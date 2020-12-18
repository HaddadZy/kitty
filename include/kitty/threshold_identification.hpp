/* kitty: C++ truth table library
 * Copyright (C) 2017-2020  EPFL
 *
 * Permission is hereby granted, free of charge, to any person
 * obtaining a copy of this software and associated documentation
 * files (the "Software"), to deal in the Software without
 * restriction, including without limitation the rights to use,
 * copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the
 * Software is furnished to do so, subject to the following
 * conditions:
 *
 * The above copyright notice and this permission notice shall be
 * included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
 * EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES
 * OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
 * NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT
 * HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,
 * WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
 * FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR
 * OTHER DEALINGS IN THE SOFTWARE.
 */
/*!
  \file threshold_identification.hpp
  \brief Threshold logic function identification
  \author CS-472 2020 Zyad HADDAD SCIPER 269774
*/
#pragma once

#include <vector>
#include <lpsolve/lp_lib.h> /* uncomment this line to include lp_solve */
#include "traits.hpp"
#include "bit_operations.hpp"
#include "isop.hpp"

namespace kitty
{

enum binate{
    NEG=-1,
    BIN=0,
    POS=1
  };

/*! \brief Threshold logic function identification
  Given a truth table, this function determines whether it is a threshold logic function (TF)
  and finds a linear form if it is. A Boolean function is a TF if it can be expressed as
  f(x_1, ..., x_n) = \sum_{i=1}^n w_i x_i >= T
  where w_i are the weight values and T is the threshold value.
  The linear form of a TF is the vector [w_1, ..., w_n; T].
  \param tt The truth table
  \param plf Pointer to a vector that will hold a linear form of `tt` if it is a TF.
             The linear form has `tt.num_vars()` weight values and the threshold value
             in the end.
  \return `true` if `tt` is a TF; `false` if `tt` is a non-TF.
*/
template<typename TT, typename = std::enable_if_t<is_complete_truth_table<TT>::value>>
bool is_threshold( const TT& tt, std::vector<int64_t>* plf = nullptr )
{
  std::vector<int64_t> linear_form;
  std::vector<int> unate;
  /* TODO */
  /* if tt is non-TF: */
  //return false;

  for ( uint8_t i = 0; i < tt.num_vars(); i++ )
  {
    auto const ttcof0 = cofactor0( tt, i );
    auto const ttcof1 = cofactor1( tt, i );

    int pos_counter=0;
    int neg_counter=0;

    int bit_number=(2 << (tt.num_vars()-1)); 

    //check unateness
    for (int j=0; j<bit_number;j++){
      if (get_bit(ttcof1, j)>=get_bit(ttcof0,j)){
        pos_counter++;
      }
      if (get_bit(ttcof0,j)>=get_bit(ttcof1,j)){
        neg_counter++;
      }
    }

    if (pos_counter==bit_number)
      unate.push_back(POS);

    else if (neg_counter==bit_number)
      unate.push_back(NEG);
    else
    {
      unate.push_back(BIN);
      return false;
    }
  }
 
 //flip for negative unate variables
  TT pos_tt=tt;
  for (int j=0; j<(int)unate.size();j++){
    if (unate.at(j)==NEG)
    {
      pos_tt=flip(pos_tt,j);
    }
  }
  //initiate variables for lp model
  lprec *lp;
  int Ncol, *colno = NULL; 
  REAL *row = NULL;
  int ret = 0, negsum=0;
 
  Ncol = tt.num_vars()+1; 
  lp = make_lp(0, Ncol);

  if(lp == NULL)
    ret = 1; /* couldn't construct a new model... */

    if(ret == 0) {
    /* create space large enough */
    colno = (int *) malloc(Ncol * sizeof(*colno));
    row = (REAL *) malloc(Ncol * sizeof(*row));
    if((colno == NULL) || (row == NULL))
      ret = 2;
  }


  //primes onset and offset
  auto on_cube=isop(pos_tt);
  auto off_cube=isop(unary_not(pos_tt));

  if (ret==0)
  {
    set_add_rowmode(lp, true); //makes building the model faster row by row
    for(int j = 0; j <= tt.num_vars(); j++){
      colno[0]++;
      row[j] = 1;
      add_constraintex(lp, 1, row, colno, GE, 0); //all variables must be positive
    }

    //onset minterms cube
    for(int i = 0; i < on_cube.size() ; i++){
      for(int j = 0; j < tt.num_vars(); j++){
        colno[j]=j+1;
        if(on_cube.at(i).get_mask(j)==1 && on_cube.at(i).get_mask(j)==1){
          row[j] = 1;
        }
        else{ 
          row[j] = 0;
        }  
      }
    //Add Threshold constraint on right side (thus -1)
      colno[tt.num_vars()] = Ncol;
      row[tt.num_vars()] = -1;
      add_constraintex(lp, Ncol, row, colno, GE, 0);
    }
    //offset minterms cube
    for(int i = 0; i < off_cube.size() ; i++){
      for(int j = 0; j < tt.num_vars(); j++){
        colno[j] = j+1;
        if(off_cube.at(i).get_mask(j)==1 && off_cube.at(i).get_bit(j)==0){
          row[j] = 0;
        }   
        else{ 
          row[j] = 1;
        }
      }
      //Add Threshold constraint on right side (thus -1)
      colno[tt.num_vars()] = Ncol;
      row[tt.num_vars()] = -1;
      add_constraintex(lp, Ncol, row, colno, LE, -1);
    }
  
    set_add_rowmode(lp, FALSE); // rowmode should be turned off again when done building the model
    int j = 0;
    for(int i = 1; i <Ncol; i++){
      colno[j] = i;
      row[j] = 1;
      j++;
    }
    colno[j] = Ncol;
    row[j] = 1;
    j++;
    set_obj_fnex(lp, j, row, colno); //function to minimize, (sort of diagonal matrix)
 

    set_minim(lp);
    ret = solve(lp);
    if(ret != 0){ //solution does not exist, not threshold
      return false;
    }
  }

  if(ret == 0) { //solution exists, get linear form now
    get_variables(lp, row);
    negsum=row[tt.num_vars()];
  }
  for(int i = 0; i < tt.num_vars(); i++){
    negsum=row[tt.num_vars()];
    if(unate.at(i)==NEG){
      linear_form.push_back(-row[i]); //get original form back after flipping
      negsum-=row[i];
    }
    else{
      linear_form.push_back(row[i]);
    }
  }
  linear_form.push_back(negsum);
/* free allocated memory */
  if(row != NULL)
    free(row);
  if(colno != NULL)
    free(colno);
  if(lp != NULL) {
    delete_lp(lp);
  }
  if ( plf )
  {
    *plf = linear_form;
  }
  return true;
}
} /* namespace kitty */