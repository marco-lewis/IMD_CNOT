
section \<open>CNOT\<close>
                  
theory CNOT
  imports
  Isabelle_Marries_Dirac.Basics
  Isabelle_Marries_Dirac.Quantum
  Isabelle_Marries_Dirac.More_Tensor
  Isabelle_Marries_Dirac.Deutsch
begin


abbreviation \<psi>00 :: "complex Matrix.mat" where
"\<psi>00 \<equiv> mat_of_cols_list 4 [[1,0,0,0]]"

abbreviation \<psi>10 :: "complex Matrix.mat" where
"\<psi>10 \<equiv> mat_of_cols_list 4 [[0,0,1,0]]"

abbreviation \<psi>11 :: "complex Matrix.mat" where
"\<psi>11 \<equiv> mat_of_cols_list 4 [[0,0,0,1]]"


lemma \<psi>00_is_zero_zero:
  shows "\<psi>00 = |zero\<rangle> \<Otimes> |zero\<rangle>"
proof 
  show "dim_row \<psi>00 = dim_row ( |zero\<rangle> \<Otimes> |zero\<rangle>)" 
    by (simp add: mat_of_cols_list_def)
  show "dim_col \<psi>00 = dim_col ( |zero\<rangle> \<Otimes> |zero\<rangle>)" 
    by (simp add: mat_of_cols_list_def)
  fix i j:: nat
  assume "i < dim_row ( |zero\<rangle> \<Otimes> |zero\<rangle>)" and "j < dim_col ( |zero\<rangle> \<Otimes> |zero\<rangle>)"
  then have "i \<in> {0,1,2,3}" and "j = 0" 
    using mat_of_cols_list_def by auto
  show "\<psi>00 $$ (i,j) = ( |zero\<rangle> \<Otimes> |zero\<rangle>) $$ (i,j)" 
    by (simp add: mat_of_cols_list_def)
qed

(*
lemma \<psi>00_is_state:
  shows "state 2 \<psi>00" 
proof
  show "dim_col \<psi>00 = 1"
    by (simp add: mat_of_cols_list_def)
  show "dim_row \<psi>00 = 2\<^sup>2"
    by (simp add: mat_of_cols_list_def)
  show "\<parallel>Matrix.col \<psi>00 0\<parallel> = 1"
    using state.is_normal tensor_state2 by auto
qed
*)


(* First Operation *)
abbreviation X_on_ctrl where "X_on_ctrl \<equiv> (X \<Otimes> Id 1)"

lemma X_tensor_id:
  defines d: "v \<equiv> mat_of_cols_list 4 [[0,0,1,0],
                                      [0,0,0,1],
                                      [1,0,0,0],
                                      [0,1,0,0]]"
  shows "X_on_ctrl = v"
proof
  show "dim_col X_on_ctrl = dim_col v"  
    by (simp add: d X_def Id_def mat_of_cols_list_def)
  show "dim_row X_on_ctrl = dim_row v"
    by (simp add: d X_def Id_def mat_of_cols_list_def)
  fix i j:: nat assume "i < dim_row v" and "j < dim_col v"
  then have "i \<in> {0..<4} \<and> j \<in> {0..<4}" 
    by (auto simp add: d mat_of_cols_list_def)
  thus "X_on_ctrl $$ (i, j) = v $$ (i, j)"
    by (auto simp add: d Id_def X_def mat_of_cols_list_def)
qed

lemma X_on_ctrl_is_gate:
  shows "gate 2 X_on_ctrl"
proof
  show "unitary X_on_ctrl"
    using X_is_gate id_is_gate gate_def tensor_gate
    by blast
  show "square_mat X_on_ctrl"
    using X_is_gate id_is_gate gate_def tensor_gate
    by blast
  show "dim_row X_on_ctrl = 2\<^sup>2"
    using X_tensor_id by (simp add: mat_of_cols_list_def)
qed

lemma \<psi>00_to_\<psi>10:              
  shows "(X \<Otimes> Id 1) * \<psi>00 = \<psi>10"
proof
  fix i j:: nat
  assume "i < dim_row \<psi>10" and "j < dim_col \<psi>10"
  then have a0:"i \<in> {0,1,2,3} \<and> j = 0" by (auto simp add: mat_of_cols_list_def)
  then have "i < dim_row (X_on_ctrl) \<and> j < dim_col \<psi>00"
    using mat_of_cols_list_def X_tensor_id by auto
  then have "(X_on_ctrl*\<psi>00) $$ (i,j)
        = (\<Sum> k \<in> {0 ..< dim_vec \<psi>00}. (Matrix.row (X_on_ctrl) i) $ k * (Matrix.col \<psi>00 j) $ k)"
    by (auto simp: times_mat_def scalar_prod_def)
  thus "(X_on_ctrl * \<psi>00) $$ (i, j) = \<psi>10 $$ (i, j)"
    using  mat_of_cols_list_def X_tensor_id a0
    by (auto simp: diff_divide_distrib)
next
  show "dim_row (X_on_ctrl * \<psi>00) = dim_row \<psi>10"
    using X_tensor_id mat_of_cols_list_def by simp
  show "dim_col (X_on_ctrl * \<psi>00) = dim_col \<psi>10"
    using X_tensor_id mat_of_cols_list_def by simp
qed

(* Second Operation *)
lemma \<psi>10_to_\<psi>11:
  shows "CNOT * \<psi>10 = \<psi>11"
proof
  show "dim_row (CNOT * \<psi>10) = dim_row \<psi>11"
    by (simp add: CNOT_def mat_of_cols_list_def)
  show "dim_col (CNOT * \<psi>10) = dim_col \<psi>11"
    by (simp add: CNOT_def mat_of_cols_list_def)
  fix i j:: nat
  assume "i < dim_row \<psi>11" and "j < dim_col \<psi>11"
  then have asm:"i \<in> {0,1,2,3} \<and> j = 0" 
    by (auto simp add: mat_of_cols_list_def)
  then have "i < dim_row CNOT \<and> j < dim_col \<psi>10" 
    by (auto simp: mat_of_cols_list_def CNOT_def)
  then have "(CNOT * \<psi>10) $$ (i,j)
        = (\<Sum> k \<in> {0 ..< dim_vec \<psi>10}. (Matrix.row (CNOT) i) $ k * (Matrix.col \<psi>10 j) $ k)"
    by (auto simp: times_mat_def scalar_prod_def)
  thus "(CNOT * \<psi>10) $$ (i, j) = \<psi>11 $$ (i, j)"
    using mat_of_cols_list_def asm
    by (auto simp add:  CNOT_def)
qed

(* Circuit *)
definition circ:: "complex Matrix.mat" where
"circ \<equiv> CNOT * ((X_on_ctrl) * \<psi>00)"

lemma circ_result [simp]:
  shows "circ = \<psi>11"
  using circ_def \<psi>00_to_\<psi>10 \<psi>10_to_\<psi>11 by simp

end