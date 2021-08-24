
section \<open>CNOT Circuit\<close>
                  
theory CNOT
  imports
  Isabelle_Marries_Dirac.Basics
  Isabelle_Marries_Dirac.Quantum
  Isabelle_Marries_Dirac.More_Tensor
  Isabelle_Marries_Dirac.Deutsch
begin


abbreviation \<psi>\<^sub>0\<^sub>0 :: "complex Matrix.mat" where
"\<psi>\<^sub>0\<^sub>0 \<equiv> mat_of_cols_list 4 [[1,0,0,0]]"

abbreviation \<psi>\<^sub>1\<^sub>0 :: "complex Matrix.mat" where
"\<psi>\<^sub>1\<^sub>0 \<equiv> mat_of_cols_list 4 [[0,0,1,0]]"

abbreviation \<psi>\<^sub>1\<^sub>1 :: "complex Matrix.mat" where
"\<psi>\<^sub>1\<^sub>1 \<equiv> mat_of_cols_list 4 [[0,0,0,1]]"


lemma \<psi>\<^sub>0\<^sub>0_is_zero_zero:
  shows "\<psi>\<^sub>0\<^sub>0 = |zero\<rangle> \<Otimes> |zero\<rangle>"
proof 
  show "dim_row \<psi>\<^sub>0\<^sub>0 = dim_row ( |zero\<rangle> \<Otimes> |zero\<rangle>)" 
    by (simp add: mat_of_cols_list_def)
  show "dim_col \<psi>\<^sub>0\<^sub>0 = dim_col ( |zero\<rangle> \<Otimes> |zero\<rangle>)" 
    by (simp add: mat_of_cols_list_def)
  fix i j:: nat
  assume "i < dim_row ( |zero\<rangle> \<Otimes> |zero\<rangle>)" 
    and "j < dim_col ( |zero\<rangle> \<Otimes> |zero\<rangle>)"
  then have "i \<in> {0,1,2,3}" and "j = 0" 
    using mat_of_cols_list_def by auto
  show "\<psi>\<^sub>0\<^sub>0 $$ (i,j) = ( |zero\<rangle> \<Otimes> |zero\<rangle>) $$ (i,j)" 
    using ket_zero_is_state 
    by auto
qed

lemma \<psi>\<^sub>0\<^sub>0_is_state:
  shows "state 2 \<psi>\<^sub>0\<^sub>0"
proof
  show "dim_col \<psi>\<^sub>0\<^sub>0 = 1"
    by (simp add: mat_of_cols_list_def)
  show "dim_row \<psi>\<^sub>0\<^sub>0 = 2\<^sup>2"
    by (simp add: mat_of_cols_list_def)
  have "\<parallel>Matrix.col |zero\<rangle> 0\<parallel> = 1" 
    using ket_zero_is_state state.is_normal by auto
  thus "\<parallel>Matrix.col \<psi>\<^sub>0\<^sub>0 0\<parallel> = 1"
    using state.is_normal tensor_state2 \<psi>\<^sub>0\<^sub>0_is_zero_zero
    ket_zero_is_state by force
qed

subsection "First Operation"

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
  fix i j:: nat assume "i < dim_row v" 
                and "j < dim_col v"
  then have "i \<in> {0..<4} \<and> j \<in> {0..<4}" 
    by (auto simp add: d mat_of_cols_list_def)
  thus "X_on_ctrl $$ (i, j) = v $$ (i, j)"
    by (auto simp add: d Id_def X_def 
        mat_of_cols_list_def)
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

lemma \<psi>\<^sub>0\<^sub>0_to_\<psi>\<^sub>1\<^sub>0:              
  shows "(X \<Otimes> Id 1) * \<psi>\<^sub>0\<^sub>0 = \<psi>\<^sub>1\<^sub>0"
proof
  fix i j:: nat
  assume "i < dim_row \<psi>\<^sub>1\<^sub>0" and "j < dim_col \<psi>\<^sub>1\<^sub>0"
  then have a0:"i \<in> {0,1,2,3} \<and> j = 0" 
    by (auto simp add: mat_of_cols_list_def)
  then have "i < dim_row (X_on_ctrl) \<and> j < dim_col \<psi>\<^sub>0\<^sub>0"
    using mat_of_cols_list_def X_tensor_id by auto
  then have "(X_on_ctrl*\<psi>\<^sub>0\<^sub>0) $$ (i,j)
        = (\<Sum> k \<in> {0 ..< dim_vec \<psi>\<^sub>0\<^sub>0}. (Matrix.row (X_on_ctrl) i) $ k * (Matrix.col \<psi>\<^sub>0\<^sub>0 j) $ k)"
    by (auto simp: times_mat_def scalar_prod_def)
  thus "(X_on_ctrl * \<psi>\<^sub>0\<^sub>0) $$ (i, j) = \<psi>\<^sub>1\<^sub>0 $$ (i, j)"
    using  mat_of_cols_list_def X_tensor_id a0
    by (auto simp: diff_divide_distrib)
next
  show "dim_row (X_on_ctrl * \<psi>\<^sub>0\<^sub>0) = dim_row \<psi>\<^sub>1\<^sub>0"
    using X_tensor_id mat_of_cols_list_def by simp
  show "dim_col (X_on_ctrl * \<psi>\<^sub>0\<^sub>0) = dim_col \<psi>\<^sub>1\<^sub>0"
    using X_tensor_id mat_of_cols_list_def by simp
qed

lemma \<psi>\<^sub>1\<^sub>0_is_state:
  shows "state 2 \<psi>\<^sub>1\<^sub>0"
  using X_on_ctrl_is_gate \<psi>\<^sub>0\<^sub>0_is_state \<psi>\<^sub>0\<^sub>0_to_\<psi>\<^sub>1\<^sub>0
  by (metis gate_on_state_is_state)

subsection "Second Operation"

lemma \<psi>\<^sub>1\<^sub>0_to_\<psi>\<^sub>1\<^sub>1:
  shows "CNOT * \<psi>\<^sub>1\<^sub>0 = \<psi>\<^sub>1\<^sub>1"
proof
  show "dim_row (CNOT * \<psi>\<^sub>1\<^sub>0) = dim_row \<psi>\<^sub>1\<^sub>1"
    by (simp add: CNOT_def mat_of_cols_list_def)
  show "dim_col (CNOT * \<psi>\<^sub>1\<^sub>0) = dim_col \<psi>\<^sub>1\<^sub>1"
    by (simp add: CNOT_def mat_of_cols_list_def)
  fix i j:: nat
  assume "i < dim_row \<psi>\<^sub>1\<^sub>1" and "j < dim_col \<psi>\<^sub>1\<^sub>1"
  then have asm:"i \<in> {0,1,2,3} \<and> j = 0" 
    by (auto simp add: mat_of_cols_list_def)
  then have "i < dim_row CNOT \<and> j < dim_col \<psi>\<^sub>1\<^sub>0" 
    by (auto simp: mat_of_cols_list_def CNOT_def)
  then have "(CNOT * \<psi>\<^sub>1\<^sub>0) $$ (i,j)
        = (\<Sum> k \<in> {0 ..< dim_vec \<psi>\<^sub>1\<^sub>0}. (Matrix.row (CNOT) i) $ k * (Matrix.col \<psi>\<^sub>1\<^sub>0 j) $ k)"
    by (auto simp: times_mat_def scalar_prod_def)
  thus "(CNOT * \<psi>\<^sub>1\<^sub>0) $$ (i, j) = \<psi>\<^sub>1\<^sub>1 $$ (i, j)"
    using mat_of_cols_list_def asm
    by (auto simp add:  CNOT_def)
qed

lemma \<psi>\<^sub>1\<^sub>1_is_state:
  shows "state 2 \<psi>\<^sub>1\<^sub>1"
  using CNOT_is_gate \<psi>\<^sub>1\<^sub>0_is_state \<psi>\<^sub>1\<^sub>0_to_\<psi>\<^sub>1\<^sub>1
  by (metis gate_on_state_is_state)

subsection "Circuit"

definition circ:: "complex Matrix.mat" where
  "circ \<equiv> CNOT * ((X_on_ctrl) * ( |zero\<rangle> \<Otimes> |zero\<rangle>))"

lemma circ_result [simp]:
  shows "circ = \<psi>\<^sub>1\<^sub>1"
  using circ_def \<psi>\<^sub>0\<^sub>0_is_zero_zero \<psi>\<^sub>0\<^sub>0_to_\<psi>\<^sub>1\<^sub>0 \<psi>\<^sub>1\<^sub>0_to_\<psi>\<^sub>1\<^sub>1 
  by simp

lemma circ_res_is_state:
  shows "state 2 circ"
  using \<psi>\<^sub>1\<^sub>1_is_state by auto

end