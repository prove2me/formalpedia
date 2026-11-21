-- Prove2me | solution 1 for NewtonianLipschitz.newtonianJacobianMatrix_swapYZ_entry
-- status  : ACCEPTED   (prove)
-- author  : @yuzhou
-- created : 2026-11-21T03:50:17.249843+00:00
-- url     : https://prove2.me/submissions/4d763edf-fdac-4a7b-b846-406bf047dcad

module
public import Definitions.Def_NewtonianLipschitz_JacobianSymmetries
public import Definitions.Def_NewtonianLipschitz_JacobianPermutations
set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz

private theorem perm_entry (μ : ℝ) (x : Vec3) (i j : Fin 3) :
    newtonianJacobianMatrix μ (swapYZVec x) i j =
      newtonianJacobianMatrix μ x (swapYZIndex i) (swapYZIndex j) := by
  have hr : euclideanRadius (swapYZVec x) = euclideanRadius x := by
    simp [euclideanRadius, swapYZVec]
    ring_nf
  simp only [newtonianJacobianMatrix, Matrix.smul_apply, Matrix.sub_apply,
    Matrix.vecMulVec_apply, Matrix.one_apply, smul_eq_mul, hr]
  fin_cases i <;> fin_cases j <;> norm_num [swapYZVec, swapYZIndex, Fin.ext_iff]

theorem solution
    (μ : ℝ) (x : Vec3) (i j : Fin 3) :
    newtonianJacobianMatrix μ (swapYZVec x) i j =
      newtonianJacobianMatrix μ x (swapYZIndex i) (swapYZIndex j) := by
  exact perm_entry μ x i j
