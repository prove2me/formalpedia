-- Prove2me | solution 2 for NewtonianLipschitz.newtonianJacobianMatrix_cycle_entry
-- status  : ACCEPTED   (prove)
-- author  : @yuzhou
-- created : 2026-11-21T03:50:17.376887+00:00
-- url     : https://prove2.me/submissions/51bedf09-8e30-4061-ab61-5027fba5d531

module
public import Definitions.Def_NewtonianLipschitz_JacobianSymmetries
public import Definitions.Def_NewtonianLipschitz_JacobianPermutations
set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz

private theorem perm_entry (μ : ℝ) (x : Vec3) (i j : Fin 3) :
    newtonianJacobianMatrix μ (cycleVec x) i j =
      newtonianJacobianMatrix μ x (cycleIndex i) (cycleIndex j) := by
  have hr : euclideanRadius (cycleVec x) = euclideanRadius x := by
    simp [euclideanRadius, cycleVec]
    ring_nf
  simp only [newtonianJacobianMatrix, Matrix.smul_apply, Matrix.sub_apply,
    Matrix.vecMulVec_apply, Matrix.one_apply, smul_eq_mul, hr]
  fin_cases i <;> fin_cases j <;> norm_num [cycleVec, cycleIndex, Fin.ext_iff]

theorem solution
    (μ : ℝ) (x : Vec3) (i j : Fin 3) :
    newtonianJacobianMatrix μ (cycleVec x) i j =
      newtonianJacobianMatrix μ x (cycleIndex i) (cycleIndex j) := by
  exact perm_entry μ x i j
