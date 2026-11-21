-- Prove2me | solution 2 for NewtonianLipschitz.newtonianJacobianMatrix_cycle_rowSum
-- status  : ACCEPTED   (prove)
-- author  : @yuzhou
-- created : 2026-11-21T03:52:11.434414+00:00
-- url     : https://prove2.me/submissions/a3ba8d42-ac40-438d-a837-6ec109c0e3f1

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
    (μ : ℝ) (x : Vec3) (i : Fin 3) :
    (∑ j : Fin 3, |newtonianJacobianMatrix μ (cycleVec x) i j|) =
      ∑ j : Fin 3,
        |newtonianJacobianMatrix μ x (cycleIndex i) j| := by
  simp only [perm_entry, Fin.sum_univ_three]
  have h0 : cycleIndex (0 : Fin 3) = 1 := by decide
  have h1 : cycleIndex (1 : Fin 3) = 2 := by decide
  have h2 : cycleIndex (2 : Fin 3) = 0 := by decide
  simp only [h0, h1, h2]
  ac_rfl
