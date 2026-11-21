-- Prove2me | solution 1 for NewtonianLipschitz.matrix3_mulVec_coordinate_abs_le_rowSum
-- status  : ACCEPTED   (prove)
-- author  : @yuzhou
-- created : 2026-11-21T03:48:28.916796+00:00
-- url     : https://prove2.me/submissions/65d525e8-2eca-4005-988d-a67f95c278a5

module
public import Definitions.Def_NewtonianLipschitz_JacobianCartesianBound
public import Definitions.Def_NewtonianLipschitz_JacobianOperatorAction
set_option autoImplicit true
@[expose] public section
public section
open Matrix
open NewtonianLipschitz


theorem solution
    (A : Matrix (Fin 3) (Fin 3) ℝ) (h : Vec3) (i : Fin 3) :
    |(A *ᵥ h) i| ≤ (∑ j : Fin 3, |A i j|) * ‖h‖ := by
  simp only [Matrix.mulVec, dotProduct]
  calc
    |∑ j : Fin 3, A i j * h j| ≤ ∑ j : Fin 3, |A i j * h j| := by
      simpa only [Real.norm_eq_abs] using
        (norm_sum_le (Finset.univ : Finset (Fin 3)) (fun j => A i j * h j))
    _ ≤ (∑ j : Fin 3, |A i j|) * ‖h‖ := by
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      simpa only [Real.norm_eq_abs] using (norm_le_pi_norm h j)
