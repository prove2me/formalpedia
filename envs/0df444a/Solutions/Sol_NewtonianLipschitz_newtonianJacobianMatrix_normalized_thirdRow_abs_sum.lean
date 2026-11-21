-- Prove2me | solution 1 for NewtonianLipschitz.newtonianJacobianMatrix_normalized_thirdRow_abs_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:50:23.620164+00:00
-- url     : https://prove2.me/submissions/971378eb-5b38-45ae-a0ff-279e829d78a2

module
public import Definitions.Def_NewtonianLipschitz_JacobianMatrix
public import Definitions.Def_NewtonianLipschitz_ScalarMaximum
public import Definitions.Def_NewtonianLipschitz_NormalizedSharpBound
public import Theorems.Thm_NewtonianLipschitz_newtonianJacobianMatrix_normalized_two_zero
public import Theorems.Thm_NewtonianLipschitz_newtonianJacobianMatrix_normalized_two_one
public import Theorems.Thm_NewtonianLipschitz_newtonianJacobianMatrix_normalized_two_two
public import Theorems.Thm_NewtonianLipschitz_euclideanRadius_eq_physical_norm
public import Theorems.Thm_NewtonianLipschitz_lateralRowNumerator_eq


set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz
namespace NewtonianLipschitz
theorem _root_.solution
    (μ u v : ℝ) (hμ : 0 ≤ μ)
    (hu0 : 0 ≤ u) (hv0 : 0 ≤ v) :
    (∑ j : Fin 3,
      |newtonianJacobianMatrix μ (normalizedVector u v) 2 j|) =
      (μ / euclideanRadius (normalizedVector u v) ^ 5) *
        lateralRowNumerator v u := by
  have hr : 0 ≤ euclideanRadius (normalizedVector u v) := by
    rw [euclideanRadius_eq_physical_norm]
    exact norm_nonneg _
  have hk : 0 ≤ μ / euclideanRadius (normalizedVector u v) ^ 5 :=
    div_nonneg hμ (pow_nonneg hr _)
  have h3v : 0 ≤ 3 * v :=
    mul_nonneg (by norm_num) hv0
  have h3vu : 0 ≤ 3 * v * u :=
    mul_nonneg h3v hu0
  rw [Fin.sum_univ_three,
    newtonianJacobianMatrix_normalized_two_zero,
    newtonianJacobianMatrix_normalized_two_one,
    newtonianJacobianMatrix_normalized_two_two]
  rw [abs_of_nonneg (mul_nonneg hk h3v),
    abs_of_nonneg (mul_nonneg hk h3vu),
    abs_mul, abs_of_nonneg hk]
  rw [lateralRowNumerator_eq]
  ring
end NewtonianLipschitz
