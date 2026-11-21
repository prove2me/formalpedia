-- Prove2me | solution 1 for NewtonianLipschitz.newtonianJacobianMatrix_normalized_secondRow_abs_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:50:20.731755+00:00
-- url     : https://prove2.me/submissions/e51831ce-1664-400e-9c3b-03b1524c27ed

module
public import Definitions.Def_NewtonianLipschitz_JacobianMatrix
public import Definitions.Def_NewtonianLipschitz_ScalarMaximum
public import Definitions.Def_NewtonianLipschitz_NormalizedSharpBound
public import Theorems.Thm_NewtonianLipschitz_newtonianJacobianMatrix_normalized_one_zero
public import Theorems.Thm_NewtonianLipschitz_newtonianJacobianMatrix_normalized_one_one
public import Theorems.Thm_NewtonianLipschitz_newtonianJacobianMatrix_normalized_one_two
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
      |newtonianJacobianMatrix μ (normalizedVector u v) 1 j|) =
      (μ / euclideanRadius (normalizedVector u v) ^ 5) *
        lateralRowNumerator u v := by
  have hr : 0 ≤ euclideanRadius (normalizedVector u v) := by
    rw [euclideanRadius_eq_physical_norm]
    exact norm_nonneg _
  have hk : 0 ≤ μ / euclideanRadius (normalizedVector u v) ^ 5 :=
    div_nonneg hμ (pow_nonneg hr _)
  have h3u : 0 ≤ 3 * u :=
    mul_nonneg (by norm_num) hu0
  have h3uv : 0 ≤ 3 * u * v :=
    mul_nonneg h3u hv0
  rw [Fin.sum_univ_three,
    newtonianJacobianMatrix_normalized_one_zero,
    newtonianJacobianMatrix_normalized_one_one,
    newtonianJacobianMatrix_normalized_one_two]
  rw [abs_of_nonneg (mul_nonneg hk h3u),
    abs_of_nonneg (mul_nonneg hk h3uv),
    abs_mul, abs_of_nonneg hk]
  rw [lateralRowNumerator_eq]
  ring
end NewtonianLipschitz
