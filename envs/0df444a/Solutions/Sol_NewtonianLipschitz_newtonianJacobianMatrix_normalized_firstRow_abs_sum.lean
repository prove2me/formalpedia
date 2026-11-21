-- Prove2me | solution 1 for NewtonianLipschitz.newtonianJacobianMatrix_normalized_firstRow_abs_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:45:18.274862+00:00
-- url     : https://prove2.me/submissions/cc1108b8-57e5-41fc-8b01-e0d529a329b9

module
public import Definitions.Def_NewtonianLipschitz_Derivative
public import Definitions.Def_NewtonianLipschitz_JacobianRows
public import Definitions.Def_NewtonianLipschitz_JacobianMatrix
public import Theorems.Thm_NewtonianLipschitz_newtonianJacobianMatrix_normalized_zero_zero
public import Theorems.Thm_NewtonianLipschitz_newtonianJacobianMatrix_normalized_zero_one
public import Theorems.Thm_NewtonianLipschitz_newtonianJacobianMatrix_normalized_zero_two
public import Theorems.Thm_NewtonianLipschitz_dominantRowNumerator_eq
public import Theorems.Thm_NewtonianLipschitz_euclideanRadius_eq_physical_norm


set_option autoImplicit true
@[expose] public section
public section
open Matrix WithLp
open scoped NNReal Topology InnerProductSpace
open NewtonianLipschitz
namespace NewtonianLipschitz
theorem _root_.solution
    (μ u v : ℝ) (hμ : 0 ≤ μ)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    (∑ j : Fin 3,
      |newtonianJacobianMatrix μ (normalizedVector u v) 0 j|) =
      (μ / euclideanRadius (normalizedVector u v) ^ 5) *
        dominantRowNumerator u v := by
  have hr : 0 ≤ euclideanRadius (normalizedVector u v) := by
    rw [euclideanRadius_eq_physical_norm]
    exact norm_nonneg _
  have hk :
      0 ≤ μ / euclideanRadius (normalizedVector u v) ^ 5 :=
    div_nonneg hμ (pow_nonneg hr _)
  have hu_prod : 0 ≤ (1 - u) * (1 + u) :=
    mul_nonneg (by linarith) (by linarith)
  have hv_prod : 0 ≤ (1 - v) * (1 + v) :=
    mul_nonneg (by linarith) (by linarith)
  have hdiag : 0 ≤ 2 - u ^ 2 - v ^ 2 := by
    nlinarith [hu_prod, hv_prod]
  rw [Fin.sum_univ_three,
    newtonianJacobianMatrix_normalized_zero_zero,
    newtonianJacobianMatrix_normalized_zero_one,
    newtonianJacobianMatrix_normalized_zero_two]
  rw [abs_of_nonneg (mul_nonneg hk hdiag),
    abs_of_nonneg (mul_nonneg hk (mul_nonneg (by norm_num) hu0)),
    abs_of_nonneg (mul_nonneg hk (mul_nonneg (by norm_num) hv0))]
  rw [dominantRowNumerator_eq]
  ring
end NewtonianLipschitz
