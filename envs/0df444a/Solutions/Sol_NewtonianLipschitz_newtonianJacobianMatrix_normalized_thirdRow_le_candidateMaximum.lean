-- Prove2me | solution 1 for NewtonianLipschitz.newtonianJacobianMatrix_normalized_thirdRow_le_candidateMaximum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:52:20.869163+00:00
-- url     : https://prove2.me/submissions/60ecb5fc-b682-4fe4-bbec-8deb48ac45d3

module
public import Definitions.Def_NewtonianLipschitz_JacobianMatrix
public import Definitions.Def_NewtonianLipschitz_ScalarMaximum
public import Definitions.Def_NewtonianLipschitz_NormalizedSharpBound
public import Theorems.Thm_NewtonianLipschitz_newtonianJacobianMatrix_normalized_firstRow_le_candidateMaximum
public import Theorems.Thm_NewtonianLipschitz_newtonianJacobianMatrix_normalized_thirdRow_abs_sum
public import Theorems.Thm_NewtonianLipschitz_euclideanRadius_eq_physical_norm
public import Theorems.Thm_NewtonianLipschitz_lateralRowNumerator_swapped_le_dominant
public import Theorems.Thm_NewtonianLipschitz_newtonianJacobianMatrix_normalized_firstRow_abs_sum


set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz
namespace NewtonianLipschitz
theorem _root_.solution
    (μ u v : ℝ) (hμ : 0 ≤ μ)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    (∑ j : Fin 3,
      |newtonianJacobianMatrix μ (normalizedVector u v) 2 j|) ≤
      μ * candidateMaximum := by
  have hr : 0 ≤ euclideanRadius (normalizedVector u v) := by
    rw [euclideanRadius_eq_physical_norm]
    exact norm_nonneg _
  have hk : 0 ≤ μ / euclideanRadius (normalizedVector u v) ^ 5 :=
    div_nonneg hμ (pow_nonneg hr _)
  calc
    (∑ j : Fin 3,
      |newtonianJacobianMatrix μ (normalizedVector u v) 2 j|)
        = (μ / euclideanRadius (normalizedVector u v) ^ 5) *
            lateralRowNumerator v u :=
          newtonianJacobianMatrix_normalized_thirdRow_abs_sum
            μ u v hμ hu0 hv0
    _ ≤ (μ / euclideanRadius (normalizedVector u v) ^ 5) *
          dominantRowNumerator u v :=
        mul_le_mul_of_nonneg_left
          (lateralRowNumerator_swapped_le_dominant
            u v hu0 hu1 hv0 hv1) hk
    _ = (∑ j : Fin 3,
          |newtonianJacobianMatrix μ (normalizedVector u v) 0 j|) :=
        (newtonianJacobianMatrix_normalized_firstRow_abs_sum
          μ u v hμ hu0 hu1 hv0 hv1).symm
    _ ≤ μ * candidateMaximum :=
        newtonianJacobianMatrix_normalized_firstRow_le_candidateMaximum
          μ u v hμ hu0 hu1 hv0 hv1
end NewtonianLipschitz
