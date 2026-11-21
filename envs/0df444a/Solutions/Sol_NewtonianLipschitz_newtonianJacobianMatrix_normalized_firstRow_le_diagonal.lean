-- Prove2me | solution 1 for NewtonianLipschitz.newtonianJacobianMatrix_normalized_firstRow_le_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:46:36.219454+00:00
-- url     : https://prove2.me/submissions/8fcfbd97-669e-4b2a-b90d-cbf6d2d34b44

module
public import Definitions.Def_NewtonianLipschitz_Derivative
public import Definitions.Def_NewtonianLipschitz_JacobianRows
public import Definitions.Def_NewtonianLipschitz_JacobianMatrix
public import Theorems.Thm_NewtonianLipschitz_newtonianJacobianMatrix_normalized_firstRow_abs_sum
public import Theorems.Thm_NewtonianLipschitz_dominantRowNumerator_le_diagonal
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
      |newtonianJacobianMatrix μ (normalizedVector u v) 0 j|) ≤
      (μ / euclideanRadius (normalizedVector u v) ^ 5) *
        dominantRowNumerator (diagonalParameter u v)
          (diagonalParameter u v) := by
  rw [newtonianJacobianMatrix_normalized_firstRow_abs_sum
    μ u v hμ hu0 hu1 hv0 hv1]
  have hr : 0 ≤ euclideanRadius (normalizedVector u v) := by
    rw [euclideanRadius_eq_physical_norm]
    exact norm_nonneg _
  exact mul_le_mul_of_nonneg_left
    (dominantRowNumerator_le_diagonal u v)
    (div_nonneg hμ (pow_nonneg hr _))
end NewtonianLipschitz
