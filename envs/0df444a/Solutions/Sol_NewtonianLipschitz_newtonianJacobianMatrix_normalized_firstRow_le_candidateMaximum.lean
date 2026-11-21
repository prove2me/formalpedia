-- Prove2me | solution 1 for NewtonianLipschitz.newtonianJacobianMatrix_normalized_firstRow_le_candidateMaximum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:48:12.418918+00:00
-- url     : https://prove2.me/submissions/d3affd00-e800-46ea-950d-b5e788f907f6

module
public import Definitions.Def_NewtonianLipschitz_JacobianMatrix
public import Definitions.Def_NewtonianLipschitz_ScalarMaximum
public import Definitions.Def_NewtonianLipschitz_NormalizedSharpBound
public import Theorems.Thm_NewtonianLipschitz_diagonalParameter_mem_unitInterval
public import Theorems.Thm_NewtonianLipschitz_normalizedVector_radius_eq_diagonal
public import Theorems.Thm_NewtonianLipschitz_candidateCoefficient_eq
public import Theorems.Thm_NewtonianLipschitz_candidateCoefficient_le_at_criticalPoint
public import Theorems.Thm_NewtonianLipschitz_candidateMaximum_eq
public import Theorems.Thm_NewtonianLipschitz_dominantRowNumerator_diagonal
public import Theorems.Thm_NewtonianLipschitz_newtonianJacobianMatrix_normalized_firstRow_le_diagonal


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
      |newtonianJacobianMatrix μ (normalizedVector u v) 0 j|) ≤
      μ * candidateMaximum := by
  let t := diagonalParameter u v
  have ht : t ∈ Set.Icc (0 : ℝ) 1 :=
    diagonalParameter_mem_unitInterval u v hu0 hu1 hv0 hv1
  have hrow :=
    newtonianJacobianMatrix_normalized_firstRow_le_diagonal
      μ u v hμ hu0 hu1 hv0 hv1
  have hr :
      euclideanRadius (normalizedVector u v) =
        Real.sqrt (1 + 2 * t ^ 2) :=
    normalizedVector_radius_eq_diagonal u v
  have hcoe :
      (μ / euclideanRadius (normalizedVector u v) ^ 5) *
        dominantRowNumerator t t = μ * candidateCoefficient t := by
    rw [dominantRowNumerator_diagonal, candidateCoefficient_eq, hr]
    ring
  have hmax :
      candidateCoefficient t ≤ candidateMaximum := by
    rw [candidateMaximum_eq]
    exact candidateCoefficient_le_at_criticalPoint t ht
  calc
    (∑ j : Fin 3,
      |newtonianJacobianMatrix μ (normalizedVector u v) 0 j|)
        ≤ (μ / euclideanRadius (normalizedVector u v) ^ 5) *
            dominantRowNumerator t t := hrow
    _ = μ * candidateCoefficient t := hcoe
    _ ≤ μ * candidateMaximum :=
      mul_le_mul_of_nonneg_left hmax hμ
end NewtonianLipschitz
