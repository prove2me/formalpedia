-- Prove2me | solution 1 for NewtonianLipschitz.newtonianJacobianMatrix_diagonal_firstRow_eq_coefficient
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:55:59.381259+00:00
-- url     : https://prove2.me/submissions/a8a05b2b-3e01-438f-84e9-202cf5c33351

module
public import Definitions.Def_NewtonianLipschitz_JacobianOperatorNorm
public import Definitions.Def_NewtonianLipschitz_JacobianSharpWitness
public import Theorems.Thm_NewtonianLipschitz_normalized_diagonal_radius
public import Theorems.Thm_NewtonianLipschitz_candidateCoefficient_eq
public import Theorems.Thm_NewtonianLipschitz_dominantRowNumerator_diagonal
public import Theorems.Thm_NewtonianLipschitz_newtonianJacobianMatrix_normalized_firstRow_abs_sum


set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz
namespace NewtonianLipschitz
theorem _root_.solution
    (μ t : ℝ) (hμ : 0 ≤ μ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (∑ j : Fin 3,
      |newtonianJacobianMatrix μ (normalizedVector t t) 0 j|) =
        μ * candidateCoefficient t := by
  calc
    (∑ j : Fin 3,
      |newtonianJacobianMatrix μ (normalizedVector t t) 0 j|)
        = (μ / euclideanRadius (normalizedVector t t) ^ 5) *
            dominantRowNumerator t t :=
          newtonianJacobianMatrix_normalized_firstRow_abs_sum
            μ t t hμ ht0 ht1 ht0 ht1
    _ = μ * candidateCoefficient t := by
      rw [normalized_diagonal_radius,
        dominantRowNumerator_diagonal, candidateCoefficient_eq]
      ring
end NewtonianLipschitz
