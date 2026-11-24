-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SplitUnique.hTens_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:58:39.075818+00:00
-- url     : https://prove2.me/submissions/17421bea-7520-493b-a06d-f3d0189df74e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_ExistsEqMulApplyZero
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_SplitQuadraticAlgebraOrder
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_ExistsInvariantForm
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_LagrangianStabilizerCharacterTrivial
import Theorems.Thm_GlobalTheory_CompanionTheory_SplitUnique_hTens_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix ValuativeRel GlobalTheory.WeilM MeasureTheory
open scoped ComplexConjugate NNReal
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SplitUnique
variable {R : Type} [CommRing R] {E : Type} [CommRing E] [Algebra R E] (c : E →ₐ[R] E)
  {α β : Type} [Fintype α] [Fintype β]
namespace GlobalTheory.CompanionTheory.SplitUnique
theorem _root_.solution (JA : Matrix α α E) {JB : Matrix β β E} {ν : Type} [Fintype ν] {Cy : Matrix β ν E}
    (h : Cyᵀ * JB * Cy.map c = 0) (z z' : Matrix α ν E) : hTens c JA JB (z * Cyᵀ) (z' * Cyᵀ) = 0 := by
  rw [hTens_eq]
  have hm : z * Cyᵀ * JB * ((z' * Cyᵀ).map c)ᵀ = 0 := by
    have hmap : (z' * Cyᵀ).map c = z'.map c * (Cyᵀ).map c := by
      simp
    rw [hmap, Matrix.transpose_mul, Matrix.transpose_map, Matrix.transpose_transpose,
      show z * Cyᵀ * JB * (Cy.map c * (z'.map c)ᵀ) = z * (Cyᵀ * JB * Cy.map c) * (z'.map c)ᵀ by
        simp only [Matrix.mul_assoc], h]
    simp
  rw [hm]
  simp
end GlobalTheory.CompanionTheory.SplitUnique
