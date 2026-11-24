-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.UnrDens.GramDiff.exists_trace_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:51:55.888218+00:00
-- url     : https://prove2.me/submissions/e96e63ee-9054-424c-96d2-4afa0db234d8

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HermitianMatricesCardStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardFibreGramDifferential

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.UnrDens.GramDiff
variable {E : Type} [CommRing E] (τ : E →+* E)
namespace GlobalTheory.CompanionTheory.UnrDens.GramDiff
theorem _root_.solution {q : ℕ} {ε : ℤ} (h : ResAlg E τ q ε) : ∃ θ : E, θ + τ θ = 1 := by
  obtain ⟨u, hu, -⟩ := h.basis
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  have h1 : (u - τ u) * τ v = -1 := by
    have := congrArg τ hv
    rw [map_mul, map_sub, h.inv, map_one] at this
    linear_combination -this
  have h2 : τ v = -v := by
    linear_combination (-(τ v)) * hv + v * h1
  refine ⟨u * v, ?_⟩
  rw [map_mul, h2]
  linear_combination hv
end GlobalTheory.CompanionTheory.UnrDens.GramDiff
