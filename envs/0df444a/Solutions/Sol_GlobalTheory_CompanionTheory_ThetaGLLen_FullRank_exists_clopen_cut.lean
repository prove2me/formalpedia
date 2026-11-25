-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ThetaGLLen.FullRank.exists_clopen_cut
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:48:43.417615+00:00
-- url     : https://prove2.me/submissions/75a34e02-718b-4a2c-b0e0-a490b13e7cf9

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FibRepApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LocallyConstantExtensionByZero
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FiniteTwistedRankQuotient
import Theorems.Thm_GlobalTheory_CompanionTheory_ThetaGLLen_FullRank_indicator_mem_SB_of_isClopen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences GlobalTheory.RankStrataProof GlobalTheory.CompanionTheory.ThetaGLLen Matrix Topology
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ThetaGLLen GlobalTheory.CompanionTheory.ThetaGLLen.FullRank
namespace GlobalTheory.CompanionTheory.ThetaGLLen.FullRank
theorem _root_.solution : ∀ (X : Type) [TopologicalSpace X] (Y : Set X), IsClopen Y → ∀ f : SB X, ∃ f₁ f₂ : SB X, f = f₁ + f₂ ∧ (∀ x, f₁.1 x ≠ 0 → x ∈ Y ∧ f.1 x ≠ 0) ∧ (∀ x, f₂.1 x ≠ 0 → x ∉ Y ∧ f.1 x ≠ 0) := by
  intro X _ Y hY f
  refine ⟨⟨_, indicator_mem_SB_of_isClopen hY f⟩, ⟨_, indicator_mem_SB_of_isClopen hY.compl f⟩, ?_, ?_, ?_⟩
  · refine Subtype.ext (funext fun x => ?_)
    show f.1 x = Y.indicator f.1 x + Yᶜ.indicator f.1 x
    by_cases h : x ∈ Y <;> simp [h]
  · intro x hx
    have hx' : Y.indicator f.1 x ≠ 0 := hx
    by_cases h : x ∈ Y
    · exact ⟨h, by simpa [h] using hx'⟩
    · exact absurd (Set.indicator_of_notMem h _) hx'
  · intro x hx
    have hx' : Yᶜ.indicator f.1 x ≠ 0 := hx
    by_cases h : x ∈ Y
    · exact absurd (Set.indicator_of_notMem (by simpa using h) _) hx'
    · exact ⟨h, by simpa [h] using hx'⟩
end GlobalTheory.CompanionTheory.ThetaGLLen.FullRank
