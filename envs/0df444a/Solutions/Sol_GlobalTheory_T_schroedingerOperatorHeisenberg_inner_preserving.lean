-- Prove2me | solution 1 for GlobalTheory.T.schroedingerOperatorHeisenberg_inner_preserving
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:24:42.830047+00:00
-- url     : https://prove2.me/submissions/5ebc8855-fcb0-42ac-bfc3-50af4e863264

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchroedingerOperatorHeisenbergInnerPreserving
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchroedingerOperatorHeisenbergInnerPreservingStatement
import Theorems.Thm_GlobalTheory_schr_unitary


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Invertible (2 : k)] (ψ0 : AddChar k ℂ), Continuous ψ0 →
    ∀ {κ : Type} [Fintype κ] (μ : @Measure (κ → k) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∀ (w : (κ → k) × (κ → k)) (φ φ' : (κ → k) → ℂ),
      ∫ y, GlobalTheory.WeilM.schr ψ0 w φ y * (starRingEnd ℂ) (GlobalTheory.WeilM.schr ψ0 w φ' y) ∂μ = ∫ y, φ y * (starRingEnd ℂ) (φ' y) ∂μ := by
  first | exact @GlobalTheory.schr_unitary | exact GlobalTheory.schr_unitary | (intros; apply GlobalTheory.schr_unitary <;> assumption)
end _root_.GlobalTheory.T
