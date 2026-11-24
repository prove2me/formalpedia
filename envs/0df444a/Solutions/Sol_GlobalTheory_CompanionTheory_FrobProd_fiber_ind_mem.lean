-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FrobProd.fiber_ind_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:33:23.424802+00:00
-- url     : https://prove2.me/submissions/1ad69f6c-2584-40a5-ba88-3479d60ad718

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_BernsteinUnitaryProducts_BernsteinTheoremA_FrobeniusReciprocity_SupportedInIffOfFrob
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SchwartzBruhatProdSpanTensors
import Theorems.Thm_PositivityTheory_PfBern_Frob_mem_SB_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory MeasureTheory.Measure GlobalTheory.SplitWeil PositivityTheory.PfBern.Frob
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FrobProd
open Classical
namespace GlobalTheory.CompanionTheory.FrobProd
theorem _root_.solution {X S : Type} [TopologicalSpace X] [T2Space X] {ξ : X → S}
    (hξ : IsLocallyConstant ξ) (s : S) (hs : IsCompact (ξ ⁻¹' {s})) :
    (fun x => if ξ x = s then (1 : ℂ) else 0) ∈ SB X := by
  refine mem_SB_iff.2 ⟨hξ.comp (fun t => if t = s then (1 : ℂ) else 0), ?_⟩
  refine HasCompactSupport.intro hs fun x hx => ?_
  have : ξ x ≠ s := hx
  simp [this]
end GlobalTheory.CompanionTheory.FrobProd
