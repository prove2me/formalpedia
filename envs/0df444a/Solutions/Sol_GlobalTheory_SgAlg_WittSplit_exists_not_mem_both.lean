-- Prove2me | solution 1 for GlobalTheory.SgAlg.WittSplit.exists_not_mem_both
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:45:39.908371+00:00
-- url     : https://prove2.me/submissions/24d66e2f-0b73-40f1-8bfa-fb4216c495d0

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_InFrameStabilizer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_WittFreeTuplesSplitQuadraticEtale

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SgAlg Matrix Module
noncomputable section
open GlobalTheory GlobalTheory.SgAlg GlobalTheory.SgAlg.WittSplit
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
namespace GlobalTheory.SgAlg.WittSplit
theorem _root_.solution (U U' : Submodule K V) (h : finrank K U = finrank K U') (hU : U ≠ ⊤) :
    ∃ v, v ∉ U ∧ v ∉ U' := by
  by_cases h1 : U ≤ U'
  · have hUU : U = U' := Submodule.eq_of_le_of_finrank_eq h1 h
    subst hUU
    obtain ⟨v, hv⟩ : ∃ v, v ∉ U := by
      by_contra hc; push_neg at hc; exact hU (eq_top_iff.2 fun x _ => hc x)
    exact ⟨v, hv, hv⟩
  by_cases h2 : U' ≤ U
  · exact absurd (Submodule.eq_of_le_of_finrank_eq h2 h.symm ▸ le_rfl) h1
  obtain ⟨x, hxU, hxU'⟩ := SetLike.not_le_iff_exists.1 h1
  obtain ⟨y, hyU', hyU⟩ := SetLike.not_le_iff_exists.1 h2
  refine ⟨x + y, fun hm => hyU ?_, fun hm => hxU' ?_⟩
  · simpa using U.sub_mem hm hxU
  · simpa using U'.sub_mem hm hyU'
end GlobalTheory.SgAlg.WittSplit
