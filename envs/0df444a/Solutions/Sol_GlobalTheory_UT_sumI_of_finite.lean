-- Prove2me | solution 1 for GlobalTheory.UT.sumI_of_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:35:11.893935+00:00
-- url     : https://prove2.me/submissions/11d8623d-8bec-41c9-8835-88c5c18162d4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_TXFrame
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SumIOfFinite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.UT
namespace GlobalTheory.UT
theorem _root_.solution {R : Type} [CommRing R] (I : Ideal R) {E Ix : Type} [AddCommGroup E] [Module R E] (x : Ix → E)
    (S : Finset Ix) (hS : ∀ i, i ∉ S → x i = 0) : SumI I x (∑ i ∈ S, x i) := by
  classical
  have hx : ∀ i, x i ∈ Submodule.span R (↑(S.image x) : Set E) := fun i => by
    by_cases h : i ∈ S
    · exact Submodule.subset_span (by simpa using ⟨i, h, rfl⟩)
    · rw [hS i h]; exact Submodule.zero_mem _
  refine ⟨Submodule.span R ↑(S.image x), ⟨_, rfl⟩, Submodule.sum_mem _ fun i _ => hx i, hx, fun n => ⟨S, fun T hT => ?_⟩⟩
  rw [Finset.sum_subset hT (fun i _ h => hS i h), sub_self]; exact Submodule.zero_mem _
end GlobalTheory.UT
