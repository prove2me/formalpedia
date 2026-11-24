-- Prove2me | solution 1 for GlobalTheory.DI.AltClosed.delta_oneC
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:26:30.755844+00:00
-- url     : https://prove2.me/submissions/42cc4be6-36ec-4505-b9f9-6533863ab0fd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFlatLift
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_NadelVanishingPairs_NadelVanishingLemmas_AlternatingProductCocycle
import Theorems.Thm_GlobalTheory_DI_AltClosed_delta_oneC_pair

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open GlobalTheory GlobalTheory.DI
open GlobalTheory GlobalTheory.DI GlobalTheory.DI.AltClosed
variable {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V] {ι : Type} [LinearOrder ι]
namespace GlobalTheory.DI.AltClosed
theorem _root_.solution (t : Finset ι) : delta (oneC : Finset ι → ExteriorAlgebra K V) t = 0 := by
  by_cases h2 : t.card = 2
  · obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp h2
    rcases lt_or_gt_of_ne hxy with hlt | hlt
    · exact delta_oneC_pair hlt
    · rw [Finset.pair_comm]
      exact delta_oneC_pair hlt
  · simp only [delta]
    apply Finset.sum_eq_zero
    intro i hi
    have hpos := Finset.card_pos.mpr ⟨i, hi⟩
    have hc : ¬ (t.erase i).card = 1 := by
      rw [Finset.card_erase_of_mem hi]
      omega
    simp [oneC, hc]
end GlobalTheory.DI.AltClosed
