-- Prove2me | solution 1 for GlobalTheory.DI.inTot_delta_Dtot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:09:22.774454+00:00
-- url     : https://prove2.me/submissions/a9927e45-2cb8-424b-9384-4652a6280c71

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFlatLift
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsTotalCochainOfDegreeSuccOfDifferentials

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.DI
open GlobalTheory GlobalTheory.DI
namespace GlobalTheory.DI
namespace _root_.GlobalTheory.DI
theorem _root_.solution : ∀ {ι : Type} [LinearOrder ι] {E : Type}
    [AddCommGroup E] (d : E →+ E)
    (T : ℕ → Finset ι → AddSubgroup E), (∀ q s t, s.Nonempty → s ⊆ t → T q s ≤ T q t) →
    ∀ m c, _root_.GlobalTheory.DI.InTot T m c → _root_.GlobalTheory.DI.InTot T (m + 1)
        (_root_.GlobalTheory.DI.delta c) ∧
      ((∀ q s x, x ∈ T q s → d x ∈ T (q + 1) s) →
        _root_.GlobalTheory.DI.InTot T (m + 1) (_root_.GlobalTheory.DI.Dtot d c)) := by
  intro ι _ E _ d T hmono m c hc
  unfold _root_.GlobalTheory.DI.InTot at hc
  obtain ⟨h0, hmem, hzero⟩ := hc
  have hδ0 : _root_.GlobalTheory.DI.delta c ∅ = 0 := by
    unfold _root_.GlobalTheory.DI.delta; simp
  have hδmem : ∀ (q : ℕ) (t : Finset ι), q + t.card = m + 1 →
      _root_.GlobalTheory.DI.delta c t ∈ T q t := by
    intro q t hqt
    unfold _root_.GlobalTheory.DI.delta
    refine AddSubgroup.sum_mem _ fun i hi => AddSubgroup.zsmul_mem _ ?_ _
    have hcard : (t.erase i).card = t.card - 1 := Finset.card_erase_of_mem hi
    have hpos : 0 < t.card := Finset.card_pos.mpr ⟨i, hi⟩
    have hq : q + (t.erase i).card = m := by omega
    rcases (t.erase i).eq_empty_or_nonempty with he | hne
    · rw [he, h0]; exact zero_mem _
    · exact hmono q _ _ hne (Finset.erase_subset i t) (hmem q _ hq)
  have hδz : ∀ t : Finset ι, m + 1 < t.card → _root_.GlobalTheory.DI.delta c t = 0 := by
    intro t ht
    unfold _root_.GlobalTheory.DI.delta
    refine Finset.sum_eq_zero fun i hi => ?_
    have hcard : (t.erase i).card = t.card - 1 := Finset.card_erase_of_mem hi
    rw [hzero _ (by omega), smul_zero]
  refine ⟨⟨hδ0, hδmem, hδz⟩, fun hd => ⟨?_, ?_, ?_⟩⟩
  · unfold _root_.GlobalTheory.DI.Dtot; simp [hδ0, h0]
  · intro q t hqt
    unfold _root_.GlobalTheory.DI.Dtot
    refine add_mem (hδmem q t hqt) (AddSubgroup.zsmul_mem _ ?_ _)
    rcases q with _ | q
    · rw [hzero t (by omega), map_zero]; exact zero_mem _
    · exact hd q t _ (hmem q t (by omega))
  · intro t ht
    unfold _root_.GlobalTheory.DI.Dtot
    rw [hδz t ht, hzero t (by omega), map_zero, smul_zero, add_zero]
end _root_.GlobalTheory.DI
end GlobalTheory.DI
