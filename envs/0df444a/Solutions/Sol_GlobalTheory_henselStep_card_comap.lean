-- Prove2me | solution 1 for GlobalTheory.henselStep_card_comap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:59:49.298595+00:00
-- url     : https://prove2.me/submissions/0fde401f-1c90-4dee-91d8-fd8cbe6bc4b7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_PrimOfIsUnitDet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HenselStepCardComap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.GramCount
open scoped Classical
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {W T : Type} [AddCommGroup W] [AddCommGroup T]
    (T1 T2 : AddSubgroup T) (h21 : T2 ≤ T1) (d : W →+ T) (hd1 : ∀ w, d w ∈ T1)
    (hd2 : ∀ t ∈ T1, ∃ w, d w - t ∈ T2) :
    Nat.card (T2.comap d) * Nat.card T1 = Nat.card W * Nat.card T2 := by
  have hsup : d.range ⊔ T2 = T1 := by
    apply le_antisymm
    · refine sup_le ?_ h21
      rintro _ ⟨w, rfl⟩
      exact hd1 w
    · intro t ht
      obtain ⟨w, hw⟩ := hd2 t ht
      have : t = d w + -(d w - t) := by abel
      rw [this]
      exact AddSubgroup.add_mem_sup ⟨w, rfl⟩ (T2.neg_mem hw)
  have h1 : (T2.comap d).index = T2.relIndex T1 := by
    rw [AddSubgroup.index_comap, ← hsup, AddSubgroup.relIndex_sup_right]
  have h2 := AddSubgroup.card_mul_index (T2.comap d)
  have h3 := AddSubgroup.card_mul_index (T2.addSubgroupOf T1)
  have h4 : Nat.card (T2.addSubgroupOf T1) = Nat.card T2 :=
    Nat.card_congr (AddSubgroup.addSubgroupOfEquivOfLe h21).toEquiv
  rw [h4] at h3
  rw [← h2, ← h3, h1]
  unfold AddSubgroup.relIndex
  ring
end GlobalTheory
