-- Prove2me | solution 1 for GlobalTheory.eq_of_le_of_multiset_prod_eq_pow_card
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:02:54.432304+00:00
-- url     : https://prove2.me/submissions/a75e8008-6446-4cc5-ac8d-599805391089

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_PowSubSelfMemSpanOfSplitsCompletely

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {g : ℕ} (hg : 0 < g) (s : Multiset ℕ)
    (hle : ∀ a ∈ s, g ≤ a) (hprod : s.prod = g ^ s.card) : ∀ a ∈ s, a = g := by
  intro a ha
  obtain ⟨t, rfl⟩ := Multiset.exists_cons_of_mem ha
  have ht : g ^ t.card ≤ t.prod :=
    Multiset.pow_card_le_prod (fun b hb => hle b (Multiset.mem_cons_of_mem hb))
  rw [Multiset.prod_cons, Multiset.card_cons, pow_succ'] at hprod
  have hpos : 0 < g ^ t.card := pow_pos hg _
  have h1 : a * g ^ t.card ≤ g * g ^ t.card := hprod ▸ Nat.mul_le_mul_left a ht
  exact le_antisymm (Nat.le_of_mul_le_mul_right h1 hpos) (hle a (Multiset.mem_cons_self _ _))
end GlobalTheory
