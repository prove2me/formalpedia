-- Prove2me | solution 1 for GlobalTheory.exists_pow_ne_one_mod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:45:48.729185+00:00
-- url     : https://prove2.me/submissions/bf408baf-24d5-4a4f-8d21-7bd2da18ee1c

import Definitions.Def_Formalism_PairingDivisors_StatementN
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_CmValuesMinPadicValBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Formalism.PairingDivisionLocalBalance
namespace GlobalTheory
theorem _root_.solution (l n : ℕ) (hl : l.Prime) (hn : ¬ (l - 1) ∣ n) :
    ∃ a : ℕ, 2 ≤ a ∧ a.Coprime l ∧ ¬ l ∣ a ^ n - 1 := by
  haveI := Fact.mk hl
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod l)ˣ)
  have hord : orderOf g = l - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
      Nat.totient_prime hl]
  refine ⟨(g : ZMod l).val, ?_, ZMod.val_coe_unit_coprime g, ?_⟩
  · by_contra h
    push_neg at h
    interval_cases hv : (g : ZMod l).val
    · have : (g : ZMod l) = 0 := (ZMod.val_eq_zero _).mp hv
      exact (Units.ne_zero g) this
    · have h1 : (g : ZMod l) = 1 := by
        rw [← ZMod.natCast_zmod_val (g : ZMod l), hv, Nat.cast_one]
      have : g = 1 := Units.ext h1
      rw [this, orderOf_one] at hord
      exact hn (by rw [← hord]; exact one_dvd n)
  · intro hdvd
    have hpos : 1 ≤ (g : ZMod l).val ^ n := by
      apply Nat.one_le_pow
      rw [Nat.pos_iff_ne_zero, Ne, ZMod.val_eq_zero]
      exact Units.ne_zero g
    have h0 : (((g : ZMod l).val ^ n - 1 : ℕ) : ZMod l) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
    rw [Nat.cast_sub hpos, Nat.cast_pow, ZMod.natCast_zmod_val, Nat.cast_one, sub_eq_zero] at h0
    have hgn : g ^ n = 1 := Units.ext (by simpa using h0)
    exact hn (hord ▸ orderOf_dvd_of_pow_eq_one hgn)
end GlobalTheory
