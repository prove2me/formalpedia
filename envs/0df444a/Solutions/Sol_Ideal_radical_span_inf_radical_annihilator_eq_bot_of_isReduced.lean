-- Prove2me | solution 1 for Ideal.radical_span_inf_radical_annihilator_eq_bot_of_isReduced
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/359cf95f-7fe4-5530-8396-bcba90f6ab45

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Ideal_radical_span_inf_radical_annihilator_eq_bot_of_isReduced

set_option autoImplicit false

namespace Ws23MilnorSplit

variable {S : Type*} [CommRing S]

theorem eq_zero_of_pow_eq_mul_of_pow_mul_eq_zero [IsReduced S] {a x t : S} {n m : ℕ}
    (hn : x ^ n = a * t) (hm : x ^ m * a = 0) : x = 0 := by
  apply IsNilpotent.eq_zero
  refine ⟨m + n, ?_⟩
  rw [pow_add, hn, ← mul_assoc, hm, zero_mul]

theorem mul_eq_zero_of_pow_mul_mul_eq_zero [IsReduced S] {a s : S} {m : ℕ}
    (hm : (a * s) ^ m * a = 0) : a * s = 0 := by
  apply IsNilpotent.eq_zero
  refine ⟨m + 1, ?_⟩
  rw [pow_succ, ← mul_assoc, hm, zero_mul]

theorem mem_annihilator_span_singleton_iff (a r : S) :
    r ∈ (Ideal.span {a} : Submodule S S).annihilator ↔ r * a = 0 := by
  rw [Submodule.mem_annihilator_span_singleton, smul_eq_mul]

theorem radical_span_inf_radical_annihilator_eq_bot [IsReduced S] (a : S) :
    (Ideal.span {a}).radical ⊓ ((Ideal.span {a} : Submodule S S).annihilator).radical = ⊥ ∧
    ∀ s : S, a * s ∈ ((Ideal.span {a} : Submodule S S).annihilator).radical →
      s ∈ ((Ideal.span {a} : Submodule S S).annihilator).radical := by
  constructor
  · rw [eq_bot_iff]
    rintro x ⟨hx1, hx2⟩
    rw [Ideal.mem_bot]
    obtain ⟨n, hn⟩ := (Ideal.mem_radical_iff).mp hx1
    obtain ⟨m, hm⟩ := (Ideal.mem_radical_iff).mp hx2
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp hn
    rw [mem_annihilator_span_singleton_iff] at hm
    exact eq_zero_of_pow_eq_mul_of_pow_mul_eq_zero (n := n) (m := m) (by rw [← ht, mul_comm]) hm
  · intro s hs
    obtain ⟨m, hm⟩ := (Ideal.mem_radical_iff).mp hs
    rw [mem_annihilator_span_singleton_iff] at hm
    have h0 : a * s = 0 := mul_eq_zero_of_pow_mul_mul_eq_zero hm
    exact Ideal.le_radical (by rw [mem_annihilator_span_singleton_iff, mul_comm]; exact h0)

end Ws23MilnorSplit

theorem solution
    {S : Type} [CommRing S] [IsReduced S] (a : S) :
    (Ideal.span {a}).radical ⊓ ((Ideal.span {a}).annihilator).radical = ⊥ ∧
      ∀ s : S, a * s ∈ ((Ideal.span {a}).annihilator).radical →
        s ∈ ((Ideal.span {a}).annihilator).radical :=
  Ws23MilnorSplit.radical_span_inf_radical_annihilator_eq_bot a

end S_Ideal_radical_span_inf_radical_annihilator_eq_bot_of_isReduced
end P2MW
export P2MW.S_Ideal_radical_span_inf_radical_annihilator_eq_bot_of_isReduced (solution)
