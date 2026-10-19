-- Prove2me | solution 1 for OAI.CirculantHadamard.sum_odd_sq_mod_eight
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T09:38:17.129976+00:00
-- url     : https://prove2.me/submissions/b6872d0c-0d6f-4136-911c-68b8bfd47926

import Mathlib

theorem solution {ι : Type*} (s : Finset ι) (a : ι → ℤ)
    (ha : ∀ i ∈ s, Odd (a i)) :
    Int.ModEq 8 (∑ i ∈ s, a i ^ 2) (s.card : ℤ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih =>
    rw [Finset.sum_insert hx, Finset.card_insert_of_notMem hx]
    have h1 := ih (fun i hi => ha i (Finset.mem_insert_of_mem hi))
    obtain ⟨k, hk⟩ := ha x (Finset.mem_insert_self _ _)
    have h2 : a x ^ 2 ≡ 1 [ZMOD 8] := by
      rw [hk, Int.ModEq]
      have : (2 * k + 1) ^ 2 = 8 * (k * (k + 1) / 2) + 1 := by
        have hdiv : 2 ∣ k * (k + 1) := by
          rcases Int.even_or_odd k with ⟨m, hm⟩ | ⟨m, hm⟩ <;> subst hm
          · exact ⟨m * (m + m + 1), by ring⟩
          · exact ⟨(2 * m + 1) * (m + 1), by ring⟩
        obtain ⟨q, hq⟩ := hdiv
        rw [hq, Int.mul_ediv_cancel_left _ (by norm_num)]
        nlinarith [hq]
      rw [this]; omega
    push_cast
    have := h2.add h1
    simpa [add_comm] using this
