-- Prove2me | solution 1 for IllinoisBrick.Cartel.proposition_2a
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T22:11:20.858956+00:00
-- url     : https://prove2.me/submissions/4bd455cf-2c24-4c19-bd91-36a9c54c3a2c

import Mathlib
import Definitions.Def_IllinoisBrick_Cartel_Model
import Theorems.Thm_IllinoisBrick_Cartel_proposition_1
import Theorems.Thm_IllinoisBrick_Cartel_retailer_profit_le
import Theorems.Thm_IllinoisBrick_Cartel_supply_chain_profit

open IllinoisBrick.Cartel

theorem solution (a b c : ℝ) (h : Standing a b c) (k : Contract) (hk : k ≠ Contract.WPFF)
    (qC : Fin 2 → ℝ) (hqC : IsRetailerEq a b c k (fun _ => competitiveTerms a b c k) qC)
    (v : Fin 2 → Terms) (hadm : ∀ j, Admissible c k (v j))
    (q : Fin 2 → ℝ) (hq : IsRetailerEq a b c k v q) :
    ¬ IsCartel a b c k v q qC := by
  rintro ⟨hC1, hC2⟩
  have hSC := supply_chain_profit a b c h
  obtain ⟨hb, hac⟩ := h
  have hP1 := (proposition_1 a b c ⟨hb, hac⟩ k).2 qC hqC
  have hle := retailer_profit_le a b c hb k hk v hadm q hq
  have hbig : ∀ i : Fin 2, (a - c) / (3 * b) ≤ q i := by
    intro i
    have h1 := hC2 i
    rw [(hP1 i).2.2] at h1
    have h2 := hle i
    have hqi : 0 ≤ q i := (hq.1 i).1
    have h3 : (a - c) ^ 2 ≤ (3 * b * q i) ^ 2 := by
      have := le_trans h1 h2
      rw [div_le_iff₀ (by linarith)] at this
      nlinarith
    rw [div_le_iff₀ (by linarith)]
    nlinarith [h3, mul_nonneg hb.le hqi]
  have hm : ∀ j : Fin 2, 0 < manufacturerProfit a b c k v q j := by
    intro j; have := hC1 j; rw [(hP1 j).2.1] at this; exact this
  have hr : ∀ i : Fin 2, (a - c) ^ 2 / (9 * b) ≤ retailerProfit a b c k v q i := by
    intro i; have := hC2 i; rw [(hP1 i).2.2] at this; exact this
  have htot := hSC.1 k v q
  set Q := q 0 + q 1 with hQ
  have hQb : 2 * (a - c) / (3 * b) ≤ Q := by
    have := hbig 0; have := hbig 1
    rw [hQ, mul_div_assoc]; linarith
  -- the supply-chain profit at `Q ≥ 2(a-c)/(3b)` is at most `2(a-c)²/(9b)`
  have hcap : (a - b * Q - c) * Q ≤ 2 * (a - c) ^ 2 / (9 * b) := hSC.2 Q hQb
  have := hm 0; have := hm 1; have := hr 0; have := hr 1
  have e : 2 * (a - c) ^ 2 / (9 * b) = (a - c) ^ 2 / (9 * b) + (a - c) ^ 2 / (9 * b) := by ring
  linarith

