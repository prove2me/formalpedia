-- Prove2me | solution 1 for IllinoisBrick.Cartel.supply_chain_profit
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T01:37:39.897858+00:00
-- url     : https://prove2.me/submissions/02711a66-097e-4a07-a814-80926605daba

import Mathlib
import Definitions.Def_IllinoisBrick_Cartel_Model

open IllinoisBrick.Cartel in
theorem solution (a b c : ℝ) (h : Standing a b c) :
    (∀ (k : Contract) (v : Fin 2 → Terms) (q : Fin 2 → ℝ),
      retailerProfit a b c k v q 0 + retailerProfit a b c k v q 1 +
          manufacturerProfit a b c k v q 0 + manufacturerProfit a b c k v q 1 =
        (a - b * (q 0 + q 1) - c) * (q 0 + q 1)) ∧
    ∀ Q : ℝ, 2 * (a - c) / (3 * b) ≤ Q → (a - b * Q - c) * Q ≤ 2 * (a - c) ^ 2 / (9 * b) := by
  obtain ⟨hb, hac⟩ := h
  refine ⟨?_, ?_⟩
  · intro k v q
    unfold retailerProfit manufacturerProfit revenue
    ring
  · intro Q hQ
    rw [div_le_iff₀ (by linarith)] at hQ
    rw [le_div_iff₀ (by linarith)]
    have h1 : 0 ≤ 3 * (b * Q) - (a - c) := by nlinarith
    have h2 : 0 ≤ 3 * (b * Q) - 2 * (a - c) := by nlinarith
    nlinarith [mul_nonneg h1 h2]
