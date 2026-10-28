-- Prove2me | solution 1 for MarketFreeze.Hetero.eq_A9_indifference
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T01:50:27.019991+00:00
-- url     : https://prove2.me/submissions/0d21d059-f645-4feb-8e21-8a66b4dd7c78

import Mathlib
import Definitions.Def_MarketFreeze_Hetero_Model

open MarketFreeze.Hetero in
theorem solution (P : Params) (h0 : Standing P)
    (θ : ℝ) (hθ : θ ∈ Set.Icc 0 P.θbar) (n : ℝ) (hn : 0 < n) :
    (buyerProfit P θ n = sellerProfit P θ n ↔
      alpha P n * ((1 - θ) / 2 *
        (price P n - P.I - (P.X - price P n) / n) -
        P.ψ * (P.X - price P n) / n) = dPi P θ) ∧
    (buyerProfit P θ n = sellerProfit P θ n ↔ eq15LHS P θ n = dPi P θ) := by
  have hn0 : n ≠ 0 := hn.ne'
  have hn1 : 1 + n ≠ 0 := by positivity
  have hn1' : n + 1 ≠ 0 := by positivity
  have key1 : buyerProfit P θ n - sellerProfit P θ n = dPi P θ -
      alpha P n * ((1 - θ) / 2 *
        (price P n - P.I - (P.X - price P n) / n) -
        P.ψ * (P.X - price P n) / n) := by
    unfold buyerProfit sellerProfit icLHS dPi piS Ehet buyerMeet alpha price
    field_simp
    ring
  have key2 : alpha P n * ((1 - θ) / 2 *
        (price P n - P.I - (P.X - price P n) / n) -
        P.ψ * (P.X - price P n) / n) = eq15LHS P θ n := by
    unfold alpha price eq15LHS
    field_simp
    ring
  have base : buyerProfit P θ n = sellerProfit P θ n ↔
      alpha P n * ((1 - θ) / 2 *
        (price P n - P.I - (P.X - price P n) / n) -
        P.ψ * (P.X - price P n) / n) = dPi P θ := by
    constructor
    · intro h; linarith
    · intro h; linarith
  refine ⟨base, ?_⟩
  rw [base, key2]
