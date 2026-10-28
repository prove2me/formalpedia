-- Prove2me | solution 1 for MajorityAttack.NegCost.not_binding
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T01:02:49.048786+00:00
-- url     : https://prove2.me/submissions/244652b5-4ffa-49d8-9549-2a7d4c245356

import Mathlib
import Definitions.Def_MajorityAttack_NegCost_Model

open MajorityAttack.NegCost in
theorem solution (τ H L ρ ρt : ℝ) (c : ℝ → ℝ) (htil hstar : ℝ)
    (hτ : 0 < τ) (hH : 0 < H) (hL : 0 < L) (hreward : ρ < ρt)
    (hopt : IsAttackOptimum (τ * H) ρt c htil)
    (hhstar : 0 < hstar) (hbound : minAttackPower H hstar ≤ htil) :
    netCost τ H L ρ ρt c htil hstar < 0 := by
  unfold netCost
  rw [max_eq_left hbound]
  have hmax : flowProfit (τ * H) ρt c hstar ≤ flowProfit (τ * H) ρt c htil :=
    isMaxOn_iff.mp hopt.2 hstar (Set.mem_Ici.mpr hhstar.le)
  have hD : 0 < hstar / (τ * H) := div_pos hhstar (mul_pos hτ hH)
  have hlt : flowProfit (τ * H) ρ c hstar < flowProfit (τ * H) ρt c hstar := by
    unfold flowProfit
    have := mul_lt_mul_of_pos_left hreward hD
    linarith
  exact mul_neg_of_neg_of_pos (by linarith) hL
