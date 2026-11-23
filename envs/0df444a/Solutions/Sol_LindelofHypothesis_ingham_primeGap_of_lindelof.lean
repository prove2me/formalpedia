-- Prove2me | solution 1 for LindelofHypothesis.ingham_primeGap_of_lindelof
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:23:55.862102+00:00
-- url     : https://prove2.me/submissions/6aa5c204-6332-4659-8f35-e34d2bb6646a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_RiemannVonMangoldt_ZeroCounts
import Definitions.Def_LindelofHypothesis_GrowthAndZeroCounts
import Theorems.Thm_mathlib_riemannHypothesis
import Theorems.Thm_Cramer_primeGap_isBigO_sqrt_mul_log_sq_of_riemannHypothesis

open Complex Filter Asymptotics
open scoped ENNReal

namespace LindelofHypothesis
end LindelofHypothesis
open LindelofHypothesis
theorem solution (hL : RiemannVonMangoldt.LindelofHypothesis)
    (ε : ℝ) (hε : 0 < ε) :
    (fun n : ℕ => (primeGap n : ℝ)) =O[atTop] (fun n : ℕ => (Nat.nth Nat.Prime n : ℝ) ^ (1 / 2 + ε)) :=
  by
  -- Cramér's bound under the Riemann hypothesis: g_n = O(√p_n · log² p_n).
  have hC := Cramer.primeGap_isBigO_sqrt_mul_log_sq_of_riemannHypothesis mathlib_riemannHypothesis
  -- log² x = o(x^ε) as x → ∞.
  have hlog : (fun x : ℝ => Real.log x ^ 2) =o[atTop] (fun x : ℝ => x ^ ε) :=
    (isLittleO_log_rpow_rpow_atTop 2 hε).congr_left (fun x => Real.rpow_two (Real.log x))
  -- √x · log² x = O(x^(1/2+ε)) as x → ∞.
  have hreal : (fun x : ℝ => Real.sqrt x * Real.log x ^ 2) =O[atTop]
      (fun x : ℝ => x ^ (1 / 2 + ε)) := by
    refine ((isBigO_refl (fun x : ℝ => Real.sqrt x) atTop).mul hlog.isBigO).trans_eventuallyEq ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [Real.sqrt_eq_rpow, Real.rpow_add hx]
  -- p_n → ∞.
  have hp : Tendsto (fun n : ℕ => (Nat.nth Nat.Prime n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp
      (Nat.nth_strictMono Nat.infinite_setOfPred_prime).tendsto_atTop
  exact hC.trans (hreal.comp_tendsto hp)
