-- Prove2me | solution 1 for LeanEval.NumberTheory.riemann_hypothesis_iff_lagarias_elementary_criterion
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Wenqian Xing
-- created : 2026-09-06T08:06:52.075116+00:00
-- url     : https://prove2.me/submissions/f19cf6bd-2d72-4088-a55c-ad26b708a5d5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_LeanEval_NumberTheory_LagariasElementaryCriterion
import Theorems.Thm_LeanEval_NumberTheory_lagarias_harmonic_lower_bound
import Theorems.Thm_LeanEval_NumberTheory_lagarias_harmonic_upper_bound
import Theorems.Thm_LeanEval_NumberTheory_lagarias_finite_range
import Theorems.Thm_LeanEval_NumberTheory_lagarias_robin_upper_bound
import Theorems.Thm_LeanEval_NumberTheory_lagarias_robin_oscillation
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

set_option autoImplicit false
open LeanEval.NumberTheory Filter
open scoped ArithmeticFunction.sigma Topology

/-- Lagarias's equivalence, with the two Robin theorems as explicit dependencies. -/
theorem solution : RiemannHypothesis ↔ LagariasElementaryCriterion := by
  constructor
  · intro hRH n hn
    by_cases hb : n ≤ 5040
    · exact (lagarias_finite_range n hn hb).1
    · have hn₁ : 5041 ≤ n := by omega
      have hu := lagarias_robin_upper_bound hRH n hn₁
      have hl := lagarias_harmonic_lower_bound n (by omega)
      have hH : 0 ≤ (harmonic n : ℝ) := by unfold harmonic; positivity
      linarith
  · intro hcrit
    by_contra hRH
    obtain ⟨β,C,hβ₀,hβ₁,hC,hosc⟩ := lagarias_robin_oscillation hRH
    have htlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    have htloglog : Tendsto (fun n : ℕ => Real.log (Real.log (n : ℝ))) atTop atTop :=
      Real.tendsto_log_atTop.comp htlog
    have htpow : Tendsto (fun n : ℕ => C * (Real.log (n : ℝ)) ^ (1-β)) atTop atTop :=
      ((tendsto_rpow_atTop (by linarith : 0 < 1-β)).comp htlog).const_mul_atTop hC
    have hev : ∀ᶠ n : ℕ in atTop,
        20 ≤ n ∧ 1 ≤ Real.log (Real.log (n : ℝ)) ∧
          7 < C * (Real.log (n : ℝ)) ^ (1-β) :=
      (eventually_ge_atTop 20).and
        ((htloglog.eventually (eventually_ge_atTop 1)).and
          (htpow.eventually (eventually_gt_atTop 7)))
    obtain ⟨N,hN⟩ := eventually_atTop.mp hev
    obtain ⟨n,hnN,hn₃,hlo⟩ := hosc N
    obtain ⟨hn₂₀,hloglog,hlarge⟩ := hN n hnN
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
    have hxpos : 0 < Real.log (n : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < n by omega))
    have hpowpos : 0 < (Real.log (n : ℝ)) ^ β := Real.rpow_pos_of_pos hxpos β
    have hupper := lagarias_harmonic_upper_bound n hn₂₀
    have hbound := hcrit n (by omega)
    simp only [Real.rpow_eq_pow] at hlo
    have herr : C * (n : ℝ) * Real.log (Real.log (n : ℝ)) /
        (Real.log (n : ℝ)) ^ β ≤ 7 * (n : ℝ) / Real.log (n : ℝ) := by linarith
    have hmul := (div_le_div_iff₀ hpowpos hxpos).mp herr
    have hsmall : C * Real.log (n : ℝ) ≤ 7 * (Real.log (n : ℝ)) ^ β := by
      apply (mul_le_mul_iff_right₀ hnpos).mp
      calc
        (n : ℝ) * (C * Real.log (n : ℝ)) =
            C * n * 1 * Real.log (n : ℝ) := by ring
        _ ≤ C * n * Real.log (Real.log (n : ℝ)) * Real.log (n : ℝ) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hloglog (mul_nonneg hC.le hnpos.le)) hxpos.le
        _ ≤ _ := hmul
        _ = (n : ℝ) * (7 * (Real.log (n : ℝ)) ^ β) := by ring
    have hreverse : 7 * (Real.log (n : ℝ)) ^ β < C * Real.log (n : ℝ) := by
      calc
        _ < (C * (Real.log (n : ℝ)) ^ (1-β)) * (Real.log (n : ℝ)) ^ β :=
          mul_lt_mul_of_pos_right hlarge hpowpos
        _ = _ := by
          rw [mul_assoc,← Real.rpow_add hxpos,sub_add_cancel,Real.rpow_one]
    exact (not_lt_of_ge hsmall) hreverse
