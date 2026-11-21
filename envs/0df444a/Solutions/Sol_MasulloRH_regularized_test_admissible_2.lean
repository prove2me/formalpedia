-- Prove2me | solution 2 for MasulloRH.regularized_test_admissible
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-20T22:09:29.237692+00:00
-- url     : https://prove2.me/submissions/d1bdfcb3-3f10-4395-8ed0-22b0b9c84251

import Definitions.Def_MasulloRH_RegularizedTrace
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

open Set Filter MasulloRH
open scoped Topology ContDiff

theorem solution (n : ℕ) (s : ℂ) :
    IsRationalTraceTest (regularizedTraceTest n s) := by
  let N : ℝ := n + 1
  have hN : 0 < N := by dsimp [N]; positivity
  let a := Real.exp (1 / N)
  let b := Real.exp (2 * N)
  have ha : 1 < a := Real.one_lt_exp_iff.mpr (by positivity)
  have leftZero {x : ℝ} (hx : x < a) : regularizedTraceTest n s x = 0 := by
    by_cases h : 1 < x
    · have hl : Real.log x < 1 / N := by simpa [a] using Real.log_lt_log (by linarith : 0 < x) hx
      have hm := (lt_div_iff₀ hN).1 hl
      have hz : N * Real.log x - 1 ≤ 0 := by linarith [mul_comm N (Real.log x)]
      simp [regularizedTraceTest, traceLogCutoff, h, Real.smoothTransition.zero_of_nonpos (show ((n : ℝ) + 1) * Real.log x - 1 ≤ 0 from hz)]
    · simp [regularizedTraceTest, h]
  have rightZero {x : ℝ} (hx : b < x) : regularizedTraceTest n s x = 0 := by
    have hb : 1 < b := Real.one_lt_exp_iff.mpr (by positivity)
    have h := hb.trans hx
    have hl : 2 * N < Real.log x := by simpa [b] using Real.log_lt_log (Real.exp_pos _) hx
    have hm : 2 ≤ Real.log x / N := (le_div_iff₀ hN).2 hl.le
    have ho : 1 ≤ Real.log x / N - 1 := by linarith
    simp [regularizedTraceTest, traceLogCutoff, h, Real.smoothTransition.one_of_one_le (show 1 ≤ Real.log x / ((n : ℝ) + 1) - 1 from ho)]
  have hsupport : tsupport (regularizedTraceTest n s) ⊆ Icc a b := by
    refine closure_minimal ?_ isClosed_Icc
    intro x hx
    exact ⟨le_of_not_gt (fun h => hx (leftZero h)), le_of_not_gt (fun h => hx (rightZero h))⟩
  refine ⟨contDiff_iff_contDiffAt.mpr ?_, isCompact_Icc.of_isClosed_subset
    (isClosed_tsupport _) hsupport, fun x hx => lt_of_lt_of_le (Real.exp_pos _) (hsupport hx).1, leftZero ha⟩
  intro x
  by_cases h : 1 < x
  · have hx : 0 < x := by linarith
    have hl : ContDiffAt ℝ ∞ Real.log x := Real.contDiffAt_log.mpr hx.ne'
    have hlogC : ContDiffAt ℝ ∞ (fun t : ℝ => (Real.log t : ℂ)) x :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp x hl
    have hpow (z : ℂ) : ContDiffAt ℝ ∞ (fun t : ℝ => (t : ℂ) ^ z) x := by
      have he : ContDiffAt ℝ ∞ (fun t : ℝ => Complex.exp ((Real.log t : ℂ) * z)) x := by
        fun_prop
      apply he.congr_of_eventuallyEq
      filter_upwards [lt_mem_nhds hx] with t ht
      rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast ht.ne' : (t : ℂ) ≠ 0), Complex.ofReal_log ht.le]
    have hd : ContDiffAt ℝ ∞ (fun t : ℝ =>
        ((Real.smoothTransition (N * Real.log t - 1) *
          (1 - Real.smoothTransition (Real.log t / N - 1)) : ℝ) : ℂ) *
          ((t : ℂ) ^ (1 / 2 - s) - (t : ℂ) ^ (-2 : ℂ))) x := by
      refine ContDiffAt.mul ?_ ((hpow _).sub (hpow _))
      have hr : ContDiffAt ℝ ∞ (fun t : ℝ => Real.smoothTransition (N * Real.log t - 1) *
          (1 - Real.smoothTransition (Real.log t / N - 1))) x := by
        fun_prop (disch := positivity)
      exact Complex.ofRealCLM.contDiff.contDiffAt.comp x hr
    apply hd.congr_of_eventuallyEq
    filter_upwards [lt_mem_nhds h] with t ht
    simp [regularizedTraceTest, traceLogCutoff, ht, N]
  · have hx : x < a := (le_of_not_gt h).trans_lt ha
    apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
    filter_upwards [gt_mem_nhds hx] with t ht
    exact leftZero ht
