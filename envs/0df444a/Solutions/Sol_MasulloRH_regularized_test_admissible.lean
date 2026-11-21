-- Prove2me | solution 1 for MasulloRH.regularized_test_admissible
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-20T22:03:02.707893+00:00
-- url     : https://prove2.me/submissions/3c775568-c331-449c-91b2-a719ada60997

import Definitions.Def_MasulloRH_RegularizedTrace

set_option autoImplicit false

open MasulloRH Set Filter
open scoped Topology ContDiff

private theorem smooth_real_cpow {x : ℝ} (hx : 0 < x) (c : ℂ) :
    ContDiffAt ℝ ∞ (fun t : ℝ => (t : ℂ) ^ c) x := by
  have hlog : ContDiffAt ℝ ∞ Real.log x := Real.contDiffAt_log.mpr hx.ne'
  have h : ContDiffAt ℝ ∞ (fun t : ℝ => Complex.exp ((Real.log t : ℂ) * c)) x :=
    ((Complex.ofRealCLM.contDiff.contDiffAt.comp x hlog).mul contDiffAt_const).cexp
  apply h.congr_of_eventuallyEq
  filter_upwards [lt_mem_nhds hx] with t ht
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr ht.ne'), Complex.ofReal_log ht.le]

theorem solution (n : ℕ) (s : ℂ) :
    IsRationalTraceTest (regularizedTraceTest n s) := by
  let N : ℝ := n + 1
  have hN : 0 < N := by dsimp [N]; positivity
  have hL : 1 < Real.exp (1 / N) := Real.one_lt_exp_iff.mpr (by positivity)
  have hleft {t : ℝ} (ht : t < Real.exp (1 / N)) : regularizedTraceTest n s t = 0 := by
    by_cases h : 1 < t
    · have hl := (Real.log_lt_iff_lt_exp (zero_lt_one.trans h)).mpr ht
      have harg : N * Real.log t - 1 ≤ 0 := by
        have := (lt_div_iff₀ hN).mp hl
        linarith [mul_comm N (Real.log t)]
      dsimp only [N] at harg
      simp [regularizedTraceTest, traceLogCutoff, h, Real.smoothTransition.zero_of_nonpos harg]
    · simp [regularizedTraceTest, h]
  have hsupp : tsupport (regularizedTraceTest n s) ⊆ Icc 1 (Real.exp (2 * N)) := by
    apply closure_minimal _ isClosed_Icc
    intro t ht
    change regularizedTraceTest n s t ≠ 0 at ht
    have h : 1 < t := by
      by_contra! h
      exact ht (hleft (h.trans_lt hL))
    refine ⟨h.le, ?_⟩
    by_contra! hhi
    have hl := (Real.lt_log_iff_exp_lt (zero_lt_one.trans h)).mpr hhi
    have harg : 1 ≤ Real.log t / N - 1 := by
      linarith [(lt_div_iff₀ hN).mpr hl]
    dsimp only [N] at harg
    exact ht (by simp [regularizedTraceTest, traceLogCutoff, h, Real.smoothTransition.one_of_one_le harg])
  refine ⟨contDiff_iff_contDiffAt.mpr ?_, isCompact_Icc.of_isClosed_subset
    (isClosed_tsupport _) hsupp, fun t ht => zero_lt_one.trans_le (hsupp ht).1, ?_⟩
  · intro x
    by_cases hx : 1 < x
    · have hlog : ContDiffAt ℝ ∞ Real.log x :=
        Real.contDiffAt_log.mpr (zero_lt_one.trans hx).ne'
      have hcut : ContDiffAt ℝ ∞ (fun t : ℝ =>
          Real.smoothTransition (N * Real.log t - 1) *
          (1 - Real.smoothTransition (Real.log t / N - 1))) x :=
        (Real.smoothTransition.contDiffAt.comp x (contDiffAt_const.mul hlog |>.sub contDiffAt_const)).mul
          (contDiffAt_const.sub (Real.smoothTransition.contDiffAt.comp x
            ((hlog.div_const N).sub contDiffAt_const)))
      have hpow := (smooth_real_cpow (zero_lt_one.trans hx) (1 / 2 - s)).sub
        (smooth_real_cpow (zero_lt_one.trans hx) (-2))
      apply ((Complex.ofRealCLM.contDiff.contDiffAt.comp x hcut).mul hpow).congr_of_eventuallyEq
      filter_upwards [lt_mem_nhds hx] with t ht
      simp [regularizedTraceTest, traceLogCutoff, ht, N]
    · apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
      filter_upwards [gt_mem_nhds ((le_of_not_gt hx).trans_lt hL)] with t ht
      exact hleft ht
  · simp [regularizedTraceTest]
