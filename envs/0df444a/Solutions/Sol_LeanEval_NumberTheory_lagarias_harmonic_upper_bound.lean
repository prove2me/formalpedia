-- Prove2me | solution 1 for LeanEval.NumberTheory.lagarias_harmonic_upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T03:39:36.797559+00:00
-- url     : https://prove2.me/submissions/a578ece5-74ee-4cd8-97da-9fedc8af98bc

import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Harmonic.Defs
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic

open scoped ArithmeticFunction.sigma

set_option autoImplicit false

theorem solution (n : ℕ) (hn : 20 ≤ n) :
    (harmonic n : ℝ) +
      Real.exp (harmonic n : ℝ) * Real.log (harmonic n : ℝ) ≤
      Real.exp Real.eulerMascheroniConstant * (n : ℝ) * Real.log (Real.log (n : ℝ)) +
        7 * (n : ℝ) / Real.log (n : ℝ) := by
  let N : ℝ := n
  let t : ℝ := Real.log N
  let H : ℝ := harmonic n
  let E : ℝ := Real.exp Real.eulerMascheroniConstant
  have hn0 : n ≠ 0 := by omega
  have hN : 20 ≤ N := by change (20 : ℝ) ≤ (n : ℝ); exact_mod_cast hn
  have hNpos : 0 < N := by linarith
  have he2 : Real.exp (2 : ℝ) < 9 := by
    have he1 := Real.exp_one_lt_three
    have he0 := Real.exp_pos (1 : ℝ)
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    nlinarith
  have ht2 : 2 ≤ t := (Real.le_log_iff_exp_le hNpos).2 (by linarith)
  have htpos : 0 < t := by linarith
  have hlogt : 0 ≤ Real.log t := Real.log_nonneg (by linarith)
  have hHup : H ≤ t + 1 := by
    simpa [H, t, N, add_comm] using harmonic_le_one_add_log n
  have hgamma : 0 < Real.eulerMascheroniConstant := by
    linarith [Real.one_half_lt_eulerMascheroniConstant]
  have hmain : Real.eulerMascheroniConstant < H - t := by
    simpa [H, t, N, Real.eulerMascheroniSeq', hn0] using
      Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' n
  have hHpos : 0 < H := by linarith
  have hHone : 1 ≤ H := by linarith
  have hlogH0 : 0 ≤ Real.log H := Real.log_nonneg hHone
  have hEpos : 0 < E := Real.exp_pos _
  have hE3 : E ≤ 3 := by
    have hg1 : Real.eulerMascheroniConstant ≤ 1 := by
      linarith [Real.eulerMascheroniConstant_lt_two_thirds]
    exact (Real.exp_le_exp.mpr hg1).trans Real.exp_one_lt_three.le
  have hseq : H - Real.log (N + 1) ≤ Real.eulerMascheroniConstant := by
    simpa [H, N, Real.eulerMascheroniSeq] using
      (Real.eulerMascheroniSeq_lt_eulerMascheroniConstant n).le
  have hexpH : Real.exp H ≤ E * (N + 1) := by
    calc
      Real.exp H ≤ Real.exp (Real.eulerMascheroniConstant + Real.log (N + 1)) :=
        Real.exp_le_exp.mpr (by linarith)
      _ = E * (N + 1) := by rw [Real.exp_add, Real.exp_log (by linarith)]
  have hlogH : Real.log H ≤ Real.log t + 1 / t := by
    have hr := Real.log_le_sub_one_of_pos (div_pos hHpos htpos)
    rw [Real.log_div hHpos.ne' htpos.ne'] at hr
    have hratio : H / t - 1 ≤ 1 / t := by
      apply (sub_le_iff_le_add).2
      apply (div_le_iff₀ htpos).2
      field_simp
      nlinarith
    linarith
  have htN : t ^ 2 + t ≤ N := by
    have hs := Real.sum_le_exp_of_nonneg htpos.le 5
    norm_num [Finset.sum_range_succ, Nat.factorial_succ] at hs
    have hexpt : Real.exp t = N := Real.exp_log hNpos
    rw [hexpt] at hs
    have hc : 0 ≤ t ^ 2 * ((t - 2) * (t + 6)) :=
      mul_nonneg (sq_nonneg t) (mul_nonneg (by linarith) (by linarith))
    nlinarith
  have htl : t * Real.log t ≤ N - 1 := by
    have hl := Real.log_le_sub_one_of_pos htpos
    have hm := mul_le_mul_of_nonneg_left hl htpos.le
    nlinarith
  have hC0 : 0 ≤ t * Real.log t + N + 1 := by positivity
  have herror : E * (t * Real.log t + N + 1) ≤ 6 * N := by
    have hmul := mul_le_mul_of_nonneg_right hE3 hC0
    nlinarith
  have hproduct : Real.exp H * Real.log H ≤ E * N * Real.log t + 6 * N / t := by
    calc
      Real.exp H * Real.log H ≤ E * (N + 1) * (Real.log t + 1 / t) :=
        mul_le_mul hexpH hlogH hlogH0 (by positivity)
      _ = E * N * Real.log t + (E * (t * Real.log t + N + 1)) / t := by
        field_simp
        ring
      _ ≤ E * N * Real.log t + 6 * N / t :=
        add_le_add_right (div_le_div_of_nonneg_right herror htpos.le) _
  have hHsmall : H ≤ N / t := by
    apply (le_div_iff₀ htpos).2
    have hm := mul_le_mul_of_nonneg_right hHup htpos.le
    nlinarith
  change H + Real.exp H * Real.log H ≤ E * N * Real.log t + 7 * N / t
  calc
    H + Real.exp H * Real.log H ≤ N / t + (E * N * Real.log t + 6 * N / t) :=
      add_le_add hHsmall hproduct
    _ = E * N * Real.log t + 7 * N / t := by ring
