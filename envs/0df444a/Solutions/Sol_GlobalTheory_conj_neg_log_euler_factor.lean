-- Prove2me | solution 1 for GlobalTheory.conj_neg_log_euler_factor
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:13:11.656114+00:00
-- url     : https://prove2.me/submissions/c348bf6a-17b9-4979-9cfe-acfb72736eea

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_LandauSummableOfExpDirichletSeriesEntire
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_HasSumLogZetaSqMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_EulerProductNeZeroOneOfEntire
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical
open scoped ContDiff nonZeroDivisors
namespace GlobalTheory
open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical in
open scoped ContDiff nonZeroDivisors in
private lemma norm_mul_natCast_cpow_neg_le {n : ℕ} (hn : 2 ≤ n) {c : ℂ} (hc : ‖c‖ ≤ 1) (s : ℂ) :
    ‖c * (n : ℂ) ^ (-s)‖ ≤ (n : ℝ) ^ (-s.re) := by
  rw [norm_mul, Complex.norm_natCast_cpow_of_pos (by omega), neg_re]
  exact mul_le_of_le_one_left (by positivity) hc
open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical in
open scoped ContDiff nonZeroDivisors in
private lemma natCast_rpow_neg_le_half {n : ℕ} (hn : 2 ≤ n) {σ : ℝ} (hσ : 1 < σ) :
    (n : ℝ) ^ (-σ) ≤ 1 / 2 := by
  have h1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  calc (n : ℝ) ^ (-σ) ≤ (n : ℝ) ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_le h1 (by linarith)
    _ = 1 / n := by rw [Real.rpow_neg_one, one_div]
    _ ≤ 1 / 2 := by
        apply one_div_le_one_div_of_le (by norm_num)
        exact_mod_cast hn
end GlobalTheory
end

set_option autoImplicit false
open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical
open scoped ContDiff nonZeroDivisors
open GlobalTheory
open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical
open scoped ContDiff nonZeroDivisors
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution (n : ℕ) (hn : 2 ≤ n) (c : ℂ) (hc : ‖c‖ ≤ 1) (s : ℂ)
    (hs : 1 < s.re) :
    starRingEnd ℂ (-Complex.log (1 - c * (n : ℂ) ^ (-(starRingEnd ℂ s)))) =
      -Complex.log (1 - starRingEnd ℂ c * (n : ℂ) ^ (-s)) := by
  have hlt : ‖c * (n : ℂ) ^ (-(starRingEnd ℂ s))‖ < 1 :=
    ((norm_mul_natCast_cpow_neg_le hn hc (starRingEnd ℂ s)).trans
      (natCast_rpow_neg_le_half hn (by simpa using hs))).trans_lt (by norm_num)
  have hre : 0 < (1 - c * (n : ℂ) ^ (-(starRingEnd ℂ s))).re := by
    rw [sub_re, one_re]
    linarith [Complex.re_le_norm (c * (n : ℂ) ^ (-(starRingEnd ℂ s)))]
  have harg : (1 - c * (n : ℂ) ^ (-(starRingEnd ℂ s))).arg ≠ Real.pi := fun h => by
    have := (Complex.arg_eq_pi_iff.mp h).1
    linarith
  have hconj : starRingEnd ℂ ((n : ℂ) ^ (-(starRingEnd ℂ s))) = (n : ℂ) ^ (-s) := by
    have := Complex.cpow_conj (n : ℂ) (-s) (by rw [Complex.natCast_arg]; exact Real.pi_ne_zero.symm)
    rw [map_neg] at this
    rw [this, Complex.conj_conj, Complex.conj_natCast]
  rw [map_neg, ← Complex.log_conj _ harg, map_sub, map_one, map_mul, hconj]
end _root_.GlobalTheory
end GlobalTheory
