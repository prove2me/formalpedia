-- Prove2me | solution 1 for GlobalTheory.Hk.LogDeriv.norm_ge_of_conv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:11:49.046692+00:00
-- url     : https://prove2.me/submissions/2583e02f-c288-4234-9f18-90210b6d8956

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassLFunctionFamilyContinuationGrowth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_TsumOneDivRpowLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassFamilyLogDerivReGtOne
import Theorems.Thm_GlobalTheory_Hk_LogDeriv_absc_div_lt
import Theorems.Thm_GlobalTheory_Hk_LogDeriv_eq_exp_of_conv
import Theorems.Thm_GlobalTheory_Hk_LogDeriv_summable_of_le
import Theorems.Thm_GlobalTheory_LLower_norm_LSeries_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical
open GlobalTheory GlobalTheory.Hk GlobalTheory.Hk.LogDeriv
open LSeries
open scoped LSeries.notation
namespace GlobalTheory.Hk.LogDeriv
theorem _root_.solution {a l : ℕ → ℂ} (ha : ∀ s : ℂ, 1 < s.re → LSeriesSummable a s)
    (hl : ∀ n, ‖l n‖ ≤ 2 * Λ n) (a1 : a 1 = 1)
    (hc : ∀ n : ℕ, n ≠ 0 → Complex.log n * a n = (l ⍟ a) n) {s : ℂ} (hs : 1 < s.re) :
    ((s.re - 1) / s.re) ^ 2 ≤ ‖LSeries a s‖ := by
  have l1 : l 1 = 0 := by simpa using hl 1
  have hl' : ∀ z : ℂ, 1 < z.re → LSeriesSummable l z := fun z hz => summable_of_le hl z hz
  have hΛs : ∀ z : ℂ, 1 < z.re → LSeriesSummable (↗Λ) z := fun z hz =>
    LSeriesSummable_vonMangoldt hz
  have h1s : ∀ z : ℂ, 1 < z.re → LSeriesSummable (1 : ℕ → ℂ) z := fun z hz =>
    LSeriesSummable_one_iff.mpr hz
  have hΛ1 : (↗Λ) 1 = 0 := by simp
  have hcz : ∀ n : ℕ, n ≠ 0 → Complex.log n * (1 : ℕ → ℂ) n = ((↗Λ) ⍟ (1 : ℕ → ℂ)) n := by
    intro n _
    rw [LSeries.convolution_def]
    simp only [Pi.one_apply, mul_one]
    rw [Nat.sum_divisorsAntidiagonal (fun x _ => ((Λ x : ℝ) : ℂ)), ← Complex.ofReal_sum,
      vonMangoldt_sum, Complex.natCast_log]
  have hσc : 1 < ((s.re : ℝ) : ℂ).re := by simpa using hs
  have hζ := eq_exp_of_conv h1s hΛs (by simp) hΛ1 hcz hσc
  have hA := eq_exp_of_conv ha hl' a1 l1 hc hs

  set t : ℕ → ℂ := fun n => LSeries.term (fun n => (↗Λ) n / Complex.log n) ((s.re : ℝ) : ℂ) n
    with ht
  have htn : ∀ n, t n = ((‖t n‖ : ℝ) : ℂ) := by
    intro n
    open ComplexOrder in
    (refine Complex.eq_coe_norm_of_nonneg (LSeries.term_nonneg ?_ s.re)
     show (0 : ℂ) ≤ ((Λ n : ℝ) : ℂ) / Complex.log n
     rw [← Complex.natCast_log, ← Complex.ofReal_div]
     exact Complex.zero_le_real.mpr (div_nonneg vonMangoldt_nonneg (Real.log_natCast_nonneg n)))
  have hts : Summable fun n => ‖t n‖ :=
    summable_norm_iff.mpr (LSeriesSummable_of_abscissaOfAbsConv_lt_re (absc_div_lt hΛ1 hΛs hσc))
  set R : ℝ := ∑' n, ‖t n‖ with hR
  have hZ : LSeries (fun n => (↗Λ) n / Complex.log n) ((s.re : ℝ) : ℂ) = (R : ℂ) := by
    show ∑' n, t n = _
    rw [tsum_congr htn, ← Complex.ofReal_tsum]
  have hζb : Real.exp R ≤ s.re / (s.re - 1) := by
    have hb := GlobalTheory.LLower.norm_LSeries_le (f := (1 : ℕ → ℂ)) (fun n => by simp) hσc
    rw [hζ, hZ, Complex.norm_exp, Complex.ofReal_re] at hb
    simpa using hb

  have hgs : Summable fun n => ‖LSeries.term (fun n => l n / Complex.log n) s n‖ :=
    summable_norm_iff.mpr (LSeriesSummable_of_abscissaOfAbsConv_lt_re (absc_div_lt l1 hl' hs))
  have hpt : ∀ n, ‖LSeries.term (fun n => l n / Complex.log n) s n‖ ≤ 2 * ‖t n‖ := by
    intro n
    simp only [ht, LSeries.norm_term_eq, Complex.ofReal_re]
    split_ifs
    · simp
    · rw [norm_div, norm_div, Complex.norm_of_nonneg vonMangoldt_nonneg, ← mul_div_assoc,
        ← mul_div_assoc]
      gcongr
      exact hl n
  have hGle : ‖LSeries (fun n => l n / Complex.log n) s‖ ≤ 2 * R := by
    calc ‖LSeries (fun n => l n / Complex.log n) s‖
        ≤ ∑' n, ‖LSeries.term (fun n => l n / Complex.log n) s n‖ := norm_tsum_le_tsum_norm hgs
      _ ≤ ∑' n, 2 * ‖t n‖ := hgs.tsum_le_tsum hpt (hts.mul_left 2)
      _ = 2 * R := hts.tsum_mul_left 2
  have hre : -(2 * R) ≤ (LSeries (fun n => l n / Complex.log n) s).re := by
    have := Complex.abs_re_le_norm (LSeries (fun n => l n / Complex.log n) s)
    have := neg_abs_le (LSeries (fun n => l n / Complex.log n) s).re
    linarith
  have hs0 : 0 < s.re := by linarith
  have hs1 : 0 < s.re - 1 := by linarith
  have hR1 : (s.re - 1) / s.re ≤ Real.exp (-R) := by
    rw [Real.exp_neg, ← inv_div]
    exact inv_anti₀ (Real.exp_pos R) hζb
  calc ((s.re - 1) / s.re) ^ 2 ≤ Real.exp (-R) ^ 2 :=
        pow_le_pow_left₀ (div_nonneg hs1.le hs0.le) hR1 2
    _ = Real.exp (-(2 * R)) := by rw [sq, ← Real.exp_add]; ring_nf
    _ ≤ Real.exp (LSeries (fun n => l n / Complex.log n) s).re := Real.exp_le_exp.mpr hre
    _ = ‖LSeries a s‖ := by rw [hA, Complex.norm_exp]
end GlobalTheory.Hk.LogDeriv
