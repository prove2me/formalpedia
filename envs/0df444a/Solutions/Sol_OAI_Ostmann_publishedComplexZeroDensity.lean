-- Prove2me | solution 1 for OAI.Ostmann.publishedComplexZeroDensity
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T06:43:38.069133+00:00
-- url     : https://prove2.me/submissions/617c34ea-c77a-4252-81c2-77d1e818d674

import Mathlib
import Definitions.Def_OAIQ095D006
import Theorems.Thm_OAI_Ostmann_density_packed_product_fourth
import Theorems.Thm_OAI_Ostmann_density_polynomial_alternative_balanced

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_RectangleAnalyticPole
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A single pole under an analytic rectangle integral -/

namespace Ostmann

open Complex Filter Set
open scoped Topology

 theorem analytic_dslope_of_analytic (f : ℂ → ℂ) (z s : ℂ)
    (hz : AnalyticAt ℂ f z) (hs : AnalyticAt ℂ f s) : AnalyticAt ℂ (dslope f z) s := by
  by_cases he : s = z
  · subst s
    obtain ⟨p, hp⟩ := hz
    exact ⟨p.fslope, hp.has_fpower_series_dslope_fslope⟩
  · have hh : dslope f z =ᶠ[𝓝 s] fun w => (w - z)⁻¹ * (f w - f z) := by
      filter_upwards [isOpen_ne.mem_nhds he] with w hw
      rw [dslope_of_ne f hw]
      rfl
    exact (((analyticAt_id.sub analyticAt_const).inv (sub_ne_zero.mpr he)).mul
      (hs.sub analyticAt_const)).congr hh.symm

 theorem rectangle_analytic_pole (f : ℂ → ℂ) (a b c d : ℝ)
    (ha : a < 0) (hb : 0 < b) (hc : c < 0) (hd : 0 < d)
    (hf : ∀ z ∈ uIcc a b ×ℂ uIcc c d, AnalyticAt ℂ f z) :
    rectangleBoundaryIntegral (fun z => f z / z) a b c d =
      (2 * (Real.pi : ℂ) * I) * f 0 := by
  have hz : (0 : ℂ) ∈ uIcc a b ×ℂ uIcc c d := by
    simp only [mem_reProdIm, zero_re, zero_im, uIcc_of_le (ha.trans hb).le,
      uIcc_of_le (hc.trans hd).le, mem_Icc]
    exact ⟨⟨ha.le, hb.le⟩, hc.le, hd.le⟩
  let g := dslope f 0
  have hg : ∀ z ∈ uIcc a b ×ℂ uIcc c d, AnalyticAt ℂ g z :=
    fun z hz' => analytic_dslope_of_analytic f 0 z (hf 0 hz) (hf z hz')
  have hn (z : ℂ) (hz' : z ∈ contourRectangleBoundary a b c d) : z ≠ 0 :=
    contourBoundary_ne_interior ⟨ha, hb, hc, hd⟩ hz'
  have hgI : RectangleIntegrable g a b c d := rectangleIntegrable_of_continuousOn
    (fun z hz' => (hg z ⟨hz'.1, hz'.2.1⟩).continuousAt.continuousWithinAt)
  have hpI : RectangleIntegrable (fun z => f 0 * (z - 0)⁻¹) a b c d :=
    (rectangleIntegrable_sub_inv ⟨ha, hb, hc, hd⟩).const_mul _
  have he : rectangleBoundaryIntegral (fun z => f z / z) a b c d =
      rectangleBoundaryIntegral (fun z => g z + f 0 * (z - 0)⁻¹) a b c d := by
    apply rectangleBoundaryIntegral_congr
    intro z hz'
    dsimp [g]
    rw [dslope_of_ne f (hn z hz')]
    simp only [slope, smul_eq_mul, vsub_eq_sub, sub_zero]
    ring
  rw [he, rectangleBoundaryIntegral_add hgI hpI, rectangleBoundaryIntegral_eq_zero hg,
    zero_add, rectangleBoundaryIntegral_const_mul,
    rectangleBoundaryIntegral_sub_inv 0 a b c d ha hb hc hd]
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityDetectorCoefficients
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual truncated Möbius coefficients in the zero detector -/

namespace Ostmann

open scoped BigOperators Classical

 theorem densityMobiusCutoff_norm (X n : ℕ) : ‖densityMobiusCutoff X n‖ ≤ 1 := by
  unfold densityMobiusCutoff
  split_ifs
  · norm_cast
    exact ArithmeticFunction.abs_moebius_le_one
  · simp

 theorem densityDetectorCoefficient_initial (X n : ℕ) (hn : n ≤ X) :
    densityDetectorCoefficient X n = if n = 1 then 1 else 0 := by
  have he : densityDetectorCoefficient X n = ∑ d ∈ n.divisors,
      (ArithmeticFunction.moebius d : ℂ) := by
    apply Finset.sum_congr rfl
    intro d hd
    unfold densityMobiusCutoff
    exact ite_eq_left ((Nat.le_of_dvd (Nat.pos_of_ne_zero (Nat.mem_divisors.mp hd).2) (Nat.dvd_of_mem_divisors hd)).trans hn)
  rw [he]
  have hm := congrArg (fun f : ArithmeticFunction ℂ => f n)
    (ArithmeticFunction.coe_zeta_mul_coe_moebius (R := ℂ))
  rw [ArithmeticFunction.coe_zeta_mul_apply] at hm
  simpa only [ArithmeticFunction.intCoe_apply, ArithmeticFunction.one_apply] using hm

 theorem densityDetectorCoefficient_one {X : ℕ} (hX : 1 ≤ X) :
    densityDetectorCoefficient X 1 = 1 := by
  rw [densityDetectorCoefficient_initial X 1 hX, ite_eq_left rfl]

 theorem densityDetectorCoefficient_small {X n : ℕ} (hn : 2 ≤ n) (hX : n ≤ X) :
    densityDetectorCoefficient X n = 0 := by
  rw [densityDetectorCoefficient_initial X n hX, ite_eq_right (by omega)]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityMollifierProduct
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual finite mollifier times the character L-function -/

namespace Ostmann

open scoped BigOperators Classical

 theorem density_detector_convolution {q : ℕ} (X : ℕ) (χ : DirichletCharacter ℂ q) :
    LSeries.convolution (fun n : ℕ => χ (n : ZMod q)) (densityMollifierCoefficient X χ) =
      fun n : ℕ => χ (n : ZMod q) * densityDetectorCoefficient X n := by
  funext n
  rw [LSeries.convolution_def]
  change (∑ p ∈ n.divisorsAntidiagonal,
    χ (p.1 : ZMod q) * (χ (p.2 : ZMod q) * densityMobiusCutoff X p.2)) = _
  calc
    _ = χ (n : ZMod q) * ∑ p ∈ n.divisorsAntidiagonal, densityMobiusCutoff X p.2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      have hm := (Nat.mem_divisorsAntidiagonal.mp hp).1
      rw [← mul_assoc, ← map_mul, ← Nat.cast_mul, hm]
    _ = _ := by
      rw [Nat.sum_divisorsAntidiagonal' (fun _ b => densityMobiusCutoff X b)]
      rfl

 theorem densityMollifier_eq_LSeries {q : ℕ} (X : ℕ) (χ : DirichletCharacter ℂ q) (s : ℂ) :
    densityMollifier X χ s = LSeries (densityMollifierCoefficient X χ) s := by
  have hout (n : ℕ) (hn : n ∉ Finset.Icc 1 X) :
      LSeries.term (densityMollifierCoefficient X χ) s n = 0 := by
    by_cases hn0 : n = 0
    · subst n; simp
    · have hnX : ¬n ≤ X := by simp only [Finset.mem_Icc] at hn; omega
      rw [LSeries.term_of_ne_zero hn0]
      simp only [densityMollifierCoefficient, densityMobiusCutoff, ite_eq_right hnX, mul_zero, zero_div]
  rw [LSeries, tsum_eq_sum hout]
  apply Finset.sum_congr rfl
  intro n hn
  have hnn := Finset.mem_Icc.mp hn
  rw [LSeries.term_of_ne_zero (by omega : n ≠ 0)]
  simp only [densityMollifierCoefficient, densityMobiusCutoff, ite_eq_left hnn.2]

 theorem densityMollifierCoefficient_norm {q : ℕ} [NeZero q] (X n : ℕ)
    (χ : DirichletCharacter ℂ q) : ‖densityMollifierCoefficient X χ n‖ ≤ 1 := by
  rw [densityMollifierCoefficient, norm_mul]
  exact (mul_le_mul (χ.norm_le_one _) (densityMobiusCutoff_norm X n)
    (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)

 theorem density_mollifier_L_product {q : ℕ} [NeZero q] (X : ℕ)
    (χ : DirichletCharacter ℂ q) (s : ℂ) (hs : 1 < s.re) :
    LSeries (fun n : ℕ => χ (n : ZMod q) * densityDetectorCoefficient X n) s =
      DirichletCharacter.LFunction χ s * densityMollifier X χ s := by
  rw [← density_detector_convolution X χ,
    LSeries_convolution' (χ.LSeriesSummable_of_one_lt_re hs)
      (LSeriesSummable_of_bounded_of_one_lt_re
        (fun n _ => densityMollifierCoefficient_norm X n χ) hs),
    DirichletCharacter.LFunction_eq_LSeries χ hs, densityMollifier_eq_LSeries]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityFiniteSeriesBridge
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original divisor coefficients in each shifted finite contour -/

namespace Ostmann

open Complex MeasureTheory
open scoped BigOperators

 theorem density_LSeries_term_add (a : ℕ → ℂ) (s w : ℂ) (n : ℕ) :
    LSeries.term a (s + w) n = LSeries.term a s n / (n : ℂ) ^ w := by
  by_cases hn : n = 0
  · subst n
    simp
  · have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn, Complex.cpow_add _ _ hnC]
    ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityFourierContour
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact Fourier scaling of the original finite contour sums -/

namespace Ostmann

open Complex MeasureTheory
open scoped BigOperators

 theorem density_fourier_integral_scale (f : ℝ → ℂ) :
    (2 * (Real.pi : ℂ))⁻¹ * (∫ u : ℝ, f u) = ∫ u : ℝ, f (2 * Real.pi * u) := by
  rw [Measure.integral_comp_mul_left f (2 * Real.pi),
    abs_of_pos (inv_pos.mpr (mul_pos (by norm_num) Real.pi_pos))]
  simp only [Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_mul, Complex.ofReal_ofNat]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityMomentCutoff
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The integer cutoff for the actual fourth moment -/

namespace Ostmann

 theorem density_moment_cutoff (Q : ℕ) (hQ : 1 ≤ Q) (T : ℝ) (hT : 2 ≤ T) :
    ∃ N : ℕ, 1 ≤ N ∧ 1 ≤ Real.log N ∧ 10 * (Q : ℝ) * T ≤ N ∧
      (N : ℝ) + (Q : ℝ) ^ 2 * T ≤ 17 * (Q : ℝ) ^ 2 * T ∧
      Real.log N ≤ 5 * Real.log ((Q : ℝ) * T) := by
  let N := ⌈10 * (Q : ℝ) * T⌉₊
  have hq : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hqt : 2 ≤ (Q : ℝ) * T := by nlinarith
  have hscale : 10 * (Q : ℝ) * T ≤ N := Nat.le_ceil _
  have hten : (10 : ℝ) ≤ N := by linarith
  have hN : 1 ≤ N := by exact_mod_cast (show (1 : ℝ) ≤ N by linarith)
  have hupper : (N : ℝ) ≤ 16 * ((Q : ℝ) * T) := by
    have h := Nat.ceil_lt_add_one (by positivity : 0 ≤ 10 * (Q : ℝ) * T)
    change (N : ℝ) < 10 * (Q : ℝ) * T + 1 at h
    linarith
  have hlogN : 1 ≤ Real.log N := by
    have hlog10 : (1 : ℝ) ≤ Real.log 10 := by
      have h := Real.le_log_one_add_of_nonneg (by norm_num : (0 : ℝ) ≤ 9)
      norm_num at h
      linarith
    exact hlog10.trans (Real.log_le_log (by norm_num) hten)
  refine ⟨N, hN, hlogN, hscale, ?_, ?_⟩
  · have hqtA : (Q : ℝ) * T ≤ (Q : ℝ) ^ 2 * T := by
      have h := mul_le_mul_of_nonneg_right hq (by positivity : 0 ≤ (Q : ℝ) * T)
      nlinarith
    linarith
  · have hlqt : Real.log 2 ≤ Real.log ((Q : ℝ) * T) := Real.log_le_log (by norm_num) hqt
    have hlog := Real.log_le_log (show (0 : ℝ) < N by linarith) hupper
    rw [Real.log_mul (by norm_num) (by positivity)] at hlog
    have h16 : Real.log 16 = 4 * Real.log 2 := by
      have h := Real.log_pow (2 : ℝ) 4
      norm_num at h
      exact h
    rw [h16] at hlog
    linarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityBalanceParameters
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The conductor-height parameters in the two zero-detector estimates -/

namespace Ostmann

 theorem density_conductor_height_log (Q : ℕ) (hQ : 1 ≤ Q) (T : ℝ) (hT : 2 ≤ T) :
    Real.log ((Q : ℝ) ^ 2 * T) ≤ 2 * Real.log ((Q : ℝ) * T) := by
  have hq : (0 : ℝ) < Q := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hQ)
  have ht : 0 < T := by linarith
  rw [Real.log_mul (by positivity) ht.ne', Real.log_pow,
    Real.log_mul hq.ne' ht.ne']
  have hl : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  norm_num only [Nat.cast_ofNat]
  linarith

 theorem density_detector_cutoff (Q : ℕ) (hQ : 1 ≤ Q) (T : ℝ) (hT : 2 ≤ T) :
    ∃ X : ℕ, 1 ≤ X ∧ (Q : ℝ) ^ 2 * T ≤ X ∧
      (X : ℝ) + (Q : ℝ) ^ 2 * T ≤ 17 * ((Q : ℝ) ^ 2 * T) ∧
      1 + Real.log X ≤ 20 * Real.log ((Q : ℝ) * T) := by
  have hq : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hB : 2 ≤ (Q : ℝ) ^ 2 * T := by nlinarith
  obtain ⟨X, hX, hlX, hscale, hsize, hlog⟩ := density_moment_cutoff 1 (by decide) ((Q : ℝ) ^ 2 * T) hB
  norm_num at hscale hsize hlog
  refine ⟨X, hX, by nlinarith, hsize, ?_⟩
  have hlB := density_conductor_height_log Q hQ T hT
  linarith

 theorem density_balance_at_least_one (σ : ℝ) (hσ : 1 / 2 ≤ σ) (hσ1 : σ ≤ 1) :
    1 ≤ densityBalanceExponent σ := by
  unfold densityBalanceExponent
  apply (le_div_iff₀ (by linarith : 0 < 2 * (2 - σ))).mpr
  linarith

 theorem density_balance_identity (B σ : ℝ) (hB : 0 < B) (hσ : σ < 2) :
    B ^ 3 * (B ^ densityBalanceExponent σ) ^ (2 - 4 * σ) =
      (B ^ densityTargetExponent σ) ^ (3 : ℕ) := by
  rw [← Real.rpow_natCast B 3, ← Real.rpow_natCast (B ^ densityTargetExponent σ) 3,
    ← Real.rpow_mul hB.le, ← Real.rpow_mul hB.le, ← Real.rpow_add hB]
  congr 1
  unfold densityTargetExponent densityBalanceExponent
  have hd : 2 - σ ≠ 0 := by linarith
  field_simp [hd]
  ring

 theorem density_away_inverse_gap (Q : ℕ) (hQ : 1 ≤ Q) (T σ : ℝ) (hT : 2 ≤ T)
    (hσ : 1 / 2 < σ) (hgap : 1 / Real.log ((Q : ℝ) ^ 2 * T) ≤ σ - 1 / 2) :
    1 / (σ - 1 / 2) ≤ 2 * Real.log ((Q : ℝ) * T) := by
  have hq : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hB : 1 < (Q : ℝ) ^ 2 * T := by nlinarith
  have hl : 0 < Real.log ((Q : ℝ) ^ 2 * T) := Real.log_pos hB
  have hh := mul_le_mul_of_nonneg_right hgap hl.le
  rw [div_mul_cancel₀ _ hl.ne'] at hh
  apply (div_le_iff₀ (by linarith : 0 < σ - 1 / 2)).mpr
  have hlog := density_conductor_height_log Q hQ T hT
  nlinarith

 theorem density_balanced_count_from_cube (C R B σ L : ℝ) (hC : 0 ≤ C)
    (hR : 0 ≤ R) (hB : 0 ≤ B)
    (h : R ^ 3 ≤ C * (B ^ densityTargetExponent σ) ^ 3 * L ^ 12) :
    R ≤ (C + 1) * B ^ densityTargetExponent σ * L ^ 4 := by
  have hc : C ≤ (C + 1) ^ 3 := by nlinarith [sq_nonneg C]
  have hh : R ^ 3 ≤ ((C + 1) * B ^ densityTargetExponent σ * L ^ 4) ^ 3 := by
    apply h.trans
    have hm := mul_le_mul_of_nonneg_right hc
      (show 0 ≤ (B ^ densityTargetExponent σ) ^ 3 * L ^ 12 by positivity)
    first | (convert hm using 1 <;> ring) | exact (le_of_eq (by ring)).trans (hm.trans (le_of_eq (by ring)))
  exact (pow_le_pow_iff_left₀ hR (by positivity) (by decide : (3 : ℕ) ≠ 0)).mp hh

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityDetectorWeight
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The compact quadratic Riesz weight for detecting actual zeros -/

namespace Ostmann

open Complex MeasureTheory Set

 theorem densityDetectorWeight_continuous : Continuous densityDetectorWeight := by
  unfold densityDetectorWeight
  fun_prop

 theorem densityDetectorWeight_zero (x : ℝ) (hx : 1 ≤ x) : densityDetectorWeight x = 0 := by
  simp [densityDetectorWeight, max_eq_right (by linarith : 1 - x ≤ 0)]

 theorem densityDetectorWeight_eq (x : ℝ) (hx : x ≤ 1) :
    densityDetectorWeight x = ((1 - x) ^ 2 / 2 : ℝ) := by
  simp only [densityDetectorWeight, max_eq_left (by linarith : 0 ≤ 1 - x),
    ofReal_div, ofReal_pow, ofReal_ofNat]

 theorem densityDetectorWeight_at_one_div (Y : ℝ) (hY : 4 ≤ Y) :
    1 / 4 ≤ (densityDetectorWeight (1 / Y)).re := by
  have hYp : 0 < Y := by linarith
  rw [densityDetectorWeight_eq _ (by exact (div_le_one hYp).mpr (by linarith))]
  simp only [ofReal_re]
  have hy : 0 ≤ 1 / Y := by positivity
  have hy4 : 1 / Y ≤ (1 / 4 : ℝ) := (div_le_div_iff₀ hYp (by norm_num)).mpr (by linarith)
  nlinarith

end Ostmann

namespace Ostmann

open Complex MeasureTheory Set

 theorem densityDetectorWeight_hasMellin (s : ℂ) (hs : 0 < s.re) :
    HasMellin densityDetectorWeight s (densityDetectorKernel s) := by
  let f0 : ℝ → ℂ := indicator (Ioc 0 1) (fun _ => 1)
  let f1 : ℝ → ℂ := indicator (Ioc 0 1) (fun u => (u : ℂ) ^ (1 : ℂ))
  let f2 : ℝ → ℂ := indicator (Ioc 0 1) (fun u => (u : ℂ) ^ (2 : ℂ))
  have h0 : HasMellin f0 s (1 / s) := hasMellin_one_Ioc hs
  have h1 : HasMellin f1 s (1 / (s + 1)) := hasMellin_cpow_Ioc 1 (by simp; linarith)
  have h2 : HasMellin f2 s (1 / (s + 2)) := hasMellin_cpow_Ioc 2 (by simp; linarith)
  have h21 := hasMellin_const_smul h1.1 (2 : ℂ)
  have hsub := hasMellin_sub h0.1 h21.1
  have hadd := hasMellin_add hsub.1 h2.1
  have hhalf := hasMellin_const_smul hadd.1 (1 / 2 : ℂ)
  rw [hadd.2, hsub.2, h21.2, h0.2, h1.2, h2.2] at hhalf
  let f : ℝ → ℂ := fun u => (1 / 2 : ℂ) • ((f0 u - (2 : ℂ) • f1 u) + f2 u)
  have he : EqOn f densityDetectorWeight (Ioi 0) := by
    intro u hu
    change 0 < u at hu
    by_cases hle : u ≤ 1
    · have hm : u ∈ Ioc (0 : ℝ) 1 := ⟨hu, hle⟩
      simp only [f, f0, f1, f2, indicator_of_mem hm, cpow_one, cpow_ofNat, smul_eq_mul,
        densityDetectorWeight, max_eq_left (sub_nonneg.mpr hle)]
      push_cast
      ring
    · have hn : u ∉ Ioc (0 : ℝ) 1 := fun h => hle h.2
      simp [f, f0, f1, f2, hn, densityDetectorWeight, max_eq_right (by linarith : 1 - u ≤ 0)]
  refine ⟨hhalf.1.congr_fun (fun u hu => congrArg (fun a : ℂ => (u : ℂ) ^ (s - 1) • a)
    (he hu)) measurableSet_Ioi, ?_⟩
  have hi : mellin densityDetectorWeight s = mellin f s := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u hu
    exact congrArg (fun a : ℂ => (u : ℂ) ^ (s - 1) • a) (he hu).symm
  rw [hi, hhalf.2]
  have hsn : s ≠ 0 := by intro h; simp [h] at hs
  have hs1 : s + 1 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp only [add_re, one_re, zero_re] at this
    linarith
  have hs2 : s + 2 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    norm_num at this
    linarith
  unfold densityDetectorKernel
  simp only [smul_eq_mul]
  field_simp
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityDetectorKernel
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The cubic vertical decay of the compact zero-detector kernel -/

namespace Ostmann

open Complex MeasureTheory

 theorem densityDetectorKernel_line_bound (σ t : ℝ) (hσ : 1 ≤ σ) :
    ‖densityDetectorKernel ((σ : ℂ) + (t : ℂ) * I)‖ ≤
      8 * (1 + |t|) ^ (-(3 : ℝ)) := by
  let s : ℂ := (σ : ℂ) + (t : ℂ) * I
  have hr : s.re = σ := by simp [s]
  have hi : s.im = t := by simp [s]
  have h0 : 1 + |t| ≤ 2 * ‖s‖ := by
    have ha := Complex.re_le_norm s
    have hb := Complex.abs_im_le_norm s
    rw [hr] at ha
    rw [hi] at hb
    linarith
  have h1 : 1 + |t| ≤ 2 * ‖s + 1‖ := by
    have ha := Complex.re_le_norm (s + 1)
    have hb := Complex.abs_im_le_norm (s + 1)
    simp only [add_re, one_re, hr, add_im, one_im, add_zero, hi] at ha hb
    linarith
  have h2 : 1 + |t| ≤ 2 * ‖s + 2‖ := by
    have ha := Complex.re_le_norm (s + 2)
    have hb := Complex.abs_im_le_norm (s + 2)
    norm_num [hr, hi] at ha hb
    linarith
  have hp : (1 + |t|) ^ 3 ≤ 8 * (‖s‖ * ‖s + 1‖ * ‖s + 2‖) := by
    have h01 := mul_le_mul h0 h1 (by positivity) (by positivity)
    have h012 := mul_le_mul h01 h2 (by positivity) (by positivity)
    nlinarith
  have hn0 : 0 < ‖s‖ := by linarith [abs_nonneg t]
  have hn1 : 0 < ‖s + 1‖ := by linarith [abs_nonneg t]
  have hn2 : 0 < ‖s + 2‖ := by linarith [abs_nonneg t]
  change ‖1 / (s * (s + 1) * (s + 2))‖ ≤ _
  rw [norm_div, norm_one, norm_mul, norm_mul, Real.rpow_neg (by positivity : 0 ≤ 1 + |t|),
    Real.rpow_ofNat, ← div_eq_mul_inv]
  apply (div_le_div_iff₀ (by positivity : 0 < ‖s‖ * ‖s + 1‖ * ‖s + 2‖)
    (by positivity : 0 < (1 + |t|) ^ 3)).mpr
  nlinarith

 theorem densityDetectorKernel_verticalIntegrable (σ : ℝ) (hσ : 1 ≤ σ) :
    Complex.VerticalIntegrable densityDetectorKernel σ := by
  have hmajor : Integrable (fun t : ℝ => 8 * (1 + ‖t‖) ^ (-(3 : ℝ))) :=
    (integrable_one_add_norm (E := ℝ) (by norm_num : (Module.finrank ℝ ℝ : ℝ) < 3)).const_mul 8
  have hc : Continuous (fun t : ℝ => densityDetectorKernel ((σ : ℂ) + (t : ℂ) * I)) := by
    unfold densityDetectorKernel
    apply continuous_const.div
    · fun_prop
    · intro t
      apply mul_ne_zero
      · apply mul_ne_zero
        · intro h
          have hr := congrArg Complex.re h
          simp at hr
          linarith
        · intro h
          have hr := congrArg Complex.re h
          simp at hr
          linarith
      · intro h
        have hr := congrArg Complex.re h
        simp at hr
        linarith
  apply hmajor.mono' hc.aestronglyMeasurable
  filter_upwards with t
  simpa only [Real.norm_eq_abs] using densityDetectorKernel_line_bound σ t hσ

 theorem densityDetectorWeight_mellin_inversion (σ x : ℝ) (hσ : 1 ≤ σ) (hx : 0 < x) :
    mellinInv σ densityDetectorKernel x = densityDetectorWeight x := by
  have hσp : 0 < σ := by linarith
  have hF : Complex.VerticalIntegrable (mellin densityDetectorWeight) σ := by
    have he : (fun t : ℝ => mellin densityDetectorWeight ((σ : ℂ) + (t : ℂ) * I)) =
        (fun t : ℝ => densityDetectorKernel ((σ : ℂ) + (t : ℂ) * I)) := by
      funext t
      exact (densityDetectorWeight_hasMellin _ (by simpa using hσp)).2
    change Integrable (fun t : ℝ => mellin densityDetectorWeight ((σ : ℂ) + (t : ℂ) * I))
    rw [he]
    exact densityDetectorKernel_verticalIntegrable σ hσ
  have hi := mellinInv_mellin_eq σ densityDetectorWeight hx
    (densityDetectorWeight_hasMellin (σ : ℂ) hσp).1 hF densityDetectorWeight_continuous.continuousAt
  rw [← hi]
  unfold mellinInv
  congr 1
  apply integral_congr_ae
  filter_upwards with t
  rw [(densityDetectorWeight_hasMellin ((σ : ℂ) + (t : ℂ) * I) (by simpa using hσp)).2]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityDetectorKernelLeft
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The critical-line side of the compact detector contour -/

namespace Ostmann

open Complex

 theorem densityDetectorKernel_left_bound (δ u : ℝ) (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2) :
    ‖densityDetectorKernel ((-δ : ℂ) + (u : ℂ) * I)‖ ≤
      (16 / δ) * (1 + |u|) ^ (-(3 : ℝ)) := by
  let w : ℂ := (-δ : ℂ) + (u : ℂ) * I
  have hr : w.re = -δ := by simp [w]
  have hi : w.im = u := by simp [w]
  have h0 : δ * (1 + |u|) ≤ 2 * ‖w‖ := by
    have ha := Complex.abs_re_le_norm w
    have hb := Complex.abs_im_le_norm w
    rw [hr, abs_neg, abs_of_pos hδ] at ha
    rw [hi] at hb
    nlinarith [abs_nonneg u]
  have h1 : 1 + |u| ≤ 4 * ‖w + 1‖ := by
    have ha := Complex.re_le_norm (w + 1)
    have hb := Complex.abs_im_le_norm (w + 1)
    simp only [add_re, one_re, hr, add_im, one_im, add_zero, hi] at ha hb
    linarith
  have h2 : 1 + |u| ≤ 2 * ‖w + 2‖ := by
    have ha := Complex.re_le_norm (w + 2)
    have hb := Complex.abs_im_le_norm (w + 2)
    norm_num [hr, hi] at ha hb
    linarith
  have hp : δ * (1 + |u|) ^ 3 ≤ 16 * (‖w‖ * ‖w + 1‖ * ‖w + 2‖) := by
    have h01 := mul_le_mul h0 h1 (by positivity) (by positivity)
    have h012 := mul_le_mul h01 h2 (by positivity) (by positivity)
    nlinarith
  have hn0 : 0 < ‖w‖ := by nlinarith [abs_nonneg u]
  have hn1 : 0 < ‖w + 1‖ := by linarith [abs_nonneg u]
  have hn2 : 0 < ‖w + 2‖ := by linarith [abs_nonneg u]
  change ‖1 / (w * (w + 1) * (w + 2))‖ ≤ _
  rw [norm_div, norm_one, norm_mul, norm_mul, Real.rpow_neg (by positivity : 0 ≤ 1 + |u|),
    Real.rpow_ofNat]
  rw [show (16 / δ) * ((1 + |u|) ^ 3)⁻¹ = 16 / (δ * (1 + |u|) ^ 3) by
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring]
  apply (div_le_div_iff₀ (by positivity : 0 < ‖w‖ * ‖w + 1‖ * ‖w + 2‖)
    (by positivity : 0 < δ * (1 + |u|) ^ 3)).mpr
  nlinarith

 theorem densityDetectorKernel_high_bound (x u : ℝ) (hu : 0 < |u|) :
    ‖densityDetectorKernel ((x : ℂ) + (u : ℂ) * I)‖ ≤ (|u| ^ 3)⁻¹ := by
  let w : ℂ := (x : ℂ) + (u : ℂ) * I
  have h0 : |u| ≤ ‖w‖ := by simpa [w] using Complex.abs_im_le_norm w
  have h1 : |u| ≤ ‖w + 1‖ := by simpa [w] using Complex.abs_im_le_norm (w + 1)
  have h2 : |u| ≤ ‖w + 2‖ := by simpa [w] using Complex.abs_im_le_norm (w + 2)
  have hp : |u| ^ 3 ≤ ‖w‖ * ‖w + 1‖ * ‖w + 2‖ := by
    have h01 := mul_le_mul h0 h1 hu.le (norm_nonneg _)
    have h012 := mul_le_mul h01 h2 hu.le (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    nlinarith
  change ‖1 / (w * (w + 1) * (w + 2))‖ ≤ _
  rw [norm_div, norm_one, norm_mul, norm_mul, ← one_div]
  exact one_div_le_one_div_of_le (pow_pos hu 3) hp

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityDetectorSeries
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The true truncated Mobius series in the zero detector -/

namespace Ostmann

open Complex MeasureTheory Set
open scoped BigOperators Classical

 theorem densityDetectorMean_split (χ : PrimitiveComplexCharacter) (X : ℕ) (hX : 1 ≤ X)
    (s : ℂ) (Y : ℝ) (hY : 1 ≤ Y) :
    densityDetectorMean χ X s Y = densityDetectorWeight (1 / Y) +
      ∑ n ∈ (Finset.Icc 1 ⌊Y⌋₊).filter (fun n => X < n),
        LSeries.term (densityDetectorCharacterCoefficient χ X) s n * densityDetectorWeight (n / Y) := by
  let U := Finset.Icc 1 ⌊Y⌋₊
  have h1 : 1 ∈ U := Finset.mem_Icc.mpr ⟨le_rfl, (Nat.le_floor_iff (by linarith : 0 ≤ Y)).mpr (by simpa using hY)⟩
  have hf : ∑ n ∈ U, LSeries.term (densityDetectorCharacterCoefficient χ X) s n * densityDetectorWeight (n / Y) =
      ∑ n ∈ U, ((if n = 1 then densityDetectorWeight (1 / Y) else 0) +
        (if X < n then LSeries.term (densityDetectorCharacterCoefficient χ X) s n *
          densityDetectorWeight (n / Y) else 0)) := by
    apply Finset.sum_congr rfl
    intro n hn
    by_cases hn1 : n = 1
    · subst n
      simp [densityDetectorCharacterCoefficient, densityDetectorCoefficient_one hX,
        LSeries.term_of_ne_zero, show ¬ X < 1 by omega]
    · by_cases hnX : X < n
      · simp [hn1, hnX]
      · have hn2 : 2 ≤ n := by have := (Finset.mem_Icc.mp hn).1; omega
        have hz := densityDetectorCoefficient_small hn2 (by omega : n ≤ X)
        simp [hn1, hnX, LSeries.term_of_ne_zero (show n ≠ 0 by omega),
          densityDetectorCharacterCoefficient, hz]
  unfold densityDetectorMean
  rw [hf, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', h1, ↓reduceIte, Finset.sum_filter]
  rfl

end Ostmann

namespace Ostmann

open Complex MeasureTheory Set
open scoped BigOperators Classical

 theorem densityDetectorCharacterCoefficient_summable (χ : PrimitiveComplexCharacter)
    (X : ℕ) (s : ℂ) (hs : 1 < s.re) :
    LSeriesSummable (densityDetectorCharacterCoefficient χ X) s := by
  let : NeZero χ.modulus := ⟨χ.positive.ne'⟩
  have h := (χ.character.LSeriesSummable_of_one_lt_re hs).convolution
    (LSeriesSummable_of_bounded_of_one_lt_re
      (fun n _ => densityMollifierCoefficient_norm X n χ.character) hs)
  rw [density_detector_convolution] at h
  exact h

 theorem densityDetectorMean_tsum (χ : PrimitiveComplexCharacter) (X : ℕ) (s : ℂ)
    (Y : ℝ) (hY : 0 < Y) :
    densityDetectorMean χ X s Y = ∑' n : ℕ,
      LSeries.term (densityDetectorCharacterCoefficient χ X) s n * densityDetectorWeight (n / Y) := by
  symm
  apply tsum_eq_sum
  intro n hn
  by_cases hn0 : n = 0
  · simp [hn0]
  · have hnY : Y < n := by
      have hnN : ⌊Y⌋₊ < n := by
        by_contra h
        exact hn (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
      exact (Nat.floor_lt (by positivity : 0 ≤ Y)).mp hnN
    rw [densityDetectorWeight_zero _ ((le_div_iff₀ hY).mpr (by simpa using hnY.le)), mul_zero]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityDetectorIntegral
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact initial contour of the compact Mobius zero detector -/

namespace Ostmann

open Complex MeasureTheory
open scoped BigOperators Classical

 theorem densityDetectorVerticalTerm_norm (χ : PrimitiveComplexCharacter) (X : ℕ)
    (s : ℂ) (Y : ℝ) (hY : 0 < Y) (n : ℕ) (t : ℝ) :
    ‖densityDetectorVerticalTerm χ X s Y n t‖ =
      (‖LSeries.term (densityDetectorCharacterCoefficient χ X) (s + 2) n‖ * Y ^ 2) *
        ‖densityDetectorKernel (2 + (t : ℂ) * I)‖ := by
  unfold densityDetectorVerticalTerm
  rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hY]
  have he : (2 + (t : ℂ) * I).re = (2 : ℝ) := by simp
  rw [he, Real.rpow_two]
  have hn : ‖LSeries.term (densityDetectorCharacterCoefficient χ X) (s + (2 + (t : ℂ) * I)) n‖ =
      ‖LSeries.term (densityDetectorCharacterCoefficient χ X) (s + 2) n‖ := by
    simp only [LSeries.norm_term_eq]
    congr 2
    simp
  rw [hn]

 theorem densityDetectorVerticalTerm_continuous (χ : PrimitiveComplexCharacter) (X : ℕ)
    (s : ℂ) (Y : ℝ) (hY : 0 < Y) (n : ℕ) :
    Continuous (densityDetectorVerticalTerm χ X s Y n) := by
  have hk : Continuous (fun t : ℝ => densityDetectorKernel (2 + (t : ℂ) * I)) := by
    unfold densityDetectorKernel
    apply continuous_const.div (by fun_prop)
    intro t
    apply mul_ne_zero
    · apply mul_ne_zero <;> norm_num [Complex.ext_iff]
    · norm_num [Complex.ext_iff]
  have hpow : Continuous (fun t : ℝ => (Y : ℂ) ^ (2 + (t : ℂ) * I)) :=
    (differentiable_id.const_cpow (Or.inl (by exact_mod_cast hY.ne'))).continuous.comp (by fun_prop)
  apply Continuous.mul _ hk
  apply Continuous.mul _ hpow
  by_cases hn : n = 0
  · subst n
    simp only [LSeries.term_zero]
    exact continuous_const
  · simp only [LSeries.term_of_ne_zero hn]
    apply continuous_const.div
    · exact (differentiable_id.const_cpow (Or.inl (by exact_mod_cast hn))).continuous.comp (by fun_prop)
    · intro t
      exact Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hn))

 theorem densityDetectorVerticalTerm_integrable (χ : PrimitiveComplexCharacter) (X : ℕ)
    (s : ℂ) (Y : ℝ) (hY : 0 < Y) (n : ℕ) :
    Integrable (densityDetectorVerticalTerm χ X s Y n) := by
  have hk := (densityDetectorKernel_verticalIntegrable 2 (by norm_num)).norm
  apply (hk.const_mul (‖LSeries.term (densityDetectorCharacterCoefficient χ X) (s + 2) n‖ * Y ^ 2)).mono'
    (densityDetectorVerticalTerm_continuous χ X s Y hY n).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun t => (densityDetectorVerticalTerm_norm χ X s Y hY n t).le)

 theorem densityDetectorVerticalTerm_summable_norm (χ : PrimitiveComplexCharacter) (X : ℕ)
    (s : ℂ) (hs : 0 ≤ s.re) (Y : ℝ) (hY : 0 < Y) :
    Summable (fun n : ℕ => ∫ t : ℝ, ‖densityDetectorVerticalTerm χ X s Y n t‖) := by
  have hsum := (densityDetectorCharacterCoefficient_summable χ X (s + 2)
    (by simp; linarith)).norm
  have h := (hsum.mul_right (Y ^ 2)).mul_right
    (∫ t : ℝ, ‖densityDetectorKernel (2 + (t : ℂ) * I)‖)
  apply h.congr
  intro n
  simp only [densityDetectorVerticalTerm_norm χ X s Y hY, integral_const_mul]

 theorem densityDetectorVerticalTerm_inversion (χ : PrimitiveComplexCharacter) (X : ℕ)
    (s : ℂ) (Y : ℝ) (hY : 0 < Y) (n : ℕ) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) * (∫ t : ℝ, densityDetectorVerticalTerm χ X s Y n t) =
      LSeries.term (densityDetectorCharacterCoefficient χ X) s n * densityDetectorWeight (n / Y) := by
  by_cases hn : n = 0
  · subst n
    simp [densityDetectorVerticalTerm]
  have hnR : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have he (t : ℝ) : densityDetectorVerticalTerm χ X s Y n t =
      LSeries.term (densityDetectorCharacterCoefficient χ X) s n *
        (((n : ℝ) / Y : ℝ) : ℂ) ^ (-(2 + (t : ℂ) * I)) *
          densityDetectorKernel (2 + (t : ℂ) * I) := by
    rw [densityDetectorVerticalTerm, density_LSeries_term_add, Complex.cpow_neg,
      Complex.ofReal_div, Complex.div_cpow_ofReal_nonneg hnR.le hY.le, inv_div]
    push_cast
    ring
  simp_rw [he, mul_assoc]
  rw [integral_const_mul]
  have hinv := densityDetectorWeight_mellin_inversion 2 ((n : ℝ) / Y) (by norm_num) (div_pos hnR hY)
  change ((1 / (2 * Real.pi) : ℝ) : ℂ) * (∫ t : ℝ,
    (((n : ℝ) / Y : ℝ) : ℂ) ^ (-(2 + (t : ℂ) * I)) *
      densityDetectorKernel (2 + (t : ℂ) * I)) = _ at hinv
  rw [← hinv]
  ring

 theorem densityDetectorMean_eq_integral (χ : PrimitiveComplexCharacter) (X : ℕ)
    (s : ℂ) (hs : 0 ≤ s.re) (Y : ℝ) (hY : 0 < Y) :
    densityDetectorMean χ X s Y = ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t : ℝ,
      χ.L (s + (2 + (t : ℂ) * I)) *
        densityMollifier X χ.character (s + (2 + (t : ℂ) * I)) *
          (Y : ℂ) ^ (2 + (t : ℂ) * I) * densityDetectorKernel (2 + (t : ℂ) * I) := by
  let : NeZero χ.modulus := ⟨χ.positive.ne'⟩
  rw [densityDetectorMean_tsum χ X s Y hY]
  simp_rw [← densityDetectorVerticalTerm_inversion χ X s Y hY]
  rw [tsum_mul_left, integral_tsum_of_summable_integral_norm
    (fun n => densityDetectorVerticalTerm_integrable χ X s Y hY n)
    (densityDetectorVerticalTerm_summable_norm χ X s hs Y hY)]
  congr 1
  apply integral_congr_ae
  filter_upwards with t
  simp only [densityDetectorVerticalTerm, tsum_mul_right]
  rw [show (∑' n, LSeries.term (densityDetectorCharacterCoefficient χ X)
      (s + (2 + (t : ℂ) * I)) n) =
      χ.L (s + (2 + (t : ℂ) * I)) * densityMollifier X χ.character (s + (2 + (t : ℂ) * I)) from
    density_mollifier_L_product X χ.character _ (by simp; linarith)]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityDetectorAnalytic
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Cancellation of the detector contour pole at an actual L-function zero -/

namespace Ostmann

open Complex Set
open scoped BigOperators

 theorem densityMollifier_shift_analytic (χ : PrimitiveComplexCharacter) (X : ℕ)
    (s w : ℂ) : AnalyticAt ℂ (fun z => densityMollifier X χ.character (s + z)) w := by
  unfold densityMollifier
  apply Finset.analyticAt_fun_sum
  intro n hn
  have hnp : 0 < n := (Finset.mem_Icc.mp hn).1
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hnp.ne'
  have hp := ((differentiable_id.const_cpow (Or.inl hnC)).analyticAt (s + w)).comp
    (analyticAt_const.add analyticAt_id : AnalyticAt ℂ (fun z : ℂ => s + z) w)
  exact analyticAt_const.div hp (Complex.cpow_ne_zero_iff.mpr (Or.inl hnC))

 theorem densityDetectorFactor_analytic (χ : PrimitiveComplexCharacter) (X : ℕ)
    (s : ℂ) (Y : ℝ) (hY : 0 < Y) (w : ℂ) (hw : -1 < w.re) :
    AnalyticAt ℂ (densityDetectorFactor χ X s Y) w := by
  have hy : (Y : ℂ) ≠ 0 := by exact_mod_cast hY.ne'
  have h1 : w + 1 ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    norm_num at hr
    linarith
  have h2 : w + 2 ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    norm_num at hr
    linarith
  exact ((((χ.L_analytic (s + w)).comp (analyticAt_const.add analyticAt_id)).mul
    (densityMollifier_shift_analytic χ X s w)).mul
      ((differentiable_id.const_cpow (Or.inl hy)).analyticAt w)).div
        ((analyticAt_id.add analyticAt_const).mul (analyticAt_id.add analyticAt_const))
        (mul_ne_zero h1 h2)

 theorem densityDetectorIntegrand_eq (χ : PrimitiveComplexCharacter) (X : ℕ)
    (s : ℂ) (Y : ℝ) (w : ℂ) :
    densityDetectorIntegrand χ X s Y w = densityDetectorFactor χ X s Y w / w := by
  unfold densityDetectorIntegrand densityDetectorFactor densityDetectorKernel
  simp only [div_eq_mul_inv, mul_inv_rev, one_mul]
  ring

 theorem densityDetector_rectangle_zero (χ : PrimitiveComplexCharacter) (X : ℕ)
    (s : ℂ) (hz : χ.L s = 0) (Y : ℝ) (hY : 0 < Y)
    (a b c d : ℝ) (ha0 : a < 0) (ha : -1 < a) (hb : 0 < b) (hc : c < 0) (hd : 0 < d) :
    rectangleBoundaryIntegral (densityDetectorIntegrand χ X s Y) a b c d = 0 := by
  have hf : ∀ w ∈ uIcc a b ×ℂ uIcc c d,
      AnalyticAt ℂ (densityDetectorFactor χ X s Y) w := by
    intro w hw
    have hr : a ≤ w.re := by
      have h := hw.1
      exact (show w.re ∈ Icc a b from by simpa only [uIcc_of_le (ha0.trans hb).le, mem_preimage] using h).1
    exact densityDetectorFactor_analytic χ X s Y hY w (ha.trans_le hr)
  have h := rectangle_analytic_pole (densityDetectorFactor χ X s Y) a b c d ha0 hb hc hd hf
  have he : densityDetectorFactor χ X s Y 0 = 0 := by simp [densityDetectorFactor, hz]
  simp only [he, mul_zero] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  exact congrArg (fun f => rectangleBoundaryIntegral f a b c d)
    (funext (densityDetectorIntegrand_eq χ X s Y))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityMollifierBound
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Elementary growth bounds for the actual zero-detector product -/

namespace Ostmann

open Complex
open scoped BigOperators

 theorem densityMollifier_norm_le (χ : PrimitiveComplexCharacter) (X : ℕ)
    (s : ℂ) (hs : 0 ≤ s.re) : ‖densityMollifier X χ.character s‖ ≤ X := by
  let : NeZero χ.modulus := ⟨χ.positive.ne'⟩
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 X, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      have hnp : 0 < n := (Finset.mem_Icc.mp hn).1
      have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hnp
      have hμ : ‖(ArithmeticFunction.moebius n : ℂ)‖ ≤ 1 := by
        norm_cast
        exact ArithmeticFunction.abs_moebius_le_one
      rw [norm_div, norm_mul, ← Complex.ofReal_natCast,
        Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
      apply (div_le_div_of_nonneg_right
        (mul_le_mul (χ.character.norm_le_one _) hμ (norm_nonneg _) zero_le_one)
        (Real.rpow_nonneg (by positivity) s.re)).trans
      rw [one_mul]
      exact (div_le_one (Real.rpow_pos_of_pos (by positivity) s.re)).mpr
        (Real.one_le_rpow hnR hs)
    _ = _ := by simp [Nat.card_Icc]

 theorem density_L_short_positive_bound (χ : PrimitiveComplexCharacter) (z : ℂ)
    (hz : 1 / 2 ≤ z.re) (hz3 : z.re ≤ 3) :
    ‖χ.L z‖ ≤ 2 * ((χ.modulus : ℝ) + 1) * (3 + |z.im|) := by
  have hzp : 0 < z.re := by linarith
  have hn : ‖z‖ ≤ 3 + |z.im| := by
    apply (Complex.norm_le_abs_re_add_abs_im z).trans
    rw [abs_of_pos hzp]
    linarith
  apply (χ.L_norm_bound_positive z hzp).trans
  apply (div_le_iff₀ hzp).mpr
  have h1 := mul_le_mul_of_nonneg_right hn (show 0 ≤ (χ.modulus : ℝ) + 1 by positivity)
  have h2 := mul_le_mul_of_nonneg_left hz
    (show 0 ≤ 2 * ((χ.modulus : ℝ) + 1) * (3 + |z.im|) by positivity)
  nlinarith

 theorem densityDetector_numerator_bound (χ : PrimitiveComplexCharacter) (X : ℕ)
    (s : ℂ) (_hs : 1 / 2 ≤ s.re) (hs1 : s.re ≤ 1) (Y : ℝ) (hY : 1 ≤ Y)
    (x u : ℝ) (hx : 1 / 2 - s.re ≤ x) (hx2 : x ≤ 2) :
    ‖χ.L (s + ((x : ℂ) + u * I)) * densityMollifier X χ.character (s + ((x : ℂ) + u * I)) *
      (Y : ℂ) ^ ((x : ℂ) + u * I)‖ ≤
        (2 * ((χ.modulus : ℝ) + 1) * X * Y ^ 2 * (3 + |s.im|)) * (1 + |u|) := by
  have hz : 1 / 2 ≤ (s + ((x : ℂ) + u * I)).re := by simp; linarith
  have hz3 : (s + ((x : ℂ) + u * I)).re ≤ 3 := by simp; linarith
  have hL := density_L_short_positive_bound χ _ hz hz3
  have hM := densityMollifier_norm_le χ X _ (by linarith)
  have hpow : ‖(Y : ℂ) ^ ((x : ℂ) + u * I)‖ ≤ Y ^ 2 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by linarith : 0 < Y)]
    have he : (((x : ℂ) + u * I).re) = x := by simp
    rw [he, ← Real.rpow_two]
    exact Real.rpow_le_rpow_of_exponent_le hY hx2
  have him : |(s + ((x : ℂ) + u * I)).im| ≤ |s.im| + |u| := by
    simpa using abs_add_le s.im u
  rw [norm_mul, norm_mul]
  apply (mul_le_mul (mul_le_mul hL hM (norm_nonneg _) (by positivity)) hpow
    (norm_nonneg _) (by positivity)).trans
  have hsimple : 3 + |(s + ((x : ℂ) + u * I)).im| ≤ (3 + |s.im|) * (1 + |u|) := by
    nlinarith [abs_nonneg s.im, abs_nonneg u]
  have h := mul_le_mul_of_nonneg_left hsimple
    (show 0 ≤ 2 * ((χ.modulus : ℝ) + 1) * X * Y ^ 2 by positivity)
  first | (convert h using 1 <;> ring) | exact (le_of_eq (by ring)).trans (h.trans (le_of_eq (by ring)))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityDetectorVertical
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integrability at the critical-line side of the actual detector -/

namespace Ostmann

open Complex MeasureTheory

 theorem densityDetectorIntegrand_line_continuous (χ : PrimitiveComplexCharacter) (X : ℕ)
    (s : ℂ) (Y : ℝ) (hY : 0 < Y) (x : ℝ) (hx : -1 < x) (hx0 : x ≠ 0) :
    Continuous (fun u : ℝ => densityDetectorIntegrand χ X s Y ((x : ℂ) + u * I)) := by
  apply continuous_iff_continuousAt.mpr
  intro u
  have hw : (x : ℂ) + u * I ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    exact hx0 (by simpa using hr)
  have ha : AnalyticAt ℂ (fun w => densityDetectorFactor χ X s Y w / w) ((x : ℂ) + u * I) :=
    (densityDetectorFactor_analytic χ X s Y hY _ (by simpa using hx)).div analyticAt_id hw
  have he : densityDetectorIntegrand χ X s Y = fun w => densityDetectorFactor χ X s Y w / w :=
    funext (densityDetectorIntegrand_eq χ X s Y)
  rw [he]
  exact ContinuousAt.comp (g := fun w : ℂ => densityDetectorFactor χ X s Y w / w)
    (f := fun v : ℝ => (x : ℂ) + v * I) ha.continuousAt (by fun_prop)

 theorem densityDetector_left_bound (χ : PrimitiveComplexCharacter) (X : ℕ)
    (s : ℂ) (hs : 1 / 2 < s.re) (hs1 : s.re ≤ 1) (Y : ℝ) (hY : 1 ≤ Y) (u : ℝ) :
    ‖densityDetectorIntegrand χ X s Y (((1 / 2 - s.re : ℝ) : ℂ) + u * I)‖ ≤
      (2 * ((χ.modulus : ℝ) + 1) * X * Y ^ 2 * (3 + |s.im|)) *
        (16 / (s.re - 1 / 2)) * (1 + |u|) ^ (-(2 : ℝ)) := by
  have hn := densityDetector_numerator_bound χ X s hs.le hs1 Y hY (1 / 2 - s.re) u le_rfl (by linarith)
  have hk := densityDetectorKernel_left_bound (s.re - 1 / 2) u (by linarith) (by linarith)
  have hx : (-(s.re - 1 / 2) : ℝ) = 1 / 2 - s.re := by ring
  rw [← Complex.ofReal_neg, hx] at hk
  rw [densityDetectorIntegrand, norm_mul]
  apply (mul_le_mul hn hk (norm_nonneg _) (by positivity)).trans_eq
  have he : (1 + |u|) * (1 + |u|) ^ (-(3 : ℝ)) = (1 + |u|) ^ (-(2 : ℝ)) := by
    rw [show -(2 : ℝ) = 1 + -(3 : ℝ) by ring,
      Real.rpow_add (by positivity : 0 < 1 + |u|), Real.rpow_one]
  calc
    _ = (2 * ((χ.modulus : ℝ) + 1) * X * Y ^ 2 * (3 + |s.im|)) *
        (16 / (s.re - 1 / 2)) * ((1 + |u|) * (1 + |u|) ^ (-(3 : ℝ))) := by ring
    _ = _ := by rw [he]

 theorem densityDetector_left_integrable (χ : PrimitiveComplexCharacter) (X : ℕ)
    (s : ℂ) (hs : 1 / 2 < s.re) (hs1 : s.re ≤ 1) (Y : ℝ) (hY : 1 ≤ Y) :
    Integrable (fun u : ℝ => densityDetectorIntegrand χ X s Y
      (((1 / 2 - s.re : ℝ) : ℂ) + u * I)) := by
  have hg : Integrable (fun u : ℝ => (1 + |u|) ^ (-(2 : ℝ))) := by
    simpa only [Real.norm_eq_abs] using
      (integrable_one_add_norm (E := ℝ) (by norm_num : (Module.finrank ℝ ℝ : ℝ) < 2))
  apply (hg.const_mul ((2 * ((χ.modulus : ℝ) + 1) * X * Y ^ 2 * (3 + |s.im|)) *
    (16 / (s.re - 1 / 2)))).mono'
  · exact (densityDetectorIntegrand_line_continuous χ X s Y (by linarith) _
      (by linarith) (by linarith)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (densityDetector_left_bound χ X s hs hs1 Y hY)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_RectangleVerticalLimit
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Passing a zero rectangle identity to its two convergent vertical lines -/

namespace Ostmann

open Complex Filter MeasureTheory
open scoped Topology Interval

 theorem rectangle_vertical_limit (f : ℂ → ℂ) (a b : ℝ)
    (ha : Integrable (fun u : ℝ => f ((a : ℂ) + u * I)))
    (hb : Integrable (fun u : ℝ => f ((b : ℂ) + u * I)))
    (ht : Tendsto (fun u : ℝ => ∫ x in a..b, f ((x : ℂ) + u * I)) atTop (𝓝 0))
    (hd : Tendsto (fun u : ℝ => ∫ x in a..b, f ((x : ℂ) + (-u) * I)) atTop (𝓝 0))
    (hz : ∀ᶠ T : ℝ in atTop, rectangleBoundaryIntegral f a b (-T) T = 0) :
    (∫ u : ℝ, f ((a : ℂ) + u * I)) = ∫ u : ℝ, f ((b : ℂ) + u * I) := by
  have hr := intervalIntegral_tendsto_integral hb tendsto_neg_atTop_atBot tendsto_id
  have hl := intervalIntegral_tendsto_integral ha tendsto_neg_atTop_atBot tendsto_id
  have hbd : Tendsto (fun T : ℝ => rectangleBoundaryIntegral f a b (-T) T) atTop
      (𝓝 (I * (∫ u : ℝ, f ((b : ℂ) + u * I)) - I * ∫ u : ℝ, f ((a : ℂ) + u * I))) := by
    simpa [rectangleBoundaryIntegral] using ((hd.sub ht).add (hr.const_mul I)).sub (hl.const_mul I)
  have hzero : Tendsto (fun T : ℝ => rectangleBoundaryIntegral f a b (-T) T) atTop (𝓝 0) :=
    tendsto_const_nhds.congr' (hz.mono fun _ h => h.symm)
  have he := tendsto_nhds_unique hbd hzero
  exact (mul_left_cancel₀ I_ne_zero (sub_eq_zero.mp he)).symm

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityDetectorHorizontal
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Vanishing horizontal edges for the actual zero detector -/

namespace Ostmann

open Complex MeasureTheory Filter Set
open scoped Topology Interval

 theorem densityDetector_high_bound (χ : PrimitiveComplexCharacter) (X : ℕ)
    (s : ℂ) (hs : 1 / 2 ≤ s.re) (hs1 : s.re ≤ 1) (Y : ℝ) (hY : 1 ≤ Y)
    (x u : ℝ) (hx : 1 / 2 - s.re ≤ x) (hx2 : x ≤ 2) (hu : 1 ≤ |u|) :
    ‖densityDetectorIntegrand χ X s Y ((x : ℂ) + u * I)‖ ≤
      2 * (2 * ((χ.modulus : ℝ) + 1) * X * Y ^ 2 * (3 + |s.im|)) / |u| ^ 2 := by
  let K := 2 * ((χ.modulus : ℝ) + 1) * X * Y ^ 2 * (3 + |s.im|)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hup : 0 < |u| := by linarith
  have hn := densityDetector_numerator_bound χ X s hs hs1 Y hY x u hx hx2
  have hk := densityDetectorKernel_high_bound x u hup
  rw [densityDetectorIntegrand, norm_mul]
  calc
    _ ≤ (K * (1 + |u|)) * (|u| ^ 3)⁻¹ := mul_le_mul hn hk (norm_nonneg _) (by positivity)
    _ ≤ (K * (2 * |u|)) * (|u| ^ 3)⁻¹ := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_left _ hK
      linarith
    _ = 2 * K / |u| ^ 2 := by field_simp

 theorem densityDetector_horizontal_bound (χ : PrimitiveComplexCharacter) (X : ℕ)
    (s : ℂ) (hs : 1 / 2 ≤ s.re) (hs1 : s.re ≤ 1) (Y : ℝ) (hY : 1 ≤ Y)
    (u : ℝ) (hu : 1 ≤ |u|) :
    ‖∫ x in (1 / 2 - s.re)..2, densityDetectorIntegrand χ X s Y ((x : ℂ) + u * I)‖ ≤
      (2 * (2 * ((χ.modulus : ℝ) + 1) * X * Y ^ 2 * (3 + |s.im|)) *
        |2 - (1 / 2 - s.re)|) / |u| ^ 2 := by
  have hab : 1 / 2 - s.re ≤ 2 := by linarith
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (fun x (hx : x ∈ Ι (1 / 2 - s.re) 2) => densityDetector_high_bound χ X s hs hs1 Y hY x u
      (by rw [uIoc_of_le hab] at hx; exact hx.1.le)
      (by rw [uIoc_of_le hab] at hx; exact hx.2) hu)
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ring

 theorem densityDetector_horizontal_tendsto (χ : PrimitiveComplexCharacter) (X : ℕ)
    (s : ℂ) (hs : 1 / 2 ≤ s.re) (hs1 : s.re ≤ 1) (Y : ℝ) (hY : 1 ≤ Y) :
    Tendsto (fun u : ℝ => ∫ x in (1 / 2 - s.re)..2,
      densityDetectorIntegrand χ X s Y ((x : ℂ) + u * I)) atTop (𝓝 0) ∧
    Tendsto (fun u : ℝ => ∫ x in (1 / 2 - s.re)..2,
      densityDetectorIntegrand χ X s Y ((x : ℂ) + (-u) * I)) atTop (𝓝 0) := by
  let K := 2 * (2 * ((χ.modulus : ℝ) + 1) * X * Y ^ 2 * (3 + |s.im|)) * |2 - (1 / 2 - s.re)|
  have ht : Tendsto (fun u : ℝ => K / u ^ 2) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero, Function.comp_apply] using
      (tendsto_inv_atTop_zero.comp (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0))).const_mul K
  constructor
  · rw [tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero' (Filter.Eventually.of_forall (fun _ => norm_nonneg _)) _ ht
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with u hu
    simpa only [abs_of_nonneg (by linarith : 0 ≤ u)] using
      densityDetector_horizontal_bound χ X s hs hs1 Y hY u (by rwa [abs_of_nonneg (by linarith)])
  · rw [tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero' (Filter.Eventually.of_forall (fun _ => norm_nonneg _)) _ ht
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with u hu
    have hb := densityDetector_horizontal_bound χ X s hs hs1 Y hY (-u)
      (by simpa only [abs_neg, abs_of_nonneg (by linarith : 0 ≤ u)] using hu)
    simpa only [abs_neg, abs_of_nonneg (by linarith : 0 ≤ u), Complex.ofReal_neg] using hb

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityDetectorShift
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact compact detector identity at an actual zero -/

namespace Ostmann

open Complex MeasureTheory Filter
open scoped Topology

 theorem densityDetector_right_integrable (χ : PrimitiveComplexCharacter) (X : ℕ)
    (s : ℂ) (hs : 1 / 2 ≤ s.re) (hs1 : s.re ≤ 1) (Y : ℝ) (hY : 1 ≤ Y) :
    Integrable (fun u : ℝ => densityDetectorIntegrand χ X s Y (2 + u * I)) := by
  let K := 2 * ((χ.modulus : ℝ) + 1) * X * Y ^ 2 * (3 + |s.im|)
  have hg : Integrable (fun u : ℝ => (1 + |u|) ^ (-(2 : ℝ))) := by
    simpa only [Real.norm_eq_abs] using
      (integrable_one_add_norm (E := ℝ) (by norm_num : (Module.finrank ℝ ℝ : ℝ) < 2))
  apply (hg.const_mul (K * 8)).mono'
  · exact (densityDetectorIntegrand_line_continuous χ X s Y (by linarith) 2
      (by norm_num) (by norm_num)).aestronglyMeasurable
  · filter_upwards with u
    have hn := densityDetector_numerator_bound χ X s hs hs1 Y hY 2 u (by linarith) le_rfl
    have hk := densityDetectorKernel_line_bound 2 u (by norm_num)
    rw [densityDetectorIntegrand, norm_mul]
    apply (mul_le_mul hn hk (norm_nonneg _) (by positivity)).trans_eq
    have he : (1 + |u|) * (1 + |u|) ^ (-(3 : ℝ)) = (1 + |u|) ^ (-(2 : ℝ)) := by
      rw [show -(2 : ℝ) = 1 + -(3 : ℝ) by ring,
        Real.rpow_add (by positivity : 0 < 1 + |u|), Real.rpow_one]
    calc
      _ = K * 8 * ((1 + |u|) * (1 + |u|) ^ (-(3 : ℝ))) := by dsimp [K]; ring
      _ = _ := by rw [he]

 theorem densityDetector_zero_contour_shift (χ : PrimitiveComplexCharacter) (X : ℕ)
    (s : ℂ) (hs : 1 / 2 < s.re) (hs1 : s.re ≤ 1) (hz : χ.L s = 0)
    (Y : ℝ) (hY : 1 ≤ Y) :
    (∫ u : ℝ, densityDetectorIntegrand χ X s Y (((1 / 2 - s.re : ℝ) : ℂ) + u * I)) =
      ∫ u : ℝ, densityDetectorIntegrand χ X s Y (2 + u * I) := by
  obtain ⟨ht, hd⟩ := densityDetector_horizontal_tendsto χ X s hs.le hs1 Y hY
  apply rectangle_vertical_limit _ _ _
    (densityDetector_left_integrable χ X s hs hs1 Y hY)
    (densityDetector_right_integrable χ X s hs.le hs1 Y hY) ht hd
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
  exact densityDetector_rectangle_zero χ X s hz Y (by linarith) (1 / 2 - s.re) 2 (-T) T
    (by linarith) (by linarith) (by norm_num) (by linarith) hT

 theorem densityDetectorMean_at_zero (χ : PrimitiveComplexCharacter) (X : ℕ)
    (s : ℂ) (hs : 1 / 2 < s.re) (hs1 : s.re ≤ 1) (hz : χ.L s = 0)
    (Y : ℝ) (hY : 1 ≤ Y) :
    densityDetectorMean χ X s Y = ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ u : ℝ,
      densityDetectorIntegrand χ X s Y (((1 / 2 - s.re : ℝ) : ℂ) + u * I) := by
  rw [densityDetectorMean_eq_integral χ X s (by linarith) Y (by linarith)]
  change _ * (∫ u : ℝ, densityDetectorIntegrand χ X s Y (2 + u * I)) = _
  rw [densityDetector_zero_contour_shift χ X s hs hs1 hz Y hY]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityDetectorDichotomy
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual polynomial-or-critical-integral alternative at every zero -/

namespace Ostmann

open Complex MeasureTheory
open scoped BigOperators

 theorem densityDetector_dichotomy (χ : PrimitiveComplexCharacter) (X : ℕ) (hX : 1 ≤ X)
    (s : ℂ) (hs : 1 / 2 < s.re) (hs1 : s.re ≤ 1) (hz : χ.L s = 0)
    (Y : ℝ) (hY : 4 ≤ Y) :
    (1 / 8 : ℝ) ≤ ‖∑ n ∈ (Finset.Icc 1 ⌊Y⌋₊).filter (fun n => X < n),
      LSeries.term (densityDetectorCharacterCoefficient χ X) s n * densityDetectorWeight (n / Y)‖ ∨
    (1 / 8 : ℝ) ≤ ‖((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ u : ℝ,
      densityDetectorIntegrand χ X s Y (((1 / 2 - s.re : ℝ) : ℂ) + u * I)‖ := by
  let P : ℂ := ∑ n ∈ (Finset.Icc 1 ⌊Y⌋₊).filter (fun n => X < n),
    LSeries.term (densityDetectorCharacterCoefficient χ X) s n * densityDetectorWeight (n / Y)
  by_cases hp : (1 / 8 : ℝ) ≤ ‖P‖
  · exact Or.inl hp
  · right
    have hsplit := densityDetectorMean_split χ X hX s Y (by linarith)
    have he : densityDetectorWeight (1 / Y) = densityDetectorMean χ X s Y - P := by
      rw [hsplit]
      dsimp [P]
      ring
    have hn := norm_sub_le (densityDetectorMean χ X s Y) P
    rw [← he] at hn
    have hw : (1 / 4 : ℝ) ≤ ‖densityDetectorWeight (1 / Y)‖ :=
      (densityDetectorWeight_at_one_div Y hY).trans (Complex.re_le_norm _)
    have hm : (1 / 8 : ℝ) ≤ ‖densityDetectorMean χ X s Y‖ := by
      have hp' : ‖P‖ < 1 / 8 := lt_of_not_ge hp
      linarith
    rwa [densityDetectorMean_at_zero χ X s hs hs1 hz Y (by linarith)] at hm

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityKernelPacking
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The cubic detector kernel on separated ordinates -/

namespace Ostmann

open scoped BigOperators

 theorem densityCubicWeight_nonneg (u : ℝ) : 0 ≤ densityCubicWeight u := by
  unfold densityCubicWeight
  positivity

 theorem densityCubicWeight_rpow (u : ℝ) :
    densityCubicWeight u = (1 + |u|) ^ (-(3 : ℝ)) := by
  rw [Real.rpow_neg (by positivity), Real.rpow_ofNat]
  simp [densityCubicWeight]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityCriticalDetector
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The detector in the height convention of the proved moments -/

namespace Ostmann

open Complex MeasureTheory

 theorem densityCriticalProduct_continuous (χ : PrimitiveComplexCharacter) (X : ℕ) (t : ℝ) :
    Continuous (densityCriticalProduct χ X t) := by
  have hL : Continuous χ.L := continuous_iff_continuousAt.mpr (fun z => (χ.L_analytic z).continuousAt)
  have hM : Continuous (densityMollifier X χ.character) := by
    apply continuous_iff_continuousAt.mpr
    intro z
    simpa only [zero_add] using (densityMollifier_shift_analytic χ X 0 z).continuousAt
  exact (hL.mul hM).comp (by unfold densityVerticalPoint; fun_prop)

 theorem densityCriticalProduct_bound (χ : PrimitiveComplexCharacter) (X : ℕ) (t u : ℝ) :
    ‖densityCriticalProduct χ X t u‖ ≤
      (2 * ((χ.modulus : ℝ) + 1) * X * (3 + 2 * Real.pi * |t| + 2 * Real.pi)) *
        (1 + |u|) := by
  have hL := density_L_short_positive_bound χ (densityVerticalPoint (1 / 2) (t + u))
    (by simp [densityVerticalPoint]) (by norm_num [densityVerticalPoint])
  have hM := densityMollifier_norm_le χ X (densityVerticalPoint (1 / 2) (t + u))
    (by simp [densityVerticalPoint])
  have ha : |(densityVerticalPoint (1 / 2) (t + u)).im| ≤
      2 * Real.pi * (|t| + |u|) := by
    have him : (densityVerticalPoint (1 / 2) (t + u)).im = 2 * Real.pi * (t + u) := by
      simp [densityVerticalPoint]
    rw [him]
    rw [abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
    exact mul_le_mul_of_nonneg_left (abs_add_le t u) (by positivity)
  have hb : 3 + |(densityVerticalPoint (1 / 2) (t + u)).im| ≤
      (3 + 2 * Real.pi * |t| + 2 * Real.pi) * (1 + |u|) := by
    nlinarith [Real.pi_pos, abs_nonneg t, abs_nonneg u,
      show 0 ≤ 2 * Real.pi * |t| * |u| by positivity]
  rw [densityCriticalProduct, norm_mul]
  apply (mul_le_mul hL hM (norm_nonneg _) (by positivity)).trans
  have h := mul_le_mul_of_nonneg_left hb
    (show 0 ≤ 2 * ((χ.modulus : ℝ) + 1) * X by positivity)
  first | (convert h using 1 <;> ring) | exact (le_of_eq (by ring)).trans (h.trans (le_of_eq (by ring)))

 theorem densityCriticalProduct_integrable (χ : PrimitiveComplexCharacter) (X : ℕ) (t : ℝ) :
    Integrable (fun u => densityCubicWeight u * ‖densityCriticalProduct χ X t u‖) := by
  let K := 2 * ((χ.modulus : ℝ) + 1) * X * (3 + 2 * Real.pi * |t| + 2 * Real.pi)
  have hg : Integrable (fun u : ℝ => (1 + |u|) ^ (-(2 : ℝ))) := by
    simpa only [Real.norm_eq_abs] using
      (integrable_one_add_norm (E := ℝ) (by norm_num : (Module.finrank ℝ ℝ : ℝ) < 2))
  apply (hg.const_mul K).mono'
  · exact ((by
      exact continuous_const.div ((continuous_const.add continuous_abs).pow 3)
        (fun u => by positivity) : Continuous densityCubicWeight).mul
      (densityCriticalProduct_continuous χ X t).norm).aestronglyMeasurable
  · filter_upwards with u
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (densityCubicWeight_nonneg _) (norm_nonneg _))]
    calc
      _ ≤ densityCubicWeight u * (K * (1 + |u|)) :=
        mul_le_mul_of_nonneg_left (densityCriticalProduct_bound χ X t u) (densityCubicWeight_nonneg u)
      _ = K * (1 + |u|) ^ (-(2 : ℝ)) := by
        rw [densityCubicWeight, Real.rpow_neg (by positivity), Real.rpow_ofNat]
        field_simp

 theorem densityCubicWeight_scaled (u : ℝ) :
    densityCubicWeight (2 * Real.pi * u) ≤ densityCubicWeight u := by
  unfold densityCubicWeight
  apply one_div_le_one_div_of_le (by positivity)
  apply pow_le_pow_left₀ (by positivity)
  rw [abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
  nlinarith [Real.pi_gt_three, abs_nonneg u]

 theorem densityDetector_scaled_bound (χ : PrimitiveComplexCharacter) (X : ℕ)
    (β t : ℝ) (hβ : 1 / 2 < β) (hβ1 : β ≤ 1) (Y : ℝ) (hY : 1 ≤ Y) (u : ℝ) :
    ‖densityDetectorIntegrand χ X (densityVerticalPoint β t) Y
      (((1 / 2 - β : ℝ) : ℂ) + (2 * Real.pi * u : ℝ) * I)‖ ≤
      (16 * Y ^ (1 / 2 - β) / (β - 1 / 2)) *
        (densityCubicWeight u * ‖densityCriticalProduct χ X t u‖) := by
  have he : densityVerticalPoint β t + (((1 / 2 - β : ℝ) : ℂ) + (2 * Real.pi * u : ℝ) * I) =
      densityVerticalPoint (1 / 2) (t + u) := by
    unfold densityVerticalPoint
    push_cast
    ring
  have hk := densityDetectorKernel_left_bound (β - 1 / 2) (2 * Real.pi * u)
    (by linarith) (by linarith)
  rw [← Complex.ofReal_neg, show -(β - 1 / 2) = 1 / 2 - β by ring,
    ← densityCubicWeight_rpow] at hk
  have hk' := hk.trans (mul_le_mul_of_nonneg_left (densityCubicWeight_scaled u) (by positivity))
  rw [densityDetectorIntegrand, norm_mul, norm_mul, he,
    Complex.norm_cpow_eq_rpow_re_of_pos (by linarith : 0 < Y)]
  simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero, zero_mul,
    sub_zero, add_zero]
  have hh := mul_le_mul_of_nonneg_left hk'
    (show 0 ≤ ‖densityCriticalProduct χ X t u‖ * Y ^ (1 / 2 - β) by positivity)
  convert hh using 1 <;> first | (with_reducible_and_instances rfl) | (dsimp [densityCriticalProduct])
  ring

 theorem densityDetectorMean_at_zero_bound (χ : PrimitiveComplexCharacter) (X : ℕ)
    (β t : ℝ) (hβ : 1 / 2 < β) (hβ1 : β ≤ 1)
    (hz : χ.L (densityVerticalPoint β t) = 0) (Y : ℝ) (hY : 1 ≤ Y) :
    ‖densityDetectorMean χ X (densityVerticalPoint β t) Y‖ ≤
      (16 * Y ^ (1 / 2 - β) / (β - 1 / 2)) *
        ∫ u : ℝ, densityCubicWeight u * ‖densityCriticalProduct χ X t u‖ := by
  rw [densityDetectorMean_at_zero χ X _ (by simpa [densityVerticalPoint] using hβ)
    (by simpa [densityVerticalPoint] using hβ1) hz Y hY]
  have hre : (densityVerticalPoint β t).re = β := by simp [densityVerticalPoint]
  rw [hre]
  have hscale := density_fourier_integral_scale (fun u => densityDetectorIntegrand χ X
    (densityVerticalPoint β t) Y (((1 / 2 - β : ℝ) : ℂ) + u * I))
  have hconst : ((1 / (2 * Real.pi) : ℝ) : ℂ) = (2 * (Real.pi : ℂ))⁻¹ := by
    simp
  rw [hconst]
  change ‖(2 * (Real.pi : ℂ))⁻¹ * (∫ u : ℝ, densityDetectorIntegrand χ X
    (densityVerticalPoint β t) Y (((1 / 2 - β : ℝ) : ℂ) + u * I))‖ ≤ _
  rw [hscale]
  apply (norm_integral_le_integral_norm _).trans
  rw [← integral_const_mul]
  apply integral_mono_of_nonneg
  · exact Filter.Eventually.of_forall (fun _ => norm_nonneg _)
  · exact (densityCriticalProduct_integrable χ X t).const_mul _
  · exact Filter.Eventually.of_forall (densityDetector_scaled_bound χ X β t hβ hβ1 Y hY)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityCriticalMass
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The literal critical-line mass controlling the integral alternative -/

namespace Ostmann

open MeasureTheory

 theorem densityCriticalMass_nonneg (χ : PrimitiveComplexCharacter) (X : ℕ) (t : ℝ) :
    0 ≤ densityCriticalMass χ X t :=
  integral_nonneg (fun _ => mul_nonneg (mul_nonneg (densityCubicWeight_nonneg _) (norm_nonneg _)) (norm_nonneg _))

 theorem densityCriticalMass_eq (χ : PrimitiveComplexCharacter) (X : ℕ) (t : ℝ) :
    (∫ u, densityCubicWeight u * ‖densityCriticalProduct χ X t u‖) = densityCriticalMass χ X t := by
  have he := integral_add_right_eq_self (μ := volume)
    (fun v => densityCubicWeight (v - t) * ‖χ.L (densityVerticalPoint (1 / 2) v)‖ *
      ‖densityMollifier X χ.character (densityVerticalPoint (1 / 2) v)‖) t
  convert he using 1
  all_goals try with_reducible_and_instances rfl
  apply integral_congr_ae
  filter_upwards with u
  simp only [add_sub_cancel_right, densityCriticalProduct, norm_mul]
  rw [add_comm u t]
  ring
  rfl

 theorem densityDetector_uniform_mass_bound (χ : PrimitiveComplexCharacter) (X : ℕ)
    (σ β t : ℝ) (hσ : 1 / 2 < σ) (hβ : σ ≤ β) (hβ1 : β ≤ 1)
    (hz : χ.L (densityVerticalPoint β t) = 0) (Y : ℝ) (hY : 1 ≤ Y) :
    ‖densityDetectorMean χ X (densityVerticalPoint β t) Y‖ ≤
      (16 * Y ^ (1 / 2 - σ) / (σ - 1 / 2)) * densityCriticalMass χ X t := by
  have hm := densityDetectorMean_at_zero_bound χ X β t (hσ.trans_le hβ) hβ1 hz Y hY
  rw [densityCriticalMass_eq] at hm
  apply hm.trans
  apply mul_le_mul_of_nonneg_right _ (densityCriticalMass_nonneg χ X t)
  calc
    _ ≤ (16 * Y ^ (1 / 2 - σ)) / (β - 1 / 2) := by
      apply div_le_div_of_nonneg_right _ (by linarith)
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hY (by linarith)) (by norm_num)
    _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by linarith) (by linarith)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityIntegralAlternative
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Counting the integral alternative at actual L-function zeros -/

namespace Ostmann

open MeasureTheory
open scoped BigOperators Classical

 theorem density_count_cube (R I K D : ℝ) (hR : 0 ≤ R) (hD : 0 ≤ D)
    (hlower : R ≤ K * I) (hfourth : I ^ 4 ≤ R * D) : R ^ 3 ≤ K ^ 4 * D := by
  by_cases hzero : R = 0
  · simpa only [hzero, zero_pow (by decide : (3 : ℕ) ≠ 0)] using
      mul_nonneg (by positivity : 0 ≤ K ^ 4) hD
  · have hpos : 0 < R := lt_of_le_of_ne hR (Ne.symm hzero)
    have hp := pow_le_pow_left₀ hR hlower 4
    rw [mul_pow] at hp
    have hu := mul_le_mul_of_nonneg_left hfourth (by positivity : 0 ≤ K ^ 4)
    have hh : R * R ^ 3 ≤ R * (K ^ 4 * D) := by nlinarith
    exact (mul_le_mul_iff_right₀ hpos).mp (by simpa only [mul_comm R] using hh)

 theorem density_integral_alternative_count :
    ∃ C : ℝ, 0 < C ∧ ∀ X Q : ℕ, 1 ≤ X → 1 ≤ Q → ∀ T σ Y : ℝ,
      2 ≤ T → 1 / 2 < σ → 1 ≤ Y →
      ∀ {ι : Type} (S : Finset ι) (c : ι → PrimitiveComplexCharacter) (β t : ι → ℝ),
      (∀ i ∈ S, (c i).modulus ≤ Q) → (∀ i ∈ S, |t i| ≤ T) →
      (∀ i ∈ S, ∀ j ∈ S, c i = c j → i ≠ j → 1 ≤ |t i - t j|) →
      (∀ i ∈ S, σ ≤ β i ∧ β i ≤ 1 ∧ (c i).L (densityVerticalPoint (β i) (t i)) = 0) →
      (∀ i ∈ S, (1 / 8 : ℝ) ≤ ‖densityDetectorMean (c i) X (densityVerticalPoint (β i) (t i)) Y‖) →
      (S.card : ℝ) ^ 3 ≤ C * (128 * Y ^ (1 / 2 - σ) / (σ - 1 / 2)) ^ 4 *
        ((Q : ℝ) ^ 2 * T) * ((X : ℝ) + (Q : ℝ) ^ 2 * T) ^ 2 *
        (Real.log ((Q : ℝ) * T)) ^ 6 * (1 + Real.log X) ^ 2 := by
  obtain ⟨C, hC, hb⟩ := density_packed_product_fourth
  refine ⟨C, hC, ?_⟩
  intro X Q hX hQ T σ Y hT hσ hY ι S c β t hc ht hsep hz hlarge
  let I0 := ∑ i ∈ S, densityCriticalMass (c i) X (t i)
  let K := 128 * Y ^ (1 / 2 - σ) / (σ - 1 / 2)
  let D := C * ((Q : ℝ) ^ 2 * T) * ((X : ℝ) + (Q : ℝ) ^ 2 * T) ^ 2 *
    (Real.log ((Q : ℝ) * T)) ^ 6 * (1 + Real.log X) ^ 2
  have hlower : (S.card : ℝ) ≤ K * I0 := by
    have hsum : (∑ _i ∈ S, (1 / 8 : ℝ)) ≤
        ∑ i ∈ S, (16 * Y ^ (1 / 2 - σ) / (σ - 1 / 2)) * densityCriticalMass (c i) X (t i) := by
      apply Finset.sum_le_sum
      intro i hi
      exact (hlarge i hi).trans (densityDetector_uniform_mass_bound (c i) X σ (β i) (t i)
        hσ (hz i hi).1 (hz i hi).2.1 (hz i hi).2.2 Y hY)
    simp only [Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum] at hsum
    have hh := mul_le_mul_of_nonneg_left hsum (by norm_num : (0 : ℝ) ≤ 8)
    refine (le_of_eq ?_).trans (hh.trans (le_of_eq ?_))
    · ring
    · dsimp [K, I0]
      ring
  have hfourth : I0 ^ 4 ≤ (S.card : ℝ) * D := by
    have h := hb X Q hX hQ T hT S c t hc ht hsep
    change I0 ^ 4 ≤ _ at h
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    dsimp [D]
    ring
  have hmain := density_count_cube (S.card : ℝ) I0 K D (Nat.cast_nonneg _) (by dsimp [D]; positivity)
    hlower hfourth
  convert hmain using 1
  all_goals try with_reducible_and_instances rfl
  dsimp [K, D]
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityIntegralBalanced
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The balanced Montgomery exponent for the integral alternative -/

namespace Ostmann

open MeasureTheory
open scoped BigOperators Classical

 theorem density_integral_alternative_balanced :
    ∃ C : ℝ, 0 < C ∧ ∀ Q : ℕ, 1 ≤ Q → ∀ T σ : ℝ,
      2 ≤ T → 1 / 2 < σ → σ ≤ 1 →
      1 / Real.log ((Q : ℝ) ^ 2 * T) ≤ σ - 1 / 2 →
      ∃ X : ℕ, 1 ≤ X ∧ (Q : ℝ) ^ 2 * T ≤ X ∧
      ∀ {ι : Type} (S : Finset ι) (c : ι → PrimitiveComplexCharacter) (β t : ι → ℝ),
      (∀ i ∈ S, (c i).modulus ≤ Q) → (∀ i ∈ S, |t i| ≤ T) →
      (∀ i ∈ S, ∀ j ∈ S, c i = c j → i ≠ j → 1 ≤ |t i - t j|) →
      (∀ i ∈ S, σ ≤ β i ∧ β i ≤ 1 ∧ (c i).L (densityVerticalPoint (β i) (t i)) = 0) →
      (∀ i ∈ S, (1 / 8 : ℝ) ≤ ‖densityDetectorMean (c i) X (densityVerticalPoint (β i) (t i))
        (((Q : ℝ) ^ 2 * T) ^ densityBalanceExponent σ)‖) →
      (S.card : ℝ) ^ 3 ≤ C * (((Q : ℝ) ^ 2 * T) ^ densityTargetExponent σ) ^ 3 *
        (Real.log ((Q : ℝ) * T)) ^ 12 := by
  obtain ⟨C, hC, hb⟩ := density_integral_alternative_count
  refine ⟨C * 256 ^ 4 * 17 ^ 2 * 20 ^ 2, by positivity, ?_⟩
  intro Q hQ T σ hT hσ hσ1 hgap
  obtain ⟨X, hX, hXB, hsize, hlogX⟩ := density_detector_cutoff Q hQ T hT
  refine ⟨X, hX, hXB, ?_⟩
  intro ι S c β t hc ht hs hz hlarge
  let B := (Q : ℝ) ^ 2 * T
  let Y := B ^ densityBalanceExponent σ
  let L := Real.log ((Q : ℝ) * T)
  have hq : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hB : 1 ≤ B := by dsimp [B]; nlinarith
  have hBp : 0 < B := lt_of_lt_of_le zero_lt_one hB
  have hY : 1 ≤ Y := Real.one_le_rpow hB (le_trans zero_le_one (density_balance_at_least_one σ hσ.le hσ1))
  have hYp : 0 < Y := lt_of_lt_of_le zero_lt_one hY
  have hL : 0 ≤ L := Real.log_nonneg (by nlinarith)
  have hXlog : 0 ≤ 1 + Real.log X := by
    have hx : (1 : ℝ) ≤ X := by exact_mod_cast hX
    have h := Real.log_nonneg hx
    linarith
  have hK : 128 * Y ^ (1 / 2 - σ) / (σ - 1 / 2) ≤
      256 * Y ^ (1 / 2 - σ) * L := by
    have h := density_away_inverse_gap Q hQ T σ hT hσ hgap
    have hm := mul_le_mul_of_nonneg_left h
      (show 0 ≤ 128 * Y ^ (1 / 2 - σ) by positivity)
    refine (le_of_eq ?_).trans (hm.trans (le_of_eq ?_))
    · ring
    · dsimp [L]
      ring
  have hpow : (Y ^ (1 / 2 - σ)) ^ (4 : ℕ) = Y ^ (2 - 4 * σ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hYp.le]
    congr 1
    ring
  have hK4 : (128 * Y ^ (1 / 2 - σ) / (σ - 1 / 2)) ^ 4 ≤
      256 ^ 4 * Y ^ (2 - 4 * σ) * L ^ 4 := by
    have h := pow_le_pow_left₀ (by positivity) hK 4
    simpa only [mul_pow, hpow] using h
  have hcount := hb X Q hX hQ T σ Y hT hσ hY S c β t hc ht hs hz hlarge
  apply hcount.trans
  calc
    _ ≤ C * (256 ^ 4 * Y ^ (2 - 4 * σ) * L ^ 4) * B * (17 * B) ^ 2 * L ^ 6 * (20 * L) ^ 2 := by
      gcongr
    _ = (C * 256 ^ 4 * 17 ^ 2 * 20 ^ 2) * (B ^ 3 * Y ^ (2 - 4 * σ)) * L ^ 12 := by ring
    _ = _ := by rw [density_balance_identity B σ hBp (by linarith)]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensitySeparatedCount
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Combining the two genuine detector alternatives at separated zeros -/

namespace Ostmann

open scoped BigOperators Classical

 theorem density_four_to_nine_logs (L : ℝ) (hL : Real.log 2 ≤ L) :
    L ^ 4 ≤ (Real.log 2)⁻¹ ^ 5 * L ^ 9 := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hp := pow_le_pow_left₀ hl.le hL 5
  calc
    L ^ 4 = (Real.log 2)⁻¹ ^ 5 * ((Real.log 2) ^ 5 * L ^ 4) := by
      rw [← mul_assoc, ← mul_pow, inv_mul_cancel₀ hl.ne', one_pow, one_mul]
    _ ≤ (Real.log 2)⁻¹ ^ 5 * (L ^ 5 * L ^ 4) := by gcongr
    _ = _ := by ring

 theorem density_separated_zero_count :
    ∃ C : ℝ, 0 < C ∧ ∀ Q : ℕ, 1 ≤ Q → ∀ T σ : ℝ,
      2 ≤ T → 4 ≤ (Q : ℝ) ^ 2 * T → 1 / 2 < σ → σ ≤ 1 →
      1 / Real.log ((Q : ℝ) ^ 2 * T) ≤ σ - 1 / 2 →
      ∀ {ι : Type} (R : Finset ι) (c : ι → PrimitiveComplexCharacter) (t β : ι → ℝ),
      (∀ i ∈ R, (c i).modulus ≤ Q) → (∀ i ∈ R, |t i| ≤ T) →
      (∀ i ∈ R, ∀ j ∈ R, c i = c j → i ≠ j → 1 ≤ |t i - t j|) →
      (∀ i ∈ R, σ ≤ β i ∧ β i ≤ 1 ∧ (c i).L (densityVerticalPoint (β i) (t i)) = 0) →
      (R.card : ℝ) ≤ C * ((Q : ℝ) ^ 2 * T) ^ densityTargetExponent σ *
        (Real.log ((Q : ℝ) * T)) ^ 9 := by
  obtain ⟨C1, hC1, hp⟩ := density_polynomial_alternative_balanced
  obtain ⟨C2, hC2, hi⟩ := density_integral_alternative_balanced
  refine ⟨C1 + (C2 + 1) * (Real.log 2)⁻¹ ^ 5, by positivity, ?_⟩
  intro Q hQ T σ hT hB4 hσ hσ1 hgap ι R c t β hc ht hs hz
  obtain ⟨X, hX, hBX, hiX⟩ := hi Q hQ T σ hT hσ hσ1 hgap
  let B := (Q : ℝ) ^ 2 * T
  let Y := B ^ densityBalanceExponent σ
  let L := Real.log ((Q : ℝ) * T)
  let p : ι → Prop := fun i => (1 / 8 : ℝ) ≤ ‖∑ n ∈ (Finset.Icc 1 ⌊Y⌋₊).filter (fun n => X < n),
    LSeries.term (densityDetectorCharacterCoefficient (c i) X) (densityVerticalPoint (β i) (t i)) n *
      densityDetectorWeight (n / Y)‖
  let P := R.filter p
  let N := R.filter (fun i => ¬p i)
  have hY : 4 ≤ Y := by
    have hh := Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ B)
      (density_balance_at_least_one σ hσ.le hσ1)
    rw [Real.rpow_one] at hh
    exact hB4.trans hh
  have hP := hp Q hQ T σ hT hσ.le hσ1 X hX hBX P c t β
    (fun i h => hc i (Finset.mem_filter.mp h).1)
    (fun i h => ht i (Finset.mem_filter.mp h).1)
    (fun i h j h' => hs i (Finset.mem_filter.mp h).1 j (Finset.mem_filter.mp h').1)
    (fun i h => ⟨(hz i (Finset.mem_filter.mp h).1).1, (hz i (Finset.mem_filter.mp h).1).2.1⟩)
    (fun _ h => (Finset.mem_filter.mp h).2)
  have hNlarge (i : ι) (hiN : i ∈ N) :
      (1 / 8 : ℝ) ≤ ‖densityDetectorMean (c i) X (densityVerticalPoint (β i) (t i)) Y‖ := by
    obtain ⟨hir, hn⟩ := Finset.mem_filter.mp hiN
    have hzi := hz i hir
    have hd := densityDetector_dichotomy (c i) X hX (densityVerticalPoint (β i) (t i))
      (by simpa [densityVerticalPoint] using hσ.trans_le hzi.1)
      (by simpa [densityVerticalPoint] using hzi.2.1) hzi.2.2 Y hY
    rcases hd with h | h
    · exact False.elim (hn h)
    · rw [densityDetectorMean_at_zero (c i) X _
        (by simpa [densityVerticalPoint] using hσ.trans_le hzi.1)
        (by simpa [densityVerticalPoint] using hzi.2.1) hzi.2.2 Y (by linarith)]
      exact h
  have hNcube := hiX N c β t
    (fun i h => hc i (Finset.mem_filter.mp h).1)
    (fun i h => ht i (Finset.mem_filter.mp h).1)
    (fun i h j h' => hs i (Finset.mem_filter.mp h).1 j (Finset.mem_filter.mp h').1)
    (fun i h => hz i (Finset.mem_filter.mp h).1) hNlarge
  have hN := density_balanced_count_from_cube C2 N.card B σ L hC2.le (Nat.cast_nonneg _)
    (by dsimp [B]; positivity) hNcube
  have hq : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hL : Real.log 2 ≤ L := Real.log_le_log (by norm_num) (by nlinarith)
  have hN' : (N.card : ℝ) ≤ (C2 + 1) * B ^ densityTargetExponent σ *
      ((Real.log 2)⁻¹ ^ 5 * L ^ 9) :=
    hN.trans (mul_le_mul_of_nonneg_left (density_four_to_nine_logs L hL) (by positivity))
  have hcard : (R.card : ℝ) = (P.card : ℝ) + (N.card : ℝ) := by
    exact_mod_cast (Finset.card_filter_add_card_filter_not (s := R) (p := p)).symm
  rw [hcard]
  have hh := add_le_add hP hN'
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  dsimp [B, L]
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityLocalMultiplicity
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Local ordinate bins retain the actual analytic zero multiplicities -/

namespace Ostmann

open scoped BigOperators Classical

 theorem density_local_index_count (χ : PrimitiveComplexCharacter) (S : Finset ℕ) (n : ℤ)
    (hr : ∀ i ∈ S, 1 / 2 ≤ ((actualCharacterZeros χ).zeros i).re)
    (hn : ∀ i ∈ S, ⌊((actualCharacterZeros χ).zeros i).im⌋ = n) :
    (S.card : ℝ) ≤ Real.log (48 * (χ.modulus : ℝ) * (|(n : ℝ) + 1 / 2| + 2)) /
      Real.log (14 / 13) := by
  let Z := actualCharacterZeros χ
  let F := S.image Z.zeros
  have hcard : S.card = ∑ z ∈ F, (S.filter fun i => Z.zeros i = z).card :=
    Finset.card_eq_sum_card_image Z.zeros S
  have hbound : (S.card : ℝ) ≤ ∑ z ∈ F, (characterZeroOrder χ z : ℝ) := by
    rw [hcard, Nat.cast_sum]
    apply Finset.sum_le_sum
    intro z _
    have h := actualCharacterZeros_respectsMultiplicity χ S z
    rw [characterZeroOrder_eq_nat]
    exact_mod_cast h
  have hlocal := characterZeroOrder_sum_le_local χ ((n : ℝ) + 1 / 2) F (by
    intro z hz
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
    have h := character_floor_mem_disk (Z.zeros i) (hr i hi) (Z.in_strip i).2.le
    change Z.zeros i ∈ Metric.closedBall (characterZeroCenter ((n : ℝ) + 1 / 2)) (13 / 8)
    have hni : ⌊(Z.zeros i).im⌋ = n := hn i hi
    simpa only [hni] using h)
  have hlocalR : (∑ z ∈ F, (characterZeroOrder χ z : ℝ)) ≤
      (characterLocalZeroMass χ ((n : ℝ) + 1 / 2) : ℝ) := by exact_mod_cast hlocal
  exact hbound.trans (hlocalR.trans (χ.local_zero_mass_bound _))

 theorem density_local_index_log_bound (Q : ℕ) (hQ : 1 ≤ Q) (T : ℝ) (hT : 2 ≤ T)
    (χ : PrimitiveComplexCharacter) (hχ : χ.modulus ≤ Q) (S : Finset ℕ) (n : ℤ)
    (hr : ∀ i ∈ S, 1 / 2 ≤ ((actualCharacterZeros χ).zeros i).re)
    (hn : ∀ i ∈ S, ⌊((actualCharacterZeros χ).zeros i).im⌋ = n)
    (hcenter : |(n : ℝ) + 1 / 2| ≤ T + 1) :
    (S.card : ℝ) ≤ (8 / Real.log (14 / 13)) * Real.log ((Q : ℝ) * T) := by
  have hq : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hc : (χ.modulus : ℝ) ≤ Q := by exact_mod_cast hχ
  have hcp : (0 : ℝ) < χ.modulus := by exact_mod_cast χ.positive
  have hl : Real.log 2 ≤ Real.log ((Q : ℝ) * T) := Real.log_le_log (by norm_num) (by nlinarith)
  have hlog : Real.log (48 * (χ.modulus : ℝ) * (|(n : ℝ) + 1 / 2| + 2)) ≤
      8 * Real.log ((Q : ℝ) * T) := by
    have hsize : 48 * (χ.modulus : ℝ) * (|(n : ℝ) + 1 / 2| + 2) ≤
        128 * ((Q : ℝ) * T) := by
      have h1 := mul_le_mul_of_nonneg_left hcenter (show 0 ≤ 48 * (χ.modulus : ℝ) by positivity)
      have h2 := mul_le_mul_of_nonneg_right hc (show 0 ≤ 48 * (T + 3) by positivity)
      nlinarith
    apply (Real.log_le_log (by positivity) hsize).trans
    rw [Real.log_mul (by norm_num) (by positivity)]
    have h128 : Real.log 128 = 7 * Real.log 2 := by
      have h := Real.log_pow (2 : ℝ) 7
      norm_num at h
      exact h
    rw [h128]
    linarith
  have h := (density_local_index_count χ S n hr hn).trans
    (div_le_div_of_nonneg_right hlog (Real.log_pos (by norm_num : (1 : ℝ) < 14 / 13)).le)
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityZeroBins
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual zero indices, unit ordinate bins and separated representatives -/

namespace Ostmann

open scoped BigOperators Classical

 theorem densityZeroIndices_mem (F : Finset PrimitiveComplexCharacter) (σ T : ℝ)
    (i : DensityZeroIndex) : i ∈ densityZeroIndices F σ T ↔
      i.1 ∈ F ∧ |((actualCharacterZeros i.1).zeros i.2).im| ≤ T ∧
        σ ≤ ((actualCharacterZeros i.1).zeros i.2).re := by
  simp [densityZeroIndices, ComplexZeroEnumeration.mem_heightIndices]

 theorem densityZeroIndices_card (F : Finset PrimitiveComplexCharacter) (σ T : ℝ) :
    ((densityZeroIndices F σ T).card : ℝ) =
      ∑ χ ∈ F, ((actualCharacterZeros χ).count σ T : ℝ) := by
  simp [densityZeroIndices, Finset.card_sigma, ComplexZeroEnumeration.count]

 theorem densityZeroBin_nonempty (S : Finset DensityZeroIndex) (k : DensityZeroBin)
    (hk : k ∈ S.image densityZeroBin) :
    ∃ n : ℕ, (⟨k.1, n⟩ : DensityZeroIndex) ∈ S ∧
      ⌊((actualCharacterZeros k.1).zeros n).im⌋ = k.2 := by
  obtain ⟨⟨χ, n⟩, hn, he⟩ := Finset.mem_image.mp hk
  cases he
  exact ⟨n, hn, rfl⟩

 theorem densityZeroBin_fiber_bound (Q : ℕ) (hQ : 1 ≤ Q) (T σ : ℝ)
    (hT : 2 ≤ T) (hσ : 1 / 2 ≤ σ) (F : Finset PrimitiveComplexCharacter)
    (hF : ∀ χ ∈ F, χ.modulus ≤ Q) (k : DensityZeroBin) :
    (((densityZeroIndices F σ T).filter fun i => densityZeroBin i = k).card : ℝ) ≤
      (8 / Real.log (14 / 13)) * Real.log ((Q : ℝ) * T) := by
  let S := (densityZeroIndices F σ T).filter fun i => densityZeroBin i = k
  let N := S.image (fun i => i.2)
  have hchar (i : DensityZeroIndex) (hi : i ∈ S) : i.1 = k.1 :=
    congrArg Sigma.fst (Finset.mem_filter.mp hi).2
  have hdata (n : ℕ) (hn : n ∈ N) :
      k.1 ∈ F ∧ |((actualCharacterZeros k.1).zeros n).im| ≤ T ∧
        σ ≤ ((actualCharacterZeros k.1).zeros n).re ∧
        ⌊((actualCharacterZeros k.1).zeros n).im⌋ = k.2 := by
    obtain ⟨⟨χ, m⟩, hm, rfl⟩ := Finset.mem_image.mp hn
    have hc := hchar ⟨χ, m⟩ hm
    dsimp at hc
    subst χ
    have hd := (densityZeroIndices_mem F σ T ⟨k.1, m⟩).mp (Finset.mem_filter.mp hm).1
    have hb := (Finset.mem_filter.mp hm).2
    have hb' : ⌊((actualCharacterZeros k.1).zeros m).im⌋ = k.2 :=
      congrArg (fun x : DensityZeroBin => x.2) hb
    exact ⟨hd.1, hd.2.1, hd.2.2, hb'⟩
  have hinj : Set.InjOn (fun i : DensityZeroIndex => i.2) S := by
    intro i hi j hj he
    exact Sigma.ext ((hchar i hi).trans (hchar j hj).symm) (heq_of_eq he)
  have hcard : N.card = S.card := Finset.card_image_of_injOn hinj
  by_cases hn : N.Nonempty
  · obtain ⟨n, hn⟩ := hn
    have hd := hdata n hn
    have hc := characterOrdinateBins_center_bound T k.2 (by
      rw [← hd.2.2.2]
      exact characterOrdinateBins_mem T _ hd.2.1)
    have hb := density_local_index_log_bound Q hQ T hT k.1 (hF k.1 hd.1) N k.2
      (fun n hn => hσ.trans (hdata n hn).2.2.1)
      (fun n hn => (hdata n hn).2.2.2) hc
    rwa [hcard] at hb
  · have hzero : N.card = 0 := Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hn)
    change (S.card : ℝ) ≤ _
    rw [← hcard, hzero, Nat.cast_zero]
    have hq : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
    apply mul_nonneg (by positivity)
    exact Real.log_nonneg (by nlinarith)

 theorem densityZeroIndices_bin_bound (Q : ℕ) (hQ : 1 ≤ Q) (T σ : ℝ)
    (hT : 2 ≤ T) (hσ : 1 / 2 ≤ σ) (F : Finset PrimitiveComplexCharacter)
    (hF : ∀ χ ∈ F, χ.modulus ≤ Q) :
    ((densityZeroIndices F σ T).card : ℝ) ≤
      ((densityZeroIndices F σ T).image densityZeroBin).card *
        ((8 / Real.log (14 / 13)) * Real.log ((Q : ℝ) * T)) := by
  rw [Finset.card_eq_sum_card_image densityZeroBin (densityZeroIndices F σ T), Nat.cast_sum]
  calc
    _ ≤ ∑ k ∈ (densityZeroIndices F σ T).image densityZeroBin,
        ((8 / Real.log (14 / 13)) * Real.log ((Q : ℝ) * T)) := by
      exact Finset.sum_le_sum fun k _ => densityZeroBin_fiber_bound Q hQ T σ hT hσ F hF k
    _ = _ := by simp

 theorem density_ordinate_bin_separation (x y : ℝ)
    (hm : ⌊x⌋ % 10 = ⌊y⌋ % 10) (hne : ⌊x⌋ ≠ ⌊y⌋) :
    1 ≤ |x / (2 * Real.pi) - y / (2 * Real.pi)| := by
  have hgap : ⌊x⌋ + 10 ≤ ⌊y⌋ ∨ ⌊y⌋ + 10 ≤ ⌊x⌋ := by omega
  have hphys : 9 ≤ |x - y| := by
    rcases hgap with h | h
    · have hc : (⌊x⌋ : ℝ) + 10 ≤ ⌊y⌋ := by exact_mod_cast h
      have hh : 9 ≤ y - x := by linarith [Int.floor_le y, Int.lt_floor_add_one x]
      rw [abs_sub_comm]
      exact hh.trans (le_abs_self _)
    · have hc : (⌊y⌋ : ℝ) + 10 ≤ ⌊x⌋ := by exact_mod_cast h
      exact (show 9 ≤ x - y by linarith [Int.floor_le x, Int.lt_floor_add_one y]).trans (le_abs_self _)
  rw [← sub_div, abs_div, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
  apply (le_div_iff₀ (by positivity : 0 < 2 * Real.pi)).mpr
  nlinarith [Real.pi_lt_four]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityAllZeros
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The separated density bound for every zero, with analytic multiplicities -/

namespace Ostmann

open scoped BigOperators Classical

 theorem density_all_zero_count :
    ∃ C : ℝ, 0 < C ∧ ∀ Q : ℕ, 1 ≤ Q → ∀ T σ : ℝ,
      2 ≤ T → 4 ≤ (Q : ℝ) ^ 2 * T → 1 / 2 < σ → σ ≤ 1 →
      1 / Real.log ((Q : ℝ) ^ 2 * T) ≤ σ - 1 / 2 →
      ∀ F : Finset PrimitiveComplexCharacter, (∀ χ ∈ F, χ.modulus ≤ Q) →
      (∑ χ ∈ F, ((actualCharacterZeros χ).count σ T : ℝ)) ≤
        C * ((Q : ℝ) ^ 2 * T) ^ densityTargetExponent σ *
          (Real.log ((Q : ℝ) * T)) ^ 10 := by
  obtain ⟨C, hC, hsep⟩ := density_separated_zero_count
  refine ⟨80 * C / Real.log (14 / 13), by positivity, ?_⟩
  intro Q hQ T σ hT hB hσ hσ1 hgap F hF
  let S := densityZeroIndices F σ T
  let K := S.image densityZeroBin
  let I := {k : DensityZeroBin // k ∈ K}
  have hex (k : I) : ∃ n : ℕ, (⟨k.val.1, n⟩ : DensityZeroIndex) ∈ S ∧
      ⌊((actualCharacterZeros k.val.1).zeros n).im⌋ = k.val.2 :=
    densityZeroBin_nonempty S k.val k.property
  choose idx hidx using hex
  let c : I → PrimitiveComplexCharacter := fun k => k.val.1
  let z : I → ℂ := fun k => (actualCharacterZeros (c k)).zeros (idx k)
  let t : I → ℝ := fun k => (z k).im / (2 * Real.pi)
  let β : I → ℝ := fun k => (z k).re
  have hdata (k : I) : c k ∈ F ∧ |(z k).im| ≤ T ∧ σ ≤ β k :=
    (densityZeroIndices_mem F σ T ⟨c k, idx k⟩).mp (hidx k).1
  have hfloor (k : I) : ⌊(z k).im⌋ = k.val.2 := (hidx k).2
  have hz (k : I) : densityVerticalPoint (β k) (t k) = z k := by
    apply Complex.ext
    · simp [densityVerticalPoint, β]
    · have him (a b : ℝ) : (densityVerticalPoint a b).im = 2 * Real.pi * b := by
        simp [densityVerticalPoint]
      rw [him]
      dsimp [t]
      field_simp
  let color : I → ℤ := fun k => k.val.2 % 10
  let U : Finset I := Finset.univ
  have hcount (j : ℤ) : ((U.filter fun k => color k = j).card : ℝ) ≤
      C * ((Q : ℝ) ^ 2 * T) ^ densityTargetExponent σ *
        (Real.log ((Q : ℝ) * T)) ^ 9 := by
    apply hsep Q hQ T σ hT hB hσ hσ1 hgap (U.filter fun k => color k = j) c t β
    · intro k _
      exact hF (c k) (hdata k).1
    · intro k _
      dsimp [t]
      rw [abs_div, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
      exact (div_le_self (abs_nonneg _) (by nlinarith [Real.pi_gt_three])).trans (hdata k).2.1
    · intro k hk l hl hcl hne
      apply density_ordinate_bin_separation
      · rw [hfloor k, hfloor l]
        exact (Finset.mem_filter.mp hk).2.trans (Finset.mem_filter.mp hl).2.symm
      · rw [hfloor k, hfloor l]
        intro hb
        apply hne
        apply Subtype.ext
        exact Sigma.ext hcl (heq_of_eq hb)
    · intro k _
      refine ⟨(hdata k).2.2, (actualCharacterZeros (c k)).in_strip (idx k) |>.2.le, ?_⟩
      rw [hz]
      exact (actualCharacterZeros (c k)).actual_zero (idx k)
  have hcolors : U.card = ∑ j ∈ Finset.Ico (0 : ℤ) 10, (U.filter fun k => color k = j).card := by
    apply Finset.card_eq_sum_card_fiberwise
    intro k _
    exact Finset.mem_Ico.mpr ⟨Int.emod_nonneg _ (by norm_num), Int.emod_lt_of_pos _ (by norm_num)⟩
  have hK : (K.card : ℝ) ≤ 10 * (C * ((Q : ℝ) ^ 2 * T) ^ densityTargetExponent σ *
      (Real.log ((Q : ℝ) * T)) ^ 9) := by
    have heq : U.card = K.card := by simp [U, I]
    rw [← heq, hcolors, Nat.cast_sum]
    calc
      _ ≤ ∑ _j ∈ Finset.Ico (0 : ℤ) 10,
          C * ((Q : ℝ) ^ 2 * T) ^ densityTargetExponent σ *
            (Real.log ((Q : ℝ) * T)) ^ 9 := Finset.sum_le_sum fun j _ => hcount j
      _ = _ := by
        norm_num
        left
        rfl
  have hq : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hlog : 0 ≤ Real.log ((Q : ℝ) * T) := Real.log_nonneg (by nlinarith)
  rw [← densityZeroIndices_card]
  have hb := densityZeroIndices_bin_bound Q hQ T σ hT hσ.le F hF
  calc
    _ ≤ (K.card : ℝ) * ((8 / Real.log (14 / 13)) * Real.log ((Q : ℝ) * T)) := hb
    _ ≤ (10 * (C * ((Q : ℝ) ^ 2 * T) ^ densityTargetExponent σ *
          (Real.log ((Q : ℝ) * T)) ^ 9)) *
        ((8 / Real.log (14 / 13)) * Real.log ((Q : ℝ) * T)) := by
      exact mul_le_mul_of_nonneg_right hK (by positivity)
    _ = _ := by ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityNearCritical
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Ordinary zero counting in the narrow strip next to the critical line -/

namespace Ostmann

open scoped BigOperators

 theorem density_near_critical_power (B σ : ℝ) (hB : 1 < B)
    (_hσ : 1 / 2 ≤ σ) (hσ1 : σ ≤ 1) (hnear : σ ≤ 1 / 2 + 1 / Real.log B) :
    B ≤ Real.exp 2 * B ^ (3 * (1 - σ) / (2 - σ)) := by
  let a := 3 * (1 - σ) / (2 - σ)
  have hl : 0 < Real.log B := Real.log_pos hB
  have hd : 0 < 2 - σ := by linarith
  have he : (1 - a) * (2 - σ) = 2 * (σ - 1 / 2) := by
    dsimp [a]
    field_simp
    ring
  have ht : 2 * (σ - 1 / 2) ≤ 2 / Real.log B := by
    rw [show 2 / Real.log B = 2 * (1 / Real.log B) by ring]
    linarith
  have hp : 2 / Real.log B ≤ (2 / Real.log B) * (2 - σ) := by
    apply le_mul_of_one_le_right (by positivity)
    linarith
  have ha : 1 - a ≤ 2 / Real.log B := by nlinarith
  have hm : (1 - a) * Real.log B ≤ 2 := by
    have hh := mul_le_mul_of_nonneg_right ha hl.le
    rwa [div_mul_cancel₀ _ hl.ne'] at hh
  calc
    B = Real.exp (Real.log B) := (Real.exp_log (by linarith)).symm
    _ ≤ Real.exp (2 + Real.log B * a) := Real.exp_le_exp.mpr (by nlinarith)
    _ = Real.exp 2 * B ^ a := by rw [Real.exp_add, Real.rpow_def_of_pos (by linarith)]

 theorem density_ordinary_family_bound (Q : ℕ) (hQ : 1 ≤ Q) (T : ℝ) (hT : 0 ≤ T)
    (σ : ℝ) (F : Finset PrimitiveComplexCharacter) (hF : ∀ χ ∈ F, χ.modulus ≤ Q) :
    (∑ χ ∈ F, ((actualCharacterZeros χ).count σ T : ℝ)) ≤
      (32 / Real.log (14 / 13)) * (Q : ℝ) ^ 2 * (T + 1) *
        Real.log ((Q : ℝ) * (T + 2)) := by
  calc
    _ ≤ ∑ χ ∈ F, ((actualCharacterZeros χ).count 0 T : ℝ) := by
      apply Finset.sum_le_sum
      intro χ _
      apply Nat.cast_le.mpr
      rw [ComplexZeroEnumeration.count_zero_eq_card]
      exact Finset.card_filter_le _ _
    _ ≤ _ := family_zero_count_of_individual (32 / Real.log (14 / 13))
      (by positivity)
      (fun χ U hU => (actualCharacterZeros χ).count_bound_of_multiplicity
        (actualCharacterZeros_respectsMultiplicity χ) U hU) Q hQ T hT F hF

 theorem density_log_thirteen_absorption (x : ℝ) (hx : Real.log 2 ≤ x) :
    x ≤ (Real.log 2)⁻¹ ^ 12 * x ^ 13 := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hx0 : 0 ≤ x := hl.le.trans hx
  have hp := pow_le_pow_left₀ hl.le hx 12
  have h : (Real.log 2) ^ 12 * x ≤ x ^ 13 := by
    calc
      _ ≤ x ^ 12 * x := mul_le_mul_of_nonneg_right hp hx0
      _ = _ := by ring
  calc
    x = (Real.log 2)⁻¹ ^ 12 * ((Real.log 2) ^ 12 * x) := by
      rw [← mul_assoc, ← mul_pow, inv_mul_cancel₀ hl.ne', one_pow, one_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left h (by positivity)

 theorem density_near_critical_family :
    ∃ C : ℝ, 0 < C ∧ ∀ Q : ℕ, 1 ≤ Q → ∀ T σ : ℝ, 2 ≤ T →
      1 / 2 ≤ σ → σ ≤ 1 → σ ≤ 1 / 2 + 1 / Real.log ((Q : ℝ) ^ 2 * T) →
      ∀ F : Finset PrimitiveComplexCharacter, (∀ χ ∈ F, χ.modulus ≤ Q) →
      (∑ χ ∈ F, ((actualCharacterZeros χ).count σ T : ℝ)) ≤
        C * ((Q : ℝ) ^ 2 * T) ^ (3 * (1 - σ) / (2 - σ)) *
          (Real.log ((Q : ℝ) * T)) ^ 13 := by
  let C0 := 32 / Real.log (14 / 13)
  refine ⟨4 * C0 * Real.exp 2 * (Real.log 2)⁻¹ ^ 12, by dsimp [C0]; positivity, ?_⟩
  intro Q hQ T σ hT hσ hσ1 hnear F hF
  have hq : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hq0 : (0 : ℝ) < Q := by linarith
  have hB : 1 < (Q : ℝ) ^ 2 * T := by nlinarith
  have hl : Real.log 2 ≤ Real.log ((Q : ℝ) * T) :=
    Real.log_le_log (by norm_num) (by nlinarith)
  have hl0 : 0 ≤ Real.log ((Q : ℝ) * T) := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le.trans hl
  have hlog : Real.log ((Q : ℝ) * (T + 2)) ≤ 2 * Real.log ((Q : ℝ) * T) := by
    calc
      _ ≤ Real.log (2 * ((Q : ℝ) * T)) := Real.log_le_log (by positivity) (by nlinarith)
      _ = Real.log 2 + Real.log ((Q : ℝ) * T) := Real.log_mul (by norm_num) (by positivity)
      _ ≤ _ := by linarith
  have hC : 0 ≤ C0 := by dsimp [C0]; positivity
  have hlog0 : 0 ≤ Real.log ((Q : ℝ) * (T + 2)) :=
    Real.log_nonneg (by nlinarith)
  have hordinary := density_ordinary_family_bound Q hQ T (by linarith) σ F hF
  have hpow := density_near_critical_power ((Q : ℝ) ^ 2 * T) σ hB hσ hσ1 hnear
  have habs := density_log_thirteen_absorption (Real.log ((Q : ℝ) * T)) hl
  calc
    _ ≤ C0 * (Q : ℝ) ^ 2 * (T + 1) * Real.log ((Q : ℝ) * (T + 2)) := hordinary
    _ ≤ C0 * (Q : ℝ) ^ 2 * (2 * T) * (2 * Real.log ((Q : ℝ) * T)) := by
      apply mul_le_mul _ hlog hlog0 (by positivity)
      exact mul_le_mul_of_nonneg_left (by linarith : T + 1 ≤ 2 * T) (by positivity)
    _ = 4 * C0 * ((Q : ℝ) ^ 2 * T) * Real.log ((Q : ℝ) * T) := by ring
    _ ≤ 4 * C0 * (Real.exp 2 * ((Q : ℝ) ^ 2 * T) ^ (3 * (1 - σ) / (2 - σ))) *
        ((Real.log 2)⁻¹ ^ 12 * (Real.log ((Q : ℝ) * T)) ^ 13) := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left hpow (by positivity)) habs hl0 (by positivity)
    _ = _ := by ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_ComplexDensityProof
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual Montgomery–Inoue zero-density input

The detector, fourth moment and large sieve prove the separated bound. Jensen
counts retain every analytic multiplicity when passing to the full enumeration.
This discharges the instance of Montgomery, *Zeros of L-functions* (1969),
Theorem 1, recorded in Inoue (2021), Lemma 1, needed by the main proof.
-/

namespace Ostmann

open scoped BigOperators

 theorem density_ten_to_thirteen_logs (L : ℝ) (hL : Real.log 2 ≤ L) :
    L ^ 10 ≤ (Real.log 2)⁻¹ ^ 3 * L ^ 13 := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hp := pow_le_pow_left₀ hl.le hL 3
  calc
    L ^ 10 = (Real.log 2)⁻¹ ^ 3 * ((Real.log 2) ^ 3 * L ^ 10) := by
      rw [← mul_assoc, ← mul_pow, inv_mul_cancel₀ hl.ne', one_pow, one_mul]
    _ ≤ (Real.log 2)⁻¹ ^ 3 * (L ^ 3 * L ^ 10) := by gcongr
    _ = _ := by ring

 theorem publishedComplexZeroDensity_oai : PublishedComplexZeroDensity actualCharacterZeros := by
  obtain ⟨C1, hC1, hnear⟩ := density_near_critical_family
  obtain ⟨C2, hC2, hfar⟩ := density_all_zero_count
  refine ⟨C1 + C2 * (Real.log 2)⁻¹ ^ 3, by positivity, ?_⟩
  intro Q hQ T σ hT hσ hσ1 F hF
  have hq : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hB : 1 < (Q : ℝ) ^ 2 * T := by nlinarith
  have hlogB : 0 < Real.log ((Q : ℝ) ^ 2 * T) := Real.log_pos hB
  have hL : Real.log 2 ≤ Real.log ((Q : ℝ) * T) :=
    Real.log_le_log (by norm_num) (by nlinarith)
  have hL0 : 0 ≤ Real.log ((Q : ℝ) * T) := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le.trans hL
  by_cases hn : σ ≤ 1 / 2 + 1 / Real.log ((Q : ℝ) ^ 2 * T)
  · exact (hnear Q hQ T σ hT hσ hσ1 hn F hF).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by positivity) :
        C1 ≤ C1 + C2 * (Real.log 2)⁻¹ ^ 3) (by positivity)) (by positivity))
  · have hs : 1 / 2 < σ := by
      have hi : 0 < 1 / Real.log ((Q : ℝ) ^ 2 * T) := by positivity
      linarith
    have hb4 : 4 ≤ (Q : ℝ) ^ 2 * T := by
      by_contra hh
      have hle : (Q : ℝ) ^ 2 * T ≤ 4 := le_of_lt (lt_of_not_ge hh)
      have hlog : Real.log ((Q : ℝ) ^ 2 * T) ≤ 2 := by
        have h := Real.log_le_log (by linarith) hle
        have h4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
          have hp := Real.log_pow (2 : ℝ) 2
          norm_num at hp
          exact hp
        rw [h4] at h
        have h2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
        linarith
      have hi : (1 / 2 : ℝ) ≤ 1 / Real.log ((Q : ℝ) ^ 2 * T) :=
        (le_div_iff₀ hlogB).mpr (by linarith)
      apply hn
      linarith
    have hg : 1 / Real.log ((Q : ℝ) ^ 2 * T) ≤ σ - 1 / 2 := by linarith
    have hf := hfar Q hQ T σ hT hb4 hs hσ1 hg F hF
    have ha := density_ten_to_thirteen_logs (Real.log ((Q : ℝ) * T)) hL
    calc
      _ ≤ C2 * ((Q : ℝ) ^ 2 * T) ^ densityTargetExponent σ *
          (Real.log ((Q : ℝ) * T)) ^ 10 := hf
      _ ≤ C2 * ((Q : ℝ) ^ 2 * T) ^ densityTargetExponent σ *
          ((Real.log 2)⁻¹ ^ 3 * (Real.log ((Q : ℝ) * T)) ^ 13) := by
        exact mul_le_mul_of_nonneg_left ha (by positivity)
      _ = (C2 * (Real.log 2)⁻¹ ^ 3) * ((Q : ℝ) ^ 2 * T) ^ (3 * (1 - σ) / (2 - σ)) *
          (Real.log ((Q : ℝ) * T)) ^ 13 := by unfold densityTargetExponent; ring
      _ ≤ _ := by
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (le_add_of_nonneg_left hC1.le) (by positivity)) (by positivity)

end Ostmann

end OAI
end

theorem solution : type_of% @OAI.Ostmann.publishedComplexZeroDensity_oai := @OAI.Ostmann.publishedComplexZeroDensity_oai
