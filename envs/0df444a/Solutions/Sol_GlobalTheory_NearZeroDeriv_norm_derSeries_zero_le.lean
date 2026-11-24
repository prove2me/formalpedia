-- Prove2me | solution 1 for GlobalTheory.NearZeroDeriv.norm_derSeries_zero_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:02:43.302266+00:00
-- url     : https://prove2.me/submissions/bc07de56-eb59-436c-9a86-dab8ff477588

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_ZerosDisc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsBoundRight
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_IteratedDerivLogDerivDirichletLViaNearbyZerosStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_TuranSecondMainTheoremPowerSumsUnitCoefficientsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsLargeVonMangoldtLogPowerSeriesNearZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical
open GlobalTheory GlobalTheory.NearZeroDeriv
namespace GlobalTheory.NearZeroDeriv
theorem _root_.solution (c : ℕ → ℂ) (hc : ∀ n, ‖c n‖ ≤ 1) (σ t : ℝ) (hσ : 1 < σ) :
    ‖derSeries c 0 (σ + t * I)‖ ≤
      (derSeries (fun n : ℕ => (1 : DirichletCharacter ℂ 1) (n : ZMod 1)) 0 (σ + (0 : ℝ) * I)).re := by
  have hsum : Summable fun n : ℕ => Λ n * (n : ℝ) ^ (-σ) := by
    have := (LSeriesSummable_vonMangoldt (s := σ) (by simpa using hσ)).norm
    refine this.congr fun n => ?_
    rw [LSeries.norm_term_eq]
    split_ifs with h
    · simp [h]
    · rw [Complex.norm_real, Real.norm_of_nonneg vonMangoldt_nonneg, Complex.ofReal_re,
        Real.rpow_neg (by positivity), div_eq_mul_inv]
  have e : derSeries (fun n : ℕ => (1 : DirichletCharacter ℂ 1) (n : ZMod 1)) 0 (σ + (0 : ℝ) * I)
      = ((∑' n : ℕ, Λ n * (n : ℝ) ^ (-σ) : ℝ) : ℂ) := by
    rw [derSeries, Complex.ofReal_tsum]
    refine tsum_congr fun n => ?_
    rw [MulChar.one_apply (isUnit_of_subsingleton _), Complex.ofReal_mul,
      Complex.ofReal_cpow (by positivity)]
    simp
  rw [e, Complex.ofReal_re, derSeries]
  refine tsum_of_norm_bounded hsum.hasSum fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [norm_mul, norm_mul, norm_mul, Complex.norm_natCast_cpow_of_pos hn, Complex.norm_real,
      Real.norm_of_nonneg vonMangoldt_nonneg]
    have h1 : (-((σ : ℂ) + t * I)).re = -σ := by simp
    rw [h1]
    have := hc n
    have h2 : (0 : ℝ) ≤ Λ n := vonMangoldt_nonneg
    simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, norm_one, mul_one]
    gcongr
    exact mul_le_of_le_one_right h2 this
end GlobalTheory.NearZeroDeriv
