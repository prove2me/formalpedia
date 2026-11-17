-- Prove2me | solution 1 for Kyprianou.Ch01.logarithmicJumpCharExponent
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T05:41:06.968048+00:00
-- url     : https://prove2.me/submissions/f63d2960-65ad-4e52-94c4-d9e8ee878954

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_logarithmicJumpWeightsHasSumOne
import Theorems.Thm_Kyprianou_Ch01_logarithmicJumpCharFunWeights
import Theorems.Thm_Kyprianou_Ch01_logarithmicJumpFourierSummable
import Theorems.Thm_Kyprianou_Ch01_fourierSeriesCompensatorAlgebra
import Theorems.Thm_Kyprianou_Ch01_phaseExpNatPower
import Theorems.Thm_Kyprianou_Ch01_logarithmicCompensatedExponent
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Complex
set_option autoImplicit false

/-! The true logarithmic jump law has precisely the geometric Lévy exponent. -/
theorem solution
    (q xi : ℝ) (hq0 : 0 < q) (hq1 : q < 1)
    (jump : PMF ℕ)
    (hjump : ∀ n : ℕ, jump n = ENNReal.ofReal
      ((q ^ (n + 1) / ((n : ℝ) + 1)) / (-Real.log (1 - q)))) :
    (((-Real.log (1 - q) : ℝ) : ℂ) *
      (charFun (jump.toMeasure.map
        (fun n : ℕ => ((n + 1 : ℕ) : ℝ))) xi - 1)) =
      Complex.log (1 - (q : ℂ)) -
        Complex.log (1 - (q : ℂ) *
          Complex.exp ((xi : ℂ) * Complex.I)) := by
  let r : ℝ := -Real.log (1 - q)
  let w : ℕ → ℝ := fun n =>
    (q ^ (n + 1) / ((n : ℝ) + 1)) / r
  let z : ℕ → ℂ := fun n =>
    Complex.exp ((xi : ℂ) * (((n + 1 : ℕ) : ℝ) : ℂ) * Complex.I)
  let ζ : ℂ := Complex.exp ((xi : ℂ) * Complex.I)
  have hr : 0 < r := by
    dsimp [r]
    exact neg_pos.mpr (Real.log_neg (sub_pos.mpr hq1) (sub_lt_self 1 hq0))
  have hrne : r ≠ 0 := ne_of_gt hr
  have hwReal : HasSum w 1 := by
    simpa only [w, r] using
      Kyprianou.Ch01.logarithmicJumpWeightsHasSumOne q hq0 hq1
  have hwComplex : HasSum (fun n => (w n : ℂ)) 1 :=
    Complex.hasSum_ofReal.mpr hwReal
  have hmass : (∑' n, (w n : ℂ)) = 1 := hwComplex.tsum_eq
  have hsumWeights : Summable (fun n => (w n : ℂ)) :=
    hwComplex.summable
  have hsumFourier : Summable (fun n => (w n : ℂ) * z n) := by
    simpa only [w, r, z, Complex.ofReal_div, Complex.ofReal_pow,
      Complex.ofReal_neg, Complex.ofReal_add, Complex.ofReal_natCast,
      Complex.ofReal_one] using
        (Kyprianou.Ch01.logarithmicJumpFourierSummable q xi hq0 hq1)
  have hChar :
      charFun (jump.toMeasure.map
          (fun n : ℕ => ((n + 1 : ℕ) : ℝ))) xi =
        ∑' n, (w n : ℂ) * z n := by
    simpa only [w, r, z, Complex.real_smul] using
      (Kyprianou.Ch01.logarithmicJumpCharFunWeights
        q hq0 hq1 jump hjump xi)
  have hComp :=
    Kyprianou.Ch01.fourierSeriesCompensatorAlgebra
      (fun n => (w n : ℂ)) z hsumWeights hsumFourier hmass (r : ℂ)
  have hRate (n : ℕ) :
      (r : ℂ) * (w n : ℂ) =
        (q : ℂ) ^ (n + 1) / ((n : ℂ) + 1) := by
    have hreal : r * w n = q ^ (n + 1) / ((n : ℝ) + 1) := by
      dsimp [w]
      field_simp [hrne]
    simpa only [Complex.ofReal_mul, Complex.ofReal_div,
      Complex.ofReal_pow, Complex.ofReal_add, Complex.ofReal_natCast,
      Complex.ofReal_one] using congrArg (fun x : ℝ => (x : ℂ)) hreal
  have hqComplex : ‖(q : ℂ)‖ < 1 := by
    simpa [Complex.norm_real, abs_of_pos hq0] using hq1
  have hζnorm : ‖ζ‖ = 1 := by
    simp [ζ, Complex.norm_exp, Complex.mul_re]
  have hqζ : ‖(q : ℂ) * ζ‖ < 1 := by
    simpa [norm_mul, hζnorm, Complex.norm_real, abs_of_pos hq0] using hq1
  have hseries := Kyprianou.Ch01.logarithmicCompensatedExponent
    (q : ℂ) ζ hqComplex hqζ
  calc
    (((-Real.log (1 - q) : ℝ) : ℂ) *
      (charFun (jump.toMeasure.map
        (fun n : ℕ => ((n + 1 : ℕ) : ℝ))) xi - 1))
        = (r : ℂ) * ((∑' n, (w n : ℂ) * z n) - 1) := by
            rw [hChar]
    _ = ∑' n : ℕ, ((r : ℂ) * (w n : ℂ)) * (z n - 1) := hComp
    _ = ∑' n : ℕ, ((q : ℂ) ^ (n + 1) / ((n : ℂ) + 1)) *
        (ζ ^ (n + 1) - 1) := by
          apply tsum_congr
          intro n
          rw [hRate n]
          have hp := Kyprianou.Ch01.phaseExpNatPower xi n
          simp only [z, ζ] at hp ⊢
          rw [hp]
    _ = Complex.log (1 - (q : ℂ)) -
        Complex.log (1 - (q : ℂ) * ζ) := hseries
