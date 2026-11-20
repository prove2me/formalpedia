-- Prove2me | solution 1 for Kyprianou.Ch01.stableAlphaBelowOnePositiveCompensatedKernelValue
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T20:39:36.492462+00:00
-- url     : https://prove2.me/submissions/01d5abf8-0cd4-4802-98bc-5975860d5fa2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Theorems.Thm_Kyprianou_Ch01_stableAlphaBelowOneFourierGammaAll
import Theorems.Thm_Kyprianou_Ch01_stableBelowOneCutoffComplexMoment
import Theorems.Thm_Kyprianou_Ch01_stableBelowOneCutoffComplexIntegrable
import Theorems.Thm_Kyprianou_Ch01_stableGammaComplexDeficitIntegrable
import Theorems.Thm_Kyprianou_Ch01_stableBelowOneCompensatedPositivePointwise
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Real Complex Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (alpha c xi : ℝ) (ha0 : 0 < alpha) (ha1 : alpha < 1) :
    (∫ r in Set.Ioi (0 : ℝ),
      (c * r ^ (-alpha - 1)) •
        ProbabilityTheory.levyCompensatedIntegrand xi r ∂volume) =
      (c : ℂ) *
        (if xi = 0 then 0 else
          ((Real.Gamma (-alpha) : ℝ) : ℂ) *
            Complex.exp ((alpha : ℂ) *
              Complex.log (-(Complex.I * (xi : ℂ))))) -
      Complex.I * (((c * xi / (1 - alpha) : ℝ) : ℂ)) := by
  let D : ℝ → ℂ := fun r =>
    (Complex.exp ((Complex.I * (xi : ℂ)) * (r : ℂ)) - 1) *
      (((r ^ (-alpha - 1) : ℝ) : ℂ))
  let B : ℝ → ℂ := fun r =>
    if r < 1 then (((r ^ (-alpha) : ℝ) : ℂ)) else 0
  have hD : IntegrableOn D (Set.Ioi (0 : ℝ)) := by
    by_cases hxi : xi = 0
    · subst xi
      simp [D]
    · have hw : Complex.I * (xi : ℂ) ≠ 0 :=
        mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr hxi)
      simpa only [D] using
        (Kyprianou.Ch01.stableGammaComplexDeficitIntegrable
          alpha ha0 ha1 (Complex.I * (xi : ℂ)) hw (by simp))
  have hB : IntegrableOn B (Set.Ioi (0 : ℝ)) := by
    exact Kyprianou.Ch01.stableBelowOneCutoffComplexIntegrable
      alpha ha0 ha1
  calc
    (∫ r in Set.Ioi (0 : ℝ),
        (c * r ^ (-alpha - 1)) •
          ProbabilityTheory.levyCompensatedIntegrand xi r ∂volume) =
      ∫ r in Set.Ioi (0 : ℝ),
        (c : ℂ) * D r -
          (Complex.I * ((c * xi : ℝ) : ℂ)) * B r ∂volume := by
          apply setIntegral_congr_fun measurableSet_Ioi
          intro r hr
          simpa only [D, B] using
            Kyprianou.Ch01.stableBelowOneCompensatedPositivePointwise
              alpha c xi r hr
    _ = (c : ℂ) * (∫ r in Set.Ioi (0 : ℝ), D r ∂volume) -
        (Complex.I * ((c * xi : ℝ) : ℂ)) *
          (∫ r in Set.Ioi (0 : ℝ), B r ∂volume) := by
          rw [integral_sub (hD.const_mul _) (hB.const_mul _),
            integral_const_mul, integral_const_mul]
    _ = (c : ℂ) *
        (if xi = 0 then 0 else
          ((Real.Gamma (-alpha) : ℝ) : ℂ) *
            Complex.exp ((alpha : ℂ) *
              Complex.log (-(Complex.I * (xi : ℂ))))) -
      Complex.I * (((c * xi / (1 - alpha) : ℝ) : ℂ)) := by
          have hGamma :=
            Kyprianou.Ch01.stableAlphaBelowOneFourierGammaAll
              alpha xi ha0 ha1
          have hcut :=
            Kyprianou.Ch01.stableBelowOneCutoffComplexMoment
              alpha ha0 ha1
          simp only [D, B] at *
          rw [hGamma, hcut]
          push_cast
          ring
