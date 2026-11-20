-- Prove2me | solution 3 for Kyprianou.Ch01.stableBelowOneOriginalTripletGammaLedger
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T23:41:03.62316+00:00
-- url     : https://prove2.me/submissions/a5147eb8-4e6a-4ca6-84d2-524a861d31f1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Theorems.Thm_Kyprianou_Ch01_stableAlphaPowerTripletIntegralSplit
import Theorems.Thm_Kyprianou_Ch01_stableAlphaPowerNegativeWeightedIntegralReflect
import Theorems.Thm_Kyprianou_Ch01_stableAlphaBelowOnePositiveCompensatedKernelValue
import Theorems.Thm_Kyprianou_Ch01_levyTripleExponentZero
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Real Complex Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (T : ProbabilityTheory.LevyKhintchineTriple)
    (alpha cpos cneg : ℝ)
    (ha0 : 0 < alpha) (ha1 : alpha < 1)
    (hcpos : 0 ≤ cpos) (hcneg : 0 ≤ cneg) :
    let Pi : Measure ℝ :=
      (volume.restrict (Set.Ioi (0 : ℝ))).withDensity
        (fun x : ℝ => ENNReal.ofReal (cpos * x ^ (-alpha - 1))) +
      (volume.restrict (Set.Iio (0 : ℝ))).withDensity
        (fun x : ℝ => ENNReal.ofReal (cneg * |x| ^ (-alpha - 1)));
    let E : ℝ → ℂ := (fun z : ℝ => if z = 0 then (0 : ℂ) else
  Complex.exp ((alpha : ℂ) *
    Complex.log (-(Complex.I * (z : ℂ)))));
    T.gaussianVariance = 0 → T.levyMeasure = Pi →
    ∀ xi : ℝ,
      -levyTripleExponent T xi =
        -((Real.Gamma (-alpha) : ℝ) : ℂ) *
          ((cpos : ℂ) * E xi + (cneg : ℂ) * E (-xi)) +
        Complex.I * (((((cpos - cneg) / (1 - alpha) -
          T.drift) * xi : ℝ) : ℂ)) := by
  intro Pi E hgauss hmeasure xi
  by_cases hxi : xi = 0
  · subst xi
    simp [E, Kyprianou.Ch01.levyTripleExponentZero]
  · have hnegxi : -xi ≠ 0 := neg_ne_zero.mpr hxi
    have hsplit :=
      Kyprianou.Ch01.stableAlphaPowerTripletIntegralSplit
        T alpha cpos cneg xi hcpos hcneg hmeasure
    have href :=
      Kyprianou.Ch01.stableAlphaPowerNegativeWeightedIntegralReflect
        alpha cneg xi
    rw [href] at hsplit
    have hp :=
      Kyprianou.Ch01.stableAlphaBelowOnePositiveCompensatedKernelValue
        alpha cpos xi ha0 ha1
    have hn :=
      Kyprianou.Ch01.stableAlphaBelowOnePositiveCompensatedKernelValue
        alpha cneg (-xi) ha0 ha1
    simp only [if_neg hxi] at hp
    simp only [if_neg hnegxi] at hn
    have hsource :
        -levyTripleExponent T xi =
          -(Complex.I * ((T.drift * xi : ℝ) : ℂ)) -
            ((∫ r in Set.Ioi (0 : ℝ),
                (cpos * r ^ (-alpha - 1)) •
                  levyCompensatedIntegrand xi r ∂volume) +
             (∫ r in Set.Ioi (0 : ℝ),
                (cneg * r ^ (-alpha - 1)) •
                  levyCompensatedIntegrand (-xi) r ∂volume)) := by
      simp only [levyTripleExponent] 
      rw [hsplit, hgauss]
      simp
      ring
    rw [hsource, hp, hn]
    dsimp [E]
    rw [if_neg hxi, if_neg hnegxi]
    push_cast
    ring
