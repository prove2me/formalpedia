-- Prove2me | solution 1 for Kyprianou.Ch01.stableAlphaOneNegativeTripletKernelIntegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T17:23:29.176018+00:00
-- url     : https://prove2.me/submissions/e33afe1a-fe83-4434-a617-62974f4f47b0

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Theorems.Thm_Kyprianou_Ch01_stableAlphaOneNegativeDensityIntegral
import Theorems.Thm_Kyprianou_Ch01_stableAlphaOneNegativeWeightedIntegralReflect
import Theorems.Thm_Kyprianou_Ch01_stableAlphaOneWeightedKernelIntegral
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Complex
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (cneg xi : ℝ) (hcneg : 0 ≤ cneg) :
    let alpha : ℝ := 1
    let muNeg : Measure ℝ := (volume.restrict (Set.Iio (0 : ℝ))).withDensity
        (fun x : ℝ => ENNReal.ofReal (cneg * |x| ^ (-alpha - 1)))
    let F : ℝ → ℂ := (fun z : ℝ =>
      ∫ r in Set.Ioi (0 : ℝ),
        ((1 : ℂ) - Complex.exp (Complex.I * (((z * r : ℝ) : ℂ))) +
            Complex.I * (((z * r : ℝ) : ℂ)) *
              (if r < 1 then (1 : ℂ) else 0)) /
          ((((r : ℝ) ^ (2 : ℕ)) : ℝ) : ℂ) ∂volume);
    -(∫ x, ProbabilityTheory.levyCompensatedIntegrand xi x ∂muNeg) =
      (cneg : ℂ) * F (-xi) := by
  intro alpha muNeg F
  have hpow (r : ℝ) : |r| ^ (-alpha - 1) = |r| ^ (-2 : ℝ) := by
    dsimp [alpha]
    congr 1
    ring
  have hdensity :
      (∫ r, ProbabilityTheory.levyCompensatedIntegrand xi r ∂muNeg) =
      (∫ r in Set.Iio (0 : ℝ),
        (cneg * |r| ^ (-2 : ℝ)) •
          ProbabilityTheory.levyCompensatedIntegrand xi r ∂volume) := by
    simpa only [muNeg, hpow] using
      (Kyprianou.Ch01.stableAlphaOneNegativeDensityIntegral cneg xi hcneg)
  have hreflection :=
    Kyprianou.Ch01.stableAlphaOneNegativeWeightedIntegralReflect cneg xi
  have hweighted :=
    Kyprianou.Ch01.stableAlphaOneWeightedKernelIntegral cneg (-xi)
  calc
    -(∫ r, ProbabilityTheory.levyCompensatedIntegrand xi r ∂muNeg) =
        -(∫ r in Set.Iio (0 : ℝ),
          (cneg * |r| ^ (-2 : ℝ)) •
          ProbabilityTheory.levyCompensatedIntegrand xi r ∂volume) :=
            congrArg Neg.neg hdensity
    _ = -(∫ r in Set.Ioi (0 : ℝ),
          (cneg * r ^ (-2 : ℝ)) •
          ProbabilityTheory.levyCompensatedIntegrand (-xi) r ∂volume) :=
            congrArg Neg.neg hreflection
    _ = (cneg : ℂ) * F (-xi) := by
          simpa only [F] using hweighted
