-- Prove2me | solution 1 for Kyprianou.Ch01.stableAlphaOnePositiveTripletKernelIntegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T17:39:40.42619+00:00
-- url     : https://prove2.me/submissions/ba97d60e-2555-416e-95f1-77a017cbc289

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Theorems.Thm_Kyprianou_Ch01_stableAlphaOnePositiveDensityIntegral
import Theorems.Thm_Kyprianou_Ch01_stableAlphaOneWeightedKernelIntegral
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Complex
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (cpos xi : ℝ) (hcpos : 0 ≤ cpos) :
    let alpha : ℝ := 1
    let muPos : Measure ℝ := (volume.restrict (Set.Ioi (0 : ℝ))).withDensity
        (fun x : ℝ => ENNReal.ofReal (cpos * x ^ (-alpha - 1)))
    let F : ℝ → ℂ := (fun z : ℝ =>
      ∫ r in Set.Ioi (0 : ℝ),
        ((1 : ℂ) - Complex.exp (Complex.I * (((z * r : ℝ) : ℂ))) +
            Complex.I * (((z * r : ℝ) : ℂ)) *
              (if r < 1 then (1 : ℂ) else 0)) /
          ((((r : ℝ) ^ (2 : ℕ)) : ℝ) : ℂ) ∂volume);
    -(∫ x, ProbabilityTheory.levyCompensatedIntegrand xi x ∂muPos) =
      (cpos : ℂ) * F xi := by
  intro alpha muPos F
  have hpow (r : ℝ) : r ^ (-alpha - 1) = r ^ (-2 : ℝ) := by
    dsimp [alpha]
    congr 1
    ring
  have hdensity :
      (∫ r, ProbabilityTheory.levyCompensatedIntegrand xi r ∂muPos) =
      (∫ r in Set.Ioi (0 : ℝ),
        (cpos * r ^ (-2 : ℝ)) •
          ProbabilityTheory.levyCompensatedIntegrand xi r ∂volume) := by
    simpa only [muPos, hpow] using
      (Kyprianou.Ch01.stableAlphaOnePositiveDensityIntegral cpos xi hcpos)
  have hweighted :=
      Kyprianou.Ch01.stableAlphaOneWeightedKernelIntegral cpos xi
  calc
    -(∫ r, ProbabilityTheory.levyCompensatedIntegrand xi r ∂muPos) =
      -(∫ r in Set.Ioi (0 : ℝ),
        (cpos * r ^ (-2 : ℝ)) •
          ProbabilityTheory.levyCompensatedIntegrand xi r ∂volume) :=
            congrArg Neg.neg hdensity
    _ = (cpos : ℂ) * F xi := by
      simpa only [F] using hweighted
