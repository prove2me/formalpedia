-- Prove2me | solution 1 for Kyprianou.Ch01.stableLevyExponentFormIndexOne
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T16:04:29.938239+00:00
-- url     : https://prove2.me/submissions/3a58e0c2-49e6-4a4d-90db-dd72128b3fc0

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Theorems.Thm_Kyprianou_Ch01_stableAlphaOneTripletToTwoSidedKernelNonnegative
import Theorems.Thm_Kyprianou_Ch01_stableAlphaOneTwoSidedIntegralValue
import Theorems.Thm_Kyprianou_Ch01_stableAlphaOneCanonicalFromTripletPhase
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter Complex
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (T : ProbabilityTheory.LevyKhintchineTriple)
    (cpos cneg : ℝ)
    (hcpos : 0 ≤ cpos) (hcneg : 0 ≤ cneg)
    (hnonzero : 0 < cpos + cneg) :
    let alpha : ℝ := 1;
    let Pi : Measure ℝ :=
      (volume.restrict (Set.Ioi (0 : ℝ))).withDensity
        (fun x : ℝ => ENNReal.ofReal (cpos * x ^ (-alpha - 1))) +
      (volume.restrict (Set.Iio (0 : ℝ))).withDensity
        (fun x : ℝ => ENNReal.ofReal (cneg * |x| ^ (-alpha - 1)));
    T.gaussianVariance = 0 →
    T.levyMeasure = Pi →
    ∃ c beta eta : ℝ,
      0 < c ∧ beta = (cpos - cneg) / (cpos + cneg) ∧
      ∀ xi : ℝ,
        let sgn : ℝ := if 0 < xi then 1 else if xi < 0 then -1 else 0;
        -levyTripleExponent T xi =
          ((c * |xi| : ℝ) : ℂ) *
            (1 + Complex.I *
              (((beta * (2 / Real.pi) * sgn * Real.log |xi| : ℝ) : ℂ))) +
          Complex.I * (((eta * xi : ℝ) : ℂ)) := by
  intro alpha Pi hVar hPi
  let F : ℝ → ℂ := (fun z : ℝ =>
      ∫ r in Set.Ioi (0 : ℝ),
        ((1 : ℂ) - Complex.exp (Complex.I * (((z * r : ℝ) : ℂ))) +
            Complex.I * (((z * r : ℝ) : ℂ)) *
              (if r < 1 then (1 : ℂ) else 0)) /
          ((((r : ℝ) ^ (2 : ℕ)) : ℝ) : ℂ) ∂volume)
  obtain ⟨k, hTwo⟩ := Kyprianou.Ch01.stableAlphaOneTwoSidedIntegralValue cpos cneg
  have hPhase : ∃ k : ℝ, ∀ xi : ℝ,
      -Kyprianou.Ch01.levyTripleExponent T xi = (((Real.pi * (cpos + cneg) * |xi| / 2 : ℝ) : ℂ) +
          Complex.I * ((((cpos - cneg) * xi * Real.log |xi| : ℝ) : ℂ)) -
          Complex.I * ((((T.drift + (cpos - cneg) * k) * xi : ℝ) : ℂ))) := by
    refine ⟨k, ?_⟩
    intro xi
    have hTrip :
        -Kyprianou.Ch01.levyTripleExponent T xi =
          -(Complex.I * (((T.drift * xi : ℝ) : ℂ))) + (cpos : ℂ) * F xi + (cneg : ℂ) * F (-xi) := by
      simpa only [F] using
        (Kyprianou.Ch01.stableAlphaOneTripletToTwoSidedKernelNonnegative
          T cpos cneg hcpos hcneg hVar hPi xi)
    have hKernel :
        (cpos : ℂ) * F xi + (cneg : ℂ) * F (-xi) = (((Real.pi * (cpos + cneg) * |xi| / 2 : ℝ) : ℂ) +
        Complex.I * ((((cpos - cneg) * xi * Real.log |xi| : ℝ) : ℂ)) -
        Complex.I * ((((cpos - cneg) * k * xi : ℝ) : ℂ))) := by
      simpa only [F] using hTwo xi
    calc
      -Kyprianou.Ch01.levyTripleExponent T xi =
          -(Complex.I * (((T.drift * xi : ℝ) : ℂ))) + ((cpos : ℂ) * F xi + (cneg : ℂ) * F (-xi)) := by
            rw [hTrip]
            ring
      _ = -(Complex.I * (((T.drift * xi : ℝ) : ℂ))) + (((Real.pi * (cpos + cneg) * |xi| / 2 : ℝ) : ℂ) +
        Complex.I * ((((cpos - cneg) * xi * Real.log |xi| : ℝ) : ℂ)) -
        Complex.I * ((((cpos - cneg) * k * xi : ℝ) : ℂ))) := by
            rw [hKernel]
      _ = (((Real.pi * (cpos + cneg) * |xi| / 2 : ℝ) : ℂ) +
          Complex.I * ((((cpos - cneg) * xi * Real.log |xi| : ℝ) : ℂ)) -
          Complex.I * ((((T.drift + (cpos - cneg) * k) * xi : ℝ) : ℂ))) := by
            push_cast
            ring
  exact Kyprianou.Ch01.stableAlphaOneCanonicalFromTripletPhase
    T cpos cneg hnonzero hPhase
