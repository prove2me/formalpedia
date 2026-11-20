-- Prove2me | solution 1 for Kyprianou.Ch01.stableLevyExponentFormAwayFromOne
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T15:44:41.667429+00:00
-- url     : https://prove2.me/submissions/dd2cb487-e029-432a-8f9d-a4ca76c39835
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Theorems.Thm_Kyprianou_Ch01_stableLevyExponentFormBelowOne
import Theorems.Thm_Kyprianou_Ch01_stableLevyExponentFormAboveOne
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter Complex
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Split the original stable LK conclusion at the unique excluded alpha index. -/
theorem solution
    (T : ProbabilityTheory.LevyKhintchineTriple)
    (alpha cpos cneg : ℝ)
    (ha0 : 0 < alpha) (ha2 : alpha < 2) (ha1 : alpha ≠ 1)
    (hcpos : 0 ≤ cpos) (hcneg : 0 ≤ cneg)
    (hnonzero : 0 < cpos + cneg) :
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
          ((c * |xi| ^ alpha : ℝ) : ℂ) *
            (1 - Complex.I *
              (((beta * Real.tan (Real.pi * alpha / 2) * sgn : ℝ) : ℂ))) +
          Complex.I * (((eta * xi : ℝ) : ℂ))  := by
  intro Pi hVariance hMeasure
  rcases lt_trichotomy alpha 1 with hlt | heq | hgt
  · exact Kyprianou.Ch01.stableLevyExponentFormBelowOne
      T alpha cpos cneg ha0 ha2 hlt hcpos hcneg hnonzero hVariance hMeasure
  · exact (ha1 heq).elim
  · exact Kyprianou.Ch01.stableLevyExponentFormAboveOne
      T alpha cpos cneg ha0 ha2 hgt hcpos hcneg hnonzero hVariance hMeasure

