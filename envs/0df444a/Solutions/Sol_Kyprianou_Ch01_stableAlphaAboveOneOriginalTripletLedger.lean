-- Prove2me | solution 1 for Kyprianou.Ch01.stableAlphaAboveOneOriginalTripletLedger
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T23:50:15.044274+00:00
-- url     : https://prove2.me/submissions/06e9805f-5a34-4962-860f-1d5c2a49d8a6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Theorems.Thm_Kyprianou_Ch01_stableAboveOneOriginalTripletGammaLedger
import Theorems.Thm_Kyprianou_Ch01_stableAboveOneWeightedGammaCanonicalForm
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Complex
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (T : ProbabilityTheory.LevyKhintchineTriple)
    (alpha cpos cneg : ℝ)
    (ha0 : 0 < alpha) (ha2 : alpha < 2) (ha1 : 1 < alpha)
    (hcpos : 0 ≤ cpos) (hcneg : 0 ≤ cneg)
    (hnonzero : 0 < cpos + cneg) :
    let Pi : Measure ℝ :=
      (volume.restrict (Set.Ioi (0 : ℝ))).withDensity
        (fun x : ℝ => ENNReal.ofReal (cpos * x ^ (-alpha - 1))) +
      (volume.restrict (Set.Iio (0 : ℝ))).withDensity
        (fun x : ℝ => ENNReal.ofReal (cneg * |x| ^ (-alpha - 1)));
    T.gaussianVariance = 0 →
    T.levyMeasure = Pi →
    ∀ xi : ℝ,
        let sgn : ℝ := if 0 < xi then 1 else if xi < 0 then -1 else 0;
        -levyTripleExponent T xi =
          (((-Real.Gamma (-alpha) * Real.cos (Real.pi * alpha / 2) * (cpos + cneg)) * |xi| ^ alpha : ℝ) : ℂ) *
            (1 - Complex.I *
              (((((cpos - cneg) / (cpos + cneg)) * Real.tan (Real.pi * alpha / 2) * sgn : ℝ) : ℂ))) +
          Complex.I * ((((-T.drift - (cpos - cneg) / (alpha - 1)) * xi : ℝ) : ℂ)) := by
  intro Pi hgauss hmeasure xi sgn
  have hg :=
    Kyprianou.Ch01.stableAboveOneOriginalTripletGammaLedger
      T alpha cpos cneg ha0 ha1 ha2 hcpos hcneg hgauss hmeasure xi
  have ha :=
    Kyprianou.Ch01.stableAboveOneWeightedGammaCanonicalForm
      alpha cpos cneg xi ha1 ha2 hnonzero
  dsimp at hg ha
  rw [hg, ha]
