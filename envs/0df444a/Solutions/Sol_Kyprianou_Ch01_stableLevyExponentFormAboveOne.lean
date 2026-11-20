-- Prove2me | solution 1 for Kyprianou.Ch01.stableLevyExponentFormAboveOne
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T19:36:04.119333+00:00
-- url     : https://prove2.me/submissions/b080e047-5104-448f-89f1-25f294ceaccb
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Theorems.Thm_Kyprianou_Ch01_stableAlphaAboveOneCanonicalScalePositive
import Theorems.Thm_Kyprianou_Ch01_stableAlphaAboveOneOriginalTripletLedger
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter Complex
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
    ∃ c beta eta : ℝ,
      0 < c ∧ beta = (cpos - cneg) / (cpos + cneg) ∧
      ∀ xi : ℝ,
        let sgn : ℝ := if 0 < xi then 1 else if xi < 0 then -1 else 0;
        -levyTripleExponent T xi =
          ((c * |xi| ^ alpha : ℝ) : ℂ) *
            (1 - Complex.I *
              (((beta * Real.tan (Real.pi * alpha / 2) * sgn : ℝ) : ℂ))) +
          Complex.I * (((eta * xi : ℝ) : ℂ)) := by
  intro Pi hgauss hmeasure
  let c : ℝ :=
    -Real.Gamma (-alpha) * Real.cos (Real.pi * alpha / 2) *
      (cpos + cneg)
  let beta : ℝ := (cpos - cneg) / (cpos + cneg)
  let eta : ℝ := -T.drift - (cpos - cneg) / (alpha - 1)
  refine ⟨c, beta, eta, ?_, rfl, ?_⟩
  · dsimp [c]
    exact Kyprianou.Ch01.stableAlphaAboveOneCanonicalScalePositive
      alpha cpos cneg ha1 ha2 hnonzero
  · intro xi
    simpa only [c, beta, eta] using
      (Kyprianou.Ch01.stableAlphaAboveOneOriginalTripletLedger
        T alpha cpos cneg ha0 ha2 ha1 hcpos hcneg hnonzero
        hgauss hmeasure xi)
