-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_result81_upper_exit_ratio_unbounded_public
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T19:17:02.554266+00:00
-- url     : https://prove2.me/submissions/b12ec488-aea3-445c-bcdc-15bd805afbfe

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_twoSidedExitExpectation_eq_corrected
import Theorems.Thm_AvramDividend_Classical_unbounded_corrected_exit_scale_identity
open MeasureTheory Filter Set Topology
open AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {F : Filtration ℝ≥0 mΩ}
    (A : SpectrallyNegativeLevy P F)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction A q W)
    (hnbv : ¬ A.BoundedVariation)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a) :
    twoSidedExitExpectation A q a x = ENNReal.ofReal (W x / W a) := by
  calc
    twoSidedExitExpectation A q a x =
        twoSidedExitExpectationCorrected A q a x :=
      chat04_twoSidedExitExpectation_eq_corrected A q a x
    _ = ENNReal.ofReal (W x / W a) :=
      unbounded_corrected_exit_scale_identity A q hq W hW hnbv a x ha hx0 hxa
