-- Prove2me | solution 1 for Malliavin.measureDense_brownianCylinderEvents
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:54:49.556256+00:00
-- url     : https://prove2.me/submissions/fe23e232-dbc7-4987-8270-be959ffb1b92

import Definitions.Def_Malliavin_PastCylinderDensity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Definitions.Def_Malliavin_BrownianCylinderDensity
import Theorems.Thm_Malliavin_isSetAlgebra_brownianCylinderEvents

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open NormedSpace
open scoped ENNReal NNReal InnerProductSpace
noncomputable section
open Malliavin
variable {E W : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
variable [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
  {B : ℝ≥0 → W → ℝ}
omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    [BorelSpace W] [SecondCountableTopology W] [IsGaussian P]
namespace Malliavin
theorem _root_.solution
    (hB : IsPreBrownianReal B P) (hgen : IsWienerGenerated B) :
    P.MeasureDense (brownianCylinderEvents B) := by
  let _ : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  exact Measure.MeasureDense.of_generateFrom_isSetAlgebra_finite
    (μ := P) (isSetAlgebra_brownianCylinderEvents B)
    (ambient_eq_generateFrom_brownianCylinderEvents hgen)
end Malliavin
