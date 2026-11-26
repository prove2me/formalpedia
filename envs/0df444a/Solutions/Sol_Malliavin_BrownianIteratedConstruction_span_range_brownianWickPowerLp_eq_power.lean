-- Prove2me | solution 1 for Malliavin.BrownianIteratedConstruction.span_range_brownianWickPowerLp_eq_power
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:30:12.880951+00:00
-- url     : https://prove2.me/submissions/95980c45-15e1-40b1-b667-a4bfed875ba6

import Definitions.Def_Malliavin_BrownianHermite
import Definitions.Def_Malliavin_BrownianCylinderDensity
import Definitions.Def_Malliavin_BrownianChaosTotality
import Definitions.Def_Malliavin_BrownianPolynomialHermite
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_span_range_polynomialFamilyLinearMap_varianceHermite


set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
noncomputable section
open Malliavin Malliavin.BrownianIteratedConstruction
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
  {B : ℝ≥0 → W → ℝ}
omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    [BorelSpace W] [SecondCountableTopology W] [IsGaussian P]
namespace Malliavin.BrownianIteratedConstruction
theorem _root_.solution (hB : IsPreBrownianReal B P)
    (v : ℝ≥0 →₀ ℝ) :
    Submodule.span ℝ (Set.range (brownianWickPowerLp hB v)) =
      Submodule.span ℝ (Set.range (brownianStepPowerLp hB v)) := by
  exact span_range_polynomialFamilyLinearMap_varianceHermite (‖stepToLp v‖ ^ 2)
    (brownianStepPowerLp hB v)
end Malliavin.BrownianIteratedConstruction
