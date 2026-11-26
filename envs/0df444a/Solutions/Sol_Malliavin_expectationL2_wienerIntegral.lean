-- Prove2me | solution 1 for Malliavin.expectationL2_wienerIntegral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:37:49.904804+00:00
-- url     : https://prove2.me/submissions/19f3557e-c6d9-494f-a97b-deb638a7d50c

import Definitions.Def_Malliavin_NaturalItoRange
import Definitions.Def_Malliavin_ClarkOconeExamples
import Definitions.Def_Malliavin_NaturalItoDuality
import Theorems.Thm_Malliavin_integral_wienerIntegral


set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
noncomputable section
open Malliavin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
  {B : ℝ≥0 → W → ℝ}
omit [CompleteSpace W] [BorelSpace W] [SecondCountableTopology W]
namespace Malliavin
theorem _root_.solution
    (hB : IsPreBrownianReal B P) (g : Lp ℝ 2 nonnegativeLebesgueMeasure) :
    expectationL2 (wienerIntegral hB g) = 0 := by
  unfold expectationL2
  rw [integral_wienerIntegral]
  exact map_zero _
end Malliavin
