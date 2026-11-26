-- Prove2me | solution 1 for Malliavin.BrownianIteratedConstruction.map_stepSum_eq_gaussianReal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:06:19.625534+00:00
-- url     : https://prove2.me/submissions/d547dc5f-0ecc-4702-8dd5-9a0a928f8b12

import Definitions.Def_Malliavin_GaussianHermite
import Definitions.Def_Malliavin_BrownianPolynomialHermite
import Definitions.Def_Malliavin_BrownianWickIsometry
import Theorems.Thm_Malliavin_coeFn_stepToRandom
import Theorems.Thm_Malliavin_map_wienerIntegral_eq_gaussianReal


set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace
noncomputable section
open Malliavin Malliavin.BrownianIteratedConstruction
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
  {B : ℝ≥0 → W → ℝ}
omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
    [SecondCountableTopology W] [IsGaussian P]
namespace Malliavin.BrownianIteratedConstruction
theorem _root_.solution (hB : IsPreBrownianReal B P)
    (v : ℝ≥0 →₀ ℝ) :
    P.map (stepSum B v) = gaussianReal 0 (‖stepToLp v‖₊ ^ 2) := by
  calc
    P.map (stepSum B v) = P.map (stepToRandom hB v : W → ℝ) :=
      (Measure.map_congr (coeFn_stepToRandom hB v)).symm
    _ = P.map (wienerIntegral hB (stepToLp v) : W → ℝ) := by
      rw [wienerIntegral_stepToLp]
    _ = gaussianReal 0 (‖stepToLp v‖₊ ^ 2) :=
      map_wienerIntegral_eq_gaussianReal hB (stepToLp v)
end Malliavin.BrownianIteratedConstruction
