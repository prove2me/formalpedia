-- Prove2me | solution 1 for Malliavin.BrownianIteratedConstruction.coeFn_brownianWickPowerLp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:18:15.20844+00:00
-- url     : https://prove2.me/submissions/d30e28ed-caca-4b5a-8a04-41a4661b97d0

import Definitions.Def_Malliavin_BrownianHermite
import Definitions.Def_Malliavin_BrownianCylinderDensity
import Definitions.Def_Malliavin_BrownianChaosTotality
import Definitions.Def_Malliavin_BrownianPolynomialHermite
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_coeFn_polynomialFamilyLinearMap


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
    (v : ℝ≥0 →₀ ℝ) (n : ℕ) :
    (brownianWickPowerLp hB v n : W → ℝ) =ᵐ[P]
      fun w ↦ (varianceHermite (‖stepToLp v‖ ^ 2) n).eval (stepSum B v w) := by
  apply coeFn_polynomialFamilyLinearMap
  intro k
  exact MemLp.coeFn_toLp _
end Malliavin.BrownianIteratedConstruction
