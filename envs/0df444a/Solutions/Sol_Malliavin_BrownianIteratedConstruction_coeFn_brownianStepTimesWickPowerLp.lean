-- Prove2me | solution 1 for Malliavin.BrownianIteratedConstruction.coeFn_brownianStepTimesWickPowerLp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:39:27.692789+00:00
-- url     : https://prove2.me/submissions/99757e72-fe7d-4141-8fc6-8e27ffa44718

import Definitions.Def_Malliavin_BrownianHermiteMultipleIntegral
import Definitions.Def_Malliavin_BrownianPurePowerRecurrence
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_coeFn_polynomialFamilyLinearMap


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
omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    [BorelSpace W] [SecondCountableTopology W] [IsGaussian P]
namespace Malliavin.BrownianIteratedConstruction
theorem _root_.solution
    (hB : IsPreBrownianReal B P) (v : ℝ≥0 →₀ ℝ) (n : ℕ) :
    (brownianStepTimesWickPowerLp hB v n : W → ℝ) =ᵐ[P]
      fun w ↦ stepSum B v w *
        (varianceHermite (‖stepToLp v‖ ^ 2) n).eval (stepSum B v w) := by
  have h := coeFn_polynomialFamilyLinearMap
    (brownianStepPowerLp hB v) (stepSum B v)
    (fun k ↦ MemLp.coeFn_toLp (memLp_two_stepSum_pow hB v k))
    (Polynomial.X * varianceHermite (‖stepToLp v‖ ^ 2) n)
  filter_upwards [h] with w hw
  rw [brownianStepTimesWickPowerLp, hw, Polynomial.eval_mul,
    Polynomial.eval_X]
end Malliavin.BrownianIteratedConstruction
