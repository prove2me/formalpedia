-- Prove2me | solution 1 for Malliavin.BrownianIteratedConstruction.brownianWickPowerLp_add_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:10:47.019949+00:00
-- url     : https://prove2.me/submissions/f78651c8-cf54-488b-8fed-484290f98f72

import Definitions.Def_Malliavin_BrownianHermiteMultipleIntegral
import Definitions.Def_Malliavin_BrownianPurePowerRecurrence
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_varianceHermite_succ


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
    brownianWickPowerLp hB v (n + 2) =
      brownianStepTimesWickPowerLp hB v (n + 1) -
        (‖stepToLp v‖ ^ 2 * ((n + 1 : ℕ) : ℝ)) •
          brownianWickPowerLp hB v n := by
  unfold brownianWickPowerLp brownianStepTimesWickPowerLp
  rw [show n + 2 = (n + 1) + 1 by omega,
    varianceHermite_succ, map_sub, ← Polynomial.smul_eq_C_mul, map_smul,
    Nat.add_sub_cancel]
end Malliavin.BrownianIteratedConstruction
