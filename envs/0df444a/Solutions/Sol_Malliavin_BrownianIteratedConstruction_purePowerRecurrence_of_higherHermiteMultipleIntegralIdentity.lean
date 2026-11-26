-- Prove2me | solution 1 for Malliavin.BrownianIteratedConstruction.purePowerRecurrence_of_higherHermiteMultipleIntegralIdentity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:34:26.262686+00:00
-- url     : https://prove2.me/submissions/e1d69406-a8b9-422e-a962-fa275f3a6e1f

import Definitions.Def_Malliavin_BrownianHermiteMultipleIntegral
import Definitions.Def_Malliavin_BrownianPurePowerRecurrence
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_brownianWickPowerLp_add_two
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_brownianWickPowerLp_eq_purePowerIntegral_of_hermiteMultipleIntegralIdentity


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
namespace Malliavin.BrownianIteratedConstruction
theorem _root_.solution
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (hid : BrownianHigherHermiteMultipleIntegralIdentity hB) :
    BrownianPurePowerHermiteRecurrence hB := by
  intro v n
  rw [← brownianWickPowerLp_eq_purePowerIntegral_of_hermiteMultipleIntegralIdentity
      hB hsm hid v (n + 2),
    ← brownianWickPowerLp_eq_purePowerIntegral_of_hermiteMultipleIntegralIdentity
      hB hsm hid v n,
    brownianWickPowerLp_add_two]
end Malliavin.BrownianIteratedConstruction
