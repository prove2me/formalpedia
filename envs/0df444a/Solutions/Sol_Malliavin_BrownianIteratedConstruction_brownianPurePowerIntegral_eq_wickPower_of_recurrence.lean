-- Prove2me | solution 1 for Malliavin.BrownianIteratedConstruction.brownianPurePowerIntegral_eq_wickPower_of_recurrence
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:32:14.795374+00:00
-- url     : https://prove2.me/submissions/a614f14e-1518-4a53-92bc-d0f852b9d586

import Definitions.Def_Malliavin_BrownianHermiteMultipleIntegral
import Definitions.Def_Malliavin_BrownianPurePowerRecurrence
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_brownianWickPowerLp_add_two
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_brownianPurePowerIntegral_one_step
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_brownianPurePowerIntegral_zero_step


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
    (hrec : BrownianPurePowerHermiteRecurrence hB)
    (v : ℝ≥0 →₀ ℝ) (n : ℕ) :
    brownianPurePowerIntegral hB n (stepToLp v) =
      brownianWickPowerLp hB v n := by
  induction n using Nat.twoStepInduction with
  | zero => exact brownianPurePowerIntegral_zero_step hB v
  | one => exact brownianPurePowerIntegral_one_step hB hsm v
  | more n hn _hn1 =>
      rw [hrec v n, brownianWickPowerLp_add_two, hn]
end Malliavin.BrownianIteratedConstruction
