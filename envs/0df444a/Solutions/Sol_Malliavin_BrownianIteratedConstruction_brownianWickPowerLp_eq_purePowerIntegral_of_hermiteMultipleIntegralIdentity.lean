-- Prove2me | solution 1 for Malliavin.BrownianIteratedConstruction.brownianWickPowerLp_eq_purePowerIntegral_of_hermiteMultipleIntegralIdentity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:32:10.074986+00:00
-- url     : https://prove2.me/submissions/8737ed77-ce26-4a87-ba80-d2dafb626fc3

import Definitions.Def_Malliavin_BrownianPurePowerIntegral
import Definitions.Def_Malliavin_BrownianHermiteMultipleIntegral
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
    (hid : BrownianHigherHermiteMultipleIntegralIdentity hB)
    (v : ℝ≥0 →₀ ℝ) (n : ℕ) :
    brownianWickPowerLp hB v n =
      brownianPurePowerIntegral hB n (stepToLp v) := by
  cases n with
  | zero => exact (brownianPurePowerIntegral_zero_step hB v).symm
  | succ n =>
      cases n with
      | zero => exact (brownianPurePowerIntegral_one_step hB hsm v).symm
      | succ n => exact hid v (Nat.succ (Nat.succ n)) (by omega)
end Malliavin.BrownianIteratedConstruction
