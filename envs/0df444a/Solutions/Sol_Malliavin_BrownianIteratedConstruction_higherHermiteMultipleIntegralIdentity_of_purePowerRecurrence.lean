-- Prove2me | solution 1 for Malliavin.BrownianIteratedConstruction.higherHermiteMultipleIntegralIdentity_of_purePowerRecurrence
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:33:38.642244+00:00
-- url     : https://prove2.me/submissions/6d18e6af-fd51-44f7-877d-d57e1253d0b8

import Definitions.Def_Malliavin_BrownianHermiteMultipleIntegral
import Definitions.Def_Malliavin_BrownianPurePowerRecurrence
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_brownianPurePowerIntegral_eq_wickPower_of_recurrence

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
    (hrec : BrownianPurePowerHermiteRecurrence hB) :
    BrownianHigherHermiteMultipleIntegralIdentity hB := by
  intro v n _hn
  exact (brownianPurePowerIntegral_eq_wickPower_of_recurrence
    hB hsm hrec v n).symm
end Malliavin.BrownianIteratedConstruction
