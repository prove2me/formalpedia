-- Prove2me | solution 1 for Malliavin.BrownianIteratedConstruction.wickPurePowerMixedInnerIdentity_iff_higher
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:37:22.817395+00:00
-- url     : https://prove2.me/submissions/0d3b7593-32ee-47cf-867f-031f6492d880

import Definitions.Def_Malliavin_BrownianWickIsometry
import Definitions.Def_Malliavin_BrownianPurePowerRecurrence
import Definitions.Def_Malliavin_BrownianWickPurePowerComparison
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_brownianWickPurePowerMixedInner_zero
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_brownianWickPurePowerMixedInner_one

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
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t)) :
    BrownianWickPurePowerMixedInnerIdentity hB ↔
      BrownianHigherWickPurePowerMixedInnerIdentity hB := by
  constructor
  · intro hinner v n _
    exact hinner v n
  · intro hinner v n
    cases n with
    | zero => exact brownianWickPurePowerMixedInner_zero hB hsm v
    | succ n =>
        cases n with
        | zero => exact brownianWickPurePowerMixedInner_one hB hsm v
        | succ n => exact hinner v (Nat.succ (Nat.succ n)) (by omega)
end Malliavin.BrownianIteratedConstruction
