-- Prove2me | solution 1 for Malliavin.sub_expectationL2_eq_clarkOconeIntegral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:33:30.325203+00:00
-- url     : https://prove2.me/submissions/8909ec35-d9c9-4ed7-8cdc-56b263423674

import Definitions.Def_Malliavin_TimeDerivative
import Mathlib.Probability.Process.Predictable
import Definitions.Def_Malliavin_ClarkOcone
import Theorems.Thm_Malliavin_clarkOcone

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9
noncomputable section
open Malliavin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
  {B : ℝ≥0 → W → ℝ}
namespace Malliavin
theorem _root_.solution
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (C : ClarkOconeFamily B P 𝓕) (F : D12 P) :
    F.1 - expectationL2 F.1 = clarkOconeIntegral C F := by
  calc
    F.1 - expectationL2 F.1 =
        (expectationL2 F.1 + clarkOconeIntegral C F) - expectationL2 F.1 :=
      congrArg (fun X : RandomL2 P => X - expectationL2 F.1)
        (clarkOcone C F)
    _ = clarkOconeIntegral C F := by abel
end Malliavin
