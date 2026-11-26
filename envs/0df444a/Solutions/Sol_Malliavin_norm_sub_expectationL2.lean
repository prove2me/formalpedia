-- Prove2me | solution 1 for Malliavin.norm_sub_expectationL2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:34:41.377405+00:00
-- url     : https://prove2.me/submissions/fe629d47-16db-42db-a74b-0a32a0a7d2d0

import Definitions.Def_Malliavin_TimeDerivative
import Mathlib.Probability.Process.Predictable
import Definitions.Def_Malliavin_ClarkOcone
import Theorems.Thm_Malliavin_sub_expectationL2_eq_clarkOconeIntegral

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
theorem _root_.solution {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (C : ClarkOconeFamily B P 𝓕) (F : D12 P) :
    ‖F.1 - expectationL2 F.1‖ = ‖predictableDerivative C F‖ := by
  rw [sub_expectationL2_eq_clarkOconeIntegral C F]
  exact C.norm_itoIntegral _
end Malliavin
