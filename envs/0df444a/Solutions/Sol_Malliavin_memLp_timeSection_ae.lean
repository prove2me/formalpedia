-- Prove2me | solution 1 for Malliavin.memLp_timeSection_ae
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:12:20.252956+00:00
-- url     : https://prove2.me/submissions/1ce2b08f-cd34-4160-92ce-7dbb1838146e

import Definitions.Def_Malliavin_TimeDerivative
import Mathlib.Probability.Process.Predictable
import Definitions.Def_Malliavin_ClarkOcone

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
omit [CompleteSpace W] [BorelSpace W]
namespace Malliavin
theorem _root_.solution (U : TimeProcessL2 P) :
    ∀ᵐ t ∂nonnegativeLebesgueMeasure, MemLp (fun ω ↦ U (t, ω)) 2 P := by
  have hmeas := (Lp.memLp U).aestronglyMeasurable.prodMk_left
  have hint := (Lp.memLp U).integrable_sq.prod_right_ae
  filter_upwards [hmeas, hint] with t hmt hit
  exact (memLp_two_iff_integrable_sq hmt).2 hit
end Malliavin
