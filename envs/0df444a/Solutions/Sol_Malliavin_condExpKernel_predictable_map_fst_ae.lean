-- Prove2me | solution 1 for Malliavin.condExpKernel_predictable_map_fst_ae
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:04:03.956729+00:00
-- url     : https://prove2.me/submissions/544784fc-8181-482a-9691-8e65613bb339

import Definitions.Def_Malliavin_ClarkOcone
import Mathlib.Probability.Kernel.Condexp
import Mathlib.Probability.Kernel.Composition.MapComap
import Definitions.Def_Malliavin_PredictableKernel
import Theorems.Thm_Malliavin_condExpKernel_predictable_ae_same_time

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal InnerProductSpace
open Malliavin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
variable {S : Type*} [MeasurableSpace S] [StandardBorelSpace S]
namespace Malliavin
theorem _root_.solution
    (μ : Measure (ℝ≥0 × S)) [IsFiniteMeasure μ]
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace S›) :
    (condExpKernel μ 𝓕.predictable).map Prod.fst =ᵐ[μ]
      Kernel.deterministic Prod.fst (measurable_fst_predictable 𝓕) := by
  filter_upwards [condExpKernel_predictable_ae_same_time μ 𝓕] with p hp
  rw [Kernel.map_apply _ measurable_fst, Kernel.deterministic_apply]
  exact (hasLaw_dirac_of_ae_eq hp).map_eq
end Malliavin
