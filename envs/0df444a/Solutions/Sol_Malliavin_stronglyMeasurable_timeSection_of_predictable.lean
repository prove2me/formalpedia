-- Prove2me | solution 1 for Malliavin.stronglyMeasurable_timeSection_of_predictable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:54:18.47315+00:00
-- url     : https://prove2.me/submissions/a4e847ab-8d39-40ed-b966-f67a5a4a2fa6

import Definitions.Def_Malliavin_ClarkOcone
import Definitions.Def_Malliavin_WienerChaos
import Mathlib.Probability.Kernel.Condexp
import Mathlib.Probability.ConditionalExpectation
import Definitions.Def_Malliavin_PointwiseCondExp
import Theorems.Thm_Malliavin_measurable_section_predictable

set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace
open Malliavin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›)
omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
  [SecondCountableTopology W]
namespace Malliavin
theorem _root_.solution {V : ℝ≥0 × W → ℝ}
    (hV : StronglyMeasurable[𝓕.predictable] V) (t : ℝ≥0) :
    StronglyMeasurable[𝓕 t] fun ω ↦ V (t, ω) :=
  hV.comp_measurable (measurable_section_predictable 𝓕 t)
end Malliavin
