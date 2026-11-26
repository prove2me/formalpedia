-- Prove2me | solution 1 for Malliavin.le_filtrationPred
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:14:46.772798+00:00
-- url     : https://prove2.me/submissions/79d7c00c-8b09-4a23-9cac-27c67a832cfc

import Definitions.Def_Malliavin_ClarkOcone
import Definitions.Def_Malliavin_WienerChaos
import Mathlib.Probability.Kernel.Condexp
import Mathlib.Probability.ConditionalExpectation
import Definitions.Def_Malliavin_PointwiseCondExp

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
  [SecondCountableTopology W] [IsGaussian P]
namespace Malliavin
theorem _root_.solution {s t : ℝ≥0} (hst : s < t) : 𝓕 s ≤ filtrationPred 𝓕 t :=
  le_iSup₂ (f := fun (s : ℝ≥0) (_ : s < t) ↦ 𝓕 s) s hst
end Malliavin
