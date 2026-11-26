-- Prove2me | solution 1 for Malliavin.adaptedIndicator_coeFn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:22:03.831056+00:00
-- url     : https://prove2.me/submissions/ee27fe0c-ca5d-43b6-82b6-e0d6044471f1

import Definitions.Def_Malliavin_ClarkOcone
import Definitions.Def_Malliavin_PredictableDensity

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Function
open scoped ENNReal NNReal InnerProductSpace
universe u_1 u_2 u_3 u_4 u_5
noncomputable section
open Malliavin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
omit [CompleteSpace W] [BorelSpace W] [SecondCountableTopology W]
namespace Malliavin
theorem _root_.solution
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) (a : ℝ≥0)
    {F : Set W} (hF : MeasurableSet[𝓕 a] F) :
    (adaptedIndicator (P := P) 𝓕 a hF : W → ℝ) =ᵐ[P]
      F.indicator (fun _ ↦ (1 : ℝ)) :=
  indicatorConstLp_coeFn (p := 2) (hs := 𝓕.le a F hF)
    (hμs := measure_ne_top P F) (c := (1 : ℝ))
end Malliavin
