-- Prove2me | solution 1 for Malliavin.predictableProjection_ae_eq_sameTimeCondExpKernel_Iic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:33:45.520537+00:00
-- url     : https://prove2.me/submissions/cdc7ef19-d204-40b4-a05c-c17258c11d37

import Definitions.Def_Malliavin_ClarkOcone
import Mathlib.Probability.Kernel.Condexp
import Mathlib.Probability.Kernel.Composition.MapComap
import Definitions.Def_Malliavin_PredictableKernel
import Theorems.Thm_Malliavin_condExpKernel_predictable_ae_same_time
import Theorems.Thm_Malliavin_predictableProjection_ae_eq_integral_condExpKernel_Iic

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal InnerProductSpace
open Malliavin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
namespace Malliavin
theorem _root_.solution
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) (U : TimeProcessL2 P) (T : ℝ≥0) :
    (predictableProjection 𝓕 U : ℝ≥0 × W → ℝ)
      =ᵐ[finiteHorizonProductMeasure P T]
        fun p => ∫ q, U (p.1, q.2)
          ∂condExpKernel (finiteHorizonProductMeasure P T) 𝓕.predictable p := by
  refine (predictableProjection_ae_eq_integral_condExpKernel_Iic 𝓕 U T).trans ?_
  filter_upwards [condExpKernel_predictable_ae_same_time
    (finiteHorizonProductMeasure P T) 𝓕] with p hp
  exact integral_congr_ae (hp.mono fun q hq ↦ by
    congr 1
    exact Prod.ext hq rfl)
end Malliavin
