-- Prove2me | solution 1 for Malliavin.predictableProjection_ae_eq_integral_predictableSectionKernel_Iic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:34:49.952804+00:00
-- url     : https://prove2.me/submissions/9944e3bd-59eb-4649-996c-81cd9518ec80

import Definitions.Def_Malliavin_ClarkOcone
import Mathlib.Probability.Kernel.Condexp
import Mathlib.Probability.Kernel.Composition.MapComap
import Definitions.Def_Malliavin_PredictableKernel
import Theorems.Thm_Malliavin_predictableProjection_ae_eq_sameTimeCondExpKernel_Iic

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
        fun p => ∫ w, U (p.1, w)
          ∂predictableSectionKernel (finiteHorizonProductMeasure P T) 𝓕 p := by
  refine (predictableProjection_ae_eq_sameTimeCondExpKernel_Iic 𝓕 U T).trans ?_
  apply Filter.Eventually.of_forall
  intro p
  change (∫ q, U (p.1, q.2)
      ∂condExpKernel (finiteHorizonProductMeasure P T) 𝓕.predictable p) =
    ∫ w, U (p.1, w)
      ∂predictableSectionKernel (finiteHorizonProductMeasure P T) 𝓕 p
  rw [predictableSectionKernel, Kernel.map_apply _ measurable_snd]
  exact (integral_map measurable_snd.aemeasurable
    ((Lp.stronglyMeasurable U).comp_measurable
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable).symm
end Malliavin
