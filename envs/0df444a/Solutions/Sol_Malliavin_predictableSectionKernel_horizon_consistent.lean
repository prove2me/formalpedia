-- Prove2me | solution 1 for Malliavin.predictableSectionKernel_horizon_consistent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:56:46.702471+00:00
-- url     : https://prove2.me/submissions/4fee3259-58bc-4fb2-a920-947d869a2685

import Definitions.Def_Malliavin_PredictableKernel
import Definitions.Def_Malliavin_TimewiseCondExp
import Definitions.Def_Malliavin_NaturalFiltrationLeftContinuous
import Mathlib.MeasureTheory.Function.Floor
import Definitions.Def_Malliavin_KernelIdentification

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal InnerProductSpace
open Malliavin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
  {B : ℝ≥0 → W → ℝ}
namespace Malliavin
theorem _root_.solution
    (hB : IsPreBrownianReal B P) (hm : ∀ s, StronglyMeasurable (B s))
    (hgen : IsWienerGenerated B) {T₁ T₂ : ℝ≥0} (h : T₁ ≤ T₂) :
    ∀ᵐ t ∂finiteHorizonTimeMeasure T₁, 0 < t →
      ∀ᵐ w ∂P,
        predictableSectionKernel (finiteHorizonProductMeasure P T₁)
            (Filtration.natural B hm) (t, w)
          = predictableSectionKernel (finiteHorizonProductMeasure P T₂)
              (Filtration.natural B hm) (t, w) := by
  have hle : finiteHorizonTimeMeasure T₁ ≤ finiteHorizonTimeMeasure T₂ := by
    unfold finiteHorizonTimeMeasure
    exact Measure.restrict_mono (Set.Iic_subset_Iic.mpr h) le_rfl
  have h1 := predictableSectionKernel_ae_eq_condExpKernel hB hm hgen T₁
  have h2 : ∀ᵐ t ∂finiteHorizonTimeMeasure T₁, 0 < t →
      ∀ᵐ w ∂P,
        predictableSectionKernel (finiteHorizonProductMeasure P T₂)
            (Filtration.natural B hm) (t, w)
          = condExpKernel P (Filtration.natural B hm t) w :=
    ae_mono hle (predictableSectionKernel_ae_eq_condExpKernel hB hm hgen T₂)
  filter_upwards [h1, h2] with t ht1 ht2 hat
  filter_upwards [ht1 hat, ht2 hat] with w hw1 hw2
  rw [hw1, hw2]
end Malliavin
