-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m810_product_law_bounded_reward
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T02:32:39.707177+00:00
-- url     : https://prove2.me/submissions/742e16b1-7bb3-45fd-9013-9687e1fac813

import Mathlib.Probability.Process.Stopping
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.Instances.NNReal.Lemmas
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem _root_.solution
    {Ω β γ : Type} [MeasurableSpace Ω] [MeasurableSpace β] [MeasurableSpace γ]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (A : Set Ω) (Y : Ω → β) (V U : Ω → γ)
    (hY : Measurable Y) (hV : Measurable V) (hU : Measurable U)
    (hLaw : Measure.map (fun ω => (Y ω,V ω)) (P.restrict A) =
      (Measure.map Y (P.restrict A)).prod (Measure.map U P))
    (H : β × γ → ℝ) (hH : Measurable H) (C : ℝ)
    (hC : ∀ z, |H z| ≤ C) :
    (∫ ω in A, H (Y ω,V ω) ∂P) =
      ∫ ω in A, (∫ η, H (Y ω,U η) ∂P) ∂P := by
  have hbm : ∀ z, ‖H z‖ ≤ C := fun z => by rw [Real.norm_eq_abs]; exact hC z
  have hpair : Measurable fun ω => (Y ω, V ω) := hY.prodMk hV
  rw [← MeasureTheory.integral_map hpair.aemeasurable hH.aestronglyMeasurable, hLaw]
  have : IsProbabilityMeasure (Measure.map U P) := Measure.isProbabilityMeasure_map hU.aemeasurable
  have hint : Integrable H ((Measure.map Y (P.restrict A)).prod (Measure.map U P)) :=
    Integrable.of_bound hH.aestronglyMeasurable C (Filter.Eventually.of_forall hbm)
  rw [MeasureTheory.integral_prod H hint]
  have hinner : StronglyMeasurable fun b => ∫ v, H (b, v) ∂(Measure.map U P) :=
    hH.stronglyMeasurable.integral_prod_right'
  rw [MeasureTheory.integral_map hY.aemeasurable hinner.aestronglyMeasurable]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  exact MeasureTheory.integral_map hU.aemeasurable (hH.comp measurable_prodMk_left).aestronglyMeasurable

