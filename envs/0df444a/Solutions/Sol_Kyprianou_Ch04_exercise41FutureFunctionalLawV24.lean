-- Prove2me | solution 1 for Kyprianou.Ch04.exercise41FutureFunctionalLawV24
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T15:37:11.235188+00:00
-- url     : https://prove2.me/submissions/4900dd26-3639-44bc-abba-66937255e88e

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise41DeterministicFutureProductV19
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false
open Kyprianou.Ch04
theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration NNReal inferInstance) (L : SpectrallyNegativeLevy P F)
    (s : NNReal) (G : (NNReal → ℝ) → ℝ) (hG : Measurable G) :
    Measure.map (fun w => (L.X s w, G (fun t => L.X (s+t) w - L.X s w))) P =
      (Measure.map (L.X s) P).prod (Measure.map (fun w => G (fun t => L.X t w)) P) := by
  letI : IsProbabilityMeasure P := L.isProbability
  let f : Ω → ℝ × (NNReal → ℝ) := fun w => (L.X s w,fun t => L.X (s+t) w - L.X s w)
  let g : ℝ × (NNReal → ℝ) → ℝ × ℝ := Prod.map id G
  have hx (t : NNReal) : Measurable (L.X t) := (L.adapted t).mono (F.le t) le_rfl
  have hf : Measurable f := (hx s).prodMk (measurable_pi_lambda _ (fun t => (hx (s+t)).sub (hx s)))
  have hg : Measurable g := measurable_id.prodMap hG
  have ho : Measurable (fun w t => L.X t w) := measurable_pi_lambda _ hx
  letI : IsProbabilityMeasure (Measure.map (L.X s) P) := Measure.isProbabilityMeasure_map (hx s).aemeasurable
  letI : IsProbabilityMeasure (Measure.map (fun w t => L.X t w) P) := Measure.isProbabilityMeasure_map ho.aemeasurable
  change Measure.map (g ∘ f) P = _
  rw [← Measure.map_map hg hf,show Measure.map f P = _ from exercise41DeterministicFutureProductV19 P F L s]
  rw [← Measure.map_prod_map _ _ measurable_id hG,Measure.map_id,Measure.map_map hG ho]
  rfl
