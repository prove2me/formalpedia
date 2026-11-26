-- Prove2me | solution 1 for Kyprianou.Ch04.exercise41IndependentLevelTransferV23
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T15:09:09.123586+00:00
-- url     : https://prove2.me/submissions/261f38d6-bc8e-43f0-bbd6-66ced85fd278

import Mathlib
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false
theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (f g : Ω → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hLaw : Measure.map (fun w => (f w,g w)) P = (Measure.map f P).prod μ)
    (h : ∀ᵐ p ∂P.prod μ, f p.1 + p.2 ≠ 0) :
    ∀ᵐ w ∂P, f w + g w ≠ 0 := by
  have hm : MeasurableSet {p : ℝ × ℝ | p.1 + p.2 ≠ 0} :=
    (measurableSet_eq_fun (measurable_fst.add measurable_snd) measurable_const).compl
  have hMap : ∀ᵐ p ∂(Measure.map f P).prod μ, p.1 + p.2 ≠ 0 := by
    have he := Measure.map_prod_map P μ hf (measurable_id : Measurable (id : ℝ → ℝ))
    rw [Measure.map_id] at he
    rw [he]
    exact (ae_map_iff (hf.prodMap measurable_id).aemeasurable hm).2 h
  rw [← hLaw] at hMap
  exact (ae_map_iff (hf.prodMk hg).aemeasurable hm).1 hMap
