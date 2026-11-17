-- Prove2me | solution 1 for Kyprianou.Ch01.identDistrib_lift_productFst
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T22:01:12.373836+00:00
-- url     : https://prove2.me/submissions/539328ff-bc6e-4ead-b3de-8b25a5033407

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
set_option autoImplicit false

theorem solution
    {Ω Λ : Type} [MeasurableSpace Ω] [MeasurableSpace Λ]
    (P : Measure Ω) (Q : Measure Λ)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (X Y : Ω → ℝ)
    (hX : Measurable X) (hY : Measurable Y)
    (hXY : IdentDistrib X Y P P) :
    IdentDistrib (fun p : Ω × Λ => X p.1)
      (fun p : Ω × Λ => Y p.1) (P.prod Q) (P.prod Q) := by
  have hp : MeasurePreserving Prod.fst (P.prod Q) P :=
    MeasureTheory.measurePreserving_fst
  have hlaw (f : Ω → ℝ) (hf : Measurable f) :
      HasLaw (fun p : Ω × Λ => f p.1) (P.map f) (P.prod Q) := by
    refine ⟨(hf.comp measurable_fst).aemeasurable, ?_⟩
    change (P.prod Q).map (f ∘ Prod.fst) = P.map f
    rw [← Measure.map_map hf measurable_fst, hp.map_eq]
  have ha := hlaw X hX
  have hb := hlaw Y hY
  rw [hXY.map_eq] at ha
  exact ha.identDistrib hb
