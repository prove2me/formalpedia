-- Prove2me | solution 1 for Kyprianou.Ch01.identDistrib_lift_productSnd
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T22:01:25.337143+00:00
-- url     : https://prove2.me/submissions/9d209790-96e0-4ad2-b2b0-dacfd7947b08

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
    (X Y : Λ → ℝ)
    (hX : Measurable X) (hY : Measurable Y)
    (hXY : IdentDistrib X Y Q Q) :
    IdentDistrib (fun p : Ω × Λ => X p.2)
      (fun p : Ω × Λ => Y p.2) (P.prod Q) (P.prod Q) := by
  have hp : MeasurePreserving Prod.snd (P.prod Q) Q :=
    MeasureTheory.measurePreserving_snd
  have hlaw (f : Λ → ℝ) (hf : Measurable f) :
      HasLaw (fun p : Ω × Λ => f p.2) (Q.map f) (P.prod Q) := by
    refine ⟨(hf.comp measurable_snd).aemeasurable, ?_⟩
    change (P.prod Q).map (f ∘ Prod.snd) = Q.map f
    rw [← Measure.map_map hf measurable_snd, hp.map_eq]
  have ha := hlaw X hX
  have hb := hlaw Y hY
  rw [hXY.map_eq] at ha
  exact ha.identDistrib hb
