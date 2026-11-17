-- Prove2me | solution 1 for Kyprianou.Ch01.iIndepFun_lift_productSnd
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T22:01:18.354562+00:00
-- url     : https://prove2.me/submissions/b1b5d485-2987-4881-886a-6c47107234dd

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
set_option autoImplicit false

theorem solution
    {Ω Λ ι : Type} [MeasurableSpace Ω] [MeasurableSpace Λ]
    [Fintype ι]
    (P : Measure Ω) (Q : Measure Λ)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (F : ι → Λ → ℝ)
    (hF : ∀ i, Measurable (F i))
    (hIndep : iIndepFun F Q) :
    iIndepFun (fun i (p : Ω × Λ) => F i p.2) (P.prod Q) := by
  classical
  have hp : MeasurePreserving Prod.snd (P.prod Q) Q :=
    MeasureTheory.measurePreserving_snd
  have hmap (f : Λ → ℝ) (hf : Measurable f) :
      (P.prod Q).map (fun p : Ω × Λ => f p.2) = Q.map f := by
    change (P.prod Q).map (f ∘ Prod.snd) = Q.map f
    rw [← Measure.map_map hf measurable_snd, hp.map_eq]
  have hpi : Measurable (fun ω : Λ => fun i : ι => F i ω) :=
    measurable_pi_lambda _ hF
  have hmapPi :
      (P.prod Q).map (fun p : Ω × Λ => fun i : ι => F i p.2) =
      Q.map (fun ω : Λ => fun i : ι => F i ω) := by
    change (P.prod Q).map
      ((fun ω : Λ => fun i : ι => F i ω) ∘ Prod.snd) =
      Q.map (fun ω : Λ => fun i : ι => F i ω)
    rw [← Measure.map_map hpi measurable_snd, hp.map_eq]
  have hA : ∀ i, AEMeasurable (F i) Q :=
    fun i => (hF i).aemeasurable
  have hB : ∀ i, AEMeasurable (fun p : Ω × Λ => F i p.2)
      (P.prod Q) :=
    fun i => ((hF i).comp measurable_snd).aemeasurable
  apply (iIndepFun_iff_map_fun_eq_pi_map hB).2
  calc
    (P.prod Q).map (fun p : Ω × Λ => fun i : ι => F i p.2)
        = Q.map (fun ω : Λ => fun i : ι => F i ω) := hmapPi
    _ = Measure.pi (fun i => Q.map (F i)) :=
      (iIndepFun_iff_map_fun_eq_pi_map hA).1 hIndep
    _ = Measure.pi (fun i => (P.prod Q).map (fun p : Ω × Λ => F i p.2)) := by
      congr 1
      funext i
      exact (hmap (F i) (hF i)).symm
