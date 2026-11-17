-- Prove2me | solution 1 for Kyprianou.Ch01.iIndepFun_lift_productFst
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:55:57.238561+00:00
-- url     : https://prove2.me/submissions/95b8c978-06a3-4834-b3ff-4b4421320ee2

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
    (F : ι → Ω → ℝ)
    (hF : ∀ i, Measurable (F i))
    (hIndep : iIndepFun F P) :
    iIndepFun (fun i (p : Ω × Λ) => F i p.1) (P.prod Q) := by
  classical
  have hp : MeasurePreserving Prod.fst (P.prod Q) P :=
    MeasureTheory.measurePreserving_fst
  have hmap (f : Ω → ℝ) (hf : Measurable f) :
      (P.prod Q).map (fun p : Ω × Λ => f p.1) = P.map f := by
    change (P.prod Q).map (f ∘ Prod.fst) = P.map f
    rw [← Measure.map_map hf measurable_fst, hp.map_eq]
  have hpi : Measurable (fun ω : Ω => fun i : ι => F i ω) :=
    measurable_pi_lambda _ hF
  have hmapPi :
      (P.prod Q).map (fun p : Ω × Λ => fun i : ι => F i p.1) =
      P.map (fun ω : Ω => fun i : ι => F i ω) := by
    change (P.prod Q).map
      ((fun ω : Ω => fun i : ι => F i ω) ∘ Prod.fst) =
      P.map (fun ω : Ω => fun i : ι => F i ω)
    rw [← Measure.map_map hpi measurable_fst, hp.map_eq]
  have hA : ∀ i, AEMeasurable (F i) P :=
    fun i => (hF i).aemeasurable
  have hB : ∀ i, AEMeasurable (fun p : Ω × Λ => F i p.1)
      (P.prod Q) :=
    fun i => ((hF i).comp measurable_fst).aemeasurable
  apply (iIndepFun_iff_map_fun_eq_pi_map hB).2
  calc
    (P.prod Q).map (fun p : Ω × Λ => fun i : ι => F i p.1)
        = P.map (fun ω : Ω => fun i : ι => F i ω) := hmapPi
    _ = Measure.pi (fun i => P.map (F i)) :=
      (iIndepFun_iff_map_fun_eq_pi_map hA).1 hIndep
    _ = Measure.pi (fun i => (P.prod Q).map (fun p : Ω × Λ => F i p.1)) := by
      congr 1
      funext i
      exact (hmap (F i) (hF i)).symm
