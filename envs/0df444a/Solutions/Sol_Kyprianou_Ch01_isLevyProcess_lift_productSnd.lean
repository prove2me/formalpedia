-- Prove2me | solution 1 for Kyprianou.Ch01.isLevyProcess_lift_productSnd
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T22:05:40.965022+00:00
-- url     : https://prove2.me/submissions/01c6b06e-9425-4982-9d98-c010c14c812a

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_Kyprianou_Ch01_iIndepFun_lift_productSnd
import Theorems.Thm_Kyprianou_Ch01_identDistrib_lift_productSnd
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped NNReal
set_option autoImplicit false

theorem solution
    {Ω Λ : Type} [MeasurableSpace Ω] [MeasurableSpace Λ]
    (P : Measure Ω) (Q : Measure Λ)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (Y : ℝ≥0 → Λ → ℝ)
    (h : IsLevyProcess Y Q)
    (hYm : ∀ t, Measurable (Y t)) :
    IsLevyProcess (fun t (p : Ω × Λ) => Y t p.2) (P.prod Q) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · funext p
    exact congrFun h.start_zero p.2
  · intro n t ht
    have hm : ∀ k : Fin n,
        Measurable (increment Y (t k.castSucc) (t k.succ)) := by
      intro k
      exact (hYm (t k.succ)).sub (hYm (t k.castSucc))
    have hi := Kyprianou.Ch01.iIndepFun_lift_productSnd P Q
      (fun k : Fin n => increment Y (t k.castSucc) (t k.succ))
      hm (h.indep_increments n t ht)
    change iIndepFun
      (fun k : Fin n => fun p : Ω × Λ =>
        increment Y (t k.castSucc) (t k.succ) p.2) (P.prod Q)
    exact hi
  · intro s u
    have hi := Kyprianou.Ch01.identDistrib_lift_productSnd P Q
      (increment Y s (s + u))
      (increment Y 0 u)
      ((hYm (s + u)).sub (hYm s))
      ((hYm u).sub (hYm 0))
      (h.stationary_increments s u)
    change IdentDistrib
      (fun p : Ω × Λ => increment Y s (s + u) p.2)
      (fun p : Ω × Λ => increment Y 0 u p.2)
      (P.prod Q) (P.prod Q)
    exact hi
  · have hp : MeasurePreserving Prod.snd (P.prod Q) Q :=
      MeasureTheory.measurePreserving_snd
    have hOrig : ∀ᵐ ω ∂((P.prod Q).map Prod.snd),
        IsCadlag (fun t => Y t ω) := by
      simpa only [hp.map_eq] using h.cadlag_ae
    exact MeasureTheory.ae_of_ae_map measurable_snd.aemeasurable hOrig
