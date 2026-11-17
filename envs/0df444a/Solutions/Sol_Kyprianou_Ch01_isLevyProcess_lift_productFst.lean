-- Prove2me | solution 1 for Kyprianou.Ch01.isLevyProcess_lift_productFst
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T22:05:55.593216+00:00
-- url     : https://prove2.me/submissions/9682b978-6b0b-4929-a420-72f23d541814

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_Kyprianou_Ch01_iIndepFun_lift_productFst
import Theorems.Thm_Kyprianou_Ch01_identDistrib_lift_productFst
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
    (X : ℝ≥0 → Ω → ℝ)
    (h : IsLevyProcess X P)
    (hXm : ∀ t, Measurable (X t)) :
    IsLevyProcess (fun t (p : Ω × Λ) => X t p.1) (P.prod Q) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · funext p
    exact congrFun h.start_zero p.1
  · intro n t ht
    have hm : ∀ k : Fin n,
        Measurable (increment X (t k.castSucc) (t k.succ)) := by
      intro k
      exact (hXm (t k.succ)).sub (hXm (t k.castSucc))
    have hi := Kyprianou.Ch01.iIndepFun_lift_productFst P Q
      (fun k : Fin n => increment X (t k.castSucc) (t k.succ))
      hm (h.indep_increments n t ht)
    change iIndepFun
      (fun k : Fin n => fun p : Ω × Λ =>
        increment X (t k.castSucc) (t k.succ) p.1) (P.prod Q)
    exact hi
  · intro s u
    have hi := Kyprianou.Ch01.identDistrib_lift_productFst P Q
      (increment X s (s + u))
      (increment X 0 u)
      ((hXm (s + u)).sub (hXm s))
      ((hXm u).sub (hXm 0))
      (h.stationary_increments s u)
    change IdentDistrib
      (fun p : Ω × Λ => increment X s (s + u) p.1)
      (fun p : Ω × Λ => increment X 0 u p.1)
      (P.prod Q) (P.prod Q)
    exact hi
  · have hp : MeasurePreserving Prod.fst (P.prod Q) P :=
      MeasureTheory.measurePreserving_fst
    have hOrig : ∀ᵐ ω ∂((P.prod Q).map Prod.fst),
        IsCadlag (fun t => X t ω) := by
      simpa only [hp.map_eq] using h.cadlag_ae
    exact MeasureTheory.ae_of_ae_map measurable_fst.aemeasurable hOrig
