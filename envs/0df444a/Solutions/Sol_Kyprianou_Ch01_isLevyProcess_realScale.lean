-- Prove2me | solution 1 for Kyprianou.Ch01.isLevyProcess_realScale
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:49:25.235469+00:00
-- url     : https://prove2.me/submissions/2e282482-dc03-4c18-b5f5-4683ee23595f

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_Kyprianou_Ch01_isCadlag_realScalarMultiple
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped NNReal
set_option autoImplicit false

theorem solution
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (c : ℝ)
    (h : IsLevyProcess X P) :
    IsLevyProcess (fun t ω => c * X t ω) P := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · funext omega
    have hz := congrFun h.start_zero omega
    simp [hz]
  · intro n t ht
    have hi := h.indep_increments n t ht
    have hi' := hi.comp (fun _ (x : ℝ) => c * x)
      (fun _ => measurable_const.mul measurable_id)
    have hfun :
        (fun k : Fin n => (fun x : ℝ => c * x) ∘
          increment X (t k.castSucc) (t k.succ)) =
        (fun k : Fin n => increment
          (fun t ω => c * X t ω) (t k.castSucc) (t k.succ)) := by
      funext k omega
      dsimp [Function.comp_def, increment]
      ring
    exact (congrArg (fun F => iIndepFun F P) hfun).mp hi'
  · intro s u
    have hi := (h.stationary_increments s u).comp
      (measurable_const.mul measurable_id : Measurable (fun x : ℝ => c * x))
    have ha :
        (fun x : ℝ => c * x) ∘ increment X s (s + u) =
        increment (fun t ω => c * X t ω) s (s + u) := by
      funext omega
      dsimp [Function.comp_def, increment]
      ring
    have hb :
        (fun x : ℝ => c * x) ∘ increment X 0 u =
        increment (fun t ω => c * X t ω) 0 u := by
      funext omega
      dsimp [Function.comp_def, increment]
      ring
    change IdentDistrib
      ((fun x : ℝ => c * x) ∘ increment X s (s + u))
      ((fun x : ℝ => c * x) ∘ increment X 0 u) P P at hi
    rw [ha, hb] at hi
    exact hi
  · filter_upwards [h.cadlag_ae] with omega hc
    exact Kyprianou.Ch01.isCadlag_realScalarMultiple
      c (fun t => X t omega) hc
