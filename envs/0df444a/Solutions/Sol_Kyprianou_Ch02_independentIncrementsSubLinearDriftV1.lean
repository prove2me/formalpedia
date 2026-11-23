-- Prove2me | solution 1 for Kyprianou.Ch02.independentIncrementsSubLinearDriftV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T20:56:51.262712+00:00
-- url     : https://prove2.me/submissions/5fab5115-973b-4c46-979c-5ab342db1542

import Mathlib
import Definitions.Def_LeanLevy_Processes_StochasticProcess
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℝ≥0 → Ω → ℝ) (c : ℝ)
    (hindep : ProbabilityTheory.HasIndependentIncrements X P) :
    ProbabilityTheory.HasIndependentIncrements
      (fun (t : ℝ≥0) ω => X t ω - (t : ℝ) * c) P := by
  intro n t ht
  let g : Fin n → ℝ → ℝ :=
    fun k x => x - ((t k.succ : ℝ) - (t k.castSucc : ℝ)) * c
  have hraw : ProbabilityTheory.iIndepFun
      (fun k : Fin n => ProbabilityTheory.increment X (t k.castSucc) (t k.succ)) P :=
    hindep n t ht
  have htranslated := hraw.comp g (fun k => measurable_id.sub_const _)
  have heq :
      (fun k : Fin n => fun ω : Ω =>
        ProbabilityTheory.increment
          (fun (u : ℝ≥0) ω => X u ω - (u : ℝ) * c)
          (t k.castSucc) (t k.succ) ω) =
      (fun k : Fin n => g k ∘
        ProbabilityTheory.increment X (t k.castSucc) (t k.succ)) := by
    funext k ω
    simp only [g, Function.comp_apply, ProbabilityTheory.increment]
    push_cast
    ring
  change ProbabilityTheory.iIndepFun
    (fun k : Fin n => fun ω : Ω =>
      ProbabilityTheory.increment
        (fun (u : ℝ≥0) ω => X u ω - (u : ℝ) * c)
        (t k.castSucc) (t k.succ) ω) P
  rw [heq]
  exact htranslated
