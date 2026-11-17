-- Prove2me | solution 1 for Kyprianou.Ch01.independentLevyProductSum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T22:11:24.855447+00:00
-- url     : https://prove2.me/submissions/7ee1aa0a-f99d-4b84-abb7-c22ec95c589b

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_Kyprianou_Ch01_isLevyProcess_lift_productFst
import Theorems.Thm_Kyprianou_Ch01_isLevyProcess_lift_productSnd
import Theorems.Thm_Kyprianou_Ch01_independentLevySum
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
    (X : ℝ≥0 → Ω → ℝ) (Y : ℝ≥0 → Λ → ℝ)
    (hX : IsLevyProcess X P) (hY : IsLevyProcess Y Q)
    (hXm : ∀ t, Measurable (X t))
    (hYm : ∀ t, Measurable (Y t)) :
    IsLevyProcess
      (fun t (p : Ω × Λ) => X t p.1 + Y t p.2) (P.prod Q) := by
  have hl : IsLevyProcess
      (fun t (p : Ω × Λ) => X t p.1) (P.prod Q) :=
    Kyprianou.Ch01.isLevyProcess_lift_productFst P Q X hX hXm
  have hr : IsLevyProcess
      (fun t (p : Ω × Λ) => Y t p.2) (P.prod Q) :=
    Kyprianou.Ch01.isLevyProcess_lift_productSnd P Q Y hY hYm
  have hpathX : Measurable (fun ω : Ω => fun t : ℝ≥0 => X t ω) :=
    measurable_pi_lambda _ hXm
  have hpathY : Measurable (fun ω : Λ => fun t : ℝ≥0 => Y t ω) :=
    measurable_pi_lambda _ hYm
  have hindep : IndepFun
      (fun p : Ω × Λ => fun t : ℝ≥0 => X t p.1)
      (fun p : Ω × Λ => fun t : ℝ≥0 => Y t p.2)
      (P.prod Q) :=
    ProbabilityTheory.indepFun_prod hpathX hpathY
  exact Kyprianou.Ch01.independentLevySum
    (P.prod Q) (fun t (p : Ω × Λ) => X t p.1)
    (fun t (p : Ω × Λ) => Y t p.2)
    hl hr hindep
