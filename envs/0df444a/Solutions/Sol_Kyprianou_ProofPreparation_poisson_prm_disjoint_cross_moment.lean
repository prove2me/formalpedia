-- Prove2me | solution 1 for Kyprianou.ProofPreparation.poisson_prm_disjoint_cross_moment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T11:31:06.386023+00:00
-- url     : https://prove2.me/submissions/f0fe281f-3fad-44f7-9b96-9df17f22ed77

import Mathlib
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
import Theorems.Thm_ProbabilityTheory_indepFun_poissonRandomMeasure_apply
import Theorems.Thm_Kyprianou_ProofPreparation_poisson_prm_eval_real_first_moment

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Independent Poisson counts have the product of their two real means. -/
theorem solution
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    [Nonempty E] (P : Measure Ω) [IsProbabilityMeasure P]
    (m : Measure E) [SigmaFinite m]
    (K : ℕ → Ω → ℕ) (Y : ℕ → ℕ → Ω → E)
    (hd : ProbabilityTheory.IsPoissonPointFamily K Y m P)
    (A B : Set E) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hfinA : m A < ⊤) (hfinB : m B < ⊤)
    (hAB : Disjoint A B) :
    (∫ ω, (ProbabilityTheory.poissonRandomMeasure K Y ω A).toReal *
      (ProbabilityTheory.poissonRandomMeasure K Y ω B).toReal ∂P) =
      (m A).toReal * (m B).toReal := by
  let ZA : Ω → ℝ≥0∞ := fun ω => poissonRandomMeasure K Y ω A
  let ZB : Ω → ℝ≥0∞ := fun ω => poissonRandomMeasure K Y ω B
  have hZA : Measurable ZA :=
    measurable_poissonRandomMeasure_apply hd.measurable_count hd.measurable_point hA
  have hZB : Measurable ZB :=
    measurable_poissonRandomMeasure_apply hd.measurable_count hd.measurable_point hB
  have hi : IndepFun (fun ω => (ZA ω).toReal) (fun ω => (ZB ω).toReal) P :=
    (indepFun_poissonRandomMeasure_apply hd hA hB hfinA hfinB hAB).comp
      ENNReal.measurable_toReal ENNReal.measurable_toReal
  have ha : AEStronglyMeasurable (fun ω => (ZA ω).toReal) P :=
    (ENNReal.measurable_toReal.comp hZA).aestronglyMeasurable
  have hb : AEStronglyMeasurable (fun ω => (ZB ω).toReal) P :=
    (ENNReal.measurable_toReal.comp hZB).aestronglyMeasurable
  have hma := (Kyprianou.ProofPreparation.poisson_prm_eval_real_first_moment
    P m K Y hd A hA hfinA).2
  have hmb := (Kyprianou.ProofPreparation.poisson_prm_eval_real_first_moment
    P m K Y hd B hB hfinB).2
  change (∫ ω, (ZA ω).toReal * (ZB ω).toReal ∂P) =
    (m A).toReal * (m B).toReal
  calc
    (∫ ω, (ZA ω).toReal * (ZB ω).toReal ∂P) =
        (∫ ω, (ZA ω).toReal ∂P) *
        (∫ ω, (ZB ω).toReal ∂P) :=
      hi.integral_mul_eq_mul_integral ha hb
    _ = (m A).toReal * (m B).toReal := by
      rw [hma, hmb]
