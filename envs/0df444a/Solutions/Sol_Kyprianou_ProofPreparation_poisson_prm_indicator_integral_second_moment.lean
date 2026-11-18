-- Prove2me | solution 1 for Kyprianou.ProofPreparation.poisson_prm_indicator_integral_second_moment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T11:07:44.427122+00:00
-- url     : https://prove2.me/submissions/42100808-de91-47bc-adb9-7fd57f16ba19

import Mathlib
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
import Theorems.Thm_Kyprianou_ProofPreparation_poisson_prm_eval_lintegral_sq

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Exact indicator integral second moment from the finite count law. -/
theorem solution
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    [Nonempty E] (P : Measure Ω) [IsProbabilityMeasure P]
    (m : Measure E) [SigmaFinite m]
    (K : ℕ → Ω → ℕ) (Y : ℕ → ℕ → Ω → E)
    (hd : ProbabilityTheory.IsPoissonPointFamily K Y m P)
    (A : Set E) (hA : MeasurableSet A) (hfin : m A < ⊤) :
    (∫ ω, (∫ x, A.indicator (fun _ => (1 : ℝ)) x ∂
      (ProbabilityTheory.poissonRandomMeasure K Y ω)) ^ 2 ∂P) =
      (m A).toReal ^ 2 + (m A).toReal := by
  let Z : Ω → ℝ≥0∞ := fun ω => poissonRandomMeasure K Y ω A
  have hZ : Measurable Z :=
    measurable_poissonRandomMeasure_apply hd.measurable_count hd.measurable_point hA
  have hSquare : AEStronglyMeasurable (fun ω => (Z ω).toReal ^ 2) P :=
    ((ENNReal.measurable_toReal.comp hZ).pow_const 2).aestronglyMeasurable
  have heq : ∀ ω, (∫ x, A.indicator (fun _ => (1 : ℝ)) x ∂
      (poissonRandomMeasure K Y ω)) = (Z ω).toReal :=
    fun ω => integral_indicator_one hA
  simp_rw [heq]
  calc
    (∫ ω, (Z ω).toReal ^ 2 ∂P) =
        (∫⁻ ω, ENNReal.ofReal ((Z ω).toReal ^ 2) ∂P).toReal :=
      integral_eq_lintegral_of_nonneg_ae
        (Filter.Eventually.of_forall fun ω => sq_nonneg _) hSquare
    _ = (ENNReal.ofReal ((m A).toReal ^ 2 + (m A).toReal)).toReal := by
      rw [Kyprianou.ProofPreparation.poisson_prm_eval_lintegral_sq
        P m K Y hd A hA hfin]
    _ = (m A).toReal ^ 2 + (m A).toReal :=
      ENNReal.toReal_ofReal (add_nonneg (sq_nonneg _) ENNReal.toReal_nonneg)
