-- Prove2me | solution 1 for Kyprianou.ProofPreparation.poisson_prm_two_cell_second_moment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T12:54:56.225375+00:00
-- url     : https://prove2.me/submissions/89df5d76-778f-4d00-b214-9994a775b6fd

import Mathlib
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
import Theorems.Thm_Kyprianou_ProofPreparation_poisson_prm_eval_sq_integrable
import Theorems.Thm_Kyprianou_ProofPreparation_poisson_prm_eval_real_second_moment
import Theorems.Thm_Kyprianou_ProofPreparation_poisson_prm_disjoint_cross_moment
import Theorems.Thm_Kyprianou_ProofPreparation_poisson_prm_eval_real_first_moment
import Theorems.Thm_Kyprianou_ProofPreparation_real_two_var_weighted_square_integral
import Theorems.Thm_ProbabilityTheory_indepFun_poissonRandomMeasure_apply

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Exact weighted two-cell Poisson count second moment via a quadratic integral lemma. -/
theorem solution
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    [Nonempty E] (P : Measure Ω) [IsProbabilityMeasure P]
    (m : Measure E) [SigmaFinite m]
    (K : ℕ → Ω → ℕ) (Y : ℕ → ℕ → Ω → E)
    (hd : ProbabilityTheory.IsPoissonPointFamily K Y m P)
    (A B : Set E) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hfinA : m A < ⊤) (hfinB : m B < ⊤)
    (hAB : Disjoint A B) (a b : ℝ) :
    (∫ ω, (a * (ProbabilityTheory.poissonRandomMeasure K Y ω A).toReal +
      b * (ProbabilityTheory.poissonRandomMeasure K Y ω B).toReal) ^ 2 ∂P) =
      (a * (m A).toReal + b * (m B).toReal) ^ 2 +
        a ^ 2 * (m A).toReal + b ^ 2 * (m B).toReal := by
  let ZA : Ω → ℝ := fun ω => (poissonRandomMeasure K Y ω A).toReal
  let ZB : Ω → ℝ := fun ω => (poissonRandomMeasure K Y ω B).toReal
  have hIA : Integrable ZA P :=
    (Kyprianou.ProofPreparation.poisson_prm_eval_real_first_moment
      P m K Y hd A hA hfinA).1
  have hIB : Integrable ZB P :=
    (Kyprianou.ProofPreparation.poisson_prm_eval_real_first_moment
      P m K Y hd B hB hfinB).1
  have hISqA : Integrable (fun ω => ZA ω ^ 2) P :=
    Kyprianou.ProofPreparation.poisson_prm_eval_sq_integrable P m K Y hd A hA hfinA
  have hISqB : Integrable (fun ω => ZB ω ^ 2) P :=
    Kyprianou.ProofPreparation.poisson_prm_eval_sq_integrable P m K Y hd B hB hfinB
  have hInd : IndepFun ZA ZB P :=
    (indepFun_poissonRandomMeasure_apply hd hA hB hfinA hfinB hAB).comp
      ENNReal.measurable_toReal ENNReal.measurable_toReal
  have hIAB : Integrable (fun ω => ZA ω * ZB ω) P :=
    hInd.integrable_mul hIA hIB
  have hMomA := Kyprianou.ProofPreparation.poisson_prm_eval_real_second_moment
    P m K Y hd A hA hfinA
  have hMomB := Kyprianou.ProofPreparation.poisson_prm_eval_real_second_moment
    P m K Y hd B hB hfinB
  have hCross := Kyprianou.ProofPreparation.poisson_prm_disjoint_cross_moment
    P m K Y hd A B hA hB hfinA hfinB hAB
  change (∫ ω, (a * ZA ω + b * ZB ω) ^ 2 ∂P) =
    (a * (m A).toReal + b * (m B).toReal) ^ 2 +
      a ^ 2 * (m A).toReal + b ^ 2 * (m B).toReal
  calc
    (∫ ω, (a * ZA ω + b * ZB ω) ^ 2 ∂P) =
        a ^ 2 * (∫ ω, ZA ω ^ 2 ∂P) +
        b ^ 2 * (∫ ω, ZB ω ^ 2 ∂P) +
        (2 * a * b) * (∫ ω, ZA ω * ZB ω ∂P) :=
      Kyprianou.ProofPreparation.real_two_var_weighted_square_integral
        P ZA ZB hISqA hISqB hIAB a b
    _ = a ^ 2 * ((m A).toReal ^ 2 + (m A).toReal) +
        b ^ 2 * ((m B).toReal ^ 2 + (m B).toReal) +
        (2 * a * b) * ((m A).toReal * (m B).toReal) := by
      rw [hMomA, hMomB, hCross]
    _ = (a * (m A).toReal + b * (m B).toReal) ^ 2 +
        a ^ 2 * (m A).toReal + b ^ 2 * (m B).toReal := by ring
