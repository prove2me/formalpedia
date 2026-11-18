-- Prove2me | solution 1 for Kyprianou.ProofPreparation.poisson_prm_two_cell_weighted_sq_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T12:15:51.096201+00:00
-- url     : https://prove2.me/submissions/aa615ba0-550b-407d-8344-f1e4867310f4

import Mathlib
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
import Theorems.Thm_Kyprianou_ProofPreparation_poisson_prm_eval_sq_integrable
import Theorems.Thm_Kyprianou_ProofPreparation_poisson_prm_eval_real_first_moment
import Theorems.Thm_ProbabilityTheory_indepFun_poissonRandomMeasure_apply
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The square of a weighted pair of disjoint finite Poisson counts is integrable. -/
theorem solution
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    [Nonempty E] (P : Measure Ω) [IsProbabilityMeasure P]
    (m : Measure E) [SigmaFinite m]
    (K : ℕ → Ω → ℕ) (Y : ℕ → ℕ → Ω → E)
    (hd : ProbabilityTheory.IsPoissonPointFamily K Y m P)
    (A B : Set E) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hfinA : m A < ⊤) (hfinB : m B < ⊤)
    (hAB : Disjoint A B) (a b : ℝ) :
    Integrable (fun ω =>
      (a * (ProbabilityTheory.poissonRandomMeasure K Y ω A).toReal +
       b * (ProbabilityTheory.poissonRandomMeasure K Y ω B).toReal) ^ 2) P := by
  let ZA : Ω → ℝ := fun ω => (poissonRandomMeasure K Y ω A).toReal
  let ZB : Ω → ℝ := fun ω => (poissonRandomMeasure K Y ω B).toReal
  have ha : Integrable ZA P :=
    (Kyprianou.ProofPreparation.poisson_prm_eval_real_first_moment
      P m K Y hd A hA hfinA).1
  have hb : Integrable ZB P :=
    (Kyprianou.ProofPreparation.poisson_prm_eval_real_first_moment
      P m K Y hd B hB hfinB).1
  have hsa : Integrable (fun ω => ZA ω ^ 2) P :=
    Kyprianou.ProofPreparation.poisson_prm_eval_sq_integrable P m K Y hd A hA hfinA
  have hsb : Integrable (fun ω => ZB ω ^ 2) P :=
    Kyprianou.ProofPreparation.poisson_prm_eval_sq_integrable P m K Y hd B hB hfinB
  have hind : IndepFun ZA ZB P :=
    (indepFun_poissonRandomMeasure_apply hd hA hB hfinA hfinB hAB).comp
      ENNReal.measurable_toReal ENNReal.measurable_toReal
  have hp : Integrable (fun ω => ZA ω * ZB ω) P :=
    hind.integrable_mul ha hb
  have hsum : Integrable (fun ω =>
      (a ^ 2 * ZA ω ^ 2 + b ^ 2 * ZB ω ^ 2) +
        (2 * a * b) * (ZA ω * ZB ω)) P :=
    ((hsa.const_mul (a ^ 2)).add (hsb.const_mul (b ^ 2))).add
      (hp.const_mul (2 * a * b))
  convert hsum using 1
  funext ω
  ring
