-- Prove2me | solution 1 for Kyprianou.ProofPreparation.poisson_prm_finset_integral_ae_eq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T12:31:53.185348+00:00
-- url     : https://prove2.me/submissions/d38d8141-a457-494b-8b4b-a47e22340d82

import Mathlib
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Every finite weighted simple Poisson integral equals its finite count sum a.s. -/
theorem solution
    {Ω E ι : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    [DecidableEq ι] [Nonempty E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (m : Measure E) [SigmaFinite m]
    (K : ℕ → Ω → ℕ) (Y : ℕ → ℕ → Ω → E)
    (hd : ProbabilityTheory.IsPoissonPointFamily K Y m P)
    (F : Finset ι) (A : ι → Set E) (a : ι → ℝ)
    (hA : ∀ i ∈ F, MeasurableSet (A i))
    (hfin : ∀ i ∈ F, m (A i) < ⊤) :
    ∀ᵐ ω ∂P,
      (∫ x, (∑ i ∈ F, a i * (A i).indicator (fun _ => (1 : ℝ)) x) ∂
        (ProbabilityTheory.poissonRandomMeasure K Y ω)) =
      ∑ i ∈ F, a i *
        (ProbabilityTheory.poissonRandomMeasure K Y ω (A i)).toReal := by
  have hall : ∀ᵐ ω ∂P, ∀ i ∈ F,
      poissonRandomMeasure K Y ω (A i) < ⊤ := by
    apply (Filter.eventually_all_finset F).2
    intro i hi
    exact ae_poissonRandomMeasure_apply_lt_top hd (hA i hi) (hfin i hi)
  filter_upwards [hall] with ω hω
  let Q : Measure E := poissonRandomMeasure K Y ω
  have hint : ∀ i ∈ F, Integrable
      (fun x => a i * (A i).indicator (fun _ => (1 : ℝ)) x) Q := by
    intro i hi
    exact ((integrableOn_const (μ := Q) (hω i hi).ne).integrable_indicator
      (hA i hi)).const_mul (a i)
  change (∫ x, (∑ i ∈ F, a i *
      (A i).indicator (fun _ => (1 : ℝ)) x) ∂Q) =
    ∑ i ∈ F, a i * (Q (A i)).toReal
  calc
    (∫ x, (∑ i ∈ F, a i *
      (A i).indicator (fun _ => (1 : ℝ)) x) ∂Q) =
        ∑ i ∈ F, (∫ x, a i * (A i).indicator (fun _ => (1 : ℝ)) x ∂Q) :=
      integral_finset_sum F hint
    _ = ∑ i ∈ F, a i * (Q (A i)).toReal := by
      apply Finset.sum_congr rfl
      intro i hi
      calc
        (∫ x, a i * (A i).indicator (fun _ => (1 : ℝ)) x ∂Q) =
            a i * (∫ x, (A i).indicator (fun _ => (1 : ℝ)) x ∂Q) := by
          rw [integral_const_mul]
        _ = a i * (Q (A i)).toReal := by
          have he : (∫ x, (A i).indicator (fun _ => (1 : ℝ)) x ∂Q) =
              (Q (A i)).toReal := integral_indicator_one (hA i hi)
          exact congrArg (fun z : ℝ => a i * z) he
