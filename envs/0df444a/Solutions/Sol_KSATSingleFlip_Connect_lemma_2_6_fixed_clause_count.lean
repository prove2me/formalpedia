-- Prove2me | solution 1 for KSATSingleFlip.Connect.lemma_2_6_fixed_clause_count
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T09:38:08.002521+00:00
-- url     : https://prove2.me/submissions/4a690ce7-a29f-4020-9ebe-79c0b70841cf

import Theorems.Thm_KSATSingleFlip_Connect_insertion_implies_replacement
import Theorems.Thm_KSATSingleFlip_Connect_lemma_2_6_fixed_count
import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators

theorem solution {A : Type} [MeasurableSpace A] (j : ℕ) (hj : 1 ≤ j)
    (μ : Measure A) [IsProbabilityMeasure μ] (F : List A → ℝ)
    (hF : Measurable (fun x : Fin j → A => F (List.ofFn x)))
    (L u : ℝ) (hL : 1 ≤ L) (hu : 0 < u)
    (hins : ∀ (xs : List A) (i : ℕ) (a : A), |F (xs.insertIdx i a) - F xs| ≤ L) :
    Measure.pi (fun _ : Fin j => μ) {x | F (List.ofFn x) ≤
      (∫ y, F (List.ofFn y) ∂(Measure.pi (fun _ : Fin j => μ))) - u} ≤
      ENNReal.ofReal (Real.exp (-(u^2)/(2*(j:ℝ)*L^2))) := by
  apply KSATSingleFlip.Connect.lemma_2_6_fixed_count j hj μ (fun x => F (List.ofFn x)) hF L u hL hu
  intro i x a
  exact KSATSingleFlip.Connect.insertion_implies_replacement j F L hins x i a
