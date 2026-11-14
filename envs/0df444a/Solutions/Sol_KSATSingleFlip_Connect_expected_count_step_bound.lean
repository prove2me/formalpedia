-- Prove2me | solution 1 for KSATSingleFlip.Connect.expected_count_step_bound
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T09:56:29.350144+00:00
-- url     : https://prove2.me/submissions/7b0ad4b0-0b29-44d3-a02a-6cc65c22f522

import Mathlib
set_option autoImplicit false
open MeasureTheory

theorem solution {Ω A : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → A) (F : List A → ℝ) (L : ℝ)
    (hins : ∀ (xs : List A) (i : ℕ) (a : A), |F (xs.insertIdx i a) - F xs| ≤ L)
    (hint : ∀ j, Integrable (fun ω => F (List.ofFn fun i : Fin j => X i.val ω)) μ)
    (j : ℕ) :
    |(∫ ω, F (List.ofFn fun i : Fin (j+1) => X i.val ω) ∂μ) -
     (∫ ω, F (List.ofFn fun i : Fin j => X i.val ω) ∂μ)| ≤ L := by
  rw [← integral_sub (hint (j+1)) (hint j)]
  have hh : ∀ ω, |F (List.ofFn fun i : Fin (j+1) => X i.val ω) -
      F (List.ofFn fun i : Fin j => X i.val ω)| ≤ L := by
    intro ω
    let xs := List.ofFn (fun i : Fin j => X i.val ω)
    have h := hins xs xs.length (X j ω)
    rw [List.insertIdx_length_self] at h
    have heq : List.ofFn (fun i : Fin (j+1) => X i.val ω) = xs ++ [X j ω] := by
      rw [List.ofFn_succ', List.concat_eq_append]
      rfl
    rw [heq]
    exact h
  have h := norm_integral_le_of_norm_le_const (μ := μ)
    (f := fun ω => F (List.ofFn fun i : Fin (j+1) => X i.val ω) -
      F (List.ofFn fun i : Fin j => X i.val ω)) (Filter.Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs] using hh ω)
  simpa [Real.norm_eq_abs, measureReal_def] using h
