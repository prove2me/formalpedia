-- Prove2me | solution 1 for HighDimStat.Localization.star_shaped_localization_reduction
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-30T22:22:32.286444+00:00
-- url     : https://prove2.me/submissions/8f4a0007-e5c3-4dc0-a762-388e660c97d7

import Mathlib
import Definitions.Def_HighDimStat_Localization_Core

namespace HighDimStat.Localization

open MeasureTheory

lemma popNormSq_nonneg {X : Type*} [MeasurableSpace X] (μ : Measure X) (f : X → ℝ) :
    0 ≤ popNormSq μ f := by
  unfold popNormSq
  exact integral_nonneg (fun x => sq_nonneg (f x))

lemma popNormSq_smul {X : Type*} [MeasurableSpace X] (μ : Measure X) (α : ℝ) (f : X → ℝ) :
    popNormSq μ (fun z => α * f z) = α ^ 2 * popNormSq μ f := by
  unfold popNormSq
  have h : (fun x => (α * f x) ^ 2) = (fun x => α ^ 2 * (f x) ^ 2) := by
    ext x; ring
  rw [h, integral_const_mul]

lemma popNorm_smul_nonneg {X : Type*} [MeasurableSpace X] (μ : Measure X) {α : ℝ} (hα : 0 ≤ α)
    (f : X → ℝ) :
    popNorm μ (fun z => α * f z) = α * popNorm μ f := by
  unfold popNorm
  rw [popNormSq_smul, Real.sqrt_mul (sq_nonneg α), Real.sqrt_sq hα]

lemma empiricalNormSq_smul {X : Type*} {n : ℕ} (xs : Fin n → X) (α : ℝ) (f : X → ℝ) :
    empiricalNormSq xs (fun z => α * f z) = α ^ 2 * empiricalNormSq xs f := by
  unfold empiricalNormSq
  have h : (∑ i, (α * f (xs i)) ^ 2) = α ^ 2 * ∑ i, (f (xs i)) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    ring
  rw [h, mul_div_assoc]

end HighDimStat.Localization

open HighDimStat.Localization MeasureTheory in
theorem solution {X : Type*} [MeasurableSpace X] {n : ℕ}
    (xs : Fin n → X) (μ : Measure X) (F : Set (X → ℝ))
    (hStar : IsStarShapedAroundOrigin F) (t : ℝ) (ht : 0 < t)
    (h_loc : ∀ g ∈ F, popNorm μ g ≤ t →
      |empiricalNormSq xs g - popNormSq μ g| ≤ t ^ 2 / 2) :
    ∀ f ∈ F, |empiricalNormSq xs f - popNormSq μ f| ≤
      (1 / 2) * popNormSq μ f + t ^ 2 / 2 := by
  intro f hf
  have h_pop_nonneg : 0 ≤ popNormSq μ f := popNormSq_nonneg μ f
  by_cases h_le : popNorm μ f ≤ t
  · have h1 := h_loc f hf h_le
    linarith
  · have h_lt : t < popNorm μ f := lt_of_not_ge h_le
    have h_pos : 0 < popNorm μ f := lt_trans ht h_lt
    set α := t / popNorm μ f
    have hα0 : 0 ≤ α := div_nonneg (le_of_lt ht) (le_of_lt h_pos)
    have hα1 : α ≤ 1 := div_le_one_of_le₀ (le_of_lt h_lt) (le_of_lt h_pos)
    let g : X → ℝ := fun z => α * f z
    have hgF : g ∈ F := hStar f hf α ⟨hα0, hα1⟩
    have hg_norm : popNorm μ g ≤ t := by
      rw [popNorm_smul_nonneg μ hα0 f]
      exact le_of_eq (div_mul_cancel₀ t (ne_of_gt h_pos))
    have h_bound := h_loc g hgF hg_norm
    have h_emp : empiricalNormSq xs g = α ^ 2 * empiricalNormSq xs f :=
      empiricalNormSq_smul xs α f
    have h_pop : popNormSq μ g = α ^ 2 * popNormSq μ f :=
      popNormSq_smul μ α f
    rw [h_emp, h_pop, ← mul_sub, abs_mul, abs_of_nonneg (sq_nonneg α)] at h_bound
    have h_sq : popNorm μ f ^ 2 = popNormSq μ f :=
      Real.sq_sqrt h_pop_nonneg
    have h_pop_pos : 0 < popNormSq μ f := by
      rw [← h_sq]; positivity
    have h_mul : α ^ 2 * popNormSq μ f = t ^ 2 := by
      dsimp [α]
      rw [div_pow, h_sq, div_mul_cancel₀ _ (ne_of_gt h_pop_pos)]
    have hα_pos : 0 < α ^ 2 := by
      dsimp [α]; positivity
    have h_scaled : |empiricalNormSq xs f - popNormSq μ f| ≤ (1 / 2) * popNormSq μ f := by
      have h2 : α ^ 2 * |empiricalNormSq xs f - popNormSq μ f| ≤ α ^ 2 * ((1 / 2) * popNormSq μ f) := by
        calc α ^ 2 * |empiricalNormSq xs f - popNormSq μ f|
            ≤ t ^ 2 / 2 := h_bound
          _ = (α ^ 2 * popNormSq μ f) / 2 := by rw [h_mul]
          _ = α ^ 2 * ((1 / 2) * popNormSq μ f) := by ring
      exact le_of_mul_le_mul_left h2 hα_pos
    have ht2 : 0 ≤ t ^ 2 := sq_nonneg t
    linarith
