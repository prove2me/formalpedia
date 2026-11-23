-- Prove2me | solution 1 for GrothendieckPD.Digits.lemma_2_5_coeff_l1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T03:35:58.188797+00:00
-- url     : https://prove2.me/submissions/6c58bf0c-afa9-4ee0-990f-e858175e7c92
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_GrothendieckPD_Digits_lemma_2_5_parseval

open MeasureTheory Filter
open GrothendieckPD.Digits

theorem solution :
    ∀ (n : ℕ) (f g : (Fin n → ℝ) → ℝ), GrothendieckLB.IsSignFn f → GrothendieckLB.IsSignFn g →
      Summable (fun m => |coeff m f g|) ∧ ∑' m, |coeff m f g| ≤ 1 := by
  have energy_nonneg {n : ℕ} (f : (Fin n → ℝ) → ℝ) (m : ℕ) : 0 ≤ coeff m f f := by
    rw [coeff, GrothendieckLB.pmInner]
    apply Finset.sum_nonneg
    intro α hα
    apply div_nonneg
    · exact mul_self_nonneg _
    · positivity
  have coefficient_cs {n : ℕ} (f g : (Fin n → ℝ) → ℝ) (m : ℕ) :
      |coeff m f g| ≤ Real.sqrt (coeff m f f) * Real.sqrt (coeff m g g) := by
    let s := Finset.Nat.antidiagonalTuple n m
    let F : (Fin n → ℕ) → ℝ := fun α =>
      GrothendieckLB.gaussExp fun x => f x * ∏ i, Polynomial.aeval (x i) (Polynomial.hermite (α i))
    let G : (Fin n → ℕ) → ℝ := fun α =>
      GrothendieckLB.gaussExp fun x => g x * ∏ i, Polynomial.aeval (x i) (Polynomial.hermite (α i))
    let w : (Fin n → ℕ) → ℝ := fun α => ∏ i, ((α i).factorial : ℝ)
    let u : (Fin n → ℕ) → ℝ := fun α => F α / Real.sqrt (w α)
    let v : (Fin n → ℕ) → ℝ := fun α => G α / Real.sqrt (w α)
    have hw (α : Fin n → ℕ) : 0 ≤ w α := by
      dsimp [w]
      positivity
    have huv (α : Fin n → ℕ) : u α * v α = F α * G α / w α := by
      dsimp [u, v]
      calc
        F α / Real.sqrt (w α) * (G α / Real.sqrt (w α)) =
            F α * G α / (Real.sqrt (w α) * Real.sqrt (w α)) := by ring
        _ = F α * G α / w α := by rw [Real.mul_self_sqrt (hw α)]
    have huu (α : Fin n → ℕ) : u α ^ 2 = F α * F α / w α := by
      dsimp [u]
      rw [div_pow, Real.sq_sqrt (hw α)]
      ring
    have hvv (α : Fin n → ℕ) : v α ^ 2 = G α * G α / w α := by
      dsimp [v]
      rw [div_pow, Real.sq_sqrt (hw α)]
      ring
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq s u v
    simp_rw [huv, huu, hvv] at hcs
    have hcs' : (coeff m f g) ^ 2 ≤ coeff m f f * coeff m g g := by
      simpa only [coeff, GrothendieckLB.pmInner, s, F, G, w] using hcs
    apply abs_le_of_sq_le_sq
    · rw [mul_pow, Real.sq_sqrt (energy_nonneg f m), Real.sq_sqrt (energy_nonneg g m)]
      exact hcs'
    · positivity
  intro n f g hf hg
  obtain ⟨hEf, hEf_sum⟩ := GrothendieckPD.Digits.lemma_2_5_parseval n f hf
  obtain ⟨hEg, hEg_sum⟩ := GrothendieckPD.Digits.lemma_2_5_parseval n g hg
  have ham_gm (m : ℕ) :
      Real.sqrt (coeff m f f) * Real.sqrt (coeff m g g) ≤
        (coeff m f f + coeff m g g) / 2 := by
    have h₁ := Real.sq_sqrt (energy_nonneg f m)
    have h₂ := Real.sq_sqrt (energy_nonneg g m)
    have h₃ := sq_nonneg (Real.sqrt (coeff m f f) - Real.sqrt (coeff m g g))
    nlinarith
  have hsqrt : Summable (fun m =>
      Real.sqrt (coeff m f f) * Real.sqrt (coeff m g g)) := by
    apply Summable.of_nonneg_of_le (hf := (hEf.add hEg).div_const 2)
    · intro m
      positivity
    · exact ham_gm
  have habs : Summable (fun m => |coeff m f g|) := by
    apply Summable.of_nonneg_of_le (hf := hsqrt)
    · intro m
      exact abs_nonneg _
    · exact coefficient_cs f g
  refine ⟨habs, ?_⟩
  calc
    ∑' m, |coeff m f g| ≤ ∑' m, Real.sqrt (coeff m f f) * Real.sqrt (coeff m g g) :=
      Summable.tsum_le_tsum (coefficient_cs f g) habs hsqrt
    _ ≤ ∑' m, (coeff m f f + coeff m g g) / 2 :=
      Summable.tsum_le_tsum ham_gm hsqrt ((hEf.add hEg).div_const 2)
    _ = 1 := by
      rw [tsum_div_const, hEf.tsum_add hEg, hEf_sum, hEg_sum]
      norm_num
