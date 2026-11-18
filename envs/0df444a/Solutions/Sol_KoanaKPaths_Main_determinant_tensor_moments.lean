-- Prove2me | solution 1 for KoanaKPaths.Main.determinant_tensor_moments
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T00:09:36.630762+00:00
-- url     : https://prove2.me/submissions/25b09075-2e76-4833-a4aa-afaafc62452f

import Theorems.Thm_KoanaKPaths_Main_sign_determinant_second_moment
import Theorems.Thm_KoanaKPaths_Main_sign_determinant_fourth_moment

open scoped BigOperators
namespace KoanaKPaths.Main.TensorMoments

lemma mean_mono {Ω : Type} [Fintype Ω] {f g : Ω → ℝ} (h : ∀ w, f w ≤ g w) :
    uniformMean f ≤ uniformMean g := by
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun w _ => h w) (by positivity)

lemma mean_mul {Ω : Type} [Fintype Ω] (a : ℝ) (f : Ω → ℝ) :
    uniformMean (fun w => a * f w) = a * uniformMean f := by
  simp [uniformMean, ← Finset.mul_sum, mul_div_assoc]

lemma mean_sum {Ω I : Type} [Fintype Ω] (s : Finset I) (f : I → Ω → ℝ) :
    uniformMean (fun w => ∑ i ∈ s, f i w) = ∑ i ∈ s, uniformMean (f i) := by
  simp only [uniformMean, ← Finset.sum_div]
  congr 1
  exact Finset.sum_comm

lemma det_zero {n k : ℕ} (τ : Fin k → Fin n)
    (hτ : ¬ Function.Injective τ) (σ : Labels n k) : detD σ τ = 0 := by
  classical
  by_contra hdet
  apply hτ
  intro a b he
  by_contra hne
  apply hdet
  apply Matrix.det_zero_of_column_eq hne
  intro r
  simp [Matrix.of_apply, he]

end KoanaKPaths.Main.TensorMoments

open KoanaKPaths.Main
open KoanaKPaths.Main.TensorMoments

theorem solution (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k)
    (c : (Fin k → Fin n) → ℤ) (hc : IsZeroOneTensor c) :
    uniformMean (fun σ : Labels n k => (psiFrobSq c σ : ℝ)) =
        (Nat.factorial k : ℝ) * (tensorN c : ℝ) ∧
      uniformMean (fun σ : Labels n k => ((psiFrobSq c σ : ℝ)) ^ 2) ≤
        (Nat.factorial k : ℝ) ^ 2 * (k : ℝ) ^ 3 * (tensorN c : ℝ) ^ 2 := by
  classical
  let M := Finset.univ.filter (fun τ : Fin k → Fin n => c τ = 1 ∧ Function.Injective τ)
  have hN : (tensorN c : ℝ) = (M.card : ℝ) := by
    have hcard : (M.card : ℝ) = ∑ τ ∈ M, (1 : ℝ) := by simp
    rw [hcard]
    simp only [M, tensorN, Int.cast_sum, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro τ _
    rcases hc τ with h | h <;> simp [h]
  have hF (σ : Labels n k) :
      (psiFrobSq c σ : ℝ) = ∑ τ ∈ M, (detD σ τ : ℝ)^2 := by
    simp only [psiFrobSq, Int.cast_sum, M, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro τ _
    rcases hc τ with h | h
    · simp [Psi, h]
    · by_cases hτ : Function.Injective τ
      · simp [Psi, h, hτ]
      · simp [Psi, h, hτ, det_zero τ hτ σ]
  constructor
  · simp_rw [hF]
    rw [mean_sum]
    have heq : (∑ τ ∈ M, uniformMean (fun σ : Labels n k => (detD σ τ : ℝ)^2)) =
        (M.card : ℝ) * (Nat.factorial k : ℝ) := by
      calc
        _ = ∑ τ ∈ M, (Nat.factorial k : ℝ) := by
          apply Finset.sum_congr rfl
          intro τ hτ
          exact sign_determinant_second_moment n k τ (Finset.mem_filter.mp hτ).2.2
        _ = _ := by simp
    rw [heq, hN]
    ring
  · simp_rw [hF]
    calc
      _ ≤ uniformMean (fun σ : Labels n k => (M.card : ℝ) *
          ∑ τ ∈ M, (detD σ τ : ℝ)^4) := by
        apply mean_mono
        intro σ
        have h := Finset.sum_mul_sq_le_sq_mul_sq M (fun _ => (1 : ℝ))
          (fun τ => (detD σ τ : ℝ)^2)
        simpa only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one, ← pow_mul] using h
      _ = (M.card : ℝ) * ∑ τ ∈ M, uniformMean (fun σ : Labels n k => (detD σ τ : ℝ)^4) := by
        rw [mean_mul, mean_sum]
      _ ≤ (M.card : ℝ) * ((M.card : ℝ) * ((Nat.factorial k : ℝ)^2*(k : ℝ)^3)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        calc
          _ ≤ ∑ τ ∈ M, (Nat.factorial k : ℝ)^2*(k : ℝ)^3 := by
            apply Finset.sum_le_sum
            intro τ hτ
            exact sign_determinant_fourth_moment n k hk τ (Finset.mem_filter.mp hτ).2.2
          _ = _ := by simp
      _ = _ := by rw [hN]; ring
