-- Prove2me | solution 1 for HunterPDE.Sobolev.HasWeakDeriv.mul_jet_bound
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-11T22:01:25.945504+00:00
-- url     : https://prove2.me/submissions/0e0f8fac-e047-4fff-8711-f6e61191649f

import Theorems.Thm_HunterPDE_Sobolev_HasWeakDeriv_mul_leibniz
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

open MeasureTheory HunterPDE.Sobolev

theorem solution {n k : ℕ}
    (f η : EuclideanSpace ℝ (Fin n) → ℝ)
    (d : (Fin n → ℕ) → EuclideanSpace ℝ (Fin n) → ℝ)
    (hd : ∀ β, ∑ i, β i ≤ k → HasWeakDeriv Set.univ β f (d β))
    (hη : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) η)
    (A : EuclideanSpace ℝ (Fin n) → ℝ) (hA : ∀ x, 0 ≤ A x)
    (hbound : ∀ β, ∑ i, β i ≤ k → ∀ x, ‖iteratedPartial β η x‖ ≤ A x)
    (α : Fin n → ℕ) (hα : ∑ i, α i ≤ k) :
    ∃ g, HasWeakDeriv Set.univ α (fun x => η x * f x) g ∧
      ∀ x, ‖g x‖ ≤ (2 : ℝ) ^ k * A x * ∑ β ∈ multiIndices n k, ‖d β x‖ := by
  classical
  refine ⟨_, HasWeakDeriv.mul_leibniz Set.univ isOpen_univ f η d hd hη α hα, ?_⟩
  intro x
  have hc (β : Fin n → ℕ) :
      (∏ i, (Nat.choose (α i) (β i) : ℝ)) ≤ (2 : ℝ) ^ k := by
    calc
      (∏ i, (Nat.choose (α i) (β i) : ℝ)) ≤ ∏ i, (2 : ℝ) ^ (α i) := by
        apply Finset.prod_le_prod
        · intros; positivity
        · intro i hi
          exact_mod_cast Nat.choose_le_two_pow (α i) (β i)
      _ = (2 : ℝ) ^ (∑ i, α i) := by rw [Finset.prod_pow_eq_pow_sum]
      _ ≤ (2 : ℝ) ^ k := by exact pow_le_pow_right₀ (by norm_num) hα
  have ht (β : Fin n → ℕ) :
      ‖(∏ i, (Nat.choose (α i) (β i) : ℝ)) *
          iteratedPartial (fun i => α i - β i) η x * d β x‖ ≤
        (2 : ℝ) ^ k * A x * ‖d β x‖ := by
    have horder : ∑ i, (α i - β i) ≤ k :=
      (Finset.sum_le_sum (fun i _ => Nat.sub_le (α i) (β i))).trans hα
    have hn : 0 ≤ ∏ i, (Nat.choose (α i) (β i) : ℝ) := by positivity
    rw [norm_mul, norm_mul, Real.norm_of_nonneg hn]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul (hc β) (hbound _ horder x) (norm_nonneg _) (by positivity))
      (norm_nonneg _)
  calc
    _ ≤ ∑ β ∈ multiIndices n k,
        ‖(∏ i, (Nat.choose (α i) (β i) : ℝ)) *
          iteratedPartial (fun i => α i - β i) η x * d β x‖ := norm_sum_le _ _
    _ ≤ ∑ β ∈ multiIndices n k, (2 : ℝ) ^ k * A x * ‖d β x‖ :=
      Finset.sum_le_sum (fun β _ => ht β)
    _ = _ := by rw [Finset.mul_sum]
