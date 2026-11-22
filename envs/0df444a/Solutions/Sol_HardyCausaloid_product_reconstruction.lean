-- Prove2me | solution 1 for HardyCausaloid.product_reconstruction
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-22T00:36:11.888193+00:00
-- url     : https://prove2.me/submissions/5168027f-1ca3-4823-a88a-8080a1a07cb6

import Mathlib

namespace HardyCausaloid

private theorem from_grid {I : Type*} [Fintype I] [DecidableEq I] {A : I → Type*}
    (Ω : ∀ i, Finset (A i)) (w : ∀ i, A i → Ω i → ℝ)
    (f g : (∀ i, A i) → ℝ)
    (hf : ∀ α i, f α = ∑ k : Ω i, w i (α i) k * f (Function.update α i k.val))
    (hg : ∀ α i, g α = ∑ k : Ω i, w i (α i) k * g (Function.update α i k.val))
    (grid : ∀ k : ∀ i, Ω i, f (fun i => (k i).val) = g (fun i => (k i).val)) :
    ∀ α, f α = g α := by
  classical
  have extend (U : Finset I) : ∀ α, (∀ i ∉ U, α i ∈ Ω i) → f α = g α := by
    induction U using Finset.induction_on with
    | empty => exact fun α h => grid (fun i => ⟨α i, h i (by simp)⟩)
    | @insert i U hi ih =>
      intro α ha
      rw [hf α i, hg α i]
      refine Finset.sum_congr rfl fun k _ => congrArg (w i (α i) k * ·) (ih _ ?_)
      intro j hj
      by_cases h : j = i
      · subst j; simpa using k.property
      · simpa [Function.update_of_ne h] using ha j (by simp [h, hj])
  exact fun α => extend Finset.univ α (by simp)

end HardyCausaloid

open HardyCausaloid

open Classical in
theorem solution {I : Type*} [Fintype I] [DecidableEq I] {A : I → Type*}
    (Ω : ∀ i, Finset (A i)) (w : ∀ i, A i → Ω i → ℝ) (f : (∀ i, A i) → ℝ)
    (rep : ∀ α i, f α = ∑ k : Ω i, w i (α i) k * f (Function.update α i k.val))
    (unit : ∀ i (k j : Ω i), w i k.val j = if k = j then 1 else 0) :
    ∀ α, f α = ∑ l : ∀ i, Ω i, (∏ i, w i (α i) (l i)) * f (fun i => (l i).val) := by
  classical
  let W (α : ∀ i, A i) (l : ∀ i, Ω i) := ∏ j, w j (α j) (l j)
  let g (α : ∀ i, A i) := ∑ l : ∀ i, Ω i, W α l * f (fun j => (l j).val)
  apply from_grid Ω w f g rep
  · intro α i
    have step (l : ∀ j, Ω j) (k : Ω i) : W (Function.update α i k.val) l =
        (if k = l i then 1 else 0) * ∏ j ∈ Finset.univ.erase i, w j (α j) (l j) := by
      rw [← unit]
      unfold W
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i), Function.update_self]
      congr 1
      apply Finset.prod_congr rfl
      intro j hj
      rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]
    change g α = ∑ k : Ω i, w i (α i) k * g (Function.update α i k.val)
    simp only [g, Finset.mul_sum, step]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro l _
    rw [Finset.sum_eq_single (l i)]
    · simp only [W, if_true, one_mul, mul_one, ← mul_assoc]
      rw [Finset.mul_prod_erase Finset.univ (fun j => w j (α j) (l j)) (Finset.mem_univ i)]
    · intro k _ hk; simp [hk]
    · simp
  · intro k
    change f _ = ∑ l : ∀ i, Ω i, W (fun i => (k i).val) l * f _
    rw [Finset.sum_eq_single k]
    · simp [W, unit]
    · intro l _ hne
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
      have hz : W (fun i => (k i).val) l = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ i) (by simp [unit, Ne.symm hi])
      simp [hz]
    · simp

