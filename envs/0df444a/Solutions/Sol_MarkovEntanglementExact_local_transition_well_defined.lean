-- Prove2me | solution 1 for MarkovEntanglementExact.local_transition_well_defined
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-11-04T12:23:13.718751+00:00
-- url     : https://prove2.me/submissions/fe1638e7-850b-49a2-a2be-e740c7cfa220

import Definitions.Def_MarkovEntanglementExact_IsOccupancy
import Mathlib.Algebra.BigOperators.Field

open scoped BigOperators
open MarkovEntanglement MarkovEntanglementExact

private theorem conditional_matrix
    {I J : Type*} [Fintype I] [Fintype J]
    (C : I → J → I → J → ℝ)
    (hC : ∀ i j i' j', 0 ≤ C i j i' j')
    (hrow : ∀ i j, ∑ i', ∑ j', C i j i' j' = 1)
    (w : I → J → ℝ) (hw : ∀ i j, 0 ≤ w i j)
    (hpos : ∀ i, 0 < ∑ j, w i j) :
    (∃! M : Matrix I I ℝ, ∀ i i',
      (∑ j, w i j) * M i i' = ∑ j, w i j * ∑ j', C i j i' j') ∧
    (∀ M : Matrix I I ℝ, (∀ i i',
      (∑ j, w i j) * M i i' = ∑ j, w i j * ∑ j', C i j i' j') →
      IsTransitionMatrix M ∧ ∀ i i', M i i' = ∑ j', ∑ j,
        C i j i' j' * (w i j / ∑ k, w i k)) := by
  classical
  let R : Matrix I I ℝ := fun i i' => (∑ j, w i j * ∑ j', C i j i' j') / ∑ j, w i j
  have hR : ∀ i i', (∑ j, w i j) * R i i' = ∑ j, w i j * ∑ j', C i j i' j' := by
    intro i i'
    exact mul_div_cancel₀ _ (ne_of_gt (hpos i))
  have unique : ∀ M : Matrix I I ℝ, (∀ i i',
      (∑ j, w i j) * M i i' = ∑ j, w i j * ∑ j', C i j i' j') → M = R := by
    intro M hM
    ext i i'
    exact mul_left_cancel₀ (ne_of_gt (hpos i)) ((hM i i').trans (hR i i').symm)
  refine ⟨⟨R, hR, unique⟩, ?_⟩
  intro M hM
  rw [unique M hM]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro i i'
    exact div_nonneg (Finset.sum_nonneg fun j _ =>
      mul_nonneg (hw i j) (Finset.sum_nonneg fun j' _ => hC i j i' j')) (hpos i).le
  · intro i
    change (∑ i', (∑ j, w i j * ∑ j', C i j i' j') / ∑ j, w i j) = 1
    rw [← Finset.sum_div, div_eq_one_iff_eq (ne_of_gt (hpos i)), Finset.sum_comm]
    simp_rw [← Finset.mul_sum, hrow, mul_one]
  · intro i i'
    change (∑ j, w i j * ∑ j', C i j i' j') / (∑ j, w i j) = _
    rw [Finset.sum_comm, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.mul_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j' _
    rw [mul_comm (w i j), mul_div_assoc]

theorem solution
    {SA SB : Type*} [Fintype SA] [Fintype SB] [DecidableEq SA] [DecidableEq SB]
    (P : Matrix (SA × SB) (SA × SB) ℝ) (hP : IsTransitionMatrix P)
    (μ : SA × SB → ℝ) (hμ : IsOccupancy μ) :
    (∃! PA : Matrix SA SA ℝ, IsLocalTransitionA P μ PA) ∧
      (∃! PB : Matrix SB SB ℝ, IsLocalTransitionB P μ PB) ∧
      (∀ PA : Matrix SA SA ℝ, IsLocalTransitionA P μ PA →
        IsTransitionMatrix PA ∧
          ∀ a a', PA a a' = ∑ b', ∑ b, P (a, b) (a', b') * (μ (a, b) / marginalA μ a)) ∧
      (∀ PB : Matrix SB SB ℝ, IsLocalTransitionB P μ PB →
        IsTransitionMatrix PB ∧
          ∀ b b', PB b b' = ∑ a', ∑ a, P (a, b) (a', b') * (μ (a, b) / marginalB μ b)) := by
  classical
  have hrowA : ∀ a b, ∑ a', ∑ b', P (a,b) (a',b') = 1 := by
    intro a b
    simpa only [Fintype.sum_prod_type] using hP.2 (a,b)
  have hrowB : ∀ b a, ∑ b', ∑ a', P (a,b) (a',b') = 1 := by
    intro b a
    rw [Finset.sum_comm]
    exact hrowA a b
  have hA := conditional_matrix (fun a b a' b' => P (a,b) (a',b'))
    (fun a b a' b' => hP.1 _ _) hrowA
    (fun a b => μ (a,b)) (fun a b => hμ.1 _) hμ.2.2.1
  have hB := conditional_matrix (fun b a b' a' => P (a,b) (a',b'))
    (fun b a b' a' => hP.1 _ _) hrowB
    (fun b a => μ (a,b)) (fun b a => hμ.1 _) hμ.2.2.2
  exact ⟨hA.1, hB.1, hA.2, hB.2⟩

#print axioms solution
