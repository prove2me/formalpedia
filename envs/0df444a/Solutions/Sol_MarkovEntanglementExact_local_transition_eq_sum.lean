-- Prove2me | solution 1 for MarkovEntanglementExact.local_transition_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-11-04T12:18:46.953612+00:00
-- url     : https://prove2.me/submissions/133aa613-6112-408f-b860-8bc4bca27287

import Definitions.Def_MarkovEntanglementExact_IsOccupancy
import Definitions.Def_MarkovEntanglementExact_IsSeparableWitness

open scoped BigOperators
open MarkovEntanglement MarkovEntanglementExact

theorem solution
    {SA SB : Type*} [Fintype SA] [Fintype SB] [DecidableEq SA] [DecidableEq SB]
    (P : Matrix (SA × SB) (SA × SB) ℝ)
    {K : ℕ} {x : Fin K → ℝ} {PAj : Fin K → Matrix SA SA ℝ} {PBj : Fin K → Matrix SB SB ℝ}
    (hw : IsSeparableWitness P K x PAj PBj)
    (μ : SA × SB → ℝ) (hμ : IsOccupancy μ)
    (PA : Matrix SA SA ℝ) (PB : Matrix SB SB ℝ)
    (hA : IsLocalTransitionA P μ PA) (hB : IsLocalTransitionB P μ PB) :
    PA = ∑ k, x k • PAj k ∧ PB = ∑ k, x k • PBj k := by
  classical
  rcases hw with ⟨hAj, hBj, hx, hexp⟩
  have hmA : ∀ a a' b, ∑ b', P (a, b) (a', b') = (∑ k, x k • PAj k) a a' := by
    intro a a' b
    rw [hexp]
    simp only [Matrix.sum_apply]
    change (∑ b', ∑ k, x k * (PAj k a a' * PBj k b b')) = ∑ k, x k * PAj k a a'
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    simp only [← mul_assoc, ← Finset.mul_sum, (hBj k).2 b, mul_one]
  have hmB : ∀ a b b', ∑ a', P (a, b) (a', b') = (∑ k, x k • PBj k) b b' := by
    intro a b b'
    rw [hexp]
    simp only [Matrix.sum_apply]
    change (∑ a', ∑ k, x k * (PAj k a a' * PBj k b b')) = ∑ k, x k * PBj k b b'
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    rw [← Finset.mul_sum, ← Finset.sum_mul, (hAj k).2 a, one_mul]
  constructor
  · ext a a'
    apply mul_left_cancel₀ (ne_of_gt (hμ.2.2.1 a))
    rw [hA a a']
    simp_rw [hmA]
    rw [← Finset.sum_mul]
    rfl
  · ext b b'
    apply mul_left_cancel₀ (ne_of_gt (hμ.2.2.2 b))
    rw [hB b b']
    simp_rw [hmB]
    rw [← Finset.sum_mul]
    rfl

#print axioms solution
