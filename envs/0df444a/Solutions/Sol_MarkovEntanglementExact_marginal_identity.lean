-- Prove2me | solution 1 for MarkovEntanglementExact.marginal_identity
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-11-03T12:35:32.094329+00:00
-- url     : https://prove2.me/submissions/b7d75d8e-5da7-41f7-a61f-c5578ca691cb

import Definitions.Def_markov_entanglement
import Definitions.Def_MarkovEntanglementExact_IsSeparableWitness

open scoped BigOperators
open MarkovEntanglement MarkovEntanglementExact

theorem solution
    {SA SB : Type*} [Fintype SA] [Fintype SB] [DecidableEq SA] [DecidableEq SB]
    [Nonempty SA] [Nonempty SB]
    (P : Matrix (SA × SB) (SA × SB) ℝ) (hP : IsTransitionMatrix P)
    {K : ℕ} {x : Fin K → ℝ} {PAj : Fin K → Matrix SA SA ℝ} {PBj : Fin K → Matrix SB SB ℝ}
    (hw : IsSeparableWitness P K x PAj PBj) :
    (∀ a a' b, ∑ b', P (a, b) (a', b') = (∑ k, x k • PAj k) a a') ∧
      (∀ a b b', ∑ a', P (a, b) (a', b') = (∑ k, x k • PBj k) b b') ∧
      IsTransitionMatrix (∑ k, x k • PAj k) ∧
      IsTransitionMatrix (∑ k, x k • PBj k) := by
  classical
  rcases hw with ⟨hA, hB, hx, hexp⟩
  have hmA : ∀ a a' b, ∑ b', P (a, b) (a', b') = (∑ k, x k • PAj k) a a' := by
    intro a a' b
    rw [hexp]
    simp only [Matrix.sum_apply]
    change (∑ b', ∑ k, x k * (PAj k a a' * PBj k b b')) = ∑ k, x k * PAj k a a'
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    simp only [← mul_assoc, ← Finset.mul_sum, (hB k).2 b, mul_one]
  have hmB : ∀ a b b', ∑ a', P (a, b) (a', b') = (∑ k, x k • PBj k) b b' := by
    intro a b b'
    rw [hexp]
    simp only [Matrix.sum_apply]
    change (∑ a', ∑ k, x k * (PAj k a a' * PBj k b b')) = ∑ k, x k * PBj k b b'
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    rw [← Finset.mul_sum]
    rw [← Finset.sum_mul, (hA k).2 a, one_mul]
  refine ⟨hmA, hmB, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro a a'
    rw [← hmA a a' (Classical.choice inferInstance)]
    exact Finset.sum_nonneg (fun b' _ => hP.1 _ _)
  · intro a
    simp only [Matrix.sum_apply]
    change (∑ a', ∑ k, x k * PAj k a a') = 1
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, fun k => (hA k).2 a, mul_one]
    exact hx
  · intro b b'
    rw [← hmB (Classical.choice inferInstance) b b']
    exact Finset.sum_nonneg (fun a' _ => hP.1 _ _)
  · intro b
    simp only [Matrix.sum_apply]
    change (∑ b', ∑ k, x k * PBj k b b') = 1
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, fun k => (hB k).2 b, mul_one]
    exact hx

#print axioms solution
