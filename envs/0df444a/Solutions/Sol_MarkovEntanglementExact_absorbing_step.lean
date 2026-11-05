-- Prove2me | solution 1 for MarkovEntanglementExact.absorbing_step
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-11-04T12:17:17.507794+00:00
-- url     : https://prove2.me/submissions/40cce74d-8154-4a90-919e-0a443c120697

import Definitions.Def_markov_entanglement
import Definitions.Def_MarkovEntanglementExact_IsSeparableWitness

open scoped BigOperators
open MarkovEntanglement MarkovEntanglementExact

theorem solution
    {SA SB : Type*} [Fintype SA] [Fintype SB] [DecidableEq SA] [DecidableEq SB]
    (P : Matrix (SA × SB) (SA × SB) ℝ)
    {K : ℕ} {x : Fin K → ℝ} {PAj : Fin K → Matrix SA SA ℝ} {PBj : Fin K → Matrix SB SB ℝ}
    (hw : IsSeparableWitness P K x PAj PBj) (t : ℕ) :
    (∀ (y : SA → ℝ) (p : SA × SB),
      (P ^ t).mulVec (fun q => y q.1) p = ((∑ k, x k • PAj k) ^ t).mulVec y p.1) ∧
      (∀ (y : SB → ℝ) (p : SA × SB),
        (P ^ t).mulVec (fun q => y q.2) p = ((∑ k, x k • PBj k) ^ t).mulVec y p.2) := by
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
    rw [← Finset.mul_sum, ← Finset.sum_mul, (hA k).2 a, one_mul]
  have stepA : ∀ (y : SA → ℝ), P.mulVec (fun q => y q.1) =
      fun p => (∑ k, x k • PAj k).mulVec y p.1 := by
    intro y
    funext p
    rcases p with ⟨a,b⟩
    simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type]
    simp_rw [← Finset.sum_mul, hmA]
  have stepB : ∀ (y : SB → ℝ), P.mulVec (fun q => y q.2) =
      fun p => (∑ k, x k • PBj k).mulVec y p.2 := by
    intro y
    funext p
    rcases p with ⟨a,b⟩
    simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, hmB]
  induction t with
  | zero => simp
  | succ t ih =>
    constructor
    · intro y p
      rw [pow_succ, ← Matrix.mulVec_mulVec, stepA]
      rw [ih.1]
      rw [pow_succ, ← Matrix.mulVec_mulVec]
    · intro y p
      rw [pow_succ, ← Matrix.mulVec_mulVec, stepB]
      rw [ih.2]
      rw [pow_succ, ← Matrix.mulVec_mulVec]

#print axioms solution
