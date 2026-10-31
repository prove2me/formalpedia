-- Prove2me | solution 1 for MinBuying.lemmaEC1_rejection_bound
-- status  : ACCEPTED   (prove)
-- author  : @mikeh
-- created : 2026-10-30T17:05:06.888518+00:00
-- url     : https://prove2.me/submissions/f6c6176f-8b57-407b-a560-54356d618d12

import Definitions.Def_MinBuying_Triangular
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open MinBuying
open scoped BigOperators

private lemma continuation_nonneg (a v C : ℝ) (ha : 0 ≤ a) (hv : 0 < v)
    (hC : 0 ≤ C) : 0 ≤ continuationStep a v C := by
  unfold continuationStep
  positivity

private lemma continuation_le_sum (a v C : ℝ) (ha : 0 ≤ a) (hv : 0 < v)
    (hC : 0 ≤ C) : continuationStep a v C ≤ a + C := by
  unfold continuationStep
  apply div_le_self (add_nonneg ha hC)
  have : 0 ≤ a / v := div_nonneg ha hv.le
  linarith

private lemma rejection_step (a v C t : ℝ) (ha : 0 ≤ a) (hv : 0 < v)
    (hC : 0 ≤ C) (ht : 0 < t) :
    t / (t + C) * (t / (t + a)) ≤ t / (t + continuationStep a v C) := by
  have hS := continuation_nonneg a v C ha hv hC
  have hbound := continuation_le_sum a v C ha hv hC
  have hTC : 0 < t + C := by positivity
  have hTA : 0 < t + a := by positivity
  have hTS : 0 < t + continuationStep a v C := by positivity
  have hcore : t * (t + continuationStep a v C) ≤ (t + C) * (t + a) := by
    nlinarith [mul_nonneg ha hC, mul_le_mul_of_nonneg_left hbound ht.le]
  rw [div_mul_div_comm]
  apply (div_le_div_iff₀ (mul_pos hTC hTA) hTS).2
  nlinarith [mul_le_mul_of_nonneg_left hcore ht.le]

private lemma rejection_fold_bound {α : Type} (a v : α → ℝ) (t : ℝ) (ht : 0 < t)
    (l : List α) (ha : ∀ i ∈ l, 0 ≤ a i) (hv : ∀ i ∈ l, 0 < v i)
    (C : ℝ) (hC : 0 ≤ C) :
    t / (t + C) * (l.map (fun i => t / (t + a i))).prod ≤
      t / (t + l.foldl (fun S i => continuationStep (a i) (v i) S) C) := by
  induction l generalizing C with
  | nil => simp
  | cons i l ih =>
    have hai : 0 ≤ a i := ha i (by simp)
    have hvi : 0 < v i := hv i (by simp)
    have hal : ∀ j ∈ l, 0 ≤ a j := fun j hj => ha j (by simp [hj])
    have hvl : ∀ j ∈ l, 0 < v j := fun j hj => hv j (by simp [hj])
    have hprod : 0 ≤ (l.map (fun j => t / (t + a j))).prod := by
      apply List.prod_nonneg
      intro x hx
      rcases List.mem_map.mp hx with ⟨j, hj, rfl⟩
      have haj := hal j hj
      positivity
    simp only [List.map_cons, List.prod_cons, List.foldl_cons]
    calc
      t / (t + C) * (t / (t + a i) * (l.map (fun j => t / (t + a j))).prod)
          = (t / (t + C) * (t / (t + a i))) *
              (l.map (fun j => t / (t + a j))).prod := by ring
      _ ≤ (t / (t + continuationStep (a i) (v i) C)) *
            (l.map (fun j => t / (t + a j))).prod :=
          mul_le_mul_of_nonneg_right (rejection_step (a i) (v i) C t hai hvi hC ht) hprod
      _ ≤ t / (t + l.foldl (fun S j => continuationStep (a j) (v j) S)
            (continuationStep (a i) (v i) C)) :=
          ih hal hvl _ (continuation_nonneg (a i) (v i) C hai hvi hC)

theorem solution (n : ℕ) (I : TriangularInstance n)
    (hOrder : Antitone I.cap) (t : ℝ) (ht : 0 < t)
    (hCaps : ∀ i, t ≤ I.cap i) :
    triangularRejectionProduct I t ≤ t / (t + triangularContinuation I n) := by
  have h := rejection_fold_bound I.a I.cap t ht (List.finRange n)
    (fun i _ => (I.a_pos i).le) (fun i _ => I.cap_pos i) 0 (by rfl)
  simpa [triangularRejectionProduct, triangularContinuation, ← Fin.prod_univ_def,
    List.take_of_length_le, ht.ne'] using h
