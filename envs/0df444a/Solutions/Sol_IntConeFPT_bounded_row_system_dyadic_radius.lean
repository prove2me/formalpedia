-- Prove2me | solution 1 for IntConeFPT.bounded_row_system_dyadic_radius
-- status  : ACCEPTED   (prove)
-- author  : @ohnesorgefelix
-- created : 2026-11-25T09:25:09.751799+00:00
-- url     : https://prove2.me/submissions/50022a5b-b5b8-4ae0-8228-037818956a1f

import Theorems.Thm_IntConeFPT_polytope_height_product

open OnlineCRS.Combine IntConeFPT RobustToDynamics

private lemma bitCap (n : ℕ) : n < 2 ^ (encNat n).length := by
  have hp (p : PosNum) : (p : ℕ) < 2 ^ (Computability.encodePosNum p).length := by
    induction p with
    | one => decide
    | bit0 p ih => simp [Computability.encodePosNum, PosNum.cast_bit0, pow_succ]; omega
    | bit1 p ih => simp [Computability.encodePosNum, PosNum.cast_bit1, pow_succ]; omega
  simp only [encNat, List.length_map, Computability.encodeNat]
  conv_lhs => rw [← Num.to_of_nat n]
  cases (n : Num) with
  | zero => decide
  | pos p => exact hp p

private def H (q : ℚ) := (q.num.natAbs + 1) * q.den

private lemma height (q : ℚ) : H q ≤ 2 ^ (encRat q).length := by
  have h := Nat.mul_le_mul (bitCap q.num.natAbs) (bitCap q.den).le
  unfold H
  refine h.trans ?_
  rw [← pow_add]
  apply Nat.pow_le_pow_right (by decide)
  simp [encRat, encInt]; omega

private lemma concatCap {α : Type} (h : α → ℕ) (f : α → List Sym)
    (hf : ∀ x, h x ≤ 2 ^ (f x).length) (xs : List α) :
    (xs.map h).prod ≤ 2 ^ (xs.flatMap f).length := by
  induction xs with
  | nil => simp
  | cons x xs ih => simpa [pow_add] using Nat.mul_le_mul (hf x) ih

private lemma vecCap {k : ℕ} (x : Fin k → ℚ) : ∏ j, H (x j) ≤ 2 ^ (encVec x).length := by
  rw [Fin.prod_univ_def]
  apply concatCap
  intro j
  exact (height _).trans (Nat.pow_le_pow_right (by decide) (by simp))

private lemma matCap {m k : ℕ} (A : Matrix (Fin m) (Fin k) ℚ) :
    ∏ i, ∏ j, H (A i j) ≤ 2 ^ (encMat A).length := by
  rw [Fin.prod_univ_def]
  apply concatCap
  intro i
  exact (vecCap (A i)).trans (Nat.pow_le_pow_right (by decide) (by simp))

theorem solution :
    ∃ a : ℕ, ∀ {m d k : ℕ} (A : Matrix (Fin m) (Fin d) ℚ)
      (B : Matrix (Fin m) (Fin k) ℚ) (b : Fin m → ℚ),
      let P : Set ((Fin d → ℝ) × (Fin k → ℝ)) :=
        {p | ∀ i, (∑ j, (A i j : ℝ) * p.1 j) + (∑ j, (B i j : ℝ) * p.2 j) ≤ (b i : ℝ)}
      Bornology.IsBounded P → ∀ p ∈ P,
        InBox (2 ^ ((1 + (encMat A ++ encMat B ++ encVec b).length) ^ a)) p  := by
  refine ⟨1, ?_⟩
  intro m d k A B b P hb p hp
  have h := polytope_height_product A B b hb p hp
  have cap := Nat.mul_le_mul (Nat.mul_le_mul (matCap A) (matCap B)) (vecCap b)
  rw [← pow_add, ← pow_add] at cap
  have step : (encMat A).length + (encMat B).length + (encVec b).length ≤
      (1 + (encMat A ++ encMat B ++ encVec b).length) ^ 1 := by simp; omega
  have bound := cap.trans (Nat.pow_le_pow_right (by decide) step)
  exact ⟨fun i => (h.1 i).trans (Nat.cast_le.mpr bound), fun j => (h.2 j).trans (Nat.cast_le.mpr bound)⟩
