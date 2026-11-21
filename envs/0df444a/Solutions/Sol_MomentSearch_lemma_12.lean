-- Prove2me | solution 1 for MomentSearch.lemma_12
-- status  : ACCEPTED   (prove)
-- author  : @nmegow
-- created : 2026-11-20T22:50:55.00246+00:00
-- url     : https://prove2.me/submissions/99239aaf-aa0b-4646-a4ea-e467f502ee01

import Mathlib
import Definitions.Def_MomentSearch_correctionNorm
import Theorems.Thm_LP_strong_duality_matrix

open scoped BigOperators
open Matrix MomentSearch

theorem solution {n : ℕ} (_hn : 2 ≤ n) (k : ℕ) (m m₀ : Fin n) :
    IsGreatest
      {y : ℝ | ∃ q : Polynomial ℝ, q.natDegree ≤ k ∧
        (∀ t : Fin n, |q.eval (grid n (t : ℕ))| ≤ 1) ∧
        y = q.eval (grid n (m : ℕ)) - q.eval (grid n (m₀ : ℕ))}
      (correctionNorm n k m m₀) ∧
    ∃ a : Fin n → ℝ, SolvesCorrection n k m m₀ a ∧
      ∑ t : Fin n, |a t| = correctionNorm n k m m₀ := by
  classical
  let τ (t : Fin n) := grid n (t : ℕ)
  let b (i : Fin (k + 1)) : ℝ := τ m ^ (i : ℕ) - τ m₀ ^ (i : ℕ)
  let A : Matrix (Fin n ⊕ Fin n) (Fin (k + 1)) ℝ :=
    fun j i => Sum.elim (fun t => τ t ^ (i : ℕ)) (fun t => -(τ t ^ (i : ℕ))) j
  let c : Fin n ⊕ Fin n → ℝ := fun _ => 1
  let δ (j t : Fin n) : ℝ := if t = j then 1 else 0
  have hP : ∃ x, A *ᵥ x ≤ c := ⟨0, by
    intro j
    simp [Matrix.mulVec, dotProduct, c]⟩
  have hD : ∃ y, 0 ≤ y ∧ Aᵀ *ᵥ y = b := by
    refine ⟨Sum.elim (δ m) (δ m₀), ?_, ?_⟩
    · intro j
      cases j <;> simp [δ, apply_ite]
    · funext i
      change (∑ j, A j i * Sum.elim (δ m) (δ m₀) j) = b i
      simp [Fintype.sum_sum_type, A, b, δ, mul_ite, sub_eq_add_neg]
  obtain ⟨x, y, hx, hy, hAy, heq, _⟩ := LP.strong_duality_matrix A c b hP hD
  let a (t : Fin n) : ℝ := y (.inl t) - y (.inr t)
  have ha : SolvesCorrection n k m m₀ a := by
    intro i hi
    let j : Fin (k + 1) := ⟨i, Nat.lt_succ_of_le hi⟩
    have h := congrFun hAy j
    change (∑ l, A l j * y l) = b j at h
    simpa [Fintype.sum_sum_type, A, b, a, τ, j, mul_comm,
      sub_mul, Finset.sum_sub_distrib, neg_mul, Finset.sum_neg_distrib, sub_eq_add_neg, mul_add, Finset.sum_add_distrib, mul_neg] using h
  let q : Polynomial ℝ :=
    ∑ i : Fin (k + 1), Polynomial.monomial (i : ℕ) (x i)
  have hqdeg : q.natDegree ≤ k := by
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro i _
    exact (Polynomial.natDegree_monomial_le _).trans (Nat.le_of_lt_succ i.isLt)
  have evalQ (z : ℝ) : q.eval z = ∑ i : Fin (k + 1), x i * z ^ (i : ℕ) := by
    simp [q, Polynomial.eval_finsetSum, Polynomial.eval_monomial]
  have hqgrid (t : Fin n) : |q.eval (τ t)| ≤ 1 := by
    rw [abs_le]
    have hp := hx (Sum.inl t)
    have hm := hx (Sum.inr t)
    simp only [Matrix.mulVec, dotProduct, A, Sum.elim_inl, Sum.elim_inr, c,
      neg_mul, Finset.sum_neg_distrib] at hp hm
    rw [evalQ]
    simp_rw [mul_comm (x _)]
    exact ⟨by linarith, hp⟩
  have hobj : q.eval (τ m) - q.eval (τ m₀) = b ⬝ᵥ x := by
    rw [evalQ, evalQ, ← Finset.sum_sub_distrib]
    simp [dotProduct, b, mul_sub, mul_comm]
  have hnorm : (∑ t : Fin n, |a t|) ≤ c ⬝ᵥ y := by
    simp only [dotProduct, Fintype.sum_sum_type, c, one_mul, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro t _
    dsimp [a]
    rw [abs_le]
    have hp : 0 ≤ y (Sum.inl t) := hy (Sum.inl t)
    have hm : 0 ≤ y (Sum.inr t) := hy (Sum.inr t)
    constructor <;> linarith
  have weak (r : Polynomial ℝ) (hr : r.natDegree ≤ k)
      (hg : ∀ t : Fin n, |r.eval (τ t)| ≤ 1)
      (u : Fin n → ℝ) (hu : SolvesCorrection n k m m₀ u) :
      r.eval (τ m) - r.eval (τ m₀) ≤ ∑ t : Fin n, |u t| := by
    have reval (z : ℝ) :
        r.eval z = ∑ i : Fin (k + 1), r.coeff (i : ℕ) * z ^ (i : ℕ) := by
      rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hr) z]
      exact (Fin.sum_univ_eq_sum_range (fun j : ℕ => r.coeff j * z ^ j) (k + 1)).symm
    calc
      r.eval (τ m) - r.eval (τ m₀) =
          ∑ i : Fin (k + 1), r.coeff (i : ℕ) * b i := by
        simp [reval, ← Finset.sum_sub_distrib, b, mul_sub]
      _ = ∑ t : Fin n, u t * r.eval (τ t) := by
        simp only [reval, Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        have h := hu (i : ℕ) (Nat.le_of_lt_succ i.isLt)
        change (∑ t : Fin n, u t * τ t ^ (i : ℕ)) = b i at h
        rw [← h, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro t _
        ring
      _ ≤ ∑ t : Fin n, |u t| := by
        apply Finset.sum_le_sum
        intro t _
        calc
          u t * r.eval (τ t) ≤ |u t * r.eval (τ t)| := le_abs_self _
          _ ≤ |u t| := by rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (hg t)
  have hval : (∑ t : Fin n, |a t|) = q.eval (τ m) - q.eval (τ m₀) := by
    apply le_antisymm
    · rwa [hobj, heq]
    · exact weak q hqdeg hqgrid a ha
  have hcorr : correctionNorm n k m m₀ = ∑ t : Fin n, |a t| := by
    unfold correctionNorm
    apply le_antisymm
    · apply csInf_le
      · exact ⟨0, by rintro s ⟨u, _, rfl⟩; positivity⟩
      · exact ⟨a, ha, rfl⟩
    · apply le_csInf
      · exact ⟨_, a, ha, rfl⟩
      · rintro s ⟨u, hu, rfl⟩
        rw [hval]
        exact weak q hqdeg hqgrid u hu
  refine ⟨⟨⟨q, hqdeg, hqgrid, hcorr.trans hval⟩, ?_⟩, a, ha, hcorr.symm⟩
  rintro s ⟨r, hr, hg, rfl⟩
  rw [hcorr]
  exact weak r hr hg a ha
