-- Prove2me | solution 1 for JaggiFW.Sparsity.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-11T03:47:57.814982+00:00
-- url     : https://prove2.me/submissions/e6fed6ed-29af-440a-a67f-7f2b3cc8c40a

import Mathlib
import Definitions.Def_JaggiFW_Sparsity_Setting

open JaggiFW.Sparsity

private lemma sparse_lower {n : ℕ} (k : ℕ) (hk : 0 < k)
    (x : Fin n → ℝ) (hx : x ∈ stdSimplex ℝ (Fin n)) (hc : card x ≤ k) :
    1 / (k : ℝ) ≤ sqNorm x := by
  classical
  let s : Finset (Fin n) := Finset.univ.filter fun i => x i ≠ 0
  have hsum : ∑ i ∈ s, x i = 1 := by
    calc
      _ = ∑ i, x i := Finset.sum_subset (Finset.filter_subset _ _) (by
        intro i _ hi
        simp only [s, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hi
        exact hi)
      _ = 1 := hx.2
  have hsq : ∑ i ∈ s, x i ^ 2 = sqNorm x := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro i _ hi
    simp only [s, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hi
    simp [hi]
  have hcs := sq_sum_le_card_mul_sum_sq (s := s) (f := x)
  rw [hsum, hsq, one_pow] at hcs
  have hcard : (s.card : ℝ) ≤ k := by exact_mod_cast hc
  have hnonneg : 0 ≤ sqNorm x := Finset.sum_nonneg fun i _ => sq_nonneg (x i)
  have hbound := hcs.trans (mul_le_mul_of_nonneg_right hcard hnonneg)
  apply (div_le_iff₀ (by exact_mod_cast hk : (0 : ℝ) < k)).2
  nlinarith

theorem solution {n : ℕ} (k : ℕ) (hk1 : 1 ≤ k) (hkn : k ≤ n) :
    IsLeast {r : ℝ | ∃ x ∈ stdSimplex ℝ (Fin n), card x ≤ k ∧ r = sqNorm x}
      (1 / (k : ℝ)) := by
  classical
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk1
  have hkne : (k : ℝ) ≠ 0 := ne_of_gt hkpos
  obtain ⟨s, _, hscard⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Fin n)))
    (by simpa using hkn)
  let x : Fin n → ℝ := fun i => if i ∈ s then 1 / (k : ℝ) else 0
  have hx : x ∈ stdSimplex ℝ (Fin n) := by
    constructor
    · intro i
      dsimp [x]
      split_ifs <;> positivity
    · simp [x, hscard, hkne]
  have hcard : card x = k := by
    unfold card
    have hs : Finset.univ.filter (fun i => x i ≠ 0) = s := by
      ext i
      simp [x, hkne]
    rw [hs, hscard]
  have hnorm : sqNorm x = 1 / (k : ℝ) := by
    simp only [sqNorm, x, ite_pow, zero_pow (by decide : 2 ≠ 0)]
    simp [hscard]
    field_simp
  constructor
  · exact ⟨x, hx, hcard.le, hnorm.symm⟩
  · rintro r ⟨y, hy, hc, rfl⟩
    exact sparse_lower k (by omega) y hy hc
