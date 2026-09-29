-- Prove2me | solution 1 for MurtyKabadi.Reduction.problems5_6_equiv
-- status  : ACCEPTED   (prove)
-- author  : @37720879
-- created : 2026-09-28T09:06:45.42895+00:00
-- url     : https://prove2.me/submissions/aea2f802-7374-4a31-b122-5a822f0218ab

import Mathlib
import Definitions.Def_MurtyKabadi_Reduction_SubsetSum
import Definitions.Def_MurtyKabadi_Reduction_Construction

open MurtyKabadi.Reduction

theorem solution {n : ℕ} (d : Fin n → ℕ) (d0 δ : ℕ)
    (hd : ∀ j, 0 < d j) (hd0 : 0 < d0)
    (hδ : 4 * (d0 * ∑ j, d j) ^ 2 * n ^ 3 < δ) :
    SubsetSumSolvable d d0 ↔ ∃ p ∈ P n, f1 d d0 δ p.1 p.2 ≤ 0 := by
  have hδpos_nat : 0 < δ := lt_of_le_of_lt (Nat.zero_le _) hδ
  have hδpos : (0 : ℝ) < δ := by exact_mod_cast hδpos_nat
  constructor
  · rintro ⟨z, hz01, hzsum⟩
    let y : Fin n → ℝ := fun j => z j
    let s : Fin n → ℝ := fun j => 1 - y j
    have hz_cases (j : Fin n) : z j = 0 ∨ z j = 1 := by
      rcases hz01 j with ⟨h0, h1⟩
      omega
    have hy_nonneg : (0 : Fin n → ℝ) ≤ y := by
      intro j
      change (0 : ℝ) ≤ (z j : ℝ)
      exact_mod_cast (hz01 j).1
    have hs_nonneg : (0 : Fin n → ℝ) ≤ s := by
      intro j
      change (0 : ℝ) ≤ 1 - (z j : ℝ)
      exact_mod_cast sub_nonneg.mpr (hz01 j).2
    have hsumys : ∑ j, (y j + s j) = (n : ℝ) := by
      simp [s]
    have hsumdy : ∑ j, (d j : ℝ) * y j = (d0 : ℝ) := by
      calc
        ∑ j, (d j : ℝ) * y j = ((∑ j, (d j : ℤ) * z j : ℤ) : ℝ) := by
          simp [y]
        _ = (d0 : ℝ) := by exact_mod_cast hzsum
    have hsum_sq : ∑ j, (y j + s j - 1) ^ 2 = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      dsimp [s]
      ring
    have hsum_prod : ∑ j, y j * s j = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      rcases hz_cases j with h0 | h1
      · simp [y, s, h0]
      · simp [y, s, h1]
    refine ⟨(y, s), ?_, ?_⟩
    · change (0 : Fin n → ℝ) ≤ y ∧ (0 : Fin n → ℝ) ≤ s ∧
        ∑ j, (y j + s j) = (n : ℝ)
      exact ⟨hy_nonneg, hs_nonneg, hsumys⟩
    · change (∑ j, (d j : ℝ) * y j - d0) ^ 2 +
        (δ : ℝ) * (∑ j, (y j + s j - 1) ^ 2) +
        ∑ j, y j * s j ≤ 0
      rw [hsumdy, hsum_sq, hsum_prod]
      norm_num
  · rintro ⟨⟨y, s⟩, hp, hf⟩
    change (0 : Fin n → ℝ) ≤ y ∧ (0 : Fin n → ℝ) ≤ s ∧
      ∑ j, (y j + s j) = (n : ℝ) at hp
    rcases hp with ⟨hy_nonneg, hs_nonneg, hsumys⟩
    have hsq_nonneg : 0 ≤ ∑ j, (y j + s j - 1) ^ 2 := by
      apply Finset.sum_nonneg
      intro j hj
      exact sq_nonneg _
    have hprod_nonneg : 0 ≤ ∑ j, y j * s j := by
      apply Finset.sum_nonneg
      intro j hj
      exact mul_nonneg (hy_nonneg j) (hs_nonneg j)
    have hfirst_nonneg : 0 ≤ (∑ j, (d j : ℝ) * y j - d0) ^ 2 := sq_nonneg _
    have hf' : (∑ j, (d j : ℝ) * y j - d0) ^ 2 +
        (δ : ℝ) * (∑ j, (y j + s j - 1) ^ 2) +
        ∑ j, y j * s j ≤ 0 := by
      simpa only [f1] using hf
    have hδsq_nonneg : 0 ≤ (δ : ℝ) * (∑ j, (y j + s j - 1) ^ 2) :=
      mul_nonneg (le_of_lt hδpos) hsq_nonneg
    have hfirst_zero : (∑ j, (d j : ℝ) * y j - d0) ^ 2 = 0 := by
      linarith
    have hδsq_zero : (δ : ℝ) * (∑ j, (y j + s j - 1) ^ 2) = 0 := by
      linarith
    have hsq_zero : ∑ j, (y j + s j - 1) ^ 2 = 0 := by
      rcases mul_eq_zero.mp hδsq_zero with hδzero | hsumzero
      · exact False.elim ((ne_of_gt hδpos) hδzero)
      · exact hsumzero
    have hprod_zero : ∑ j, y j * s j = 0 := by
      linarith
    have hsumdy : ∑ j, (d j : ℝ) * y j = (d0 : ℝ) := by
      nlinarith [hfirst_zero]
    have hys (j : Fin n) : y j + s j = 1 := by
      have hzero : (y j + s j - 1) ^ 2 = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (y i + s i - 1))).mp
          hsq_zero j (Finset.mem_univ j)
      nlinarith
    have hprod (j : Fin n) : y j * s j = 0 := by
      exact (Finset.sum_eq_zero_iff_of_nonneg
        (fun i _ => mul_nonneg (hy_nonneg i) (hs_nonneg i))).mp
          hprod_zero j (Finset.mem_univ j)
    have hy_cases (j : Fin n) : y j = 0 ∨ y j = 1 := by
      rcases mul_eq_zero.mp (hprod j) with hy | hs
      · exact Or.inl hy
      · exact Or.inr (by linarith [hys j])
    let z : Fin n → ℤ := fun j => if y j = 0 then 0 else 1
    have hzcast (j : Fin n) : (z j : ℝ) = y j := by
      rcases hy_cases j with h0 | h1
      · simp [z, h0]
      · simp [z, h1]
    refine ⟨z, ?_, ?_⟩
    · intro j
      dsimp [z]
      split_ifs <;> omega
    · have hsumcast : ((∑ j, (d j : ℤ) * z j : ℤ) : ℝ) =
          ∑ j, (d j : ℝ) * y j := by
        calc
          ((∑ j, (d j : ℤ) * z j : ℤ) : ℝ) =
              ∑ j, (d j : ℝ) * (z j : ℝ) := by norm_cast
          _ = ∑ j, (d j : ℝ) * y j := by simp_rw [hzcast]
      have hsumz : ((∑ j, (d j : ℤ) * z j : ℤ) : ℝ) = (d0 : ℝ) :=
        hsumcast.trans hsumdy
      exact_mod_cast hsumz
