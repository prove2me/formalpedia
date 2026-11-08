-- Prove2me | solution 1 for L0BnB.Relax.VB_le_vstar
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T15:44:56.750375+00:00
-- url     : https://prove2.me/submissions/537c2928-e6db-44cb-89ff-a52f33b3e711

import Mathlib
import Definitions.Def_L0BnB_Relax_VB
import Definitions.Def_L0BnB_Relax_vstar

open L0BnB.Relax in
theorem solution {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ)
    (lam0 lam2 M : ℝ) (h0 : 0 < lam0) (h2 : 0 < lam2) (hM : Real.sqrt (lam0 / lam2) ≤ M) :
    VB X y lam0 lam2 M ≤ vstar X y lam0 lam2 M := by
  have hc : 0 < Real.sqrt (lam2 / lam0) := Real.sqrt_pos.mpr (div_pos h2 h0)
  have hc2 : Real.sqrt (lam2 / lam0) ^ 2 = lam2 / lam0 := Real.sq_sqrt (div_pos h2 h0).le
  have hlam2 : lam2 = lam0 * Real.sqrt (lam2 / lam0) ^ 2 := by
    rw [hc2]
    field_simp
  have hinv : Real.sqrt (lam0 / lam2) * Real.sqrt (lam2 / lam0) = 1 := by
    rw [← Real.sqrt_mul (div_pos h0 h2).le]
    rw [show lam0 / lam2 * (lam2 / lam0) = 1 by field_simp]
    exact Real.sqrt_one
  have hMpos : 0 < M := lt_of_lt_of_le (Real.sqrt_pos.mpr (div_pos h0 h2)) hM
  obtain ⟨c, hcdef⟩ : ∃ c, c = Real.sqrt (lam2 / lam0) := ⟨_, rfl⟩
  rw [← hcdef] at hc hlam2 hinv
  have hMc : 1 ≤ M * c := by
    have := mul_le_mul_of_nonneg_right hM hc.le
    linarith
  -- pointwise: for each coordinate, a feasible z with small cost
  have hpt : ∀ b : ℝ, |b| ≤ M → ∃ z : ℝ, 0 ≤ z ∧ z ≤ 1 ∧ -(M * z) ≤ b ∧ b ≤ M * z ∧
      lam0 * z + lam2 * b ^ 2 ≤ psi1 lam0 lam2 b := by
    intro b hb
    unfold psi1 reverseHuber
    rw [← hcdef]
    split_ifs with ht
    · rw [abs_mul, abs_of_pos hc] at ht ⊢
      refine ⟨|b| / M, by positivity, by rw [div_le_one hMpos]; exact hb, ?_, ?_, ?_⟩
      · rw [mul_div_cancel₀ _ hMpos.ne']
        exact neg_abs_le b
      · rw [mul_div_cancel₀ _ hMpos.ne']
        exact le_abs_self b
      · rw [hlam2]
        have h1 : |b| / M ≤ |b| * c := by
          rw [div_le_iff₀ hMpos]
          nlinarith [abs_nonneg b]
        have h2' : c ^ 2 * b ^ 2 ≤ |b| * c := by
          have : (|b| * c) ^ 2 ≤ |b| * c := by
            nlinarith [mul_nonneg (mul_nonneg (abs_nonneg b) hc.le) (sub_nonneg.mpr ht)]
          rw [mul_pow, sq_abs] at this
          linarith
        nlinarith
    · refine ⟨1, zero_le_one, le_rfl, ?_, ?_, ?_⟩
      · rw [mul_one]
        exact neg_le_of_abs_le hb
      · rw [mul_one]
        exact le_of_abs_le hb
      · rw [hlam2]
        nlinarith
  have hS1bdd : BddBelow {v | ∃ β z : Fin p → ℝ, bigMFeasible M β z ∧
      bigMObj X y lam0 lam2 β z = v} := by
    refine ⟨0, ?_⟩
    rintro v ⟨β, z, hf, rfl⟩
    unfold bigMObj rss
    have h1 : 0 ≤ ∑ j, (y j - X.mulVec β j) ^ 2 := Finset.sum_nonneg (fun j _ => sq_nonneg _)
    have h2' : 0 ≤ ∑ i, z i := Finset.sum_nonneg (fun i _ => (hf i).1)
    have h3 : 0 ≤ ∑ i, β i ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
    positivity
  have hne : (G X y lam0 lam2 '' {β | ∀ i, |β i| ≤ M}).Nonempty :=
    ⟨_, ⟨0, fun i => by simp [hMpos.le], rfl⟩⟩
  unfold vstar VB
  apply le_csInf hne
  rintro v ⟨β, hβ, rfl⟩
  choose z hz using fun i => hpt (β i) (hβ i)
  apply csInf_le_of_le hS1bdd ⟨β, z, fun i => ⟨(hz i).1, (hz i).2.1, (hz i).2.2.1, (hz i).2.2.2.1⟩,
    rfl⟩
  unfold bigMObj G
  have : lam0 * ∑ i, z i + lam2 * ∑ i, β i ^ 2 ≤ ∑ i, psi1 lam0 lam2 (β i) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun i _ => (hz i).2.2.2.2)
  linarith
