-- Prove2me | solution 1 for KnapsackFacets.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T15:16:55.75872+00:00
-- url     : https://prove2.me/submissions/86cfe64e-9cfe-4f6f-8339-e8545c7db075

import Definitions.Def_KnapsackFacets_ShiftedFib

set_option autoImplicit false

open KnapsackFacets in
theorem solution (j : ℕ) (hj : 3 ≤ j) :
    (Real.sqrt 2 - 1) / 4 * Real.sqrt 2 ^ j ≤ (KnapsackFacets.shiftedFib j : ℝ) ∧
      (KnapsackFacets.shiftedFib j : ℝ) ≤ 2 ^ j := by
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hs1 : 1 ≤ Real.sqrt 2 := by nlinarith
  have hs2 : Real.sqrt 2 ≤ 2 := by nlinarith
  have hc : 0 ≤ (Real.sqrt 2 - 1) / 4 := div_nonneg (by linarith) (by norm_num)
  have key : ∀ j, 3 ≤ j →
      ((Real.sqrt 2 - 1) / 4 * Real.sqrt 2 ^ j ≤ (KnapsackFacets.shiftedFib j : ℝ) ∧
        (KnapsackFacets.shiftedFib j : ℝ) ≤ 2 ^ j) ∧
      ((Real.sqrt 2 - 1) / 4 * Real.sqrt 2 ^ (j + 1) ≤ (KnapsackFacets.shiftedFib (j + 1) : ℝ) ∧
        (KnapsackFacets.shiftedFib (j + 1) : ℝ) ≤ 2 ^ (j + 1)) := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base =>
      have f3 : KnapsackFacets.shiftedFib 3 = 1 := by decide
      have f4 : KnapsackFacets.shiftedFib (3 + 1) = 2 := by decide
      rw [f3, f4]
      have e3 : Real.sqrt 2 ^ 3 = 2 * Real.sqrt 2 := by
        rw [pow_succ, hs]
      have e4 : Real.sqrt 2 ^ (3 + 1) = 4 := by
        rw [show 3 + 1 = 2 * 2 by rfl, pow_mul, hs]; norm_num
      rw [e3, e4]
      norm_num
      constructor <;> nlinarith
    | succ j hj ih =>
      refine ⟨ih.2, ?_⟩
      have hrec : KnapsackFacets.shiftedFib (j + 1 + 1) =
          KnapsackFacets.shiftedFib j + KnapsackFacets.shiftedFib (j + 1) := by
        obtain ⟨i, rfl⟩ : ∃ i, j = i + 2 := ⟨j - 2, by omega⟩
        show KnapsackFacets.shiftedFib (i + 4) = _
        rw [KnapsackFacets.shiftedFib]
      rw [hrec]
      push_cast
      obtain ⟨⟨l1, u1⟩, ⟨l2, u2⟩⟩ := ih
      constructor
      · have e : Real.sqrt 2 ^ (j + 1 + 1) = 2 * Real.sqrt 2 ^ j := by
          rw [pow_succ, pow_succ, mul_assoc, ← sq, hs]; ring
        have h2 : Real.sqrt 2 ^ j ≤ Real.sqrt 2 ^ (j + 1) := by
          rw [pow_succ]
          nlinarith [pow_nonneg hs0 j]
        rw [e]
        nlinarith [mul_le_mul_of_nonneg_left h2 hc]
      · have e1 : (2:ℝ) ^ (j + 1 + 1) = 4 * 2 ^ j := by ring
        have e2 : (2:ℝ) ^ (j + 1) = 2 * 2 ^ j := by ring
        rw [e1]
        rw [e2] at u2
        linarith
  exact (key j hj).1
