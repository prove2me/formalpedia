-- Prove2me | solution 1 for NeedPersuasion.FullInfo.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-16T08:56:41.320817+00:00
-- url     : https://prove2.me/submissions/98c48c92-11c5-46d5-83c6-561eb4083fef

import Mathlib
import Definitions.Def_NeedPersuasion_FullInfo_Model

open NeedPersuasion.FullInfo

-- Alexander Richard Towell (queelius), with Codex assistance.
-- Anunrojwong, Iyer and Manshadi, arXiv:2005.07253v3, Lemma 3.
theorem solution (M : Model) (hM : M.Standing) (π : ℕ → ℝ) (hπ : π ∈ PiAP M) :
    (∀ q k : ℕ, q < k → M.lamH ^ (k - q) * π q ≤ π k ∧ π k ≤ M.lam ^ (k - q) * π q) ∧
      (0 < M.lamH → ∀ k : ℕ, 0 < π k ∧ π k < 1) := by
  rcases hπ with ⟨hnonneg, hsum, hstep, hwL, hwH⟩
  have hH : 0 ≤ M.lamH := hM.2.1
  have hL : 0 ≤ M.lam := by unfold Model.lam; linarith [hM.1]
  have bounds (q d : ℕ) : M.lamH ^ d * π q ≤ π (q + d) ∧
      π (q + d) ≤ M.lam ^ d * π q := by
    induction d with
    | zero => simp
    | succ d ih =>
      constructor
      · calc
          M.lamH ^ (d + 1) * π q = M.lamH * (M.lamH ^ d * π q) := by ring
          _ ≤ M.lamH * π (q + d) := mul_le_mul_of_nonneg_left ih.1 hH
          _ ≤ π (q + (d + 1)) := by simpa [Nat.add_assoc] using (hstep (q + d)).1
      · calc
          π (q + (d + 1)) ≤ M.lam * π (q + d) := by simpa [Nat.add_assoc] using (hstep (q + d)).2
          _ ≤ M.lam * (M.lam ^ d * π q) := mul_le_mul_of_nonneg_left ih.2 hL
          _ = M.lam ^ (d + 1) * π q := by ring
  constructor
  · intro q k hqk
    simpa [Nat.add_sub_of_le hqk.le] using bounds q (k-q)
  · intro hpos
    have hp0 : 0 < π 0 := by
      by_contra h
      have hz : π 0 = 0 := le_antisymm (le_of_not_gt h) (hnonneg 0)
      have hall : π = 0 := funext fun k => le_antisymm
        (by simpa [hz] using (bounds 0 k).2) (hnonneg k)
      have := hsum.tsum_eq
      simp [hall] at this
    have hp (k : ℕ) : 0 < π k := by
      have := (bounds 0 k).1
      exact lt_of_lt_of_le (mul_pos (pow_pos hpos k) hp0) (by simpa using this)
    intro k
    refine ⟨hp k, ?_⟩
    have hpair := hsum.summable.sum_le_tsum ({k, k + 1} : Finset ℕ)
      (fun i _ => hnonneg i)
    have heq : ∑ i ∈ ({k, k + 1} : Finset ℕ), π i = π k + π (k + 1) := by
      simp
    rw [heq, hsum.tsum_eq] at hpair
    linarith [hp (k+1)]

#print axioms solution
