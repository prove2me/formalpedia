-- Prove2me | solution 1 for MultPacing.Existence.theorem_2_continuity
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-27T02:18:11.643191+00:00
-- url     : https://prove2.me/submissions/644939af-4c60-426e-aed7-e570a48a4a4b

import Mathlib
import Definitions.Def_MultPacing_Existence_Smoothed

open MultPacing.Existence

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace MPX

variable {N G : Type*} [Fintype N] [DecidableEq N] [Fintype G]

lemma le_topBid (P : PacingGame N G) (ε : ℝ) (α : N → ℝ) (j : G) (k : Option N) :
    smBid P ε α j k ≤ topBid P ε α j :=
  Finset.le_sup' (smBid P ε α j) (Finset.mem_univ k)

lemma exists_top (P : PacingGame N G) (ε : ℝ) (α : N → ℝ) (j : G) :
    ∃ k, topBid P ε α j = smBid P ε α j k := by
  obtain ⟨k, -, hk⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (smBid P ε α j)
  exact ⟨k, hk⟩

lemma two_eps_le_topBid (P : PacingGame N G) (ε : ℝ) (α : N → ℝ) (j : G) :
    2 * ε ≤ topBid P ε α j := le_topBid P ε α j none

lemma bandWeight_nonneg (P : PacingGame N G) (ε : ℝ) (α : N → ℝ) (j : G) (k : Option N) :
    0 ≤ bandWeight P ε α j k := le_max_left _ _

lemma eps_le_denom (P : PacingGame N G) (ε : ℝ) (hε : 0 < ε) (α : N → ℝ) (j : G) :
    ε ≤ ∑ k : Option N, bandWeight P ε α j k := by
  obtain ⟨k, hk⟩ := exists_top P ε α j
  have h1 : bandWeight P ε α j k = ε := by
    unfold bandWeight; rw [hk]; simp [hε.le]
  calc ε = bandWeight P ε α j k := h1.symm
    _ ≤ _ := Finset.single_le_sum (fun k _ => bandWeight_nonneg P ε α j k) (Finset.mem_univ k)

lemma denom_pos (P : PacingGame N G) (ε : ℝ) (hε : 0 < ε) (α : N → ℝ) (j : G) :
    0 < ∑ k : Option N, bandWeight P ε α j k := lt_of_lt_of_le hε (eps_le_denom P ε hε α j)

lemma smAlloc_nonneg (P : PacingGame N G) (ε : ℝ) (α : N → ℝ) (i : N) (j : G) :
    0 ≤ smAlloc P ε α i j :=
  div_nonneg (bandWeight_nonneg _ _ _ _ _) (Finset.sum_nonneg fun k _ => bandWeight_nonneg _ _ _ _ _)

lemma sum_smAlloc_le (P : PacingGame N G) (ε : ℝ) (hε : 0 < ε) (α : N → ℝ) (j : G) :
    ∑ i, smAlloc P ε α i j ≤ 1 := by
  unfold smAlloc
  rw [← Finset.sum_div, div_le_one (denom_pos P ε hε α j), Fintype.sum_option]
  linarith [bandWeight_nonneg P ε α j none]

lemma smAlloc_le_one (P : PacingGame N G) (ε : ℝ) (hε : 0 < ε) (α : N → ℝ) (i : N) (j : G) :
    smAlloc P ε α i j ≤ 1 := by
  calc smAlloc P ε α i j ≤ ∑ i, smAlloc P ε α i j :=
        Finset.single_le_sum (fun k _ => smAlloc_nonneg P ε α k j) (Finset.mem_univ i)
    _ ≤ 1 := sum_smAlloc_le P ε hε α j

lemma smPrice_add (P : PacingGame N G) (ε : ℝ) (α : N → ℝ) (i : N) (j : G) :
    smPrice P ε α i j + ε = (Finset.univ.erase (some i)).sup' ⟨none, by simp⟩ (smBid P ε α j) := by
  unfold smPrice; ring

lemma eps_le_smPrice (P : PacingGame N G) (ε : ℝ) (α : N → ℝ) (i : N) (j : G) :
    ε ≤ smPrice P ε α i j := by
  have : smBid P ε α j none ≤ (Finset.univ.erase (some i)).sup' ⟨none, by simp⟩ (smBid P ε α j) :=
    Finset.le_sup' (smBid P ε α j) (by simp)
  have h2 := smPrice_add P ε α i j
  simp [smBid] at this
  linarith

lemma topBid_eq (P : PacingGame N G) (ε : ℝ) (α : N → ℝ) (i : N) (j : G) :
    topBid P ε α j = max (α i * P.v i j) (smPrice P ε α i j + ε) := by
  rw [smPrice_add]
  apply le_antisymm
  · apply Finset.sup'_le
    intro k _
    by_cases hk : k = some i
    · subst hk; exact le_max_of_le_left (le_refl _)
    · exact le_max_of_le_right (Finset.le_sup' (smBid P ε α j) (by simp [hk]))
  · apply max_le
    · exact le_topBid P ε α j (some i)
    · exact Finset.sup'_mono _ (Finset.subset_univ _) _

lemma smPrice_update (P : PacingGame N G) (ε : ℝ) (α : N → ℝ) (i : N) (a : ℝ) (j : G) :
    smPrice P ε (Function.update α i a) i j = smPrice P ε α i j := by
  unfold smPrice
  congr 1
  apply Finset.sup'_congr _ rfl
  intro k hk
  rcases k with _ | k
  · rfl
  · have : k ≠ i := by rintro rfl; simp at hk
    simp [smBid, Function.update_of_ne this]

lemma budgetTerm_eq (H y : ℝ) : budgetTerm H y = max y 0 + H * min y 0 := by
  unfold budgetTerm
  split_ifs with h
  · simp [h]
  · push Not at h; simp [h.le]

/-! Continuity -/

lemma smBid_cont (P : PacingGame N G) (ε : ℝ) (j : G) (k : Option N) :
    Continuous (fun α : N → ℝ => smBid P ε α j k) := by
  rcases k with _ | k
  · exact continuous_const
  · exact (continuous_apply k).mul continuous_const

lemma topBid_cont (P : PacingGame N G) (ε : ℝ) (j : G) :
    Continuous (fun α : N → ℝ => topBid P ε α j) := by
  unfold topBid
  exact Continuous.finset_sup'_apply _ (fun k _ => smBid_cont P ε j k)

lemma bandWeight_cont (P : PacingGame N G) (ε : ℝ) (j : G) (k : Option N) :
    Continuous (fun α : N → ℝ => bandWeight P ε α j k) := by
  unfold bandWeight
  exact continuous_const.max ((smBid_cont P ε j k).sub ((topBid_cont P ε j).sub continuous_const))

lemma smAlloc_cont (P : PacingGame N G) (ε : ℝ) (hε : 0 < ε) (i : N) (j : G) :
    Continuous (fun α : N → ℝ => smAlloc P ε α i j) := by
  unfold smAlloc
  exact (bandWeight_cont P ε j (some i)).div
    (continuous_finsetSum _ fun k _ => bandWeight_cont P ε j k)
    (fun α => (denom_pos P ε hε α j).ne')

lemma smPrice_cont (P : PacingGame N G) (ε : ℝ) (i : N) (j : G) :
    Continuous (fun α : N → ℝ => smPrice P ε α i j) := by
  unfold smPrice
  exact (Continuous.finset_sup'_apply _ (fun k _ => smBid_cont P ε j k)).sub continuous_const

lemma smPay_cont (P : PacingGame N G) (ε : ℝ) (hε : 0 < ε) (i : N) (j : G) :
    Continuous (fun α : N → ℝ => smPay P ε α i j) :=
  (smAlloc_cont P ε hε i j).mul (smPrice_cont P ε i j)

lemma smSpend_cont (P : PacingGame N G) (ε : ℝ) (hε : 0 < ε) (i : N) :
    Continuous (fun α : N → ℝ => smSpend P ε α i) :=
  ((continuous_apply i).mul continuous_const).add
    (continuous_finsetSum _ fun j _ => smPay_cont P ε hε i j)

lemma smUtility_cont (P : PacingGame N G) (ε H : ℝ) (hε : 0 < ε) (i : N) :
    Continuous (fun α : N → ℝ => smUtility P ε H α i) := by
  unfold smUtility
  simp only [budgetTerm_eq]
  have hs := smSpend_cont P ε hε i
  refine ((((continuous_const.sub hs).max continuous_const).add
    (continuous_const.mul ((continuous_const.sub hs).min continuous_const))).add
    ((continuous_const.mul (continuous_apply i)).mul continuous_const)).add
    (continuous_finsetSum _ fun j _ => (smAlloc_cont P ε hε i j).mul continuous_const)

end MPX

open MPX in
theorem solution {N G : Type*} [Fintype N] [DecidableEq N] [Fintype G]
    (P : PacingGame N G) (ε H : ℝ) (hε : 0 < ε) :
    (∀ i j, ContinuousOn (fun α => smAlloc P ε α i j) (Set.univ.pi fun _ => Set.Icc (0 : ℝ) 1)) ∧
    (∀ i j, ContinuousOn (fun α => smPay P ε α i j) (Set.univ.pi fun _ => Set.Icc (0 : ℝ) 1)) ∧
    (∀ i, ContinuousOn (fun α => smUtility P ε H α i) (Set.univ.pi fun _ => Set.Icc (0 : ℝ) 1)) :=
  ⟨fun i j => (smAlloc_cont P ε hε i j).continuousOn, fun i j => (smPay_cont P ε hε i j).continuousOn,
    fun i => (smUtility_cont P ε H hε i).continuousOn⟩
