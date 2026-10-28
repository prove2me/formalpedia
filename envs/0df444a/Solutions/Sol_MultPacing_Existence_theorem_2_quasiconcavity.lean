-- Prove2me | solution 1 for MultPacing.Existence.theorem_2_quasiconcavity
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-27T02:20:48.683363+00:00
-- url     : https://prove2.me/submissions/3bd8cbe9-6902-4654-8af1-33bd46217e54

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

namespace MPX

variable {N G : Type*} [Fintype N] [DecidableEq N] [Fintype G]

lemma bid_update_self (P : PacingGame N G) (ε : ℝ) (α : N → ℝ) (i : N) (a : ℝ) (j : G) :
    smBid P ε (Function.update α i a) j (some i) = a * P.v i j := by
  simp [smBid]

lemma bid_update_ne (P : PacingGame N G) (ε : ℝ) (α : N → ℝ) (i : N) (a : ℝ) (j : G)
    (k : Option N) (hk : k ≠ some i) :
    smBid P ε (Function.update α i a) j k = smBid P ε α j k := by
  rcases k with _ | k
  · rfl
  · have : k ≠ i := by rintro rfl; exact hk rfl
    simp [smBid, Function.update_of_ne this]

lemma topBid_update (P : PacingGame N G) (ε : ℝ) (α : N → ℝ) (i : N) (a : ℝ) (j : G) :
    topBid P ε (Function.update α i a) j = max (a * P.v i j) (smPrice P ε α i j + ε) := by
  rw [topBid_eq P ε _ i j, smPrice_update]; simp

lemma alloc_zero_of_lt (P : PacingGame N G) (ε : ℝ) (α : N → ℝ) (i : N) (j : G)
    (h : α i * P.v i j < smPrice P ε α i j) : smAlloc P ε α i j = 0 := by
  have hT := topBid_eq P ε α i j
  have hw : bandWeight P ε α j (some i) = 0 := by
    unfold bandWeight
    apply max_eq_left
    simp only [smBid]
    have := le_max_right (α i * P.v i j) (smPrice P ε α i j + ε)
    linarith
  simp [smAlloc, hw]

lemma price_le_bid_of_pos (P : PacingGame N G) (ε : ℝ) (α : N → ℝ) (i : N) (j : G)
    (h : 0 < smAlloc P ε α i j) : smPrice P ε α i j ≤ α i * P.v i j := by
  by_contra h'
  push Not at h'
  rw [alloc_zero_of_lt P ε α i j h'] at h
  exact lt_irrefl _ h

/-- monotonicity of the allocation in the own multiplier -/
lemma alloc_mono (P : PacingGame N G) (ε : ℝ) (hε : 0 < ε) (α : N → ℝ) (i : N) (j : G)
    {a1 a2 : ℝ} (h12 : a1 ≤ a2) :
    smAlloc P ε (Function.update α i a1) i j ≤ smAlloc P ε (Function.update α i a2) i j := by
  set α1 := Function.update α i a1
  set α2 := Function.update α i a2
  have hv := P.v_nonneg i j
  have hb : a1 * P.v i j ≤ a2 * P.v i j := mul_le_mul_of_nonneg_right h12 hv
  set m := smPrice P ε α i j + ε
  have hT1 : topBid P ε α1 j = max (a1 * P.v i j) m := topBid_update P ε α i a1 j
  have hT2 : topBid P ε α2 j = max (a2 * P.v i j) m := topBid_update P ε α i a2 j
  have hTle : topBid P ε α1 j ≤ topBid P ε α2 j := by rw [hT1, hT2]; exact max_le_max hb le_rfl
  -- own weights
  have hw : bandWeight P ε α1 j (some i) ≤ bandWeight P ε α2 j (some i) := by
    unfold bandWeight
    rw [hT1, hT2, bid_update_self, bid_update_self]
    apply max_le_max le_rfl
    rcases le_total (a1 * P.v i j) m with h1 | h1 <;>
    rcases le_total (a2 * P.v i j) m with h2 | h2 <;>
    simp only [max_eq_right h1, max_eq_left h1, max_eq_right h2, max_eq_left h2] <;> linarith
  have hk : ∀ k ∈ Finset.univ.erase (some i), bandWeight P ε α2 j k ≤ bandWeight P ε α1 j k := by
    intro k hk
    have hk' : k ≠ some i := Finset.ne_of_mem_erase hk
    unfold bandWeight
    rw [bid_update_ne P ε α i a1 j k hk', bid_update_ne P ε α i a2 j k hk']
    apply max_le_max le_rfl
    linarith
  set w1 := bandWeight P ε α1 j (some i)
  set w2 := bandWeight P ε α2 j (some i)
  set S1 := ∑ k ∈ Finset.univ.erase (some i), bandWeight P ε α1 j k
  set S2 := ∑ k ∈ Finset.univ.erase (some i), bandWeight P ε α2 j k
  have hD1 : ∑ k : Option N, bandWeight P ε α1 j k = w1 + S1 :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ _)).symm
  have hD2 : ∑ k : Option N, bandWeight P ε α2 j k = w2 + S2 :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ _)).symm
  have hS : S2 ≤ S1 := Finset.sum_le_sum hk
  have hS2 : 0 ≤ S2 := Finset.sum_nonneg fun k _ => bandWeight_nonneg _ _ _ _ _
  have hw1 : 0 ≤ w1 := bandWeight_nonneg _ _ _ _ _
  have hp1 := denom_pos P ε hε α1 j
  have hp2 := denom_pos P ε hε α2 j
  unfold smAlloc
  rw [div_le_div_iff₀ hp1 hp2, hD1, hD2]
  rw [hD1] at hp1
  nlinarith [mul_le_mul hw hS hS2 (hw1.trans hw)]

lemma smSpend_update (P : PacingGame N G) (ε : ℝ) (α : N → ℝ) (i : N) (a : ℝ) :
    smSpend P ε (Function.update α i a) i =
      a * ε + ∑ j, smAlloc P ε (Function.update α i a) i j * smPrice P ε α i j := by
  unfold smSpend smPay
  simp [smPrice_update]

lemma smUtility_update (P : PacingGame N G) (ε H : ℝ) (α : N → ℝ) (i : N) (a : ℝ) :
    smUtility P ε H (Function.update α i a) i =
      budgetTerm H (P.B i - smSpend P ε (Function.update α i a) i) + 2 * a * ε +
        ∑ j, smAlloc P ε (Function.update α i a) i j * P.v i j := by
  unfold smUtility
  simp

lemma spend_diff (P : PacingGame N G) (ε : ℝ) (hε : 0 < ε) (α : N → ℝ) (i : N)
    {a1 a2 : ℝ} (h12 : a1 ≤ a2) :
    (a2 - a1) * ε + ε * ∑ j, (smAlloc P ε (Function.update α i a2) i j -
        smAlloc P ε (Function.update α i a1) i j) ≤
      smSpend P ε (Function.update α i a2) i - smSpend P ε (Function.update α i a1) i := by
  rw [smSpend_update, smSpend_update, Finset.mul_sum]
  have : ∀ j ∈ Finset.univ, ε * (smAlloc P ε (Function.update α i a2) i j -
        smAlloc P ε (Function.update α i a1) i j) ≤
      smAlloc P ε (Function.update α i a2) i j * smPrice P ε α i j -
        smAlloc P ε (Function.update α i a1) i j * smPrice P ε α i j := by
    intro j _
    have h1 := alloc_mono P ε hε α i j h12
    have h2 := eps_le_smPrice P ε α i j
    nlinarith
  have := Finset.sum_le_sum this
  rw [Finset.sum_sub_distrib] at this
  linarith

lemma alloc_sum_diff_nonneg (P : PacingGame N G) (ε : ℝ) (hε : 0 < ε) (α : N → ℝ) (i : N)
    {a1 a2 : ℝ} (h12 : a1 ≤ a2) :
    0 ≤ ∑ j, (smAlloc P ε (Function.update α i a2) i j - smAlloc P ε (Function.update α i a1) i j) :=
  Finset.sum_nonneg fun j _ => sub_nonneg.2 (alloc_mono P ε hε α i j h12)

lemma spend_strictMono (P : PacingGame N G) (ε : ℝ) (hε : 0 < ε) (α : N → ℝ) (i : N)
    {a1 a2 : ℝ} (h12 : a1 < a2) :
    smSpend P ε (Function.update α i a1) i < smSpend P ε (Function.update α i a2) i := by
  have h1 := spend_diff P ε hε α i h12.le
  have h2 := alloc_sum_diff_nonneg P ε hε α i h12.le
  nlinarith

lemma util_strictMono_low (P : PacingGame N G) (ε H : ℝ) (hε : 0 < ε) (α : N → ℝ) (i : N)
    {a1 a2 : ℝ} (ha1 : 0 ≤ a1) (ha2 : a2 ≤ 1) (h12 : a1 < a2)
    (hs1 : smSpend P ε (Function.update α i a1) i ≤ P.B i)
    (hs2 : smSpend P ε (Function.update α i a2) i ≤ P.B i) :
    smUtility P ε H (Function.update α i a1) i < smUtility P ε H (Function.update α i a2) i := by
  rw [smUtility_update, smUtility_update]
  unfold budgetTerm
  rw [if_pos (by linarith), if_pos (by linarith)]
  rw [smSpend_update, smSpend_update]
  have key : ∀ j ∈ Finset.univ,
      smAlloc P ε (Function.update α i a1) i j * P.v i j -
        smAlloc P ε (Function.update α i a1) i j * smPrice P ε α i j ≤
      smAlloc P ε (Function.update α i a2) i j * P.v i j -
        smAlloc P ε (Function.update α i a2) i j * smPrice P ε α i j := by
    intro j _
    have hv := P.v_nonneg i j
    rcases lt_or_ge (P.v i j) (smPrice P ε α i j) with h | h
    · have e1 : smAlloc P ε (Function.update α i a1) i j = 0 := by
        apply alloc_zero_of_lt
        simp only [Function.update_self, smPrice_update]
        nlinarith
      have e2 : smAlloc P ε (Function.update α i a2) i j = 0 := by
        apply alloc_zero_of_lt
        simp only [Function.update_self, smPrice_update]
        nlinarith
      rw [e1, e2]
    · have := alloc_mono P ε hε α i j h12.le
      nlinarith
  have := Finset.sum_le_sum key
  simp only [Finset.sum_sub_distrib] at this
  nlinarith

lemma util_strictAnti_high (P : PacingGame N G) (ε H M : ℝ) (hε : 0 < ε) (α : N → ℝ) (i : N)
    (hM : ∑ j, P.v i j + 2 * ε ≤ M) (hH : M / ε < H)
    {a1 a2 : ℝ} (h12 : a1 < a2)
    (hs1 : P.B i ≤ smSpend P ε (Function.update α i a1) i)
    (hs2 : P.B i ≤ smSpend P ε (Function.update α i a2) i) :
    smUtility P ε H (Function.update α i a2) i < smUtility P ε H (Function.update α i a1) i := by
  rw [smUtility_update, smUtility_update]
  have hbt : ∀ y ≤ (0:ℝ), budgetTerm H y = H * y := by
    intro y hy; unfold budgetTerm; split_ifs with h
    · have : y = 0 := le_antisymm hy h
      subst this; simp
    · rfl
  rw [hbt _ (by linarith), hbt _ (by linarith)]
  have hsumv : ∀ j, P.v i j ≤ M := by
    intro j
    have : P.v i j ≤ ∑ j, P.v i j :=
      Finset.single_le_sum (fun k _ => P.v_nonneg i k) (Finset.mem_univ j)
    linarith
  have hHe : M < H * ε := by rwa [div_lt_iff₀ hε] at hH
  have hM0 : 0 < M := by
    have : 0 ≤ ∑ j, P.v i j := Finset.sum_nonneg fun k _ => P.v_nonneg i k
    linarith
  have hH0 : 0 < H := by
    have : 0 < M / ε := div_pos hM0 hε
    linarith
  have hT := alloc_sum_diff_nonneg P ε hε α i h12.le
  have hsd := spend_diff P ε hε α i h12.le
  set T := ∑ j, (smAlloc P ε (Function.update α i a2) i j - smAlloc P ε (Function.update α i a1) i j)
  have hv : ∑ j, smAlloc P ε (Function.update α i a2) i j * P.v i j -
      ∑ j, smAlloc P ε (Function.update α i a1) i j * P.v i j ≤ M * T := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    have := alloc_mono P ε hε α i j h12.le
    have := hsumv j
    have := P.v_nonneg i j
    nlinarith
  have hspos : 0 < (a2 - a1) + T := by linarith
  have e1 := mul_le_mul_of_nonneg_left hsd hH0.le
  have e2 := mul_lt_mul_of_pos_right hHe hspos
  have h2e : 2 * ε ≤ M := by
    have : 0 ≤ ∑ j, P.v i j := Finset.sum_nonneg fun k _ => P.v_nonneg i k
    linarith
  have e3 : 2 * ε * (a2 - a1) ≤ M * (a2 - a1) := mul_le_mul_of_nonneg_right h2e (by linarith)
  nlinarith

end MPX

namespace MPX

lemma update_cont {N : Type*} [DecidableEq N] (α : N → ℝ) (i : N) :
    Continuous (fun a : ℝ => Function.update α i a) :=
  continuous_const.update i continuous_id

end MPX

open MPX in
theorem solution {N G : Type*} [Fintype N] [DecidableEq N] [Fintype G]
    (P : PacingGame N G) (ε H M : ℝ) (hε : 0 < ε) (α : N → ℝ)
    (hα : ∀ k, α k ∈ Set.Icc (0 : ℝ) 1) (i : N) :
    (ContinuousOn (fun a => smSpend P ε (Function.update α i a) i) (Set.Icc 0 1) ∧
      StrictMonoOn (fun a => smSpend P ε (Function.update α i a) i) (Set.Icc 0 1)) ∧
    StrictMonoOn (fun a => smUtility P ε H (Function.update α i a) i)
      {a | a ∈ Set.Icc (0 : ℝ) 1 ∧ smSpend P ε (Function.update α i a) i ≤ P.B i} ∧
    ((∀ k, ∑ j, P.v k j + 2 * ε ≤ M) → M / ε < H →
      StrictAntiOn (fun a => smUtility P ε H (Function.update α i a) i)
        {a | a ∈ Set.Icc (0 : ℝ) 1 ∧ P.B i ≤ smSpend P ε (Function.update α i a) i}) := by
  refine ⟨⟨((smSpend_cont P ε hε i).comp (update_cont α i)).continuousOn, ?_⟩, ?_, ?_⟩
  · intro a1 _ a2 _ h12
    exact spend_strictMono P ε hε α i h12
  · rintro a1 ⟨⟨h0, -⟩, hs1⟩ a2 ⟨⟨-, h1⟩, hs2⟩ h12
    exact util_strictMono_low P ε H hε α i h0 h1 h12 hs1 hs2
  · intro hM hH
    rintro a1 ⟨-, hs1⟩ a2 ⟨-, hs2⟩ h12
    exact util_strictAnti_high P ε H M hε α i (hM i) hH h12 hs1 hs2
