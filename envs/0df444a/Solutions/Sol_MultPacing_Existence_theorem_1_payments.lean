-- Prove2me | solution 1 for MultPacing.Existence.theorem_1_payments
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-27T02:42:36.768094+00:00
-- url     : https://prove2.me/submissions/c00eea43-55e8-4fbc-9a02-a66686db425b

import Mathlib
import Definitions.Def_MultPacing_Existence_Limit

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

variable {N G : Type*} [Fintype N] [DecidableEq N] [Fintype G]

lemma spend_zero (P : PacingGame N G) (ε : ℝ) (hε : 0 < ε) (α : N → ℝ) (i : N) :
    smSpend P ε (Function.update α i 0) i = 0 := by
  rw [smSpend_update]
  have : ∀ j, smAlloc P ε (Function.update α i 0) i j = 0 := by
    intro j
    apply alloc_zero_of_lt
    simp only [Function.update_self, smPrice_update, zero_mul]
    linarith [eps_le_smPrice P ε α i j]
  simp [this]

lemma spend_at_zero (P : PacingGame N G) (ε : ℝ) (hε : 0 < ε) (α : N → ℝ) (i : N)
    (h : α i = 0) : smSpend P ε α i = 0 := by
  calc smSpend P ε α i = smSpend P ε (Function.update α i 0) i := by
        rw [← h, Function.update_eq_self]
    _ = 0 := spend_zero P ε hε α i

lemma pne_of_cond (P : PacingGame N G) (ε H M : ℝ) (hε : 0 < ε)
    (hM : ∀ i, ∑ j, P.v i j + 2 * ε ≤ M) (hH : M / ε < H) (α : N → ℝ)
    (hα : ∀ i, α i ∈ Set.Icc (0 : ℝ) 1)
    (hc : ∀ i, smSpend P ε α i ≤ P.B i ∧ (α i < 1 → smSpend P ε α i = P.B i)) :
    IsSmoothedPNE P ε H α := by
  refine ⟨hα, fun i a ha => ?_⟩
  have e : Function.update α i (α i) = α := Function.update_eq_self i α
  rcases lt_trichotomy a (α i) with h | h | h
  · have hs := spend_strictMono P ε hε α i h
    rw [e] at hs
    have := util_strictMono_low P ε H hε α i ha.1 (hα i).2 h (by linarith [(hc i).1])
      (by rw [e]; exact (hc i).1)
    rw [e] at this
    exact this.le
  · rw [h, e]
  · have hs := spend_strictMono P ε hε α i h
    rw [e] at hs
    have hlt : α i < 1 := lt_of_lt_of_le h ha.2
    have hB := (hc i).2 hlt
    have := util_strictAnti_high P ε H M hε α i (hM i) hH h (by rw [e]; exact hB.ge)
      (by linarith)
    rw [e] at this
    exact this.le

lemma cond_of_pne (P : PacingGame N G) (ε H M : ℝ) (hε : 0 < ε)
    (hM : ∀ i, ∑ j, P.v i j + 2 * ε ≤ M) (hH : M / ε < H) (α : N → ℝ)
    (hpne : IsSmoothedPNE P ε H α) (i : N) :
    smSpend P ε α i ≤ P.B i ∧ (α i < 1 → smSpend P ε α i = P.B i) := by
  obtain ⟨hα, hbest⟩ := hpne
  have e : Function.update α i (α i) = α := Function.update_eq_self i α
  have hB := P.B_pos i
  set S : ℝ → ℝ := fun a => smSpend P ε (Function.update α i a) i with hS
  have hS0 : S 0 = 0 := spend_zero P ε hε α i
  have hSα : S (α i) = smSpend P ε α i := by simp [hS]
  have hcont : ContinuousOn S (Set.Icc 0 1) :=
    ((smSpend_cont P ε hε i).comp (continuous_const.update i continuous_id)).continuousOn
  have hai := hα i
  rcases le_or_gt (S 1) (P.B i) with h1 | h1
  · -- spend at 1 within budget: α i = 1
    have hall : ∀ a ∈ Set.Icc (0:ℝ) 1, S a ≤ P.B i := by
      intro a ha
      rcases eq_or_lt_of_le ha.2 with h | h
      · rw [h]; exact h1
      · exact (spend_strictMono P ε hε α i h).le.trans h1
    have hα1 : α i = 1 := by
      by_contra hne
      have hlt : α i < 1 := lt_of_le_of_ne hai.2 hne
      have := util_strictMono_low P ε H hε α i hai.1 le_rfl hlt (hall _ hai)
        (hall 1 ⟨zero_le_one, le_rfl⟩)
      rw [e] at this
      linarith [hbest i 1 ⟨zero_le_one, le_rfl⟩]
    refine ⟨?_, fun h => absurd hα1 h.ne⟩
    rw [← hSα]; exact hall _ hai
  · obtain ⟨c, hc, hSc⟩ : ∃ c ∈ Set.Icc (0:ℝ) 1, S c = P.B i :=
      intermediate_value_Icc zero_le_one hcont ⟨by rw [hS0]; exact hB.le, h1.le⟩
    have hαc : α i = c := by
      rcases lt_trichotomy (α i) c with h | h | h
      · have hs := spend_strictMono P ε hε α i h
        have := util_strictMono_low P ε H hε α i hai.1 hc.2 h (by
          have : S (α i) < S c := hs
          linarith) hSc.le
        rw [e] at this
        linarith [hbest i c hc]
      · exact h
      · have hs := spend_strictMono P ε hε α i h
        have := util_strictAnti_high P ε H M hε α i (hM i) hH h hSc.ge (by
          have : S c < S (α i) := hs
          linarith)
        rw [e] at this
        linarith [hbest i c hc]
    have : smSpend P ε α i = P.B i := by rw [← hSα, hαc, hSc]
    exact ⟨this.le, fun _ => this⟩

end MPX

namespace MPX

open Filter Topology

variable {N G : Type*} [Fintype N] [DecidableEq N] [Fintype G]

section Lim

variable {P : PacingGame N G} {ε H : ℕ → ℝ} {M : ℝ} {α : ℕ → N → ℝ} {αs : N → ℝ}
  {xs ps ss : N → G → ℝ}

lemma L_alpha_mem (hlim : IsSmoothedLimit P ε H M α αs xs ps ss) (l : ℕ) (i : N) :
    α l i ∈ Set.Icc (0 : ℝ) 1 := (hlim.equilibrium l).1 i

lemma L_alpha_tendsto (hlim : IsSmoothedLimit P ε H M α αs xs ps ss) (i : N) :
    Tendsto (fun l => α l i) atTop (𝓝 (αs i)) := tendsto_pi_nhds.1 hlim.alpha_tendsto i

lemma L_alphas_mem (hlim : IsSmoothedLimit P ε H M α αs xs ps ss) (i : N) :
    αs i ∈ Set.Icc (0 : ℝ) 1 :=
  isClosed_Icc.mem_of_tendsto (L_alpha_tendsto hlim i) (Eventually.of_forall fun l => L_alpha_mem hlim l i)

lemma L_xs_mem (hlim : IsSmoothedLimit P ε H M α αs xs ps ss) (i : N) (j : G) :
    xs i j ∈ Set.Icc (0 : ℝ) 1 :=
  isClosed_Icc.mem_of_tendsto (hlim.alloc_tendsto i j) (Eventually.of_forall fun l =>
    ⟨smAlloc_nonneg _ _ _ _ _, smAlloc_le_one _ _ (hlim.eps_pos l) _ _ _⟩)

lemma L_cond (hlim : IsSmoothedLimit P ε H M α αs xs ps ss) (l : ℕ) (i : N) :
    smSpend P (ε l) (α l) i ≤ P.B i ∧ (α l i < 1 → smSpend P (ε l) (α l) i = P.B i) :=
  cond_of_pne P (ε l) (H l) M (hlim.eps_pos l) (hlim.M_bound l) (hlim.H_gt l) (α l)
    (hlim.equilibrium l) i

end Lim

/-- joint continuity of the price in `(ε, α)` -/
lemma smPrice_cont2 (P : PacingGame N G) (i : N) (j : G) :
    Continuous (fun p : ℝ × (N → ℝ) => smPrice P p.1 p.2 i j) := by
  unfold smPrice
  refine (Continuous.finset_sup'_apply _ (fun k _ => ?_)).sub continuous_fst
  rcases k with _ | k
  · exact continuous_const.mul continuous_fst
  · exact ((continuous_apply k).comp continuous_snd).mul continuous_const

lemma smPrice_zero_eq (P : PacingGame N G) (α : N → ℝ) (hα : ∀ k, 0 ≤ α k) (i : N) (j : G) :
    smPrice P 0 α i j = highestOther P.v α i j := by
  unfold smPrice highestOther
  rw [sub_zero]
  have hb : ∀ k, 0 ≤ smBid P 0 α j k := by
    intro k; rcases k with _ | k
    · simp [smBid]
    · exact mul_nonneg (hα k) (P.v_nonneg k j)
  split_ifs with h
  · apply le_antisymm
    · apply Finset.sup'_le
      intro k hk
      rcases k with _ | k
      · simp only [smBid, mul_zero]
        obtain ⟨k0, hk0⟩ := h
        exact le_trans (mul_nonneg (hα k0) (P.v_nonneg k0 j))
          (Finset.le_sup' (fun k => α k * P.v k j) hk0)
      · have : k ≠ i := by rintro rfl; simp at hk
        exact Finset.le_sup' (fun k => α k * P.v k j) (by simp [this])
    · apply Finset.sup'_le
      intro k hk
      have : k ≠ i := Finset.ne_of_mem_erase hk
      exact Finset.le_sup' (smBid P 0 α j) (b := some k) (by simp [this])
  · apply le_antisymm
    · apply Finset.sup'_le
      intro k hk
      rcases k with _ | k
      · simp [smBid]
      · have : k ≠ i := by rintro rfl; simp at hk
        exact absurd ⟨k, by simp [this]⟩ h
    · exact le_trans (hb none) (Finset.le_sup' _ (by simp))

section Lim2

variable {P : PacingGame N G} {ε H : ℕ → ℝ} {M : ℝ} {α : ℕ → N → ℝ} {αs : N → ℝ}
  {xs ps ss : N → G → ℝ}

lemma L_price (hlim : IsSmoothedLimit P ε H M α αs xs ps ss) (i : N) (j : G) :
    ps i j = highestOther P.v αs i j := by
  have ht : Tendsto (fun l => (ε l, α l)) atTop (𝓝 ((0 : ℝ), αs)) :=
    hlim.eps_tendsto.prodMk_nhds hlim.alpha_tendsto
  have h2 := ((smPrice_cont2 P i j).tendsto _).comp ht
  have := tendsto_nhds_unique (hlim.price_tendsto i j) h2
  rw [this]
  exact smPrice_zero_eq P αs (fun k => (L_alphas_mem hlim k).1) i j

lemma L_pay (hlim : IsSmoothedLimit P ε H M α αs xs ps ss) (i : N) (j : G) :
    ss i j = xs i j * ps i j :=
  tendsto_nhds_unique (hlim.pay_tendsto i j)
    ((hlim.alloc_tendsto i j).mul (hlim.price_tendsto i j))

lemma L_budget (hlim : IsSmoothedLimit P ε H M α αs xs ps ss) (i : N) :
    ∑ j, ss i j ≤ P.B i := by
  have ht : Tendsto (fun l => ∑ j, smPay P (ε l) (α l) i j) atTop (𝓝 (∑ j, ss i j)) :=
    tendsto_finsetSum _ fun j _ => hlim.pay_tendsto i j
  refine le_of_tendsto' ht fun l => ?_
  have h1 := (L_cond hlim l i).1
  unfold smSpend at h1
  have := mul_nonneg (L_alpha_mem hlim l i).1 (hlim.eps_pos l).le
  linarith

lemma L_spend_all (hlim : IsSmoothedLimit P ε H M α αs xs ps ss) (i : N) (hi : αs i < 1) :
    ∑ j, ss i j = P.B i := by
  have ht : Tendsto (fun l => ∑ j, smPay P (ε l) (α l) i j) atTop (𝓝 (∑ j, ss i j)) :=
    tendsto_finsetSum _ fun j _ => hlim.pay_tendsto i j
  have hev : ∀ᶠ l in atTop, α l i < 1 := (L_alpha_tendsto hlim i).eventually (gt_mem_nhds hi)
  have ht2 : Tendsto (fun l => P.B i - α l i * ε l) atTop (𝓝 (P.B i - αs i * 0)) :=
    tendsto_const_nhds.sub ((L_alpha_tendsto hlim i).mul hlim.eps_tendsto)
  rw [mul_zero, sub_zero] at ht2
  refine tendsto_nhds_unique ht (ht2.congr' ?_)
  filter_upwards [hev] with l hl
  have := (L_cond hlim l i).2 hl
  unfold smSpend at this
  linarith

lemma L_supply (hlim : IsSmoothedLimit P ε H M α αs xs ps ss) (j : G) :
    ∑ i, xs i j ≤ 1 :=
  le_of_tendsto' (tendsto_finsetSum _ fun i _ => hlim.alloc_tendsto i j)
    fun l => sum_smAlloc_le P (ε l) (hlim.eps_pos l) (α l) j

lemma bid_lt_of_alloc_pos (P : PacingGame N G) (e : ℝ) (a : N → ℝ) (i : N) (j : G)
    (h : 0 < smAlloc P e a i j) (k : Option N) :
    smBid P e a j k < a i * P.v i j + e := by
  have hw : 0 < bandWeight P e a j (some i) := by
    by_contra hw
    push Not at hw
    have : bandWeight P e a j (some i) = 0 := le_antisymm hw (bandWeight_nonneg _ _ _ _ _)
    simp [smAlloc, this] at h
  unfold bandWeight at hw
  have hT := le_topBid P e a j k
  rcases le_total 0 (smBid P e a j (some i) - (topBid P e a j - e)) with h' | h'
  · rw [max_eq_right h'] at hw; simp only [smBid] at hw; linarith
  · rw [max_eq_left h'] at hw; exact absurd hw (lt_irrefl _)

lemma L_winner (hlim : IsSmoothedLimit P ε H M α αs xs ps ss) (i : N) (j : G)
    (hx : 0 < xs i j) (k : N) : αs k * P.v k j ≤ αs i * P.v i j := by
  have hev : ∀ᶠ l in atTop, 0 < smAlloc P (ε l) (α l) i j :=
    (hlim.alloc_tendsto i j).eventually (lt_mem_nhds hx)
  have h1 : Tendsto (fun l => α l k * P.v k j) atTop (𝓝 (αs k * P.v k j)) :=
    (L_alpha_tendsto hlim k).mul_const _
  have h2 : Tendsto (fun l => α l i * P.v i j + ε l) atTop (𝓝 (αs i * P.v i j + 0)) :=
    ((L_alpha_tendsto hlim i).mul_const _).add hlim.eps_tendsto
  rw [add_zero] at h2
  refine le_of_tendsto_of_tendsto h1 h2 ?_
  filter_upwards [hev] with l hl
  exact (bid_lt_of_alloc_pos P (ε l) (α l) i j hl (some k)).le

lemma pay_le_bid (P : PacingGame N G) (e : ℝ) (he : 0 < e) (a : N → ℝ) (i : N) (ha : 0 ≤ a i)
    (j : G) : smPay P e a i j ≤ a i * P.v i j := by
  unfold smPay
  have hb : 0 ≤ a i * P.v i j := mul_nonneg ha (P.v_nonneg i j)
  rcases eq_or_lt_of_le (smAlloc_nonneg P e a i j) with h | h
  · rw [← h, zero_mul]; exact hb
  · have hp := price_le_bid_of_pos P e a i j h
    have h1 := smAlloc_le_one P e he a i j
    have hp0 := eps_le_smPrice P e a i j
    calc smAlloc P e a i j * smPrice P e a i j ≤ 1 * smPrice P e a i j :=
          mul_le_mul_of_nonneg_right h1 (by linarith)
      _ ≤ a i * P.v i j := by linarith

lemma spend_le (P : PacingGame N G) (e M : ℝ) (he : 0 < e) (a : N → ℝ) (i : N) (ha : 0 ≤ a i)
    (hM : ∑ j, P.v i j + 2 * e ≤ M) : smSpend P e a i ≤ a i * M := by
  unfold smSpend
  have h1 : ∑ j, smPay P e a i j ≤ ∑ j, a i * P.v i j :=
    Finset.sum_le_sum fun j _ => pay_le_bid P e he a i ha j
  rw [← Finset.mul_sum] at h1
  have : a i * (e + ∑ j, P.v i j) ≤ a i * M := mul_le_mul_of_nonneg_left (by linarith) ha
  nlinarith

lemma L_alpha_lb (hlim : IsSmoothedLimit P ε H M α αs xs ps ss) (l : ℕ) (i : N) :
    min 1 (P.B i / M) ≤ α l i := by
  have hM := hlim.M_bound l i
  have he := hlim.eps_pos l
  have hM0 : 0 < M := by
    have : 0 ≤ ∑ j, P.v i j := Finset.sum_nonneg fun k _ => P.v_nonneg i k
    linarith
  rcases eq_or_lt_of_le (L_alpha_mem hlim l i).2 with h | h
  · rw [h]; exact min_le_left _ _
  · have hs := (L_cond hlim l i).2 h
    have := spend_le P (ε l) M he (α l) i (L_alpha_mem hlim l i).1 hM
    refine (min_le_right _ _).trans ?_
    rw [div_le_iff₀ hM0]; linarith

lemma L_full (hlim : IsSmoothedLimit P ε H M α αs xs ps ss) (j : G) (hj : ∃ i, 0 < P.v i j) :
    ∑ i, xs i j = 1 := by
  obtain ⟨i, hi⟩ := hj
  have hM0 : 0 < M := by
    have := hlim.M_bound 0 i
    have : 0 ≤ ∑ j, P.v i j := Finset.sum_nonneg fun k _ => P.v_nonneg i k
    linarith [hlim.eps_pos 0]
  have hc : 0 < min 1 (P.B i / M) := lt_min one_pos (div_pos (P.B_pos i) hM0)
  have hαs : min 1 (P.B i / M) ≤ αs i :=
    ge_of_tendsto (L_alpha_tendsto hlim i) (Eventually.of_forall fun l => L_alpha_lb hlim l i)
  have hcpos : 0 < αs i * P.v i j := mul_pos (lt_of_lt_of_le hc hαs) hi
  have h1 : ∀ᶠ l in atTop, αs i * P.v i j / 2 < α l i * P.v i j :=
    ((L_alpha_tendsto hlim i).mul_const (P.v i j)).eventually (lt_mem_nhds (by linarith))
  have h2 : ∀ᶠ l in atTop, ε l < αs i * P.v i j / 6 :=
    hlim.eps_tendsto.eventually (gt_mem_nhds (by linarith))
  have hev : ∀ᶠ l in atTop, ∑ i, smAlloc P (ε l) (α l) i j = 1 := by
    filter_upwards [h1, h2] with l hl1 hl2
    have hT := le_topBid P (ε l) (α l) j (some i)
    simp only [smBid] at hT
    have hw0 : bandWeight P (ε l) (α l) j none = 0 := by
      unfold bandWeight; apply max_eq_left; simp only [smBid]; linarith
    have hD := denom_pos P (ε l) (hlim.eps_pos l) (α l) j
    unfold smAlloc
    rw [← Finset.sum_div, div_eq_one_iff_eq hD.ne', Fintype.sum_option, hw0, zero_add]
  exact tendsto_nhds_unique (tendsto_finsetSum _ fun i _ => hlim.alloc_tendsto i j)
    (tendsto_const_nhds.congr' (hev.mono fun l hl => hl.symm))

end Lim2

end MPX

open MPX in
theorem solution {N G : Type*} [Fintype N] [DecidableEq N] [Fintype G]
    (P : PacingGame N G) (ε H : ℕ → ℝ) (M : ℝ) (α : ℕ → N → ℝ) (αs : N → ℝ)
    (xs ps ss : N → G → ℝ) (hlim : IsSmoothedLimit P ε H M α αs xs ps ss) :
    (∀ i j, ps i j = highestOther P.v αs i j) ∧ (∀ i j, ss i j = xs i j * ps i j) :=
  ⟨L_price hlim, L_pay hlim⟩
