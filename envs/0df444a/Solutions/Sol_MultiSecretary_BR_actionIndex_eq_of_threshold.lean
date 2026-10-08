-- Prove2me | solution 1 for MultiSecretary.BR.actionIndex_eq_of_threshold
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T03:37:00.536702+00:00
-- url     : https://prove2.me/submissions/22008da0-cee7-43be-8d8f-002b7a2c49f8

import Mathlib
import Definitions.Def_MultiSecretary_BR_Model

set_option autoImplicit false

open MultiSecretary.BR Finset in
theorem MSBR_00d9e080_surv_add_le {m : ℕ} (I : Instance m) (i i' : Fin m) (h : i < i') :
    I.survival i + I.f i ≤ I.survival i' := by
  unfold Instance.survival
  have hsub : insert i (univ.filter (fun l => l < i)) ⊆ univ.filter (fun l => l < i') := by
    intro l hl
    simp only [mem_insert, mem_filter, mem_univ, true_and] at hl ⊢
    rcases hl with rfl | hl
    · exact h
    · exact lt_trans hl h
  have hni : i ∉ univ.filter (fun l => l < i) := by simp
  have := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun l _ _ => (I.f_pos l).le)
  rw [Finset.sum_insert hni] at this
  linarith

open MultiSecretary.BR Finset in
theorem MSBR_00d9e080_g_mono {m : ℕ} (I : Instance m) (i i' : Fin m) (h : i ≤ i') :
    I.survival i + I.f i / 2 ≤ I.survival i' + I.f i' / 2 := by
  rcases h.lt_or_eq with h | h
  · have := MSBR_00d9e080_surv_add_le I i i' h
    have h1 := I.f_pos i
    have h2 := I.f_pos i'
    linarith
  · rw [h]

open MultiSecretary.BR Finset in
theorem solution {m : ℕ} (I : Instance m) (n k : ℕ) (hk : k ≤ n) (hn : 0 < n)
    (j : Fin m) (hlo : I.T j ≤ (k : ℝ) / n)
    (hhi : ∀ h : j.val + 1 < m, (k : ℝ) / n < I.T ⟨j.val + 1, h⟩) :
    I.actionIndex n k = j := by
  -- every element of the filter set is ≤ j
  have hle : ∀ i ∈ univ.filter (fun i : Fin m => I.survival i + I.f i / 2 ≤ (k : ℝ) / n),
      i ≤ j := by
    intro i hi
    simp only [mem_filter, mem_univ, true_and] at hi
    by_contra hcon
    rw [not_le] at hcon
    have hj1 : j.val + 1 < m := lt_of_le_of_lt (Nat.succ_le_of_lt hcon) i.isLt
    have hT := hhi hj1
    unfold Instance.T at hT
    simp only [Nat.add_one_ne_zero, if_false] at hT
    have hmono := MSBR_00d9e080_g_mono I ⟨j.val + 1, hj1⟩ i
      (by rw [Fin.le_def]; exact Nat.succ_le_of_lt hcon)
    linarith
  unfold Instance.actionIndex
  split_ifs with hne
  · apply le_antisymm
    · exact Finset.max'_le _ _ _ hle
    · by_cases hj0 : j.val = 0
      · rw [Fin.le_def, hj0]; exact Nat.zero_le _
      · apply Finset.le_max'
        simp only [mem_filter, mem_univ, true_and]
        unfold Instance.T at hlo
        simpa [hj0] using hlo
  · -- empty: j must be 0
    by_contra hcon
    have hj0 : j.val ≠ 0 := by
      intro h0; apply hcon; unfold Instance.top; exact Fin.ext h0.symm
    apply hne
    refine ⟨j, ?_⟩
    simp only [mem_filter, mem_univ, true_and]
    unfold Instance.T at hlo
    simpa [hj0] using hlo
