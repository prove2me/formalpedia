-- Prove2me | solution 1 for JohnsonApprox.SetCover.lemma2_selectable_card_le
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T18:41:52.826997+00:00
-- url     : https://prove2.me/submissions/4012c931-c3a6-4cbf-9d06-4f727efea618

import Mathlib
import Definitions.Def_JohnsonApprox_SetCover_Problem
import Definitions.Def_JohnsonApprox_SetCover_Config



namespace JohnsonApprox.SetCover

open Finset

lemma harmonic_sub_ge (a b : ℕ) (hba : b ≤ a) (ha : 0 < a) :
    ((a : ℚ) - b) / a ≤ harmonic a - harmonic b := by
  unfold harmonic
  rw [← Finset.sum_range_add_sum_Ico _ hba, add_sub_cancel_left]
  have : ∑ _i ∈ Ico b a, (1 / (a : ℚ)) ≤ ∑ i ∈ Ico b a, ((↑(i + 1) : ℚ))⁻¹ := by
    apply sum_le_sum
    intro i hi
    rw [mem_Ico] at hi
    rw [one_div]
    apply inv_anti₀ (by positivity)
    exact_mod_cast (by omega : i + 1 ≤ a)
  rw [sum_const, Nat.card_Ico, nsmul_eq_mul] at this
  rw [Nat.cast_sub hba] at this
  calc ((a : ℚ) - b) / a = ((a : ℚ) - b) * (1 / a) := by ring
    _ ≤ _ := this

lemma harmonic_nonneg' (n : ℕ) : 0 ≤ harmonic n := by
  unfold harmonic; exact sum_nonneg (fun i _ => by positivity)

lemma harmonic_mono' {a b : ℕ} (h : a ≤ b) : harmonic a ≤ harmonic b := by
  unfold harmonic
  exact sum_le_sum_of_subset_of_nonneg (range_mono h) (fun i _ _ => by positivity)

variable {ι α : Type} [Fintype ι] [DecidableEq α]

theorem lemma2_core [DecidableEq ι]
    (K : Config ι α) (M1 M0 : Finset ι)
    (h1 : Selectable K M1) (h0 : M0.biUnion K.SET = K.UNCOV) :
    (M1.card : ℚ) ≤ ∑ i ∈ M0, harmonic (K.SET i).card := by
  obtain ⟨js, hrun, rfl⟩ := h1
  induction hrun generalizing M0 with
  | halt K _ =>
    simp only [List.toFinset_nil, card_empty, Nat.cast_zero]
    exact sum_nonneg (fun i _ => harmonic_nonneg' _)
  | step K j K' js hstep hrun' ih =>
    obtain ⟨hne, hmax, hU, hS⟩ := hstep
    have h0' : M0.biUnion K'.SET = K'.UNCOV := by
      rw [hS, hU, ← h0]
      ext x; simp only [mem_biUnion, mem_sdiff]
      constructor
      · rintro ⟨i, hi, hx, hxj⟩; exact ⟨⟨i, hi, hx⟩, hxj⟩
      · rintro ⟨⟨i, hi, hx⟩, hxj⟩; exact ⟨i, hi, hx, hxj⟩
    have hIH := ih M0 h0'
    -- the chosen set is nonempty
    set m := (K.SET j).card with hm
    have hm1 : 1 ≤ m := by
      obtain ⟨u, hu⟩ := nonempty_iff_ne_empty.2 hne
      rw [← K.union_eq, mem_biUnion] at hu
      obtain ⟨i, _, hui⟩ := hu
      have := hmax i
      have : 0 < (K.SET i).card := card_pos.2 ⟨u, hui⟩
      omega
    -- charging
    have hcharge : ∀ i, ((K.SET i ∩ K.SET j).card : ℚ) / m ≤
        harmonic (K.SET i).card - harmonic (K'.SET i).card := by
      intro i
      have hsd : (K'.SET i) = K.SET i \ K.SET j := by rw [hS]
      have hcard : (K'.SET i).card = (K.SET i).card - (K.SET i ∩ K.SET j).card := by
        have := card_sdiff_add_card_inter (K.SET i) (K.SET j)
        rw [hsd]; omega
      have hle : (K'.SET i).card ≤ (K.SET i).card := by rw [hsd]; exact card_le_card sdiff_subset
      rcases Nat.eq_zero_or_pos (K.SET i).card with h0i | hposi
      · have : (K.SET i ∩ K.SET j).card = 0 := by
          have := card_le_card (inter_subset_left : K.SET i ∩ K.SET j ⊆ K.SET i); omega
        have h0' : (K'.SET i).card = 0 := by omega
        rw [this, h0i, h0']; simp
      · have h1 := harmonic_sub_ge _ _ hle hposi
        have h2 : ((K.SET i ∩ K.SET j).card : ℚ) = (K.SET i).card - (K'.SET i).card := by
          rw [hcard, Nat.cast_sub (card_le_card inter_subset_left)]; ring
        rw [h2]
        refine le_trans ?_ h1
        apply div_le_div_of_nonneg_left
        · rw [sub_nonneg]; exact_mod_cast hle
        · exact_mod_cast hposi
        · exact_mod_cast hmax i
    have hcover : m ≤ ∑ i ∈ M0, (K.SET i ∩ K.SET j).card := by
      have hsub : K.SET j ⊆ M0.biUnion (fun i => K.SET i ∩ K.SET j) := by
        intro x hx
        have hxU : x ∈ K.UNCOV := by rw [← K.union_eq]; exact mem_biUnion.2 ⟨j, mem_univ _, hx⟩
        rw [← h0, mem_biUnion] at hxU
        obtain ⟨i, hi, hxi⟩ := hxU
        exact mem_biUnion.2 ⟨i, hi, mem_inter.2 ⟨hxi, hx⟩⟩
      exact (card_le_card hsub).trans card_biUnion_le
    have hsum1 : (1 : ℚ) ≤ ∑ i ∈ M0, (harmonic (K.SET i).card - harmonic (K'.SET i).card) := by
      calc (1 : ℚ) = (m : ℚ) / m := by rw [div_self]; exact_mod_cast (by omega : m ≠ 0)
        _ ≤ (∑ i ∈ M0, ((K.SET i ∩ K.SET j).card : ℚ)) / m := by
            apply div_le_div_of_nonneg_right _ (by positivity)
            exact_mod_cast hcover
        _ = ∑ i ∈ M0, ((K.SET i ∩ K.SET j).card : ℚ) / m := by rw [sum_div]
        _ ≤ _ := sum_le_sum (fun i _ => hcharge i)
    rw [sum_sub_distrib] at hsum1
    have hins : ((j :: js).toFinset.card : ℚ) ≤ (js.toFinset.card : ℚ) + 1 := by
      rw [List.toFinset_cons]
      exact_mod_cast card_insert_le _ _
    linarith

end JohnsonApprox.SetCover

open JohnsonApprox.SetCover

theorem solution {ι α : Type} [Fintype ι] [DecidableEq ι] [DecidableEq α]
    (K : Config ι α) (M1 M0 : Finset ι)
    (h1 : Selectable K M1) (h0 : M0.biUnion K.SET = K.UNCOV) :
    (M1.card : ℚ) ≤ ∑ i ∈ M0, harmonic (K.SET i).card := by
  exact lemma2_core K M1 M0 h1 h0
