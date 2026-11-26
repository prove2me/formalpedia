-- Prove2me | solution 1 for N4Code.exists_goodWord_fixed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:28:02.465691+00:00
-- url     : https://prove2.me/submissions/833fcc54-3457-4ff5-b38b-7013ce8cbf80

import Definitions.Def_N4Code_ZeroColumn
import Definitions.Def_N4Code_TwoColumn
import Theorems.Thm_N4Code_pickSubset_mem
import Theorems.Thm_N4Code_pickSubset_subset
import Theorems.Thm_N4Code_pickSubset_card
import Theorems.Thm_N4Code_fiber_card_eq_count
import Theorems.Thm_N4Code_onesOn_tupleWord
import Theorems.Thm_N4Code_w_i_eq_card_onesOn


set_option autoImplicit true
open N4Code
set_option maxRecDepth 1000000
open scoped BigOperators
namespace N4Code
theorem _root_.solution {n : ℕ} (C : Code n) (k : ℕ → ℕ) (t₁ t₂ : Fin n)
    (ht1 : colVal (C t₁) = 1) (ht2 : colVal (C t₂) = 7)
    (hk1 : 1 ≤ k 1) (hk7 : k 7 + 1 ≤ count C 7)
    (hk : ∀ i ∈ Finset.Icc 0 15, k i ≤ count C i) :
    ∃ y : Word n, y t₁ = true ∧ y t₂ = false ∧ ∀ i ∈ Finset.Icc 0 15, w_i C i y = k i := by
  have hf1 : t₁ ∈ fiber C 1 := by simp [fiber, ht1]
  have hf7 : t₂ ∈ fiber C 7 := by simp [fiber, ht2]
  have hk1le : k 1 - 1 ≤ ((fiber C 1).erase t₁).card := by
    have h1' : (fiber C 1).card = count C 1 := fiber_card_eq_count C 1
    have hcard : ((fiber C 1).erase t₁).card = count C 1 - 1 := by
      rw [Finset.card_erase_of_mem hf1, h1']
    have hk1' : k 1 ≤ count C 1 := hk 1 (by simp)
    omega
  have hk7le : k 7 ≤ ((fiber C 7).erase t₂).card := by
    have h7' : (fiber C 7).card = count C 7 := fiber_card_eq_count C 7
    have hcard : ((fiber C 7).erase t₂).card = count C 7 - 1 := by
      rw [Finset.card_erase_of_mem hf7, h7']
    omega
  let g : Fin 16 → Finset (Fin n) := fun a =>
    if h1a : a.val = 1 then
      insert t₁ (pickSubset ((fiber C 1).erase t₁) (k 1 - 1) hk1le)
    else if h7a : a.val = 7 then
      pickSubset ((fiber C 7).erase t₂) (k 7) hk7le
    else
      pickSubset (fiber C a.val) (k a.val) (by
        have hle := hk a.val (by
          have : a.val ≤ 15 := Nat.le_of_lt_succ a.isLt
          simp [Finset.mem_Icc, this])
        rw [fiber_card_eq_count]
        exact hle)
  let y : Word n := tupleWord C g
  have hg1 : g ⟨1, by decide⟩ =
      insert t₁ (pickSubset ((fiber C 1).erase t₁) (k 1 - 1) hk1le) := by
    simp [g]
  have hg7 : g ⟨7, by decide⟩ = pickSubset ((fiber C 7).erase t₂) (k 7) hk7le := by
    simp [g]
  have hg : GoodTuplePred C k g := by
    intro a
    by_cases ha1 : a.val = 1
    · have hg' : g a = insert t₁ (pickSubset ((fiber C 1).erase t₁) (k 1 - 1) hk1le) := by
        simp [g, ha1]
      rw [hg', ha1]
      rw [Finset.mem_powersetCard]
      refine ⟨?_, ?_⟩
      · intro u hu
        rw [Finset.mem_insert] at hu
        rcases hu with rfl | hu
        · exact hf1
        · have hsub := pickSubset_subset hk1le
          have : u ∈ (fiber C 1).erase t₁ := hsub hu
          exact (Finset.mem_erase.mp this).2
      · have hPcard : (pickSubset ((fiber C 1).erase t₁) (k 1 - 1) hk1le).card = k 1 - 1 :=
          pickSubset_card hk1le
        have ht1' : t₁ ∉ pickSubset ((fiber C 1).erase t₁) (k 1 - 1) hk1le := by
          intro h
          have hsub := pickSubset_subset hk1le
          have : t₁ ∈ (fiber C 1).erase t₁ := hsub h
          exact (Finset.mem_erase.mp this).1 rfl
        rw [Finset.card_insert_of_notMem ht1', hPcard]
        omega
    · by_cases ha7 : a.val = 7
      · have hg' : g a = pickSubset ((fiber C 7).erase t₂) (k 7) hk7le := by
          simp [g, ha7]
        rw [hg', ha7]
        have hsub : pickSubset ((fiber C 7).erase t₂) (k 7) hk7le ⊆ (fiber C 7).erase t₂ :=
          pickSubset_subset hk7le
        rw [Finset.mem_powersetCard]
        refine ⟨?_, ?_⟩
        · intro u hu
          exact (Finset.mem_erase.mp (hsub hu)).2
        · exact pickSubset_card hk7le
      · have hg' : g a = pickSubset (fiber C a.val) (k a.val)
          (by
            have hle := hk a.val (by
              have : a.val ≤ 15 := Nat.le_of_lt_succ a.isLt
              simp [Finset.mem_Icc, this])
            rw [fiber_card_eq_count]
            exact hle) := by
          simp [g, ha1, ha7]
        rw [hg']
        exact pickSubset_mem
          (by
            have hle := hk a.val (by
              have : a.val ≤ 15 := Nat.le_of_lt_succ a.isLt
              simp [Finset.mem_Icc, this])
            rw [fiber_card_eq_count]
            exact hle)
  have hy1 : y t₁ = true := by
    unfold y
    simp [tupleWord]
    have h : t₁ ∈ g ⟨colVal (C t₁), Nat.lt_succ_of_le (colVal_le_15 (C t₁))⟩ := by
      have hg1' : g ⟨colVal (C t₁), Nat.lt_succ_of_le (colVal_le_15 (C t₁))⟩ =
          insert t₁ (pickSubset ((fiber C 1).erase t₁) (k 1 - 1) hk1le) := by
        simpa [ht1] using hg1
      rw [hg1']
      exact Finset.mem_insert_self t₁ _
    exact h
  have hy2 : y t₂ = false := by
    unfold y
    simp [tupleWord]
    intro h
    have hg7' : g ⟨colVal (C t₂), Nat.lt_succ_of_le (colVal_le_15 (C t₂))⟩ =
        pickSubset ((fiber C 7).erase t₂) (k 7) hk7le := by
      simpa [ht2] using hg7
    rw [hg7'] at h
    have hsub := pickSubset_subset hk7le
    have : t₂ ∈ (fiber C 7).erase t₂ := hsub h
    exact (Finset.mem_erase.mp this).1 rfl
  have hw : ∀ i ∈ Finset.Icc 0 15, w_i C i y = k i := by
    intro i hi
    have hones := onesOn_tupleWord C k g hg hi
    rw [w_i_eq_card_onesOn]
    rw [hones]
    have hi' : i < 16 := by
      have : i ≤ 15 := (Finset.mem_Icc.mp hi).2
      omega
    by_cases hi1 : i = 1
    · subst i
      rw [hg1]
      have hPcard : (pickSubset ((fiber C 1).erase t₁) (k 1 - 1) hk1le).card = k 1 - 1 :=
        pickSubset_card hk1le
      have ht1' : t₁ ∉ pickSubset ((fiber C 1).erase t₁) (k 1 - 1) hk1le := by
        intro h
        have hsub := pickSubset_subset hk1le
        have : t₁ ∈ (fiber C 1).erase t₁ := hsub h
        exact (Finset.mem_erase.mp this).1 rfl
      rw [Finset.card_insert_of_notMem ht1', hPcard]
      omega
    · by_cases hi7 : i = 7
      · subst i
        rw [hg7]
        exact pickSubset_card hk7le
      · have hg' : g ⟨i, hi'⟩ = pickSubset (fiber C i) (k i)
            (by
              have hle := hk i hi
              rw [fiber_card_eq_count]
              exact hle) := by
          simp [g, hi1, hi7]
        rw [hg']
        exact pickSubset_card
          (by
            have hle := hk i hi
            rw [fiber_card_eq_count]
            exact hle)
  exact ⟨y, hy1, hy2, hw⟩
end N4Code
