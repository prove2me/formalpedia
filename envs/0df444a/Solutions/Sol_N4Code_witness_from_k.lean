-- Prove2me | solution 1 for N4Code.witness_from_k
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:22:57.675869+00:00
-- url     : https://prove2.me/submissions/30ca355f-37c5-4e7e-a87e-8c53208b6e3b

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
import Theorems.Thm_N4Code_exists_goodWord
import Theorems.Thm_N4Code_colVal_eq_zero_iff_col0
import Theorems.Thm_N4Code_dRow_witness_formula
import Theorems.Thm_N4Code_w_i_eq_card_onesOn


set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000
namespace N4Code
theorem _root_.solution {n : ℕ} (C : Code n) (h07 : Columns07 C) (k : ℕ → ℕ)
    (hcnt0 : 1 ≤ count C 0) (hk0 : k 0 = 1)
    (hk03 : k 1 = 0 ∧ k 2 = 0 ∧ k 3 = 0)
    (hk47 : ∀ i ∈ Finset.Icc 4 7, k i ≤ count C i)
    (hk815 : ∀ i ∈ Finset.Icc 8 15, k i = 0)
    (hmid : 2 * (k 4 + k 5 + k 6 + k 7) =
      count C 4 + count C 5 + count C 6 + count C 7)
    (hge2 : 2 * k 6 + 2 * k 7 ≤ count C 2 + count C 3 + count C 6 + count C 7)
    (hge3 : 2 * k 5 + 2 * k 7 ≤ count C 1 + count C 3 + count C 5 + count C 7) :
    ∃ t : Fin n, C t = col0 ∧ ∃ y : Word n, Y3c C col5 colZeros_col5_nonempty
      colOnes_col5_nonempty t y := by
  have hk : ∀ i ∈ Finset.Icc 0 15, k i ≤ count C i := by
    intro i hi
    have hi7 : i ≤ 15 := (Finset.mem_Icc.mp hi).2
    by_cases hi0 : i = 0
    · rw [hi0, hk0]
      omega
    · by_cases hi47 : i ∈ Finset.Icc 4 7
      · exact hk47 i hi47
      · -- i ∈ 1..3 or 8..15: k i = 0
        have hk0' : k i = 0 := by
          rcases hk03 with ⟨h1, h2, h3⟩
          by_cases hi1 : i = 1
          · subst i
            exact h1
          · by_cases hi2 : i = 2
            · subst i
              exact h2
            · by_cases hi3 : i = 3
              · subst i
                exact h3
              · have h8 : 8 ≤ i := by
                  simp [Finset.mem_Icc] at hi47
                  omega
                exact hk815 i (by simp [Finset.mem_Icc, h8, hi7])
        omega
  rcases exists_goodWord C k hk with ⟨y, hy⟩
  have hw0 : w_i C 0 y = 1 := by
    rw [← hk0]
    exact hy 0 (by simp [Finset.mem_Icc])
  have hw1 : w_i C 1 y = 0 := by
    rw [← hk03.1]
    exact hy 1 (by simp [Finset.mem_Icc])
  have hw2 : w_i C 2 y = 0 := by
    rw [← hk03.2.1]
    exact hy 2 (by simp [Finset.mem_Icc])
  have hw3 : w_i C 3 y = 0 := by
    rw [← hk03.2.2]
    exact hy 3 (by simp [Finset.mem_Icc])
  have hw47 : ∀ i ∈ Finset.Icc 4 7, w_i C i y = k i := by
    intro i hi
    exact hy i (by simp [Finset.mem_Icc] at hi ⊢; omega)
  have hw815 : ∀ i ∈ Finset.Icc 8 15, w_i C i y = 0 := by
    intro i hi
    have : k i = 0 := hk815 i hi
    rw [← this]
    exact hy i (by simp [Finset.mem_Icc] at hi ⊢; omega)
  have hform := dRow_witness_formula C y h07 ⟨hw1, hw2, hw3⟩ hw815
  rcases hform with ⟨hd0, hd1, hd2, hd3⟩
  have hw0card : (onesOn (fiber C 0) y).card = 1 := by
    rw [← w_i_eq_card_onesOn, hw0]
  rcases Finset.card_pos.mp (by omega : 0 < (onesOn (fiber C 0) y).card) with ⟨t, ht⟩
  have htmem : t ∈ onesOn (fiber C 0) y := ht
  have ht0 : C t = col0 := by
    have hf : t ∈ fiber C 0 := (Finset.mem_filter.mp htmem).1
    have hcv : colVal (C t) = 0 := (Finset.mem_filter.mp hf).2
    exact (colVal_eq_zero_iff_col0 (C t)).mp hcv
  have hyt : y t = true := (Finset.mem_filter.mp htmem).2
  have hb4 : k 4 ≤ count C 4 := hk47 4 (by simp)
  have hb5 : k 5 ≤ count C 5 := hk47 5 (by simp)
  have hb6 : k 6 ≤ count C 6 := hk47 6 (by simp)
  have hb7 : k 7 ≤ count C 7 := hk47 7 (by simp)
  have htwo : 2 * (k 4 + k 5 + k 6 + k 7) = count C 4 + count C 5 + count C 6 + count C 7 := hmid
  have hd12 : dRow C 0 y = dRow C 1 y := by
    rw [hd0, hd1]
    simp [hw0, hw47 4 (by simp), hw47 5 (by simp), hw47 6 (by simp), hw47 7 (by simp)]
    omega
  have hd12' : dRow C 0 y ≤ dRow C 2 y := by
    rw [hd0, hd2]
    simp [hw0, hw47 4 (by simp), hw47 5 (by simp), hw47 6 (by simp), hw47 7 (by simp)]
    omega
  have hd13' : dRow C 0 y ≤ dRow C 3 y := by
    rw [hd0, hd3]
    simp [hw0, hw47 4 (by simp), hw47 5 (by simp), hw47 6 (by simp), hw47 7 (by simp)]
    omega
  have hd1le3 : dRow C 1 y ≤ dRow C 3 y := by
    rw [← hd12]
    exact hd13'
  have hz : (colZeros col5) = ({⟨0, by decide⟩, ⟨2, by decide⟩} : Finset (Fin 4)) := by
    ext i
    fin_cases i <;> simp [colZeros, col5]
  have hp : (colOnes col5) = ({⟨1, by decide⟩, ⟨3, by decide⟩} : Finset (Fin 4)) := by
    ext i
    fin_cases i <;> simp [colOnes, col5]
  have hdO : dOc C col5 colZeros_col5_nonempty y = dRow C 0 y := by
    unfold dOc dRowMin
    have hmin : ({dRow C 0 y, dRow C 2 y} : Finset ℕ).min' (by simp) =
        min (dRow C 0 y) (dRow C 2 y) := by
      apply le_antisymm
      · apply le_min
        · exact Finset.min'_le ({dRow C 0 y, dRow C 2 y} : Finset ℕ) (dRow C 0 y) (by simp)
        · exact Finset.min'_le ({dRow C 0 y, dRow C 2 y} : Finset ℕ) (dRow C 2 y) (by simp)
      · apply Finset.le_min'
        intro z hz
        simp at hz
        rcases hz with rfl | rfl
        · exact min_le_left _ _
        · exact min_le_right _ _
    simp [hz, hmin, min_eq_left hd12']
  have hdP : dPc C col5 colOnes_col5_nonempty y = dRow C 1 y := by
    unfold dPc dRowMin
    have hmin : ({dRow C 1 y, dRow C 3 y} : Finset ℕ).min' (by simp) =
        min (dRow C 1 y) (dRow C 3 y) := by
      apply le_antisymm
      · apply le_min
        · exact Finset.min'_le ({dRow C 1 y, dRow C 3 y} : Finset ℕ) (dRow C 1 y) (by simp)
        · exact Finset.min'_le ({dRow C 1 y, dRow C 3 y} : Finset ℕ) (dRow C 3 y) (by simp)
      · apply Finset.le_min'
        intro z hz
        simp at hz
        rcases hz with rfl | rfl
        · exact min_le_left _ _
        · exact min_le_right _ _
    simp [hp, hmin, min_eq_left hd1le3]
  refine ⟨t, ht0, y, ?_⟩
  unfold Y3c
  exact ⟨hyt, by rw [hdO, hdP, hd12]⟩
end N4Code
