-- Prove2me | solution 1 for LostSalesOldNew.StateReduction.vectorBaseStock_mem_Zs
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T06:53:42.489882+00:00
-- url     : https://prove2.me/submissions/dafcc9e7-7e61-4b95-9f24-bfef4560e971

import Mathlib
import Definitions.Def_LostSalesOldNew_StateReduction_Model

set_option autoImplicit false
open LostSalesOldNew.StateReduction

theorem solution {L : ℕ} (hL : 0 < L)
    (s : Fin (L + 1) → ℝ) (hs : IsLevelVector s) :
    vectorBaseStock s ∈ Zs s := by
  have hle : ∀ (x : Fin L → ℝ) (l : Fin (L + 1)),
      Finset.univ.inf' Finset.univ_nonempty (fun l : Fin (L + 1) => s l - v x l) ≤ s l - v x l :=
    fun x l => Finset.inf'_le _ (Finset.mem_univ l)
  refine ⟨?_, ?_, ?_⟩
  · intro x _
    exact le_max_right _ _
  · intro x hx0 hx
    unfold vectorBaseStock
    have : ∃ l : Fin L, s l.castSucc < v x l := by
      by_contra hcon
      push_neg at hcon
      exact hx ⟨hx0, hcon⟩
    obtain ⟨l, hl⟩ := this
    have h1 := hle x l.castSucc
    simp only [Fin.val_castSucc] at h1
    exact max_eq_right (by linarith)
  · intro x hx l
    unfold vectorBaseStock
    have h1 := hle x l
    have hvl : v x l ≤ s l := by
      by_cases hl : (l : ℕ) < L
      · have := hx.2 ⟨l, hl⟩
        simpa using this
      · have hlL : (l : ℕ) = L := by omega
        have hv0 : v x l = 0 := by
          unfold v
          apply Finset.sum_eq_zero
          intro m _
          have := m.isLt
          rw [if_neg (by omega)]
        have hlast : l = Fin.last L := Fin.ext hlL
        rw [hv0, hlast]
        exact hs.2
    rcases le_total 0 (Finset.univ.inf' Finset.univ_nonempty (fun l : Fin (L + 1) => s l - v x l)) with h | h
    · rw [max_eq_left h]; linarith
    · rw [max_eq_right h]; linarith
