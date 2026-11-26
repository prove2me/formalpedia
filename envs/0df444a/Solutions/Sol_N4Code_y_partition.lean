-- Prove2me | solution 1 for N4Code.y_partition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:29:52.622848+00:00
-- url     : https://prove2.me/submissions/1f764e14-b897-4ded-8e7c-f0fc1b9c8c6a

import Definitions.Def_N4Code_Comparison
import Mathlib.Tactic.FieldSimp
import Definitions.Def_N4Code_Compare
import Theorems.Thm_N4Code_Y1_or_Y4_or_Y5_iff
import Theorems.Thm_N4Code_Y2_or_Y3_iff
import Theorems.Thm_N4Code_Y1_Y4_disjoint
import Theorems.Thm_N4Code_Y1_Y5_disjoint
import Theorems.Thm_N4Code_Y4_Y5_disjoint
import Theorems.Thm_N4Code_Y2_Y3_disjoint

set_option autoImplicit true
open N4Code
namespace N4Code
theorem _root_.solution {n : ℕ} (C _C' : Code n) (t : Fin n) :
    ∀ y : Word n, ∃! i : Fin 5, YSet C t i y := by
  intro y
  by_cases h : dO C y ≤ min (dP C y) (dPp C t y)
  · have hnot23 : ¬ (Y2 C t y ∨ Y3 C t y) := by
      intro h23
      have hgt : min (dP C y) (dPp C t y) < dO C y := (Y2_or_Y3_iff C t y).mp h23
      omega
    rcases (Y1_or_Y4_or_Y5_iff C t y).mpr h with hy | hy | hy
    · refine ⟨⟨0, by decide⟩, ?_, ?_⟩
      · simp [YSet, hy]
      · intro j hj
        fin_cases j
        · rfl
        · exfalso
          exact hnot23 (Or.inl (by simpa [YSet] using hj))
        · exfalso
          exact hnot23 (Or.inr (by simpa [YSet] using hj))
        · exfalso
          exact Y1_Y4_disjoint C t y ⟨hy, by simpa [YSet] using hj⟩
        · exfalso
          exact Y1_Y5_disjoint C t y ⟨hy, by simpa [YSet] using hj⟩
    · refine ⟨⟨3, by decide⟩, ?_, ?_⟩
      · simp [YSet, hy]
      · intro j hj
        fin_cases j
        · exfalso
          exact Y1_Y4_disjoint C t y ⟨by simpa [YSet] using hj, hy⟩
        · exfalso
          exact hnot23 (Or.inl (by simpa [YSet] using hj))
        · exfalso
          exact hnot23 (Or.inr (by simpa [YSet] using hj))
        · rfl
        · exfalso
          exact Y4_Y5_disjoint C t y ⟨hy, by simpa [YSet] using hj⟩
    · refine ⟨⟨4, by decide⟩, ?_, ?_⟩
      · simp [YSet, hy]
      · intro j hj
        fin_cases j
        · exfalso
          exact Y1_Y5_disjoint C t y ⟨by simpa [YSet] using hj, hy⟩
        · exfalso
          exact hnot23 (Or.inl (by simpa [YSet] using hj))
        · exfalso
          exact hnot23 (Or.inr (by simpa [YSet] using hj))
        · exfalso
          exact Y4_Y5_disjoint C t y ⟨by simpa [YSet] using hj, hy⟩
        · rfl
  · have hgt : min (dP C y) (dPp C t y) < dO C y := lt_of_not_ge h
    have hnotA : ¬ (Y1 C t y ∨ Y4 C t y ∨ Y5 C t y) := by
      intro hA'
      exact (lt_irrefl (dO C y))
        (lt_of_le_of_lt ((Y1_or_Y4_or_Y5_iff C t y).mp hA') hgt)
    rcases (Y2_or_Y3_iff C t y).mpr hgt with hy | hy
    · refine ⟨⟨1, by decide⟩, ?_, ?_⟩
      · simp [YSet, hy]
      · intro j hj
        fin_cases j
        · exfalso
          exact hnotA (Or.inl (by simpa [YSet] using hj))
        · rfl
        · exfalso
          exact Y2_Y3_disjoint C t y ⟨hy, by simpa [YSet] using hj⟩
        · exfalso
          exact hnotA (Or.inr (Or.inl (by simpa [YSet] using hj)))
        · exfalso
          exact hnotA (Or.inr (Or.inr (by simpa [YSet] using hj)))
    · refine ⟨⟨2, by decide⟩, ?_, ?_⟩
      · simp [YSet, hy]
      · intro j hj
        fin_cases j
        · exfalso
          exact hnotA (Or.inl (by simpa [YSet] using hj))
        · exfalso
          exact Y2_Y3_disjoint C t y ⟨by simpa [YSet] using hj, hy⟩
        · rfl
        · exfalso
          exact hnotA (Or.inr (Or.inl (by simpa [YSet] using hj)))
        · exfalso
          exact hnotA (Or.inr (Or.inr (by simpa [YSet] using hj)))
end N4Code
