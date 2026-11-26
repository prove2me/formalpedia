-- Prove2me | solution 1 for N4Code.Y2_or_Y3_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:05:59.537797+00:00
-- url     : https://prove2.me/submissions/8835f2ad-93f3-4ded-bab5-1c4a33dd1fa5

import Definitions.Def_N4Code_Comparison
import Mathlib.Tactic.FieldSimp
import Definitions.Def_N4Code_Compare
import Theorems.Thm_N4Code_dOp_le_dO_add_one
import Theorems.Thm_N4Code_dPp_le_dP_add_one

set_option autoImplicit true
open N4Code
namespace N4Code
theorem _root_.solution {n : ℕ} (C : Code n) (t : Fin n) (y : Word n) :
    (Y2 C t y ∨ Y3 C t y) ↔ dO C y > min (dP C y) (dPp C t y) := by
  have h1 := dOp_le_dO_add_one C t y
  have h2 := dO_le_dOp_add_one C t y
  have h3 := dPp_le_dP_add_one C t y
  have h4 := dP_le_dPp_add_one C t y
  constructor
  · intro hy
    rcases hy with hy | hy
    · rcases hy with hy | hy
      · rcases hy with ⟨ha, hb⟩
        rw [min_eq_left ha]
        exact hb
      · rcases hy with ⟨ha, hb, hc⟩
        rw [min_eq_right (le_of_lt ha)]
        omega
    · rcases hy with ⟨ha, hb, hc⟩
      rw [min_eq_right (le_of_lt hb)]
      exact lt_of_lt_of_eq hb hc
  · intro h
    have hgt : min (dP C y) (dPp C t y) < dO C y := h
    by_cases hcmp : dP C y < dPp C t y
    · have hdP : dP C y < dO C y := by
        rw [min_eq_left (le_of_lt hcmp)] at hgt
        exact hgt
      exact Or.inl (Or.inl ⟨le_of_lt hcmp, hdP⟩)
    · have hdPp_le : dPp C t y ≤ dP C y := le_of_not_gt hcmp
      by_cases heq : dPp C t y = dP C y
      · have hdP : dP C y < dO C y := by
          rw [heq] at hgt
          simpa using hgt
        exact Or.inl (Or.inl ⟨le_of_eq heq.symm, hdP⟩)
      · have hdPp_lt : dPp C t y < dP C y := lt_of_le_of_ne hdPp_le heq
        have hdPp_lt_dO : dPp C t y < dO C y := by
          rw [min_eq_right (le_of_lt hdPp_lt)] at hgt
          exact hgt
        by_cases hop : dOp C t y ≤ dPp C t y
        · have hdOp_eq : dOp C t y = dPp C t y := by omega
          have hdP_eq : dP C y = dO C y := by omega
          exact Or.inr ⟨hdOp_eq.symm, hdPp_lt, hdP_eq⟩
        · have hdP_le_dO : dP C y ≤ dO C y := by omega
          have hdP_le_dOp : dP C y ≤ dOp C t y := by omega
          exact Or.inl (Or.inr ⟨hdPp_lt, hdP_le_dO, hdP_le_dOp⟩)
end N4Code
