-- Prove2me | solution 1 for N4Code.Y1_or_Y4_or_Y5_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:05:59.076704+00:00
-- url     : https://prove2.me/submissions/034bf7bc-8589-4534-bb0e-2e3e4b51d326

import Definitions.Def_N4Code_Comparison
import Mathlib.Tactic.FieldSimp
import Definitions.Def_N4Code_Compare
import Theorems.Thm_N4Code_dOp_le_dO_add_one
import Theorems.Thm_N4Code_dPp_le_dP_add_one

set_option autoImplicit true
open N4Code
namespace N4Code
theorem _root_.solution {n : ℕ} (C : Code n) (t : Fin n) (y : Word n) :
    (Y1 C t y ∨ Y4 C t y ∨ Y5 C t y) ↔ dO C y ≤ min (dP C y) (dPp C t y) := by
  have h1 := dOp_le_dO_add_one C t y
  have h2 := dO_le_dOp_add_one C t y
  have h3 := dPp_le_dP_add_one C t y
  have h4 := dP_le_dPp_add_one C t y
  constructor
  · intro hy
    rcases hy with hy | hy | hy
    · rcases hy with hy | hy
      · rcases hy with ⟨ha, hb⟩
        exact le_min ha (le_trans ha (le_of_lt hb))
      · rcases hy with ⟨ha, hb, hc⟩
        exact le_min (le_trans ha hb) ha
    · rcases hy with ⟨ha, hb, hc⟩
      exact le_min (le_of_eq (hb.symm.trans ha.symm)) (le_of_eq hb.symm)
    · rcases hy with ⟨ha, hb, hc⟩
      exact le_min (le_of_lt (lt_of_lt_of_eq hc hb)) (le_of_eq ha.symm)
  · intro h
    have hdP : dO C y ≤ dP C y := (le_min_iff.mp h).1
    have hdPp : dO C y ≤ dPp C t y := (le_min_iff.mp h).2
    by_cases hcmp : dP C y < dPp C t y
    · exact Or.inl (Or.inl ⟨hdP, hcmp⟩)
    · have hdPp_le : dPp C t y ≤ dP C y := le_of_not_gt hcmp
      by_cases hop : dOp C t y ≤ dPp C t y
      · exact Or.inl (Or.inr ⟨hdPp, hdPp_le, hop⟩)
      · have hop' : dPp C t y < dOp C t y := lt_of_not_ge hop
        by_cases heq : dPp C t y = dP C y
        · have hdO_eq : dPp C t y = dO C y := by omega
          exact Or.inr (Or.inl ⟨heq.symm, hdO_eq, by omega⟩)
        · have hdPp_lt : dPp C t y < dP C y := lt_of_le_of_ne hdPp_le heq
          have hdO_eq : dPp C t y = dO C y := by omega
          have hdOp_eq : dOp C t y = dP C y := by omega
          exact Or.inr (Or.inr ⟨hdO_eq, hdOp_eq, by omega⟩)
end N4Code
