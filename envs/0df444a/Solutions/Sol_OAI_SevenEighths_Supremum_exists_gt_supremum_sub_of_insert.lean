-- Prove2me | solution 1 for OAI.SevenEighths.Supremum.exists_gt_supremum_sub_of_insert
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:44:24.560457+00:00
-- url     : https://prove2.me/submissions/fd1a0166-d3f8-4ecc-b834-2a263c659e98

import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_OAI_NumberTheory_DirichletL_Supremum
import Theorems.Thm_OAI_SevenEighths_Supremum_exists_gt_supremum_sub

set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.Supremum
noncomputable section
namespace OAI.SevenEighths.Supremum
theorem _root_.solution {S : Set ℝ} {a ε : ℝ}
    (hbounded : BddAbove (insert a S)) (hε : 0 < ε)
    (ha : a ≤ sSup (insert a S) - ε) :
    ∃ x ∈ S, sSup (insert a S) - ε < x := by
  obtain ⟨x, hx, hlt⟩ :=
    exists_gt_supremum_sub (Set.insert_nonempty a S) hbounded hε
  rcases Set.mem_insert_iff.mp hx with hxa | hxS
  · subst x
    exact False.elim ((not_lt_of_ge ha) hlt)
  · exact ⟨x, hxS, hlt⟩
end OAI.SevenEighths.Supremum
