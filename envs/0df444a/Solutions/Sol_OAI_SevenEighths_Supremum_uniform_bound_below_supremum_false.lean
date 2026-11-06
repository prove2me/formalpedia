-- Prove2me | solution 1 for OAI.SevenEighths.Supremum.uniform_bound_below_supremum_false
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:16:14.459896+00:00
-- url     : https://prove2.me/submissions/e1b66235-03fc-479a-a089-136751cc82e6

import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_OAI_NumberTheory_DirichletL_Supremum
import Theorems.Thm_OAI_SevenEighths_Supremum_exists_gt_supremum_sub

set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.Supremum
noncomputable section
namespace OAI.SevenEighths.Supremum
theorem _root_.solution {S : Set ℝ}
    (hne : S.Nonempty) (hbounded : BddAbove S) {ε : ℝ} (hε : 0 < ε)
    (hbound : ∀ x ∈ S, x ≤ sSup S - ε) : False := by
  obtain ⟨x, hx, hlt⟩ := exists_gt_supremum_sub hne hbounded hε
  exact (not_lt_of_ge (hbound x hx)) hlt
end OAI.SevenEighths.Supremum
