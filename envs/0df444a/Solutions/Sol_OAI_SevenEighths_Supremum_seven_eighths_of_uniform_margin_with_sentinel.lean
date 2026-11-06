-- Prove2me | solution 1 for OAI.SevenEighths.Supremum.seven_eighths_of_uniform_margin_with_sentinel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:12:34.955934+00:00
-- url     : https://prove2.me/submissions/bcd6606f-64da-4d71-a16b-b5781e68eb76

import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_OAI_NumberTheory_DirichletL_Supremum
import Theorems.Thm_OAI_SevenEighths_Supremum_continuationMargin_pos
import Theorems.Thm_OAI_SevenEighths_Supremum_continuation_boundary_gt
import Theorems.Thm_OAI_SevenEighths_Supremum_exists_gt_supremum_sub_of_insert

set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.Supremum
noncomputable section
namespace OAI.SevenEighths.Supremum
theorem _root_.solution {S : Set ℝ}
    (hbounded : BddAbove (insert (1 / 2 : ℝ) S))
    (hbound : 7 / 8 < sSup (insert (1 / 2 : ℝ) S) →
      ∃ ω σ : ℝ, 0 < ω ∧ ω < sSup (insert (1 / 2 : ℝ) S) - 7 / 8 ∧
        0 < σ ∧ ∀ x ∈ S, x ≤ sSup (insert (1 / 2 : ℝ) S) -
          continuationMargin (sSup (insert (1 / 2 : ℝ) S)) ω σ) :
    sSup (insert (1 / 2 : ℝ) S) ≤ 7 / 8 := by
  by_contra h
  obtain ⟨ω, σ, hω0, hω, hσ, hbound⟩ := hbound (lt_of_not_ge h)
  have hε := continuationMargin_pos hω hσ
  have hboundary := continuation_boundary_gt (β := sSup (insert (1 / 2 : ℝ) S))
    (σ := σ) hω0
  have hsentinel : (1 / 2 : ℝ) ≤ sSup (insert (1 / 2 : ℝ) S) -
      continuationMargin (sSup (insert (1 / 2 : ℝ) S)) ω σ := by
    linarith
  obtain ⟨x, hx, hlt⟩ := exists_gt_supremum_sub_of_insert hbounded hε hsentinel
  exact (not_lt_of_ge (hbound x hx)) hlt
end OAI.SevenEighths.Supremum
