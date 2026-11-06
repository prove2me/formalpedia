-- Prove2me | solution 1 for OAI.SevenEighths.Supremum.seven_eighths_of_uniform_margin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:12:30.129243+00:00
-- url     : https://prove2.me/submissions/4d92dedc-6509-47dd-b4a7-7ad351dea58c

import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_OAI_NumberTheory_DirichletL_Supremum
import Theorems.Thm_OAI_SevenEighths_Supremum_continuationMargin_pos
import Theorems.Thm_OAI_SevenEighths_Supremum_uniform_bound_below_supremum_false

set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.Supremum
noncomputable section
namespace OAI.SevenEighths.Supremum
theorem _root_.solution {S : Set ℝ}
    (hne : S.Nonempty) (hbounded : BddAbove S)
    (hbound : 7 / 8 < sSup S →
      ∃ ω σ : ℝ, ω < sSup S - 7 / 8 ∧ 0 < σ ∧
        ∀ x ∈ S, x ≤ sSup S - continuationMargin (sSup S) ω σ) :
    sSup S ≤ 7 / 8 := by
  by_contra h
  obtain ⟨ω, σ, hω, hσ, hbound⟩ := hbound (lt_of_not_ge h)
  exact uniform_bound_below_supremum_false hne hbounded
    (continuationMargin_pos hω hσ) hbound
end OAI.SevenEighths.Supremum
