-- Prove2me | solution 1 for OAI.SevenEighths.Supremum.max_signal_exponents
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:15:39.04482+00:00
-- url     : https://prove2.me/submissions/7d569a51-27de-4564-82b5-aa310fd827e9

import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_OAI_NumberTheory_DirichletL_Supremum

set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.Supremum
noncomputable section
namespace OAI.SevenEighths.Supremum
theorem _root_.solution (β ω σ c : ℝ) :
    max (7 / 8 + c + ω) (β + c - σ) =
      β + c - continuationMargin β ω σ := by
  unfold continuationMargin
  rcases le_total (β - 7 / 8 - ω) σ with h | h
  · rw [min_eq_left h, max_eq_left (by linarith)]
    linarith
  · rw [min_eq_right h, max_eq_right (by linarith)]
end OAI.SevenEighths.Supremum
