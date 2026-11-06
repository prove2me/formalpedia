-- Prove2me | solution 1 for OAI.SevenEighths.InverseMoment.clipping_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:19:24.544781+00:00
-- url     : https://prove2.me/submissions/2510ea9f-455e-419c-b838-28203a8c34c1

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Definitions.Def_OAI_NumberTheory_DirichletL_Descent_Basic

set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.InverseMoment
namespace OAI.SevenEighths.InverseMoment
theorem _root_.solution {N eta : ℝ} (heta : 0 ≤ eta) (hN : -6 * eta ≤ N) :
    0 ≤ max 0 N - N ∧ max 0 N - N ≤ 6 * eta := by
  constructor
  · exact sub_nonneg.mpr (le_max_right 0 N)
  · rcases le_total 0 N with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h]; linarith
end OAI.SevenEighths.InverseMoment
