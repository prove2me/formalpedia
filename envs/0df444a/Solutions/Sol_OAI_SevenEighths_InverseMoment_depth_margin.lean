-- Prove2me | solution 1 for OAI.SevenEighths.InverseMoment.depth_margin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:19:37.324414+00:00
-- url     : https://prove2.me/submissions/b26d2412-c7ad-4d76-8814-d258b21a75a2

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Definitions.Def_OAI_NumberTheory_DirichletL_Descent_Basic

set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.InverseMoment
namespace OAI.SevenEighths.InverseMoment
theorem _root_.solution {c D h eta : ℝ} (heta : 0 ≤ eta) (hh : h ≤ D)
    (hbudget : D * eta ≤ c / 14) : c / 2 ≤ c - 7 * h * eta := by
  have := mul_le_mul_of_nonneg_right hh heta
  nlinarith
end OAI.SevenEighths.InverseMoment
