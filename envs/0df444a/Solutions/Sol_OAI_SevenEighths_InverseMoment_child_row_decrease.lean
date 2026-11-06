-- Prove2me | solution 1 for OAI.SevenEighths.InverseMoment.child_row_decrease
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:19:19.435688+00:00
-- url     : https://prove2.me/submissions/c589cadd-6465-4122-8a2c-ed2a7b5a0c99

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Definitions.Def_OAI_NumberTheory_DirichletL_Descent_Basic

set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.InverseMoment
namespace OAI.SevenEighths.InverseMoment
theorem _root_.solution {M ell A t g theta V j eta d : ℝ}
    (hA : 0 ≤ A) (ht : 0 ≤ t) (hgt : -2 * eta ≤ g - theta)
    (hj : j ≤ 2 * ell + 3 * eta) (hterminal : d ≤ ell + V)
    (heta : eta ≤ d / 16) :
    3 * d / 2 ≤ M - childM M ell A t g theta V j eta := by
  unfold childM decrease
  linarith
end OAI.SevenEighths.InverseMoment
