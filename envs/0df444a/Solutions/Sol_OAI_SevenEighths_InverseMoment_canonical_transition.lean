-- Prove2me | solution 1 for OAI.SevenEighths.InverseMoment.canonical_transition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:19:16.523854+00:00
-- url     : https://prove2.me/submissions/5b4060e6-cbaa-4917-9b4b-6ffb27adc4ec

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Definitions.Def_OAI_NumberTheory_DirichletL_Descent_Basic

set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.InverseMoment
namespace OAI.SevenEighths.InverseMoment
theorem _root_.solution (F M ell A t g theta V j : ℝ) :
    childF F ell A t g theta V j 0 - childM M ell A t g theta V j 0 =
      F - M + decrease ell A t g theta V ∧
    4 * childF F ell A t g theta V j 0 -
      3 * childM M ell A t g theta V j 0 =
      4 * F - 3 * M + 2 * (A + t + g - theta + V) + j := by
  constructor <;> unfold childF childM decrease <;> ring
end OAI.SevenEighths.InverseMoment
