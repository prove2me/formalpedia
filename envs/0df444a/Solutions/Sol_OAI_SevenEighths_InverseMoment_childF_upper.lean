-- Prove2me | solution 1 for OAI.SevenEighths.InverseMoment.childF_upper
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:19:23.759193+00:00
-- url     : https://prove2.me/submissions/6407051d-e8c7-475b-9648-d46b26ac53f7

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Definitions.Def_OAI_NumberTheory_DirichletL_Descent_Basic

set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.InverseMoment
namespace OAI.SevenEighths.InverseMoment
theorem _root_.solution {F ell A t g theta V j delta eta : ℝ}
    (hA : 0 ≤ A) (ht : 0 ≤ t) (hell : 0 ≤ ell) (hV : 0 ≤ V)
    (hgt : -2 * eta ≤ g - theta) (hj : j ≤ 2 * ell + 3 * eta)
    (hdelta : delta ≤ 6 * eta) :
    childF F ell A t g theta V j delta ≤ F + 11 * eta := by
  unfold childF decrease
  linarith
end OAI.SevenEighths.InverseMoment
