-- Prove2me | solution 1 for OAI.SevenEighths.InverseMoment.child_margins
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:19:18.70546+00:00
-- url     : https://prove2.me/submissions/2e3d6061-4fcf-48c1-b569-7667040749f4

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Definitions.Def_OAI_NumberTheory_DirichletL_Descent_Basic
import Theorems.Thm_OAI_SevenEighths_InverseMoment_child_margins_sharp

set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.InverseMoment
namespace OAI.SevenEighths.InverseMoment
theorem _root_.solution {F M Q Q' z c ell A t g theta V j delta eta : ℝ}
    (h : CanonicalMargins F M Q z c)
    (hA : 0 ≤ A) (ht : 0 ≤ t) (hV : 0 ≤ V) (hj : 0 ≤ j)
    (hgt : -2 * eta ≤ g - theta) (hdelta : 0 ≤ delta) (heta : 0 ≤ eta)
    (hQ : Q' ≤ Q + decrease ell A t g theta V + 4 * eta) :
    CanonicalMargins (childF F ell A t g theta V j delta)
      (childM M ell A t g theta V j eta) Q' z (c - 7 * eta) := by
  obtain ⟨h₁, h₂⟩ := child_margins_sharp (delta := delta) h hA ht hV hj hgt hQ
  constructor <;> linarith
end OAI.SevenEighths.InverseMoment
