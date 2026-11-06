-- Prove2me | solution 1 for OAI.SevenEighths.InverseMoment.step_energy_exponent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:19:25.395782+00:00
-- url     : https://prove2.me/submissions/bf618d93-8f99-4bc8-a0bf-7ce74f0c39c9

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Definitions.Def_OAI_NumberTheory_DirichletL_Descent_Basic

set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.InverseMoment
namespace OAI.SevenEighths.InverseMoment
theorem _root_.solution {F Fc kappa lambda count delta eta tau pi eps : ℝ}
    (hid : kappa + lambda + count + 2 * Fc = F)
    (hdelta : delta ≤ 6 * eta) :
    kappa + lambda + count + 2 * (Fc + delta) +
      (9 / 2 + 18 + 11 / 2) * eta + tau + pi + eps ≤
      F + 40 * eta + tau + pi + eps := by
  linarith
end OAI.SevenEighths.InverseMoment
