-- Prove2me | solution 1 for OAI.SevenEighths.InverseMoment.initial_energy_exponent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:19:33.015211+00:00
-- url     : https://prove2.me/submissions/a4e241a5-17e8-4b03-bcc5-3694ddedd368

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Definitions.Def_OAI_NumberTheory_DirichletL_Descent_Basic

set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.InverseMoment
namespace OAI.SevenEighths.InverseMoment
theorem _root_.solution {m delta eta pi eps : ℝ}
    (hdelta : delta ≤ 3 * eta) :
    m + 3 * eta + 2 * eta + 2 * delta + pi + eps ≤
      m + 11 * eta + pi + eps := by
  linarith
end OAI.SevenEighths.InverseMoment
