-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.g1_inj
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T22:01:32.286787+00:00
-- url     : https://prove2.me/submissions/4324eb64-6bcf-48a7-8578-e56ae386861d

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankWireLayout
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankQHNet
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

open IntMul.Kappa.R8.Bit.Oppbank

theorem solution {b b' w w' : ℕ} (hb : b < 1771) (hb' : b' < 1771)
    (hw : w < NL) (hw' : w' < NL) (heq : g1 b w = g1 b' w') :
    b = b' ∧ w = w' := by
  change (if w < v then w * v + b
      else if w < wEnt then N + (w - v) * v + b
      else if w < wAuxEnd then 2 * N + b * NR + (w - wEnt)
      else W + h * b + (w - wAuxEnd)) =
    (if w' < v then w' * v + b'
      else if w' < wEnt then N + (w' - v) * v + b'
      else if w' < wAuxEnd then 2 * N + b' * NR + (w' - wEnt)
      else W + h * b' + (w' - wAuxEnd)) at heq
  rw [show v = 1771 from rfl, show wEnt = 3542 from rfl, show wAuxEnd = 31336 from rfl,
      show N = 3136441 from rfl, show NR = 27794 from rfl, show W = 104719230 from rfl,
      show h = 23 from rfl, show NL = 31359 from rfl] at *
  split_ifs at heq <;> omega
