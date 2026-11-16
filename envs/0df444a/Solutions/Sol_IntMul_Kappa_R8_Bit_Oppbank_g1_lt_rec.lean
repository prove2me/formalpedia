-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.g1_lt_rec
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T07:27:16.10619+00:00
-- url     : https://prove2.me/submissions/1209b2a9-d663-4373-bcc3-189354317c77

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankWireLayout
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankQHNetRec
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

open IntMul.Kappa.R8.Bit.Oppbank

theorem solution {b w : ℕ} (hb : b < 1771) (hw : w < NL) : g1 b w < W + Tmp := by
  -- Expand `g1` and replace every layout constant by its numeral.
  change (if w < v then w * v + b
      else if w < wEnt then N + (w - v) * v + b
      else if w < wAuxEnd then 2 * N + b * NR + (w - wEnt)
      else W + h * b + (w - wAuxEnd)) < W + Tmp
  rw [show v = 1771 from rfl, show wEnt = 3542 from rfl, show wAuxEnd = 31336 from rfl,
      show N = 3136441 from rfl, show NR = 27794 from rfl, show W = 104719230 from rfl,
      show Tmp = 3217907 from rfl, show h = 23 from rfl, show NL = 31359 from rfl] at *
  split_ifs <;> omega
