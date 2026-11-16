-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.g1_inj_rec
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T07:27:15.626327+00:00
-- url     : https://prove2.me/submissions/50e77e1c-64ff-4c02-b2e8-f42622fdf0e9

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankWireLayout
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankQHNetRec
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

open IntMul.Kappa.R8.Bit.Oppbank

private theorem g1_unfold (b w : ℕ) :
    g1 b w =
      (if w < v then w * v + b
        else if w < wEnt then N + (w - v) * v + b
        else if w < wAuxEnd then 2 * N + b * NR + (w - wEnt)
        else W + IntMul.Kappa.R8.Bit.Oppbank.h * b + (w - wAuxEnd)) :=
  rfl

theorem solution {b b' w w' : ℕ} (hb : b < 1771) (hb' : b' < 1771)
    (hw : w < NL) (hw' : w' < NL) (heq : g1 b w = g1 b' w') :
    b = b' ∧ w = w' := by
  rw [g1_unfold, g1_unfold] at heq
  simp only [v, wEnt, wAuxEnd, N, NR, W, IntMul.Kappa.R8.Bit.Oppbank.h, NL] at heq hw hw'
  -- Case-split every branch of both if-trees explicitly so omega never sees a residual `ite`.
  by_cases hA : w < 1771
  all_goals by_cases hA' : w' < 1771
  all_goals by_cases hB : w < 3542
  all_goals by_cases hB' : w' < 3542
  all_goals by_cases hC : w < 31336
  all_goals by_cases hC' : w' < 31336
  all_goals (simp only [hA, hA', hB, hB', hC, hC', ite_true, ite_false] at heq; omega)
