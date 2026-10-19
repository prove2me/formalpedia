-- Prove2me | solution 1 for IntMul.Kappa.halted_multitape_step_fixed
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-16T22:02:32.492097+00:00
-- url     : https://prove2.me/submissions/d712295d-7892-4633-b074-ad33686808d8

import Mathlib
import Definitions.Def_IntMul_MultitapeModel

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open IntMul

theorem solution
    (M : MultitapeTM) (c : M.Cfg)
    (hc : c.state = M.qHalt) : M.step c = c := by
  cases c with
  | mk state cells head =>
      dsimp at hc
      subst state
      simp [MultitapeTM.step, M.halt_fixed]
