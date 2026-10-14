-- Prove2me | solution 1 for LogicBenders.Generic.subVal_upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-13T01:51:42.14725+00:00
-- url     : https://prove2.me/submissions/8360ae9a-c046-44f7-86a7-8319cda8ccee

import Definitions.Def_LogicBenders_Generic_Setting
import Mathlib

open LogicBenders.Generic

theorem solution {X Y : Type*} (S : Set (X × Y)) (f : X → Y → ℝ) (yb : Y) :
    optVal S f ≤ subVal S f yb := by
  unfold optVal subVal
  apply le_iInf
  intro x
  apply le_iInf
  intro hx
  exact iInf_le_of_le (x, yb) (iInf_le_of_le hx le_rfl)
