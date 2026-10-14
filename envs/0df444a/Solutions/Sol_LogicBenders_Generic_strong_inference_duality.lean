-- Prove2me | solution 1 for LogicBenders.Generic.strong_inference_duality
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-13T01:50:47.099889+00:00
-- url     : https://prove2.me/submissions/ffd0ce1a-5ac9-4e81-9197-cf5e6a0c8f03

import Definitions.Def_LogicBenders_Generic_Setting
import Mathlib

open LogicBenders.Generic

theorem solution {D : Type*} (S : Set D) (f : D → ℝ) :
    optVal1 S f = infDualVal1 S f := by
  unfold optVal1 infDualVal1 ImpliesWrt
  apply le_antisymm
  · apply le_sSup
    intro x hx
    exact iInf_le_of_le x (iInf_le_of_le hx le_rfl)
  · apply sSup_le
    intro b hb
    exact le_iInf fun x => le_iInf fun hx => hb x hx
