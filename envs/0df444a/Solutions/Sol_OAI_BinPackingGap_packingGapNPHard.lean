-- Prove2me | solution 1 for OAI.BinPackingGap.packingGapNPHard
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-02T20:02:18.780759+00:00
-- url     : https://prove2.me/submissions/3fcbfd86-62cb-476b-9e37-36981356003b

import Theorems.Thm_OAI_BinPackingGap_packingGapNPHard_oaiq082
import Lean.Elab.Tactic.Omega
import Std

import Mathlib
import Definitions.Def_BinPackingGap
open OAI BinPackingGap


noncomputable section


open scoped BigOperators

theorem solution (c : Nat) : PackingGapNPHard c :=
  OAI.BinPackingGap.packingGapNPHard_oaiq082 c