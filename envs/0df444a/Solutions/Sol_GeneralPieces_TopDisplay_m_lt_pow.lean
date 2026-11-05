-- Prove2me | solution 1 for GeneralPieces.TopDisplay.m_lt_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T02:08:43.136133+00:00
-- url     : https://prove2.me/submissions/3761354a-6f8b-4713-ba8f-f9cc943e11ee

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Num_PartAUse
import Definitions.Def_ClauseBound_Alg_TopArith
import Definitions.Def_ClauseBound_Gen_Seq
import Definitions.Def_StepMachines_Prog_CountNet
import Definitions.Def_StepMachines_Math_SatNet
import Definitions.Def_GeneralPieces_Num_TopDisplay

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.TopDisplay
open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.TopArith ClauseBound.Gen Levels.Gen GeneralPieces.PartA
namespace GeneralPieces.TopDisplay
theorem _root_.solution (x₀ l m : ℕ) (hx : 1 ≤ x₀) (h : m < K x₀ (l + 1) ^ 9) : m < K x₀ l ^ 90 :=
  calc m < K x₀ (l + 1) ^ 9 := h
    _ ≤ (K x₀ l ^ 10) ^ 9 := Nat.pow_le_pow_left (K_lt_le x₀ l hx).2 9
    _ = K x₀ l ^ 90 := by rw [← pow_mul]
end GeneralPieces.TopDisplay
