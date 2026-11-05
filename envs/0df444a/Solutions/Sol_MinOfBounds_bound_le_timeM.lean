-- Prove2me | solution 1 for MinOfBounds.bound_le_timeM
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:22:43.208608+00:00
-- url     : https://prove2.me/submissions/34d6bed4-91f5-4b5c-8644-51415e4dc1c4

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_MinOfBounds_Defs
import Definitions.Def_VariableBound_Paper_Arith
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Definitions.Def_MinOfBounds_Arith
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_VariableBound_Paper_absorb
import Theorems.Thm_VariableBound_Paper_shiftM_le
import Theorems.Thm_VariableBound_Paper_two_le_expM


set_option autoImplicit false
section
section
open MinOfBounds
open MainTheoremForms VariableBound.Paper
namespace MinOfBounds
theorem _root_.solution (C : ℕ) {k m : ℕ} (hk : 1 ≤ k) (hm : 2 ≤ m) : SatM.bound (SatM.rPow (1 / 2)) C k m ≤ timeM (3 * C) k m := by
  unfold SatM.bound timeM
  refine Nat.floor_le_floor ?_
  have e : (C : ℝ) * k * m * SatM.rPow (1 / 2) m = (C : ℝ) * ((k : ℝ) * m * SatM.rPow (1 / 2) m) := by ring
  have h2 := two_le_expM hk hm
  rw [e]
  exact absorb C ((shiftM_le k hm).trans (by linarith)) (by linarith)
end MinOfBounds
