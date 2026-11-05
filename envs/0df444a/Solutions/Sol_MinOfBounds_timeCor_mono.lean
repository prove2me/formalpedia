-- Prove2me | solution 1 for MinOfBounds.timeCor_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:18:08.01792+00:00
-- url     : https://prove2.me/submissions/80cbf31f-f265-4a45-a000-71cac41b4fff

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
import Theorems.Thm_VariableBound_Paper_timeCor_eq
import Theorems.Thm_VariableBound_Paper_timeMin_mono


set_option autoImplicit false
section
section
open MinOfBounds
open MainTheoremForms VariableBound.Paper
namespace MinOfBounds
theorem _root_.solution {C C' : ℕ} (h : C ≤ C') {k m n : ℕ} (hk : 1 ≤ k) (hm : 2 ≤ m) (hn : 4 ≤ n) : timeCor C k m n ≤ timeCor C' k m n := by
  rw [timeCor_eq, timeCor_eq]
  exact timeMin_mono h hk hm hn
end MinOfBounds
