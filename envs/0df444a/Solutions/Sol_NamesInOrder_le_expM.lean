-- Prove2me | solution 1 for NamesInOrder.le_expM
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:18:24.258072+00:00
-- url     : https://prove2.me/submissions/96a541b7-5199-449e-b12f-5c8d4149bd33

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_NamesInOrder_Defs
import Definitions.Def_MinOfBounds_Arith
import Definitions.Def_PairsToBound_Arith
import Definitions.Def_VariableBound_Paper_Arith
import Definitions.Def_VariableBound_Paper_Forms
import Definitions.Def_ClauseBound_Alg_End
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Definitions.Def_NamesInOrder_Arith
import Theorems.Thm_PairsToBound_lg_le_div_sqrt
import Theorems.Thm_VariableBound_Paper_expM_eq
import Theorems.Thm_VariableBound_Paper_one_le_lg


set_option autoImplicit false
section
section
open NamesInOrder
open Turing MainTheoremForms VariableBound.Paper MinOfBounds PairsToBound
open Sat3 (CNF)
namespace NamesInOrder
theorem _root_.solution {k m : ℕ} (hk : 1 ≤ k) (hm : 2 ≤ m) : (k : ℝ) ≤ expM k m ∧ lg m ≤ expM k m := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have h1 := lg_le_div_sqrt hm
  have h2 := one_le_lg hm
  rw [expM_eq]
  constructor
  · nlinarith
  · nlinarith
end NamesInOrder
