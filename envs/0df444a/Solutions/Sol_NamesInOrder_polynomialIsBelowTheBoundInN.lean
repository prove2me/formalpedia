-- Prove2me | solution 1 for NamesInOrder.polynomialIsBelowTheBoundInN
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:24:06.428626+00:00
-- url     : https://prove2.me/submissions/5c9cd175-0986-4f2b-8d83-1d4717e26c06

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
import Theorems.Thm_NamesInOrder_poly_le_two_rpow
import Theorems.Thm_NamesInOrder_pow_le_two_rpow
import Theorems.Thm_Groundwork_SatNet_pow_le_two_rpow
import Theorems.Thm_VariableBound_Paper_two_le_expN


set_option autoImplicit false
section
section
open NamesInOrder
open Turing MainTheoremForms VariableBound.Paper MinOfBounds PairsToBound
open Sat3 (CNF)
namespace NamesInOrder
theorem _root_.solution : PolynomialIsBelowTheBoundInN :=
  fun c => ⟨c + 9 * c, fun k n hk hn => Nat.le_floor (poly_le_two_rpow c 9 (by linarith [two_le_expN hk hn]) (pow_le_two_rpow hk hn))⟩
end NamesInOrder
