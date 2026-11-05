-- Prove2me | solution 1 for NamesInOrder.polynomialIsBelowTheBoundInM
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:47:11.694544+00:00
-- url     : https://prove2.me/submissions/c43ba1b1-abd4-4882-87f6-32775be84a47

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
import Theorems.Thm_NamesInOrder_sq_le_two_rpow
import Theorems.Thm_VariableBound_Paper_two_le_expM


set_option autoImplicit false
section
section
open NamesInOrder
open Turing MainTheoremForms VariableBound.Paper MinOfBounds PairsToBound
open Sat3 (CNF)
namespace NamesInOrder
theorem _root_.solution : PolynomialIsBelowTheBoundInM :=
  fun c => ⟨c + 6 * c, fun k m hk hm => Nat.le_floor (poly_le_two_rpow c 6 (by linarith [two_le_expM hk hm]) (sq_le_two_rpow hk hm))⟩
end NamesInOrder
