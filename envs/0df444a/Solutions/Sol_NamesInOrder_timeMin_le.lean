-- Prove2me | solution 1 for NamesInOrder.timeMin_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:53:02.872542+00:00
-- url     : https://prove2.me/submissions/e75db29d-176c-4e4c-9afc-a172cbc849c8

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_NamesInOrder_Defs
import Definitions.Def_MinOfBounds_Main
import Definitions.Def_MinOfBounds_Rename
import Definitions.Def_MinOfBounds_Arith
import Definitions.Def_Wrap_Main
import Definitions.Def_Wrap_Sim
import Definitions.Def_ToTuring_Closure_Basic
import Definitions.Def_VariableBound_Paper_Arith
import Definitions.Def_NamesInOrder_General

set_option autoImplicit false
section
section
open NamesInOrder
open Turing Groundwork Wrap TwoMachines MainTheoremForms MinOfBounds
open Sat3 (CNF)
namespace NamesInOrder
theorem _root_.solution (C k m n : ℕ) : timeMin C k m n ≤ timeM C k m ∧ timeMin C k m n ≤ timeN C k n :=
  ⟨Nat.floor_mono (Real.rpow_le_rpow_of_exponent_le one_le_two (mul_le_mul_of_nonneg_left (min_le_left _ _) (Nat.cast_nonneg C))),
   Nat.floor_mono (Real.rpow_le_rpow_of_exponent_le one_le_two (mul_le_mul_of_nonneg_left (min_le_right _ _) (Nat.cast_nonneg C)))⟩
end NamesInOrder
