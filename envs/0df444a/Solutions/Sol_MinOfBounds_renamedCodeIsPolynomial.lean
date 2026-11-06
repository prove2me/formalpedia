-- Prove2me | solution 1 for MinOfBounds.renamedCodeIsPolynomial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:17:17.927275+00:00
-- url     : https://prove2.me/submissions/741d2919-f592-4815-bd44-2440e9a2e5e6

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_MinOfBounds_Defs
import Definitions.Def_VariableBound_Paper_Rename_Math
import Definitions.Def_VariableBound_Paper_Rename_Compact
import Definitions.Def_VariableBound_Paper_Rename_Code
import Definitions.Def_WidthK_Decode
import Mathlib.Data.Nat.Log
import Mathlib.Data.List.Dedup
import Definitions.Def_MinOfBounds_Rename
import Theorems.Thm_MinOfBounds_length_renamedCode_le
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
open MinOfBounds
open Groundwork Groundwork.Decode VariableBound.Rename MainTheoremForms
open Sat3 (CNF)
namespace MinOfBounds
theorem _root_.solution : RenamedCodeIsPolynomial :=
  ⟨2, fun _ _ φ _ hφ => (length_renamedCode_le φ hφ.1).trans (Nat.mul_le_mul_left _ (Nat.le_self_pow two_ne_zero _))⟩
end MinOfBounds
