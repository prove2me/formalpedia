-- Prove2me | solution 1 for MinOfBounds.renamedCode_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:39:36.764505+00:00
-- url     : https://prove2.me/submissions/aca688aa-b3b5-4da8-8409-914b5d0c5231

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
import Theorems.Thm_VariableBound_Rename_encN_toN
import Theorems.Thm_VariableBound_Rename_toN_ren


set_option autoImplicit false
section
section
open MinOfBounds
open Groundwork Groundwork.Decode VariableBound.Rename MainTheoremForms
open Sat3 (CNF)
namespace MinOfBounds
theorem _root_.solution (k : ℕ) {V : ℕ} (φ : CNF V) : renamedCode k φ = SatM.enc k (ren φ) := by
  rw [renamedCode, ← encN_toN, toN_ren, renF, ← length_occL, List.map_const']
end MinOfBounds
