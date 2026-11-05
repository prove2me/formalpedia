-- Prove2me | solution 1 for GeneralPieces.Trim.exists_bitsOf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T02:07:32.075422+00:00
-- url     : https://prove2.me/submissions/6eb050ea-c6c4-4b4e-9a80-fbf72e0fed96

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_DefGenPieces_Progs
import Definitions.Def_GeneralPieces_Trim_Prog
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open GeneralPieces
open Finset Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg ClauseBound.Gen
open GeneralPieces.Trim
namespace GeneralPieces.Trim
theorem _root_.solution {n : ℕ} {w : List Bool} (hw : w.length = n) : ∃ x : Pieces.Bits n, bitsOf x = w := by
  subst hw
  exact ⟨w.get, List.ofFn_get w⟩
end GeneralPieces.Trim
