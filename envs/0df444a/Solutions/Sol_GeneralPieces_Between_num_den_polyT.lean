-- Prove2me | solution 1 for GeneralPieces.Between.num_den_polyT
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T21:27:32.713529+00:00
-- url     : https://prove2.me/submissions/48117240-ad1c-43c6-bbab-bd168f9f03a8

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Num_Asymptotic
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_GeneralPieces_Num_Between
import Theorems.Thm_Groundwork_PB_add
import Theorems.Thm_Groundwork_PB_const
import Theorems.Thm_Groundwork_PB_mul
import Theorems.Thm_Groundwork_PolyT_const
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_mul
import Theorems.Thm_Groundwork_PolyT_prodMk
import Theorems.Thm_Groundwork_Unary_add
import Theorems.Thm_Groundwork_Unary_const
import Theorems.Thm_Groundwork_Unary_mul
import Theorems.Thm_Groundwork_Unary_poly
import Theorems.Thm_P2M_Groundwork_PB_id__8af0b594aff4
import Theorems.Thm_P2M_Groundwork_PolyT_id__1c5d0f44cc8f
attribute [local fun_prop] Groundwork.PolyT.const
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.mul
attribute [local fun_prop] Groundwork.PolyT.prodMk
attribute [local fun_prop] P2M_Groundwork_PolyT_id__1c5d0f44cc8f



set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Between
open Groundwork PaddedDescent.F Levels.Gen
namespace GeneralPieces.Between
theorem _root_.solution : PolyT fun u : U => (num u.length, den u.length) := by
  have hl : Unary fun u : U => u.length := unary_length PolyT.id'
  have h1 : PolyT fun u : U => 5 + 2 * (u.length - 2 * (u.length / 2)) :=
    PolyT.add (PolyT.const 5) (PolyT.mul (PolyT.const 2) (unary_sub hl (PolyT.mul (PolyT.const 2) (unary_div hl (PolyT.const 2)).poly)).poly)
  have h2 : PolyT fun u : U => 5 * 2 ^ ((u.length + 1) / 2) :=
    PolyT.mul (PolyT.const 5) (pow_polyT (PolyT.const 2) (unary_div (unary_add hl (unary_const 1)) (PolyT.const 2)))
  exact PolyT.prodMk h1 h2
end GeneralPieces.Between
