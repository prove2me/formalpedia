-- Prove2me | solution 1 for GeneralPieces.Half.zz_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:40:48.897323+00:00
-- url     : https://prove2.me/submissions/bd74249d-3bde-496f-a806-d0b115aa7aa9

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Op
import Definitions.Def_ClauseBound_Boson_HalfList
import Definitions.Def_GeneralPieces_Half_List
import Theorems.Thm_GeneralPieces_Ring_count_toN


set_option autoImplicit false
section
section
open GeneralPieces
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring
open GeneralPieces.Half
namespace GeneralPieces.Half
theorem _root_.solution (μ : Ptn) : AppHalfPieces.zz μ = ClauseBound.Boson.zz (toN μ) := by
  unfold AppHalfPieces.zz ClauseBound.Boson.zz
  have h : (toN μ).toFinset = μ.toFinset.image fun k : ℕ+ => (k : ℕ) := Multiset.toFinset_map _ _
  rw [h, Finset.prod_image fun a _ b _ e => PNat.coe_injective e]
  exact Finset.prod_congr rfl fun k _ => by rw [count_toN]
end GeneralPieces.Half
