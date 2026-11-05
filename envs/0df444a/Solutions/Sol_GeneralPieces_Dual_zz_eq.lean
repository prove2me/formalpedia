-- Prove2me | solution 1 for GeneralPieces.Dual.zz_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:21:13.059222+00:00
-- url     : https://prove2.me/submissions/5b032d31-7861-4227-b068-33a79ec68dcf

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Op
import Definitions.Def_ClauseBound_Boson_Dual
import Definitions.Def_GeneralPieces_Ring_Dual

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Dual
open Finset MvPolynomial AppHalfPieces
namespace GeneralPieces.Dual
theorem _root_.solution (μ : Ptn) : zz μ = ClauseBound.Boson.zz (μ.map fun k : ℕ+ => (k : ℕ)) := by
  unfold zz ClauseBound.Boson.zz
  rw [Multiset.toFinset_map, prod_image PNat.coe_injective.injOn]
  refine prod_congr rfl fun k _ => ?_
  rw [Multiset.count_map_eq_count' _ _ PNat.coe_injective]
end GeneralPieces.Dual
