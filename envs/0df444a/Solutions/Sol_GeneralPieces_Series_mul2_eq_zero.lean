-- Prove2me | solution 1 for GeneralPieces.Series.mul2_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:38:03.434953+00:00
-- url     : https://prove2.me/submissions/384470cf-9c35-4cbc-8ebc-ea34140ca7c6

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Series_Rings
import Definitions.Def_ClauseBound_Boson_Defs
import Definitions.Def_GeneralPieces_Series_Expansion

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Series
open ClauseBound.Boson
namespace GeneralPieces.Series
theorem _root_.solution (a b : List ℕ) (r : ℤ) {r' : ℤ} (π : Multiset ℕ) {σ : Multiset ℕ} (h : (σ.sum : ℤ) + r' < 0) : mul2 a r b r' π σ = 0 := by
  rw [mul2, Pz, if_neg (by omega), Finset.sum_empty]
end GeneralPieces.Series
