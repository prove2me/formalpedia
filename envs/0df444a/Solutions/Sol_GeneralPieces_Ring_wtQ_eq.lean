-- Prove2me | solution 1 for GeneralPieces.Ring.wtQ_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:20:44.311204+00:00
-- url     : https://prove2.me/submissions/38a4880d-47fa-4418-8497-665ed24b082d

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Defs
import Definitions.Def_ClauseBound_Boson_Text
import Mathlib.RingTheory.Derivation.Lie
import Definitions.Def_GeneralPieces_Ring_Bridge

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Ring
open AppHalfPieces MvPolynomial Finset
namespace GeneralPieces.Ring
theorem _root_.solution (μ : List ℕ+) (ks : List ℤ) : wtQ μ ks = ClauseBound.Boson.wt (toL μ) ks := by
  unfold wtQ ClauseBound.Boson.wt toL
  rw [List.zipWith_map_left]
  congr 1
  refine congrArg (fun F => List.zipWith F μ ks) ?_
  funext m k
  have hm := m.pos
  rw [binom, if_pos (by omega)]
  congr 1
  omega
end GeneralPieces.Ring
