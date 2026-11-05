-- Prove2me | solution 1 for GeneralPieces.Ring.VE_natCast
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:34:10.013383+00:00
-- url     : https://prove2.me/submissions/0fe9e844-e9b4-4471-b4cd-02f12da10775

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Bridge
import Definitions.Def_ClauseBound_Part_Rec
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Definitions.Def_GeneralPieces_Ring_Basic

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Ring
open AppHalfPieces MvPolynomial Finset
namespace GeneralPieces.Ring
theorem _root_.solution (E : ℕ) : VE (E : ℤ) = weightedHomogeneousSubmodule ℚ wgt E := by
  rw [VE, if_pos (by omega), Int.toNat_natCast]
  rfl
end GeneralPieces.Ring
