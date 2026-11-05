-- Prove2me | solution 1 for GeneralPieces.Ring.ext_coef
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:28:59.101116+00:00
-- url     : https://prove2.me/submissions/b250ed8a-d550-4b3f-98c4-dc609f0d3314

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
theorem _root_.solution {f g : V} (h : ∀ π, coef π f = coef π g) : f = g := by
  ext d
  have := h (Finsupp.toMultiset d)
  unfold coef at this
  rwa [Finsupp.toMultiset_toFinsupp] at this
end GeneralPieces.Ring
