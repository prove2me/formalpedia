-- Prove2me | solution 1 for GeneralPieces.Ring.card_ptns
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:31:23.263199+00:00
-- url     : https://prove2.me/submissions/bfde1540-681d-42b2-b6f9-6798d9c42188

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Bridge
import Definitions.Def_ClauseBound_Part_Rec
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Definitions.Def_GeneralPieces_Ring_Basic
import Theorems.Thm_P2M_GeneralPieces_Ring_toN_map_toPNat__be122ac80f3b

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Ring
open AppHalfPieces MvPolynomial Finset
namespace GeneralPieces.Ring
theorem _root_.solution (E : ℕ) : #(ptns E) = Partitions.p E := by
  unfold ptns Partitions.p
  rw [card_image_of_injective _ fun q q' h => ?_, card_univ]
  have h' := congrArg toN h
  rw [toN_map_toPNat' fun i hi => q.parts_pos hi, toN_map_toPNat' fun i hi => q'.parts_pos hi] at h'
  exact Nat.Partition.ext h'
end GeneralPieces.Ring
