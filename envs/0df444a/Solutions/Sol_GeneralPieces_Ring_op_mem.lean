-- Prove2me | solution 1 for GeneralPieces.Ring.op_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:42:39.887261+00:00
-- url     : https://prove2.me/submissions/5c933ef4-12c8-42ff-bed8-db66c0c9074a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_OpFacts
import Definitions.Def_GeneralPieces_Ring_Op
import Theorems.Thm_GeneralPieces_Ring_opMon_mem

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Ring
open AppHalfPieces MvPolynomial Finset
namespace GeneralPieces.Ring
theorem _root_.solution (a : V) (r : ℤ) {E : ℤ} {f : V} (hf : f ∈ VE E) : op a r f ∈ VE (E + r) :=
  Submodule.sum_mem _ fun _ _ => Submodule.smul_mem _ _ (opMon_mem _ r hf)
end GeneralPieces.Ring
