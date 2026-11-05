-- Prove2me | solution 1 for GeneralPieces.Dual.coe_snoc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T20:26:58.707329+00:00
-- url     : https://prove2.me/submissions/eccdc2f4-1b90-4f91-b4d7-f05714d19823

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
theorem _root_.solution (μ : List ℕ+) (n : ℕ+) : ((μ ++ [n] : List ℕ+) : Multiset ℕ+) = n ::ₘ (μ : Multiset ℕ+) := by
  rw [← Multiset.coe_add, Multiset.coe_singleton, add_comm, Multiset.singleton_add]
end GeneralPieces.Dual
