-- Prove2me | solution 2 for GeneralPieces.Dual.tpow_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:23:09.899211+00:00
-- url     : https://prove2.me/submissions/463ee202-161b-49a5-aeb0-ae82998d4098

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Op
import Definitions.Def_ClauseBound_Boson_Dual
import Definitions.Def_GeneralPieces_Ring_Dual
import Theorems.Thm_GeneralPieces_Dual_weight_toFinsupp
import Theorems.Thm_GeneralPieces_Ring_weight_toFinsupp


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Dual
open Finset MvPolynomial AppHalfPieces
namespace GeneralPieces.Dual
theorem _root_.solution (ν : Ptn) : tpow ν ∈ VE (wt ν) := by
  rw [VE, if_pos (Int.natCast_nonneg _), Int.toNat_natCast, mem_weightedHomogeneousSubmodule]
  exact isWeightedHomogeneous_monomial _ _ _ (weight_toFinsupp ν)
end GeneralPieces.Dual
