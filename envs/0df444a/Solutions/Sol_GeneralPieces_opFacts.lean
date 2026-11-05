-- Prove2me | solution 1 for GeneralPieces.opFacts
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:43:52.894198+00:00
-- url     : https://prove2.me/submissions/834be788-8302-4169-87b3-18a78e859727

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Basic
import Definitions.Def_GeneralPieces_Ring_OpFacts
import Theorems.Thm_GeneralPieces_Ring_Bd_mono
import Theorems.Thm_GeneralPieces_Ring_finite_terms
import Theorems.Thm_GeneralPieces_Ring_opMon_perm
import Theorems.Thm_GeneralPieces_Ring_op_tpow
import Theorems.Thm_GeneralPieces_Ring_op_add_right
import Theorems.Thm_GeneralPieces_Ring_op_smul_right
import Theorems.Thm_GeneralPieces_Ring_op_add_left
import Theorems.Thm_GeneralPieces_Ring_op_smul_left

set_option autoImplicit false
section
section
open GeneralPieces
open AppHalfPieces GeneralPieces.Ring
namespace GeneralPieces
theorem _root_.solution : OpFacts where
  finite := finite_terms
  perm := fun _ _ r f h => opMon_perm h r f
  mono := op_tpow
  add_right := op_add_right
  smul_right := op_smul_right
  add_left := op_add_left
  smul_left := op_smul_left
end GeneralPieces
