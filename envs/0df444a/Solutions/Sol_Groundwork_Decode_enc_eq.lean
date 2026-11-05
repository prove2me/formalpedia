-- Prove2me | solution 1 for Groundwork.Decode.enc_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:28:39.14004+00:00
-- url     : https://prove2.me/submissions/d196bb90-35ec-4ac3-9fd3-fc702ffa8548

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThreeSatStatement
import Definitions.Def_StepMachines_Prog_Chunks
import Mathlib.Data.Nat.Size
import Definitions.Def_StepMachines_Math_Formula
import Definitions.Def_StepMachines_Prog_Decode

set_option autoImplicit false
section
open Groundwork Groundwork.Decode
open Sat3
namespace Groundwork.Decode
theorem _root_.solution {n : ℕ} (φ : CNF n) : enc φ = List.replicate n true ++ false :: (φ.map (blk n)).flatten := by
  rw [enc, List.flatMap_def]
  rfl
end Groundwork.Decode
