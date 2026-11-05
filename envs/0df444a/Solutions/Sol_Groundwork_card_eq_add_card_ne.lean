-- Prove2me | solution 1 for Groundwork.card_eq_add_card_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:06:42.690194+00:00
-- url     : https://prove2.me/submissions/0223901e-d8aa-4432-be85-b4515886ff2d

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_GridDefs
import Definitions.Def_StepMachines_Math_CodeMore
import Definitions.Def_StepMachines_Math_Sparse

set_option autoImplicit false
section
section
open Groundwork
open Finset
open Groundwork.Prog (tb capW)
namespace Groundwork
theorem _root_.solution {n : ℕ} (s₀ : Bell) (β : Fin n → Bell) : #{k | β k = s₀} + #{k | β k ≠ s₀} = n := by
  rw [card_filter_add_card_filter_not, card_univ, Fintype.card_fin]
end Groundwork
