-- Prove2me | solution 1 for Groundwork.Grid.length_he
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:56:03.830224+00:00
-- url     : https://prove2.me/submissions/6b940bb4-f131-4e8b-b693-4d99c76c9462

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Math_CutWord
import Definitions.Def_StepMachines_Math_Digits
import Definitions.Def_StepMachines_Prog_Brute
import Mathlib.Logic.Equiv.Fin.Basic
import Definitions.Def_StepMachines_Math_SideCodes
import Theorems.Thm_Groundwork_length_block


set_option autoImplicit false
section
section
open Groundwork Groundwork.Grid
open Finset
namespace Groundwork.Grid
theorem _root_.solution {g ℓ : ℕ} {z : List Bool} (hz : z.length = g ^ 3 * ℓ) {x u : ℕ} (hx : x < g) (hu : u < g * g) :
    (he g ℓ z x u).length = ℓ := by
  have h1 : (block (g * g * ℓ) x z).length = g * g * ℓ := length_block (by
    rw [hz, show g ^ 3 * ℓ = g * (g * g * ℓ) by ring]
    exact Nat.mul_le_mul_right _ hx)
  exact length_block (by rw [h1]; exact Nat.mul_le_mul_right _ hu)
end Groundwork.Grid
