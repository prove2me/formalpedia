-- Prove2me | solution 1 for Groundwork.Sparsify.pickP_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T20:32:05.695996+00:00
-- url     : https://prove2.me/submissions/441cb04e-ef1c-41f7-9066-06c111a2110f

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Math_SparsifyProg
import Definitions.Def_ToTuring_Lib_List3
import Definitions.Def_ToTuring_Poly_Sparsify
import Theorems.Thm_Groundwork_PolyT_elim
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_product
import Theorems.Thm_P2M_Groundwork_PolyT_find__e812ffd764ea
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.product
attribute [local fun_prop] P2M_Groundwork_PolyT_find__e812ffd764ea



set_option autoImplicit false
section
section
open Groundwork Groundwork.Sparsify
variable {α : Type} [Enc α]
namespace Groundwork.Sparsify
theorem _root_.solution (τ : ℕ) (s : PFml) : pickP τ s =
    ((litsOf s).find? fun a => decide (τ ≤ (overP s 2 [a]).length)).elim
      (((List.product (litsOf s) (litsOf s)).find? fun ab =>
          !(ab.1 == ab.2) && decide (τ ≤ (overP s 3 [ab.1, ab.2]).length)).elim
        (((litsOf s).find? fun a => decide (2 * τ ^ 3 ≤ (overP s 3 [a]).length)).elim none
          fun a => some ([a], greedyP (τ ^ 2) [] ((overP s 3 [a]).map (minusP [a]))))
        fun ab => some ([ab.1, ab.2], ((overP s 3 [ab.1, ab.2]).take τ).map (minusP [ab.1, ab.2])))
      fun a => some ([a], ((overP s 2 [a]).take τ).map (minusP [a])) := by
  unfold pickP
  split
  · next a h => rw [h]; rfl
  · next h =>
    rw [h]
    split
    · next ab h' => rw [h']; rfl
    · next h' =>
      rw [h']
      split
      · next a h'' => rw [h'']; rfl
      · next h'' => rw [h'']; rfl
end Groundwork.Sparsify
