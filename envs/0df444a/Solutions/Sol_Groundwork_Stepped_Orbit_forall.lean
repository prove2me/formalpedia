-- Prove2me | solution 1 for Groundwork.Stepped.Orbit.forall
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:23:18.382853+00:00
-- url     : https://prove2.me/submissions/61fe4954-670c-4864-9650-1c799cb1ea68

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_Stepped
import Definitions.Def_StepMachines_Math_SparsifyTree
import Definitions.Def_StepMachines_Prog_Walk
import Theorems.Thm_Groundwork_size_bool
import Theorems.Thm_Groundwork_size_inl
import Theorems.Thm_Groundwork_size_inr
import Theorems.Thm_Groundwork_size_int
import Theorems.Thm_Groundwork_size_list
import Theorems.Thm_Groundwork_size_nat
import Theorems.Thm_Groundwork_size_none
import Theorems.Thm_Groundwork_size_prod
import Theorems.Thm_Groundwork_size_some
import Theorems.Thm_Groundwork_size_unit
attribute [local simp] Groundwork.size_bool
attribute [local simp] Groundwork.size_inl
attribute [local simp] Groundwork.size_inr
attribute [local simp] Groundwork.size_int
attribute [local simp] Groundwork.size_list
attribute [local simp] Groundwork.size_nat
attribute [local simp] Groundwork.size_none
attribute [local simp] Groundwork.size_prod
attribute [local simp] Groundwork.size_some
attribute [local simp] Groundwork.size_unit



set_option autoImplicit false
section
open Groundwork Groundwork.Stepped
open Groundwork.Sparsify (leaves)
variable {α β τ ν : Type}
namespace Groundwork.Stepped
namespace Orbit
theorem _root_.solution {nxt : τ → Option τ} {o : Option τ} {xs : List τ} (h : Orbit nxt o xs) (P : τ → Prop)
    (h0 : ∀ x, o = some x → P x) (hs : ∀ y z, P y → nxt y = some z → P z) : ∀ y ∈ xs, P y := by
  induction h with
  | nil => simp
  | @cons x xs _ ih =>
    have hx := h0 x rfl
    intro y hy
    rcases List.mem_cons.1 hy with rfl | hy
    · exact hx
    · exact ih (fun z hz => hs x z hx hz) y hy
end Orbit
end Groundwork.Stepped
