-- Prove2me | solution 1 for Groundwork.Grid.U_sideN_col
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:15:06.018187+00:00
-- url     : https://prove2.me/submissions/6e4bb3a4-9f89-425e-ad25-abec77647c77

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Math_SideCodes
import Definitions.Def_StepMachines_Math_CodeSeq
import Definitions.Def_StepMachines_Math_Pull
import Definitions.Def_Groundwork_Grid_Size
import Definitions.Def_StepMachines_Math_SideNet
import Theorems.Thm_Groundwork_Grid_U_rowNet
import Theorems.Thm_Groundwork_length_toWord
import Theorems.Thm_Groundwork_mem_words
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
import Theorems.Thm_P2M_Groundwork_Grid_sum___ixOf_e2b52bf0c490
attribute [local simp] Groundwork.length_toWord
attribute [local simp] Groundwork.mem_words
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
section
open Groundwork Groundwork.Grid
open Finset
open Groundwork.Prog (digit nRect tb capW priceRow priceCol BoundedInst SideNet)
namespace Groundwork.Grid
theorem _root_.solution (g n : ℕ) (Rm : Inst (Fin (g * g)) (List Bool)) (y : ℕ) :
    (sideN g true n Rm y).U = g ^ 2 * (g - 1) * n + priceCol g n y := by
  change (sideNet g true n (sideR g true n Rm) y).U = _
  unfold sideNet priceCol
  rw [U_rowNet (Fintype.card_fin g) (Fintype.card_fin g), ← sum_Ω_ixOf]
  congr 2
  exact Finset.sum_equiv (Equiv.prodComm _ _) (fun ω => by simp [Ω, and_comm]) fun ω _ => rfl
end Groundwork.Grid
