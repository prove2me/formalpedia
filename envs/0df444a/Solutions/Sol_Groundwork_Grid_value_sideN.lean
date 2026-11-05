-- Prove2me | solution 1 for Groundwork.Grid.value_sideN
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:17:25.447527+00:00
-- url     : https://prove2.me/submissions/5b0e0910-07c4-4cdb-bfdd-9ae646f3dd88

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Math_SideCodes
import Definitions.Def_StepMachines_Math_CodeSeq
import Definitions.Def_StepMachines_Math_Pull
import Definitions.Def_Groundwork_Grid_Size
import Definitions.Def_StepMachines_Math_SideNet
import Theorems.Thm_Groundwork_Grid_ZG_congr
import Theorems.Thm_Groundwork_Grid_ZG_tr
import Theorems.Thm_Groundwork_Grid_digit_le
import Theorems.Thm_Groundwork_Grid_sideCut_factors_col
import Theorems.Thm_Groundwork_Grid_sideCut_factors_row
import Theorems.Thm_Groundwork_Grid_sideR_true
import Theorems.Thm_Groundwork_Grid_stC_full
import Theorems.Thm_Groundwork_Grid_value_rowNet
import Theorems.Thm_Groundwork_Network_value_pull
import Theorems.Thm_Groundwork_Prog_digit_le
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
theorem _root_.solution (g : ℕ) (tr : Bool) (n : ℕ) (Rm : Inst (Fin (g * g)) (List Bool)) (y : ℕ) :
    (sideN g tr n Rm y).value = sideZ g n Rm y := by
  refine (Network.value_pull _ _ _ _ (fun _ => stC_full g tr n)).trans ?_
  have hc : ZG (sideR g false n Rm) (fun ω => A n (digit n y (ixOf g ω))) = sideZ g n Rm y :=
    ZG_congr _ fun ω hω => by simp [patOf, hω]
  cases tr with
  | false =>
    rw [← hc]
    exact value_rowNet (G := fun ω => A n (digit n y (ixOf g ω))) (fun ω => sideCut_factors_row (digit_le _ _ _)) _ _ _
  | true =>
    rw [← hc, ← ZG_tr, sideR_true]
    exact value_rowNet (G := trG fun ω => A n (digit n y (ixOf g ω))) (fun ω => sideCut_factors_col _ _) _ _ _
end Groundwork.Grid
