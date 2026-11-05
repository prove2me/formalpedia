-- Prove2me | solution 1 for Groundwork.Grid.sideNet_sized
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:19:19.643797+00:00
-- url     : https://prove2.me/submissions/c49ffc14-de4e-463e-b7de-0314d7d41b02

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Math_SideCodes
import Definitions.Def_StepMachines_Math_CodeSeq
import Definitions.Def_StepMachines_Math_Pull
import Definitions.Def_Groundwork_Grid_Size
import Definitions.Def_StepMachines_Math_SideNet
import Theorems.Thm_Groundwork_Grid_abs_sideCut_bot
import Theorems.Thm_Groundwork_Grid_abs_sideCut_top
import Theorems.Thm_Groundwork_Grid_card_sideCut_lab
import Theorems.Thm_Groundwork_Grid_digit_le
import Theorems.Thm_Groundwork_Grid_sideCut_cap_le
import Theorems.Thm_Groundwork_Grid_sideCut_factors_col
import Theorems.Thm_Groundwork_Grid_sideCut_factors_row
import Theorems.Thm_Groundwork_Prog_digit_le
import Theorems.Thm_Groundwork_abs_A_le
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
import Theorems.Thm_P2M_Groundwork_Grid_rowNet_sized__9b8262c1a57f
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
theorem _root_.solution {g n B : ℕ} (tr : Bool) (hn : 1 ≤ n) {R : Inst (Fin g × Fin g) (Bits n)}
    (hR : ∀ w h, |R w h| ≤ 2 ^ B) (y : ℕ) : (sideNet g tr n R y).Sized (2 * g ^ 3 * n) (g * B + g ^ 2 * n) := by
  have hα : Fintype.card (Bits n) = 2 ^ n := by simp
  rw [Nat.mul_assoc]
  cases tr with
  | false =>
    exact rowNet_sized' (m := 2) (by norm_num) (Fintype.card_fin g) (Fintype.card_fin g) hα R hR
      (G := fun ω => A n (rectDig g false n y (tri ω.1.1 ω.1.2) (tri ω.2.1 ω.2.2))) _ _
      (fun ω => sideCut_factors_row (digit_le _ _ _)) (fun ω => card_sideCut_lab _ _ _)
      (fun ω => sideCut_cap_le _ hn (digit_le _ _ _)) (fun ω => abs_sideCut_top _ _ _) (fun ω => abs_sideCut_bot _ _ _)
      (fun ω => abs_A_le _ _)
  | true =>
    exact rowNet_sized' (m := 2) (by norm_num) (Fintype.card_fin g) (Fintype.card_fin g) hα R hR
      (G := fun ω x u y' v => A n (rectDig g true n y (tri ω.1.1 ω.1.2) (tri ω.2.1 ω.2.2)) x y' u v) _ _
      (fun ω => sideCut_factors_col _ _) (fun ω => card_sideCut_lab _ _ _)
      (fun ω => sideCut_cap_le _ hn (digit_le _ _ _)) (fun ω => abs_sideCut_top _ _ _) (fun ω => abs_sideCut_bot _ _ _)
      (fun ω x u y' v => abs_A_le _ _ x y' u v)
end Groundwork.Grid
