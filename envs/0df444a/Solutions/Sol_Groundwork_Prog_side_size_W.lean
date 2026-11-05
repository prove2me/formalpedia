-- Prove2me | solution 1 for Groundwork.Prog.side_size_W
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:27:52.987384+00:00
-- url     : https://prove2.me/submissions/db7ba5b4-ca18-425c-b952-37b33df93378

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_Side
import Definitions.Def_StepMachines_Prog_SideBasics
import Definitions.Def_StepMachines_Prog_GridCount
import Definitions.Def_StepMachines_Prog_SidePresents
import Theorems.Thm_Groundwork_Prog_sideA_mul
import Theorems.Thm_Groundwork_Prog_side_size_of
import Theorems.Thm_Groundwork_Prog_size_pattern_le
import Theorems.Thm_Groundwork_Prog_size_bools
import Theorems.Thm_Groundwork_Prog_size_nat_le
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
open Groundwork Groundwork.Prog
open Finset Stepped
open Groundwork.Grid (he node c2 sideN sideCap)
namespace Groundwork.Prog
theorem _root_.solution {C : Type} [HasSize C] (g B S lm : ℕ) (hl : 1 ≤ lm) (c : C) {y a : ℕ} {z : List Bool}
    (hy : y < (lm + 1) ^ nRect g) (ha : a < g) (hz : z.length = g ^ 3 * lm) :
    size ((c, y), (a, z)) + size g + (B * g + 2) + S + 3 ≤ S + sideA g * (size c + B + lm) ^ sideA g := by
  refine side_size_of ?_
  have h3 := sideA_mul g (size c + B + lm)
  have hY := size_pattern_le hy
  have e4 : g ^ 4 * (size c + B + lm) = g ^ 4 * size c + g ^ 4 * B + g ^ 4 * lm := by ring
  have e3 : g ^ 3 * (size c + B + lm) = g ^ 3 * size c + g ^ 3 * B + g ^ 3 * lm := by ring
  have e1 : g * (size c + B + lm) = g * size c + B * g + g * lm := by ring
  have hg : g ≤ g * lm := Nat.le_mul_of_pos_right _ hl
  have s1 := size_nat_le a
  have s2 := size_nat_le g
  simp only [size_prod, size_bools, hz]
  omega
end Groundwork.Prog
