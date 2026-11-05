-- Prove2me | solution 1 for Groundwork.Prog.sideN_f_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:35:05.832202+00:00
-- url     : https://prove2.me/submissions/66851186-8b13-4275-b55e-f929e0af8bf8

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_Side
import Definitions.Def_StepMachines_Prog_SideBasics
import Definitions.Def_StepMachines_Prog_GridCount
import Definitions.Def_StepMachines_Prog_SidePresents
import Theorems.Thm_Groundwork_Prog_prod_counter_pairs
import Theorems.Thm_Groundwork_Prog_prod_sideEdges
import Theorems.Thm_Groundwork_Grid_sideN_f
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
theorem _root_.solution {C : Type} {g : ℕ} {tr : Bool} {lam : C → ℕ} (Rm : Inst (Fin (g * g)) (List Bool)) (c : C) (y : ℕ)
    {a b : Fin g} (hab : a ≠ b) {z θ : List Bool} (hz : z.length = g ^ 3 * lam c)
    (hθ : θ.length = sideCap g tr (lam c) y a b) :
    (sideN g tr (lam c) Rm y).f a b z θ =
      sideFv g tr (lam c) y (sideEdges g tr lam ((c, y), ((a.val, b.val), (z, θ)))) a b z θ := by
  rw [Grid.sideN_f g tr (lam c) Rm y hab hz hθ,
    prod_sideEdges (g := g) (tr := tr) (lam := lam) ((c, y), ((a.val, b.val), (z, θ))), sideFv,
    prod_counter_pairs g fun i i' => Grid.sideItem g tr (lam c) y a b z θ i i']
  split_ifs <;> simp
end Groundwork.Prog
