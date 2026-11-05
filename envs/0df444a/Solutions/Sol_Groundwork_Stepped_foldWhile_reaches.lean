-- Prove2me | solution 1 for Groundwork.Stepped.foldWhile_reaches
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:44:42.290609+00:00
-- url     : https://prove2.me/submissions/f0ace15d-049d-490b-ab4f-72bb67679c64

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachineStatements
import Definitions.Def_StepMachines_Prog_Stepped
import Theorems.Thm_Groundwork_size_nat
import Theorems.Thm_Groundwork_size_int
import Theorems.Thm_Groundwork_size_bool
import Theorems.Thm_Groundwork_size_unit
import Theorems.Thm_Groundwork_size_prod
import Theorems.Thm_Groundwork_size_inl
import Theorems.Thm_Groundwork_size_inr
import Theorems.Thm_Groundwork_size_none
import Theorems.Thm_Groundwork_size_some
import Theorems.Thm_Groundwork_size_list
import Theorems.Thm_Groundwork_Stepped_foldWhile_body
attribute [local simp] Groundwork.size_nat
attribute [local simp] Groundwork.size_int
attribute [local simp] Groundwork.size_bool
attribute [local simp] Groundwork.size_unit
attribute [local simp] Groundwork.size_prod
attribute [local simp] Groundwork.size_inl
attribute [local simp] Groundwork.size_inr
attribute [local simp] Groundwork.size_none
attribute [local simp] Groundwork.size_some
attribute [local simp] Groundwork.size_list

set_option autoImplicit false
section
open Groundwork
open Groundwork.Stepped
variable {α β γ τ : Type}
variable [HasSize τ] [HasSize γ] {start : α → Option τ} {nxt : τ → Option τ} {M : Stepped τ β}
  {g : γ → τ → β → γ} {c₀ : α → γ}
namespace Groundwork.Stepped
theorem _root_.solution {xs : List τ} {o : Option τ} (ho : Orbit nxt o xs) (t : τ → ℕ) (v : τ → β)
    (Sx Sc Sm : ℕ) (c : γ) (hM : ∀ x ∈ xs, M.Runs x (t x) Sm (v x)) (hx : ∀ x ∈ xs, size x ≤ Sx)
    (hc : ∀ l, l <+: xs → size (l.foldl (fun c x => g c x (v x)) c) ≤ Sc) :
    (foldWhile start nxt M g c₀).Reaches (Sx + (Sc + Sm) + 1) (xs.foldl (fun c x => g c x (v x)) c)
      (foldGo M c o) (xs.map fun x => t x + 1).sum := by
  induction ho generalizing c with
  | nil =>
    have := hc [] (List.nil_prefix)
    exact .halt rfl (by change size c + 1 ≤ _; simp only [List.foldl_nil] at this; omega)
  | @cons x xs _ ih =>
    simp only [List.map_cons, List.sum_cons, List.foldl_cons]
    refine foldWhile_body (hM x List.mem_cons_self) ?_
      (ih (g c x (v x)) (fun y hy => hM y (List.mem_cons_of_mem _ hy))
        (fun y hy => hx y (List.mem_cons_of_mem _ hy))
        fun l hl => by simpa using hc (x :: l) ((List.prefix_cons_inj x).2 hl))
    have h1 := hx x List.mem_cons_self
    have h2 := hc [] List.nil_prefix
    simp only [List.foldl_nil] at h2
    omega
end Groundwork.Stepped
