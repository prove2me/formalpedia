-- Prove2me | solution 1 for Groundwork.Prog.NetE.labOf_eq_mdec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:01:54.104242+00:00
-- url     : https://prove2.me/submissions/1341c030-562c-49c7-a812-bb5e110466f8

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_NetProg
import Definitions.Def_StepMachines_Prog_NetVal
import Theorems.Thm_Groundwork_Prog_NetE_getD_ofFn
import Theorems.Thm_Groundwork_Prog_NetE_chi_eq_iff
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
open Groundwork
open Finset
open Groundwork.Prog Groundwork.Prog.NetE
variable {C : Type} {K g : ℕ} (Np : PNet C)
namespace Groundwork.Prog.NetE
theorem _root_.solution (hK : 0 < K) (c : C) (x : ℕ) (G G' : Fin K) (hne : G' ≠ G) (θ : Fin K → List Bool)
    (p : Fin g × Fin g) (hp : chi hK x p.2 = G') :
    labOf K g Np ((c, x), (G.val, List.ofFn θ)) p.1 p.2 =
      mdec K g Np c x (min G G') (max G G') (θ G') (if G < G' then p else p.swap) := by
  have hc := (chi_eq_iff hK x p.2 G').1 hp
  unfold labOf mdec
  simp only [hc, getD_ofFn, Fin.val_fin_lt]
  split_ifs with h
  · rw [min_eq_left h.le, max_eq_right h.le]
  · have h' : G' < G := lt_of_le_of_ne (not_lt.1 h) hne
    rw [min_eq_right h'.le, max_eq_left h'.le]
    rfl
end Groundwork.Prog.NetE
