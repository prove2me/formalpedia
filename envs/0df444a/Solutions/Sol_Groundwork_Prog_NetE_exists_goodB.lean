-- Prove2me | solution 1 for Groundwork.Prog.NetE.exists_goodB
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:05:00.341353+00:00
-- url     : https://prove2.me/submissions/295b634f-8f29-4a16-bf55-dccd99707884

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_NetProg
import Definitions.Def_StepMachines_Prog_NetVal
import Theorems.Thm_Groundwork_Prog_NetE_rowSum_eq
import Theorems.Thm_Groundwork_Prog_NetE_Uc_eq
import Theorems.Thm_Groundwork_Prog_NetE_rowSum_le_Pc
import Theorems.Thm_Groundwork_Prog_NetE_goodB_iff
import Theorems.Thm_Groundwork_Colouring_exists_colouring_beta
import Theorems.Thm_Groundwork_Network_merge_c
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
variable {c : C} {N : Network (Fin g) (List Bool) (List Bool)} {t S : ℕ}
namespace Groundwork.Prog.NetE
theorem _root_.solution (hK : 2 ≤ K) (hg : 3 * K ^ 8 ≤ g) (hN : Np.Presents c N t S) {P B : ℕ}
    (hS : N.Sized P B) : ∃ x < K ^ g, goodB K g Np (c, x) = true := by
  have hK0 : 0 < K := by omega
  obtain ⟨χ, h1, h2⟩ := Colouring.exists_colouring_beta hK hg N.c hS.c_symm (Pc g Np c) (fun a => by
    rw [Finset.filter_ne', ← rowSum_eq Np hN]
    exact rowSum_le_Pc Np a)
  have hχ : chi hK0 (finFunctionFinEquiv χ).val = χ := by
    funext a
    have := congrFun (finFunctionFinEquiv.symm_apply_apply χ) a
    rw [← this]
    rfl
  refine ⟨(finFunctionFinEquiv χ).val, (finFunctionFinEquiv χ).2, (goodB_iff Np hK0 hN _).2 ?_⟩
  rw [hχ]
  refine ⟨h1, fun G G' hne => ?_⟩
  rw [Network.merge_c, betaC, Uc_eq Np hN, Network.U]
  have := h2 G G' hne
  simp only [Finset.filter_ne'] at this
  exact this
end Groundwork.Prog.NetE
