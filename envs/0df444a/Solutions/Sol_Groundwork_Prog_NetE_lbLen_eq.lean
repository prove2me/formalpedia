-- Prove2me | solution 1 for Groundwork.Prog.NetE.lbLen_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:08:23.697056+00:00
-- url     : https://prove2.me/submissions/7f2212b4-0db5-4209-910c-ef34d34e51f6

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_NetProg
import Definitions.Def_StepMachines_Prog_NetVal
import Theorems.Thm_Groundwork_Prog_NetE_mem_prsF
import Theorems.Thm_Groundwork_Prog_NetE_nodup_prsF
import Theorems.Thm_Groundwork_Prog_NetE_lbLens_eq
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
variable {c : C} {N : Network (Fin g) (List Bool) (List Bool)} {t S : ℕ}
namespace Groundwork.Prog.NetE
theorem _root_.solution (hK : 0 < K) (hN : Np.Presents c N t S) (x : ℕ) {G G' : Fin K} (hne : G ≠ G') :
    lbLen K g Np c x G.val G'.val = (N.merge (chi hK x) [] []).c G G' := by
  change _ = ∑ p : Fin g × Fin g with chi hK x p.1 = G ∧ chi hK x p.2 = G', N.c p.1 p.2
  rw [lbLen, lbLens_eq, ← List.sum_toFinset _ (nodup_prsF x G.val G'.val)]
  refine Finset.sum_congr ?_ fun p hp => (hN.c_eq p.1 p.2 fun e => ?_).symm
  swap
  · obtain ⟨h1, h2⟩ := (Finset.mem_filter.1 hp).2
    rw [e, h2] at h1
    exact hne h1.symm
  ext p
  simp [mem_prsF, chi_eq_iff]
end Groundwork.Prog.NetE
