-- Prove2me | solution 1 for Groundwork.Prog.NetE.toInst_eq_mergedVal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:04:47.804372+00:00
-- url     : https://prove2.me/submissions/42ca308b-6d94-4447-a872-06353b238290

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_NetProg
import Definitions.Def_StepMachines_Prog_NetVal
import Theorems.Thm_P2M_Groundwork_tuples_congr__2a63300181ad
import Theorems.Thm_Groundwork_Prog_NetE_nodup_membersF
import Theorems.Thm_Groundwork_Prog_NetE_mem_membersF
import Theorems.Thm_Groundwork_Prog_NetE_stLens_eq
import Theorems.Thm_Groundwork_Prog_NetE_zAt_eq_cut
import Theorems.Thm_Groundwork_Prog_NetE_chi_eq_iff
import Theorems.Thm_Groundwork_Prog_NetE_prod_termVal
import Theorems.Thm_Groundwork_Prog_NetE_validB_iff
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
import Theorems.Thm_Groundwork_sum_cut_toWord
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
theorem _root_.solution (hK : 0 < K) {c : C} {N : Network (Fin g) (List Bool) (List Bool)} {t S : ℕ}
    (hN : Np.Presents c N t S) (x β : ℕ) (G : Fin K) (θ : Fin K → List Bool)
    (hθ : ∀ G', G' ≠ G → (θ G').length = β) :
    (N.merge (chi hK x) [] []).toInst (mD K g Np c x β) (mdec K g Np c x) G θ =
      mergedVal K g Np N ((c, x), (G.val, List.ofFn θ)) := by
  unfold mergedVal
  by_cases hv : validB K g Np ((c, x), (G.val, List.ofFn θ)) = true
  · rw [if_pos hv]
    have hv' := (validB_iff Np c x β G θ hθ).1 hv
    unfold Network.toInst
    have hS : (N.merge (chi hK x) [] []).S G =
        tuples (fun a => chi hK x a = G) (fun a : Fin g => words (Np.n c a.val)) [] := by
      change tuples (fun a => chi hK x a = G) N.S [] = _
      exact tuples_congr' _ [] fun a _ => hN.S_eq a
    have hlen : ((membersF K x G.val : List (Fin g)).map fun a => Np.n c a.val).sum = stLen K g Np c x G.val := by
      rw [stLen, stLens_eq]
    rw [hS, ← sum_cut_toWord (fun a => chi hK x a = G) (membersF K x G.val) (nodup_membersF x G.val)
      (fun a => by rw [mem_membersF, chi_eq_iff]), hlen]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [prod_termVal Np hK hN x G θ y
      (cut (fun a : Fin g => Np.n c a.val) [] (membersF K x G.val) (toWord (stLen K g Np c x G.val) y))
      (fun a => (zAt_eq_cut Np c x G.val _ a).symm)]
    congr 1
    refine Finset.prod_congr rfl fun G' hG' => ?_
    rw [if_pos (hv' G' (by simpa using hG'))]
    rfl
  · rw [if_neg hv]
    obtain ⟨G', hne, hG'⟩ : ∃ G', G' ≠ G ∧ θ G' ∉ mD K g Np c x β (min G G') (max G G') := by
      by_contra hcon
      push Not at hcon
      exact hv ((validB_iff Np c x β G θ hθ).2 hcon)
    unfold Network.toInst
    refine Finset.sum_eq_zero fun Z _ => ?_
    rw [Finset.prod_eq_zero (i := G') (by simp [hne]) (if_neg hG'), mul_zero]
end Groundwork.Prog.NetE
