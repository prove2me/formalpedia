-- Prove2me | solution 1 for Groundwork.Prog.NetE.sum_mdec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:02:44.577181+00:00
-- url     : https://prove2.me/submissions/da7d375b-9f72-4620-95a6-66493660e78d

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_NetProg
import Definitions.Def_StepMachines_Prog_NetVal
import Theorems.Thm_Groundwork_cut_take
import Theorems.Thm_Groundwork_Prog_NetE_mem_prsF
import Theorems.Thm_Groundwork_Prog_NetE_nodup_prsF
import Theorems.Thm_Groundwork_Prog_NetE_lbLens_eq
import Theorems.Thm_Groundwork_Prog_NetE_lAt_eq_cut
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
import Theorems.Thm_Groundwork_sum_cut
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
theorem _root_.solution (hK : 0 < K) (c : C) (x β : ℕ) (G G' : Fin K) (hβ : lbLen K g Np c x G G' ≤ β)
    (F : (Fin g × Fin g → List Bool) → ℤ) :
    ∑ θ ∈ mD K g Np c x β G G', F (mdec K g Np c x G G' θ) =
      ∑ t ∈ tuples (fun p : Fin g × Fin g => chi hK x p.1 = G ∧ chi hK x p.2 = G')
        (fun p => words (Np.cap c p.1.val p.2.val)) [], F t := by
  have hlen : lbLen K g Np c x G G' =
      ((prsF K x G G' : List (Fin g × Fin g)).map fun p => Np.cap c p.1.val p.2.val).sum := by
    rw [lbLen, lbLens_eq]
  rw [← sum_cut (fun p : Fin g × Fin g => chi hK x p.1 = G ∧ chi hK x p.2 = G') (prsF K x G G')
    (nodup_prsF x G G') (fun p => by rw [mem_prsF]; simp [chi, Fin.ext_iff]), ← hlen]
  have hdec : ∀ θ, mdec K g Np c x G G' θ =
      cut (fun p : Fin g × Fin g => Np.cap c p.1.val p.2.val) [] (prsF K x G G') θ := by
    intro θ; funext p; exact lAt_eq_cut Np c x G G' θ p
  simp only [hdec]
  refine Finset.sum_nbij' (fun θ => θ.take (lbLen K g Np c x G G'))
    (fun w => w ++ List.replicate (β - lbLen K g Np c x G G') false) ?_ ?_ ?_ ?_ ?_
  · intro θ hθ
    simp only [mD, mem_filter, mem_words] at hθ
    simp only [mem_words, List.length_take]
    omega
  · intro w hw
    simp only [mem_words] at hw
    simp only [mD, mem_filter, mem_words, List.length_append, List.length_replicate]
    refine ⟨by omega, ?_⟩
    rw [← hw, List.drop_left]
    simp
  · intro θ hθ
    simp only [mD, mem_filter, mem_words] at hθ
    have h1 : θ.drop (lbLen K g Np c x G G') = List.replicate (β - lbLen K g Np c x G G') false := by
      rw [List.eq_replicate_iff]
      refine ⟨by rw [List.length_drop, hθ.1], fun b hb => ?_⟩
      have := List.all_eq_true.1 hθ.2 b hb
      simpa using this
    rw [← h1, List.take_append_drop]
  · intro w hw
    simp only [mem_words] at hw
    rw [← hw, List.take_left]
  · intro θ _
    rw [hlen, cut_take]
end Groundwork.Prog.NetE
