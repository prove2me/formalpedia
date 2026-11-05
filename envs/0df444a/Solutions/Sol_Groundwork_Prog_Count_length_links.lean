-- Prove2me | solution 1 for Groundwork.Prog.Count.length_links
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:23:54.159192+00:00
-- url     : https://prove2.me/submissions/5932d1eb-2bf9-4996-a0ac-588adaf55cdb

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_Spec
import Definitions.Def_StepMachines_Math_SatNet
import Definitions.Def_StepMachines_Prog_CountNet
import Theorems.Thm_Groundwork_Prog_Count_loc_lt
import Theorems.Thm_Groundwork_Prog_Count_exists_loc
import Theorems.Thm_Groundwork_Prog_Count_idx_eq
import Theorems.Thm_Groundwork_Prog_Count_linkB_iff
import Theorems.Thm_Groundwork_Prog_Count_mem_links
import Theorems.Thm_Groundwork_Prog_Count_nodup_links
import Theorems.Thm_Groundwork_SatNet_Consec_succ_unique
import Theorems.Thm_Groundwork_SatNet_idx_injective
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
import Theorems.Thm_P2M_Groundwork_SatNet_mul_add_inj__c1cceb82cc73
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
open Groundwork Groundwork.Prog
open Finset SatNet
open Groundwork.Prog.Count
variable {g μ k : ℕ} {φ : Fml}
namespace Groundwork.Prog.Count
theorem _root_.solution (hg : 0 < g) (hm : φ.length ≤ g * mu g φ) (a b : Fin g) :
    (links g k φ a.val b.val).length = #{s : Sl (mu g φ) k | Out φ a b s} := by
  classical
  rw [← List.toFinset_card_of_nodup (nodup_links hg _ _)]
  set A : Finset (Sl (mu g φ) k × Sl (mu g φ) k) := {q | Link φ (a, q.1) (b, q.2)} with hA
  have h1 : ({s : Sl (mu g φ) k | Out φ a b s} : Finset _) = A.image Prod.fst := by
    ext s
    simp only [mem_filter, mem_univ, true_and, mem_image, hA, Prod.exists, exists_and_right, exists_eq_right, Out]
  have h2 : (links g k φ a.val b.val).toFinset = A.image fun q => (loc q.1, loc q.2) := by
    ext ⟨r, r'⟩
    simp only [List.mem_toFinset, mem_links hg, mem_image, hA, mem_filter, mem_univ, true_and, Prod.mk.injEq]
    constructor
    · rintro ⟨hr, hr', hl⟩
      obtain ⟨s, rfl⟩ := exists_loc hr
      obtain ⟨s', rfl⟩ := exists_loc hr'
      rw [← idx_eq, ← idx_eq] at hl
      exact ⟨(s, s'), (linkB_iff hm _ _).1 hl, rfl, rfl⟩
    · rintro ⟨⟨s, s'⟩, hl, rfl, rfl⟩
      refine ⟨loc_lt s, loc_lt s', ?_⟩
      rw [← idx_eq, ← idx_eq]
      exact (linkB_iff hm _ _).2 hl
  have loc_inj : ∀ s s' : Sl (mu g φ) k, loc s = loc s' → s = s' := fun s s' h => by
    obtain ⟨e1, e2⟩ := SatNet.mul_add_inj' s.2.2 s'.2.2 h
    exact Prod.ext (Fin.ext e1) (Fin.ext e2)
  rw [h1, h2, Finset.card_image_of_injOn, Finset.card_image_of_injOn]
  · rintro ⟨s, s'⟩ hq ⟨t, t'⟩ hq' (e : s = t)
    subst e
    have hl : Link φ (a, s) (b, s') := by simpa [hA] using hq
    have hl' : Link φ (a, s) (b, t') := by simpa [hA] using hq'
    have := hl.succ_unique idx_injective hl'
    simp only [Prod.mk.injEq, true_and] at this
    rw [this]
  · rintro ⟨s, s'⟩ _ ⟨t, t'⟩ _ e
    simp only [Prod.mk.injEq] at e
    rw [loc_inj _ _ e.1, loc_inj _ _ e.2]
end Groundwork.Prog.Count
