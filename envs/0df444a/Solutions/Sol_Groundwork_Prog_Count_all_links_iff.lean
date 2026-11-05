-- Prove2me | solution 1 for Groundwork.Prog.Count.all_links_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:23:49.891405+00:00
-- url     : https://prove2.me/submissions/9e452029-8465-4a8d-8181-4423f504c0b0

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
open Groundwork Groundwork.Prog
open Finset SatNet
open Groundwork.Prog.Count
variable {g μ k : ℕ} {φ : Fml}
namespace Groundwork.Prog.Count
theorem _root_.solution (hg : 0 < g) (hm : φ.length ≤ g * mu g φ) (a b : Fin g) (P : ℕ → ℕ → Bool) :
    ((links g k φ a.val b.val).all fun p => P p.1 p.2) = true ↔
      ∀ s s' : Sl (mu g φ) k, Link φ (a, s) (b, s') → P (loc s) (loc s') = true := by
  simp only [List.all_eq_true, mem_links hg]
  constructor
  · intro h s s' hl
    refine h (loc s, loc s') ⟨loc_lt s, loc_lt s', ?_⟩
    rw [← idx_eq, ← idx_eq]
    exact (linkB_iff hm _ _).2 hl
  · rintro h ⟨r, r'⟩ ⟨h1, h2, h3⟩
    obtain ⟨s, rfl⟩ := exists_loc h1
    obtain ⟨s', rfl⟩ := exists_loc h2
    simp only [← idx_eq] at h3
    exact h s s' ((linkB_iff hm _ _).1 h3)
end Groundwork.Prog.Count
