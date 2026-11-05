-- Prove2me | solution 1 for Groundwork.Grid.Z_eq_symm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:11:41.263633+00:00
-- url     : https://prove2.me/submissions/011f3445-575d-44d2-a682-407bdd5ed14a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Groundwork_Grid_Defs
import Definitions.Def_Groundwork_Net_Net
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_Groundwork_Grid_Grid
import Theorems.Thm_Groundwork_Grid_prod_ind
import Theorems.Thm_P2M_Groundwork_Grid_prod___rows_436f8d628931
import Theorems.Thm_Groundwork_Grid_mem_halfEdges
import Theorems.Thm_Groundwork_Inst_Z_eq_halfEdges


set_option autoImplicit false
section
section
open Groundwork Groundwork.Grid
open Finset
variable {J ρ γ α : Type}
variable [Fintype ρ] [LinearOrder ρ] [Fintype γ] [LinearOrder γ] [Fintype α] [DecidableEq α]
namespace Groundwork.Grid
theorem _root_.solution [Fintype J] [LinearOrder J] (R : Inst J α) (d : α) :
    R.Z d = ∑ ℓ : J → J → α, (∏ w, if ℓ w w = d then R w (ℓ w) else 0) *
      (if ∀ w w', ℓ w w' = ℓ w' w then 1 else 0) := by
  rw [Inst.Z_eq_halfEdges, ← Finset.sum_subset (Finset.subset_univ
    (Fintype.piFinset fun w : J => tuples (fun w' => w' ≠ w) (fun _ => (univ : Finset α)) d))]
  · refine sum_congr rfl fun ℓ hℓ => ?_
    have hd := (mem_halfEdges d ℓ).1 hℓ
    congr 1
    · simp [hd]
    · refine prod_ind _ _ ⟨fun h p _ => h _ _, fun h w w' => ?_⟩
      rcases lt_trichotomy w w' with hw | hw | hw
      · exact h (w, w') (by simp [pairs, hw])
      · rw [hw]
      · exact (h (w', w) (by simp [pairs, hw])).symm
  · intro ℓ _ hℓ
    rw [mem_halfEdges] at hℓ
    push Not at hℓ
    obtain ⟨w, hw⟩ := hℓ
    rw [Finset.prod_eq_zero (mem_univ w) (by simp [hw]), zero_mul]
end Groundwork.Grid
