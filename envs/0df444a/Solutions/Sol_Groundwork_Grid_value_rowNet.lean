-- Prove2me | solution 1 for Groundwork.Grid.value_rowNet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:15:10.636205+00:00
-- url     : https://prove2.me/submissions/a45e34bc-7fed-4c16-9bd0-4e00f8178e44

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Groundwork_Grid_Grid
import Definitions.Def_Groundwork_Grid_RowNet
import Theorems.Thm_Groundwork_Grid_ZG_eq_rows
import Theorems.Thm_P2M_Groundwork_Grid_rowNet___43280a58588e

set_option autoImplicit false
section
section
open Groundwork Groundwork.Grid
open Finset
variable {ρ γ α τ : Type}
variable [Fintype ρ] [LinearOrder ρ] [Fintype γ] [LinearOrder γ] [Fintype α] [DecidableEq α]
namespace Groundwork.Grid
theorem _root_.solution {G : Rect ρ γ → α → α → α → α → ℤ} {C : Rect ρ γ → Cut α τ} (h : ∀ ω, (C ω).Factors (G ω))
    (R : Inst (ρ × γ) α) (t₀ : τ) (L : ℕ) : (rowNet R C t₀ L).value = ZG R G := by
  rw [ZG_eq_rows]
  unfold Network.value
  have hS : Fintype.piFinset (rowNet R C t₀ L).S = univ := by simp [rowNet]
  rw [hS]
  refine sum_congr rfl fun z _ => congrArg₂ (· * ·) rfl (prod_congr rfl fun p hp => ?_)
  exact rowNet_Ψ h R t₀ L (by simpa [pairs] using hp) _ _
end Groundwork.Grid
