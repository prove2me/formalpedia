-- Prove2me | solution 1 for Groundwork.Grid.Z_eq_ZG_X
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:14:45.266025+00:00
-- url     : https://prove2.me/submissions/737b225f-4566-4e24-8f6c-1b5c684f2c7e

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Groundwork_Grid_Defs
import Definitions.Def_Groundwork_Net_Net
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_Groundwork_Grid_Grid
import Theorems.Thm_Groundwork_Grid_boole_congr
import Theorems.Thm_Groundwork_Grid_symm_eq_prod
import Theorems.Thm_P2M_Groundwork_Grid_prod___rows_436f8d628931
import Theorems.Thm_Groundwork_Grid_Z_eq_symm

set_option autoImplicit false
section
section
open Groundwork Groundwork.Grid
open Finset
variable {J ρ γ α : Type}
variable [Fintype ρ] [LinearOrder ρ] [Fintype γ] [LinearOrder γ] [Fintype α] [DecidableEq α]
namespace Groundwork.Grid
theorem _root_.solution [Fintype J] [LinearOrder J] (R : Inst J α) (d : α) (e : J ≃ ρ × γ) :
    R.Z d = ZG (onGrid R d e) (fun _ => Cross.X) := by
  rw [Z_eq_symm]
  unfold ZG
  refine Fintype.sum_equiv (e.arrowCongr (e.arrowCongr (Equiv.refl _))) _ _ fun ℓ => ?_
  rw [← symm_eq_prod]
  congr 1
  · refine Fintype.prod_equiv e _ _ fun w => ?_
    simp [onGrid, Equiv.arrowCongr, Function.comp_def]
  · refine boole_congr ⟨fun h w w' => ?_, fun h w w' => ?_⟩
    · simp [Equiv.arrowCongr, h]
    · simpa [Equiv.arrowCongr] using h (e w) (e w')
end Groundwork.Grid
