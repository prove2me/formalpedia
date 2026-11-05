-- Prove2me | solution 1 for Groundwork.Grid.ZG_cross_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:09:50.676738+00:00
-- url     : https://prove2.me/submissions/68c3bf48-c280-456a-929a-ef323c6df694

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Groundwork_Grid_RowNet
import Definitions.Def_Groundwork_Cross_Bit
import Definitions.Def_Groundwork_Grid_Expand
import Theorems.Thm_Groundwork_sum_A
import Theorems.Thm_Groundwork_sum_tuples_prod

section
namespace Groundwork.Grid
open Finset
variable {ρ γ α : Type}
variable [Fintype ρ] [LinearOrder ρ] [Fintype γ] [LinearOrder γ]
private theorem filter_mem_Ω : (univ.filter fun ω => ω ∈ Ω ρ γ) = Ω ρ γ := by
  ext ω; simp
end Groundwork.Grid
set_option autoImplicit false
section
section
open Groundwork Groundwork.Grid
open Finset
variable {ρ γ α : Type}
variable [Fintype ρ] [LinearOrder ρ] [Fintype γ] [LinearOrder γ]
namespace Groundwork.Grid
theorem _root_.solution {n : ℕ} (R : Inst (ρ × γ) (Bits n)) :
    ZG R (fun _ => Cross.X) = ∑ ι ∈ Pat ρ γ n, ZG R fun ω => A n (ι ω) := by
  unfold ZG
  rw [sum_comm]
  refine sum_congr rfl fun ℓ _ => ?_
  rw [← mul_sum, ← mul_sum]
  congr 2
  have h := sum_tuples_prod (fun ω => ω ∈ Ω ρ γ) (fun _ => range (n + 1)) 0 fun ω i => app (A n i) ℓ ω
  rw [filter_mem_Ω] at h
  rw [Pat, h]
  exact prod_congr rfl fun ω _ => (sum_A _ _ _ _).symm
end Groundwork.Grid
