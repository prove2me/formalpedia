-- Prove2me | solution 1 for Groundwork.Grid.ZG_tr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:56:00.311227+00:00
-- url     : https://prove2.me/submissions/dff3d569-e027-49bc-8db4-d87c28a7ce70

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Groundwork_Grid_RowNet
import Definitions.Def_Groundwork_Cross_Bit
import Definitions.Def_Groundwork_Grid_Expand

set_option autoImplicit false
section
section
open Groundwork Groundwork.Grid
open Finset
variable {ρ γ α : Type}
variable [Fintype ρ] [LinearOrder ρ] [Fintype γ] [LinearOrder γ]
namespace Groundwork.Grid
theorem _root_.solution [Fintype α] [DecidableEq α] (R : Inst (ρ × γ) α) (G : Rect ρ γ → α → α → α → α → ℤ) :
    ZG (trInst R) (trG G) = ZG R G := by
  unfold ZG
  refine (Fintype.sum_equiv (trHalf ρ γ α) _ _ fun ℓ => ?_).symm
  have h1 : ∏ w, trInst R w (trHalf ρ γ α ℓ w) = ∏ w, R w (ℓ w) :=
    (Fintype.prod_equiv (Equiv.prodComm ρ γ) _ _ fun _ => rfl).symm
  have h2 : ∏ ω ∈ Ω γ ρ, app (trG G ω) (trHalf ρ γ α ℓ) ω = ∏ ω ∈ Ω ρ γ, app (G ω) ℓ ω :=
    (prod_equiv (Equiv.prodComm (ρ × ρ) (γ × γ)) (fun ω => by simp [Ω, and_comm]) fun _ _ => rfl).symm
  rw [h1, h2]
  congr 2
  exact mul_comm _ _
end Groundwork.Grid
