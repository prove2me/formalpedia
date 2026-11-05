-- Prove2me | solution 1 for Groundwork.Inst.Z_eq_halfEdges
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:47:06.886773+00:00
-- url     : https://prove2.me/submissions/9a8c4edc-5e49-4d87-845d-1d9662b8d2dc

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Groundwork_Net_Defs
import Definitions.Def_Groundwork_Net_Calculus
import Definitions.Def_Groundwork_Net_Net
import Theorems.Thm_Groundwork_Inst_Z_eq_value

set_option autoImplicit false
section
open Groundwork
open Finset
variable {J J' σ τ A A' : Type*}
namespace Groundwork
namespace Inst
theorem _root_.solution [Fintype J] [LinearOrder J] [Fintype A] [DecidableEq A] (R : Inst J A) (d : A) :
    R.Z d = ∑ ℓ ∈ Fintype.piFinset fun w : J => tuples (fun w' => w' ≠ w) (fun _ => (univ : Finset A)) d,
      (∏ w, R w (ℓ w)) * ∏ p ∈ pairs J, if ℓ p.1 p.2 = ℓ p.2 p.1 then 1 else 0 := by
  rw [Inst.Z_eq_value]
  unfold Network.value
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  congr 1
  refine Finset.prod_congr rfl fun p _ => ?_
  simp [Network.Ψ, Network.lab, Inst.net]
end Inst
end Groundwork
