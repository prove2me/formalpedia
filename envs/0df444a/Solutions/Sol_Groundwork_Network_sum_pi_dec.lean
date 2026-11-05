-- Prove2me | solution 1 for Groundwork.Network.sum_pi_dec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:13:25.584191+00:00
-- url     : https://prove2.me/submissions/e771c444-616c-4861-a152-a39652eb2e25

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Math_Code
import Definitions.Def_StepMachines_Math_Pull

set_option autoImplicit false
section
open Groundwork
open Finset
open Groundwork.Network
variable {J σ τ : Type*}
variable [Fintype J] [LinearOrder J] (N : Network J σ τ) (n : J → ℕ) (cs : ∀ a, Code (N.S a) (n a))
  (cl : ∀ a b, Code (N.Θ a b) (N.c a b))
namespace Groundwork.Network
theorem _root_.solution {S : J → Finset σ} (cs : ∀ a, Code (S a) (n a)) (F : (J → σ) → ℤ) :
    ∑ z ∈ Fintype.piFinset fun a => (cs a).D, F (fun a => (cs a).dec (z a)) = ∑ x ∈ Fintype.piFinset S, F x := by
  refine Finset.sum_nbij (fun z a => (cs a).dec (z a)) ?_ ?_ ?_ fun _ _ => rfl
  · intro z hz
    rw [Fintype.mem_piFinset] at hz ⊢
    exact fun a => (cs a).bij.mapsTo (hz a)
  · intro z hz z' hz' h
    rw [Finset.mem_coe, Fintype.mem_piFinset] at hz hz'
    funext a
    exact (cs a).bij.injOn (hz a) (hz' a) (congrFun h a)
  · intro x hx
    rw [Finset.mem_coe, Fintype.mem_piFinset] at hx
    choose w hw hwx using fun a => (cs a).bij.surjOn (hx a)
    exact ⟨w, by rw [Finset.mem_coe, Fintype.mem_piFinset]; exact hw, funext hwx⟩
end Groundwork.Network
