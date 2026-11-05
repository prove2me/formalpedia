-- Prove2me | solution 1 for Groundwork.Prog.Count.value_congr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:20:50.79923+00:00
-- url     : https://prove2.me/submissions/d770c796-e030-46fc-af9e-5d21e689fb75

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_Spec
import Definitions.Def_StepMachines_Math_SatNet
import Definitions.Def_StepMachines_Prog_CountNet

set_option autoImplicit false
section
open Groundwork Groundwork.Prog
open Finset SatNet
open Groundwork.Prog.Count
variable {g μ k : ℕ} {φ : Fml}
namespace Groundwork.Prog.Count
theorem _root_.solution {J σ τ σ' τ' : Type} [Fintype J] [LinearOrder J] (N : Network J σ τ) (N' : Network J σ' τ')
    (es : σ' → σ) (hS : ∀ a, Set.BijOn es (N'.S a) (N.S a)) (hW : ∀ a z, N'.W a z = N.W a (es z))
    (hΨ : ∀ a b, a < b → ∀ z z', N'.Ψ a b z z' = N.Ψ a b (es z) (es z')) : N'.value = N.value := by
  unfold Network.value
  refine Finset.sum_nbij (fun z a => es (z a)) ?_ ?_ ?_ ?_
  · intro z hz
    rw [Fintype.mem_piFinset] at *
    exact fun a => (hS a).mapsTo (hz a)
  · intro z hz z' hz' h
    funext a
    exact (hS a).injOn (Fintype.mem_piFinset.1 (Finset.mem_coe.1 hz) a) (Fintype.mem_piFinset.1 (Finset.mem_coe.1 hz') a)
      (congrFun h a)
  · intro y hy
    have : ∀ a, ∃ x ∈ N'.S a, es x = y a := fun a => (hS a).surjOn (Fintype.mem_piFinset.1 (Finset.mem_coe.1 hy) a)
    choose x hx hxy using this
    exact ⟨x, Finset.mem_coe.2 (Fintype.mem_piFinset.2 hx), funext hxy⟩
  · intro z _
    congr 1
    · exact Finset.prod_congr rfl fun a _ => hW a _
    · exact Finset.prod_congr rfl fun p hp => hΨ _ _ (Finset.mem_filter.1 hp).2 _ _
end Groundwork.Prog.Count
