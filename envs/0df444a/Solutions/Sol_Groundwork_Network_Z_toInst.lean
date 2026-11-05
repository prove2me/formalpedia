-- Prove2me | solution 1 for Groundwork.Network.Z_toInst
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:44:41.083861+00:00
-- url     : https://prove2.me/submissions/d1f848e5-48ae-4b9c-86bb-00d0f5f5a9c0

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Groundwork_Net_Defs
import Definitions.Def_Groundwork_Net_Calculus
import Definitions.Def_Groundwork_Net_Net
import Theorems.Thm_Groundwork_prod_erase_eq_pairs
import Theorems.Thm_Groundwork_pr_of_lt
import Theorems.Thm_Groundwork_sum_renamed
import Theorems.Thm_Groundwork_sum_tuples_prod


set_option autoImplicit false
section
open Groundwork
open Finset
variable {J J' σ τ A A' : Type*}
open Groundwork.Network
namespace Groundwork.Network
theorem _root_.solution [Fintype J] [LinearOrder J] [Fintype A] [DecidableEq A] (N : Network J σ τ)
    (D : J → J → Finset A) (dec : J → J → A → τ) (h : ∀ a b, a < b → Set.BijOn (dec a b) (D a b) (N.Θ a b)) (d : A) :
    (N.toInst D dec).Z d = N.value := by
  unfold Inst.Z value toInst
  simp only [Finset.prod_univ_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun z _ => ?_
  simp only [Finset.prod_mul_distrib, ← Finset.mul_sum]
  congr 1
  have key : ∀ Λ : J × J → A,
      ∏ a, ∏ b ∈ univ.erase a, (if star Λ a b ∈ D (min a b) (max a b) then
        N.f a b (z a) (dec (min a b) (max a b) (star Λ a b)) else 0) =
      ∏ p : J × J with p.1 < p.2, (if Λ p ∈ D p.1 p.2 then N.f p.1 p.2 (z p.1) (dec p.1 p.2 (Λ p)) else 0) *
        (if Λ p ∈ D p.1 p.2 then N.f p.2 p.1 (z p.2) (dec p.1 p.2 (Λ p)) else 0) := by
    intro Λ
    rw [prod_erase_eq_pairs]
    refine Finset.prod_congr rfl fun p hp => ?_
    have hp' : p.1 < p.2 := by simpa [pairs] using hp
    simp [star, pr_of_lt hp', hp'.le]
  simp only [key]
  rw [labellings, sum_tuples_prod (fun p : J × J => p.1 < p.2) (fun _ => univ) d
    (fun p x => (if x ∈ D p.1 p.2 then N.f p.1 p.2 (z p.1) (dec p.1 p.2 x) else 0) *
        (if x ∈ D p.1 p.2 then N.f p.2 p.1 (z p.2) (dec p.1 p.2 x) else 0))]
  refine Finset.prod_congr rfl fun p hp => ?_
  have hp' : p.1 < p.2 := by simpa [pairs] using hp
  rw [sum_renamed (D p.1 p.2) (dec p.1 p.2) (N.Θ p.1 p.2) (h _ _ hp')]
  simp [Ψ, lab, hp'.le]
end Groundwork.Network
