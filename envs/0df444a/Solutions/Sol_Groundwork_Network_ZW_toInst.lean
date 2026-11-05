-- Prove2me | solution 1 for Groundwork.Network.ZW_toInst
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:01:24.631715+00:00
-- url     : https://prove2.me/submissions/cf777012-2d4c-43b3-b5f3-53016b7d61d7

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_NetProg
import Definitions.Def_StepMachines_Prog_NetVal
import Theorems.Thm_Groundwork_length_toWord
import Theorems.Thm_Groundwork_mem_words
import Theorems.Thm_Groundwork_prod_erase_eq_pairs
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
import Theorems.Thm_Groundwork_sum_tuples_prod
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
open Groundwork
open Finset
namespace Groundwork
namespace Network
theorem _root_.solution {J σ τ : Type*} [Fintype J] [LinearOrder J] (N : Network J σ τ) (ℓ : ℕ) (d : List Bool)
    (D : J → J → Finset (List Bool)) (dec : J → J → List Bool → τ) (hD : ∀ a b, a < b → D a b ⊆ words ℓ)
    (h : ∀ a b, a < b → ∀ F : τ → ℤ, ∑ x ∈ D a b, F (dec a b x) = ∑ θ ∈ N.Θ a b, F θ) :
    Inst.ZW ℓ d (N.toInst D dec) = N.value := by
  unfold Inst.ZW Network.value Network.toInst
  simp only [Finset.prod_univ_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun z _ => ?_
  simp only [Finset.prod_mul_distrib, ← Finset.mul_sum]
  congr 1
  have key : ∀ Λ : J × J → List Bool,
      ∏ a, ∏ b ∈ univ.erase a, (if star Λ a b ∈ D (min a b) (max a b) then
        N.f a b (z a) (dec (min a b) (max a b) (star Λ a b)) else 0) =
      ∏ p : J × J with p.1 < p.2, (if Λ p ∈ D p.1 p.2 then N.f p.1 p.2 (z p.1) (dec p.1 p.2 (Λ p)) else 0) *
        (if Λ p ∈ D p.1 p.2 then N.f p.2 p.1 (z p.2) (dec p.1 p.2 (Λ p)) else 0) := by
    intro Λ
    rw [prod_erase_eq_pairs]
    refine Finset.prod_congr rfl fun p hp => ?_
    have hp' : p.1 < p.2 := by simpa [pairs] using hp
    simp [star, pr, hp'.le]
  simp only [key]
  rw [sum_tuples_prod (fun p : J × J => p.1 < p.2) (fun _ => words ℓ) d
    (fun p x => (if x ∈ D p.1 p.2 then N.f p.1 p.2 (z p.1) (dec p.1 p.2 x) else 0) *
        (if x ∈ D p.1 p.2 then N.f p.2 p.1 (z p.2) (dec p.1 p.2 x) else 0))]
  refine Finset.prod_congr rfl fun p hp => ?_
  have hp' : p.1 < p.2 := by simpa [pairs] using hp
  have h1 : ∀ x, (if x ∈ D p.1 p.2 then N.f p.1 p.2 (z p.1) (dec p.1 p.2 x) else 0) *
        (if x ∈ D p.1 p.2 then N.f p.2 p.1 (z p.2) (dec p.1 p.2 x) else 0) =
      if x ∈ D p.1 p.2 then N.f p.1 p.2 (z p.1) (dec p.1 p.2 x) * N.f p.2 p.1 (z p.2) (dec p.1 p.2 x) else 0 := by
    intro x; split_ifs <;> simp
  simp only [h1]
  rw [Finset.sum_ite_mem, Finset.inter_eq_right.2 (hD _ _ hp'),
    h _ _ hp' (fun θ => N.f p.1 p.2 (z p.1) θ * N.f p.2 p.1 (z p.2) θ)]
  simp [Network.Ψ, Network.lab, hp'.le]
end Network
end Groundwork
