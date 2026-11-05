-- Prove2me | solution 1 for Groundwork.Prog.NetE.prod_termVal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:03:45.809025+00:00
-- url     : https://prove2.me/submissions/d1368130-a70f-4575-a09f-261d379ce547

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_NetProg
import Definitions.Def_StepMachines_Prog_NetVal
import Theorems.Thm_Groundwork_prod_range_mul_self
import Theorems.Thm_Groundwork_Prog_NetE_termVal_pair
import Theorems.Thm_Groundwork_Prog_NetE_chi_eq_iff
import Theorems.Thm_Groundwork_Prog_NetE_labOf_eq_mdec
import Theorems.Thm_Groundwork_length_toWord
import Theorems.Thm_Groundwork_mem_words
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
open Groundwork.Prog Groundwork.Prog.NetE
variable {C : Type} {K g : ℕ} (Np : PNet C)
namespace Groundwork.Prog.NetE
theorem _root_.solution (hK : 0 < K) {c : C} {N : Network (Fin g) (List Bool) (List Bool)} {t S : ℕ}
    (hN : Np.Presents c N t S) (x : ℕ) (G : Fin K) (θ : Fin K → List Bool) (y : ℕ) (Z : Fin g → List Bool)
    (hZ : ∀ a : Fin g, Z a = zA K g Np (((c, x), (G.val, List.ofFn θ)), y) a) :
    ∏ i ∈ range (g * g), termVal K g Np N ((((c, x), (G.val, List.ofFn θ)), y), i) =
      ((∏ a with chi hK x a = G, N.W a (Z a)) *
        ∏ p ∈ pairs (Fin g) with chi hK x p.1 = G ∧ chi hK x p.2 = G, N.Ψ p.1 p.2 (Z p.1) (Z p.2)) *
      ∏ G' ∈ univ.erase G, ∏ p : Fin g × Fin g with chi hK x p.1 = G ∧ chi hK x p.2 = G',
        N.f p.1 p.2 (Z p.1) (mdec K g Np c x (min G G') (max G G') (θ G') (if G < G' then p else p.swap)) := by
  rw [prod_range_mul_self]
  simp only [termVal_pair Np hN, ← hZ]
  have hT : ∀ p : Fin g × Fin g,
      (if col K x p.1 ≠ G.val ∨ (col K x p.2 = G.val ∧ p.2 < p.1) then (1 : ℤ)
      else if p.1 = p.2 then N.W p.1 (Z p.1)
      else if col K x p.2 = G.val then N.Ψ p.1 p.2 (Z p.1) (Z p.2)
      else N.f p.1 p.2 (Z p.1) (labOf K g Np ((c, x), (G.val, List.ofFn θ)) p.1 p.2)) =
      ((if chi hK x p.1 = G ∧ p.1 = p.2 then N.W p.1 (Z p.1) else 1) *
       (if p.1 < p.2 ∧ (chi hK x p.1 = G ∧ chi hK x p.2 = G) then N.Ψ p.1 p.2 (Z p.1) (Z p.2) else 1)) *
       (if chi hK x p.1 = G ∧ chi hK x p.2 ≠ G then
          N.f p.1 p.2 (Z p.1) (labOf K g Np ((c, x), (G.val, List.ofFn θ)) p.1 p.2) else 1) := by
    rintro ⟨a, b⟩
    simp only [chi_eq_iff, ne_eq]
    by_cases h1 : col K x a = G.val
    · by_cases h2 : a = b
      · subst h2; simp [h1]
      · by_cases h3 : col K x b = G.val
        · rcases lt_or_gt_of_ne h2 with h4 | h4
          · simp [h1, h2, h3, h4, h4.not_gt]
          · simp [h1, h2, h3, h4, h4.not_gt]
        · simp [h1, h2, h3]
    · simp [h1]
  simp only [hT, Finset.prod_mul_distrib]
  congr 1
  · congr 1
    · rw [Fintype.prod_prod_type, Finset.prod_filter]
      refine Finset.prod_congr rfl fun a _ => ?_
      by_cases h : chi hK x a = G
      · simp [h]
      · simp [h]
    · rw [pairs, Finset.filter_filter, Finset.prod_filter]
  · rw [← Finset.prod_filter, ← Finset.prod_fiberwise_of_maps_to
      (s := univ.filter fun p : Fin g × Fin g => chi hK x p.1 = G ∧ chi hK x p.2 ≠ G) (t := univ.erase G)
      (g := fun p => chi hK x p.2) (by intro p; simp)]
    refine Finset.prod_congr rfl fun G' hG' => ?_
    have hne : G' ≠ G := by simpa using hG'
    rw [Finset.filter_filter]
    have hset : (univ.filter fun p : Fin g × Fin g => (chi hK x p.1 = G ∧ chi hK x p.2 ≠ G) ∧ chi hK x p.2 = G') =
        univ.filter fun p : Fin g × Fin g => chi hK x p.1 = G ∧ chi hK x p.2 = G' := by
      refine Finset.filter_congr fun p _ => ?_
      constructor
      · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
      · rintro ⟨h1, h3⟩; exact ⟨⟨h1, h3 ▸ hne⟩, h3⟩
    rw [hset]
    refine Finset.prod_congr rfl fun p hp => ?_
    rw [labOf_eq_mdec Np hK c x G G' hne θ p (Finset.mem_filter.1 hp).2.2]
end Groundwork.Prog.NetE
