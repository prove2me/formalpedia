-- Prove2me | solution 1 for Groundwork.SatNet.term_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:21:24.00521+00:00
-- url     : https://prove2.me/submissions/50846abf-47df-42bc-8ab1-fec6a8463a7b

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThreeSatStatement
import Definitions.Def_Groundwork_Net_Defs
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Definitions.Def_StepMachines_Math_SatNet
import Theorems.Thm_Groundwork_SatNet_Link_fst_le
import Theorems.Thm_P2M_Groundwork_SatNet___of_lt_d32e7cdb1e61
import Theorems.Thm_P2M_Groundwork_SatNet_ite_mul_ite__7e510a0ac38e

set_option autoImplicit false
section
open Groundwork Groundwork.SatNet
open Finset
variable {V : Type}
variable [DecidableEq V]
variable {φ : List (List (V × Bool))} {g μ k : ℕ}
namespace Groundwork.SatNet
theorem _root_.solution (z : Fin g → Sl μ k → Bool) :
    (∏ a, (net φ g μ k).W a (z a)) * ∏ p ∈ pairs (Fin g), (net φ g μ k).Ψ p.1 p.2 (z p.1) (z p.2) =
      if Good φ z then 1 else 0 := by
  have hΨ : ∀ p ∈ pairs (Fin g), (net φ g μ k).Ψ p.1 p.2 (z p.1) (z p.2) =
      if ∀ s s', Link φ (p.1, s) (p.2, s') → z p.1 s = z p.2 s' then 1 else 0 :=
    fun p hp => Ψ_of_lt (Finset.mem_filter.1 hp).2 _ _
  rw [Finset.prod_congr rfl hΨ]
  simp only [net, weight]
  rw [Finset.prod_ite_zero, Finset.prod_ite_zero]
  simp only [Finset.prod_const_one]
  rw [ite_mul_ite']
  split_ifs with hAB hG hG
  · rfl
  · obtain ⟨hW, hP⟩ := hAB
    refine absurd ?_ hG
    refine ⟨fun p hp => (hW p.1 (mem_univ _)).1 p.2 hp, fun a c hc => (hW a (mem_univ _)).2.1 c hc, ?_⟩
    rintro ⟨a, s⟩ ⟨b, s'⟩ hl
    rcases lt_or_eq_of_le hl.fst_le with hlt | heq
    · exact hP (a, b) (Finset.mem_filter.2 ⟨mem_univ _, hlt⟩) s s' hl
    · simp only at heq
      subst heq
      exact (hW a (mem_univ _)).2.2 s s' hl
  · obtain ⟨h1, h2, h3⟩ := hG
    exact absurd ⟨fun a _ => ⟨fun s hs => h1 (a, s) hs, fun c hc => h2 a c hc, fun s s' hl => h3 (a, s) (a, s') hl⟩,
      fun p _ s s' hl => h3 (p.1, s) (p.2, s') hl⟩ hAB
  · rfl
end Groundwork.SatNet
