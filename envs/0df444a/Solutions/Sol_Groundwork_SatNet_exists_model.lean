-- Prove2me | solution 1 for Groundwork.SatNet.exists_model
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:08:38.179978+00:00
-- url     : https://prove2.me/submissions/07343d08-3200-4b85-b09f-e885d16d8400

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
import Theorems.Thm_Groundwork_SatNet_eq_of_consec
import Theorems.Thm_Groundwork_SatNet_idx_injective
import Theorems.Thm_Groundwork_SatNet_lit_mem

set_option autoImplicit false
section
open Groundwork Groundwork.SatNet
open Finset
variable {V : Type}
variable [DecidableEq V]
variable {φ : List (List (V × Bool))} {g μ k : ℕ}
namespace Groundwork.SatNet
theorem _root_.solution (hm : φ.length ≤ g * μ) {z : Fin g → Sl μ k → Bool} (hz : Good φ z) :
    ∃ a, IsModel φ a ∧ toState φ a = z := by
  classical
  let a : V → Bool := fun v =>
    if h : ∃ p : Slot g μ k, lab φ p = some v then z h.choose.1 h.choose.2 else false
  have key : ∀ (p : Slot g μ k) l, lit φ p = some l → a l.1 = z p.1 p.2 := by
    intro p l hp
    have h : ∃ p : Slot g μ k, lab φ p = some l.1 := ⟨p, by simp [lab, hp]⟩
    simp only [a, h, dite_true]
    have := h.choose_spec
    exact eq_of_consec (z := fun p => z p.1 p.2) idx_injective hz.2.2 (by rw [this]; simp)
      (by rw [this]; simp [lab, hp])
  refine ⟨a, ⟨?_, ?_⟩, ?_⟩
  · intro C hC
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hC
    have hμ : 0 < μ := by
      rcases Nat.eq_zero_or_pos μ with h | h
      · subst h; omega
      · exact h
    have hg : i / μ < g := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; omega)
    obtain ⟨j, hj⟩ := hz.2.1 ⟨i / μ, hg⟩ ⟨i % μ, Nat.mod_lt _ hμ⟩ (by simpa [Nat.div_add_mod'] using hi)
    obtain ⟨l, hl, hl2⟩ := Option.map_eq_some_iff.1 hj
    refine ⟨l, ?_, ?_⟩
    · have hl' := hl
      simp only [lit, Nat.div_add_mod', List.getElem?_eq_getElem hi, Option.bind_some] at hl'
      exact List.mem_of_getElem? hl'
    · rw [key _ _ hl]; exact hl2.symm
  · intro v hv
    suffices hne : ¬ ∃ p : Slot g μ k, lab φ p = some v by simp only [a, hne, dite_false]
    rintro ⟨p, hp⟩
    obtain ⟨l, hl, rfl⟩ := Option.map_eq_some_iff.1 hp
    obtain ⟨C, hC, hlC⟩ := lit_mem hl
    exact hv C hC l hlC rfl
  · funext c s
    cases h : lit φ (c, s) with
    | none => simp [toState, h, hz.1 (c, s) h]
    | some l => simp [toState, h, key (c, s) l h]
end Groundwork.SatNet
