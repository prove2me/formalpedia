-- Prove2me | solution 1 for Groundwork.SatNet.exists_slot
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:08:17.740713+00:00
-- url     : https://prove2.me/submissions/974fc8bf-586d-445e-a440-6fc969b58352

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

set_option autoImplicit false
section
open Groundwork Groundwork.SatNet
open Finset
variable {V : Type}
variable [DecidableEq V]
omit [DecidableEq V]
namespace Groundwork.SatNet
theorem _root_.solution {φ : List (List (V × Bool))} {g μ k : ℕ} (hk : ∀ C ∈ φ, C.length ≤ k)
    (hm : φ.length ≤ g * μ) {C : List (V × Bool)} (hC : C ∈ φ) {l : V × Bool} (hl : l ∈ C) :
    ∃ p : Slot g μ k, lit φ p = some l := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hC
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hl
  have hμ : 0 < μ := by
    rcases Nat.eq_zero_or_pos μ with h | h
    · subst h; omega
    · exact h
  have hg : i / μ < g := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; omega)
  refine ⟨(⟨i / μ, hg⟩, ⟨i % μ, Nat.mod_lt _ hμ⟩, ⟨j, lt_of_lt_of_le hj (hk _ hC)⟩), ?_⟩
  simp [lit, Nat.div_add_mod', hi, hj]
end Groundwork.SatNet
