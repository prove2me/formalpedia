-- Prove2me | solution 1 for Groundwork.Prog.all_pairs_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:11:20.16006+00:00
-- url     : https://prove2.me/submissions/5128f3a5-0cc0-4fbe-9f4d-fb50cbd59af7

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Groundwork_Net_Defs
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Logic.Equiv.Fin.Basic
import Definitions.Def_StepMachines_Prog_GridCount

set_option autoImplicit false
section
open Groundwork Groundwork.Prog
open Finset
namespace Groundwork.Prog
theorem _root_.solution (g : ℕ) (p : ℕ → ℕ → Bool) :
    ((List.range g).all fun i => (List.range g).all fun i' => decide (i' ≤ i) || p i i') = true ↔
      ∀ q ∈ pairs (Fin g), p q.1 q.2 = true := by
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, decide_eq_true_eq, pairs, mem_filter, mem_univ,
    true_and]
  constructor
  · rintro h ⟨a, b⟩ hab
    exact (h a a.2 b b.2).resolve_left (by have : a.val < b.val := hab; omega)
  · intro h i hi i' hi'
    by_cases hle : i' ≤ i
    · exact Or.inl hle
    · exact Or.inr (h (⟨i, hi⟩, ⟨i', hi'⟩) (show i < i' by omega))
end Groundwork.Prog
