-- Prove2me | solution 1 for KernelRamsey.even_card_adjacent_pairs
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-24T16:29:14.855614+00:00
-- url     : https://prove2.me/submissions/8db2bdfe-7fa8-4abd-a662-f21ee8c63bab

import Mathlib
open Finset

theorem solution {V : Type} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (B : Finset V) : Even (((B ×ˢ B).filter (fun p => G.Adj p.1 p.2)).card) := by
  rw [← ZMod.natCast_eq_zero_iff_even]
  have h : ∑ p ∈ (B ×ˢ B).filter (fun p => G.Adj p.1 p.2), (1 : ZMod 2) = 0 := by
    refine Finset.sum_involution (fun p _ => (p.2, p.1)) ?_ ?_ ?_ ?_
    · intro a _; decide
    · intro a ha _ heq
      have h1 := (Finset.mem_filter.mp ha).2
      have : a.1 = a.2 := congrArg Prod.fst heq.symm
      rw [← this] at h1
      exact G.loopless.irrefl _ h1
    · intro a ha
      have := Finset.mem_filter.mp ha
      have h2 := Finset.mem_product.mp this.1
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨h2.2, h2.1⟩, this.2.symm⟩
    · intro a ha; rfl
  simpa using h
