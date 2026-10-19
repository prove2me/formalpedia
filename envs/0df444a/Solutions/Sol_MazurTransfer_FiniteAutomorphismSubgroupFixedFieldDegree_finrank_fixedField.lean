-- Prove2me | solution 1 for MazurTransfer.FiniteAutomorphismSubgroupFixedFieldDegree.finrank_fixedField
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T15:58:01.777492+00:00
-- url     : https://prove2.me/submissions/7dd80b6a-6296-4d1c-9442-8740591b2c28

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: a finite subgroup's fixed-field degree without requiring
that the ambient field be finite over the ground field. Named downstream
consumer: the cyclic order-three actual diamond quotient of X_1(13).
-/
import Mathlib

noncomputable section
universe u v

theorem solution (K : Type u) [Field K] (E : Type v) [Field E] [Algebra K E]
    (H : Subgroup (E ≃ₐ[K] E)) [Finite H] :
    Module.finrank (IntermediateField.fixedField H) E = Nat.card H := by
  letI := Fintype.ofFinite H
  rw [Nat.card_eq_fintype_card]
  exact FixedPoints.finrank_eq_card H E


#print axioms solution
