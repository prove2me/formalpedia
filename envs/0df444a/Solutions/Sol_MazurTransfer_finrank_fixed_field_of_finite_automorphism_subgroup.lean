-- Prove2me | solution 1 for MazurTransfer.finrank_fixed_field_of_finite_automorphism_subgroup
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-10T14:52:53.852514+00:00
-- url     : https://prove2.me/submissions/4aa88c4d-8104-4aa7-b49d-7a67d11f0024

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: a finite subgroup's fixed-field degree without requiring
that the ambient field be finite over the ground field. Named downstream
consumer: the cyclic order-three actual diamond quotient of X_1(13).
-/
import Mathlib

noncomputable section
universe u v
namespace MazurTransfer.PublicFiniteFixedFieldProof

theorem finrank_fixedField (K : Type u) [Field K] (E : Type v) [Field E] [Algebra K E]
    (H : Subgroup (E ≃ₐ[K] E)) [Finite H] :
    Module.finrank (IntermediateField.fixedField H) E = Nat.card H := by
  letI := Fintype.ofFinite H
  rw [Nat.card_eq_fintype_card]
  exact FixedPoints.finrank_eq_card H E

end MazurTransfer.PublicFiniteFixedFieldProof
#print axioms MazurTransfer.PublicFiniteFixedFieldProof.finrank_fixedField

theorem solution (K : Type u) [Field K] (E : Type v) [Field E] [Algebra K E]
    (H : Subgroup (E ≃ₐ[K] E)) [Finite H] :
    Module.finrank (IntermediateField.fixedField H) E = Nat.card H := by
  exact MazurTransfer.PublicFiniteFixedFieldProof.finrank_fixedField K E H

#print axioms solution
