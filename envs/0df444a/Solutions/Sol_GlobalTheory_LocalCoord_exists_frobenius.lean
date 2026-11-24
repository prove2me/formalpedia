-- Prove2me | solution 1 for GlobalTheory.LocalCoord.exists_frobenius
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:49:03.108826+00:00
-- url     : https://prove2.me/submissions/b202128c-94e4-4c0e-bec9-f0d264084b5f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_EqZeroOfForallLTensorEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsLocalCoordinates

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
open GlobalTheory GlobalTheory.LocalCoord
namespace GlobalTheory.LocalCoord
theorem _root_.solution (k A : Type) [Field k] [Finite k] [CommRing A] [Algebra k A]
    [Algebra.FiniteType k A] (m : Ideal A) (hm : m.IsMaximal) :
    ∃ F : A →ₐ[k] A, (∀ a, a - F a ∈ m) ∧ ∀ a, ∃ c, F a = a * a * c := by
  letI := Fintype.ofFinite k
  letI := Ideal.Quotient.field m
  haveI : Module.Finite k (A ⧸ m) := finite_of_finite_type_of_isJacobsonRing k (A ⧸ m)
  haveI : Finite (A ⧸ m) := Module.finite_of_finite k
  letI := Fintype.ofFinite (A ⧸ m)
  have hpow : ∀ (n : ℕ) (a : A),
      (FiniteField.frobeniusAlgHom k A ^ n) a = a ^ (Fintype.card k ^ n) := by
    intro n
    induction n with
    | zero => intro a; simp
    | succ n ih =>
      intro a
      rw [pow_succ', AlgHom.mul_apply, ih, FiniteField.coe_frobeniusAlgHom, pow_succ, pow_mul]
  have hc : Fintype.card (A ⧸ m) = Fintype.card k ^ Module.finrank k (A ⧸ m) :=
    Module.card_eq_pow_finrank
  refine ⟨FiniteField.frobeniusAlgHom k A ^ Module.finrank k (A ⧸ m), fun a => ?_, fun a => ?_⟩
  · rw [hpow, ← hc, ← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, FiniteField.pow_card,
      sub_self]
  · obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (Fintype.one_lt_card (α := A ⧸ m))
    exact ⟨a ^ d, by rw [hpow, ← hc, hd]; ring⟩
end GlobalTheory.LocalCoord
