-- Prove2me | solution 1 for GlobalTheory.exists_finite_separable_point_of_separableClosure_point
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:41:34.662231+00:00
-- url     : https://prove2.me/submissions/71dd4aaf-012c-4666-9aad-01f5792d82af

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFiniteSeparablePointOfSeparableClosurePoin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (k B : Type) [Field k] [CommRing B] [Algebra k B], Algebra.FiniteType k B →
      Nonempty (B →ₐ[k] SeparableClosure k) →
      ∃ (k' : Type) (_ : Field k') (_ : Algebra k k'),
        FiniteDimensional k k' ∧ Algebra.IsSeparable k k' ∧ Nonempty (B →ₐ[k] k') := by
  intro k B _ _ _ hB ⟨φ⟩
  classical
  obtain ⟨t, ht⟩ := hB.out
  let K : IntermediateField k (SeparableClosure k) :=
    IntermediateField.adjoin k (φ '' (t : Set B))
  have hfin : (φ '' (t : Set B)).Finite := t.finite_toSet.image φ
  haveI : Finite (φ '' (t : Set B)) := hfin.to_subtype
  have hfd : FiniteDimensional k K :=
    IntermediateField.finiteDimensional_adjoin
      (fun x _ => (Algebra.IsSeparable.isSeparable k x).isIntegral)
  have hsep : Algebra.IsSeparable k K := Algebra.IsSeparable.of_algHom k (SeparableClosure k) K.val
  have hmem : ∀ b, φ b ∈ K.toSubalgebra := by
    intro b
    apply IntermediateField.algebra_adjoin_le_adjoin
    rw [← AlgHom.map_adjoin, ht]
    exact ⟨b, trivial, rfl⟩
  exact ⟨K, inferInstance, inferInstance, hfd, hsep, ⟨φ.codRestrict K.toSubalgebra hmem⟩⟩
end GlobalTheory
