-- Prove2me | solution 1 for GlobalTheory.FiniteExtensionEmbedding.exists_finite_extension_embedding
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:47:23.248547+00:00
-- url     : https://prove2.me/submissions/295c7427-e14b-42b2-8e66-9cdb3193a148

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFiniteExtensionEmbedding

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory GlobalTheory.FiniteExtensionEmbedding
namespace GlobalTheory.FiniteExtensionEmbedding
theorem _root_.solution (F K : Type) [Field F] [CharZero F]
    [FiniteDimensional ℚ F] [Field K] [CharZero K] :
    ∃ (L : Type) (_ : Field L) (_ : Algebra K L), FiniteDimensional K L ∧ Nonempty (F →+* L) := by
  haveI : Nontrivial (K ⊗[ℚ] F) := inferInstance
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (K ⊗[ℚ] F)
  letI : Field ((K ⊗[ℚ] F) ⧸ m) := Ideal.Quotient.field m
  refine ⟨(K ⊗[ℚ] F) ⧸ m, inferInstance, inferInstance, ?_, ⟨?_⟩⟩
  · exact Module.Finite.of_surjective (Ideal.Quotient.mkₐ K m).toLinearMap
      (Ideal.Quotient.mkₐ_surjective K m)
  · exact (Ideal.Quotient.mk m).comp
      (Algebra.TensorProduct.includeRight (R := ℚ) (A := K) (B := F)).toRingHom
end GlobalTheory.FiniteExtensionEmbedding
