-- Prove2me | solution 1 for GlobalTheory.CommonAlgClosedExtension.exists_common_algClosed_extension
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:15:58.137611+00:00
-- url     : https://prove2.me/submissions/1a51b6b7-7469-41d3-8abe-d91c34d8ac15

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsCommonAlgClosedExtension

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CommonAlgClosedExtension
open scoped TensorProduct
namespace GlobalTheory.CommonAlgClosedExtension
theorem _root_.solution (K₀ K K' : Type) [Field K₀] [Field K] [Field K']
    (i : K₀ →+* K) (i' : K₀ →+* K') :
    ∃ (Ω : Type) (_ : Field Ω) (_ : IsAlgClosed Ω) (j : K →+* Ω) (j' : K' →+* Ω),
      RingHom.comp j i = RingHom.comp j' i' := by
  letI : Algebra K₀ K := i.toAlgebra
  letI : Algebra K₀ K' := i'.toAlgebra
  haveI : Nontrivial (K ⊗[K₀] K') := inferInstance
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (K ⊗[K₀] K')
  letI : Field ((K ⊗[K₀] K') ⧸ m) := Ideal.Quotient.field m
  let φ : (K ⊗[K₀] K') →+* AlgebraicClosure ((K ⊗[K₀] K') ⧸ m) :=
    (algebraMap ((K ⊗[K₀] K') ⧸ m) _).comp (Ideal.Quotient.mk m)
  refine ⟨AlgebraicClosure ((K ⊗[K₀] K') ⧸ m), inferInstance, inferInstance,
    φ.comp (Algebra.TensorProduct.includeLeft (R := K₀) (S := K₀) (A := K) (B := K')).toRingHom,
    φ.comp (Algebra.TensorProduct.includeRight (R := K₀) (A := K) (B := K')).toRingHom, ?_⟩
  ext x
  have h1 := (Algebra.TensorProduct.includeLeft (R := K₀) (S := K₀) (A := K) (B := K')).commutes x
  have h2 := (Algebra.TensorProduct.includeRight (R := K₀) (A := K) (B := K')).commutes x
  exact congrArg φ (h1.trans h2.symm)
end GlobalTheory.CommonAlgClosedExtension
