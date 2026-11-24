-- Prove2me | solution 1 for GlobalTheory.compositum_finite_formallyUnramified
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:34:04.111507+00:00
-- url     : https://prove2.me/submissions/21323f5e-ecd2-4a31-9227-c44fde945973

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsCommonUnramifiedExtension

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open scoped TensorProduct
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ {k K L : Type} [Field k] [Field K] [Field L] (i : k →+* K) (j : k →+* L), i.Finite → i.FormallyUnramified → ∃ (M : Type) (_ : Field M) (u : K →+* M) (v : L →+* M), u.comp i = v.comp j ∧ v.Finite ∧ v.FormallyUnramified := by
  intro k K L _ _ _ i j hf hu
  letI : Algebra k K := i.toAlgebra
  letI : Algebra k L := j.toAlgebra
  haveI : Module.Finite k K := hf
  haveI : Algebra.FormallyUnramified k K := hu
  haveI : Nontrivial (L ⊗[k] K) := inferInstance
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (L ⊗[k] K)
  letI : Field (L ⊗[k] K ⧸ m) := Ideal.Quotient.field m
  refine ⟨L ⊗[k] K ⧸ m, inferInstance,
    (Ideal.Quotient.mk m).comp (Algebra.TensorProduct.includeRight : K →ₐ[k] L ⊗[k] K).toRingHom,
    algebraMap L (L ⊗[k] K ⧸ m), ?_, ?_, ?_⟩
  · ext a
    show Ideal.Quotient.mk m (1 ⊗ₜ (algebraMap k K a)) = Ideal.Quotient.mk m (algebraMap L (L ⊗[k] K) (algebraMap k L a))
    congr 1
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self_apply, Algebra.TensorProduct.tmul_one_eq_one_tmul]
  · exact RingHom.finite_algebraMap.mpr inferInstance
  · exact (RingHom.formallyUnramified_algebraMap).mpr inferInstance
end GlobalTheory
