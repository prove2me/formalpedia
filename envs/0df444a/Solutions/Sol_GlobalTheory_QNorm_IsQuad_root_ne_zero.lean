-- Prove2me | solution 1 for GlobalTheory.QNorm.IsQuad.root_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:17:14.529801+00:00
-- url     : https://prove2.me/submissions/77a3ec8f-7b61-4836-95b4-9eaa58f87ee6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsQuadraticSqrtExtensionBasicFacts

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
open GlobalTheory GlobalTheory.QNorm
variable {F E : Type} [Field F] [Field E] [Algebra F E] {δ : F} {θ : E} {σ : E ≃ₐ[F] E}
open NumberField IsDedekindDomain
open scoped WithZero
variable {F E : Type} [Field F] [Field E] [Algebra F E] {δ : F} {θ : E} {σ : E ≃ₐ[F] E}
namespace GlobalTheory.QNorm
namespace _root_.GlobalTheory.QNorm.IsQuad
theorem _root_.solution (h : _root_.GlobalTheory.QNorm.IsQuad δ θ σ) :
    θ ≠ 0 := by
  intro hθ
  apply h.nonsq
  refine ⟨0, (algebraMap F E).injective ?_⟩
  rw [← h.sq, hθ]
  simp
end _root_.GlobalTheory.QNorm.IsQuad
end GlobalTheory.QNorm
