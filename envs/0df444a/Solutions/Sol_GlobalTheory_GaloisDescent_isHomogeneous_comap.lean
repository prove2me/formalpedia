-- Prove2me | solution 1 for GlobalTheory.GaloisDescent.isHomogeneous_comap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:08:37.270619+00:00
-- url     : https://prove2.me/submissions/9a3aa34a-c25c-49dc-bcb4-50218601bd05

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsOneTmulOfForallFixed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_RestrictScalarsMapEqSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_MvPolynomialIsHomogeneousComapWeighted

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct Module
open GlobalTheory GlobalTheory.GaloisDescent
variable {K L A B G : Type*} [Field K] [Field L] [Algebra K L] [Ring A] [Ring B] [Algebra K A]
  [Algebra K B] [Algebra L B] [IsScalarTower K L B] {j : A →ₐ[K] B}
variable {ι σ τ : Type*} [DecidableEq ι] [AddMonoid ι] [SetLike σ A] [AddSubmonoidClass σ A]
  [SetLike τ B] [AddSubmonoidClass τ B] (𝒜 : ι → σ) (ℬ : ι → τ) [GradedRing 𝒜] [GradedRing ℬ]
namespace GlobalTheory.GaloisDescent
theorem _root_.solution (h : ∀ i, ∀ a ∈ 𝒜 i, j a ∈ ℬ i) {I : Ideal B}
    (hI : I.IsHomogeneous ℬ) : (I.comap j).IsHomogeneous 𝒜 :=
  (HomogeneousIdeal.comap (⟨j.toRingHom, fun {i a} => h i a⟩ : 𝒜 →+*ᵍ ℬ) ⟨I, hI⟩).isHomogeneous
end GlobalTheory.GaloisDescent
