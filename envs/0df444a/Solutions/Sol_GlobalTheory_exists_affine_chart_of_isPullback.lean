-- Prove2me | solution 1 for GlobalTheory.exists_affine_chart_of_isPullback
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:49:14.952836+00:00
-- url     : https://prove2.me/submissions/4b25f90f-e28b-4091-83b1-405a6cda7a29

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_MaximalIdealSquares_RingKrullDimQuotientSpanSingletonAddOne
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_RingKrullDimQuotientEqOfMemMinimalPrimes
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SpanFinrankMaximalIdealLeNcardOfLeSupSq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct IsLocalRing
open GlobalTheory
universe u
open AlgebraicGeometry CategoryTheory Topology
namespace GlobalTheory
theorem _root_.solution {O k : Type u} [CommRing O] [CommRing k] [Algebra O k]
    {X X₀ : Scheme.{u}} {f : X ⟶ Spec (.of O)} {i : X₀ ⟶ X} {p : X₀ ⟶ Spec (.of k)}
    (h : IsPullback i p f (Spec.map (CommRingCat.ofHom (algebraMap O k))))
    {A : Type u} [CommRing A] [Algebra O A] (j : Spec (.of A) ⟶ X) [IsOpenImmersion j]
    (hj : j ≫ f = Spec.map (CommRingCat.ofHom (algebraMap O A))) :
    ∃ (j₀ : Spec (.of (k ⊗[O] A)) ⟶ X₀) (_ : IsOpenImmersion j₀),
      IsPullback j₀ (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : A →ₐ[O] k ⊗[O] A).toRingHom)) i j := by
  have H := isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct O k A)
  rw [← hj] at H
  let j₀ := h.lift _ _ ((Category.assoc _ _ _).trans H.w.symm)
  have h₂ : j₀ ≫ p = _ := h.lift_snd _ _ _
  rw [← h₂] at H
  have H' := IsPullback.of_right H (h.lift_fst _ _ _) h.flip
  exact ⟨j₀, MorphismProperty.of_isPullback H'.flip ‹_›, H'⟩
end GlobalTheory
