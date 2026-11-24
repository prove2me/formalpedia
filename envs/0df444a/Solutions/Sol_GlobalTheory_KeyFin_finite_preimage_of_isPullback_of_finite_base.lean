-- Prove2me | solution 1 for GlobalTheory.KeyFin.finite_preimage_of_isPullback_of_finite_base
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:36:26.468799+00:00
-- url     : https://prove2.me/submissions/5f465af2-14e7-44f4-910d-e045224bf91c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_FinitePreimageOfIsPullbackOfFiniteBase

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
open GlobalTheory GlobalTheory.KeyFin
namespace GlobalTheory.KeyFin
theorem _root_.solution :
    ∀ (X X' S S' : Scheme.{0}) (h : X ⟶ S) (h' : X' ⟶ S') (φ : X' ⟶ X) (f : S' ⟶ S) (Z : Set X),
      LocallyOfFiniteType h → QuasiCompact h → IsPullback φ h' h f → Finite S' → IsClosed Z →
      Z.Finite → (φ ⁻¹' Z).Finite := by
  intro X X' S S' h h' φ f Z _ _ H _ hZ hfin
  let I := Scheme.IdealSheafData.vanishingIdeal (X := X) ⟨Z, hZ⟩
  have hr : Set.range I.subschemeι = Z := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]; rfl
  have hf : Finite I.subscheme := by
    have : Finite (Set.range I.subschemeι) := by rw [hr]; exact hfin.to_subtype
    exact Finite.of_injective_finite_range I.subschemeι.isClosedEmbedding.injective
  have hq : LocallyQuasiFinite (I.subschemeι ≫ h) :=
    .of_finite_preimage_singleton _ fun _ => Set.toFinite _
  have P := (IsPullback.of_hasPullback I.subschemeι φ).paste_vert H
  have h1 : LocallyQuasiFinite (pullback.snd I.subschemeι φ ≫ h') :=
    MorphismProperty.of_isPullback (P := @LocallyQuasiFinite) P hq
  have h2 : QuasiCompact (pullback.snd I.subschemeι φ ≫ h') :=
    MorphismProperty.of_isPullback (P := @QuasiCompact) P inferInstance
  have h3 : (Set.univ : Set ↑(pullback I.subschemeι φ)).Finite := by
    have := (Set.toFinite (Set.univ : Set S')).preimage'
      (f := (pullback.snd I.subschemeι φ ≫ h')) fun _ _ =>
        (pullback.snd I.subschemeι φ ≫ h').finite_preimage_singleton _
    simpa using this
  rw [← hr, ← Scheme.Pullback.range_snd, ← Set.image_univ]
  exact h3.image _
end GlobalTheory.KeyFin
