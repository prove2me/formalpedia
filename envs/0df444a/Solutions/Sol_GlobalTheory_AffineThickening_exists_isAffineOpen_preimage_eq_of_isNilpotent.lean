-- Prove2me | solution 1 for GlobalTheory.AffineThickening.exists_isAffineOpen_preimage_eq_of_isNilpotent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:21:46.60839+00:00
-- url     : https://prove2.me/submissions/dbafc368-c6d3-4cc1-9d04-9201e2f4486f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsAffineOfIsAffinePullbackQuotientOfIsNilpotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsIsAffineOpenPreimageEqOfIsNilpotent
import Theorems.Thm_GlobalTheory_AffineThickening_isAffine_of_isPullback_of_isNilpotent


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open GlobalTheory GlobalTheory.AffineThickening
namespace GlobalTheory.AffineThickening
theorem _root_.solution (A A' : Type) [CommRing A] [CommRing A']
    (g : A →+* A') (hg : Function.Surjective g) (hn : IsNilpotent (RingHom.ker g))
    (X X' : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of A)) (f' : X' ⟶ Spec (CommRingCat.of A'))
    (β : X' ⟶ X) (h : IsPullback β f' f (Spec.map (CommRingCat.ofHom g)))
    (D' : X'.Opens) (hD' : IsAffineOpen D') :
    ∃ D : X.Opens, IsAffineOpen D ∧ β ⁻¹ᵁ D = D' := by
  have h1 := IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom g) hg
  have : IsClosedImmersion β := MorphismProperty.of_isPullback h.flip h1
  obtain ⟨O, hO, hO'⟩ := β.isClosedEmbedding.isInducing.isOpen_iff.mp D'.isOpen
  have e : β ⁻¹ᵁ ⟨O, hO⟩ = D' := Opens.ext hO'
  refine ⟨⟨O, hO⟩, ?_, e⟩
  subst e
  exact isAffine_of_isPullback_of_isNilpotent (RingHom.ker g) hn (CommRingCat.ofHom g) hg rfl
    ((isPullback_morphismRestrict β ⟨O, hO⟩).paste_vert h) hD'
end GlobalTheory.AffineThickening
