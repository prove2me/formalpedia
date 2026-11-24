-- Prove2me | solution 1 for GlobalTheory.SmallLift.step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:04:18.965219+00:00
-- url     : https://prove2.me/submissions/90bbbb40-6c8d-4e87-936e-c12586df958f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsStalkRetractionOfSmallLifting
import Theorems.Thm_GlobalTheory_SmallLift_map_closedPoint

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
open GlobalTheory GlobalTheory.SmallLift
namespace GlobalTheory.SmallLift
theorem _root_.solution {X Y : Scheme.{0}} (f : X ⟶ Y) (x : X) (C : Type) [CommRing C] [IsLocalRing C]
    (I : Ideal C) [IsLocalRing (C ⧸ I)]
    (H : ∀ (a : Spec (CommRingCat.of (C ⧸ I)) ⟶ X) (b : Spec (CommRingCat.of C) ⟶ Y),
      a ≫ f = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ b →
      ∃ l : Spec (CommRingCat.of C) ⟶ X,
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ l = a ∧ l ≫ f = b)
    (π : Y.presheaf.stalk (f x) ⟶ CommRingCat.of C)
    (ψ : X.presheaf.stalk x ⟶ CommRingCat.of (C ⧸ I)) [IsLocalHom ψ.hom]
    (hψ : ψ.hom.comp (f.stalkMap x).hom = (Ideal.Quotient.mk I).comp π.hom) :
    ∃ g : X.presheaf.stalk x →+* C, IsLocalHom g ∧ g.comp (f.stalkMap x).hom = π.hom := by
  have e : f.stalkMap x ≫ ψ =
      π ≫ CommRingCat.ofHom (Ideal.Quotient.mk I) := by
    ext1
    exact hψ
  obtain ⟨l, hl, hs⟩ := H (Spec.map ψ ≫ X.fromSpecStalk x)
    (Spec.map π ≫ Y.fromSpecStalk (f x)) (by
      rw [Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk, ← Spec.map_comp_assoc,
        ← Spec.map_comp_assoc, e])
  obtain ⟨⟨x', φ, hφ⟩, rfl⟩ := (SpecToEquivOfLocalRing X (CommRingCat.of C)).symm.surjective l
  rw [SpecToEquivOfLocalRing_symm_apply] at hs hl
  dsimp only at hs hl
  have hmk : IsLocalHom (CommRingCat.ofHom (Ideal.Quotient.mk I)).hom :=
    IsLocalHom.of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have hx : x' = x := by
    rw [← Spec.map_comp_assoc] at hl
    have : IsLocalHom (φ ≫ CommRingCat.ofHom (Ideal.Quotient.mk I)).hom :=
      @RingHom.isLocalHom_comp _ _ _ _ _ _ _ φ.hom hmk hφ
    have h1 := map_closedPoint (φ ≫ CommRingCat.ofHom (Ideal.Quotient.mk I))
    rw [hl] at h1
    exact h1.symm.trans (map_closedPoint ψ)
  subst hx
  rw [Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk, ← Spec.map_comp_assoc] at hs
  have : Mono (Y.fromSpecStalk (f x')) :=
    SurjectiveOnStalks.mono_of_injective (Y.fromSpecStalk (f x')).isEmbedding.injective
  have key := Spec.map_injective ((cancel_mono _).1 hs)
  exact ⟨φ.hom, hφ, congrArg CommRingCat.Hom.hom key⟩
end GlobalTheory.SmallLift
