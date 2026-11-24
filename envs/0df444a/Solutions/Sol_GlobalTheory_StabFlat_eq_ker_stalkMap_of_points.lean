-- Prove2me | solution 1 for GlobalTheory.StabFlat.eq_ker_stalkMap_of_points
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:57:12.856033+00:00
-- url     : https://prove2.me/submissions/60c2a7fc-f928-49fc-b82b-575d889500f3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FlatOfFormallyUnramifiedGrpEnd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_FlatClosedSubschemeFiniteOverLocalRing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry
open GlobalTheory GlobalTheory.StabFlat
namespace GlobalTheory.StabFlat
theorem _root_.solution {X H : Scheme.{0}} (j : H ⟶ X) [IsClosedImmersion j] (h : H)
    (I : Ideal (X.presheaf.stalk (j h)))
    (hI : ∀ (R : Type) [CommRing R] [IsLocalRing R] (φ : X.presheaf.stalk (j h) →+* R),
      (∃ y : Spec (CommRingCat.of R) ⟶ H, y ≫ j = Spec.map (CommRingCat.ofHom φ) ≫ X.fromSpecStalk (j h)) ↔
        I ≤ RingHom.ker φ) : I = RingHom.ker (j.stalkMap h).hom := by
  have h₁ : I ≤ RingHom.ker (j.stalkMap h).hom :=
    (hI (H.presheaf.stalk h) (j.stalkMap h).hom).1
      ⟨H.fromSpecStalk h, (Scheme.SpecMap_stalkMap_fromSpecStalk j).symm⟩
  have : Nontrivial (X.presheaf.stalk (j h) ⧸ I) := Ideal.Quotient.nontrivial_iff.2
    (ne_top_of_le_ne_top (RingHom.ker_ne_top _) h₁)
  have : IsLocalRing (X.presheaf.stalk (j h) ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  obtain ⟨y, hy⟩ := (hI (X.presheaf.stalk (j h) ⧸ I) (Ideal.Quotient.mk I)).2 Ideal.mk_ker.ge
  have hl : IsLocalHom (Ideal.Quotient.mk I) := IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  have e : y (IsLocalRing.closedPoint _) = h := by
    apply j.isClosedEmbedding.injective
    refine (congrArg (fun q => q (IsLocalRing.closedPoint _)) hy).trans ?_
    exact (congrArg (X.fromSpecStalk (j h)) (IsLocalRing.comap_closedPoint (Ideal.Quotient.mk I))).trans
      Scheme.fromSpecStalk_closedPoint
  let ψ := H.presheaf.stalkSpecializes (specializes_of_eq e) ≫ Scheme.stalkClosedPointTo y
  have hψ : j.stalkMap h ≫ ψ = CommRingCat.ofHom (Ideal.Quotient.mk I) := by
    apply Spec.map_injective
    rw [← cancel_mono (X.fromSpecStalk (j h)), ← hy, Spec.map_comp, Category.assoc,
      Scheme.SpecMap_stalkMap_fromSpecStalk, Spec.map_comp, Category.assoc,
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk_assoc, Scheme.Spec_stalkClosedPointTo_fromSpecStalk_assoc]
  have hψ' : ∀ a, ψ.hom ((j.stalkMap h).hom a) = Ideal.Quotient.mk I a := fun a => congrArg (fun q => q.hom a) hψ
  refine le_antisymm h₁ fun a ha => Ideal.Quotient.eq_zero_iff_mem.1 ?_
  rw [← hψ', RingHom.mem_ker.1 ha, map_zero]
end GlobalTheory.StabFlat
