-- Prove2me | solution 1 for GlobalTheory.specializes_lift_closedFibre_stalkBaseChange
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:33:50.762844+00:00
-- url     : https://prove2.me/submissions/cb7ac47f-ab07-4e81-aff8-e7959032bd74

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SpecializesLiftClosedFibreStalkBaseChange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ {X Y : Scheme.{0}} (π : X ⟶ Y) (z : Y) (R : Type) [CommRing R] [IsLocalRing R] (i : Y.presheaf.stalk z →+* R) [IsLocalHom i], Function.Surjective (IsLocalRing.ResidueField.map i) → ∀ (v : ↥(pullback (Spec.map (CommRingCat.ofHom i) ≫ Y.fromSpecStalk z) π)) (y : X), pullback.fst (Spec.map (CommRingCat.ofHom i) ≫ Y.fromSpecStalk z) π v = IsLocalRing.closedPoint R → pullback.snd (Spec.map (CommRingCat.ofHom i) ≫ Y.fromSpecStalk z) π v ⤳ y → π y = z → ∃ w : ↥(pullback (Spec.map (CommRingCat.ofHom i) ≫ Y.fromSpecStalk z) π), v ⤳ w ∧ pullback.snd (Spec.map (CommRingCat.ofHom i) ≫ Y.fromSpecStalk z) π w = y := by
  intro X Y π z R _ _ i _ hi v y hv hsp hy
  let e : IsLocalRing.ResidueField (Y.presheaf.stalk z) ≃+* IsLocalRing.ResidueField R :=
    RingEquiv.ofBijective (IsLocalRing.ResidueField.map i) ⟨(IsLocalRing.ResidueField.map i).injective, hi⟩
  let β : R →+* IsLocalRing.ResidueField (Y.presheaf.stalk z) := e.symm.toRingHom.comp (IsLocalRing.residue R)
  have hβ : β.comp i = IsLocalRing.residue _ := by
    ext x
    simp only [β, RingHom.comp_apply, RingEquiv.coe_toRingHom]
    rw [← IsLocalRing.ResidueField.map_residue]
    exact e.symm_apply_apply (IsLocalRing.residue _ x)
  have hcomp : Spec.map (CommRingCat.ofHom β : CommRingCat.of R ⟶ Y.residueField z) ≫ Spec.map (CommRingCat.ofHom i) ≫ Y.fromSpecStalk z = Y.fromSpecResidueField z := by
    rw [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp, hβ]
    rfl
  have hβcl : Spec.map (CommRingCat.ofHom β : CommRingCat.of R ⟶ Y.residueField z) (IsLocalRing.closedPoint (Y.residueField z)) = IsLocalRing.closedPoint R := by
    have : IsLocalHom β := inferInstance
    exact IsLocalRing.comap_closedPoint β
  let g : π.fiber z ⟶ pullback (Spec.map (CommRingCat.ofHom i) ≫ Y.fromSpecStalk z) π :=
    pullback.lift (π.fiberToSpecResidueField z ≫ (Spec.map (CommRingCat.ofHom β : CommRingCat.of R ⟶ Y.residueField z))) (π.fiberι z)
      (by rw [Category.assoc]; exact (congrArg (π.fiberToSpecResidueField z ≫ ·) hcomp).trans (π.fiber_fac z).symm)
  have hgq : g ≫ pullback.snd (Spec.map (CommRingCat.ofHom i) ≫ Y.fromSpecStalk z) π = π.fiberι z := pullback.lift_snd _ _ _
  let h : pullback (Spec.map (CommRingCat.ofHom β : CommRingCat.of R ⟶ Y.residueField z)) (pullback.fst (Spec.map (CommRingCat.ofHom i) ≫ Y.fromSpecStalk z) π) ⟶ π.fiber z :=
    pullback.lift (pullback.snd (Spec.map (CommRingCat.ofHom β : CommRingCat.of R ⟶ Y.residueField z)) (pullback.fst (Spec.map (CommRingCat.ofHom i) ≫ Y.fromSpecStalk z) π) ≫ pullback.snd (Spec.map (CommRingCat.ofHom i) ≫ Y.fromSpecStalk z) π) (pullback.fst (Spec.map (CommRingCat.ofHom β : CommRingCat.of R ⟶ Y.residueField z)) (pullback.fst (Spec.map (CommRingCat.ofHom i) ≫ Y.fromSpecStalk z) π))
      (by
        rw [Category.assoc, ← pullback.condition (f := (Spec.map (CommRingCat.ofHom i) ≫ Y.fromSpecStalk z)) (g := π), ← Category.assoc,
          ← pullback.condition (f := (Spec.map (CommRingCat.ofHom β : CommRingCat.of R ⟶ Y.residueField z))) (g := pullback.fst (Spec.map (CommRingCat.ofHom i) ≫ Y.fromSpecStalk z) π), Category.assoc]; exact congrArg _ hcomp)
  have hgf : g ≫ pullback.fst (Spec.map (CommRingCat.ofHom i) ≫ Y.fromSpecStalk z) π = π.fiberToSpecResidueField z ≫ (Spec.map (CommRingCat.ofHom β : CommRingCat.of R ⟶ Y.residueField z)) := pullback.lift_fst _ _ _
  have hhf : h ≫ π.fiberToSpecResidueField z = pullback.fst (Spec.map (CommRingCat.ofHom β : CommRingCat.of R ⟶ Y.residueField z)) (pullback.fst (Spec.map (CommRingCat.ofHom i) ≫ Y.fromSpecStalk z) π) := pullback.lift_snd _ _ _
  have hhι : h ≫ π.fiberι z = pullback.snd (Spec.map (CommRingCat.ofHom β : CommRingCat.of R ⟶ Y.residueField z)) (pullback.fst (Spec.map (CommRingCat.ofHom i) ≫ Y.fromSpecStalk z) π) ≫ pullback.snd (Spec.map (CommRingCat.ofHom i) ≫ Y.fromSpecStalk z) π := pullback.lift_fst _ _ _
  have hhg : h ≫ g = pullback.snd (Spec.map (CommRingCat.ofHom β : CommRingCat.of R ⟶ Y.residueField z)) (pullback.fst (Spec.map (CommRingCat.ofHom i) ≫ Y.fromSpecStalk z) π) := by
    apply pullback.hom_ext
    · rw [Category.assoc, hgf, ← Category.assoc, hhf]
      exact pullback.condition (f := (Spec.map (CommRingCat.ofHom β : CommRingCat.of R ⟶ Y.residueField z))) (g := pullback.fst (Spec.map (CommRingCat.ofHom i) ≫ Y.fromSpecStalk z) π)
    · rw [Category.assoc, hgq, hhι]
  obtain ⟨u, -, hu2⟩ := Scheme.Pullback.exists_preimage_pullback (f := (Spec.map (CommRingCat.ofHom β : CommRingCat.of R ⟶ Y.residueField z))) (g := pullback.fst (Spec.map (CommRingCat.ofHom i) ≫ Y.fromSpecStalk z) π)
    (IsLocalRing.closedPoint (Y.residueField z)) v (hβcl.trans hv.symm)
  have hga : g (h u) = v := by
    rw [← Scheme.Hom.comp_apply, hhg, hu2]
  have hfa : π.fiberι z (h u) = pullback.snd (Spec.map (CommRingCat.ofHom i) ≫ Y.fromSpecStalk z) π v := by
    rw [← hga, ← Scheme.Hom.comp_apply g, hgq]
  let b := (π.fiberHomeo z).symm ⟨y, hy⟩
  have hb : π.fiberι z b = y := π.fiberι_fiberHomeo_symm z ⟨y, hy⟩
  have hab : h u ⤳ b := by
    rw [← (π.fiberι z).isEmbedding.toIsInducing.specializes_iff, hfa, hb]
    exact hsp
  refine ⟨g b, ?_, ?_⟩
  · rw [← hga]
    exact hab.map g.continuous
  · rw [← Scheme.Hom.comp_apply, hgq, hb]
end GlobalTheory
