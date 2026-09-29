-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.smooth_irreducibleSpace_geometricFibre_iff_of_ker_eq_ker
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/fad94a10-6753-57c4-8f30-112be80344b9

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Theorems.Thm_GoodReductionJacobian_nonempty_relativeGroupLaw_geometricFibre_of_nonempty_of_ker_eq
import Theorems.Thm_AlgebraicGeometry_geometricallyIrreducible_of_irreducibleSpace_pullback_of_isAlgClosed
import Theorems.Thm_AlgebraicGeometry_forall_irreducibleSpace_pullback_iff_geometricallyIrreducible_fiberToSpecResidueField
import Theorems.Thm_AlgebraicGeometry_topologicalKrullDim_preimage_eq_of_isPullback_of_smooth_of_isConnected
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_smooth_irreducibleSpace_geometricFibre_iff_of_ker_eq_ker
p2m_attr_erase "instance" "AlgebraicGeometry.SubalgebraStages.compactSpace_pullback AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_pullback AlgebraicGeometry.SubalgebraStages.compactSpace_obj AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_obj AlgebraicGeometry.SubalgebraStages.quasiCompact_snd AlgebraicGeometry.SubalgebraStages.isAffineHom_leg AlgebraicGeometry.SubalgebraStages.isAffineHom_trans AlgebraicGeometry.SubalgebraStages.isAffineHom_diagram_map AlgebraicGeometry.SubalgebraStages.quasiSeparated_snd AlgebraicGeometry.SubalgebraStages.isCofiltered_op"
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.SubalgebraStages.specCone_π_app AlgebraicGeometry.SubalgebraStages.specLeg_specHom AlgebraicGeometry.SubalgebraStages.specLeg_specTrans AlgebraicGeometry.SubalgebraStages.cone_pt AlgebraicGeometry.SubalgebraStages.trans_fst"
p2m_attr_erase "simp" "AlgebraicGeometry.SubalgebraStages.diagram_obj AlgebraicGeometry.SubalgebraStages.leg_snd AlgebraicGeometry.SubalgebraStages.diagram_map AlgebraicGeometry.SubalgebraStages.specTrans_refl AlgebraicGeometry.SubalgebraStages.trans_snd AlgebraicGeometry.SubalgebraStages.specTrans_specHom AlgebraicGeometry.SubalgebraStages.specCone_pt AlgebraicGeometry.SubalgebraStages.cone_π_app AlgebraicGeometry.SubalgebraStages.specDiagram_map AlgebraicGeometry.SubalgebraStages.specDiagram_obj AlgebraicGeometry.SubalgebraStages.leg_fst AlgebraicGeometry.SubalgebraStages.leg_trans"

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
attribute [local instance] MvPolynomial.gradedAlgebra

namespace L2Sol

p2m_open "CategoryTheory.MorphismProperty"

variable {R : Type} [CommRing R] {Z : Scheme.{0}} (f : Z ⟶ Spec (CommRingCat.of R))

theorem specMap_base_eq {k : Type} [Field k] (x : R →+* k) (p : ↥(Spec (CommRingCat.of k))) :
    (Spec.map (CommRingCat.ofHom x)).base p = (⟨RingHom.ker x, RingHom.ker_isPrime x⟩ : PrimeSpectrum R) := by
  apply PrimeSpectrum.ext
  show (PrimeSpectrum.comap (CommRingCat.ofHom x).hom p).asIdeal = RingHom.ker x
  rw [PrimeSpectrum.comap_asIdeal, Ideal.eq_bot_of_prime p.asIdeal, ← RingHom.ker_eq_comap_bot]
  rfl

theorem exists_isPullback_fiber (s : ↥(Spec (CommRingCat.of R))) {k : Type} [Field k] (x : R →+* k)
    (hx : RingHom.ker x = s.asIdeal) :
    ∃ (φ : ↑((Spec (CommRingCat.of R)).residueField s) →+* k)
      (t : pullback f (Spec.map (CommRingCat.ofHom x)) ⟶ f.fiber s),
      IsPullback t (pullback.snd f (Spec.map (CommRingCat.ofHom x))) (f.fiberToSpecResidueField s)
        (Spec.map (CommRingCat.ofHom φ)) := by
  have hs : (Spec.map (CommRingCat.ofHom x)).base (IsLocalRing.closedPoint k) = s := by
    rw [specMap_base_eq]; exact PrimeSpectrum.ext hx
  subst hs
  let g := Spec.map (CommRingCat.ofHom x)
  let φ := (Spec (CommRingCat.of R)).descResidueField (Scheme.stalkClosedPointTo g)
  let y : Spec (CommRingCat.of k) ⟶ Spec ((Spec (CommRingCat.of R)).residueField (g.base (IsLocalRing.closedPoint k))) :=
    Spec.map φ
  have hy : y ≫ (Spec (CommRingCat.of R)).fromSpecResidueField _ = g :=
    Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField k _ g
  have houter : IsPullback (pullback.fst f g) (pullback.snd f g) f (y ≫ (Spec (CommRingCat.of R)).fromSpecResidueField _) := by
    rw [hy]; exact IsPullback.of_hasPullback f g
  let t : pullback f g ⟶ f.fiber (g.base (IsLocalRing.closedPoint k)) :=
    pullback.lift (pullback.fst f g) (pullback.snd f g ≫ y) (by rw [houter.w, Category.assoc])
  have ht : t ≫ pullback.fst f _ = pullback.fst f g := pullback.lift_fst _ _ _
  have hsq : IsPullback t (pullback.snd f g) (f.fiberToSpecResidueField _) y :=
    IsPullback.of_right (by rw [ht]; exact houter) (pullback.lift_snd _ _ _)
      (IsPullback.of_hasPullback f ((Spec (CommRingCat.of R)).fromSpecResidueField _))
  exact ⟨φ.hom, t, hsq⟩

theorem fpqc_specMap {K k : Type} [Field K] [Field k] (φ : K →+* k) :
    (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0}) (Spec.map (CommRingCat.ofHom φ)) := by
  refine ⟨⟨⟨fun p => ⟨IsLocalRing.closedPoint k, Subsingleton.elim _ _⟩⟩, ?_⟩, inferInstance⟩
  rw [HasRingHomProperty.Spec_iff (P := @Flat)]
  show φ.Flat
  letI : Algebra K k := φ.toAlgebra
  haveI : Module.Free K k := Module.Free.of_divisionRing K k
  exact (inferInstance : Module.Flat K k)

theorem smooth_descendsAlong :
    MorphismProperty.DescendsAlong (@Smooth : MorphismProperty Scheme.{0}) (@Surjective ⊓ @Flat ⊓ @QuasiCompact) :=
  HasRingHomProperty.descendsAlong_flat (P := @Smooth) RingHom.Smooth.codescendsAlong_faithfullyFlat

theorem topologicalKrullDim_preimage_eq {X Y : Scheme.{0}} (p : X ⟶ Y) [Subsingleton ↥Y] (q : ↥Y) :
    topologicalKrullDim ↥(p.base ⁻¹' {q}) = topologicalKrullDim ↥X := by
  have : p.base ⁻¹' {q} = Set.univ := by
    ext z; simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_univ, iff_true]; exact Subsingleton.elim _ _
  rw [this]
  exact IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ ↥X).isHomeomorph

theorem isConnected_preimage {X Y : Scheme.{0}} (p : X ⟶ Y) [Subsingleton ↥Y]
    [IrreducibleSpace ↥X] (q : ↥Y) : _root_.IsConnected (p.base ⁻¹' {q}) := by
  have : p.base ⁻¹' {q} = Set.univ := by
    ext z; simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_univ, iff_true]; exact Subsingleton.elim _ _
  rw [this]; exact isConnected_univ

theorem oneWay [IsProper f] [Flat f] [LocallyOfFinitePresentation f]
    (hproj : ∃ (N : ℕ) (ι : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)),
      IsClosedImmersion ι ∧ ι ≫ ProjSpace.π R N = f)
    (g : ℕ)
    (k₁ : Type) [Field k₁] [IsAlgClosed k₁] (x₁ : R →+* k₁)
    (k₂ : Type) [Field k₂] [IsAlgClosed k₂] (x₂ : R →+* k₂)
    (hker : RingHom.ker x₁ = RingHom.ker x₂) :
    (Smooth (pullback.snd f (Spec.map (CommRingCat.ofHom x₁))) ∧
        IrreducibleSpace ↥(pullback f (Spec.map (CommRingCat.ofHom x₁))) ∧
        topologicalKrullDim ↥(pullback f (Spec.map (CommRingCat.ofHom x₁))) = g ∧
        Nonempty (RelativeGroupLaw k₁ (pullback.snd f (Spec.map (CommRingCat.ofHom x₁))))) →
    (Smooth (pullback.snd f (Spec.map (CommRingCat.ofHom x₂))) ∧
        IrreducibleSpace ↥(pullback f (Spec.map (CommRingCat.ofHom x₂))) ∧
        topologicalKrullDim ↥(pullback f (Spec.map (CommRingCat.ofHom x₂))) = g ∧
        Nonempty (RelativeGroupLaw k₂ (pullback.snd f (Spec.map (CommRingCat.ofHom x₂))))) := by
  rintro ⟨hsm₁, hirr₁, hdim₁, hlaw₁⟩
  let s : ↥(Spec (CommRingCat.of R)) := ⟨RingHom.ker x₁, RingHom.ker_isPrime x₁⟩
  have hx₁ : RingHom.ker x₁ = s.asIdeal := rfl
  have hx₂ : RingHom.ker x₂ = s.asIdeal := hker.symm
  obtain ⟨φ₁, t₁, sq₁⟩ := exists_isPullback_fiber f s x₁ hx₁
  obtain ⟨φ₂, t₂, sq₂⟩ := exists_isPullback_fiber f s x₂ hx₂

  haveI := smooth_descendsAlong
  have hsmF : Smooth (f.fiberToSpecResidueField s) :=
    MorphismProperty.of_isPullback_of_descendsAlong (P := @Smooth) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
      sq₁.flip (fpqc_specMap φ₁) hsm₁
  have hsm₂ : Smooth (pullback.snd f (Spec.map (CommRingCat.ofHom x₂))) :=
    MorphismProperty.of_isPullback (P := @Smooth) sq₂ hsmF

  haveI : IrreducibleSpace ↥(pullback (f.fiberToSpecResidueField s) (Spec.map (CommRingCat.ofHom φ₁))) :=
    (Scheme.homeoOfIso sq₁.isoPullback).irreducibleSpace_iff.mp hirr₁
  have hgi : GeometricallyIrreducible (f.fiberToSpecResidueField s) :=
    @AlgebraicGeometry.geometricallyIrreducible_of_irreducibleSpace_pullback_of_isAlgClosed
      ↑((Spec (CommRingCat.of R)).residueField s) _ _ (f.fiberToSpecResidueField s) k₁ _ φ₁.toAlgebra _ ‹_›
  have hirr₂ : IrreducibleSpace ↥(pullback f (Spec.map (CommRingCat.ofHom x₂))) :=
    (AlgebraicGeometry.forall_irreducibleSpace_pullback_iff_geometricallyIrreducible_fiberToSpecResidueField f s).mpr
      hgi k₂ x₂ hx₂

  haveI hirrF : IrreducibleSpace ↥(f.fiber s) := by
    have hsurj : Surjective t₁ :=
      MorphismProperty.of_isPullback (P := @Surjective) sq₁.flip (fpqc_specMap φ₁).1.1
    have h := (IrreducibleSpace.isIrreducible_univ (X := ↥(pullback f (Spec.map (CommRingCat.ofHom x₁))))).image
      t₁.base t₁.base.hom.continuous.continuousOn
    rw [Set.image_univ, hsurj.1.range_eq] at h
    exact (irreducibleSpace_def _).mpr h

  have hd₁ := AlgebraicGeometry.topologicalKrullDim_preimage_eq_of_isPullback_of_smooth_of_isConnected
    (f.fiberToSpecResidueField s) hsmF (Spec.map (CommRingCat.ofHom φ₁)) _ t₁ sq₁ (IsLocalRing.closedPoint k₁)
    (isConnected_preimage _ _)
  have hd₂ := AlgebraicGeometry.topologicalKrullDim_preimage_eq_of_isPullback_of_smooth_of_isConnected
    (f.fiberToSpecResidueField s) hsmF (Spec.map (CommRingCat.ofHom φ₂)) _ t₂ sq₂ (IsLocalRing.closedPoint k₂)
    (isConnected_preimage _ _)
  rw [topologicalKrullDim_preimage_eq, topologicalKrullDim_preimage_eq] at hd₁ hd₂
  have hdim₂ : topologicalKrullDim ↥(pullback f (Spec.map (CommRingCat.ofHom x₂))) = g := by
    rw [hd₂, ← hd₁, hdim₁]

  have hlaw₂ := GoodReductionJacobian.nonempty_relativeGroupLaw_geometricFibre_of_nonempty_of_ker_eq
    f hproj s k₁ x₁ hx₁ k₂ x₂ hx₂ hlaw₁
  exact ⟨hsm₂, hirr₂, hdim₂, hlaw₂⟩

end L2Sol

theorem solution
    {R : Type} [CommRing R] {Z : Scheme.{0}} (f : Z ⟶ Spec (CommRingCat.of R))
    [IsProper f] [Flat f] [LocallyOfFinitePresentation f]
    (hproj : ∃ (N : ℕ) (ι : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)),
      IsClosedImmersion ι ∧ ι ≫ ProjSpace.π R N = f)
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f) (g : ℕ)
    (k₁ : Type) [Field k₁] [IsAlgClosed k₁] (x₁ : R →+* k₁)
    (k₂ : Type) [Field k₂] [IsAlgClosed k₂] (x₂ : R →+* k₂)
    (hker : RingHom.ker x₁ = RingHom.ker x₂) :
    (Smooth (pullback.snd f (Spec.map (CommRingCat.ofHom x₁))) ∧
        IrreducibleSpace ↥(pullback f (Spec.map (CommRingCat.ofHom x₁))) ∧
        topologicalKrullDim ↥(pullback f (Spec.map (CommRingCat.ofHom x₁))) = g ∧
        Nonempty (RelativeGroupLaw k₁ (pullback.snd f (Spec.map (CommRingCat.ofHom x₁))))) ↔
    (Smooth (pullback.snd f (Spec.map (CommRingCat.ofHom x₂))) ∧
        IrreducibleSpace ↥(pullback f (Spec.map (CommRingCat.ofHom x₂))) ∧
        topologicalKrullDim ↥(pullback f (Spec.map (CommRingCat.ofHom x₂))) = g ∧
        Nonempty (RelativeGroupLaw k₂ (pullback.snd f (Spec.map (CommRingCat.ofHom x₂))))) := by
  exact ⟨L2Sol.oneWay f hproj g k₁ x₁ k₂ x₂ hker, L2Sol.oneWay f hproj g k₂ x₂ k₁ x₁ hker.symm⟩

end S_GoodReductionJacobian_RelativeGroupLaw_smooth_irreducibleSpace_geometricFibre_iff_of_ker_eq_ker
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_smooth_irreducibleSpace_geometricFibre_iff_of_ker_eq_ker (solution)
