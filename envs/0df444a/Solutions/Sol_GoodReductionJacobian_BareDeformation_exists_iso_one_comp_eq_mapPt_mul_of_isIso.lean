-- Prove2me | solution 1 for GoodReductionJacobian.BareDeformation.exists_iso_one_comp_eq_mapPt_mul_of_isIso
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/29adc4dd-cf73-5af6-8f71-ea5fe6356ff7

import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_GoodReductionJacobian_BareDeformation
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_mul_comp_eq_mul_comp_of_one_comp_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_BareDeformation_exists_iso_one_comp_eq_mapPt_mul_of_isIso
p2m_attr_erase "instance" "AlgebraicGeometry.SubalgebraStages.compactSpace_pullback AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_pullback AlgebraicGeometry.SubalgebraStages.compactSpace_obj AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_obj AlgebraicGeometry.SubalgebraStages.quasiCompact_snd AlgebraicGeometry.SubalgebraStages.isAffineHom_leg AlgebraicGeometry.SubalgebraStages.isAffineHom_trans AlgebraicGeometry.SubalgebraStages.isAffineHom_diagram_map AlgebraicGeometry.SubalgebraStages.quasiSeparated_snd AlgebraicGeometry.SubalgebraStages.isCofiltered_op IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial AdicCompletion.instIsLocalRingMaximalIdeal"
p2m_attr_erase "simp" "GoodReductionJacobian.prodInr_comp_prodFst GoodReductionJacobian.RelativeGroupLaw.prod_inv GoodReductionJacobian.prodInl_comp_prodSnd GoodReductionJacobian.prodInr_comp_prodSnd GoodReductionJacobian.prodInl_comp_prodFst GoodReductionJacobian.prodFstPt_prodPairPt GoodReductionJacobian.prodFst_coe GoodReductionJacobian.prodSndPt_prodPairPt GoodReductionJacobian.RelativeGroupLaw.prod_one GoodReductionJacobian.prodPairPt_coe GoodReductionJacobian.prodPairPt_prodFstPt_prodSndPt GoodReductionJacobian.prodFstPt_coe GoodReductionJacobian.RelativeGroupLaw.prod_mul GoodReductionJacobian.prodSndPt_coe GoodReductionJacobian.prodSnd_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe AlgebraicGeometry.SubalgebraStages.specCone_π_app AlgebraicGeometry.SubalgebraStages.specLeg_specHom AlgebraicGeometry.SubalgebraStages.specLeg_specTrans AlgebraicGeometry.SubalgebraStages.cone_pt AlgebraicGeometry.SubalgebraStages.trans_fst AlgebraicGeometry.SubalgebraStages.diagram_obj AlgebraicGeometry.SubalgebraStages.leg_snd AlgebraicGeometry.SubalgebraStages.diagram_map AlgebraicGeometry.SubalgebraStages.specTrans_refl AlgebraicGeometry.SubalgebraStages.trans_snd AlgebraicGeometry.SubalgebraStages.specTrans_specHom AlgebraicGeometry.SubalgebraStages.specCone_pt AlgebraicGeometry.SubalgebraStages.cone_π_app AlgebraicGeometry.SubalgebraStages.specDiagram_map AlgebraicGeometry.SubalgebraStages.specDiagram_obj AlgebraicGeometry.SubalgebraStages.leg_fst AlgebraicGeometry.SubalgebraStages.leg_trans IsDirectLimit.Module.linearEquiv_symm_apply"
p2m_attr_erase "simp" "IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst RegularLocalRingQuotientAscent.dualNumberFst_apply GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension"
p2m_attr_erase "simp" "NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc"

set_option autoImplicit false

p2m_open "CategoryTheory AlgebraicGeometry NeronModelInfra~schemeHomOverComp~schemeHomOverComp_coe GoodReductionJacobian P2MW.S_GoodReductionJacobian_BareDeformation_exists_iso_one_comp_eq_mapPt_mul_of_isIso.GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.QM"
open scoped TensorProduct

noncomputable section

namespace GoodReductionJacobian
p2m_export "GoodReductionJacobian" "schemeHomOverComp schemeHomOverComp_coe RelativeGroupLaw AbelianSchemePropertyBundle BareDeformation AbelianSchemePropertyBundle.mul_comp_eq_mul_comp_of_one_comp_eq_one"
namespace P2mIsoUpgrade
p2m_open "GoodReductionJacobian"

universe u

section Translation

variable {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)

def secPt (τ : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    SchemeHomOver t f :=
  schemeHomOverComp t (Category.comp_id t) τ

@[scoped simp] theorem secPt_coe (τ : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    (secPt τ t).1 = t ≫ τ.1 := rfl

theorem schemeHomOverComp_secPt (τ : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f) {T T' : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (t' : T' ⟶ Spec (CommRingCat.of R)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') :
    schemeHomOverComp ψ hψ (secPt τ t) = secPt τ t' :=
  Subtype.ext (by simp only [schemeHomOverComp_coe, secPt_coe, ← Category.assoc, hψ])

theorem secPt_id (τ : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f) : secPt τ (𝟙 _) = τ :=
  Subtype.ext (Category.id_comp _)

def idPt (f : A ⟶ Spec (CommRingCat.of R)) : SchemeHomOver f f := ⟨𝟙 A, Category.id_comp f⟩

def transl (τ : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f) : A ⟶ A := (L.mul f (idPt f) (secPt τ f)).1

theorem transl_comp (τ : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f) : transl L τ ≫ f = f := (L.mul f (idPt f) (secPt τ f)).2

theorem mapPt_transl (τ : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f) {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    (P : SchemeHomOver t f) : mapPt (transl L τ) (transl_comp L τ) P = L.mul t P (secPt τ t) := by
  have h := L.mul_natural f t P.1 P.2 (idPt f) (secPt τ f)
  have h1 : schemeHomOverComp P.1 P.2 (idPt f) = P := Subtype.ext (Category.comp_id _)
  rw [h1, schemeHomOverComp_secPt] at h
  exact h

theorem transl_comp_transl_inv (τ : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f) :
    transl L τ ≫ transl L (L.inv (𝟙 _) τ) = 𝟙 A := by
  have h : mapPt (transl L (L.inv (𝟙 _) τ)) (transl_comp L _) (mapPt (transl L τ) (transl_comp L τ) (idPt f)) = idPt f := by
    rw [mapPt_transl, mapPt_transl, L.mul_assoc]
    have : L.mul f (secPt τ f) (secPt (L.inv (𝟙 _) τ) f) = L.one f := by
      rw [secPt, secPt, ← L.mul_natural, L.mul_inv_cancel, L.one_natural]
    rw [this, L.mul_one]
  have := congrArg Subtype.val h
  simpa only [mapPt_coe, idPt, Category.id_comp] using this

theorem transl_inv_comp_transl (τ : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f) :
    transl L (L.inv (𝟙 _) τ) ≫ transl L τ = 𝟙 A := by
  have h : mapPt (transl L τ) (transl_comp L τ) (mapPt (transl L (L.inv (𝟙 _) τ)) (transl_comp L _) (idPt f)) = idPt f := by
    rw [mapPt_transl, mapPt_transl, L.mul_assoc]
    have : L.mul f (secPt (L.inv (𝟙 _) τ) f) (secPt τ f) = L.one f := by
      rw [secPt, secPt, ← L.mul_natural, L.inv_mul_cancel, L.one_natural]
    rw [this, L.mul_one]
  have := congrArg Subtype.val h
  simpa only [mapPt_coe, idPt, Category.id_comp] using this

def translIso (τ : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f) : A ≅ A where
  hom := transl L τ
  inv := transl L (L.inv (𝟙 _) τ)
  hom_inv_id := transl_comp_transl_inv L τ
  inv_hom_id := transl_inv_comp_transl L τ

theorem eq_one_of_mul_self {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f)
    (h : L.mul t x x = x) : x = L.one t := by
  have := congrArg (L.mul t (L.inv t x)) h
  rwa [← L.mul_assoc, L.inv_mul_cancel, L.one_mul] at this

end Translation

theorem one_comp_g {S : Type} [CommRing S] {Aₛ : Scheme.{0}} {fₛ : Aₛ ⟶ Spec (CommRingCat.of S)} {Lₛ : RelativeGroupLaw S fₛ}
    {B : Type} [CommRing B] [Algebra B S] (D : BareDeformation fₛ Lₛ B)
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) :
    (Lₛ.one t).1 ≫ D.g = (D.L.one (t ≫ Spec.map (CommRingCat.ofHom (algebraMap B S)))).1 := by
  have h := D.hom t (Lₛ.one t) (Lₛ.one t)
  rw [Lₛ.one_mul] at h
  have : (⟨(Lₛ.one t).1 ≫ D.g, by rw [Category.assoc, D.cart.w, ← Category.assoc, (Lₛ.one t).2]⟩ :
      SchemeHomOver (t ≫ Spec.map (CommRingCat.ofHom (algebraMap B S))) D.f) = D.L.one _ :=
    eq_one_of_mul_self D.L _ _ (Subtype.ext h).symm
  exact congrArg Subtype.val this

end GoodReductionJacobian.P2mIsoUpgrade
p2m_reactivate "P2MW.S_GoodReductionJacobian_BareDeformation_exists_iso_one_comp_eq_mapPt_mul_of_isIso.GoodReductionJacobian P2MW.S_GoodReductionJacobian_BareDeformation_exists_iso_one_comp_eq_mapPt_mul_of_isIso.GoodReductionJacobian.P2mIsoUpgrade"
p2m_reactivate "P2MW.S_GoodReductionJacobian_BareDeformation_exists_iso_one_comp_eq_mapPt_mul_of_isIso.GoodReductionJacobian"

end
p2m_reactivate "P2MW.S_GoodReductionJacobian_BareDeformation_exists_iso_one_comp_eq_mapPt_mul_of_isIso.GoodReductionJacobian P2MW.S_GoodReductionJacobian_BareDeformation_exists_iso_one_comp_eq_mapPt_mul_of_isIso.GoodReductionJacobian.P2mIsoUpgrade"

open GoodReductionJacobian.P2mIsoUpgrade in

theorem solution
    (B B₁ : Type) [CommRing B] [CommRing B₁] [Algebra B B₁]
    {A₁ : Scheme.{0}} {f₁ : A₁ ⟶ Spec (CommRingCat.of B₁)} {L₁ : RelativeGroupLaw B₁ f₁}
    (D D' : BareDeformation f₁ L₁ B) (h : D.IsIso D') :
    ∃ (e : D.A ≅ D'.A) (he : e.hom ≫ D'.f = D.f), D.g ≫ e.hom = D'.g ∧
      (D.L.one (𝟙 _)).1 ≫ e.hom = (D'.L.one (𝟙 _)).1 ∧
      ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (P Q : SchemeHomOver t D.f),
        mapPt e.hom he (D.L.mul t P Q) = D'.L.mul t (mapPt e.hom he P) (mapPt e.hom he Q) := by
  obtain ⟨e, he, hge⟩ := h
  have he' : e.inv ≫ D.f = D'.f := by rw [← he, e.inv_hom_id_assoc]

  let s₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of B))) D.f := mapPt e.inv he' (D'.L.one (𝟙 _))
  let e' : D.A ≅ D'.A := translIso D.L s₀ ≪≫ e
  have he'f : e'.hom ≫ D'.f = D.f := by
    show (transl D.L s₀ ≫ e.hom) ≫ D'.f = D.f
    rw [Category.assoc, he, transl_comp]

  have hone : (D.L.one (𝟙 _)).1 ≫ e'.hom = (D'.L.one (𝟙 _)).1 := by
    show (D.L.one (𝟙 _)).1 ≫ transl D.L s₀ ≫ e.hom = (D'.L.one (𝟙 _)).1
    have h1 : (D.L.one (𝟙 _)).1 ≫ transl D.L s₀ = s₀.1 := by
      have := congrArg Subtype.val (mapPt_transl D.L s₀ (D.L.one (𝟙 _)))
      rw [D.L.one_mul, secPt_id] at this
      exact this
    rw [← Category.assoc, h1]
    show ((D'.L.one (𝟙 _)).1 ≫ e.inv) ≫ e.hom = _
    rw [Category.assoc, e.inv_hom_id, Category.comp_id]

  have hgs : D.g ≫ transl D.L s₀ = D.g := by
    let Pg : SchemeHomOver (f₁ ≫ Spec.map (CommRingCat.ofHom (algebraMap B B₁))) D.f := ⟨D.g, D.cart.w⟩
    have hsec : secPt s₀ (f₁ ≫ Spec.map (CommRingCat.ofHom (algebraMap B B₁))) =
        D.L.one (f₁ ≫ Spec.map (CommRingCat.ofHom (algebraMap B B₁))) := by
      apply Subtype.ext
      rw [secPt_coe]
      show (f₁ ≫ Spec.map (CommRingCat.ofHom (algebraMap B B₁))) ≫ (D'.L.one (𝟙 _)).1 ≫ e.inv = _
      have h2 := congrArg Subtype.val
        (D'.L.one_natural (𝟙 _) (f₁ ≫ Spec.map (CommRingCat.ofHom (algebraMap B B₁)))
          (f₁ ≫ Spec.map (CommRingCat.ofHom (algebraMap B B₁))) (Category.comp_id _))
      rw [schemeHomOverComp_coe] at h2
      rw [← Category.assoc _ _ e.inv, h2, ← one_comp_g D' f₁, Category.assoc, ← hge, Category.assoc, e.hom_inv_id,
        Category.comp_id, one_comp_g D f₁]
    have := congrArg Subtype.val (mapPt_transl D.L s₀ Pg)
    rw [hsec, D.L.mul_one] at this
    exact this
  have hge' : D.g ≫ e'.hom = D'.g := by
    show D.g ≫ transl D.L s₀ ≫ e.hom = D'.g
    rw [← Category.assoc, hgs, hge]

  haveI : IsSeparated D'.f := D'.bundle.proper.toIsSeparated
  refine ⟨e', he'f, hge', hone, ?_⟩
  intro T t P Q
  exact Subtype.ext (AbelianSchemePropertyBundle.mul_comp_eq_mul_comp_of_one_comp_eq_one D.bundle D.L D'.L e'.hom he'f hone t P Q)

end S_GoodReductionJacobian_BareDeformation_exists_iso_one_comp_eq_mapPt_mul_of_isIso
end P2MW
export P2MW.S_GoodReductionJacobian_BareDeformation_exists_iso_one_comp_eq_mapPt_mul_of_isIso (solution)
