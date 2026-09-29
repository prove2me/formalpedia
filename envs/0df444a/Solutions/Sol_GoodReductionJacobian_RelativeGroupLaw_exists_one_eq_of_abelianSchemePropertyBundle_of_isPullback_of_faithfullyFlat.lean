-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.exists_one_eq_of_abelianSchemePropertyBundle_of_isPullback_of_faithfullyFlat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/c41ebbac-5db5-599b-8117-1fcae2644479

import Mathlib
import Definitions.Def_JacJ1Iface
import Theorems.Thm_AlgebraicGeometry_existsUnique_comp_eq_of_isPullback_of_faithfullyFlat
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_comp_eq_mul_of_isPullback_of_faithfullyFlat
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_eq_of_one_eq_of_abelianSchemePropertyBundle
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_of_isPullback
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_one_eq_of_abelianSchemePropertyBundle_of_isPullback_of_faithfullyFlat
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicGeometry.SubalgebraStages.compactSpace_pullback AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_pullback AlgebraicGeometry.SubalgebraStages.compactSpace_obj AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_obj AlgebraicGeometry.SubalgebraStages.quasiCompact_snd AlgebraicGeometry.SubalgebraStages.isAffineHom_leg AlgebraicGeometry.SubalgebraStages.isAffineHom_trans AlgebraicGeometry.SubalgebraStages.isAffineHom_diagram_map AlgebraicGeometry.SubalgebraStages.quasiSeparated_snd AlgebraicGeometry.SubalgebraStages.isCofiltered_op IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty AdicCompletion.instIsLocalRingMaximalIdeal"
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring"
p2m_attr_erase "simp" "AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicGeometry.SubalgebraStages.specCone_π_app AlgebraicGeometry.SubalgebraStages.specLeg_specHom AlgebraicGeometry.SubalgebraStages.specLeg_specTrans AlgebraicGeometry.SubalgebraStages.cone_pt AlgebraicGeometry.SubalgebraStages.trans_fst AlgebraicGeometry.SubalgebraStages.diagram_obj AlgebraicGeometry.SubalgebraStages.leg_snd AlgebraicGeometry.SubalgebraStages.diagram_map AlgebraicGeometry.SubalgebraStages.specTrans_refl AlgebraicGeometry.SubalgebraStages.trans_snd AlgebraicGeometry.SubalgebraStages.specTrans_specHom"
p2m_attr_erase "simp" "AlgebraicGeometry.SubalgebraStages.specCone_pt AlgebraicGeometry.SubalgebraStages.cone_π_app AlgebraicGeometry.SubalgebraStages.specDiagram_map AlgebraicGeometry.SubalgebraStages.specDiagram_obj AlgebraicGeometry.SubalgebraStages.leg_fst AlgebraicGeometry.SubalgebraStages.leg_trans IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply"

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped TensorProduct

noncomputable section

namespace P2mWs49LawDescent

section PullbackLaw

variable {R : Type u} [CommRing R] {R' : Type u} [CommRing R']
  {ι : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R)}
  {A A' : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} {f' : A' ⟶ Spec (CommRingCat.of R')}
  {g : A' ⟶ A} (hg : IsPullback g f' f ι)

def toBase {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of R')} (x : SchemeHomOver t' f') :
    SchemeHomOver (t' ≫ ι) f :=
  ⟨x.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, x.2]⟩

def ofBase {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of R')} (y : SchemeHomOver (t' ≫ ι) f) :
    SchemeHomOver t' f' :=
  ⟨hg.lift y.1 t' y.2, hg.lift_snd _ _ _⟩

@[scoped simp] theorem toBase_coe {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of R')} (x : SchemeHomOver t' f') :
    (toBase hg x).1 = x.1 ≫ g := rfl

@[scoped simp] theorem ofBase_coe_comp {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of R')}
    (y : SchemeHomOver (t' ≫ ι) f) : (ofBase hg y).1 ≫ g = y.1 :=
  hg.lift_fst _ _ _

@[scoped simp] theorem toBase_ofBase {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of R')}
    (y : SchemeHomOver (t' ≫ ι) f) : toBase hg (ofBase hg y) = y :=
  Subtype.ext (hg.lift_fst _ _ _)

@[scoped simp] theorem ofBase_toBase {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of R')}
    (x : SchemeHomOver t' f') : ofBase hg (toBase hg x) = x :=
  Subtype.ext (hg.hom_ext (by rw [ofBase_coe_comp, toBase_coe]) (by rw [(ofBase hg _).2, x.2]))

theorem toBase_injective {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of R')}
    {x y : SchemeHomOver t' f'} (h : toBase hg x = toBase hg y) : x = y := by
  rw [← ofBase_toBase hg x, ← ofBase_toBase hg y, h]

theorem toBase_comp {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R')) (t' : T' ⟶ Spec (CommRingCat.of R'))
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x : SchemeHomOver t f') :
    toBase hg (GoodReductionJacobian.schemeHomOverComp ψ hψ x) =
      GoodReductionJacobian.schemeHomOverComp ψ (by rw [← Category.assoc, hψ]) (toBase hg x) :=
  Subtype.ext (Category.assoc _ _ _)

theorem one_coe_eq {T : Scheme.{u}} (L : RelativeGroupLaw R f) (t : T ⟶ Spec (CommRingCat.of R)) :
    (L.one t).1 = t ≫ (L.one (𝟙 (Spec (CommRingCat.of R)))).1 :=
  (congrArg Subtype.val (L.one_natural (𝟙 _) t t (Category.comp_id t))).symm

def pullbackLaw (L : RelativeGroupLaw R f) : RelativeGroupLaw R' f' where
  mul t' x y := ofBase hg (L.mul (t' ≫ ι) (toBase hg x) (toBase hg y))
  one t' := ofBase hg (L.one (t' ≫ ι))
  inv t' x := ofBase hg (L.inv (t' ≫ ι) (toBase hg x))
  mul_assoc t' x y z := by simp only [toBase_ofBase, L.mul_assoc]
  one_mul t' x := by simp only [toBase_ofBase, L.one_mul, ofBase_toBase]
  mul_one t' x := by simp only [toBase_ofBase, L.mul_one, ofBase_toBase]
  inv_mul_cancel t' x := by simp only [toBase_ofBase, L.inv_mul_cancel]
  mul_natural t t' ψ hψ x y := by
    apply toBase_injective hg
    rw [toBase_comp, toBase_ofBase, toBase_ofBase, toBase_comp, toBase_comp,
      L.mul_natural (t ≫ ι) (t' ≫ ι) ψ (by rw [← Category.assoc, hψ])]

@[scoped simp] theorem pullbackLaw_mul (L : RelativeGroupLaw R f) {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R'))
    (x y : SchemeHomOver t' f') :
    (pullbackLaw hg L).mul t' x y = ofBase hg (L.mul (t' ≫ ι) (toBase hg x) (toBase hg y)) := rfl

@[scoped simp] theorem pullbackLaw_one (L : RelativeGroupLaw R f) {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R')) :
    (pullbackLaw hg L).one t' = ofBase hg (L.one (t' ≫ ι)) := rfl

theorem pullbackLaw_mul_coe_comp (L : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t' : T ⟶ Spec (CommRingCat.of R')) (x y : SchemeHomOver t' f') :
    ((pullbackLaw hg L).mul t' x y).1 ≫ g =
      (L.mul (t' ≫ ι) ⟨x.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, x.2]⟩
        ⟨y.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, y.2]⟩).1 :=
  hg.lift_fst _ _ _

theorem pullbackLaw_one_coe_comp (L : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t' : T ⟶ Spec (CommRingCat.of R')) :
    ((pullbackLaw hg L).one t').1 ≫ g = (t' ≫ ι) ≫ (L.one (𝟙 (Spec (CommRingCat.of R)))).1 := by
  rw [pullbackLaw_one, ofBase_coe_comp, one_coe_eq]

end PullbackLaw

theorem map_one_of_map_mul {R₁ R₂ : Type u} [CommRing R₁] [CommRing R₂] {A₁ A₂ T₁ T₂ : Scheme.{u}}
    {f₁ : A₁ ⟶ Spec (CommRingCat.of R₁)} {f₂ : A₂ ⟶ Spec (CommRingCat.of R₂)}
    (G₁ : RelativeGroupLaw R₁ f₁) (G₂ : RelativeGroupLaw R₂ f₂)
    {t₁ : T₁ ⟶ Spec (CommRingCat.of R₁)} {t₂ : T₂ ⟶ Spec (CommRingCat.of R₂)}
    (φ : SchemeHomOver t₁ f₁ → SchemeHomOver t₂ f₂)
    (hφ : ∀ x y, φ (G₁.mul t₁ x y) = G₂.mul t₂ (φ x) (φ y)) :
    φ (G₁.one t₁) = G₂.one t₂ := by
  letI := G₁.pointGroup t₁
  letI := G₂.pointGroup t₂
  exact map_one (MonoidHom.mk' φ hφ)

section Cover

variable (S : Type u) [CommRing S] (S' : Type u) [CommRing S'] [Algebra S S']

abbrev ιb : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S) :=
  Spec.map (CommRingCat.ofHom (algebraMap S S'))

abbrev ι₁ : Spec (CommRingCat.of (S' ⊗[S] S')) ⟶ Spec (CommRingCat.of S') :=
  Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeft : S' →ₐ[S] S' ⊗[S] S').toRingHom)

abbrev ι₂ : Spec (CommRingCat.of (S' ⊗[S] S')) ⟶ Spec (CommRingCat.of S') :=
  Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : S' →ₐ[S] S' ⊗[S] S').toRingHom)

theorem ι₁_comp : ι₁ S S' ≫ ιb S S' = ιb S (S' ⊗[S] S') := by
  rw [ιb, ιb, ι₁, ← Spec.map_comp]
  congr 1

theorem ι₂_comp : ι₂ S S' ≫ ιb S S' = ιb S (S' ⊗[S] S') := by
  rw [ιb, ιb, ι₂, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  ext s
  simp [Algebra.algebraMap_eq_smul_one]

theorem ι₁_comp_eq_ι₂_comp : ι₁ S S' ≫ ιb S S' = ι₂ S S' ≫ ιb S S' := by
  rw [ι₁_comp, ι₂_comp]

theorem isPullback_id (X Y : Scheme.{u}) (p : X ⟶ Y) : IsPullback p (𝟙 X) (𝟙 Y) p :=
  IsPullback.of_vert_isIso ⟨by simp⟩

variable [Module.FaithfullyFlat S S']

theorem eq_of_ιb_comp_eq {Y : Scheme.{u}} {a b : Spec (CommRingCat.of S) ⟶ Y}
    (h : ιb S S' ≫ a = ιb S S' ≫ b) : a = b := by
  have hq : Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : S' →+* S' ⊗[S] S')) ≫ ιb S S' =
      ι₂ S S' ≫ ιb S S' :=
    ι₁_comp_eq_ι₂_comp S S'
  have H := AlgebraicGeometry.existsUnique_comp_eq_of_isPullback_of_faithfullyFlat
    (𝟙 (Spec (CommRingCat.of S))) (𝟙 (Spec (CommRingCat.of S'))) (ιb S S')
    (isPullback_id _ _ (ιb S S')) (𝟙 _)
    (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : S' →+* S' ⊗[S] S'))) (ι₂ S S')
    (isPullback_id _ _ _) (isPullback_id _ _ _) hq (ιb S S' ≫ b)
    (by rw [← Category.assoc, hq, Category.assoc])
  exact H.unique h rfl

end Cover

section PullbackLawAssoc

variable {R : Type u} [CommRing R] {R' : Type u} [CommRing R']
  {ι : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R)}
  {A A' : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} {f' : A' ⟶ Spec (CommRingCat.of R')}
  {g : A' ⟶ A} (hg : IsPullback g f' f ι)

theorem pullbackLaw_one_coe_comp_assoc (L : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t' : T ⟶ Spec (CommRingCat.of R')) {Z : Scheme.{u}} (h : A ⟶ Z) :
    ((pullbackLaw hg L).one t').1 ≫ g ≫ h = (t' ≫ ι) ≫ (L.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ h := by
  rw [← Category.assoc, pullbackLaw_one_coe_comp, Category.assoc]

end PullbackLawAssoc

end P2mWs49LawDescent
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_one_eq_of_abelianSchemePropertyBundle_of_isPullback_of_faithfullyFlat.P2mWs49LawDescent"

end
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_one_eq_of_abelianSchemePropertyBundle_of_isPullback_of_faithfullyFlat.P2mWs49LawDescent"

open P2mWs49LawDescent in
theorem solution
    {S : Type u} [CommRing S] (S' : Type u) [CommRing S'] [Algebra S S'] [Module.FaithfullyFlat S S']
    {A A' : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of S)) (e : SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) f)
    (f' : A' ⟶ Spec (CommRingCat.of S')) (c : A' ⟶ A)
    (hc : IsPullback c f' f (Spec.map (CommRingCat.ofHom (algebraMap S S'))))
    (hA' : AbelianSchemePropertyBundle S' f') (L' : RelativeGroupLaw S' f')
    (he' : (L'.one (𝟙 (Spec (CommRingCat.of S')))).1 ≫ c = Spec.map (CommRingCat.ofHom (algebraMap S S')) ≫ e.1) :
    ∃ L : RelativeGroupLaw S f, (L.one (𝟙 (Spec (CommRingCat.of S)))).1 = e.1 := by
  have hc' : IsPullback c f' f (ιb S S') := hc

  let A'' : Scheme.{u} := pullback f' (ι₁ S S')
  let f'' : A'' ⟶ Spec (CommRingCat.of (S' ⊗[S] S')) := pullback.snd f' (ι₁ S S')
  let a₁ : A'' ⟶ A' := pullback.fst f' (ι₁ S S')
  have ha₁ : IsPullback a₁ f'' f' (ι₁ S S') := IsPullback.of_hasPullback _ _
  have w₂ : (a₁ ≫ c) ≫ f = (f'' ≫ ι₂ S S') ≫ ιb S S' := by
    rw [Category.assoc, hc'.w, ← Category.assoc, ha₁.w, Category.assoc, ι₁_comp_eq_ι₂_comp, Category.assoc]
  let a₂ : A'' ⟶ A' := hc'.lift (a₁ ≫ c) (f'' ≫ ι₂ S S') w₂
  have ha₂c : a₂ ≫ c = a₁ ≫ c := hc'.lift_fst _ _ _
  have ha₂f : a₂ ≫ f' = f'' ≫ ι₂ S S' := hc'.lift_snd _ _ _
  have big : IsPullback (a₁ ≫ c) f'' f (ι₁ S S' ≫ ιb S S') := ha₁.paste_horiz hc'
  have big₂ : IsPullback (a₂ ≫ c) f'' f (ι₂ S S' ≫ ιb S S') := by
    rw [ha₂c, ← ι₁_comp_eq_ι₂_comp]; exact big
  have ha₂ : IsPullback a₂ f'' f' (ι₂ S S') := big₂.of_right ha₂f hc'

  have hA'' : AbelianSchemePropertyBundle (S' ⊗[S] S') f'' := hA'.of_isPullback ha₁
  have h₁ : ((pullbackLaw ha₁ L').one (𝟙 _)).1 ≫ a₁ ≫ c = ι₁ S S' ≫ ιb S S' ≫ e.1 := by
    rw [pullbackLaw_one_coe_comp_assoc, he', Category.id_comp]
  have h₂ : ((pullbackLaw ha₂ L').one (𝟙 _)).1 ≫ a₁ ≫ c = ι₂ S S' ≫ ιb S S' ≫ e.1 := by
    rw [← ha₂c, pullbackLaw_one_coe_comp_assoc, he', Category.id_comp]
  have hone : (pullbackLaw ha₁ L').one (𝟙 _) = (pullbackLaw ha₂ L').one (𝟙 _) := by
    apply Subtype.ext
    apply big.hom_ext
    · rw [h₁, h₂]
      simpa only [Category.assoc] using eq_whisker (ι₁_comp_eq_ι₂_comp S S') e.1
    · rw [((pullbackLaw ha₁ L').one _).2, ((pullbackLaw ha₂ L').one _).2]
  have hL : pullbackLaw ha₁ L' = pullbackLaw ha₂ L' :=
    GoodReductionJacobian.RelativeGroupLaw.eq_of_one_eq_of_abelianSchemePropertyBundle hA'' _ _ hone

  obtain ⟨L, hLmul, -⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.exists_relativeGroupLaw_comp_eq_mul_of_isPullback_of_faithfullyFlat
      S' f f' c hc f'' a₁ a₂ ha₁ ha₂ ha₂c.symm L' (pullbackLaw ha₁ L')
      (fun t'' x y => pullbackLaw_mul_coe_comp ha₁ L' t'' x y)
      (fun t'' x y => by rw [hL]; exact pullbackLaw_mul_coe_comp ha₂ L' t'' x y)
  refine ⟨L, ?_⟩

  have hφ : ∀ x y : SchemeHomOver (𝟙 (Spec (CommRingCat.of S'))) f',
      toBase hc' (L'.mul (𝟙 _) x y) = L.mul (𝟙 _ ≫ ιb S S') (toBase hc' x) (toBase hc' y) :=
    fun x y => Subtype.ext (hLmul (𝟙 _) x y)
  have h1 : toBase hc' (L'.one (𝟙 _)) = L.one (𝟙 _ ≫ ιb S S') :=
    map_one_of_map_mul L' L (toBase hc') hφ
  have h3 := congrArg Subtype.val h1
  rw [toBase_coe, he', one_coe_eq L (𝟙 _ ≫ ιb S S'), Category.id_comp] at h3
  exact eq_of_ιb_comp_eq S S' h3.symm

end S_GoodReductionJacobian_RelativeGroupLaw_exists_one_eq_of_abelianSchemePropertyBundle_of_isPullback_of_faithfullyFlat
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_one_eq_of_abelianSchemePropertyBundle_of_isPullback_of_faithfullyFlat (solution)
