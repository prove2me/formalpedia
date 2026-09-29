-- Prove2me | solution 1 for GoodReductionJacobian.AbelianSchemePropertyBundle.exists_submodule_pointEquiv_quotient_differentiableOn_appLE
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/91319591-58be-5f7c-ac5e-e3b308f960bf

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMModuli
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_localExp_differentiableOn_appLE_of_smoothOfRelativeDimension
import Theorems.Thm_exists_unique_monoidHom_multiplicative_eq_of_forall_norm_lt_map_add
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_tendsto_appLE_complex
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_nsmul_surjective_of_isAlgClosed_of_connectedSpace
import Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_topologicalKrullDim_le
import Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_le_topologicalKrullDim
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_smoothOfRelativeDimension_of_smooth_of_isLocalRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_submodule_pointEquiv_quotient_differentiableOn_appLE
p2m_attr_erase "instance" "PresheafOfModules.ExteriorPower.instModulePresheafAb TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype"
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf_obj PresheafOfModules.exteriorPower_map_ιMulti PresheafOfModules.ExteriorPower.appₗ_apply AlgebraicGeometry.Scheme.Modules.exteriorPower_obj AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec"
p2m_attr_erase "simp" "DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero"
p2m_attr_erase "simp" "ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.PoleDivisorPackage.mk.injEq"

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld.QM Topology Filter

namespace ExpUnif

abbrev Pt {G : Scheme.{0}} (f : G ⟶ Spec (CommRingCat.of ℂ)) : Type :=
  SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) f

section Values

variable {G : Scheme.{0}} {f : G ⟶ Spec (CommRingCat.of ℂ)}

private def _root_.ExpUnif.val (P : Pt f) (U : G.Opens) (s : Γ(G, U)) : ℂ := by
  classical
  exact if h : ⊤ ≤ P.1 ⁻¹ᵁ U then (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (P.1.appLE U ⊤ h s) else 0

p2m_export "ExpUnif" "val"
theorem val_of_le (P : Pt f) (U : G.Opens) (s : Γ(G, U)) (h : ⊤ ≤ P.1 ⁻¹ᵁ U) :
    val P U s = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (P.1.appLE U ⊤ h s) := by
  classical
  unfold val; rw [dif_pos h]

theorem appLE_eq_of_eq {X Y : Scheme.{0}} {a b : X ⟶ Y} (h : a = b) (U : Y.Opens) (V : X.Opens)
    (e : V ≤ a ⁻¹ᵁ U) : a.appLE U V e = b.appLE U V (h ▸ e) := by
  subst h; rfl

end Values

section Transl

variable {G : Scheme.{0}} {f : G ⟶ Spec (CommRingCat.of ℂ)} (L : RelativeGroupLaw ℂ f)

def liftPt (P : Pt f) : SchemeHomOver f f :=
  ⟨f ≫ P.1, by rw [Category.assoc, P.2, Category.comp_id]⟩

def idPt : SchemeHomOver f f := ⟨𝟙 G, Category.id_comp f⟩

def transl (P : Pt f) : G ⟶ G := (L.mul f (liftPt P) idPt).1

theorem transl_over (P : Pt f) : transl L P ≫ f = f := (L.mul f (liftPt P) idPt).2

theorem comp_transl_gen (P : Pt f) {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of ℂ)}
    (x : SchemeHomOver t f) :
    x.1 ≫ transl L P =
      (L.mul t ⟨t ≫ P.1, by rw [Category.assoc, P.2, Category.comp_id]⟩ x).1 := by
  have hnat := L.mul_natural f t x.1 x.2 (liftPt P) idPt
  have h1 : schemeHomOverComp x.1 x.2 (liftPt P) =
      (⟨t ≫ P.1, by rw [Category.assoc, P.2, Category.comp_id]⟩ : SchemeHomOver t f) := by
    apply Subtype.ext
    show x.1 ≫ (f ≫ P.1) = t ≫ P.1
    rw [← Category.assoc, x.2]
  have h2 : schemeHomOverComp x.1 x.2 (idPt (f := f)) = x := by
    apply Subtype.ext
    show x.1 ≫ 𝟙 G = x.1
    exact Category.comp_id _
  rw [h1, h2] at hnat
  exact congrArg Subtype.val hnat

theorem comp_transl (P Q : Pt f) :
    Q.1 ≫ transl L P = (L.mul (𝟙 _) P Q).1 := by
  rw [comp_transl_gen]
  congr 2

theorem liftPt_eq (P : Pt f) :
    liftPt P = schemeHomOverComp f (Category.comp_id f) P := by
  apply Subtype.ext; rfl

theorem transl_comp_transl (P P' : Pt f) :
    transl L P ≫ transl L P' = transl L (L.mul (𝟙 _) P' P) := by
  have h := comp_transl_gen L P' (L.mul f (liftPt P) idPt)
  change transl L P ≫ transl L P' = _ at h
  rw [h]
  have hl : (⟨f ≫ P'.1, by rw [Category.assoc, P'.2, Category.comp_id]⟩ : SchemeHomOver f f) = liftPt P' :=
    rfl
  rw [hl, ← L.mul_assoc]
  have hm : L.mul f (liftPt P') (liftPt P) = liftPt (L.mul (𝟙 _) P' P) := by
    rw [liftPt_eq, liftPt_eq, liftPt_eq, L.mul_natural]
  rw [hm]
  rfl

theorem transl_one : transl L (L.one (𝟙 _)) = 𝟙 G := by
  have h : liftPt (L.one (𝟙 _)) = L.one f := by
    rw [liftPt_eq, L.one_natural]
  show (L.mul f (liftPt (L.one (𝟙 _))) idPt).1 = 𝟙 G
  rw [h, L.one_mul]
  rfl

scoped instance isIso_transl (P : Pt f) : IsIso (transl L P) :=
  ⟨⟨transl L (L.inv (𝟙 _) P), by rw [transl_comp_transl, L.inv_mul_cancel, transl_one],
    by rw [transl_comp_transl, L.mul_inv_cancel, transl_one]⟩⟩

theorem le_preimage_mul_iff (P Q : Pt f) (U : G.Opens) :
    ⊤ ≤ (L.mul (𝟙 _) P Q).1 ⁻¹ᵁ U ↔ ⊤ ≤ Q.1 ⁻¹ᵁ (transl L P ⁻¹ᵁ U) := by
  rw [← comp_transl, Scheme.Hom.comp_preimage]

theorem val_mul (P Q : Pt f) (U : G.Opens) (s : Γ(G, U)) :
    val (L.mul (𝟙 _) P Q) U s = val Q (transl L P ⁻¹ᵁ U) ((transl L P).app U s) := by
  classical
  by_cases h : ⊤ ≤ Q.1 ⁻¹ᵁ (transl L P ⁻¹ᵁ U)
  · have h' : ⊤ ≤ (L.mul (𝟙 _) P Q).1 ⁻¹ᵁ U := (le_preimage_mul_iff L P Q U).2 h
    rw [val_of_le _ _ _ h', val_of_le _ _ _ h,
      appLE_eq_of_eq (comp_transl L P Q).symm U ⊤ h', Scheme.Hom.comp_appLE]
    rfl
  · have h' : ¬ ⊤ ≤ (L.mul (𝟙 _) P Q).1 ⁻¹ᵁ U := fun h' => h ((le_preimage_mul_iff L P Q U).1 h')
    unfold val
    rw [dif_neg h, dif_neg h']

end Transl

section Conv

variable {G : Scheme.{0}} {f : G ⟶ Spec (CommRingCat.of ℂ)} (L : RelativeGroupLaw ℂ f)

def Conv (P : ℕ → Pt f) (Q : Pt f) : Prop :=
  ∀ U : G.Opens, IsAffineOpen U → ⊤ ≤ Q.1 ⁻¹ᵁ U →
    (∀ᶠ n in atTop, ⊤ ≤ (P n).1 ⁻¹ᵁ U) ∧
      ∀ s : Γ(G, U), Tendsto (fun n => val (P n) U s) atTop (𝓝 (val Q U s))

include L in
theorem exists_conv (hA : AbelianSchemePropertyBundle ℂ f) {g : ℕ}
    (hdim : ∀ s : ↥(Spec (CommRingCat.of ℂ)), topologicalKrullDim ↥(f.base ⁻¹' {s}) = g)
    (P : ℕ → Pt f) : ∃ (Q : Pt f) (φ : ℕ → ℕ), StrictMono φ ∧ Conv (P ∘ φ) Q := by
  obtain ⟨Q, φ, hφ, H⟩ :=
    GoodReductionJacobian.AbelianSchemePropertyBundle.exists_tendsto_appLE_complex L hA hdim P
  refine ⟨Q, φ, hφ, fun U hU hQ => ?_⟩
  obtain ⟨n₀, hP, hs⟩ := H U hU hQ
  refine ⟨eventually_atTop.2 ⟨n₀, fun n hn => hP n hn⟩, fun s => ?_⟩
  rw [val_of_le _ _ _ hQ]
  refine (hs s).congr' (eventually_atTop.2 ⟨n₀, fun n hn => ?_⟩)
  show _ = val (P (φ n)) U s
  rw [dif_pos hn, val_of_le]

theorem conv_mul (P : ℕ → Pt f) (Q R : Pt f) (h : Conv P Q) :
    Conv (fun n => L.mul (𝟙 _) R (P n)) (L.mul (𝟙 _) R Q) := by
  intro U hU hQ
  have hU₁ : IsAffineOpen (transl L R ⁻¹ᵁ U) := hU.preimage_of_isIso (transl L R)
  have hQ₁ : ⊤ ≤ Q.1 ⁻¹ᵁ (transl L R ⁻¹ᵁ U) := (le_preimage_mul_iff L R Q U).1 hQ
  obtain ⟨hev, ht⟩ := h _ hU₁ hQ₁
  refine ⟨hev.mono fun n hn => (le_preimage_mul_iff L R (P n) U).2 hn, fun s => ?_⟩
  simp_rw [val_mul]
  exact ht _

end Conv

section Calculus

theorem hasFDerivAt_comp_sub_const' {E' F' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E']
    [NormedAddCommGroup F'] [NormedSpace ℂ F'] {F₀ : E' → F'} {D : E' →L[ℂ] F'} (v₀ : E')
    (h : HasFDerivAt F₀ D 0) : HasFDerivAt (fun v => F₀ (v - v₀)) D v₀ := by
  have h1 : HasFDerivAt F₀ D (v₀ - v₀) := by rwa [sub_self]
  have h2 := HasFDerivAt.comp (f := fun v => v - v₀) v₀ h1 ((hasFDerivAt_id v₀).sub_const v₀)
  simpa [Function.comp_def] using h2

theorem differentiableAt_comp_sub_const'' {E' F' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E']
    [NormedAddCommGroup F'] [NormedSpace ℂ F'] {F₀ : E' → F'} (v₀ : E')
    (h : DifferentiableAt ℂ F₀ 0) : DifferentiableAt ℂ (fun v => F₀ (v - v₀)) v₀ := by
  have h1 : DifferentiableAt ℂ F₀ (v₀ - v₀) := by rwa [sub_self]
  have h2 := DifferentiableAt.comp (f := fun v => v - v₀) v₀ h1 (differentiableAt_id.sub_const v₀)
  simpa [Function.comp_def] using h2

end Calculus

def PtGrp {G : Scheme.{0}} {f : G ⟶ Spec (CommRingCat.of ℂ)} (L : RelativeGroupLaw ℂ f)
    (_hc : L.IsCommutative) : Type := Pt f

scoped instance instCommGroupPtGrp {G : Scheme.{0}} {f : G ⟶ Spec (CommRingCat.of ℂ)} (L : RelativeGroupLaw ℂ f)
    (hc : L.IsCommutative) : CommGroup (PtGrp L hc) :=
  { L.pointGroup (𝟙 _) with mul_comm := fun x y => hc _ x y }

section Main

variable {G : Scheme.{0}} {f : G ⟶ Spec (CommRingCat.of ℂ)} (L : RelativeGroupLaw ℂ f)
  (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle ℂ f) {g : ℕ}
  (hdim : ∀ s : ↥(Spec (CommRingCat.of ℂ)), topologicalKrullDim ↥(f.base ⁻¹' {s}) = g)

include L hA hdim in
theorem smoothOfRelativeDimension : SmoothOfRelativeDimension g f := by
  haveI : Smooth f := hA.smooth
  obtain ⟨d, hd⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.exists_smoothOfRelativeDimension_of_smooth_of_isLocalRing L
  haveI := hd
  haveI : Nonempty G := ⟨(L.one (𝟙 _)).1.base (IsLocalRing.closedPoint ℂ)⟩
  have h1 := AlgebraicGeometry.SmoothOfRelativeDimension.le_topologicalKrullDim f d
  have h2 := AlgebraicGeometry.SmoothOfRelativeDimension.topologicalKrullDim_le f d
  have hG : topologicalKrullDim G = d := le_antisymm h2 h1
  let s₀ : ↥(Spec (CommRingCat.of ℂ)) := IsLocalRing.closedPoint ℂ
  have hfib : f.base ⁻¹' {s₀} = Set.univ := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    exact Subsingleton.elim _ _
  have hdim' : topologicalKrullDim ↥(f.base ⁻¹' {s₀}) = topologicalKrullDim G := by
    rw [hfib]
    exact IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ G).isHomeomorph
  have hdg' : (d : WithBot ℕ∞) = (g : WithBot ℕ∞) := by
    rw [← hG, ← hdim', hdim s₀]
  have hdg : d = g := by exact_mod_cast hdg'
  exact hdg ▸ hd

include hA in
theorem connectedSpace : ConnectedSpace G := by
  let s₀ : ↥(Spec (CommRingCat.of ℂ)) := IsLocalRing.closedPoint ℂ
  have hfib : f.base ⁻¹' {s₀} = Set.univ := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    exact Subsingleton.elim _ _
  have h := hA.connectedFibres s₀
  rw [hfib] at h
  exact connectedSpace_iff_univ.2 h

theorem nsmulPt_eq_pow (n : ℕ) (P : PtGrp L hc) :
    (nsmulPt L (𝟙 _) n P : PtGrp L hc) = P ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ, ← ih]; rfl

theorem nsmul_eq_pow (n : ℕ) (P : PtGrp L hc) :
    (L.nsmul (𝟙 _) n P : PtGrp L hc) = P ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ, ← ih]; rfl

include hA in

theorem exists_pow_eq (n : ℕ) (hn : n ≠ 0) (Q : PtGrp L hc) : ∃ P : PtGrp L hc, P ^ n = Q := by
  haveI : Smooth f := hA.smooth
  haveI : ConnectedSpace G := connectedSpace hA
  have hu : IsUnit (n : ℂ) := isUnit_iff_ne_zero.2 (Nat.cast_ne_zero.2 hn)
  obtain ⟨P, hP⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.nsmul_surjective_of_isAlgClosed_of_connectedSpace L
      (fun t x y => hc t x y) n hu Q
  exact ⟨P, by rw [← nsmul_eq_pow]; exact hP⟩

structure LED (L : RelativeGroupLaw ℂ f) (g : ℕ) where
  r : ℝ
  hr : 0 < r
  exp₀ : (Fin g → ℂ) → Pt f
  U : G.Opens
  hUaff : IsAffineOpen U
  t : Fin g → Γ(G, U)
  hU : ∀ v ∈ Metric.ball (0 : Fin g → ℂ) r, ⊤ ≤ (exp₀ v).1 ⁻¹ᵁ U
  h0 : exp₀ 0 = L.one (𝟙 _)
  hom : ∀ v w : Fin g → ℂ, v ∈ Metric.ball (0 : Fin g → ℂ) r → w ∈ Metric.ball (0 : Fin g → ℂ) r →
    v + w ∈ Metric.ball (0 : Fin g → ℂ) r → exp₀ (v + w) = L.mul (𝟙 _) (exp₀ v) (exp₀ w)
  inj : Set.InjOn exp₀ (Metric.ball (0 : Fin g → ℂ) r)
  an : ∀ (V : G.Opens) (φ : Γ(G, V)),
    IsOpen {v : Fin g → ℂ | v ∈ Metric.ball (0 : Fin g → ℂ) r ∧ ⊤ ≤ (exp₀ v).1 ⁻¹ᵁ V} ∧
    ∃ F : (Fin g → ℂ) → ℂ,
      DifferentiableOn ℂ F {v : Fin g → ℂ | v ∈ Metric.ball (0 : Fin g → ℂ) r ∧ ⊤ ≤ (exp₀ v).1 ⁻¹ᵁ V} ∧
      ∀ (v : Fin g → ℂ) (h : ⊤ ≤ (exp₀ v).1 ⁻¹ᵁ V), v ∈ Metric.ball (0 : Fin g → ℂ) r →
        F v = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((exp₀ v).1.appLE V ⊤ h) φ)
  cov : ∃ (D : (Fin g → ℂ) ≃L[ℂ] (Fin g → ℂ)) (F : (Fin g → ℂ) → (Fin g → ℂ)),
    (∀ (v : Fin g → ℂ) (hv : v ∈ Metric.ball (0 : Fin g → ℂ) r),
      F v = fun i : Fin g => (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((exp₀ v).1.appLE U ⊤ (hU v hv)) (t i))) ∧
    HasFDerivAt F (D : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ)) 0
  surj : ∃ (fs : Finset (Γ(G, U))) (ε : ℝ) (h1 : ⊤ ≤ (L.one (𝟙 (Spec (CommRingCat.of ℂ)))).1 ⁻¹ᵁ U), 0 < ε ∧
    ∀ (P : Pt f) (hP : ⊤ ≤ P.1 ⁻¹ᵁ U),
      (∀ φ ∈ fs, ‖(Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((P.1.appLE U ⊤ hP) φ) -
          (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((L.one (𝟙 (Spec (CommRingCat.of ℂ)))).1.appLE U ⊤ h1) φ)‖ < ε) →
      ∃ v ∈ Metric.ball (0 : Fin g → ℂ) r, exp₀ v = P

include hc hA hdim in
theorem nonempty_LED : Nonempty (LED L g) := by
  have hsm := smoothOfRelativeDimension L hA hdim
  obtain ⟨r, hr, exp₀, U, hUaff, t, hU, h0, hom, inj, an, cov, surj⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.exists_localExp_differentiableOn_appLE_of_smoothOfRelativeDimension L hc hsm
  exact ⟨⟨r, hr, exp₀, U, hUaff, t, hU, h0, hom, inj, an, cov, surj⟩⟩

variable (E : LED L g)

theorem exists_expHom : ∃! e : Multiplicative (Fin g → ℂ) →* PtGrp L hc,
    ∀ v : Fin g → ℂ, ‖v‖ < E.r → e (Multiplicative.ofAdd v) = E.exp₀ v :=
  exists_unique_monoidHom_multiplicative_eq_of_forall_norm_lt_map_add (A := PtGrp L hc) E.hr E.exp₀
    (fun v w hv hw hvw => E.hom v w (mem_ball_zero_iff.2 hv) (mem_ball_zero_iff.2 hw)
      (mem_ball_zero_iff.2 hvw))

def expHom : Multiplicative (Fin g → ℂ) →* PtGrp L hc := (exists_expHom L hc E).exists.choose

theorem expHom_spec (v : Fin g → ℂ) (hv : ‖v‖ < E.r) :
    expHom L hc E (Multiplicative.ofAdd v) = E.exp₀ v :=
  (exists_expHom L hc E).exists.choose_spec v hv

def ex (v : Fin g → ℂ) : Pt f := expHom L hc E (Multiplicative.ofAdd v)

theorem ex_eq (v : Fin g → ℂ) (hv : v ∈ Metric.ball (0 : Fin g → ℂ) E.r) : ex L hc E v = E.exp₀ v :=
  expHom_spec L hc E v (mem_ball_zero_iff.1 hv)

theorem ex_add (v w : Fin g → ℂ) : ex L hc E (v + w) = L.mul (𝟙 _) (ex L hc E v) (ex L hc E w) := by
  show expHom L hc E (Multiplicative.ofAdd (v + w)) =
    expHom L hc E (Multiplicative.ofAdd v) * expHom L hc E (Multiplicative.ofAdd w)
  rw [ofAdd_add, map_mul]

theorem ex_zero : ex L hc E 0 = L.one (𝟙 _) := by
  rw [ex_eq L hc E 0 (Metric.mem_ball_self E.hr), E.h0]

theorem ex_neg (v : Fin g → ℂ) : ex L hc E (-v) = L.inv (𝟙 _) (ex L hc E v) := by
  show expHom L hc E (Multiplicative.ofAdd (-v)) = (expHom L hc E (Multiplicative.ofAdd v))⁻¹
  rw [ofAdd_neg, map_inv]

theorem ex_add_of_mem (v₀ w : Fin g → ℂ) (hw : w ∈ Metric.ball (0 : Fin g → ℂ) E.r) :
    ex L hc E (v₀ + w) = L.mul (𝟙 _) (ex L hc E v₀) (E.exp₀ w) := by
  rw [ex_add, ex_eq L hc E w hw]

theorem mul_neg_add (v₀ v : Fin g → ℂ) :
    L.mul (𝟙 _) (ex L hc E (-v₀)) (ex L hc E v) = ex L hc E (v - v₀) := by
  rw [← ex_add]; congr 1; abel_nf

theorem le_preimage_ex_iff (v₀ v : Fin g → ℂ) (U : G.Opens) :
    ⊤ ≤ (ex L hc E v).1 ⁻¹ᵁ U ↔
      ⊤ ≤ (ex L hc E (v - v₀)).1 ⁻¹ᵁ (transl L (ex L hc E v₀) ⁻¹ᵁ U) := by
  rw [← le_preimage_mul_iff, ← ex_add]; congr! 2; abel_nf

theorem an_ex (Uo : G.Opens) (φ : Γ(G, Uo)) :
      IsOpen {v : Fin g → ℂ | ⊤ ≤ (ex L hc E v).1 ⁻¹ᵁ Uo} ∧
      ∃ F : (Fin g → ℂ) → ℂ,
        DifferentiableOn ℂ F {v : Fin g → ℂ | ⊤ ≤ (ex L hc E v).1 ⁻¹ᵁ Uo} ∧
        ∀ (v : Fin g → ℂ) (h : ⊤ ≤ (ex L hc E v).1 ⁻¹ᵁ Uo),
          F v = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((((ex L hc E v).1.appLE Uo ⊤ h) φ)) := by

  have key : ∀ v₀ : Fin g → ℂ, ⊤ ≤ (ex L hc E v₀).1 ⁻¹ᵁ Uo →
      ∃ S₀ : Set (Fin g → ℂ), IsOpen S₀ ∧ (0 : Fin g → ℂ) ∈ S₀ ∧
        (∀ w ∈ S₀, ⊤ ≤ (ex L hc E (v₀ + w)).1 ⁻¹ᵁ Uo) ∧
        ∃ F₀ : (Fin g → ℂ) → ℂ, DifferentiableOn ℂ F₀ S₀ ∧
          ∀ w ∈ S₀, F₀ w = val (ex L hc E (v₀ + w)) Uo φ := by
    intro v₀ hv₀
    set P := ex L hc E v₀ with hP
    set V := transl L P ⁻¹ᵁ Uo with hV
    obtain ⟨hop, F₀, hF₀, hF₀v⟩ := E.an V ((transl L P).app Uo φ)
    refine ⟨_, hop, ⟨Metric.mem_ball_self E.hr, ?_⟩, ?_, F₀, hF₀, ?_⟩
    · rw [E.h0, ← le_preimage_mul_iff, L.mul_one]; exact hv₀
    · rintro w ⟨hw, hwV⟩
      rw [ex_add_of_mem L hc E v₀ w hw, le_preimage_mul_iff]; exact hwV
    · rintro w ⟨hw, hwV⟩
      rw [hF₀v w hwV hw, ex_add_of_mem L hc E v₀ w hw, val_mul, val_of_le]
  refine ⟨?_, fun v => val (ex L hc E v) Uo φ, ?_, fun v h => val_of_le _ _ _ h⟩
  · rw [isOpen_iff_forall_mem_open]
    intro v₀ hv₀
    obtain ⟨S₀, hS₀, h0, hmem, -⟩ := key v₀ hv₀
    refine ⟨(fun v => v - v₀) ⁻¹' S₀, fun v hv => ?_, hS₀.preimage (by fun_prop), by simpa using h0⟩
    have := hmem (v - v₀) hv
    simpa using this
  · intro v₀ hv₀
    obtain ⟨S₀, hS₀, h0, hmem, F₀, hF₀, hF₀v⟩ := key v₀ hv₀
    have hnhds : (fun v => v - v₀) ⁻¹' S₀ ∈ 𝓝 v₀ :=
      (hS₀.preimage (by fun_prop)).mem_nhds (by simpa using h0)
    have heq : (fun v => val (ex L hc E v) Uo φ) =ᶠ[𝓝 v₀] (fun v => F₀ (v - v₀)) :=
      Filter.eventuallyEq_of_mem hnhds (fun v hv => by
        have hv' : v - v₀ ∈ S₀ := hv
        show val (ex L hc E v) Uo φ = F₀ (v - v₀)
        rw [hF₀v _ hv', add_sub_cancel])
    have hd : DifferentiableAt ℂ (fun v => F₀ (v - v₀)) v₀ :=
      differentiableAt_comp_sub_const'' v₀ (hF₀.differentiableAt (hS₀.mem_nhds h0))
    exact ((Filter.EventuallyEq.differentiableAt_iff heq).2 hd).differentiableWithinAt

theorem cov_ex (v₀ : Fin g → ℂ) :
      ∃ (U : G.Opens) (t : Fin g → Γ(G, U)) (ε : ℝ) (D : (Fin g → ℂ) ≃L[ℂ] (Fin g → ℂ))
        (F : (Fin g → ℂ) → (Fin g → ℂ)),
        0 < ε ∧
        (∀ v ∈ Metric.ball v₀ ε, ⊤ ≤ (ex L hc E v).1 ⁻¹ᵁ U) ∧
        (∀ (v : Fin g → ℂ) (h : ⊤ ≤ (ex L hc E v).1 ⁻¹ᵁ U), v ∈ Metric.ball v₀ ε →
          F v = fun i : Fin g => (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((((ex L hc E v).1.appLE U ⊤ h) (t i)))) ∧
        HasFDerivAt F (D : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ)) v₀ := by
  obtain ⟨D, F₀, hF₀, hD⟩ := E.cov
  set τ := transl L (ex L hc E (-v₀)) with hτ
  have hmem : ∀ v ∈ Metric.ball v₀ E.r, v - v₀ ∈ Metric.ball (0 : Fin g → ℂ) E.r := fun v hv => by
    simpa [mem_ball_zero_iff, Metric.mem_ball, dist_eq_norm] using hv
  refine ⟨τ ⁻¹ᵁ E.U, fun i => (transl L (ex L hc E (-v₀))).app E.U (E.t i), E.r, D,
    fun v => F₀ (v - v₀), E.hr, fun v hv => ?_, fun v h hv => ?_, ?_⟩
  · rw [← le_preimage_mul_iff, mul_neg_add, ex_eq L hc E _ (hmem v hv)]
    exact E.hU _ (hmem v hv)
  · show F₀ (v - v₀) = _
    rw [hF₀ _ (hmem v hv)]
    funext i
    beta_reduce
    rw [← val_of_le, ← val_of_le, ← val_mul, mul_neg_add, ex_eq L hc E _ (hmem v hv)]
  · exact hasFDerivAt_comp_sub_const' v₀ hD

def H : Subgroup (PtGrp L hc) := (expHom L hc E).range

theorem ex_mem_H (v : Fin g → ℂ) : (ex L hc E v : PtGrp L hc) ∈ H L hc E := ⟨Multiplicative.ofAdd v, rfl⟩

theorem eventually_exists_of_conv_one (P : ℕ → Pt f) (h : Conv P (L.one (𝟙 _))) :
    ∀ᶠ n in atTop, ∃ v ∈ Metric.ball (0 : Fin g → ℂ) E.r, E.exp₀ v = P n := by
  obtain ⟨fs, ε, h1, hε, hs⟩ := E.surj
  obtain ⟨hev, ht⟩ := h E.U E.hUaff h1
  have hclose : ∀ᶠ n in atTop, ∀ φ ∈ fs, ‖val (P n) E.U φ - val (L.one (𝟙 _)) E.U φ‖ < ε := by
    rw [Filter.eventually_all_finset]
    intro φ hφ
    have := (ht φ).sub_const (val (L.one (𝟙 _)) E.U φ)
    rw [sub_self] at this
    exact (NormedAddGroup.tendsto_nhds_zero.1 this) ε hε
  filter_upwards [hev, hclose] with n hn hcl
  refine hs (P n) hn fun φ hφ => ?_
  rw [← val_of_le, ← val_of_le]
  exact hcl φ hφ

include hA hdim in
theorem finite_quotient : Finite (PtGrp L hc ⧸ H L hc E) := by
  by_contra hinf
  haveI : Infinite (PtGrp L hc ⧸ H L hc E) := not_finite_iff_infinite.1 hinf
  let q : ℕ ↪ PtGrp L hc ⧸ H L hc E := Infinite.natEmbedding _
  let P : ℕ → PtGrp L hc := fun n => (q n).out
  have hPq : ∀ n, (QuotientGroup.mk (P n) : PtGrp L hc ⧸ H L hc E) = q n := fun n => (q n).out_eq
  obtain ⟨Q, φ, hφ, hconv⟩ := exists_conv L hA hdim P
  let Q' : PtGrp L hc := Q
  have hconv' := conv_mul L (P ∘ φ) Q (L.inv (𝟙 _) Q) hconv
  rw [L.inv_mul_cancel] at hconv'
  obtain ⟨N, hN⟩ := eventually_atTop.1 (eventually_exists_of_conv_one L E _ hconv')
  have hcoset : ∀ n, N ≤ n →
      (QuotientGroup.mk (P (φ n)) : PtGrp L hc ⧸ H L hc E) = QuotientGroup.mk Q' := by
    intro n hn
    obtain ⟨v, hv, hvP⟩ := hN n hn
    have hmem : Q'⁻¹ * P (φ n) ∈ H L hc E := by
      have h3 : (E.exp₀ v : PtGrp L hc) ∈ H L hc E := by
        rw [← ex_eq L hc E v hv]; exact ex_mem_H L hc E v
      have h4 : (E.exp₀ v : PtGrp L hc) = Q'⁻¹ * P (φ n) := hvP
      rwa [h4] at h3
    rw [eq_comm, QuotientGroup.eq]
    exact hmem
  have h1 := hcoset N le_rfl
  have h2 := hcoset (N + 1) (Nat.le_succ N)
  rw [hPq, ← h2, hPq] at h1
  exact absurd (q.injective h1) (ne_of_lt (hφ (Nat.lt_succ_self N)))

include hA hdim in
theorem H_eq_top : H L hc E = ⊤ := by
  haveI := finite_quotient L hc hA hdim E
  rw [eq_top_iff]
  intro Q _
  set m := Nat.card (PtGrp L hc ⧸ H L hc E) with hm
  have hm0 : m ≠ 0 := Nat.card_pos.ne'
  have hpow : ∀ R : PtGrp L hc, R ^ m ∈ H L hc E := fun R => by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact pow_card_eq_one'
  obtain ⟨P, hP⟩ := exists_pow_eq L hc hA m hm0 Q
  rw [← hP]; exact hpow P

include hA hdim in
theorem ex_surjective : Function.Surjective (ex L hc E) := by
  intro Q
  have hQ : (Q : PtGrp L hc) ∈ H L hc E := by rw [H_eq_top L hc hA hdim E]; trivial
  obtain ⟨v, hv⟩ := hQ
  exact ⟨Multiplicative.toAdd v, hv⟩

def expAdd : (Fin g → ℂ) →+ Additive (PtGrp L hc) := MonoidHom.toAdditiveRight (expHom L hc E)

theorem expAdd_apply (v : Fin g → ℂ) : expAdd L hc E v = Additive.ofMul (ex L hc E v) := rfl

def Λ : Submodule ℤ (Fin g → ℂ) := (expAdd L hc E).ker.toIntSubmodule

theorem Λ_toAddSubgroup : (Λ L hc E).toAddSubgroup = (expAdd L hc E).ker := rfl

theorem mem_Λ_iff (v : Fin g → ℂ) : v ∈ Λ L hc E ↔ ex L hc E v = L.one (𝟙 _) := by
  show v ∈ (expAdd L hc E).ker ↔ _
  rw [AddMonoidHom.mem_ker]
  rfl

theorem eq_zero_of_mem_Λ_of_mem_ball (v : Fin g → ℂ) (hv : v ∈ Λ L hc E)
    (hb : v ∈ Metric.ball (0 : Fin g → ℂ) E.r) : v = 0 := by
  rw [mem_Λ_iff, ex_eq L hc E v hb, ← E.h0] at hv
  exact E.inj hb (Metric.mem_ball_self E.hr) hv

scoped instance discreteTopology_Λ : DiscreteTopology (Λ L hc E) := by
  rw [discreteTopology_iff_isOpen_singleton_zero]
  have : ({0} : Set (Λ L hc E)) = Subtype.val ⁻¹' Metric.ball (0 : Fin g → ℂ) E.r := by
    ext ⟨v, hv⟩
    simp only [Set.mem_singleton_iff, Set.mem_preimage]
    constructor
    · intro h
      have hv0 : v = 0 := congrArg Subtype.val h
      rw [hv0]; exact Metric.mem_ball_self E.hr
    · intro h; exact Subtype.ext (eq_zero_of_mem_Λ_of_mem_ball L hc E v hv h)
  rw [this]
  exact Metric.isOpen_ball.preimage continuous_subtype_val

include hA hdim in

theorem exists_covering_radius : ∃ R : ℝ, ∀ v : Fin g → ℂ, ∃ l ∈ Λ L hc E, ‖v - l‖ ≤ R := by
  by_contra hcon
  push Not at hcon
  choose v hv using fun n : ℕ => hcon n
  obtain ⟨Q, φ, hφ, hconv⟩ := exists_conv L hA hdim (fun n => ex L hc E (v n))
  obtain ⟨w, rfl⟩ := ex_surjective L hc hA hdim E Q
  have hconv' := conv_mul L _ _ (ex L hc E (-w)) hconv
  rw [← ex_add, neg_add_cancel, ex_zero] at hconv'
  obtain ⟨N, hN⟩ := eventually_atTop.1 (eventually_exists_of_conv_one L E _ hconv')
  obtain ⟨N', hN'⟩ := exists_nat_gt (‖w‖ + E.r)
  obtain ⟨u, hu, huP⟩ := hN (max N N') (le_max_left _ _)
  simp only [Function.comp_apply] at huP
  rw [mul_neg_add, ← ex_eq L hc E u hu] at huP

  have hl : v (φ (max N N')) - w - u ∈ Λ L hc E := by
    rw [mem_Λ_iff, sub_eq_add_neg, ex_add, ← huP, ex_neg, L.mul_inv_cancel]
  have h1 := hv (φ (max N N')) _ hl
  have h2 : ‖v (φ (max N N')) - (v (φ (max N N')) - w - u)‖ ≤ ‖w‖ + E.r := by
    rw [show v (φ (max N N')) - (v (φ (max N N')) - w - u) = w + u by abel]
    exact (norm_add_le _ _).trans (by gcongr; exact (mem_ball_zero_iff.1 hu).le)
  have h3 : (N' : ℝ) ≤ (φ (max N N') : ℕ) := by
    exact_mod_cast (le_max_right N N').trans (hφ.id_le _)
  linarith

include hA hdim in
theorem span_Λ_eq_top : Submodule.span ℝ ((Λ L hc E : Set (Fin g → ℂ))) = ⊤ := by
  obtain ⟨R, hR⟩ := exists_covering_radius L hc hA hdim E
  by_contra hne
  obtain ⟨l, hl0, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
  let lc : (Fin g → ℂ) →L[ℝ] ℝ := LinearMap.toContinuousLinearMap l
  have hbound : ∀ v : Fin g → ℂ, ‖l v‖ ≤ ‖lc‖ * R := by
    intro v
    obtain ⟨m, hm, hvm⟩ := hR v
    have hlm : l m = 0 := by
      have : m ∈ Submodule.span ℝ ((Λ L hc E : Set (Fin g → ℂ))) := Submodule.subset_span hm
      exact LinearMap.mem_ker.1 (hle this)
    have : l v = lc (v - m) := by simp [lc, map_sub, hlm]
    rw [this]
    exact (lc.le_opNorm _).trans (by gcongr)
  obtain ⟨x, hx⟩ : ∃ x, l x ≠ 0 := by
    by_contra h; push Not at h; exact hl0 (LinearMap.ext h)
  have hpos : 0 < ‖l x‖ := norm_pos_iff.2 hx
  set c : ℝ := (‖lc‖ * R + 1) / ‖l x‖ with hcdef
  have h1 := hbound (c • x)
  rw [map_smul, norm_smul, Real.norm_eq_abs] at h1
  have h2 : c * ‖l x‖ = ‖lc‖ * R + 1 := by rw [hcdef, div_mul_cancel₀ _ hpos.ne']
  have h3 : c * ‖l x‖ ≤ |c| * ‖l x‖ := mul_le_mul_of_nonneg_right (le_abs_self c) (norm_nonneg _)
  linarith

include hA hdim in
theorem isZLattice_Λ : IsZLattice ℝ (Λ L hc E) := ⟨by rw [span_Λ_eq_top L hc hA hdim E]⟩

include hA hdim in
theorem exists_basis : ∃ b₀ : Module.Basis (Fin (2 * g)) ℝ (Fin g → ℂ),
    Λ L hc E = Submodule.span ℤ (Set.range b₀) := by
  haveI := isZLattice_Λ L hc hA hdim E
  let b := Module.Free.chooseBasis ℤ (Λ L hc E)
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ (Λ L hc E)) = 2 * g := by
    rw [← Module.finrank_eq_card_chooseBasisIndex, ZLattice.rank ℝ (Λ L hc E),
      Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
      Complex.finrank_real_complex, mul_comm]
  let eqv : Module.Free.ChooseBasisIndex ℤ (Λ L hc E) ≃ Fin (2 * g) := Fintype.equivFinOfCardEq hcard
  refine ⟨(b.ofZLatticeBasis ℝ (Λ L hc E)).reindex eqv, ?_⟩
  rw [Module.Basis.range_reindex, Module.Basis.ofZLatticeBasis_span]

def eAdd : (Fin g → ℂ) ⧸ (Λ L hc E).toAddSubgroup ≃+ Additive (PtGrp L hc) :=
  QuotientAddGroup.quotientKerEquivOfSurjective (expAdd L hc E)
    (fun Q => by
      obtain ⟨v, hv⟩ := ex_surjective L hc hA hdim E (Additive.toMul Q)
      exact ⟨v, by rw [expAdd_apply, hv]; rfl⟩)

def e : Pt f ≃ (Fin g → ℂ) ⧸ (Λ L hc E).toAddSubgroup :=
  (Additive.ofMul (α := PtGrp L hc)).trans (eAdd L hc hA hdim E).symm.toEquiv

theorem e_mul (P Q : Pt f) :
    e L hc hA hdim E (L.mul (𝟙 _) P Q) = e L hc hA hdim E P + e L hc hA hdim E Q := by
  let P' : PtGrp L hc := P
  let Q' : PtGrp L hc := Q
  show (eAdd L hc hA hdim E).symm (Additive.ofMul (P' * Q')) =
    (eAdd L hc hA hdim E).symm (Additive.ofMul P') + (eAdd L hc hA hdim E).symm (Additive.ofMul Q')
  rw [ofMul_mul, map_add]

theorem e_symm_coe (v : Fin g → ℂ) :
    (e L hc hA hdim E).symm (v : (Fin g → ℂ) ⧸ (Λ L hc E).toAddSubgroup) = ex L hc E v := by
  show Additive.toMul (eAdd L hc hA hdim E (v : (Fin g → ℂ) ⧸ (Λ L hc E).toAddSubgroup)) = ex L hc E v
  rfl

include hc hA hdim in
theorem final :
    ∃ (Λ : Submodule ℤ (Fin g → ℂ))
      (e : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) f ≃ ((Fin g → ℂ) ⧸ Λ.toAddSubgroup)),
      (∃ b₀ : Module.Basis (Fin (2 * g)) ℝ (Fin g → ℂ), Λ = Submodule.span ℤ (Set.range b₀)) ∧
      (∀ P Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) f, e (L.mul (𝟙 (Spec (CommRingCat.of ℂ))) P Q) = e P + e Q) ∧
      (∀ (U : G.Opens) (φ : Γ(G, U)),
      IsOpen {v : Fin g → ℂ | ⊤ ≤ (e.symm (v : (Fin g → ℂ) ⧸ Λ.toAddSubgroup)).1 ⁻¹ᵁ U} ∧
      ∃ F : (Fin g → ℂ) → ℂ,
        DifferentiableOn ℂ F {v : Fin g → ℂ | ⊤ ≤ (e.symm (v : (Fin g → ℂ) ⧸ Λ.toAddSubgroup)).1 ⁻¹ᵁ U} ∧
        ∀ (v : Fin g → ℂ) (h : ⊤ ≤ (e.symm (v : (Fin g → ℂ) ⧸ Λ.toAddSubgroup)).1 ⁻¹ᵁ U),
          F v = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((((e.symm (v : (Fin g → ℂ) ⧸ Λ.toAddSubgroup)).1.appLE U ⊤ h) φ))) ∧
      (∀ v₀ : Fin g → ℂ,
      ∃ (U : G.Opens) (t : Fin g → Γ(G, U)) (ε : ℝ) (D : (Fin g → ℂ) ≃L[ℂ] (Fin g → ℂ))
        (F : (Fin g → ℂ) → (Fin g → ℂ)),
        0 < ε ∧
        (∀ v ∈ Metric.ball v₀ ε, ⊤ ≤ (e.symm (v : (Fin g → ℂ) ⧸ Λ.toAddSubgroup)).1 ⁻¹ᵁ U) ∧
        (∀ (v : Fin g → ℂ) (h : ⊤ ≤ (e.symm (v : (Fin g → ℂ) ⧸ Λ.toAddSubgroup)).1 ⁻¹ᵁ U), v ∈ Metric.ball v₀ ε →
          F v = fun i : Fin g => (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((((e.symm (v : (Fin g → ℂ) ⧸ Λ.toAddSubgroup)).1.appLE U ⊤ h) (t i)))) ∧
        HasFDerivAt F (D : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ)) v₀) := by
  obtain ⟨E⟩ := nonempty_LED L hc hA hdim
  have key : ∀ π : (Fin g → ℂ) → Pt f, (∀ v, π v = ex L hc E v) →
      (∀ (U : G.Opens) (φ : Γ(G, U)),
      IsOpen {v : Fin g → ℂ | ⊤ ≤ (π v).1 ⁻¹ᵁ U} ∧
      ∃ F : (Fin g → ℂ) → ℂ,
        DifferentiableOn ℂ F {v : Fin g → ℂ | ⊤ ≤ (π v).1 ⁻¹ᵁ U} ∧
        ∀ (v : Fin g → ℂ) (h : ⊤ ≤ (π v).1 ⁻¹ᵁ U),
          F v = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((((π v).1.appLE U ⊤ h) φ))) ∧
      (∀ v₀ : Fin g → ℂ,
      ∃ (U : G.Opens) (t : Fin g → Γ(G, U)) (ε : ℝ) (D : (Fin g → ℂ) ≃L[ℂ] (Fin g → ℂ))
        (F : (Fin g → ℂ) → (Fin g → ℂ)),
        0 < ε ∧
        (∀ v ∈ Metric.ball v₀ ε, ⊤ ≤ (π v).1 ⁻¹ᵁ U) ∧
        (∀ (v : Fin g → ℂ) (h : ⊤ ≤ (π v).1 ⁻¹ᵁ U), v ∈ Metric.ball v₀ ε →
          F v = fun i : Fin g => (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((((π v).1.appLE U ⊤ h) (t i)))) ∧
        HasFDerivAt F (D : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ)) v₀) := by
    intro π hπ
    obtain rfl : π = ex L hc E := funext hπ
    exact ⟨an_ex L hc E, cov_ex L hc E⟩
  obtain ⟨hAN, hCOV⟩ := key (fun v => (e L hc hA hdim E).symm (v : (Fin g → ℂ) ⧸ (Λ L hc E).toAddSubgroup))
    (e_symm_coe L hc hA hdim E)
  exact ⟨Λ L hc E, e L hc hA hdim E, exists_basis L hc hA hdim E, e_mul L hc hA hdim E, hAN, hCOV⟩

end Main

end ExpUnif
p2m_reactivate "P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_submodule_pointEquiv_quotient_differentiableOn_appLE.ExpUnif"

open ExpUnif in
theorem solution
    {G : Scheme.{0}} {f : G ⟶ Spec (CommRingCat.of ℂ)} (L : RelativeGroupLaw ℂ f) (hc : L.IsCommutative)
    (hA : AbelianSchemePropertyBundle ℂ f) {g : ℕ}
    (hdim : ∀ s : ↥(Spec (CommRingCat.of ℂ)), topologicalKrullDim ↥(f.base ⁻¹' {s}) = g) :
    ∃ (Λ : Submodule ℤ (Fin g → ℂ))
      (e : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) f ≃ ((Fin g → ℂ) ⧸ Λ.toAddSubgroup)),

      (∃ b₀ : Module.Basis (Fin (2 * g)) ℝ (Fin g → ℂ), Λ = Submodule.span ℤ (Set.range b₀)) ∧

      (∀ P Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) f, e (L.mul (𝟙 (Spec (CommRingCat.of ℂ))) P Q) = e P + e Q) ∧

      (∀ (U : G.Opens) (φ : Γ(G, U)),
      IsOpen {v : Fin g → ℂ | ⊤ ≤ (e.symm (v : (Fin g → ℂ) ⧸ Λ.toAddSubgroup)).1 ⁻¹ᵁ U} ∧
      ∃ F : (Fin g → ℂ) → ℂ,
        DifferentiableOn ℂ F {v : Fin g → ℂ | ⊤ ≤ (e.symm (v : (Fin g → ℂ) ⧸ Λ.toAddSubgroup)).1 ⁻¹ᵁ U} ∧
        ∀ (v : Fin g → ℂ) (h : ⊤ ≤ (e.symm (v : (Fin g → ℂ) ⧸ Λ.toAddSubgroup)).1 ⁻¹ᵁ U),
          F v = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((((e.symm (v : (Fin g → ℂ) ⧸ Λ.toAddSubgroup)).1.appLE U ⊤ h) φ))) ∧

      (∀ v₀ : Fin g → ℂ,
      ∃ (U : G.Opens) (t : Fin g → Γ(G, U)) (ε : ℝ) (D : (Fin g → ℂ) ≃L[ℂ] (Fin g → ℂ))
        (F : (Fin g → ℂ) → (Fin g → ℂ)),
        0 < ε ∧
        (∀ v ∈ Metric.ball v₀ ε, ⊤ ≤ (e.symm (v : (Fin g → ℂ) ⧸ Λ.toAddSubgroup)).1 ⁻¹ᵁ U) ∧
        (∀ (v : Fin g → ℂ) (h : ⊤ ≤ (e.symm (v : (Fin g → ℂ) ⧸ Λ.toAddSubgroup)).1 ⁻¹ᵁ U), v ∈ Metric.ball v₀ ε →
          F v = fun i : Fin g => (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((((e.symm (v : (Fin g → ℂ) ⧸ Λ.toAddSubgroup)).1.appLE U ⊤ h) (t i)))) ∧
        HasFDerivAt F (D : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ)) v₀) :=
  ExpUnif.final L hc hA hdim

end
end S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_submodule_pointEquiv_quotient_differentiableOn_appLE
end P2MW
export P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_submodule_pointEquiv_quotient_differentiableOn_appLE (solution)
