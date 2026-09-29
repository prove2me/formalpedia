-- Prove2me | solution 1 for ModularCurve.DRModelPackage.exists_swap_forall_isStrict_section_mem_range_comp_of_reading
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/1adc3492-bc72-5c1e-bb04-7831a548a6b0

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackage
import Definitions.Def_ModularCurve_DRModelLegTwoInput
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_ModularCurve_NodeDepth
import Definitions.Def_ModularCurve_LevelOneGlueData
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_JWidth
import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_NodeLocalizedPlaces
import Definitions.Def_ModularCurve_DRResolvedModelPackageV4
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import Definitions.Def_ModularCurve_X0MqResolvedTable
import Definitions.Def_ModularCurve_SpecializeModuli
import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_GluedPic0
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Theorems.Thm_ModularCurve_eq_charLGeomPlaceOfPoint_or_eq_charLGeomPlaceEquiv_placeInfty
import Theorems.Thm_ModularCurve_ord_charLGeomPlaceOfPoint_jqModC_sub_algebraMap
import Theorems.Thm_ModularCurve_PlaceSpecialization_exists_families_isStrictFst_isStrictSnd_notMem_forall_inertia_smul_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModelPackage_exists_swap_forall_isStrict_section_mem_range_comp_of_reading
p2m_attr_erase "instance" "AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.GaussReduction.isLocalHom_constToGauss AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.B3.instIsElliptic_goodModel"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.GaussReduction.constToGauss_coe AlgebraicCurve.ComponentChart.ofConstantReductionNodes_dom AlgebraicCurve.ComponentChart.ofConstantReductionNodes_placeMap AlgebraicCurve.ComponentChart.ofConstantReductionNodes_nodes AlgebraicCurve.ComponentChart.ofConstantReductionNodes_residue AlgebraicCurve.ComponentChart.ofConstantReductionNodes_integers ModularCurve.FinitePlaceLift.traceHom_coe ModularCurve.FinitePlaceLift.mk.injEq ModularCurve.FinitePlaceLift.mk.sizeOf_spec WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply AlgebraicCurve.ComponentChart.ofConstantReduction_integers AlgebraicCurve.ComponentChart.mk.sizeOf_spec AlgebraicCurve.ComponentChart.ofConstantReduction_placeMap AlgebraicCurve.ComponentChart.ofConstantReduction_nodes AlgebraicCurve.ComponentChart.mk.injEq AlgebraicCurve.ComponentChart.ofConstantReduction_dom AlgebraicCurve.Annulus.mk.sizeOf_spec AlgebraicCurve.Annulus.mk.injEq AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_towerInclBar"
p2m_attr_erase "simp" "ModularCurve.coe_towerSubstBar ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.cuspCount_one ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluX_empty WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec"
p2m_attr_erase "simp" "WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ ModularCurve.B3.cycOfCongr_apply_coe"
p2m_attr_erase "simp" "ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero HahnSeries.ramScale_apply WeierstrassCurve.veluPointMap2_zero"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve P2MW.S_ModularCurve_DRModelPackage_exists_swap_forall_isStrict_section_mem_range_comp_of_reading.ModularCurve AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve AlgebraicCurve"

open IsLocalRing ModularCurve.PlaceSpecialization
open TopologicalSpace Opposite

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "DRModel DRModel.toBase DRModelPackage qExpand jq evalAtJ ModularPolynomialData jq_mem modularFunctionFieldFull jqd_mem_full modularFunctionField_le_full IgusaScheme.jFull IgusaScheme coeffEmb coeffEmb_mem_laurentBaseChange arithmeticGalois modularFunctionFieldBar PlaceSpecialization.ProlongationTuple.jFun PlaceSpecialization.ProlongationTuple.jQFun PlaceSpecialization.ProlongationTuple jqModC modularFunctionFieldC PlaceSpecialization PlaceSpecialization.d0_j heckeAlphaBar coe_heckeAlphaBar heckeBetaBar HeckeAlphaBarIntegral HeckeBetaBarIntegral frobOnPlacesGeomLevel exists_ramification_frobenius reduceModBivar KroneckerCongruence jGeomGen jGeomGen_sub_algebraMap_ne_zero frobeniusGeomLevel_jGeomGen_sub_pow ratFuncEquivCharLOneC charLGeomPlaceEquiv charLGeomPlaceOfPoint transcendental_jqModC coeffMap_qExpand DRModel.baseChangeMap eq_charLGeomPlaceOfPoint_or_eq_charLGeomPlaceEquiv_placeInfty ord_charLGeomPlaceOfPoint_jqModC_sub_algebraMap"
namespace StrictOrientation
p2m_open "ModularCurve"

universe u v

private theorem exists_factor_of_closedPoint_mem {X Y : Scheme.{u}} (i : Y ⟶ X) [IsOpenImmersion i]
    {S : CommRingCat.{u}} [IsLocalRing S] (f : Spec S ⟶ X)
    (h : f.base (closedPoint S) ∈ Set.range i.base) :
    ∃ g : Spec S ⟶ Y, g ≫ i = f := by
  refine ⟨IsOpenImmersion.lift i f ?_, IsOpenImmersion.lift_fac i f _⟩
  rintro _ ⟨q, rfl⟩
  have hs : q ⤳ closedPoint S := IsLocalRing.specializes_closedPoint q
  exact (hs.map f.base.hom.continuous).mem_open i.isOpenEmbedding.isOpen_range h

private theorem exists_ringHom_of_closedPoint_mem {X : Scheme.{u}} {B : CommRingCat.{u}} (i : Spec B ⟶ X)
    [IsOpenImmersion i] {S : CommRingCat.{u}} [IsLocalRing S] (f : Spec S ⟶ X)
    (h : f.base (closedPoint S) ∈ Set.range i.base) :
    ∃ ψ : B ⟶ S, Spec.map ψ ≫ i = f := by
  obtain ⟨g, hg⟩ := exists_factor_of_closedPoint_mem i f h
  exact ⟨Spec.preimage g, by rw [Spec.map_preimage, hg]⟩

private theorem stalkMap_germ_appIso {X : Scheme.{u}} {B : CommRingCat.{u}} (i : Spec B ⟶ X) [IsOpenImmersion i]
    (q : ↥(Spec B)) (t : Γ(Spec B, ⊤)) :
    (i.stalkMap q).hom (X.presheaf.germ (i ''ᵁ ⊤) (i.base q) ⟨q, trivial, rfl⟩ ((i.appIso ⊤).inv t)) =
      (Spec B).presheaf.germ ⊤ q trivial t := by
  rw [Scheme.Hom.germ_stalkMap_apply, Scheme.Hom.appIso_inv_app_apply, TopCat.Presheaf.germ_res_apply]

private theorem stalkClosedPointTo_germ_appIso {X : Scheme.{u}} {B : CommRingCat.{u}} (i : Spec B ⟶ X)
    [IsOpenImmersion i] {S : CommRingCat.{u}} [IsLocalRing S] (ψ : B ⟶ S) (f : Spec S ⟶ X)
    (hf : Spec.map ψ ≫ i = f) (a : B) (hmem : f.base (closedPoint S) ∈ i ''ᵁ ⊤) :
    (Scheme.stalkClosedPointTo f).hom
        (X.presheaf.germ (i ''ᵁ ⊤) _ hmem ((i.appIso ⊤).inv ((Scheme.ΓSpecIso B).inv a))) = ψ a := by
  subst hf
  rw [Scheme.stalkClosedPointTo_comp]
  change (Scheme.stalkClosedPointTo (Spec.map ψ)).hom ((i.stalkMap ((Spec.map ψ).base (closedPoint S))).hom
    (X.presheaf.germ (i ''ᵁ ⊤) (i.base ((Spec.map ψ).base (closedPoint S))) _
      ((i.appIso ⊤).inv ((Scheme.ΓSpecIso B).inv a)))) = ψ a
  rw [stalkMap_germ_appIso]
  have h := Scheme.germ_stalkClosedPointTo_Spec ψ
  have h' := congrArg (fun φ : Γ(Spec B, ⊤) ⟶ S => φ.hom ((Scheme.ΓSpecIso B).inv a)) h
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h'
  rw [h']
  change ψ.hom ((Scheme.ΓSpecIso B).hom ((Scheme.ΓSpecIso B).inv a)) = ψ.hom a
  rw [Iso.inv_hom_id_apply]

section Eval

variable {K : Type u} [Field K] [IsAlgClosed K] {L : Type v} [Field L] [Algebra K L]

omit [IsAlgClosed K] in

private theorem stalkClosedPointTo_const (M : CurveModel K L)
    (y : {q : Spec (CommRingCat.of K) ⟶ M.C // q ≫ M.toBase = 𝟙 _}) (e : K) :
    (Scheme.stalkClosedPointTo y.1).hom
      ((M.C.presheaf.germ ⊤ (y.1.base (closedPoint K)) trivial).hom
        (M.toBase.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv e))) = e := by

  have h1 : (M.C.presheaf.germ ⊤ (y.1.base (closedPoint K)) trivial).hom
        (M.toBase.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv e)) =
      (M.toBase.stalkMap (y.1.base (closedPoint K))).hom
        (((Spec (CommRingCat.of K)).presheaf.germ ⊤ (M.toBase.base (y.1.base (closedPoint K))) trivial).hom
          ((Scheme.ΓSpecIso (CommRingCat.of K)).inv e)) := by
    rw [Scheme.Hom.germ_stalkMap_apply]
    rfl
  rw [h1]
  have h2 : (Scheme.stalkClosedPointTo y.1).hom.comp (M.toBase.stalkMap (y.1.base (closedPoint K))).hom =
      (Scheme.stalkClosedPointTo (y.1 ≫ M.toBase)).hom := by
    rw [Scheme.stalkClosedPointTo_comp]
    rfl
  have h2' := congrArg (fun φ => φ
    (((Spec (CommRingCat.of K)).presheaf.germ ⊤ (M.toBase.base (y.1.base (closedPoint K))) trivial).hom
      ((Scheme.ΓSpecIso (CommRingCat.of K)).inv e))) h2
  simp only [RingHom.comp_apply] at h2'
  rw [h2']

  have key : ∀ (f : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of K))
      (hf : Spec.map (𝟙 (CommRingCat.of K)) = f) (t : Γ(Spec (CommRingCat.of K), ⊤)),
      (Scheme.stalkClosedPointTo f).hom
        (((Spec (CommRingCat.of K)).presheaf.germ ⊤ (f.base (closedPoint K)) trivial).hom t) =
        (Scheme.ΓSpecIso (CommRingCat.of K)).hom t := by
    intro f hf t
    subst hf
    have h := Scheme.germ_stalkClosedPointTo_Spec (𝟙 (CommRingCat.of K))
    have h' := congrArg (fun φ : Γ(Spec (CommRingCat.of K), ⊤) ⟶ CommRingCat.of K => φ.hom t) h
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, Category.comp_id] at h'
    exact h'
  have hy : Spec.map (𝟙 (CommRingCat.of K)) = y.1 ≫ M.toBase := by rw [Spec.map_id, y.2]
  change (Scheme.stalkClosedPointTo (y.1 ≫ M.toBase)).hom
    (((Spec (CommRingCat.of K)).presheaf.germ ⊤ ((y.1 ≫ M.toBase).base (closedPoint K)) trivial).hom
      ((Scheme.ΓSpecIso (CommRingCat.of K)).inv e)) = e
  rw [key (y.1 ≫ M.toBase) hy, Iso.inv_hom_id_apply]

private theorem hasValue_stalkClosedPointTo (M : CurveModel K L)
    (y : {q : Spec (CommRingCat.of K) ⟶ M.C // q ≫ M.toBase = 𝟙 _})
    (U : M.C.Opens) [Nonempty U] (hU : y.1.base (closedPoint K) ∈ U) (g : Γ(M.C, U)) :
    (M.pointEquivPlace y).HasValue (M.ffEquiv.symm (M.C.germToFunctionField U g))
      ((Scheme.stalkClosedPointTo y.1).hom ((M.C.presheaf.germ U _ hU).hom g)) := by
  have hc : IsClosed ({y.1.base (closedPoint K)} : Set M.C) := (pointEquivClosedPoint M.toBase y).2
  have hw : M.pointEquivPlace y = M.placeOfPoint ⟨y.1.base (closedPoint K), hc⟩ := rfl
  rw [hw]

  let Rm : M.C.presheaf.stalk (y.1.base (closedPoint K)) →+* L :=
    (M.ffEquiv.symm : M.C.functionField ≃+* L).toRingHom.comp
      (algebraMap (M.C.presheaf.stalk (y.1.base (closedPoint K))) M.C.functionField)
  have hRm : ∀ s, Rm s = M.ffEquiv.symm (algebraMap _ M.C.functionField s) := fun s => rfl
  have hrange : Rm.range = (M.placeOfPoint ⟨y.1.base (closedPoint K), hc⟩).toValuationSubring.toSubring :=
    M.range_stalk_eq ⟨y.1.base (closedPoint K), hc⟩
  have hRmem : ∀ s, Rm s ∈ (M.placeOfPoint ⟨y.1.base (closedPoint K), hc⟩).toValuationSubring := by
    intro s
    have : Rm s ∈ Rm.range := ⟨s, rfl⟩
    rw [hrange] at this
    exact this
  have hRinj : Function.Injective Rm :=
    M.ffEquiv.symm.injective.comp (IsFractionRing.injective _ _)
  let ρ' : M.C.presheaf.stalk (y.1.base (closedPoint K)) →+*
      ↥(M.placeOfPoint ⟨y.1.base (closedPoint K), hc⟩).toValuationSubring :=
    Rm.codRestrict (M.placeOfPoint ⟨y.1.base (closedPoint K), hc⟩).toValuationSubring.toSubring hRmem
  have hbij : Function.Bijective ρ' := by
    refine ⟨fun s s' h => hRinj (congrArg
      (fun z : ↥(M.placeOfPoint ⟨y.1.base (closedPoint K), hc⟩).toValuationSubring => (z : L)) h), fun z => ?_⟩
    have hz : (z : L) ∈ Rm.range := by rw [hrange]; exact z.2
    obtain ⟨s, hs⟩ := hz
    exact ⟨s, Subtype.ext hs⟩
  let ρ : M.C.presheaf.stalk (y.1.base (closedPoint K)) ≃+*
      ↥(M.placeOfPoint ⟨y.1.base (closedPoint K), hc⟩).toValuationSubring := RingEquiv.ofBijective ρ' hbij
  have hρ : ∀ s, ((ρ s : ↥(M.placeOfPoint ⟨y.1.base (closedPoint K), hc⟩).toValuationSubring) : L) = Rm s :=
    fun s => rfl

  let const : K →+* M.C.presheaf.stalk (y.1.base (closedPoint K)) :=
    (M.C.presheaf.germ ⊤ (y.1.base (closedPoint K)) trivial).hom.comp
      (M.toBase.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)
  have hev_const : ∀ e : K, (Scheme.stalkClosedPointTo y.1).hom (const e) = e :=
    fun e => stalkClosedPointTo_const M y e
  have hRm_const : ∀ e : K, Rm (const e) = algebraMap K L e := by
    intro e
    rw [hRm]
    apply M.ffEquiv.injective
    rw [RingEquiv.apply_symm_apply, M.ffEquiv_algebraMap]
    change (M.C.presheaf.stalkSpecializes (genericPoint_specializes (y.1.base (closedPoint K)))).hom
      ((M.C.presheaf.germ ⊤ (y.1.base (closedPoint K)) trivial).hom _) = _
    rw [TopCat.Presheaf.germ_stalkSpecializes_apply]
    rfl

  have hG : M.ffEquiv.symm (M.C.germToFunctionField U g) = Rm ((M.C.presheaf.germ U _ hU).hom g) := by
    rw [hRm]
    congr 1
    change _ = (M.C.presheaf.stalkSpecializes (genericPoint_specializes (y.1.base (closedPoint K)))).hom
      ((M.C.presheaf.germ U (y.1.base (closedPoint K)) hU).hom g)
    rw [TopCat.Presheaf.germ_stalkSpecializes_apply]

  set s₀ := (M.C.presheaf.germ U _ hU).hom g with hs₀
  set e := (Scheme.stalkClosedPointTo y.1).hom s₀ with he
  have hδ : s₀ - const e ∈ IsLocalRing.maximalIdeal _ := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have hu' := hu.map (Scheme.stalkClosedPointTo y.1).hom
    rw [map_sub, hev_const, ← he, sub_self] at hu'
    exact not_isUnit_zero hu'
  have hρδ : ρ s₀ - ρ (const e) ∈ IsLocalRing.maximalIdeal _ := by
    rw [← map_sub, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    exact (IsLocalRing.mem_maximalIdeal _ |>.mp hδ) ((isUnit_map_iff ρ _).mp hu)

  have hres : IsLocalRing.residue _ (ρ s₀) = IsLocalRing.residue _ (ρ (const e)) := by
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
    exact hρδ
  have hconst : ρ (const e) =
      algebraMap K ↥(M.placeOfPoint ⟨y.1.base (closedPoint K), hc⟩).toValuationSubring e := by
    apply Subtype.ext
    rw [hρ, hRm_const, Place.coe_algebraMap]
  have hmem : M.ffEquiv.symm (M.C.germToFunctionField U g) ∈
      (M.placeOfPoint ⟨y.1.base (closedPoint K), hc⟩).toValuationSubring := by
    rw [hG]; exact hRmem _
  refine ⟨hmem, ?_⟩
  have hval : (⟨M.ffEquiv.symm (M.C.germToFunctionField U g), hmem⟩ :
      ↥(M.placeOfPoint ⟨y.1.base (closedPoint K), hc⟩).toValuationSubring) = ρ s₀ :=
    Subtype.ext (by rw [hρ, ← hG])
  rw [hval, hres, hconst, Place.residue_algebraMap]

end Eval

section Values

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

private theorem HasValue.mul' {w : Place K F} {g g' : F} {c c' : K} (h : w.HasValue g c) (h' : w.HasValue g' c') :
    w.HasValue (g * g') (c * c') := by
  obtain ⟨hm, hr⟩ := h
  obtain ⟨hm', hr'⟩ := h'
  refine ⟨mul_mem hm hm', ?_⟩
  have : (⟨g * g', mul_mem hm hm'⟩ : w.toValuationSubring) = ⟨g, hm⟩ * ⟨g', hm'⟩ := rfl
  rw [this, map_mul, hr, hr', ← map_mul]

private theorem HasValue.eq' {w : Place K F} {g : F} {c c' : K} (h : w.HasValue g c) (h' : w.HasValue g c') : c = c' := by
  obtain ⟨hm, hr⟩ := h
  obtain ⟨hm', hr'⟩ := h'
  exact (algebraMap K w.ResidueField).injective (hr.symm.trans hr')

private theorem HasValue.one' (w : Place K F) : w.HasValue (1 : F) (1 : K) :=
  ⟨one_mem _, by rw [map_one]; exact map_one _⟩

end Values

private abbrev secOf {X : Scheme.{u}} {B : CommRingCat.{u}} (i : Spec B ⟶ X) [IsOpenImmersion i] (a : B) :
    Γ(X, i ''ᵁ ⊤) :=
  (i.appIso ⊤).inv ((Scheme.ΓSpecIso B).inv a)

private theorem mem_zeroLocus_secOf_iff {X : Scheme.{u}} {B : CommRingCat.{u}} (i : Spec B ⟶ X) [IsOpenImmersion i]
    (a : B) (q : ↥(Spec B)) : i.base q ∈ X.zeroLocus {secOf i a} ↔ a ∈ q.asIdeal := by
  rw [Scheme.zeroLocus_singleton, Set.mem_compl_iff]
  have himg : X.basicOpen (secOf i a) = i ''ᵁ (Spec B).basicOpen ((Scheme.ΓSpecIso B).inv a) :=
    (Scheme.image_basicOpen i _).symm
  rw [himg]
  constructor
  · intro hnot
    by_contra ha
    apply hnot
    refine ⟨q, ?_, rfl⟩
    show q ∈ (Spec B).basicOpen ((Scheme.ΓSpecIso B).inv a)
    rw [basicOpen_eq_of_affine]
    exact ha
  · intro ha hmem
    obtain ⟨q', hq', hqq'⟩ := hmem
    have heq : q' = q := i.isOpenEmbedding.injective hqq'
    subst heq
    have hq'' : q' ∈ (Spec B).basicOpen ((Scheme.ΓSpecIso B).inv a) := hq'
    rw [basicOpen_eq_of_affine] at hq''
    exact hq'' ha

private theorem hasValue_of_factor {K : Type u} [Field K] [IsAlgClosed K] {Lf : Type v} [Field Lf] [Algebra K Lf]
    (M : CurveModel K Lf) {X : Scheme.{u}} (h : M.C ⟶ X) {B : CommRingCat.{u}} (i : Spec B ⟶ X)
    [IsOpenImmersion i] [Nonempty (h ⁻¹ᵁ (i ''ᵁ ⊤))]
    (readL : B → Lf)
    (hread : ∀ a : B, M.ffEquiv.symm (M.C.germToFunctionField (h ⁻¹ᵁ (i ''ᵁ ⊤))
      ((h.app (i ''ᵁ ⊤)).hom (secOf i a))) = readL a)
    {S : CommRingCat.{u}} [IsLocalRing S] (ι : S ⟶ CommRingCat.of K)
    (t : Spec S ⟶ X) (ψ : B ⟶ S) (hψ : Spec.map ψ ≫ i = t)
    (w : Place K Lf) (hgen : Spec.map ι ≫ t = ((M.pointEquivPlace).symm w).1 ≫ h) (a : B) :
    w.HasValue (readL a) (ι (ψ a)) := by
  set y := (M.pointEquivPlace).symm w with hy
  have hw : M.pointEquivPlace y = w := (M.pointEquivPlace).apply_symm_apply w
  have hfac : Spec.map (ψ ≫ ι) ≫ i = y.1 ≫ h := by
    rw [Spec.map_comp, Category.assoc, hψ, hgen]
  have hcU : y.1.base (closedPoint K) ∈ h ⁻¹ᵁ (i ''ᵁ ⊤) := by
    change (y.1 ≫ h).base (closedPoint K) ∈ (i ''ᵁ ⊤)
    rw [← hfac]
    exact ⟨_, trivial, rfl⟩
  have E := hasValue_stalkClosedPointTo M y (h ⁻¹ᵁ (i ''ᵁ ⊤)) hcU ((h.app (i ''ᵁ ⊤)).hom (secOf i a))
  rw [hw, hread] at E
  have hev : (Scheme.stalkClosedPointTo y.1).hom
      ((M.C.presheaf.germ (h ⁻¹ᵁ (i ''ᵁ ⊤)) _ hcU).hom ((h.app (i ''ᵁ ⊤)).hom (secOf i a))) = ι (ψ a) := by
    have h1 : (M.C.presheaf.germ (h ⁻¹ᵁ (i ''ᵁ ⊤)) _ hcU).hom ((h.app (i ''ᵁ ⊤)).hom (secOf i a)) =
        (h.stalkMap (y.1.base (closedPoint K))).hom
          ((X.presheaf.germ (i ''ᵁ ⊤) (h.base (y.1.base (closedPoint K))) hcU).hom (secOf i a)) := by
      rw [Scheme.Hom.germ_stalkMap_apply]
    rw [h1]
    have h2 : (Scheme.stalkClosedPointTo y.1).hom.comp (h.stalkMap (y.1.base (closedPoint K))).hom =
        (Scheme.stalkClosedPointTo (y.1 ≫ h)).hom := by
      rw [Scheme.stalkClosedPointTo_comp]
      rfl
    have h2' := congrArg (fun φ => φ
      ((X.presheaf.germ (i ''ᵁ ⊤) (h.base (y.1.base (closedPoint K))) hcU).hom (secOf i a))) h2
    simp only [RingHom.comp_apply] at h2'
    rw [h2']
    change (Scheme.stalkClosedPointTo (y.1 ≫ h)).hom
      ((X.presheaf.germ (i ''ᵁ ⊤) ((y.1 ≫ h).base (closedPoint K)) hcU).hom (secOf i a)) = _
    rw [stalkClosedPointTo_germ_appIso i (ψ ≫ ι) (y.1 ≫ h) hfac a]
    rfl
  rw [hev] at E
  exact E

section TwoChart

variable (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]

open AlgebraicCurve.TwoChartIntegralModel

private abbrev overlap : (TwoChartIntegralModel R F j).Opens := (ιFin R F j ''ᵁ ⊤) ⊓ (ιInf R F j ''ᵁ ⊤)

private theorem secFin_mul_secInf [IsIntegral (TwoChartIntegralModel R F j)] :
    (TwoChartIntegralModel R F j).presheaf.map (homOfLE (inf_le_left : overlap R F j ≤ _)).op
        (secOf (ιFin R F j) (jChartFin R F j)) *
      (TwoChartIntegralModel R F j).presheaf.map (homOfLE (inf_le_right : overlap R F j ≤ _)).op
        (secOf (ιInf R F j) (jInvChartInf R F j)) = 1 := by

  let X := TwoChartIntegralModel R F j
  let z₀ : ↥(XMid R F j) := ⟨⊥, Ideal.isPrime_bot⟩
  let m : XMid R F j ⟶ X := fFin R F j ≫ ιFin R F j
  have hm' : m = fInf R F j ≫ ιInf R F j := glue_condition R F j
  have hzF : m.base z₀ ∈ (ιFin R F j ''ᵁ ⊤) := ⟨(fFin R F j).base z₀, trivial, rfl⟩
  have hzI : m.base z₀ ∈ (ιInf R F j ''ᵁ ⊤) := ⟨(fInf R F j).base z₀, trivial, by rw [hm']; rfl⟩
  have hz : m.base z₀ ∈ overlap R F j := ⟨hzF, hzI⟩

  apply germ_injective_of_isIntegral _ (m.base z₀) hz
  rw [map_mul, map_one, TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply]

  haveI : IsIso (m.stalkMap z₀) := (IsOpenImmersion.iff_isIso_stalkMap.mp inferInstance).2 z₀
  have hinj : Function.Injective (m.stalkMap z₀).hom :=
    (ConcreteCategory.bijective_of_isIso (m.stalkMap z₀)).1
  apply hinj
  rw [map_mul, map_one]

  have hF : (m.stalkMap z₀).hom ((X.presheaf.germ (ιFin R F j ''ᵁ ⊤) (m.base z₀) hzF).hom
      (secOf (ιFin R F j) (jChartFin R F j))) =
      ((XMid R F j).presheaf.germ ⊤ z₀ trivial).hom
        ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgMid R F j))).inv (inclFin R F j (jChartFin R F j))) := by
    change ((fFin R F j ≫ ιFin R F j).stalkMap z₀).hom ((X.presheaf.germ (ιFin R F j ''ᵁ ⊤)
      ((ιFin R F j).base ((fFin R F j).base z₀)) hzF).hom (secOf (ιFin R F j) (jChartFin R F j))) = _
    rw [Scheme.Hom.stalkMap_comp]
    change ((fFin R F j).stalkMap z₀).hom (((ιFin R F j).stalkMap ((fFin R F j).base z₀)).hom
      ((X.presheaf.germ (ιFin R F j ''ᵁ ⊤) ((ιFin R F j).base ((fFin R F j).base z₀)) hzF).hom
        (secOf (ιFin R F j) (jChartFin R F j)))) = _
    rw [stalkMap_germ_appIso, Scheme.Hom.germ_stalkMap_apply]
    congr 1
    have hn := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (inclFin R F j).toRingHom)
    have hn' := congrArg (fun φ => φ.hom (jChartFin R F j)) hn
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at hn'
    exact hn'.symm

  have hI : (m.stalkMap z₀).hom ((X.presheaf.germ (ιInf R F j ''ᵁ ⊤) (m.base z₀) hzI).hom
      (secOf (ιInf R F j) (jInvChartInf R F j))) =
      ((XMid R F j).presheaf.germ ⊤ z₀ trivial).hom
        ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgMid R F j))).inv (inclInf R F j (jInvChartInf R F j))) := by
    rw [Scheme.Hom.stalkMap_congr_hom m (fInf R F j ≫ ιInf R F j) hm' z₀]
    rw [CommRingCat.hom_comp, RingHom.comp_apply, TopCat.Presheaf.stalkCongr_hom,
      TopCat.Presheaf.germ_stalkSpecializes_apply]
    change ((fInf R F j ≫ ιInf R F j).stalkMap z₀).hom ((X.presheaf.germ (ιInf R F j ''ᵁ ⊤)
      ((ιInf R F j).base ((fInf R F j).base z₀)) _).hom (secOf (ιInf R F j) (jInvChartInf R F j))) = _
    rw [Scheme.Hom.stalkMap_comp]
    change ((fInf R F j).stalkMap z₀).hom (((ιInf R F j).stalkMap ((fInf R F j).base z₀)).hom
      ((X.presheaf.germ (ιInf R F j ''ᵁ ⊤) ((ιInf R F j).base ((fInf R F j).base z₀))
        ⟨(fInf R F j).base z₀, trivial, rfl⟩).hom (secOf (ιInf R F j) (jInvChartInf R F j)))) = _
    rw [stalkMap_germ_appIso, Scheme.Hom.germ_stalkMap_apply]
    congr 1
    have hn := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (inclInf R F j).toRingHom)
    have hn' := congrArg (fun φ => φ.hom (jInvChartInf R F j)) hn
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at hn'
    exact hn'.symm
  rw [hF, hI, ← map_mul, ← map_mul]
  have h1 : inclFin R F j (jChartFin R F j) * inclInf R F j (jInvChartInf R F j) = 1 := by
    apply Subtype.ext
    rw [Subalgebra.coe_mul, Subalgebra.coe_one, coe_chartIncl, coe_chartIncl, coe_jChartFin, coe_jInvChartInf]
    exact mul_inv_cancel₀ (j_ne_zero j)
  rw [h1, map_one, map_one]

private theorem closedPoint_mem_range_ιFin [IsIntegral (TwoChartIntegralModel R F j)]
    {K : Type u} [Field K] [IsAlgClosed K] {Lf : Type v} [Field Lf] [Algebra K Lf]
    (M : CurveModel K Lf) (h : M.C ⟶ TwoChartIntegralModel R F j)
    [Nonempty (h ⁻¹ᵁ (ιFin R F j ''ᵁ ⊤))]
    (jL : Lf)
    (hread : M.ffEquiv.symm (M.C.germToFunctionField (h ⁻¹ᵁ (ιFin R F j ''ᵁ ⊤))
      ((h.app (ιFin R F j ''ᵁ ⊤)).hom (secOf (ιFin R F j) (jChartFin R F j)))) = jL)
    {Ar : Type*} [CommRing Ar] (inc : Ar →+* K) (hinc : Function.Injective inc)
    {S : CommRingCat.{u}} [IsLocalRing S] (ιA : S →+* Ar) [IsLocalHom ιA]
    (t : Spec S ⟶ TwoChartIntegralModel R F j) (w : Place K Lf)
    (hgen : Spec.map (CommRingCat.ofHom (inc.comp ιA)) ≫ t = ((M.pointEquivPlace).symm w).1 ≫ h)
    (hj : ∃ a : Ar, w.HasValue jL (inc a)) :
    t.base (closedPoint S) ∈ Set.range (ιFin R F j).base := by
  by_contra hnot
  have hinf : t.base (closedPoint S) ∈ Set.range (ιInf R F j).base :=
    (mem_range_ιFin_or_mem_range_ιInf R F j _).resolve_left hnot
  obtain ⟨ψ', hψ'⟩ := exists_ringHom_of_closedPoint_mem (ιInf R F j) t hinf

  have hb : ψ' (jInvChartInf R F j) ∈ maximalIdeal S := by
    by_contra hb
    apply hnot
    have hq : ((Spec.map ψ').base (closedPoint S)) ∈
        (PrimeSpectrum.basicOpen (jInvChartInf R F j) : Set (PrimeSpectrum ↥(chartAlgInf R F j))) := hb
    letI := (inclInf R F j).toRingHom.toAlgebra
    haveI := isLocalization_away_inclInf R F j
    rw [← PrimeSpectrum.localization_away_comap_range (chartAlgMid R F j) (jInvChartInf R F j)] at hq
    obtain ⟨q'', hq''⟩ := hq
    refine ⟨(fFin R F j).base q'', ?_⟩
    rw [← hψ']
    change ((fFin R F j) ≫ ιFin R F j).base q'' = (ιInf R F j).base ((Spec.map ψ').base (closedPoint S))
    rw [glue_condition]
    change (ιInf R F j).base ((fInf R F j).base q'') = _
    exact congrArg (fun x => (ιInf R F j).base x) hq''

  have hcU : ((M.pointEquivPlace).symm w).1.base (closedPoint K) ∈ h ⁻¹ᵁ (ιInf R F j ''ᵁ ⊤) := by
    change (((M.pointEquivPlace).symm w).1 ≫ h).base (closedPoint K) ∈ (ιInf R F j ''ᵁ ⊤)
    rw [← hgen, ← hψ']
    exact ⟨_, trivial, rfl⟩
  haveI : Nonempty (h ⁻¹ᵁ (ιInf R F j ''ᵁ ⊤)) := ⟨⟨_, hcU⟩⟩
  have hvalI := hasValue_of_factor M h (ιInf R F j)
    (fun b => M.ffEquiv.symm (M.C.germToFunctionField (h ⁻¹ᵁ (ιInf R F j ''ᵁ ⊤))
      ((h.app (ιInf R F j ''ᵁ ⊤)).hom (secOf (ιInf R F j) b))))
    (fun _ => rfl) (CommRingCat.ofHom (inc.comp ιA)) t ψ' hψ' w hgen (jInvChartInf R F j)
  obtain ⟨a, ha⟩ := hj

  have hprod : M.ffEquiv.symm (M.C.germToFunctionField (h ⁻¹ᵁ (ιInf R F j ''ᵁ ⊤))
      ((h.app (ιInf R F j ''ᵁ ⊤)).hom (secOf (ιInf R F j) (jInvChartInf R F j)))) * jL = 1 := by
    rw [← hread, ← map_mul]
    have key : (M.C.germToFunctionField (h ⁻¹ᵁ (ιInf R F j ''ᵁ ⊤)))
          ((h.app (ιInf R F j ''ᵁ ⊤)).hom (secOf (ιInf R F j) (jInvChartInf R F j))) *
        (M.C.germToFunctionField (h ⁻¹ᵁ (ιFin R F j ''ᵁ ⊤)))
          ((h.app (ιFin R F j ''ᵁ ⊤)).hom (secOf (ιFin R F j) (jChartFin R F j))) = 1 := by
      have hξI : genericPoint M.C ∈ h ⁻¹ᵁ (ιInf R F j ''ᵁ ⊤) :=
        ((genericPoint_spec M.C).mem_open_set_iff (h ⁻¹ᵁ (ιInf R F j ''ᵁ ⊤)).isOpen).mpr
          ⟨_, Set.mem_univ _, hcU⟩
      have hξF : genericPoint M.C ∈ h ⁻¹ᵁ (ιFin R F j ''ᵁ ⊤) :=
        ((genericPoint_spec M.C).mem_open_set_iff (h ⁻¹ᵁ (ιFin R F j ''ᵁ ⊤)).isOpen).mpr
          (by obtain ⟨⟨x, hx⟩⟩ := (inferInstance : Nonempty (h ⁻¹ᵁ (ιFin R F j ''ᵁ ⊤))); exact ⟨x, Set.mem_univ _, hx⟩)
      change (M.C.presheaf.germ (h ⁻¹ᵁ (ιInf R F j ''ᵁ ⊤)) (genericPoint M.C) hξI).hom _ *
        (M.C.presheaf.germ (h ⁻¹ᵁ (ιFin R F j ''ᵁ ⊤)) (genericPoint M.C) hξF).hom _ = 1

      have hW : genericPoint M.C ∈ h ⁻¹ᵁ overlap R F j := ⟨hξF, hξI⟩
      rw [← TopCat.Presheaf.germ_res_apply M.C.presheaf
            (homOfLE (show h ⁻¹ᵁ overlap R F j ≤ h ⁻¹ᵁ (ιInf R F j ''ᵁ ⊤) from fun _ hx => hx.2)) _ hW,
          ← TopCat.Presheaf.germ_res_apply M.C.presheaf
            (homOfLE (show h ⁻¹ᵁ overlap R F j ≤ h ⁻¹ᵁ (ιFin R F j ''ᵁ ⊤) from fun _ hx => hx.1)) _ hW,
          ← map_mul]

      have nI : M.C.presheaf.map (homOfLE (show h ⁻¹ᵁ overlap R F j ≤ h ⁻¹ᵁ (ιInf R F j ''ᵁ ⊤)
            from fun _ hx => hx.2)).op ((h.app (ιInf R F j ''ᵁ ⊤)).hom (secOf (ιInf R F j) (jInvChartInf R F j))) =
          (h.app (overlap R F j)).hom ((TwoChartIntegralModel R F j).presheaf.map
            (homOfLE (inf_le_right : overlap R F j ≤ _)).op (secOf (ιInf R F j) (jInvChartInf R F j))) := by
        have := h.naturality (homOfLE (inf_le_right : overlap R F j ≤ ιInf R F j ''ᵁ ⊤)).op
        have := congrArg (fun φ => φ.hom (secOf (ιInf R F j) (jInvChartInf R F j))) this
        simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
        exact this.symm
      have nF : M.C.presheaf.map (homOfLE (show h ⁻¹ᵁ overlap R F j ≤ h ⁻¹ᵁ (ιFin R F j ''ᵁ ⊤)
            from fun _ hx => hx.1)).op ((h.app (ιFin R F j ''ᵁ ⊤)).hom (secOf (ιFin R F j) (jChartFin R F j))) =
          (h.app (overlap R F j)).hom ((TwoChartIntegralModel R F j).presheaf.map
            (homOfLE (inf_le_left : overlap R F j ≤ _)).op (secOf (ιFin R F j) (jChartFin R F j))) := by
        have := h.naturality (homOfLE (inf_le_left : overlap R F j ≤ ιFin R F j ''ᵁ ⊤)).op
        have := congrArg (fun φ => φ.hom (secOf (ιFin R F j) (jChartFin R F j))) this
        simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
        exact this.symm
      rw [nI, nF, ← map_mul, mul_comm, secFin_mul_secInf R F j, map_one, map_one]
    rw [key, map_one]

  have hv := HasValue.mul' hvalI ha
  rw [hprod] at hv
  have h1 := HasValue.eq' hv (HasValue.one' w)

  have hunit : IsUnit (ιA (ψ' (jInvChartInf R F j))) := by
    refine IsUnit.of_mul_eq_one a (hinc ?_)
    rw [map_mul, map_one]
    exact h1
  have := (isUnit_map_iff ιA _).mp hunit
  exact (IsLocalRing.mem_maximalIdeal _ |>.mp hb) this

end TwoChart

section LevelOne

variable (k : Type) [Field k]

private theorem jGeomGen_notMem_placeInfty [DecidableEq (RatFunc k)] :
    jGeomGen k 1 ∉ (charLGeomPlaceEquiv k (RationalFunctionField.placeInfty k)).toValuationSubring := by
  intro hmem
  change (ratFuncEquivCharLOneC k).toRingEquiv.symm (jGeomGen k 1) ∈
    (RationalFunctionField.placeInfty k).toValuationSubring at hmem
  rw [RationalFunctionField.placeInfty_toValuationSubring, Valuation.mem_valuationSubring_iff] at hmem
  have hX : (ratFuncEquivCharLOneC k).toRingEquiv.symm (jGeomGen k 1) = RatFunc.X := by
    rw [RingEquiv.symm_apply_eq]
    apply Subtype.ext
    change jqModC k = ((RatFunc.algEquivOfTranscendental (jqModC k) (transcendental_jqModC k) RatFunc.X :
      ↥(IntermediateField.adjoin k {jqModC k})) : LaurentSeries k)
    rw [RatFunc.algEquivOfTranscendental_X]
  rw [hX, RatFunc.inftyValuation.X, ← WithZero.exp_zero, WithZero.exp_le_exp] at hmem
  exact absurd hmem (by norm_num)

private theorem eq_of_ord_sub_pos (N : ℕ) [NeZero N] (w : Place k (modularFunctionFieldC k N)) (a b : k)
    (ha : 0 < w.ord (jGeomGen k N - algebraMap k (modularFunctionFieldC k N) a))
    (hb : 0 < w.ord (jGeomGen k N - algebraMap k (modularFunctionFieldC k N) b)) : a = b := by
  by_contra hne
  have hm : ∀ (c : k), 0 < w.ord (jGeomGen k N - algebraMap k (modularFunctionFieldC k N) c) →
      ∃ hy : jGeomGen k N - algebraMap k (modularFunctionFieldC k N) c ∈ w.toValuationSubring,
        (⟨_, hy⟩ : w.toValuationSubring) ∈ IsLocalRing.maximalIdeal w.toValuationSubring := by
    intro c hc
    have hy : jGeomGen k N - algebraMap k (modularFunctionFieldC k N) c ∈ w.toValuationSubring :=
      w.mem_of_ord_nonneg (jGeomGen_sub_algebraMap_ne_zero k N c) hc.le
    refine ⟨hy, ?_⟩
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have h0 : w.ord (((hu.unit : w.toValuationSubringˣ) : w.toValuationSubring) :
        modularFunctionFieldC k N) = 0 := w.ord_coe_unit hu.unit
    rw [IsUnit.unit_spec] at h0
    exact absurd h0 hc.ne'
  obtain ⟨h1, hm1⟩ := hm a ha
  obtain ⟨h2, hm2⟩ := hm b hb
  have hdiff := Ideal.sub_mem _ hm2 hm1
  have hval : ((⟨jGeomGen k N - algebraMap k (modularFunctionFieldC k N) b, h2⟩ :
        w.toValuationSubring)
      - ⟨jGeomGen k N - algebraMap k (modularFunctionFieldC k N) a, h1⟩)
      = algebraMap k w.toValuationSubring (a - b) := by
    apply Subtype.ext
    simp only [AddSubgroupClass.coe_sub, Place.coe_algebraMap, map_sub]
    ring
  rw [hval] at hdiff
  have hunit : IsUnit (algebraMap k w.toValuationSubring (a - b)) :=
    (IsUnit.mk0 _ (sub_ne_zero.mpr hne)).map _
  exact (IsLocalRing.mem_maximalIdeal _).mp hdiff hunit

variable (p : ℕ) [Fact p.Prime]

private theorem ord_frob_sub_pow_pos [CharP k p] (N : ℕ) [NeZero N]
    (data : ModularPolynomialData p) (hKr : KroneckerCongruence p data)
    (w : Place k (modularFunctionFieldC k N)) (a : k)
    (ha : 0 < w.ord (jGeomGen k N - algebraMap k (modularFunctionFieldC k N) a)) :
    0 < (frobOnPlacesGeomLevel k N data hKr w).ord
      (jGeomGen k N - algebraMap k (modularFunctionFieldC k N) (a ^ p)) := by
  have hq : p.Prime := Fact.out
  have hqpos : 0 < (p : ℤ) := by exact_mod_cast hq.pos
  obtain ⟨e, he, -, hord⟩ := ModularCurve.exists_ramification_frobenius k N data hKr w
  have hkey := hord (jGeomGen k N - algebraMap k (modularFunctionFieldC k N) (a ^ p))
  rw [ModularCurve.frobeniusGeomLevel_jGeomGen_sub_pow k N data hKr a,
    ← zpow_natCast (jGeomGen k N - algebraMap k (modularFunctionFieldC k N) a) p, Place.ord_zpow] at hkey
  have he' : 0 < (e : ℤ) := by exact_mod_cast he
  have hprod : 0 < (e : ℤ) * (frobOnPlacesGeomLevel k N data hKr w).ord
      (jGeomGen k N - algebraMap k (modularFunctionFieldC k N) (a ^ p)) := by
    rw [← hkey]; exact mul_pos hqpos ha
  exact pos_of_mul_pos_right hprod he'.le

private theorem ord_frob_sub_pos_of_pow_eq [CharP k p] (N : ℕ) [NeZero N]
    (data : ModularPolynomialData p) (hKr : KroneckerCongruence p data)
    (w : Place k (modularFunctionFieldC k N)) (a a' : k) (h' : a ^ p = a')
    (ha : 0 < w.ord (jGeomGen k N - algebraMap k (modularFunctionFieldC k N) a)) :
    0 < (frobOnPlacesGeomLevel k N data hKr w).ord
      (jGeomGen k N - algebraMap k (modularFunctionFieldC k N) a') := by
  subst h'
  exact ord_frob_sub_pow_pos k p N data hKr w a ha

private theorem not_ord_sub_pos_placeInfty [DecidableEq (RatFunc k)] (c : k) :
    ¬ 0 < (charLGeomPlaceEquiv k (RationalFunctionField.placeInfty k)).ord
      (jGeomGen k 1 - algebraMap k (modularFunctionFieldC k 1) c) := by
  intro hc
  apply jGeomGen_notMem_placeInfty k
  have hmem := (charLGeomPlaceEquiv k (RationalFunctionField.placeInfty k)).mem_of_ord_nonneg
    (jGeomGen_sub_algebraMap_ne_zero k 1 c) hc.le
  have := add_mem hmem ((charLGeomPlaceEquiv k (RationalFunctionField.placeInfty k)).algebraMap_mem' c)
  rwa [sub_add_cancel] at this

private theorem eq_of_ord_sub_pos_levelOne [IsAlgClosed k] (v v' : Place k (modularFunctionFieldC k 1)) (c : k)
    (hv : 0 < v.ord (jGeomGen k 1 - algebraMap k (modularFunctionFieldC k 1) c))
    (hv' : 0 < v'.ord (jGeomGen k 1 - algebraMap k (modularFunctionFieldC k 1) c)) : v = v' := by
  classical
  have key : ∀ u : Place k (modularFunctionFieldC k 1),
      0 < u.ord (jGeomGen k 1 - algebraMap k (modularFunctionFieldC k 1) c) → u = charLGeomPlaceOfPoint k c := by
    intro u hu
    rcases ModularCurve.eq_charLGeomPlaceOfPoint_or_eq_charLGeomPlaceEquiv_placeInfty k u with ⟨c₁, rfl⟩ | rfl
    · have h := ModularCurve.ord_charLGeomPlaceOfPoint_jqModC_sub_algebraMap k c₁ c
      change (charLGeomPlaceOfPoint k c₁).ord (jGeomGen k 1 - _) = _ at h
      rw [h] at hu
      split_ifs at hu with hc
      · rw [hc]
      · exact absurd hu (lt_irrefl 0)
    · exfalso
      apply jGeomGen_notMem_placeInfty k
      have hmem := (charLGeomPlaceEquiv k (RationalFunctionField.placeInfty k)).mem_of_ord_nonneg
        (jGeomGen_sub_algebraMap_ne_zero k 1 c) hu.le
      have := add_mem hmem ((charLGeomPlaceEquiv k (RationalFunctionField.placeInfty k)).algebraMap_mem' c)
      rwa [sub_add_cancel] at this
  rw [key v hv, key v' hv']

private theorem eq_placeInfty_of_ord_neg [IsAlgClosed k] [DecidableEq (RatFunc k)] (u : Place k (modularFunctionFieldC k 1))
    (hu : u.ord (jGeomGen k 1) < 0) : u = charLGeomPlaceEquiv k (RationalFunctionField.placeInfty k) := by
  classical
  rcases ModularCurve.eq_charLGeomPlaceOfPoint_or_eq_charLGeomPlaceEquiv_placeInfty k u with ⟨c₁, rfl⟩ | h
  · exfalso
    have h := ModularCurve.ord_charLGeomPlaceOfPoint_jqModC_sub_algebraMap k c₁ c₁
    rw [if_pos rfl] at h
    change (charLGeomPlaceOfPoint k c₁).ord (jGeomGen k 1 - _) = 1 at h
    have hmem := (charLGeomPlaceOfPoint k c₁).mem_of_ord_nonneg (jGeomGen_sub_algebraMap_ne_zero k 1 c₁)
      (by rw [h]; exact zero_le_one)
    have hj := add_mem hmem ((charLGeomPlaceOfPoint k c₁).algebraMap_mem' c₁)
    rw [sub_add_cancel] at hj
    exact absurd ((charLGeomPlaceOfPoint k c₁).ord_nonneg_of_mem hj) (not_le.mpr hu)
  · exact h

private theorem frob_placeInfty [CharP k p] [IsAlgClosed k] [DecidableEq (RatFunc k)] (data : ModularPolynomialData p) (hKr : KroneckerCongruence p data) :
    frobOnPlacesGeomLevel k 1 data hKr (charLGeomPlaceEquiv k (RationalFunctionField.placeInfty k)) =
      charLGeomPlaceEquiv k (RationalFunctionField.placeInfty k) := by
  classical
  rcases ModularCurve.eq_charLGeomPlaceOfPoint_or_eq_charLGeomPlaceEquiv_placeInfty k
      (frobOnPlacesGeomLevel k 1 data hKr (charLGeomPlaceEquiv k (RationalFunctionField.placeInfty k))) with
    ⟨c', hc'⟩ | h
  · exfalso
    obtain ⟨d, hd⟩ := IsAlgClosed.exists_pow_nat_eq c' (Fact.out : p.Prime).pos
    have h1 := ModularCurve.ord_charLGeomPlaceOfPoint_jqModC_sub_algebraMap k c' c'
    rw [if_pos rfl] at h1
    change (charLGeomPlaceOfPoint k c').ord (jGeomGen k 1 - _) = 1 at h1
    rw [← hc', ← hd] at h1
    obtain ⟨e, he, -, hord⟩ := ModularCurve.exists_ramification_frobenius k 1 data hKr
      (charLGeomPlaceEquiv k (RationalFunctionField.placeInfty k))
    have h2 := hord (jGeomGen k 1 - algebraMap k (modularFunctionFieldC k 1) (d ^ p))
    rw [ModularCurve.frobeniusGeomLevel_jGeomGen_sub_pow k 1 data hKr d, h1, mul_one,
      ← zpow_natCast (jGeomGen k 1 - algebraMap k (modularFunctionFieldC k 1) d) p, Place.ord_zpow] at h2
    have hpos : 0 < (charLGeomPlaceEquiv k (RationalFunctionField.placeInfty k)).ord
        (jGeomGen k 1 - algebraMap k (modularFunctionFieldC k 1) d) := by
      have he' : (0 : ℤ) < e := by exact_mod_cast he
      rw [← h2] at he'
      exact pos_of_mul_pos_right he' (by exact_mod_cast (Nat.zero_le p))
    apply jGeomGen_notMem_placeInfty k
    have hmem := (charLGeomPlaceEquiv k (RationalFunctionField.placeInfty k)).mem_of_ord_nonneg
      (jGeomGen_sub_algebraMap_ne_zero k 1 d) hpos.le
    have := add_mem hmem ((charLGeomPlaceEquiv k (RationalFunctionField.placeInfty k)).algebraMap_mem' d)
    rwa [sub_add_cancel] at this
  · exact h

end LevelOne

section Transfer

private theorem ord_pos_restrictAlong_iff {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (W : Place K F') (f : F) :
    0 < W.ord (φ f) ↔ 0 < (W.restrictAlong φ hφ).ord f := by
  rw [Place.ord_restrictAlong φ hφ W f]
  have he : 0 < (Place.ramificationIndexAlong φ W : ℤ) := by
    letI := algebraAlong φ
    haveI := isScalarTower_along φ
    haveI := isIntegral_along φ hφ
    have := Place.ramificationIndex_pos (F := F) W
    exact_mod_cast this
  constructor
  · intro h
    exact pos_of_mul_pos_right h he.le
  · intro h
    exact mul_pos he h

variable (p : ℕ) [Fact p.Prime]

private theorem neZero_of_fact_prime' : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩

attribute [local instance] neZero_of_fact_prime'

private abbrev jOne : ↥(modularFunctionFieldBar 1) :=
  ⟨coeffEmb (AlgebraicClosure ℚ) jq,
    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full 1 (jq_mem 1))⟩

private theorem heckeAlphaBar_jOne : heckeAlphaBar (AlgebraicClosure ℚ) 1 p jOne = ProlongationTuple.jFun 1 p :=
  Subtype.ext (by rw [coe_heckeAlphaBar]; rfl)

private theorem heckeBetaBar_jOne : heckeBetaBar (AlgebraicClosure ℚ) 1 p jOne = ProlongationTuple.jQFun 1 p :=
  Subtype.ext (by
    change qExpand (AlgebraicClosure ℚ) p (coeffEmb (AlgebraicClosure ℚ) jq) =
      coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ p jq)
    exact (coeffMap_qExpand (algebraMap ℚ (AlgebraicClosure ℚ)) p jq).symm)

end Transfer

section Dictionary

variable (p : ℕ) [Fact p.Prime]

attribute [local instance] neZero_of_fact_prime'

variable {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type} [Field k] [CharP k p] [PerfectField k] [IsAlgClosed k] {red : A →+* k}
  {data : ModularPolynomialData p} {hKr : KroneckerCongruence p data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 p} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 p}
  (P : PlaceSpecialization A p 1 data hKr k red hα hβ)
  (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)))

private theorem ord_jFun_sub_pos_iff (a : A) :
    0 < V.ord (ProlongationTuple.jFun 1 p -
        algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) (a : AlgebraicClosure ℚ)) ↔
      0 < (V.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) 1 p) hα).ord
        (jOne - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar 1) (a : AlgebraicClosure ℚ)) := by
  rw [← ord_pos_restrictAlong_iff (heckeAlphaBar (AlgebraicClosure ℚ) 1 p) hα V, map_sub,
    heckeAlphaBar_jOne, AlgHom.commutes]

private theorem ord_jQFun_sub_pos_iff (b : A) :
    0 < V.ord (ProlongationTuple.jQFun 1 p -
        algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) (b : AlgebraicClosure ℚ)) ↔
      0 < (V.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) 1 p) hβ).ord
        (jOne - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar 1) (b : AlgebraicClosure ℚ)) := by
  rw [← ord_pos_restrictAlong_iff (heckeBetaBar (AlgebraicClosure ℚ) 1 p) hβ V, map_sub,
    heckeBetaBar_jOne, AlgHom.commutes]

omit [PerfectField k] [IsAlgClosed k] in

private theorem ord_reduceFst_sub_pos (a : A)
    (h : 0 < V.ord (ProlongationTuple.jFun 1 p -
        algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) (a : AlgebraicClosure ℚ))) :
    0 < (P.reduceFst V).ord (jGeomGen k 1 - algebraMap k (modularFunctionFieldC k 1) (red a)) :=
  P.d0_j _ a ((ord_jFun_sub_pos_iff p V a).mp h)

omit [PerfectField k] [IsAlgClosed k] in

private theorem ord_reduceSnd_sub_pos (b : A)
    (h : 0 < V.ord (ProlongationTuple.jQFun 1 p -
        algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) (b : AlgebraicClosure ℚ))) :
    0 < (P.reduceSnd V).ord (jGeomGen k 1 - algebraMap k (modularFunctionFieldC k 1) (red b)) :=
  P.d0_j _ b ((ord_jQFun_sub_pos_iff p V b).mp h)

omit [PerfectField k] in

private theorem reduceFst_eq_placeInfty [DecidableEq (RatFunc k)]
    (hall : ∀ a : A, ¬ 0 < V.ord (ProlongationTuple.jFun 1 p -
        algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) (a : AlgebraicClosure ℚ))) :
    P.reduceFst V = charLGeomPlaceEquiv k (RationalFunctionField.placeInfty k) :=
  eq_placeInfty_of_ord_neg k _ (P.d0_j_pole _ fun a => not_lt.mp fun h => hall a ((ord_jFun_sub_pos_iff p V a).mpr h))

omit [PerfectField k] in

private theorem reduceSnd_eq_placeInfty [DecidableEq (RatFunc k)]
    (hall : ∀ b : A, ¬ 0 < V.ord (ProlongationTuple.jQFun 1 p -
        algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) (b : AlgebraicClosure ℚ))) :
    P.reduceSnd V = charLGeomPlaceEquiv k (RationalFunctionField.placeInfty k) :=
  eq_placeInfty_of_ord_neg k _ (P.d0_j_pole _ fun b => not_lt.mp fun h => hall b ((ord_jQFun_sub_pos_iff p V b).mpr h))

private theorem values_of_isStrictFst (hs : P.IsStrictFst V) : ∃ a b : A,
      0 < V.ord (ProlongationTuple.jFun 1 p -
        algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) (a : AlgebraicClosure ℚ)) ∧
      0 < V.ord (ProlongationTuple.jQFun 1 p -
        algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) (b : AlgebraicClosure ℚ)) ∧
      red b = red a ^ p ∧ red a ^ (p ^ 2) ≠ red a := by
  classical
  obtain ⟨hφ, hne⟩ := hs
  have finf := frob_placeInfty k p data hKr
  have ha : ∃ a : A, 0 < V.ord (ProlongationTuple.jFun 1 p -
      algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) (a : AlgebraicClosure ℚ)) := by
    by_contra hno
    have e1 := reduceFst_eq_placeInfty p P V fun a h => hno ⟨a, h⟩
    exact hne (by rw [e1, finf, finf])
  obtain ⟨a, ha⟩ := ha
  have h1 := ord_reduceFst_sub_pos p P V a ha
  have hb : ∃ b : A, 0 < V.ord (ProlongationTuple.jQFun 1 p -
      algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) (b : AlgebraicClosure ℚ)) := by
    by_contra hno
    have e2 := reduceSnd_eq_placeInfty p P V fun b h => hno ⟨b, h⟩
    have hc := ord_frob_sub_pow_pos k p 1 data hKr (P.reduceFst V) (red a) h1
    rw [hφ, e2] at hc
    exact not_ord_sub_pos_placeInfty k _ hc
  obtain ⟨b, hb⟩ := hb
  have h3 := ord_reduceSnd_sub_pos p P V b hb
  refine ⟨a, b, ha, hb, ?_, ?_⟩
  · have h2 : 0 < (P.reduceSnd V).ord (jGeomGen k 1 - algebraMap k (modularFunctionFieldC k 1) (red a ^ p)) := by
      rw [← hφ]
      exact ord_frob_sub_pow_pos k p 1 data hKr _ _ h1
    exact eq_of_ord_sub_pos k 1 _ _ _ h3 h2
  · intro heq
    apply hne
    have heq' : (red a ^ p) ^ p = red a := by rw [← pow_mul, ← pow_two]; exact heq
    have h2 := ord_frob_sub_pos_of_pow_eq k p 1 data hKr _ (red a ^ p) (red a) heq'
      (ord_frob_sub_pow_pos k p 1 data hKr _ _ h1)
    exact eq_of_ord_sub_pos_levelOne k _ _ (red a) h2 h1

private theorem values_of_isStrictSnd (hs : P.IsStrictSnd V) : ∃ a b : A,
      0 < V.ord (ProlongationTuple.jFun 1 p -
        algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) (a : AlgebraicClosure ℚ)) ∧
      0 < V.ord (ProlongationTuple.jQFun 1 p -
        algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) (b : AlgebraicClosure ℚ)) ∧
      red a = red b ^ p ∧ red b ^ (p ^ 2) ≠ red b := by
  classical
  obtain ⟨hφ, hne⟩ := hs
  have finf := frob_placeInfty k p data hKr
  have hb : ∃ b : A, 0 < V.ord (ProlongationTuple.jQFun 1 p -
      algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) (b : AlgebraicClosure ℚ)) := by
    by_contra hno
    have e2 := reduceSnd_eq_placeInfty p P V fun b h => hno ⟨b, h⟩
    exact hne (by rw [e2, finf, finf])
  obtain ⟨b, hb⟩ := hb
  have h3 := ord_reduceSnd_sub_pos p P V b hb
  have ha : ∃ a : A, 0 < V.ord (ProlongationTuple.jFun 1 p -
      algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) (a : AlgebraicClosure ℚ)) := by
    by_contra hno
    have e1 := reduceFst_eq_placeInfty p P V fun a h => hno ⟨a, h⟩
    have hc := ord_frob_sub_pow_pos k p 1 data hKr (P.reduceSnd V) (red b) h3
    rw [← hφ, e1] at hc
    exact not_ord_sub_pos_placeInfty k _ hc
  obtain ⟨a, ha⟩ := ha
  have h1 := ord_reduceFst_sub_pos p P V a ha
  refine ⟨a, b, ha, hb, ?_, ?_⟩
  · have h2 : 0 < (P.reduceFst V).ord (jGeomGen k 1 - algebraMap k (modularFunctionFieldC k 1) (red b ^ p)) := by
      rw [hφ]
      exact ord_frob_sub_pow_pos k p 1 data hKr _ _ h3
    exact eq_of_ord_sub_pos k 1 _ _ _ h1 h2
  · intro heq
    apply hne
    have heq' : (red b ^ p) ^ p = red b := by rw [← pow_mul, ← pow_two]; exact heq
    have h2 := ord_frob_sub_pos_of_pow_eq k p 1 data hKr _ (red b ^ p) (red b) heq'
      (ord_frob_sub_pow_pos k p 1 data hKr _ _ h3)
    exact eq_of_ord_sub_pos_levelOne k _ _ (red b) h2 h3

private theorem values_of_isStrict :
    (P.IsStrictFst V → ∃ a b : A,
      0 < V.ord (ProlongationTuple.jFun 1 p -
        algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) (a : AlgebraicClosure ℚ)) ∧
      0 < V.ord (ProlongationTuple.jQFun 1 p -
        algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) (b : AlgebraicClosure ℚ)) ∧
      red b = red a ^ p ∧ red a ^ (p ^ 2) ≠ red a) ∧
    (P.IsStrictSnd V → ∃ a b : A,
      0 < V.ord (ProlongationTuple.jFun 1 p -
        algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) (a : AlgebraicClosure ℚ)) ∧
      0 < V.ord (ProlongationTuple.jQFun 1 p -
        algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) (b : AlgebraicClosure ℚ)) ∧
      red a = red b ^ p ∧ red b ^ (p ^ 2) ≠ red b) :=
  ⟨values_of_isStrictFst p P V, values_of_isStrictSnd p P V⟩

end Dictionary

variable (p : ℕ) [Fact p.Prime]

private abbrev Bfin := TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)

private abbrev XO (O : Type) [CommRing O] : Scheme.{0} :=
  pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))

private abbrev finOpen : (DRModel p).Opens :=
  (TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤

private abbrev sec (a : Bfin p) : Γ(DRModel p, finOpen p) :=
  ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).appIso ⊤).inv
    ((Scheme.ΓSpecIso (CommRingCat.of ↥(Bfin p))).inv a)

private def Z (O : Type) [CommRing O] (a : Bfin p) : Set ↥(XO p O) :=
  (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).base ⁻¹'
    (DRModel p).zeroLocus {sec p a}

private def fibre (O : Type) [CommRing O] [IsLocalRing O] : Set ↥(XO p O) :=
  {x | (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).base x =
    IsLocalRing.closedPoint O}

private abbrev aJ : Bfin p := TwoChartIntegralModel.jChartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)

private def jpFull : ↥(modularFunctionFieldFull p) :=
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  ⟨qExpand ℚ p jq, jqd_mem_full p (dvd_refl p)⟩

private theorem jpFull_mem (data : ModularPolynomialData p) : jpFull p ∈ Bfin p := by
  rw [AlgebraicCurve.TwoChartIntegralModel.mem_chartAlg_iff]
  let jS : Algebra.adjoin ℤ ({ModularCurve.IgusaScheme.jFull p} : Set ↥(modularFunctionFieldFull p)) :=
    ⟨ModularCurve.IgusaScheme.jFull p, Algebra.self_mem_adjoin_singleton ℤ _⟩
  let φ : Polynomial ℤ →+* Algebra.adjoin ℤ ({ModularCurve.IgusaScheme.jFull p} : Set ↥(modularFunctionFieldFull p)) :=
    (Polynomial.aeval (R := ℤ) jS).toRingHom
  refine ⟨data.Φ.map φ, data.monic.map φ, ?_⟩
  rw [Polynomial.eval₂_map]
  apply (algebraMap ↥(modularFunctionFieldFull p) (LaurentSeries ℚ)).injective
  rw [map_zero, Polynomial.hom_eval₂]
  have h1 : (algebraMap ↥(modularFunctionFieldFull p) (LaurentSeries ℚ)).comp
      ((algebraMap (Algebra.adjoin ℤ ({ModularCurve.IgusaScheme.jFull p} : Set ↥(modularFunctionFieldFull p)))
        ↥(modularFunctionFieldFull p)).comp φ) = ModularCurve.evalAtJ := by
    apply Polynomial.ringHom_ext
    · intro a
      simp [φ, ModularCurve.evalAtJ]
    · simp [φ, jS, ModularCurve.evalAtJ]
  rw [h1]
  exact data.eval_eq_zero

private def aJp (data : ModularPolynomialData p) : Bfin p := ⟨jpFull p, jpFull_mem p data⟩

private def uu (data : ModularPolynomialData p) : Bfin p := aJp p data - aJ p ^ p

private def vv (data : ModularPolynomialData p) : Bfin p := aJ p - aJp p data ^ p

private theorem Φ_eval_aJ_aJp (data : ModularCurve.ModularPolynomialData p) :
    Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom (Bfin p)) (aJ p)) (aJp p data) data.Φ = 0 := by
  have hinj : Function.Injective ⇑((algebraMap ↥(modularFunctionFieldFull p) (LaurentSeries ℚ)).comp
      (algebraMap (Bfin p) ↥(modularFunctionFieldFull p))) :=
    fun a b h => Subtype.ext ((algebraMap ↥(modularFunctionFieldFull p) (LaurentSeries ℚ)).injective h)
  apply hinj
  rw [map_zero, Polynomial.hom_eval₂]
  have h1 : ((algebraMap ↥(modularFunctionFieldFull p) (LaurentSeries ℚ)).comp
      (algebraMap (Bfin p) ↥(modularFunctionFieldFull p))).comp
        (Polynomial.eval₂RingHom (Int.castRingHom (Bfin p)) (aJ p)) = ModularCurve.evalAtJ := by
    apply Polynomial.ringHom_ext
    · intro a
      simp [ModularCurve.evalAtJ]
    · simp [ModularCurve.evalAtJ]
  rw [h1]
  exact data.eval_eq_zero

private theorem kronecker_mem_or {R : Type} [CommRing R] {data : ModularCurve.ModularPolynomialData p}
    (hKr : ModularCurve.KroneckerCongruence p data) {q : Ideal R} (hq : q.IsPrime) (hpq : ((p : ℕ) : R) ∈ q) {x y : R}
    (hΦ : Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom R) x) y data.Φ = 0) :
    y - x ^ p ∈ q ∨ x - y ^ p ∈ q := by
  haveI := hq
  let π : R →+* R ⧸ q := Ideal.Quotient.mk q
  have hp0 : ((p : ℕ) : R ⧸ q) = 0 := by
    rw [← map_natCast π, Ideal.Quotient.eq_zero_iff_mem]
    exact hpq
  haveI : CharP (R ⧸ q) p := (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr hp0
  let e : Polynomial (Polynomial ℤ) →+* R ⧸ q :=
    Polynomial.eval₂RingHom (Polynomial.eval₂RingHom (Int.castRingHom (R ⧸ q)) (π x)) (π y)
  let e' : Polynomial (Polynomial (ZMod p)) →+* R ⧸ q :=
    Polynomial.eval₂RingHom (Polynomial.eval₂RingHom (ZMod.castHom (dvd_refl p) (R ⧸ q)) (π x)) (π y)
  have hfactor : e'.comp (ModularCurve.reduceModBivar p) = e := by
    apply Polynomial.ringHom_ext
    · intro c
      simp only [ModularCurve.reduceModBivar, RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_C, e, e',
        Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, Polynomial.eval₂_map]
      rw [show (ZMod.castHom (dvd_refl p) (R ⧸ q)).comp (Int.castRingHom (ZMod p)) = Int.castRingHom (R ⧸ q) from
        RingHom.ext_int _ _]
    · simp [ModularCurve.reduceModBivar, e, e']
  have hinner : π.comp (Polynomial.eval₂RingHom (Int.castRingHom R) x) =
      Polynomial.eval₂RingHom (Int.castRingHom (R ⧸ q)) (π x) := by
    apply Polynomial.ringHom_ext
    · intro a
      simp [π]
    · simp [π]
  have h1 : e data.Φ = 0 := by
    have : e data.Φ = π (Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom R) x) y data.Φ) := by
      rw [Polynomial.hom_eval₂, hinner]
      rfl
    rw [this, hΦ, map_zero]
  have h2 : e data.Φ = (π x ^ p - π y) * (π x - π y ^ p) := by
    rw [← hfactor, RingHom.comp_apply, hKr]
    simp [e', Polynomial.eval₂_pow]
  rw [h1] at h2
  rcases mul_eq_zero.mp h2.symm with h | h
  · left
    have h' : π (y - x ^ p) = 0 := by
      rw [map_sub, map_pow]
      rw [sub_eq_zero] at h ⊢
      exact h.symm
    exact Ideal.Quotient.eq_zero_iff_mem.mp h'
  · right
    have h' : π (x - y ^ p) = 0 := by
      rw [map_sub, map_pow]
      exact h
    exact Ideal.Quotient.eq_zero_iff_mem.mp h'

private theorem uu_mem_or_vv_mem {data : ModularCurve.ModularPolynomialData p}
    (hKr : ModularCurve.KroneckerCongruence p data)
    {q : Ideal (Bfin p)} (hq : q.IsPrime) (hpq : ((p : ℕ) : Bfin p) ∈ q) :
    uu p data ∈ q ∨ vv p data ∈ q :=
  kronecker_mem_or p hKr hq hpq (Φ_eval_aJ_aJp p data)

private theorem mem_Z_uu_or_mem_Z_vv {data : ModularPolynomialData p} (hKr : KroneckerCongruence p data)
    (O : Type) [CommRing O] [IsLocalRing O] (hpO : ((p : ℕ) : O) ∈ IsLocalRing.maximalIdeal O) :
    ∀ x ∈ fibre p O, x ∈ Z p O (uu p data) ∨ x ∈ Z p O (vv p data) := by
  intro x hx

  set y : ↥(DRModel p) :=
    (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) x with hy

  have hZ : ∀ a : Bfin p, x ∈ Z p O a ↔ y ∉ (DRModel p).basicOpen (sec p a) := by
    intro a
    show y ∈ (DRModel p).zeroLocus {sec p a} ↔ _
    rw [AlgebraicGeometry.Scheme.mem_zeroLocus_iff]
    simp

  have hB : ∀ a : Bfin p, (DRModel p).basicOpen (sec p a) =
      (TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ
        ((Spec (CommRingCat.of ↥(Bfin p))).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of ↥(Bfin p))).inv a)) := by
    intro a
    exact (AlgebraicGeometry.Scheme.image_basicOpen _ _).symm
  by_cases hchart : ∃ q : ↥(Spec (CommRingCat.of ↥(Bfin p))),
      (TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) q = y
  · obtain ⟨q, hq⟩ := hchart

    have hpq : ((p : ℕ) : Bfin p) ∈ q.asIdeal := by
      have h1 : (DRModel.toBase p) y =
          (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))) (IsLocalRing.closedPoint O) := by
        have hc := congrArg (fun h : XO p O ⟶ Spec (CommRingCat.of ℤ) => h x)
          (pullback.condition (f := DRModel.toBase p) (g := Spec.map (CommRingCat.ofHom (algebraMap ℤ O))))
        simp only [AlgebraicGeometry.Scheme.Hom.comp_apply] at hc
        have hsnd : (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) x =
            IsLocalRing.closedPoint O := hx
        rw [hsnd] at hc
        exact hc
      have h2 : (DRModel.toBase p) y =
          (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥(Bfin p)))) q := by
        rw [← hq, ← AlgebraicGeometry.Scheme.Hom.comp_apply, AlgebraicCurve.TwoChartIntegralModel.ιFin_toBase]
      have h3 : PrimeSpectrum.comap (algebraMap ℤ ↥(Bfin p)) q =
          PrimeSpectrum.comap (algebraMap ℤ O) (IsLocalRing.closedPoint O) := h2.symm.trans h1
      have h4 : ((p : ℕ) : ℤ) ∈ (PrimeSpectrum.comap (algebraMap ℤ ↥(Bfin p)) q).asIdeal := by
        rw [h3, PrimeSpectrum.comap_asIdeal, Ideal.mem_comap]
        simp at hpO ⊢
        exact hpO
      rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap] at h4
      simpa using h4

    have hmem : ∀ a : Bfin p, y ∈ (DRModel p).basicOpen (sec p a) → a ∉ q.asIdeal := by
      intro a ha
      rw [hB] at ha
      obtain ⟨q', hq', hq'q⟩ := ha
      have hinj := (TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p)
        (IgusaScheme.jFull p)).isOpenEmbedding.injective
      have : q' = q := hinj (hq'q.trans hq.symm)
      subst this
      rw [SetLike.mem_coe, AlgebraicGeometry.basicOpen_eq_of_affine] at hq'
      exact (PrimeSpectrum.mem_basicOpen _ _).mp hq'
    rcases uu_mem_or_vv_mem p hKr q.isPrime hpq with h | h
    · left
      exact (hZ _).mpr fun hb => hmem _ hb h
    · right
      exact (hZ _).mpr fun hb => hmem _ hb h
  ·
    left
    refine (hZ _).mpr fun hb => hchart ?_
    rw [hB] at hb
    obtain ⟨q, -, hqy⟩ := hb
    exact ⟨q, hqy⟩

private theorem isClosed_Z (O : Type) [CommRing O] (a : Bfin p) : IsClosed (Z p O a) := by
  unfold Z
  exact ((DRModel p).zeroLocus_isClosed {sec p a}).preimage
    (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).continuous

private theorem range_subset_Z_or {data : ModularPolynomialData p} (hKr : KroneckerCongruence p data)
    (O : Type) [CommRing O] [IsLocalRing O] (hpO : ((p : ℕ) : O) ∈ IsLocalRing.maximalIdeal O)
    {Y : Scheme.{0}} [IrreducibleSpace ↥Y] (f : Y ⟶ XO p O) (hf : Set.range f.base ⊆ fibre p O) :
    Set.range f.base ⊆ Z p O (uu p data) ∨ Set.range f.base ⊆ Z p O (vv p data) := by
  have hcover : (Set.univ : Set ↥Y) ⊆
      f.base ⁻¹' Z p O (uu p data) ∪ f.base ⁻¹' Z p O (vv p data) := fun y _ =>
    (mem_Z_uu_or_mem_Z_vv p hKr O hpO (f.base y) (hf (Set.mem_range_self y))).elim Or.inl Or.inr
  rcases isPreirreducible_iff_isClosed_union_isClosed.mp PreirreducibleSpace.isPreirreducible_univ _ _
      ((isClosed_Z p O (uu p data)).preimage f.continuous)
      ((isClosed_Z p O (vv p data)).preimage f.continuous) hcover with h | h
  · exact Or.inl (Set.range_subset_iff.mpr fun y => h (Set.mem_univ y))
  · exact Or.inr (Set.range_subset_iff.mpr fun y => h (Set.mem_univ y))

private theorem spec_map_apply_eq_closedPoint (O : Type) [CommRing O] [IsLocalRing O] (k : Type) [Field k]
    (toκ : O →+* k) (hker : RingHom.ker toκ = IsLocalRing.maximalIdeal O) (y : ↥(Spec (CommRingCat.of k))) :
    (Spec.map (CommRingCat.ofHom toκ)).base y = IsLocalRing.closedPoint O := by
  have hy : y.asIdeal = ⊥ := (Ideal.eq_bot_or_top y.asIdeal).resolve_right y.isPrime.ne_top
  have h1 : (Spec.map (CommRingCat.ofHom toκ)).base y = PrimeSpectrum.comap toκ y := rfl
  have h2 : (IsLocalRing.closedPoint O).asIdeal = IsLocalRing.maximalIdeal O := rfl
  rw [h1]
  apply PrimeSpectrum.ext
  rw [PrimeSpectrum.comap_asIdeal, hy, ← RingHom.ker_eq_comap_bot, hker, h2]

private theorem mem_range_or (𝔛 : DRModelPackage p) (O : Type) [CommRing O] [IsLocalRing O]
    (k : Type) [Field k] [CharP k p] [IsAlgClosed k] (toκ : O →+* k)
    (hker : RingHom.ker toκ = IsLocalRing.maximalIdeal O) :
    ∀ x ∈ fibre p O,
      x ∈ Set.range ((𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base) ∨
      x ∈ Set.range ((𝔛.compZero k ≫ DRModel.baseChangeMap toκ).base) := by
  intro x hx
  have hx' : x ∈ Set.range (DRModel.baseChangeMap (p := p) toκ) := by
    unfold DRModel.baseChangeMap
    rw [Scheme.Pullback.range_map]
    refine ⟨⟨pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))) x,
      rfl⟩, ⟨IsLocalRing.closedPoint k, ?_⟩⟩
    exact (spec_map_apply_eq_closedPoint O k toκ hker (IsLocalRing.closedPoint k)).trans hx.symm
  obtain ⟨y, hy⟩ := hx'
  rcases 𝔛.comp_jointly_surjective k y with ⟨z, hz⟩ | ⟨z, hz⟩
  · left
    refine ⟨z, ?_⟩
    have hz' : 𝔛.compInf k z = y := hz
    show (𝔛.compInf k ≫ DRModel.baseChangeMap toκ) z = x
    rw [Scheme.Hom.comp_apply, hz', hy]
  · right
    refine ⟨z, ?_⟩
    have hz' : 𝔛.compZero k z = y := hz
    show (𝔛.compZero k ≫ DRModel.baseChangeMap toκ) z = x
    rw [Scheme.Hom.comp_apply, hz', hy]

private theorem range_comp_subset_fibre (𝔛 : DRModelPackage p) (O : Type) [CommRing O] [IsLocalRing O]
    (k : Type) [Field k] [CharP k p] [IsAlgClosed k] (toκ : O →+* k)
    (hker : RingHom.ker toκ = IsLocalRing.maximalIdeal O)
    (C : (𝔛.ratModel k).C ⟶ pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))) :
    Set.range ((C ≫ DRModel.baseChangeMap toκ).base) ⊆ fibre p O := by
  rintro _ ⟨z, rfl⟩
  have h : (C ≫ DRModel.baseChangeMap toκ) ≫
        pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))) =
      (C ≫ pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))) ≫
        Spec.map (CommRingCat.ofHom toκ) := by
    simp only [Category.assoc, DRModel.baseChangeMap, pullback.lift_snd]
  have h' := Scheme.Hom.comp_apply (C ≫ DRModel.baseChangeMap toκ)
    (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) z
  rw [h, Scheme.Hom.comp_apply] at h'
  show (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))))
      ((C ≫ DRModel.baseChangeMap toκ) z) = IsLocalRing.closedPoint O
  rw [← h']
  exact spec_map_apply_eq_closedPoint O k toκ hker _

private def jbar : ↥(modularFunctionFieldBar p) :=
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  ⟨coeffEmb (AlgebraicClosure ℚ) jq,
    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full p (jq_mem p))⟩

private def abar (a : Bfin p) : ↥(modularFunctionFieldBar p) :=
  ⟨coeffEmb (AlgebraicClosure ℚ) ((a : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ),
    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (a : ↥(modularFunctionFieldFull p)).2⟩

private theorem reading (𝔛 : DRModelPackage p)
    [hneη : Nonempty (Scheme.Opens.toScheme
      ((𝔛.eη ≫ pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ))))) ⁻¹ᵁ
        finOpen p))]
    (hMη : ∀ a : ↥(Bfin p),
      ((𝔛.Mη.ffEquiv.symm
          (𝔛.Mη.C.germToFunctionField
            ((𝔛.eη ≫ pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ))))) ⁻¹ᵁ
              finOpen p)
            (((𝔛.eη ≫ pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ))))).app
                (finOpen p)).hom (sec p a)))
          : ↥(modularFunctionFieldBar p)) : LaurentSeries (AlgebraicClosure ℚ)) =
        coeffEmb (AlgebraicClosure ℚ) ((a : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ))
    {A : ValuationSubring (AlgebraicClosure ℚ)}
    (R : Type) [CommRing R] [IsLocalRing R] (ιA : R →+* ↥A) [IsLocalHom ιA]
    (t : Spec (CommRingCat.of R) ⟶ DRModel p)
    (w : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar p))
    (hgen : Spec.map (CommRingCat.ofHom (A.subtype.comp ιA)) ≫ t =
      ((𝔛.Mη.pointEquivPlace).symm w).1 ≫ 𝔛.eη ≫ pullback.fst (DRModel.toBase p) _)
    (hj : ∃ a : ↥A, w.HasValue (jbar p) (a : AlgebraicClosure ℚ)) :
    ∃ ψ : ↥(Bfin p) →+* R,
      Spec.map (CommRingCat.ofHom ψ) ≫ TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) = t ∧
      (∀ a : ↥(Bfin p), w.HasValue (abar p a) ((ιA (ψ a) : ↥A) : AlgebraicClosure ℚ)) ∧
      (∀ (q : ↥(Spec (CommRingCat.of R))) (a : ↥(Bfin p)),
        t.base q ∈ (DRModel p).zeroLocus {sec p a} ↔ ψ a ∈ q.asIdeal) := by
  haveI := 𝔛.isIntegral
  haveI : Fact (IgusaScheme.jFull p ≠ 0) := inferInstance
  set h := 𝔛.eη ≫ pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ))))
    with hh

  have hread : ∀ a : ↥(Bfin p), 𝔛.Mη.ffEquiv.symm (𝔛.Mη.C.germToFunctionField
      (h ⁻¹ᵁ (TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) ''ᵁ ⊤))
      ((h.app (TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) ''ᵁ ⊤)).hom
        (secOf (TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) a))) = abar p a :=
    fun a => Subtype.ext (hMη a)
  have hreadj : 𝔛.Mη.ffEquiv.symm (𝔛.Mη.C.germToFunctionField
      (h ⁻¹ᵁ (TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) ''ᵁ ⊤))
      ((h.app (TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) ''ᵁ ⊤)).hom
        (secOf (TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))
          (TwoChartIntegralModel.jChartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))))) = jbar p :=
    hread (aJ p)

  have hfin : t.base (IsLocalRing.closedPoint R) ∈
      Set.range (TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).base :=
    closedPoint_mem_range_ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) 𝔛.Mη h (jbar p) hreadj
      A.subtype Subtype.val_injective (S := CommRingCat.of R) ιA t w hgen hj

  obtain ⟨ψ, hψ⟩ := exists_ringHom_of_closedPoint_mem
    (TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) t hfin
  refine ⟨ψ.hom, ?_, ?_, ?_⟩
  · rw [CommRingCat.ofHom_hom]; exact hψ
  ·
    intro a
    exact hasValue_of_factor 𝔛.Mη h (TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))
      (fun a => abar p a) hread (CommRingCat.ofHom (A.subtype.comp ιA)) t ψ hψ w hgen a
  ·
    intro q a
    rw [← hψ]
    exact mem_zeroLocus_secOf_iff (TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))
      a ((Spec.map ψ).base q)

private theorem mem_maximalIdeal_iff_inv_notMem {F : Type*} [Field F] (A : ValuationSubring F) {x : F}
    (hx : x ∈ A) (hx0 : x ≠ 0) :
    (⟨x, hx⟩ : A) ∈ IsLocalRing.maximalIdeal A ↔ x⁻¹ ∉ A := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  constructor
  · intro hnu hinv
    apply hnu
    refine ⟨⟨⟨x, hx⟩, ⟨x⁻¹, hinv⟩, ?_, ?_⟩, rfl⟩
    · exact Subtype.ext (mul_inv_cancel₀ hx0)
    · exact Subtype.ext (inv_mul_cancel₀ hx0)
  · intro hinv hu
    apply hinv
    obtain ⟨u, hu⟩ := hu
    have h2 : x * (((u⁻¹ : Aˣ) : A) : F) = 1 := by
      have := congrArg (fun a : A => (a : F)) u.mul_inv
      simpa [hu] using this
    have h3 : x⁻¹ = (((u⁻¹ : Aˣ) : A) : F) := (eq_inv_of_mul_eq_one_right h2).symm
    rw [h3]
    exact ((u⁻¹ : Aˣ) : A).2

private theorem hasValue_of_sub_mem_maximalIdeal {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
    {g : F} {c : K} (hg : g ∈ v.toValuationSubring) (hgc : g - algebraMap K F c ∈ v.toValuationSubring)
    (hm : (⟨g - algebraMap K F c, hgc⟩ : v.toValuationSubring) ∈ IsLocalRing.maximalIdeal v.toValuationSubring) :
    v.HasValue g c := by
  refine ⟨hg, ?_⟩
  have hsplit : (⟨g, hg⟩ : v.toValuationSubring) =
      ⟨g - algebraMap K F c, hgc⟩ + ⟨algebraMap K F c, v.algebraMap_mem' c⟩ := Subtype.ext (by simp)
  rw [hsplit, map_add, (IsLocalRing.residue_eq_zero_iff _).mpr hm, zero_add]
  exact v.residue_algebraMap c

private theorem sub_mem_maximalIdeal_of_hasValue {K F : Type*} [Field K] [Field F] [Algebra K F] {v : Place K F}
    {g : F} {c : K} (h : v.HasValue g c) :
    (⟨g - algebraMap K F c, sub_mem h.mem (v.algebraMap_mem' c)⟩ : v.toValuationSubring) ∈
      IsLocalRing.maximalIdeal v.toValuationSubring := by
  rw [← IsLocalRing.residue_eq_zero_iff]
  have hsplit : (⟨g - algebraMap K F c, sub_mem h.mem (v.algebraMap_mem' c)⟩ : v.toValuationSubring) =
      ⟨g, h.mem⟩ - ⟨algebraMap K F c, v.algebraMap_mem' c⟩ := Subtype.ext (by simp)
  rw [hsplit, map_sub, h.residue_eq, sub_eq_zero]
  exact (v.residue_algebraMap c).symm

private theorem hasValue_of_ord_pos {K F : Type*} [Field K] [Field F] [Algebra K F] (w : Place K F) (g : F) (c : K)
    (h : 0 < w.ord (g - algebraMap K F c)) (hne : g - algebraMap K F c ≠ 0) : w.HasValue g c := by
  have hgc : g - algebraMap K F c ∈ w.toValuationSubring := AlgebraicCurve.Place.mem_of_ord_nonneg (v := w) hne h.le
  have hg : g ∈ w.toValuationSubring := by
    have := add_mem hgc (w.algebraMap_mem' c)
    simpa using this
  refine hasValue_of_sub_mem_maximalIdeal w hg hgc ?_
  rw [mem_maximalIdeal_iff_inv_notMem _ hgc hne]
  intro hinv
  have h1 := AlgebraicCurve.Place.ord_nonneg_of_mem (v := w) hinv
  rw [AlgebraicCurve.Place.ord_inv] at h1
  omega

omit [Fact p.Prime] in

private theorem hasValue_ePl
    (ePl : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) ≃ Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar p))
    (hePl_fun : ∀ (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)))
      (f : ↥(modularFunctionFieldBar (1 * p))) (f' : ↥(modularFunctionFieldBar p)),
      ((f : LaurentSeries (AlgebraicClosure ℚ)) = (f' : LaurentSeries (AlgebraicClosure ℚ))) →
        ((f ∈ V.toValuationSubring ↔ f' ∈ (ePl V).toValuationSubring) ∧ V.evalAt f = (ePl V).evalAt f'))
    (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)))
    (f : ↥(modularFunctionFieldBar (1 * p))) (f' : ↥(modularFunctionFieldBar p))
    (hff : (f : LaurentSeries (AlgebraicClosure ℚ)) = (f' : LaurentSeries (AlgebraicClosure ℚ))) (c : AlgebraicClosure ℚ)
    (h : V.HasValue f c) : (ePl V).HasValue f' c := by
  have hmem' : f' ∈ (ePl V).toValuationSubring := (hePl_fun V f f' hff).1.mp h.mem
  by_cases hfc : f = algebraMap (AlgebraicClosure ℚ) _ c
  · have hf'c : f' = algebraMap (AlgebraicClosure ℚ) _ c := by
      apply Subtype.ext
      have h1 : (f' : LaurentSeries (AlgebraicClosure ℚ)) = (f : LaurentSeries (AlgebraicClosure ℚ)) := hff.symm
      rw [h1, hfc]
      simp
    rw [hf'c]
    exact (ePl V).hasValue_algebraMap c
  · have hne : f - algebraMap (AlgebraicClosure ℚ) _ c ≠ 0 := sub_ne_zero.mpr hfc
    have hne' : f' - algebraMap (AlgebraicClosure ℚ) _ c ≠ 0 := by
      intro h0
      apply hfc
      apply Subtype.ext
      have h0' := congrArg (fun x : ↥(modularFunctionFieldBar p) => (x : LaurentSeries (AlgebraicClosure ℚ)))
        (sub_eq_zero.mp h0)
      rw [hff, h0']
      simp
    have hV := sub_mem_maximalIdeal_of_hasValue h
    rw [mem_maximalIdeal_iff_inv_notMem _ _ hne] at hV
    have hgc' : f' - algebraMap (AlgebraicClosure ℚ) _ c ∈ (ePl V).toValuationSubring :=
      sub_mem hmem' ((ePl V).algebraMap_mem' c)
    refine hasValue_of_sub_mem_maximalIdeal (ePl V) hmem' hgc' ?_
    rw [mem_maximalIdeal_iff_inv_notMem _ hgc' hne']
    intro hinv'
    apply hV
    have hseries : (((f - algebraMap (AlgebraicClosure ℚ) _ c)⁻¹ : ↥(modularFunctionFieldBar (1 * p))) :
          LaurentSeries (AlgebraicClosure ℚ)) =
        (((f' - algebraMap (AlgebraicClosure ℚ) _ c)⁻¹ : ↥(modularFunctionFieldBar p)) :
          LaurentSeries (AlgebraicClosure ℚ)) := by
      simp [hff]
    exact (hePl_fun V _ _ hseries).1.mpr hinv'

private theorem exists_extend (𝔛 : DRModelPackage p) (A : ValuationSubring (AlgebraicClosure ℚ))
    (x : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ DRModel p) :
    ∃ t : Spec (CommRingCat.of ↥A) ⟶ DRModel p, Spec.map (CommRingCat.ofHom A.subtype) ≫ t = x := by
  haveI := 𝔛.isProper
  have hex : ValuativeCriterion.Existence (DRModel.toBase p) :=
    (IsProper.eq_valuativeCriterion ▸ (inferInstance : IsProper (DRModel.toBase p))).1.1.1.existence
  have hsq : CommSq x (Spec.map (CommRingCat.ofHom (algebraMap ↥A (AlgebraicClosure ℚ)))) (DRModel.toBase p)
      (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥A))) :=
    ⟨specZIsTerminal.hom_ext _ _⟩
  let S : ValuativeCommSq (DRModel.toBase p) :=
    { R := ↥A, K := AlgebraicClosure ℚ, i₁ := x,
      i₂ := Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥A)), commSq := hsq }
  haveI : S.commSq.HasLift := hex S
  have e : A.subtype = algebraMap ↥A (AlgebraicClosure ℚ) := RingHom.ext fun _ => rfl
  refine ⟨S.commSq.lift, ?_⟩
  rw [e]
  exact S.commSq.fac_left

private theorem exists_swap_of_cover {X : Type*} {F RI RZ Zu Zv : Set X}
    (hcov : ∀ x ∈ F, x ∈ RI ∨ x ∈ RZ)
    (hI : RI ⊆ Zu ∨ RI ⊆ Zv) (hZ : RZ ⊆ Zu ∨ RZ ⊆ Zv)
    (hwv : ∃ x ∈ F, x ∉ Zv) (hwu : ∃ x ∈ F, x ∉ Zu) :
    ∃ swap : Bool, ∀ x ∈ F,
      (x ∉ Zv → x ∈ (if swap then RZ else RI) ∧ x ∉ (if swap then RI else RZ)) ∧
      (x ∉ Zu → x ∈ (if swap then RI else RZ) ∧ x ∉ (if swap then RZ else RI)) := by
  rcases hI with hIu | hIv <;> rcases hZ with hZu | hZv
  · obtain ⟨x, hxF, hxu⟩ := hwu
    exact (hxu ((hcov x hxF).elim (fun h => hIu h) (fun h => hZu h))).elim
  · refine ⟨false, fun x hxF => ?_⟩
    simp only [Bool.false_eq_true, if_false]
    exact ⟨fun hxv => ⟨(hcov x hxF).resolve_right (fun h => hxv (hZv h)), fun h => hxv (hZv h)⟩,
      fun hxu => ⟨(hcov x hxF).resolve_left (fun h => hxu (hIu h)), fun h => hxu (hIu h)⟩⟩
  · refine ⟨true, fun x hxF => ?_⟩
    simp only [if_true]
    exact ⟨fun hxv => ⟨(hcov x hxF).resolve_left (fun h => hxv (hIv h)), fun h => hxv (hIv h)⟩,
      fun hxu => ⟨(hcov x hxF).resolve_right (fun h => hxu (hZu h)), fun h => hxu (hZu h)⟩⟩
  · obtain ⟨x, hxF, hxv⟩ := hwv
    exact (hxv ((hcov x hxF).elim (fun h => hIv h) (fun h => hZv h))).elim

private theorem coe_jFun_eq_coe_jbar :
    ((ModularCurve.PlaceSpecialization.ProlongationTuple.jFun 1 p :
        ↥(modularFunctionFieldBar (1 * p))) : LaurentSeries (AlgebraicClosure ℚ)) =
      ((jbar p : ↥(modularFunctionFieldBar p)) : LaurentSeries (AlgebraicClosure ℚ)) :=
  rfl

private theorem abar_aJ_eq_jbar : abar p (aJ p) = jbar p :=
  rfl

private theorem coe_jQFun_eq_coe_abar_aJp (data : ModularCurve.ModularPolynomialData p) :
    ((ModularCurve.PlaceSpecialization.ProlongationTuple.jQFun 1 p :
        ↥(modularFunctionFieldBar (1 * p))) : LaurentSeries (AlgebraicClosure ℚ)) =
      ((abar p (aJp p data) : ↥(modularFunctionFieldBar p)) : LaurentSeries (AlgebraicClosure ℚ)) :=
  rfl

omit [Fact p.Prime] in
private theorem ker_toκ_eq (O : Type) [CommRing O] [IsLocalRing O] (k : Type) [Field k] [CharP k p]
    (hϖO : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)}) (toκ : O →+* k) :
    RingHom.ker toκ = IsLocalRing.maximalIdeal O := by
  apply le_antisymm (IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top toκ))
  rw [hϖO, Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker, map_natCast toκ,
    CharP.cast_eq_zero]

omit [Fact p.Prime] in
private theorem natCast_mem_maximalIdeal (O : Type) [CommRing O] [IsLocalRing O]
    (hϖO : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)}) :
    ((p : ℕ) : O) ∈ IsLocalRing.maximalIdeal O := by
  rw [hϖO]
  exact Ideal.subset_span (Set.mem_singleton _)

private abbrev Kf (A : ValuationSubring (AlgebraicClosure ℚ)) : Type :=
  ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ))

private def iotaA {A : ValuationSubring (AlgebraicClosure ℚ)} {O : Type} [CommRing O]
    (eO : O ≃+* ↥(A.comap (algebraMap (Kf A) (AlgebraicClosure ℚ)))) : O →+* ↥A :=
  RingHom.codRestrict
    ((algebraMap (Kf A) (AlgebraicClosure ℚ)).comp ((A.comap (algebraMap (Kf A) (AlgebraicClosure ℚ))).subtype.comp eO.toRingHom))
    A (fun o => (eO o).2)

private theorem subtype_comp_iotaA {A : ValuationSubring (AlgebraicClosure ℚ)} {O : Type} [CommRing O]
    (eO : O ≃+* ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))) :
    A.subtype.comp (iotaA eO) =
      (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)).comp
        ((A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))).subtype.comp
          eO.toRingHom) :=
  RingHom.ext fun _ => rfl

private theorem toκ_eq_red_comp_iotaA {A : ValuationSubring (AlgebraicClosure ℚ)} {O : Type} [CommRing O]
    {k : Type} [Field k] {red : ↥A →+* k}
    (eO : O ≃+* ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))))
    (toκ : O →+* k)
    (htoκ : ∀ o : O, toκ o = red ⟨algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)
      ((eO o : ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))) :
        ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ))), (eO o).2⟩) :
    ∀ o : O, toκ o = red (iotaA eO o) :=
  fun o => htoκ o

omit [Fact p.Prime] in

private theorem isLocalHom_iotaA {A : ValuationSubring (AlgebraicClosure ℚ)} {O : Type} [CommRing O] [IsLocalRing O]
    {k : Type} [Field k] [CharP k p] (red : ↥A →+* k)
    (eO : O ≃+* ↥(A.comap (algebraMap (Kf A) (AlgebraicClosure ℚ))))
    (hϖO : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)}) : IsLocalHom (iotaA eO) := by
  refine ⟨fun o ho => ?_⟩
  by_contra hno
  have hmem : o ∈ IsLocalRing.maximalIdeal O := (IsLocalRing.mem_maximalIdeal o).mpr (mem_nonunits_iff.mpr hno)
  rw [hϖO, Ideal.mem_span_singleton] at hmem
  obtain ⟨c, rfl⟩ := hmem
  have h0 : red (iotaA eO (((p : ℕ) : O) * c)) = 0 := by
    rw [map_mul (iotaA eO), map_natCast (iotaA eO), map_mul red, map_natCast red, CharP.cast_eq_zero, zero_mul]
  exact (ho.map red).ne_zero h0

private theorem red_iotaA_ψ_vv_ne_zero {A : ValuationSubring (AlgebraicClosure ℚ)} {k : Type} [Field k]
    {red : ↥A →+* k} (data : ModularPolynomialData p)
    {R : Type} [CommRing R] (ιA : R →+* ↥A) (ψ : ↥(Bfin p) →+* R)
    (w : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar p))
    (hv : ∀ a : ↥(Bfin p), w.HasValue (abar p a) ((ιA (ψ a) : ↥A) : AlgebraicClosure ℚ))
    (a b : ↥A) (ha : w.HasValue (abar p (aJ p)) (a : AlgebraicClosure ℚ))
    (hb : w.HasValue (abar p (aJp p data)) (b : AlgebraicClosure ℚ))
    (hab : red b = red a ^ p) (hne : red a ^ (p ^ 2) ≠ red a) :
    red (ιA (ψ (vv p data))) ≠ 0 := by
  have h1 : ιA (ψ (aJ p)) = a := Subtype.ext ((hv (aJ p)).unique ha)
  have h2 : ιA (ψ (aJp p data)) = b := Subtype.ext ((hv (aJp p data)).unique hb)
  have h3 : red (ιA (ψ (vv p data))) = red a - red a ^ (p ^ 2) := by
    rw [vv, ψ.map_sub, ιA.map_sub, red.map_sub, ψ.map_pow, ιA.map_pow, red.map_pow, h1, h2, hab, ← pow_mul, ← sq]
  intro h0
  rw [h3, sub_eq_zero] at h0
  exact hne h0.symm

private theorem red_iotaA_ψ_uu_ne_zero {A : ValuationSubring (AlgebraicClosure ℚ)} {k : Type} [Field k]
    {red : ↥A →+* k} (data : ModularPolynomialData p)
    {R : Type} [CommRing R] (ιA : R →+* ↥A) (ψ : ↥(Bfin p) →+* R)
    (w : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar p))
    (hv : ∀ a : ↥(Bfin p), w.HasValue (abar p a) ((ιA (ψ a) : ↥A) : AlgebraicClosure ℚ))
    (a b : ↥A) (ha : w.HasValue (abar p (aJ p)) (a : AlgebraicClosure ℚ))
    (hb : w.HasValue (abar p (aJp p data)) (b : AlgebraicClosure ℚ))
    (hab : red a = red b ^ p) (hne : red b ^ (p ^ 2) ≠ red b) :
    red (ιA (ψ (uu p data))) ≠ 0 := by
  have h1 : ιA (ψ (aJ p)) = a := Subtype.ext ((hv (aJ p)).unique ha)
  have h2 : ιA (ψ (aJp p data)) = b := Subtype.ext ((hv (aJp p data)).unique hb)
  have h3 : red (ιA (ψ (uu p data))) = red b - red b ^ (p ^ 2) := by
    rw [uu, ψ.map_sub, ιA.map_sub, red.map_sub, ψ.map_pow, ιA.map_pow, red.map_pow, h1, h2, hab, ← pow_mul, ← sq]
  intro h0
  rw [h3, sub_eq_zero] at h0
  exact hne h0.symm

private theorem not_mem_Z_of_section (O : Type) [CommRing O] [IsLocalRing O] (k : Type) [Field k] (toκ : O →+* k)
    (hker : RingHom.ker toκ = IsLocalRing.maximalIdeal O)
    (s : Spec (CommRingCat.of O) ⟶ XO p O) (ψ : ↥(Bfin p) →+* O)
    (hψ : ∀ (q : ↥(Spec (CommRingCat.of O))) (a' : ↥(Bfin p)),
      (s ≫ pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).base q ∈
          (DRModel p).zeroLocus {sec p a'} ↔ ψ a' ∈ q.asIdeal)
    (a : ↥(Bfin p)) (hne : toκ (ψ a) ≠ 0) :
    s.base (IsLocalRing.closedPoint O) ∉ Z p O a := by
  intro hmem
  apply hne
  have h0 := Scheme.Hom.comp_apply s
    (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) (IsLocalRing.closedPoint O)
  have h1 : (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))))
      (s (IsLocalRing.closedPoint O)) ∈ (DRModel p).zeroLocus {sec p a} := hmem
  rw [← h0] at h1
  have h2 : ψ a ∈ (IsLocalRing.closedPoint O).asIdeal := (hψ (IsLocalRing.closedPoint O) a).mp h1
  have h3 : ψ a ∈ RingHom.ker toκ := by
    rw [hker]
    exact h2
  exact (RingHom.mem_ker).mp h3

private theorem exists_mem_fibre_notMem_Z {A : ValuationSubring (AlgebraicClosure ℚ)}
    (O : Type) [CommRing O] [IsLocalRing O] (k : Type) [Field k] (toκ : O →+* k)
    (hker : RingHom.ker toκ = IsLocalRing.maximalIdeal O) (red : ↥A →+* k)
    (t : Spec (CommRingCat.of ↥A) ⟶ DRModel p) (ψ : ↥(Bfin p) →+* ↥A)
    (hψ : ∀ (q : ↥(Spec (CommRingCat.of ↥A))) (a' : ↥(Bfin p)),
      t.base q ∈ (DRModel p).zeroLocus {sec p a'} ↔ ψ a' ∈ q.asIdeal)
    (a : ↥(Bfin p)) (hne : red (ψ a) ≠ 0) :
    ∃ x ∈ fibre p O, x ∉ Z p O a := by
  let ℓ : Spec (CommRingCat.of k) ⟶ XO p O :=
    pullback.lift (Spec.map (CommRingCat.ofHom red) ≫ t) (Spec.map (CommRingCat.ofHom toκ))
      (specZIsTerminal.hom_ext _ _)
  have hℓ₁ : ℓ ≫ pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))) =
      Spec.map (CommRingCat.ofHom red) ≫ t := pullback.lift_fst _ _ _
  have hℓ₂ : ℓ ≫ pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))) =
      Spec.map (CommRingCat.ofHom toκ) := pullback.lift_snd _ _ _
  refine ⟨ℓ.base (IsLocalRing.closedPoint k), ?_, ?_⟩
  · have h0 := Scheme.Hom.comp_apply ℓ
      (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) (IsLocalRing.closedPoint k)
    rw [hℓ₂] at h0
    show (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) (ℓ (IsLocalRing.closedPoint k)) =
      IsLocalRing.closedPoint O
    rw [← h0]
    exact spec_map_apply_eq_closedPoint O k toκ hker _
  · intro hmem
    apply hne
    have h0 := Scheme.Hom.comp_apply ℓ
      (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) (IsLocalRing.closedPoint k)
    rw [hℓ₁, Scheme.Hom.comp_apply] at h0
    have h1 : (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))))
        (ℓ (IsLocalRing.closedPoint k)) ∈ (DRModel p).zeroLocus {sec p a} := hmem
    rw [← h0] at h1
    have h2 : ψ a ∈ ((Spec.map (CommRingCat.ofHom red)).base (IsLocalRing.closedPoint k)).asIdeal :=
      (hψ ((Spec.map (CommRingCat.ofHom red)).base (IsLocalRing.closedPoint k)) a).mp h1
    have h4 : ((Spec.map (CommRingCat.ofHom red)).base (IsLocalRing.closedPoint k)).asIdeal = RingHom.ker red := by
      have e : (Spec.map (CommRingCat.ofHom red)).base (IsLocalRing.closedPoint k) =
          PrimeSpectrum.comap red (IsLocalRing.closedPoint k) := rfl
      have hbot : (IsLocalRing.closedPoint k).asIdeal = ⊥ :=
        (Ideal.eq_bot_or_top _).resolve_right (IsLocalRing.closedPoint k).isPrime.ne_top
      rw [e, PrimeSpectrum.comap_asIdeal, hbot, RingHom.ker_eq_comap_bot]
    rw [h4] at h2
    exact (RingHom.mem_ker).mp h2

private theorem ne_zero_of_ord_pos {K F : Type*} [Field K] [Field F] [Algebra K F] {w : Place K F} {x : F}
    (h : 0 < w.ord x) : x ≠ 0 := fun h0 => by
  rw [h0, Place.ord_zero] at h
  exact lt_irrefl _ h

end ModularCurve.StrictOrientation

open ModularCurve.StrictOrientation in
set_option maxHeartbeats 1600000 in

theorem solution
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    {A : ValuationSubring (AlgebraicClosure ℚ)} (hA : A.LiesOverPrime p)
    (𝔛 : DRModelPackage p)
    [hneη : Nonempty (Scheme.Opens.toScheme
      ((𝔛.eη ≫ pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ))))) ⁻¹ᵁ
        ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)))]
    (hMη : ∀ a : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)),
      ((𝔛.Mη.ffEquiv.symm
          (𝔛.Mη.C.germToFunctionField
            ((𝔛.eη ≫ pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ))))) ⁻¹ᵁ
              ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤))
            (((𝔛.eη ≫ pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ))))).app
                ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)).hom
              (((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).appIso ⊤).inv
                ((Scheme.ΓSpecIso (CommRingCat.of
                  ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))).inv a))))
          : ↥(modularFunctionFieldBar p)) : LaurentSeries (AlgebraicClosure ℚ)) =
        coeffEmb (AlgebraicClosure ℚ) ((a : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ))
    (ePl : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) ≃ Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar p))
    (hePl_fun : ∀ (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)))
        (f : ↥(modularFunctionFieldBar (1 * p))) (f' : ↥(modularFunctionFieldBar p)),
      (f : LaurentSeries (AlgebraicClosure ℚ)) = (f' : LaurentSeries (AlgebraicClosure ℚ)) →
        (f ∈ V.toValuationSubring ↔ f' ∈ (ePl V).toValuationSubring) ∧ V.evalAt f = (ePl V).evalAt f')
    {k : Type} [Field k] [CharP k p] [PerfectField k] [IsAlgClosed k] {red : A →+* k}
    {data : ModularPolynomialData p} {hKr : KroneckerCongruence p data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 p} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 p}
    (P : PlaceSpecialization A p 1 data hKr k red hα hβ)
    (R : ProlongationTuple P)
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (eO : O ≃+* ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))))
    (hϖO : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})
    (K : Type) [Field K] [Algebra O K] [IsFractionRing O K]
    (ιK : K →+* AlgebraicClosure ℚ)
    (hιK : ∀ o : O, ιK (algebraMap O K o) =
      algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)
        ((eO o : ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))) :
          ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ))))
    (hιA : ∀ a : O, ιK (algebraMap O K a) ∈ A)
    (toκ : O →+* k)
    (htoκ : ∀ o : O, toκ o = red ⟨algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)
      ((eO o : ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))) :
        ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ))), (eO o).2⟩)
    [hint : IsIntegral (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))))]
    (φ : ↥((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField) →+*
      ↥(modularFunctionFieldBar (1 * p)))
    (hφO : ∀ a : O,
      φ (algebraMap ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk (genericPoint ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))))) _
        (((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.germ ⊤ (genericPoint ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))))) trivial).hom
          (((pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).appTop).hom
            ((Scheme.ΓSpecIso (CommRingCat.of O)).inv a)))) =
        algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) (ιK (algebraMap O K a)))
    [hne : Nonempty (Scheme.Opens.toScheme ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ
      ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)))]
    (hφj : ∀ a : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)),
      ((φ ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).germToFunctionField
          ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ
            ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤))
          (((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).app
              ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)).hom
            (((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).appIso ⊤).inv
              ((Scheme.ΓSpecIso (CommRingCat.of
                ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))).inv a)))) :
            ↥(modularFunctionFieldBar (1 * p))) : LaurentSeries (AlgebraicClosure ℚ)) =
        coeffEmb (AlgebraicClosure ℚ) ((a : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ)) :
    ∃ swap : Bool, ∀ (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))),
      (∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (1 * p)) σ • V = V) →
      ∀ s : Spec (CommRingCat.of O) ⟶ pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))),
        s ≫ pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))) = 𝟙 _ →
        Spec.map (CommRingCat.ofHom ((algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)).comp
            (((A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))).subtype.comp eO.toRingHom)))) ≫ s ≫ pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))) =
          ((𝔛.Mη.pointEquivPlace).symm (ePl V)).1 ≫ 𝔛.eη ≫ pullback.fst (DRModel.toBase p) _ →
        (P.IsStrictFst V →
          s.base (IsLocalRing.closedPoint O) ∈ Set.range ((if swap then 𝔛.compZero k else 𝔛.compInf k) ≫ DRModel.baseChangeMap toκ).base ∧
          s.base (IsLocalRing.closedPoint O) ∉ Set.range ((if swap then 𝔛.compInf k else 𝔛.compZero k) ≫ DRModel.baseChangeMap toκ).base) ∧
        (P.IsStrictSnd V →
          s.base (IsLocalRing.closedPoint O) ∈ Set.range ((if swap then 𝔛.compInf k else 𝔛.compZero k) ≫ DRModel.baseChangeMap toκ).base ∧
          s.base (IsLocalRing.closedPoint O) ∉ Set.range ((if swap then 𝔛.compZero k else 𝔛.compInf k) ≫ DRModel.baseChangeMap toκ).base) := by
  classical
  have _ := hp; have _ := hA; have _ := R; have _ := hιK; have _ := hιA; have _ := hint; have _ := hφO
  have _ := hne; have _ := hφj

  have hker : RingHom.ker toκ = IsLocalRing.maximalIdeal O := ker_toκ_eq p O k hϖO toκ
  have hpO : ((p : ℕ) : O) ∈ IsLocalRing.maximalIdeal O := natCast_mem_maximalIdeal p O hϖO
  haveI hloc : IsLocalHom (iotaA eO) := isLocalHom_iotaA p red eO hϖO
  have hιred : ∀ o : O, toκ o = red (iotaA eO o) := toκ_eq_red_comp_iotaA eO toκ htoκ
  haveI := (𝔛.ratModel k).isIntegral

  have key : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)),
      (P.IsStrictFst W → ∃ a b : A, (ePl W).HasValue (jbar p) (a : AlgebraicClosure ℚ) ∧
        (ePl W).HasValue (abar p (aJp p data)) (b : AlgebraicClosure ℚ) ∧ red b = red a ^ p ∧ red a ^ (p ^ 2) ≠ red a) ∧
      (P.IsStrictSnd W → ∃ a b : A, (ePl W).HasValue (jbar p) (a : AlgebraicClosure ℚ) ∧
        (ePl W).HasValue (abar p (aJp p data)) (b : AlgebraicClosure ℚ) ∧ red a = red b ^ p ∧ red b ^ (p ^ 2) ≠ red b) := by
    intro W
    have hv := values_of_isStrict p P W
    have tr : ∀ a : A, 0 < W.ord (ProlongationTuple.jFun 1 p -
        algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) (a : AlgebraicClosure ℚ)) →
        (ePl W).HasValue (jbar p) (a : AlgebraicClosure ℚ) := fun a h =>
      hasValue_ePl p ePl hePl_fun W (ProlongationTuple.jFun 1 p) (jbar p) (coe_jFun_eq_coe_jbar p) (a : AlgebraicClosure ℚ)
        (hasValue_of_ord_pos W _ _ h (ne_zero_of_ord_pos h))
    have tr' : ∀ b : A, 0 < W.ord (ProlongationTuple.jQFun 1 p -
        algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) (b : AlgebraicClosure ℚ)) →
        (ePl W).HasValue (abar p (aJp p data)) (b : AlgebraicClosure ℚ) := fun b h =>
      hasValue_ePl p ePl hePl_fun W (ProlongationTuple.jQFun 1 p) (abar p (aJp p data)) (coe_jQFun_eq_coe_abar_aJp p data)
        (b : AlgebraicClosure ℚ) (hasValue_of_ord_pos W _ _ h (ne_zero_of_ord_pos h))
    refine ⟨fun hs => ?_, fun hs => ?_⟩
    · obtain ⟨a, b, ha, hb, h1, h2⟩ := hv.1 hs
      exact ⟨a, b, tr a ha, tr' b hb, h1, h2⟩
    · obtain ⟨a, b, ha, hb, h1, h2⟩ := hv.2 hs
      exact ⟨a, b, tr a ha, tr' b hb, h1, h2⟩

  haveI : IsLocalHom (RingHom.id ↥A) := isLocalHom_id ↥A
  have witness : ∀ (W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))) (a : A),
      (ePl W).HasValue (jbar p) (a : AlgebraicClosure ℚ) →
      ∃ ψ : ↥(Bfin p) →+* ↥A, (∀ c : ↥(Bfin p), (ePl W).HasValue (abar p c) ((ψ c : ↥A) : AlgebraicClosure ℚ)) ∧
        ∃ t : Spec (CommRingCat.of ↥A) ⟶ DRModel p,
          ∀ (q : ↥(Spec (CommRingCat.of ↥A))) (c : ↥(Bfin p)),
            t.base q ∈ (DRModel p).zeroLocus {sec p c} ↔ ψ c ∈ q.asIdeal := by
    intro W a ha
    obtain ⟨t, ht⟩ := exists_extend p 𝔛 A
      (((𝔛.Mη.pointEquivPlace).symm (ePl W)).1 ≫ 𝔛.eη ≫ pullback.fst (DRModel.toBase p) _)
    obtain ⟨ψ, -, hval, hzero⟩ := reading p 𝔛 hMη (R := ↥A) (RingHom.id ↥A) t (ePl W)
      (by rw [RingHom.comp_id]; exact ht) ⟨a, ha⟩
    exact ⟨ψ, hval, t, hzero⟩

  have hp1 : ¬ p ∣ 1 := fun h => (Fact.out : p.Prime).ne_one (Nat.dvd_one.mp h)
  obtain ⟨Q₁, Q₂, hQ₁, hQ₂, -, -, -, -, -, -⟩ :=
    P.exists_families_isStrictFst_isStrictSnd_notMem_forall_inertia_smul_eq hp1 ∅ 1 1
  have hwv : ∃ x ∈ fibre p O, x ∉ Z p O (vv p data) := by
    obtain ⟨a, b, ha, hb, hab, hne⟩ := (key (Q₁ 0)).1 (hQ₁ 0)
    obtain ⟨ψ, hval, t, hzero⟩ := witness (Q₁ 0) a ha
    have ha' : (ePl (Q₁ 0)).HasValue (abar p (aJ p)) (a : AlgebraicClosure ℚ) := by rw [abar_aJ_eq_jbar]; exact ha
    have hred : red ((RingHom.id ↥A) (ψ (vv p data))) ≠ 0 :=
      red_iotaA_ψ_vv_ne_zero p data (RingHom.id ↥A) ψ (ePl (Q₁ 0)) hval a b ha' hb hab hne
    exact exists_mem_fibre_notMem_Z p O k toκ hker red t ψ hzero (vv p data) hred
  have hwu : ∃ x ∈ fibre p O, x ∉ Z p O (uu p data) := by
    obtain ⟨a, b, ha, hb, hab, hne⟩ := (key (Q₂ 0)).2 (hQ₂ 0)
    obtain ⟨ψ, hval, t, hzero⟩ := witness (Q₂ 0) a ha
    have ha' : (ePl (Q₂ 0)).HasValue (abar p (aJ p)) (a : AlgebraicClosure ℚ) := by rw [abar_aJ_eq_jbar]; exact ha
    have hred : red ((RingHom.id ↥A) (ψ (uu p data))) ≠ 0 :=
      red_iotaA_ψ_uu_ne_zero p data (RingHom.id ↥A) ψ (ePl (Q₂ 0)) hval a b ha' hb hab hne
    exact exists_mem_fibre_notMem_Z p O k toκ hker red t ψ hzero (uu p data) hred

  have hcov := mem_range_or p 𝔛 O k toκ hker
  have hI := range_subset_Z_or p hKr O hpO (𝔛.compInf k ≫ DRModel.baseChangeMap toκ)
    (range_comp_subset_fibre p 𝔛 O k toκ hker (𝔛.compInf k))
  have hZ := range_subset_Z_or p hKr O hpO (𝔛.compZero k ≫ DRModel.baseChangeMap toκ)
    (range_comp_subset_fibre p 𝔛 O k toκ hker (𝔛.compZero k))
  obtain ⟨swap, hswap⟩ := exists_swap_of_cover hcov hI hZ hwv hwu
  refine ⟨swap, fun V _ s hs hgen => ?_⟩

  have hxF : s.base (IsLocalRing.closedPoint O) ∈ fibre p O := by
    change (s ≫ pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).base
      (IsLocalRing.closedPoint O) = IsLocalRing.closedPoint O
    rw [hs]
    rfl

  have sect : ∀ a : A, (ePl V).HasValue (jbar p) (a : AlgebraicClosure ℚ) →
      ∃ ψ : ↥(Bfin p) →+* O, (∀ c : ↥(Bfin p), (ePl V).HasValue (abar p c) ((iotaA eO (ψ c) : ↥A) : AlgebraicClosure ℚ)) ∧
        ∀ (q : ↥(Spec (CommRingCat.of O))) (c : ↥(Bfin p)),
          (s ≫ pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).base q ∈
              (DRModel p).zeroLocus {sec p c} ↔ ψ c ∈ q.asIdeal := by
    intro a ha
    obtain ⟨ψ, -, hval, hzero⟩ := reading p 𝔛 hMη (R := O) (iotaA eO)
      (s ≫ pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) (ePl V)
      (by rw [subtype_comp_iotaA]; exact hgen) ⟨a, ha⟩
    exact ⟨ψ, hval, hzero⟩
  have glueV := hswap _ hxF
  refine ⟨fun hst => ?_, fun hst => ?_⟩
  · obtain ⟨a, b, ha, hb, hab, hne⟩ := (key V).1 hst
    obtain ⟨ψ, hval, hzero⟩ := sect a ha
    have ha' : (ePl V).HasValue (abar p (aJ p)) (a : AlgebraicClosure ℚ) := by rw [abar_aJ_eq_jbar]; exact ha
    have hred := red_iotaA_ψ_vv_ne_zero p data (iotaA eO) ψ (ePl V) hval a b ha' hb hab hne
    have hne' : toκ (ψ (vv p data)) ≠ 0 := by rw [hιred]; exact hred
    have hnot := not_mem_Z_of_section p O k toκ hker s ψ hzero (vv p data) hne'
    have hV := glueV.1 hnot
    cases swap
    · simp only [Bool.false_eq_true, if_false] at hV ⊢
      exact hV
    · simp only [if_true] at hV ⊢
      exact hV
  · obtain ⟨a, b, ha, hb, hab, hne⟩ := (key V).2 hst
    obtain ⟨ψ, hval, hzero⟩ := sect a ha
    have ha' : (ePl V).HasValue (abar p (aJ p)) (a : AlgebraicClosure ℚ) := by rw [abar_aJ_eq_jbar]; exact ha
    have hred := red_iotaA_ψ_uu_ne_zero p data (iotaA eO) ψ (ePl V) hval a b ha' hb hab hne
    have hne' : toκ (ψ (uu p data)) ≠ 0 := by rw [hιred]; exact hred
    have hnot := not_mem_Z_of_section p O k toκ hker s ψ hzero (uu p data) hne'
    have hV := glueV.2 hnot
    cases swap
    · simp only [Bool.false_eq_true, if_false] at hV ⊢
      exact hV
    · simp only [if_true] at hV ⊢
      exact hV

end

end S_ModularCurve_DRModelPackage_exists_swap_forall_isStrict_section_mem_range_comp_of_reading
end P2MW
export P2MW.S_ModularCurve_DRModelPackage_exists_swap_forall_isStrict_section_mem_range_comp_of_reading (solution)
