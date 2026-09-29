-- Prove2me | solution 1 for ModularCurve.DRModelPackage.nodeResidue_eq_zero_iff_and_ord_eq_of_specializes_of_mem_maximalIdeal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/2825a964-e3ff-5564-8ee6-488aa4cda3a2

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackage
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_NodeLocalizedPlaces
import Definitions.Def_ModularCurve_DRResolvedModelPackageV4
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.Def_AlgebraicCurve_PlacesOverDVR
import Definitions.Def_ModularCurve_SpecializeModuli
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Theorems.Thm_ModularCurve_eq_charLGeomPlaceOfPoint_of_ord_pos
import Theorems.Thm_ModularCurve_arithFrobC_smul_charLGeomPlaceOfPoint
import Theorems.Thm_ModularCurve_arithFrobC_smul_arithFrobC_smul_of_mem_ssPlaces
import Theorems.Thm_ModularCurve_ord_charLGeomPlaceOfPoint_jqModC_sub_algebraMap
import Theorems.Thm_ModularCurve_mem_ssPlaces_one_iff_exists_charLGeomPlaceOfPoint_eq
import Theorems.Thm_ModularCurve_DRModelPackage_phi_algebraMap_stalk_mem_integers_and_exists_eq_jFun_of_specializes_of_mem_maximalIdeal
import Theorems.Thm_ModularCurve_DRModelPackage_exists_ringEquiv_ratFunc_forall_stalkMap_genericPoint_eq_residueFst
import Theorems.Thm_ModularCurve_DRModelPackage_exists_ringEquiv_ratFunc_forall_stalkMap_genericPoint_eq_residueSnd
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_residue_jFun_sub_jQFun_sub
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModelPackage_nodeResidue_eq_zero_iff_and_ord_eq_of_specializes_of_mem_maximalIdeal
p2m_attr_erase "instance" "AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.PhiGen.instNeZeroPhiGenCosetA WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.Gamma0Pair.map_toCurve WeierstrassCurve.mapPoint_eq_ratPointMap ModularCurve.Gamma0Pair.map_gen ModularCurve.Gamma0Pair.map_eq_gamma0PairMap ModularCurve.ModuliPoint.map_eq_moduliPointMapRingHom ModularCurve.ModuliPoint.map_mk WeierstrassCurve.mapPointHom_apply WeierstrassCurve.mapPoint_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero"
p2m_attr_erase "simp" "compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁"
p2m_attr_erase "simp" "WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluX_empty WeierstrassCurve.vcInvEmbedding_apply ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂"
p2m_attr_erase "simp" "TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero ModularCurve.cuspCount_one WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero HahnSeries.ramScale_apply GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe"
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord RegularLocalRingQuotientAscent.dualNumberFst_apply"
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
p2m_open "AlgebraicCurve IsLocalRing ModularCurve P2MW.S_ModularCurve_DRModelPackage_nodeResidue_eq_zero_iff_and_ord_eq_of_specializes_of_mem_maximalIdeal.ModularCurve ModularCurve.PlaceSpecialization"

noncomputable section

namespace ResMatchOrdCore

universe u

variable {K : Type u} [Field K] {L : Type} [Field L] [Algebra K L]

def read (M : CurveModel K L) {X : Scheme.{u}} (f : M.C ⟶ X) (y : M.C) (x : X) (hx : x = f.base y) :
    X.presheaf.stalk x →+* L :=
  (M.ffEquiv.symm : M.C.functionField ≃+* L).toRingHom.comp
    ((algebraMap (M.C.presheaf.stalk y) M.C.functionField).comp
      ((f.stalkMap y).hom.comp (X.presheaf.stalkCongr (.of_eq hx)).hom.hom))

theorem read_apply (M : CurveModel K L) {X : Scheme.{u}} (f : M.C ⟶ X) (y : M.C) (x : X) (hx : x = f.base y)
    (s : X.presheaf.stalk x) :
    read M f y x hx s = M.ffEquiv.symm (algebraMap (M.C.presheaf.stalk y) M.C.functionField
      ((f.stalkMap y).hom ((X.presheaf.stalkCongr (.of_eq hx)).hom.hom s))) := rfl

theorem algebraMap_stalkMap_stalkCongr {C X : Scheme.{u}} [IsIntegral C] (f : C ⟶ X) (y : C) (x : X) (hx : x = f.base y)
    (s : X.presheaf.stalk x) :
    algebraMap (C.presheaf.stalk y) C.functionField ((f.stalkMap y).hom ((X.presheaf.stalkCongr (.of_eq hx)).hom.hom s)) =
      (f.stalkMap (genericPoint C)).hom
        ((X.presheaf.stalkSpecializes (hx ▸ f.base.hom.map_specializes (genericPoint_specializes y))).hom s) := by
  subst hx

  change (C.presheaf.stalkSpecializes (genericPoint_specializes y)).hom ((f.stalkMap y).hom
    ((X.presheaf.stalkSpecializes (specializes_refl (f.base y))).hom s)) = _
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← Scheme.Hom.stalkSpecializes_stalkMap f _ _ (genericPoint_specializes y),
    ← Category.assoc, TopCat.Presheaf.stalkSpecializes_comp]
  rfl

theorem read_eq_stalkMap_genericPoint (M : CurveModel K L) {X : Scheme.{u}} (f : M.C ⟶ X) (y : M.C) (x : X)
    (hx : x = f.base y) (s : X.presheaf.stalk x) :
    read M f y x hx s = M.ffEquiv.symm ((f.stalkMap (genericPoint M.C)).hom
      ((X.presheaf.stalkSpecializes (hx ▸ f.base.hom.map_specializes (genericPoint_specializes y))).hom s)) := by
  rw [read_apply, algebraMap_stalkMap_stalkCongr f y x hx s]

section Branch

variable {C X : Scheme.{u}} [IsIntegral C] (f : C ⟶ X)

def branchEmb : IsLocalRing.ResidueField (X.presheaf.stalk (f.base (genericPoint C))) →+* C.functionField :=
  IsLocalRing.ResidueField.lift (f.stalkMap (genericPoint C)).hom

theorem branchEmb_residue (u : X.presheaf.stalk (f.base (genericPoint C))) :
    branchEmb f (IsLocalRing.residue _ u) = (f.stalkMap (genericPoint C)).hom u :=
  IsLocalRing.ResidueField.lift_residue_apply _ _

theorem branchEmb_injective : Function.Injective (branchEmb f) := (branchEmb f).injective

def toBranchResidue (x : X) (h : f.base (genericPoint C) ⤳ x) :
    X.presheaf.stalk x →+* IsLocalRing.ResidueField (X.presheaf.stalk (f.base (genericPoint C))) :=
  (IsLocalRing.residue _).comp (X.presheaf.stalkSpecializes h).hom

theorem toBranchResidue_apply (x : X) (h : f.base (genericPoint C) ⤳ x) (s : X.presheaf.stalk x) :
    toBranchResidue f x h s = IsLocalRing.residue _ ((X.presheaf.stalkSpecializes h).hom s) := rfl

end Branch

theorem read_eq_branchEmb (M : CurveModel K L) {X : Scheme.{u}} (f : M.C ⟶ X) (y : M.C) (x : X) (hx : x = f.base y)
    (s : X.presheaf.stalk x) :
    read M f y x hx s = M.ffEquiv.symm (branchEmb f
      (toBranchResidue f x (hx ▸ f.base.hom.map_specializes (genericPoint_specializes y)) s)) := by
  rw [read_eq_stalkMap_genericPoint, toBranchResidue_apply, branchEmb_residue]

omit [Algebra K L] in
theorem stalkCongr_of_eq_rfl_apply {X : Scheme.{u}} (x : X) (t : X.presheaf.stalk x) :
    (X.presheaf.stalkCongr (.of_eq (rfl : x = x))).hom.hom t = t := by
  show (X.presheaf.stalkSpecializes (specializes_refl x)).hom t = t
  rw [TopCat.Presheaf.stalkSpecializes_refl]
  rfl

theorem ord_read_pos (M : CurveModel K L) {X : Scheme.{u}} (f : M.C ⟶ X) (y : M.C) (hy : IsClosed ({y} : Set M.C)) (x : X)
    (hx : x = f.base y) (t : X.presheaf.stalk x) (ht : t ∈ IsLocalRing.maximalIdeal _) (h0 : read M f y x hx t ≠ 0) :
    0 < (M.placeOfPoint ⟨y, hy⟩).ord (read M f y x hx t) := by
  subst hx

  set u : M.C.presheaf.stalk y := (f.stalkMap y).hom ((X.presheaf.stalkCongr (.of_eq rfl)).hom.hom t) with hu_def
  have hu : u ∈ IsLocalRing.maximalIdeal (M.C.presheaf.stalk y) := by
    rw [hu_def, stalkCongr_of_eq_rfl_apply]
    exact map_nonunit (f.stalkMap y).hom t ht

  let a : M.C.presheaf.stalk y →+* L :=
    (M.ffEquiv.symm : M.C.functionField ≃+* L).toRingHom.comp (algebraMap (M.C.presheaf.stalk y) M.C.functionField)
  have ha : ∀ z, a z = M.ffEquiv.symm (algebraMap (M.C.presheaf.stalk y) M.C.functionField z) := fun z => rfl
  have hinj : Function.Injective a :=
    M.ffEquiv.symm.injective.comp (IsFractionRing.injective (M.C.presheaf.stalk y) M.C.functionField)
  have hrange : a.range = (M.placeOfPoint ⟨y, hy⟩).toValuationSubring.toSubring := M.range_stalk_eq ⟨y, hy⟩
  have hmem : ∀ z, a z ∈ (M.placeOfPoint ⟨y, hy⟩).toValuationSubring := fun z => by
    have h : a z ∈ a.range := ⟨z, rfl⟩
    rw [hrange] at h
    exact h
  have hread : read M f y (f.base y) rfl t = a u := rfl
  rw [hread] at h0 ⊢
  refine ((M.placeOfPoint ⟨y, hy⟩).mem_maximalIdeal_iff_ord_pos h0 (hmem u)).mp ?_

  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hunit
  obtain ⟨w', hw'⟩ := hunit.exists_right_inv
  obtain ⟨z, hz⟩ : ((w' : (M.placeOfPoint ⟨y, hy⟩).toValuationSubring) : L) ∈ a.range := by
    rw [hrange]; exact w'.2
  have h1 : a (u * z) = a 1 := by
    rw [map_mul, map_one, hz]
    exact congrArg Subtype.val hw'
  have h2 : u * z = 1 := hinj h1
  exact (IsLocalRing.mem_maximalIdeal _ |>.mp hu) (IsUnit.of_mul_eq_one z h2)

variable {L' : Type} [Field L'] [Algebra K L']

theorem ord_res_eq_ord_read {S : Type*} [CommRing S] (res : S →+* L') (read : S →+* L) (θ : L ≃+* L')
    (hθ : ∀ s, res s = θ (read s)) (w : Place K L') (P : Place K L) (hpin : ∀ g : L, w.ord (θ g) = P.ord g) (s : S) :
    w.ord (res s) = P.ord (read s) := by
  rw [hθ, hpin]

theorem ord_eq_of_restrict_eq {F S : Type*} [Field F] [CommRing S] (π : S →+* F) (e : F →+* L) (ψ : F →+* L')
    (res : S →+* L') (read : S →+* L) (hres : ∀ s, res s = ψ (π s)) (hread : ∀ s, read s = e (π s))
    (w : Place K L') (P : Place K L) (hpin : ∀ u : F, w.ord (ψ u) = P.ord (e u)) (s : S) :
    w.ord (res s) = P.ord (read s) := by
  rw [hres, hread, hpin]

end ResMatchOrdCore

namespace ModularCurve
p2m_export "ModularCurve" "DRModelPackage.neZero_of_fact_prime DRModel DRModel.toBase DRModelPackage ModularPolynomialData modularFunctionFieldFull IgusaScheme.jFull IgusaScheme coeffEmb modularFunctionFieldBar PlaceSpecialization.ProlongationTuple.jFun PlaceSpecialization.ProlongationTuple.jQFun PlaceSpecialization.ProlongationTuple jqModC modularFunctionFieldC jqModC_mem PlaceSpecialization HeckeAlphaBarIntegral HeckeBetaBarIntegral KroneckerCongruence ssPlaces jGeomGen jGeomGen_sub_algebraMap_ne_zero charLGeomPlaceOfPoint arithFrobC DRModel.baseChangeMap eq_charLGeomPlaceOfPoint_of_ord_pos arithFrobC_smul_charLGeomPlaceOfPoint arithFrobC_smul_arithFrobC_smul_of_mem_ssPlaces ord_charLGeomPlaceOfPoint_jqModC_sub_algebraMap mem_ssPlaces_one_iff_exists_charLGeomPlaceOfPoint_eq DRModelPackage.phi_algebraMap_stalk_mem_integers_and_exists_eq_jFun_of_specializes_of_mem_maximalIdeal DRModelPackage.exists_ringEquiv_ratFunc_forall_stalkMap_genericPoint_eq_residueFst DRModelPackage.exists_ringEquiv_ratFunc_forall_stalkMap_genericPoint_eq_residueSnd"
namespace DRModelPackage
p2m_export "ModularCurve.DRModelPackage" "neZero_of_fact_prime compZero ratModel compInf w phi_algebraMap_stalk_mem_integers_and_exists_eq_jFun_of_specializes_of_mem_maximalIdeal exists_ringEquiv_ratFunc_forall_stalkMap_genericPoint_eq_residueFst exists_ringEquiv_ratFunc_forall_stalkMap_genericPoint_eq_residueSnd"
namespace ResMatchOrd
p2m_open "ModularCurve.DRModelPackage ModularCurve"

universe u

section Concrete

variable (p : ℕ) [Fact p.Prime]

attribute [local instance] DRModelPackage.neZero_of_fact_prime

def res₁ (O : Type) [CommRing O]
    [IsIntegral (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))))]
    (x : ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))))
    (φ : ↥((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField) →+*
      ↥(modularFunctionFieldBar (1 * p)))
    {A : ValuationSubring (AlgebraicClosure ℚ)} {k : Type} [Field k] [CharP k p] {red : A →+* k}
    {data : ModularPolynomialData p} {hKr : KroneckerCongruence p data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 p} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 p}
    {P : PlaceSpecialization A p 1 data hKr k red hα hβ} (R : ProlongationTuple P)
    (w : Place k (modularFunctionFieldC k 1))
    (hconv : ∀ s : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x,
      φ (algebraMap _ (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField s) ∈ R.nodeIntegers w) :
    (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x →+* ↥(modularFunctionFieldC k 1) :=
  (R.nodeResidue₁ w).comp
    ((φ.comp (algebraMap _ (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField)).codRestrict
      (R.nodeIntegers w) hconv)

theorem res₁_apply (O : Type) [CommRing O]
    [IsIntegral (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))))]
    (x : ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))))
    (φ : ↥((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField) →+*
      ↥(modularFunctionFieldBar (1 * p)))
    {A : ValuationSubring (AlgebraicClosure ℚ)} {k : Type} [Field k] [CharP k p] {red : A →+* k}
    {data : ModularPolynomialData p} {hKr : KroneckerCongruence p data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 p} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 p}
    {P : PlaceSpecialization A p 1 data hKr k red hα hβ} (R : ProlongationTuple P)
    (w : Place k (modularFunctionFieldC k 1))
    (hconv : ∀ s : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x,
      φ (algebraMap _ (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField s) ∈ R.nodeIntegers w)
    (s : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x) :
    res₁ p O x φ R w hconv s = R.nodeResidue₁ w ⟨_, hconv s⟩ := rfl

def res₂ (O : Type) [CommRing O]
    [IsIntegral (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))))]
    (x : ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))))
    (φ : ↥((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField) →+*
      ↥(modularFunctionFieldBar (1 * p)))
    {A : ValuationSubring (AlgebraicClosure ℚ)} {k : Type} [Field k] [CharP k p] {red : A →+* k}
    {data : ModularPolynomialData p} {hKr : KroneckerCongruence p data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 p} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 p}
    {P : PlaceSpecialization A p 1 data hKr k red hα hβ} (R : ProlongationTuple P)
    (w : Place k (modularFunctionFieldC k 1))
    (hconv : ∀ s : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x,
      φ (algebraMap _ (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField s) ∈ R.nodeIntegers w) :
    (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x →+* ↥(modularFunctionFieldC k 1) :=
  (R.nodeResidue₂ w).comp
    ((φ.comp (algebraMap _ (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField)).codRestrict
      (R.nodeIntegers w) hconv)

omit [Fact p.Prime] in

theorem algebraMap_functionField_stalkSpecializes {X : Scheme.{0}} [IsIntegral X] {ξ x : X} (h : ξ ⤳ x)
    (s : X.presheaf.stalk x) :
    algebraMap (X.presheaf.stalk ξ) X.functionField ((X.presheaf.stalkSpecializes h).hom s) =
      algebraMap (X.presheaf.stalk x) X.functionField s := by
  change (X.presheaf.stalkSpecializes _).hom ((X.presheaf.stalkSpecializes h).hom s) = (X.presheaf.stalkSpecializes _).hom s
  rw [← CommRingCat.comp_apply, TopCat.Presheaf.stalkSpecializes_comp]

theorem res₁_eq_theta_read (𝔛 : DRModelPackage p)
    (O : Type) [CommRing O]
    [IsIntegral (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))))]
    (x : ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))))
    (φ : ↥((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField) →+*
      ↥(modularFunctionFieldBar (1 * p)))
    {A : ValuationSubring (AlgebraicClosure ℚ)} {k : Type} [Field k] [CharP k p] [IsAlgClosed k] {red : A →+* k}
    {data : ModularPolynomialData p} {hKr : KroneckerCongruence p data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 p} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 p}
    {P : PlaceSpecialization A p 1 data hKr k red hα hβ} (R : ProlongationTuple P)
    (toκ : O →+* k)
    (w : Place k (modularFunctionFieldC k 1))
    (n : ↥(pullback (𝔛.compInf k) (𝔛.compZero k)))
    (hx₁ : x = (𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base ((pullback.fst (𝔛.compInf k) (𝔛.compZero k)).base n))
    (hsp₁ : (𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel k).C) ⤳ x)
    (hconv : ∀ s : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x,
      φ (algebraMap _ (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField s) ∈ R.nodeIntegers w)
    (hval : ∀ u : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk
        ((𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel k).C)),
      φ (algebraMap _ (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField u) ∈ R.R₁.integers)
    (θ : RatFunc k ≃+* ↥(modularFunctionFieldC k 1))
    (hθξ : ∀ u : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk
          ((𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel k).C)),
        θ ((𝔛.ratModel k).ffEquiv.symm
            (((𝔛.compInf k ≫ DRModel.baseChangeMap toκ).stalkMap (genericPoint ↥(𝔛.ratModel k).C)).hom u)) =
          (R.residue₁ ⟨φ (algebraMap _ (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField u),
            hval u⟩ : ↥(modularFunctionFieldC k 1)))
    (s : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x) :
    res₁ p O x φ R w hconv s =
      θ (ResMatchOrdCore.read (𝔛.ratModel k) (𝔛.compInf k ≫ DRModel.baseChangeMap toκ)
        ((pullback.fst (𝔛.compInf k) (𝔛.compZero k)).base n) x hx₁ s) := by
  rw [ResMatchOrdCore.read_eq_stalkMap_genericPoint, hθξ, res₁_apply, ProlongationTuple.nodeResidue₁_apply]
  congr 1
  apply Subtype.ext
  show φ _ = φ _
  rw [algebraMap_functionField_stalkSpecializes]

theorem res₂_eq_theta_read (𝔛 : DRModelPackage p)
    (O : Type) [CommRing O]
    [IsIntegral (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))))]
    (x : ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))))
    (φ : ↥((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField) →+*
      ↥(modularFunctionFieldBar (1 * p)))
    {A : ValuationSubring (AlgebraicClosure ℚ)} {k : Type} [Field k] [CharP k p] [IsAlgClosed k] {red : A →+* k}
    {data : ModularPolynomialData p} {hKr : KroneckerCongruence p data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 p} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 p}
    {P : PlaceSpecialization A p 1 data hKr k red hα hβ} (R : ProlongationTuple P)
    (toκ : O →+* k)
    (w : Place k (modularFunctionFieldC k 1))
    (n : ↥(pullback (𝔛.compInf k) (𝔛.compZero k)))
    (hx₂ : x = (𝔛.compZero k ≫ DRModel.baseChangeMap toκ).base ((pullback.snd (𝔛.compInf k) (𝔛.compZero k)).base n))
        (hconv : ∀ s : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x,
      φ (algebraMap _ (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField s) ∈ R.nodeIntegers w)
    (hval : ∀ u : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk
        ((𝔛.compZero k ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel k).C)),
      φ (algebraMap _ (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField u) ∈ R.R₂.integers)
    (θ : RatFunc k ≃+* ↥(modularFunctionFieldC k 1))
    (hθξ : ∀ u : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk
          ((𝔛.compZero k ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel k).C)),
        θ ((𝔛.ratModel k).ffEquiv.symm
            (((𝔛.compZero k ≫ DRModel.baseChangeMap toκ).stalkMap (genericPoint ↥(𝔛.ratModel k).C)).hom u)) =
          (R.residue₂ ⟨φ (algebraMap _ (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField u),
            hval u⟩ : ↥(modularFunctionFieldC k 1)))
    (s : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x) :
    res₂ p O x φ R w hconv s =
      θ (ResMatchOrdCore.read (𝔛.ratModel k) (𝔛.compZero k ≫ DRModel.baseChangeMap toκ)
        ((pullback.snd (𝔛.compInf k) (𝔛.compZero k)).base n) x hx₂ s) := by
  rw [ResMatchOrdCore.read_eq_stalkMap_genericPoint, hθξ, show res₂ p O x φ R w hconv s = R.nodeResidue₂ w ⟨_, hconv s⟩ from rfl,
    ProlongationTuple.nodeResidue₂_apply]
  congr 1
  apply Subtype.ext
  show φ _ = φ _
  rw [algebraMap_functionField_stalkSpecializes]

omit [Fact p.Prime] in
private theorem _root_.AlgebraicCurve.Place.mem_of_ord_nonneg' {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
    {f : F} (hf : f ≠ 0) (h : 0 ≤ v.ord f) : f ∈ v.toValuationSubring := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  rw [hu]
  lift v.ord f to ℕ using h with n hn
  rw [zpow_natCast]
  exact mul_mem (u : v.toValuationSubring).2 (pow_mem π.2 n)

p2m_alias "P2MW.S_ModularCurve_DRModelPackage_nodeResidue_eq_zero_iff_and_ord_eq_of_specializes_of_mem_maximalIdeal.AlgebraicCurve.Place.mem_of_ord_nonneg'" "AlgebraicCurve.Place.mem_of_ord_nonneg'"
omit [Fact p.Prime] in

theorem evalAt_jGeomGen_charLGeomPlaceOfPoint (k : Type) [Field k] [DecidableEq k] (a : k) :
    (charLGeomPlaceOfPoint k a).evalAt (jGeomGen k 1) = a := by
  set v := charLGeomPlaceOfPoint k a with hv
  set g : ↥(modularFunctionFieldC k 1) := jGeomGen k 1 - algebraMap k ↥(modularFunctionFieldC k 1) a with hg
  have hord : v.ord g = 1 := by
    rw [hg, show (jGeomGen k 1 : ↥(modularFunctionFieldC k 1)) = ⟨jqModC k, jqModC_mem k 1⟩ from rfl,
      ModularCurve.ord_charLGeomPlaceOfPoint_jqModC_sub_algebraMap k a a, if_pos rfl]
  have hg0 : g ≠ 0 := fun h => by rw [h, Place.ord_zero] at hord; exact zero_ne_one hord
  have hgmem : g ∈ v.toValuationSubring := v.mem_of_ord_nonneg' hg0 (by rw [hord]; exact zero_le_one)
  have hcmem : algebraMap k ↥(modularFunctionFieldC k 1) a ∈ v.toValuationSubring := v.algebraMap_mem' a
  have hjmem : (jGeomGen k 1 : ↥(modularFunctionFieldC k 1)) ∈ v.toValuationSubring := by
    have : (jGeomGen k 1 : ↥(modularFunctionFieldC k 1)) = g + algebraMap k ↥(modularFunctionFieldC k 1) a := by rw [hg, sub_add_cancel]
    rw [this]; exact add_mem hgmem hcmem
  have hgmax : (⟨g, hgmem⟩ : v.toValuationSubring) ∈ IsLocalRing.maximalIdeal _ :=
    (v.mem_maximalIdeal_iff_ord_pos hg0 hgmem).mpr (by rw [hord]; exact zero_lt_one)

  have hres : IsLocalRing.residue v.toValuationSubring ⟨_, hjmem⟩ = algebraMap k v.ResidueField a := by
    have e : (⟨_, hjmem⟩ : v.toValuationSubring) = ⟨g, hgmem⟩ + ⟨_, hcmem⟩ := by
      apply Subtype.ext
      show (jGeomGen k 1 : ↥(modularFunctionFieldC k 1)) = g + algebraMap k ↥(modularFunctionFieldC k 1) a
      rw [hg, sub_add_cancel]
    rw [e, map_add, (IsLocalRing.residue_eq_zero_iff _).mpr hgmax, zero_add]
    rfl
  rw [v.evalAt_of_mem hjmem, hres, Place.residueInv_algebraMap]

omit [Fact p.Prime] in

theorem eq_charLGeomPlaceOfPoint_evalAt_of_mem_ssPlaces {k : Type} [Field k] [DecidableEq k]
    {w : Place k (modularFunctionFieldC k 1)} (hw : w ∈ ssPlaces p 1 k) :
    w = charLGeomPlaceOfPoint k (w.evalAt (jGeomGen k 1)) := by
  obtain ⟨a, -, rfl⟩ := (ModularCurve.mem_ssPlaces_one_iff_exists_charLGeomPlaceOfPoint_eq p k _).mp hw
  rw [evalAt_jGeomGen_charLGeomPlaceOfPoint]

section Ord

variable (𝔛 : DRModelPackage p)
    (O : Type) [CommRing O]
    [IsIntegral (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))))]
    (x : ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))))
    (φ : ↥((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField) →+*
      ↥(modularFunctionFieldBar (1 * p)))
    {A : ValuationSubring (AlgebraicClosure ℚ)} {k : Type} [Field k] [CharP k p] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData p} {hKr : KroneckerCongruence p data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 p} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 p}
    {P : PlaceSpecialization A p 1 data hKr k red hα hβ} (R : ProlongationTuple P)
    (toκ : O →+* k)
    (w : Place k (modularFunctionFieldC k 1))
    (n : ↥(pullback (𝔛.compInf k) (𝔛.compZero k)))
    (hconv : ∀ s : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x,
      φ (algebraMap _ (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField s) ∈ R.nodeIntegers w)

    (c : k) (hwc : w = charLGeomPlaceOfPoint k c)
    (t : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x)
    (ht : t ∈ IsLocalRing.maximalIdeal _)

omit [Fact p.Prime] [CommRing O] [IsIntegral (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))))]
  [CharP k p] [IsAlgClosed k] in

theorem jGeomGen_sub_algebraMap_ne_zero (a : k) : jGeomGen k 1 - algebraMap k ↥(modularFunctionFieldC k 1) a ≠ 0 := by
  intro h
  have h1 := ModularCurve.ord_charLGeomPlaceOfPoint_jqModC_sub_algebraMap k a a
  rw [if_pos rfl, show ((⟨jqModC k, jqModC_mem k 1⟩ : ↥(modularFunctionFieldC k 1))) = jGeomGen k 1 from rfl, h,
    Place.ord_zero] at h1
  exact zero_ne_one h1

include hwc ht

theorem ord₁
    (hy₁ : IsClosed ({(pullback.fst (𝔛.compInf k) (𝔛.compZero k)).base n} : Set ↥(𝔛.ratModel k).C))
    (hx₁ : x = (𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base ((pullback.fst (𝔛.compInf k) (𝔛.compZero k)).base n))

    (hT1 : res₁ p O x φ R w hconv t = jGeomGen k 1 - algebraMap k ↥(modularFunctionFieldC k 1) c)

    (θ₁ : RatFunc k ≃+* ↥(modularFunctionFieldC k 1))
    (hθ₁k : ∀ a : k, θ₁ (algebraMap k (RatFunc k) a) = algebraMap k ↥(modularFunctionFieldC k 1) a)
    (hθ₁ : ∀ s, res₁ p O x φ R w hconv s =
      θ₁ (ResMatchOrdCore.read (𝔛.ratModel k) (𝔛.compInf k ≫ DRModel.baseChangeMap toκ)
        ((pullback.fst (𝔛.compInf k) (𝔛.compZero k)).base n) x hx₁ s))
    (s : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x) :
    w.ord (R.nodeResidue₁ w ⟨_, hconv s⟩ : ↥(modularFunctionFieldC k 1)) =
      ((𝔛.ratModel k).placeOfPoint ⟨((pullback.fst (𝔛.compInf k) (𝔛.compZero k)).base n), hy₁⟩).ord
        ((𝔛.ratModel k).ffEquiv.symm (algebraMap _ (𝔛.ratModel k).C.functionField
          (((𝔛.compInf k ≫ DRModel.baseChangeMap toκ).stalkMap ((pullback.fst (𝔛.compInf k) (𝔛.compZero k)).base n)).hom
            (((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalkCongr (.of_eq hx₁)).hom.hom s)))) := by
  set P₁ := (𝔛.ratModel k).placeOfPoint ⟨((pullback.fst (𝔛.compInf k) (𝔛.compZero k)).base n), hy₁⟩ with hP₁
  set rd := ResMatchOrdCore.read (𝔛.ratModel k) (𝔛.compInf k ≫ DRModel.baseChangeMap toκ)
        ((pullback.fst (𝔛.compInf k) (𝔛.compZero k)).base n) x hx₁ with hrd

  have h0 : rd t ≠ 0 := fun h => by
    have := hθ₁ t
    rw [hT1, h, map_zero] at this
    exact jGeomGen_sub_algebraMap_ne_zero (k := k) c this
  have hpos : 0 < P₁.ord (rd t) :=
    ResMatchOrdCore.ord_read_pos (𝔛.ratModel k) _ _ hy₁ x hx₁ t ht h0

  have hP₁' : Place.congrRingEquiv θ₁ hθ₁k P₁ = w := by
    rw [hwc]
    refine ModularCurve.eq_charLGeomPlaceOfPoint_of_ord_pos ?_
    rw [show ((⟨jqModC k, jqModC_mem k 1⟩ : ↥(modularFunctionFieldC k 1))) = jGeomGen k 1 from rfl, ← hT1, hθ₁ t,
      Place.ord_congrRingEquiv]
    exact hpos
  have key : w.ord (res₁ p O x φ R w hconv s) = P₁.ord (rd s) := by
    rw [hθ₁ s, ← hP₁', Place.ord_congrRingEquiv]
  rw [res₁_apply, ResMatchOrdCore.read_apply] at key
  exact key

theorem ord₂ (hss : w ∈ ssPlaces p 1 k)
    (hy₂ : IsClosed ({(pullback.snd (𝔛.compInf k) (𝔛.compZero k)).base n} : Set ↥(𝔛.ratModel k).C))
    (hx₂ : x = (𝔛.compZero k ≫ DRModel.baseChangeMap toκ).base ((pullback.snd (𝔛.compInf k) (𝔛.compZero k)).base n))

    (hT1 : res₂ p O x φ R w hconv t = jGeomGen k 1 ^ p - algebraMap k ↥(modularFunctionFieldC k 1) c)

    (θ₂ : RatFunc k ≃+* ↥(modularFunctionFieldC k 1))
    (hθ₂k : ∀ a : k, θ₂ (algebraMap k (RatFunc k) a) = algebraMap k ↥(modularFunctionFieldC k 1) a)
    (hθ₂ : ∀ s, res₂ p O x φ R w hconv s =
      θ₂ (ResMatchOrdCore.read (𝔛.ratModel k) (𝔛.compZero k ≫ DRModel.baseChangeMap toκ)
        ((pullback.snd (𝔛.compInf k) (𝔛.compZero k)).base n) x hx₂ s))
    (s : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x) :
    (arithFrobC p k 1 • w).ord (R.nodeResidue₂ w ⟨_, hconv s⟩ : ↥(modularFunctionFieldC k 1)) =
      ((𝔛.ratModel k).placeOfPoint ⟨((pullback.snd (𝔛.compInf k) (𝔛.compZero k)).base n), hy₂⟩).ord
        ((𝔛.ratModel k).ffEquiv.symm (algebraMap _ (𝔛.ratModel k).C.functionField
          (((𝔛.compZero k ≫ DRModel.baseChangeMap toκ).stalkMap ((pullback.snd (𝔛.compInf k) (𝔛.compZero k)).base n)).hom
            (((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalkCongr (.of_eq hx₂)).hom.hom s)))) := by
  haveI : Fact p.Prime := inferInstance
  have hp : p.Prime := Fact.out
  set P₂ := (𝔛.ratModel k).placeOfPoint ⟨((pullback.snd (𝔛.compInf k) (𝔛.compZero k)).base n), hy₂⟩ with hP₂
  set rd := ResMatchOrdCore.read (𝔛.ratModel k) (𝔛.compZero k ≫ DRModel.baseChangeMap toκ)
        ((pullback.snd (𝔛.compInf k) (𝔛.compZero k)).base n) x hx₂ with hrd

  obtain ⟨c', hc'⟩ : ∃ c' : k, c' ^ p = c := ⟨(frobeniusEquiv k p).symm c, by
    have h := (frobeniusEquiv k p).apply_symm_apply c
    rwa [coe_frobeniusEquiv, frobenius_def] at h⟩
  haveI : CharP ↥(modularFunctionFieldC k 1) p :=
    charP_of_injective_algebraMap (algebraMap k ↥(modularFunctionFieldC k 1)).injective p
  have hfrob : jGeomGen k 1 ^ p - algebraMap k ↥(modularFunctionFieldC k 1) c =
      (jGeomGen k 1 - algebraMap k ↥(modularFunctionFieldC k 1) c') ^ p := by
    rw [← hc', map_pow, sub_pow_char]
  have hne' : jGeomGen k 1 - algebraMap k ↥(modularFunctionFieldC k 1) c' ≠ 0 :=
    jGeomGen_sub_algebraMap_ne_zero (k := k) c'

  have h0 : rd t ≠ 0 := fun h => by
    have := hθ₂ t
    rw [hT1, h, map_zero, hfrob] at this
    exact pow_ne_zero p hne' this
  have hpos : 0 < P₂.ord (rd t) :=
    ResMatchOrdCore.ord_read_pos (𝔛.ratModel k) _ _ hy₂ x hx₂ t ht h0

  have hP₂' : Place.congrRingEquiv θ₂ hθ₂k P₂ = charLGeomPlaceOfPoint k c' := by
    refine ModularCurve.eq_charLGeomPlaceOfPoint_of_ord_pos ?_
    rw [show ((⟨jqModC k, jqModC_mem k 1⟩ : ↥(modularFunctionFieldC k 1))) = jGeomGen k 1 from rfl]
    have h1 : 0 < (Place.congrRingEquiv θ₂ hθ₂k P₂).ord ((jGeomGen k 1 - algebraMap k ↥(modularFunctionFieldC k 1) c') ^ p) := by
      rw [← hfrob, ← hT1, hθ₂ t, Place.ord_congrRingEquiv]
      exact hpos
    rw [← zpow_natCast, Place.ord_zpow] at h1
    exact pos_of_mul_pos_right h1 (by exact_mod_cast Nat.zero_le p)

  have hFw : arithFrobC p k 1 • charLGeomPlaceOfPoint k c' = w := by
    rw [ModularCurve.arithFrobC_smul_charLGeomPlaceOfPoint p c', hc', ← hwc]
  have hFF : arithFrobC p k 1 • (arithFrobC p k 1 • w) = w :=
    ModularCurve.arithFrobC_smul_arithFrobC_smul_of_mem_ssPlaces p 1 k w hss
  have hw₂ : arithFrobC p k 1 • w = charLGeomPlaceOfPoint k c' := by
    apply smul_left_cancel (arithFrobC p k 1)
    rw [hFF, hFw]
  have key : (arithFrobC p k 1 • w).ord (res₂ p O x φ R w hconv s) = P₂.ord (rd s) := by
    rw [hθ₂ s, hw₂, ← hP₂', Place.ord_congrRingEquiv]
  rw [ResMatchOrdCore.read_apply] at key
  exact key

end Ord

end Concrete

end ModularCurve.DRModelPackage.ResMatchOrd

namespace ResMatchDock

open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple

set_option maxHeartbeats 6400000 in
open Classical in

theorem nodeResidue_of_eq_jFun_sub
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (𝔛 : DRModelPackage p)

    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})
    (K : Type) [Field K] [Algebra O K] [IsFractionRing O K]
    (ιK : K →+* AlgebraicClosure ℚ)

    [hint : IsIntegral (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))))]
    (x : ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))))
    (φ : ↥((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField) →+*
      ↥(modularFunctionFieldBar (1 * p)))

    (hφO : ∀ a : O,
      φ (algebraMap ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x) _
        (((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.germ ⊤ x trivial).hom
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
        coeffEmb (AlgebraicClosure ℚ) ((a : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ))

    {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type} [Field k] [CharP k p] [PerfectField k] {red : A →+* k}
    {data : ModularPolynomialData p} {hKr : KroneckerCongruence p data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 p} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 p}
    (P : PlaceSpecialization A p 1 data hKr k red hα hβ) (R : ProlongationTuple P)
    (hιA : ∀ a : O, ιK (algebraMap O K a) ∈ A)

    [IsAlgClosed k] (toκ : O →+* k) (htoκ : ∀ a : O, toκ a = red ⟨ιK (algebraMap O K a), hιA a⟩)

    (w : Place k (modularFunctionFieldC k 1)) (hw : w ∈ ssPlaces p 1 k)
    (hxj : ∃ ĵ : O, red ⟨ιK (algebraMap O K ĵ), hιA ĵ⟩ = w.evalAt (jGeomGen k 1) ∧
      ∃ t ∈ IsLocalRing.maximalIdeal ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x),
        φ (algebraMap _ (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField t) =
          ModularCurve.PlaceSpecialization.ProlongationTuple.jFun 1 p -
            algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) (ιK (algebraMap O K ĵ)))

    (n : ↥(pullback (𝔛.compInf k) (𝔛.compZero k)))
    (hy₁ : IsClosed ({(pullback.fst (𝔛.compInf k) (𝔛.compZero k)).base n} : Set ↥(𝔛.ratModel k).C))
    (hy₂ : IsClosed ({(pullback.snd (𝔛.compInf k) (𝔛.compZero k)).base n} : Set ↥(𝔛.ratModel k).C))
    (hx₁ : x = (𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base ((pullback.fst (𝔛.compInf k) (𝔛.compZero k)).base n))
    (hx₂ : x = (𝔛.compZero k ≫ DRModel.baseChangeMap toκ).base ((pullback.snd (𝔛.compInf k) (𝔛.compZero k)).base n))
    (hsp₁ : (𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel k).C) ⤳ x)
    (hsp₂ : (𝔛.compZero k ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel k).C) ⤳ x)

    (tF : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x)
    (htF : φ (algebraMap _ (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField tF) =
      ModularCurve.PlaceSpecialization.ProlongationTuple.jQFun 1 p - ModularCurve.PlaceSpecialization.ProlongationTuple.jFun 1 p ^ p)
    (hor : ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalkSpecializes hsp₁).hom tF ∈ IsLocalRing.maximalIdeal _)

    (hconv : ∀ s : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x, φ (algebraMap _ (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField s) ∈ R.nodeIntegers w)
    (ĵ : O) (t : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x)
    (hφt : φ (algebraMap _ ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField) t) =
      jFun 1 p - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) (ιK (algebraMap O K ĵ))) :
    R.nodeResidue₁ w ⟨_, hconv t⟩ = jGeomGen k 1 - algebraMap k _ (red ⟨ιK (algebraMap O K ĵ), hιA ĵ⟩) ∧
    R.nodeResidue₂ w ⟨_, hconv t⟩ = jGeomGen k 1 ^ p - algebraMap k _ (red ⟨ιK (algebraMap O K ĵ), hιA ĵ⟩) := by
  have hp1 : ¬ p ∣ 1 := fun h => (Fact.out : p.Prime).ne_one (Nat.dvd_one.mp h)
  obtain ⟨h₁, h₂, -, -, e₁, e₂, -, -⟩ := R.residue_jFun_sub_jQFun_sub hp1 ⟨ιK (algebraMap O K ĵ), hιA ĵ⟩
  constructor
  · show R.residue₁ ⟨_, (hconv t).1⟩ = _
    rw [← e₁]; congr 1; exact Subtype.ext hφt
  · show R.residue₂ ⟨_, (hconv t).2.1⟩ = _
    rw [← e₂]; congr 1; exact Subtype.ext hφt

open Classical in

theorem phi_germ_const
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (𝔛 : DRModelPackage p)

    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})
    (K : Type) [Field K] [Algebra O K] [IsFractionRing O K]
    (ιK : K →+* AlgebraicClosure ℚ)

    [hint : IsIntegral (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))))]
    (x : ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))))
    (φ : ↥((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField) →+*
      ↥(modularFunctionFieldBar (1 * p)))

    (hφO : ∀ a : O,
      φ (algebraMap ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x) _
        (((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.germ ⊤ x trivial).hom
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
        coeffEmb (AlgebraicClosure ℚ) ((a : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ))

    {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type} [Field k] [CharP k p] [PerfectField k] {red : A →+* k}
    {data : ModularPolynomialData p} {hKr : KroneckerCongruence p data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 p} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 p}
    (P : PlaceSpecialization A p 1 data hKr k red hα hβ) (R : ProlongationTuple P)
    (hιA : ∀ a : O, ιK (algebraMap O K a) ∈ A)

    [IsAlgClosed k] (toκ : O →+* k) (htoκ : ∀ a : O, toκ a = red ⟨ιK (algebraMap O K a), hιA a⟩)

    (w : Place k (modularFunctionFieldC k 1)) (hw : w ∈ ssPlaces p 1 k)
    (hxj : ∃ ĵ : O, red ⟨ιK (algebraMap O K ĵ), hιA ĵ⟩ = w.evalAt (jGeomGen k 1) ∧
      ∃ t ∈ IsLocalRing.maximalIdeal ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x),
        φ (algebraMap _ (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField t) =
          ModularCurve.PlaceSpecialization.ProlongationTuple.jFun 1 p -
            algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) (ιK (algebraMap O K ĵ)))

    (n : ↥(pullback (𝔛.compInf k) (𝔛.compZero k)))
    (hy₁ : IsClosed ({(pullback.fst (𝔛.compInf k) (𝔛.compZero k)).base n} : Set ↥(𝔛.ratModel k).C))
    (hy₂ : IsClosed ({(pullback.snd (𝔛.compInf k) (𝔛.compZero k)).base n} : Set ↥(𝔛.ratModel k).C))
    (hx₁ : x = (𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base ((pullback.fst (𝔛.compInf k) (𝔛.compZero k)).base n))
    (hx₂ : x = (𝔛.compZero k ≫ DRModel.baseChangeMap toκ).base ((pullback.snd (𝔛.compInf k) (𝔛.compZero k)).base n))
    (hsp₁ : (𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel k).C) ⤳ x)
    (hsp₂ : (𝔛.compZero k ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel k).C) ⤳ x)

    (tF : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x)
    (htF : φ (algebraMap _ (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField tF) =
      ModularCurve.PlaceSpecialization.ProlongationTuple.jQFun 1 p - ModularCurve.PlaceSpecialization.ProlongationTuple.jFun 1 p ^ p)
    (hor : ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalkSpecializes hsp₁).hom tF ∈ IsLocalRing.maximalIdeal _)

    (hconv : ∀ s : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x, φ (algebraMap _ (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField s) ∈ R.nodeIntegers w)
    (ξ : ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))))) (a : O) :
    φ (algebraMap ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk ξ) _
        (((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.germ ⊤ ξ trivial).hom
          (((pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).appTop).hom
            ((Scheme.ΓSpecIso (CommRingCat.of O)).inv a)))) =
      algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) (ιK (algebraMap O K a)) := by
  rw [← hφO a]
  congr 1
  show ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.germ ⊤ ξ trivial ≫ (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalkSpecializes _).hom _ =
    ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.germ ⊤ x trivial ≫ (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalkSpecializes _).hom _
  rw [TopCat.Presheaf.germ_stalkSpecializes, TopCat.Presheaf.germ_stalkSpecializes]

theorem residue_eq_zero_of_mem_nonunits {p : ℕ} [Fact p.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type} [Field k] [CharP k p] {red : A →+* k}
    {data : ModularPolynomialData p} {hKr : KroneckerCongruence p data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 p} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 p}
    {P : PlaceSpecialization A p 1 data hKr k red hα hβ} (R : ProlongationTuple P)
    (f : ↥(modularFunctionFieldBar (1 * p))) :
    (∀ (h : f ∈ R.R₁.integers), f ∈ R.R₁.integers.nonunits → R.residue₁ ⟨f, h⟩ = 0) ∧
    (∀ (h : f ∈ R.R₂.integers), f ∈ R.R₂.integers.nonunits → R.residue₂ ⟨f, h⟩ = 0) := by
  constructor
  · intro h hn
    rw [residue₁_apply, map_eq_zero_iff _ R.ι.injective, ← RingHom.mem_ker, RegularProlongation.ker_residue,
      ← ValuationSubring.coe_mem_nonunits_iff]
    exact hn
  · intro h hn
    rw [residue₂_apply, map_eq_zero_iff _ R.ι.injective, ← RingHom.mem_ker, RegularProlongation.ker_residue,
      ← ValuationSubring.coe_mem_nonunits_iff]
    exact hn

end ResMatchDock

theorem mem_nonunits_iff_mem_maximalIdeal_of_forall {S L F : Type*} [CommRing S] [IsLocalRing S] [Field L] [Field F]
    (a : S →+* L) (φ : L →+* F) (V : ValuationSubring F)
    (hV : ∀ u, φ (a u) ∈ V ∧ (u ∈ IsLocalRing.maximalIdeal S → φ (a u) ∈ V.nonunits)) (u : S) :
    φ (a u) ∈ V.nonunits ↔ u ∈ IsLocalRing.maximalIdeal S := by
  refine ⟨fun hn => ?_, fun hu => (hV u).2 hu⟩
  by_contra hu
  have hunit : IsUnit u := not_not.mp ((IsLocalRing.mem_maximalIdeal u).not.mp hu)
  obtain ⟨v, hv⟩ := hunit.exists_right_inv
  have h1 : (⟨φ (a u), (hV u).1⟩ : V) * ⟨φ (a v), (hV v).1⟩ = 1 :=
    Subtype.ext (by rw [V.coe_mul, ← map_mul, ← map_mul, hv, map_one, map_one]; rfl)
  have h2 : IsUnit (⟨φ (a u), (hV u).1⟩ : V) := IsUnit.of_mul_eq_one _ h1
  exact (IsLocalRing.mem_maximalIdeal _).mp (ValuationSubring.coe_mem_nonunits_iff.mp hn) h2

set_option maxHeartbeats 12800000 in
open Classical in
open ModularCurve.DRModelPackage.ResMatchOrd ResMatchDock in
theorem solution
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (𝔛 : DRModelPackage p)

    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})
    (K : Type) [Field K] [Algebra O K] [IsFractionRing O K]
    (ιK : K →+* AlgebraicClosure ℚ)

    [hint : IsIntegral (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))))]
    (x : ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))))
    (φ : ↥((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField) →+*
      ↥(modularFunctionFieldBar (1 * p)))

    (hφO : ∀ a : O,
      φ (algebraMap ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x) _
        (((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.germ ⊤ x trivial).hom
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
        coeffEmb (AlgebraicClosure ℚ) ((a : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ))

    {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type} [Field k] [CharP k p] [PerfectField k] {red : A →+* k}
    {data : ModularPolynomialData p} {hKr : KroneckerCongruence p data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 p} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 p}
    (P : PlaceSpecialization A p 1 data hKr k red hα hβ) (R : ProlongationTuple P)
    (hιA : ∀ a : O, ιK (algebraMap O K a) ∈ A)

    [IsAlgClosed k] (toκ : O →+* k) (htoκ : ∀ a : O, toκ a = red ⟨ιK (algebraMap O K a), hιA a⟩)

    (w : Place k (modularFunctionFieldC k 1)) (hw : w ∈ ssPlaces p 1 k)
    (hxj : ∃ ĵ : O, red ⟨ιK (algebraMap O K ĵ), hιA ĵ⟩ = w.evalAt (jGeomGen k 1) ∧
      ∃ t ∈ IsLocalRing.maximalIdeal ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x),
        φ (algebraMap _ (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField t) =
          ModularCurve.PlaceSpecialization.ProlongationTuple.jFun 1 p -
            algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) (ιK (algebraMap O K ĵ)))

    (n : ↥(pullback (𝔛.compInf k) (𝔛.compZero k)))
    (hy₁ : IsClosed ({(pullback.fst (𝔛.compInf k) (𝔛.compZero k)).base n} : Set ↥(𝔛.ratModel k).C))
    (hy₂ : IsClosed ({(pullback.snd (𝔛.compInf k) (𝔛.compZero k)).base n} : Set ↥(𝔛.ratModel k).C))
    (hx₁ : x = (𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base ((pullback.fst (𝔛.compInf k) (𝔛.compZero k)).base n))
    (hx₂ : x = (𝔛.compZero k ≫ DRModel.baseChangeMap toκ).base ((pullback.snd (𝔛.compInf k) (𝔛.compZero k)).base n))
    (hsp₁ : (𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel k).C) ⤳ x)
    (hsp₂ : (𝔛.compZero k ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel k).C) ⤳ x)

    (tF : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x)
    (htF : φ (algebraMap _ (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField tF) =
      ModularCurve.PlaceSpecialization.ProlongationTuple.jQFun 1 p - ModularCurve.PlaceSpecialization.ProlongationTuple.jFun 1 p ^ p)
    (hor : ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalkSpecializes hsp₁).hom tF ∈ IsLocalRing.maximalIdeal _)

    (hconv : ∀ s : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x, φ (algebraMap _ (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField s) ∈ R.nodeIntegers w) :
    ∀ s : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x,

      (R.nodeResidue₁ w ⟨_, hconv s⟩ = 0 ↔
        s ∈ Ideal.comap ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalkSpecializes hsp₁).hom (IsLocalRing.maximalIdeal _)) ∧
      (R.nodeResidue₂ w ⟨_, hconv s⟩ = 0 ↔
        s ∈ Ideal.comap ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalkSpecializes hsp₂).hom (IsLocalRing.maximalIdeal _)) ∧

      w.ord (R.nodeResidue₁ w ⟨_, hconv s⟩ : ↥(modularFunctionFieldC k 1)) =
        ((𝔛.ratModel k).placeOfPoint ⟨((pullback.fst (𝔛.compInf k) (𝔛.compZero k)).base n), hy₁⟩).ord ((𝔛.ratModel k).ffEquiv.symm (algebraMap _ (𝔛.ratModel k).C.functionField
            (((𝔛.compInf k ≫ DRModel.baseChangeMap toκ).stalkMap ((pullback.fst (𝔛.compInf k) (𝔛.compZero k)).base n)).hom (((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalkCongr (.of_eq hx₁)).hom.hom s)))) ∧
      (arithFrobC p k 1 • w).ord (R.nodeResidue₂ w ⟨_, hconv s⟩ : ↥(modularFunctionFieldC k 1)) =
        ((𝔛.ratModel k).placeOfPoint ⟨((pullback.snd (𝔛.compInf k) (𝔛.compZero k)).base n), hy₂⟩).ord ((𝔛.ratModel k).ffEquiv.symm (algebraMap _ (𝔛.ratModel k).C.functionField
            (((𝔛.compZero k ≫ DRModel.baseChangeMap toκ).stalkMap ((pullback.snd (𝔛.compInf k) (𝔛.compZero k)).base n)).hom (((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalkCongr (.of_eq hx₂)).hom.hom s)))) := by

  obtain ⟨hV₁, hV₂, hj₁, hj₂⟩ :=
    ModularCurve.DRModelPackage.phi_algebraMap_stalk_mem_integers_and_exists_eq_jFun_of_specializes_of_mem_maximalIdeal
      p hp 𝔛 O hϖ K ιK x φ hφO hφj P R hιA toκ htoκ w hw hxj n hy₁ hy₂ hx₁ hx₂ hsp₁ hsp₂ tF htF hor hconv
  have hval₁ := fun u => (hV₁ u).1
  have hval₂ := fun u => (hV₂ u).1
  have hloc₁ : ∀ u, u ∈ IsLocalRing.maximalIdeal _ → R.residue₁ ⟨_, hval₁ u⟩ = 0 :=
    fun u hu => (residue_eq_zero_of_mem_nonunits R _).1 _ ((hV₁ u).2 hu)
  have hloc₂ : ∀ u, u ∈ IsLocalRing.maximalIdeal _ → R.residue₂ ⟨_, hval₂ u⟩ = 0 :=
    fun u hu => (residue_eq_zero_of_mem_nonunits R _).2 _ ((hV₂ u).2 hu)

  obtain ⟨θ₁, hθ₁k, hθ₁ξ⟩ :=
    ModularCurve.DRModelPackage.exists_ringEquiv_ratFunc_forall_stalkMap_genericPoint_eq_residueFst
      p hp 𝔛 O hϖ K ιK φ P R hιA toκ htoκ (fun a => phi_germ_const p hp 𝔛 O hϖ K ιK x φ hφO hφj P R hιA toκ htoκ w hw hxj n hy₁ hy₂ hx₁ hx₂ hsp₁ hsp₂ tF htF hor hconv _ a) hval₁ hloc₁ hj₁
  obtain ⟨θ₂, hθ₂k, hθ₂ξ⟩ :=
    ModularCurve.DRModelPackage.exists_ringEquiv_ratFunc_forall_stalkMap_genericPoint_eq_residueSnd
      p hp 𝔛 O hϖ K ιK φ P R hιA toκ htoκ (fun a => phi_germ_const p hp 𝔛 O hϖ K ιK x φ hφO hφj P R hιA toκ htoκ w hw hxj n hy₁ hy₂ hx₁ hx₂ hsp₁ hsp₂ tF htF hor hconv _ a) hval₂ hloc₂ hj₂
  have hθ₁ := res₁_eq_theta_read p 𝔛 O x φ R toκ w n hx₁ hsp₁ hconv hval₁ θ₁ hθ₁ξ
  have hθ₂ := res₂_eq_theta_read p 𝔛 O x φ R toκ w n hx₂ hconv hval₂ θ₂ hθ₂ξ

  obtain ⟨ĵ, hĵ, t, ht, hφt⟩ := hxj
  have hwc := eq_charLGeomPlaceOfPoint_evalAt_of_mem_ssPlaces (p := p) hw
  obtain ⟨hT1₁, hT1₂⟩ := nodeResidue_of_eq_jFun_sub p hp 𝔛 O hϖ K ιK x φ hφO hφj P R hιA toκ htoκ w hw ⟨ĵ, hĵ, t, ht, hφt⟩ n hy₁ hy₂ hx₁ hx₂ hsp₁ hsp₂ tF htF hor hconv ĵ t hφt
  rw [hĵ] at hT1₁ hT1₂
  intro s
  refine ⟨?_, ?_, ?_, ?_⟩

  · have h1 : R.nodeResidue₁ w ⟨_, hconv s⟩ = 0 ↔
        φ (algebraMap _ (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField s) ∈
          R.R₁.integers.nonunits := by
      show R.residue₁ ⟨_, (hconv s).1⟩ = 0 ↔ _
      rw [ProlongationTuple.residue₁_apply, map_eq_zero_iff _ R.ι.injective, ← RingHom.mem_ker, RegularProlongation.ker_residue,
        ← ValuationSubring.coe_mem_nonunits_iff]
    rw [h1, ← algebraMap_functionField_stalkSpecializes hsp₁ s, Ideal.mem_comap]
    exact mem_nonunits_iff_mem_maximalIdeal_of_forall _ φ R.R₁.integers hV₁ _

  · have h1 : R.nodeResidue₂ w ⟨_, hconv s⟩ = 0 ↔
        φ (algebraMap _ (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField s) ∈
          R.R₂.integers.nonunits := by
      show R.residue₂ ⟨_, (hconv s).2.1⟩ = 0 ↔ _
      rw [ProlongationTuple.residue₂_apply, map_eq_zero_iff _ R.ι.injective, ← RingHom.mem_ker, RegularProlongation.ker_residue,
        ← ValuationSubring.coe_mem_nonunits_iff]
    rw [h1, ← algebraMap_functionField_stalkSpecializes hsp₂ s, Ideal.mem_comap]
    exact mem_nonunits_iff_mem_maximalIdeal_of_forall _ φ R.R₂.integers hV₂ _

  · exact ord₁ p 𝔛 O x φ R toκ w n hconv (w.evalAt (jGeomGen k 1)) hwc t ht hy₁ hx₁ hT1₁ θ₁ hθ₁k hθ₁ s

  · exact ord₂ p 𝔛 O x φ R toκ w n hconv (w.evalAt (jGeomGen k 1)) hwc t ht hw hy₂ hx₂ hT1₂ θ₂ hθ₂k hθ₂ s

end

end S_ModularCurve_DRModelPackage_nodeResidue_eq_zero_iff_and_ord_eq_of_specializes_of_mem_maximalIdeal
end P2MW
export P2MW.S_ModularCurve_DRModelPackage_nodeResidue_eq_zero_iff_and_ord_eq_of_specializes_of_mem_maximalIdeal (solution)
