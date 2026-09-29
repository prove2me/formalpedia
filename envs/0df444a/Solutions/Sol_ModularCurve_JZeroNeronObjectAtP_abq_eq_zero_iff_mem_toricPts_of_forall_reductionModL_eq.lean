-- Prove2me | solution 1 for ModularCurve.JZeroNeronObjectAtP.abq_eq_zero_iff_mem_toricPts_of_forall_reductionModL_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/356cac4f-521d-5d2a-90c0-4e96f4df1332

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_ModularCurve_JZeroNeronAtPData
import Definitions.Def_AlgebraicCurve_Repartitions
import Theorems.Thm_AlgebraicGeometry_SchemeHomOver_ext_of_forall_algebraicClosure_point_of_isReduced_of_flat
import Theorems.Thm_ValuationSubring_addMonoidAlgebra_algHom_apply_mem_of_isOfFinAddOrder
import Theorems.Thm_ModularCurve_JZeroNeronObjectAtP_toricPts_of_pos
import Theorems.Thm_ModularCurve_JZeroNeronObjectAtP_toricPts_le_finPts
import Theorems.Thm_ModularCurve_eq_zero_of_reductionModL_eq_zero_of_nsmul_eq_zero
import Theorems.Thm_ModularCurve_reductionInputsModL_of_not_dvd
import Theorems.Thm_ValuationSubring_charP_residueField_of_liesOverPrime
import Theorems.Thm_ValuationSubring_henselianLocalRing_of_isAlgClosed
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_eq_one_of_isTorsionPoint_of_comp_residue_eq
import Theorems.Thm_ModularCurve_JZeroNeronObjectAtP_mem_finPts_iff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JZeroNeronObjectAtP_abq_eq_zero_iff_mem_toricPts_of_forall_reductionModL_eq
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt CuspForm.heckeAlgebra.instCommRing CuspForm.heckeAlgebra.instIsMulCommutative CuspForm.heckeAlgebra.instIsAddTorsionFree ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent"
p2m_attr_erase "instance" "ModularCurve.instModuleKaehlerIntermediateFieldLaurent ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar ModularCurve.instIsScalarTowerJAdjoin FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par HeckeEis.instFiniteIndexHeckeUpper WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular"
p2m_attr_erase "simp" "AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.dualHeckeRep_apply_apply ModularCurve.coe_segmentPath ModularCurve.cuspHeckeAeval_heckeGen ModularCurve.coe_periodLatticeRestrict_apply CuspForm.heckeAlgebra.coe_U CuspForm.heckeAlgebra.coe_T ModularForm.coe_heckeTLin_apply CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply ModularForm.coe_heckeULin_apply ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃"
p2m_attr_erase "simp" "PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ ModularCurve.ProjectiveLine.map_mk AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.cuspCount_one ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluX_empty WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply HahnSeries.ramScale_apply WeierstrassCurve.veluPointMap2_zero FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero HeckeEis.coeffCoboundaryMap_apply HeckeEis.heckeConjMat_apply_one_one"
p2m_attr_erase "simp" "HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some"
p2m_attr_erase "simp" "FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff"

set_option autoImplicit false

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve IsLocalRing AlgebraicCurve ModularCurve.JZeroNeronObjectAtP

noncomputable section

namespace ABQK

variable {N₀ p : ℕ} [NeZero N₀] [Fact p.Prime] [NeZero p] {hpN₀ : ¬ p ∣ N₀}
  {A : ValuationSubring (AlgebraicClosure ℚ)} {hA : A.LiesOverPrime p} {Λ : LevelData N₀ p A}

theorem eq_one_of_mul_self {R : Type} [CommRing R] {X T : Scheme.{0}} {f : X ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (t : T ⟶ Spec (CommRingCat.of R)) (a : SchemeHomOver t f) (h : L.mul t a a = a) :
    a = L.one t := by
  calc a = L.mul t (L.one t) a := (L.one_mul t a).symm
    _ = L.mul t (L.mul t (L.inv t a) a) a := by rw [L.inv_mul_cancel]
    _ = L.mul t (L.inv t a) (L.mul t a a) := by rw [L.mul_assoc]
    _ = L.one t := by rw [h, L.inv_mul_cancel]

theorem mul_castOver {R : Type} [CommRing R] {X T : Scheme.{0}} {f : X ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) {ι ι' : T ⟶ Spec (CommRingCat.of R)} (h : ι = ι') (u v : SchemeHomOver ι f) :
    L.mul ι' (castOver h u) (castOver h v) = castOver h (L.mul ι u v) := by
  subst h; rfl

theorem one_castOver {R : Type} [CommRing R] {X T : Scheme.{0}} {f : X ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) {ι ι' : T ⟶ Spec (CommRingCat.of R)} (h : ι = ι') :
    L.one ι' = castOver h (L.one ι) := by
  subst h; rfl

theorem nsmul_castOver {R : Type} [CommRing R] {X T : Scheme.{0}} {f : X ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) {ι ι' : T ⟶ Spec (CommRingCat.of R)} (h : ι = ι') (n : ℕ) (u : SchemeHomOver ι f) :
    L.nsmul ι' n (castOver h u) = castOver h (L.nsmul ι n u) := by
  subst h; rfl

theorem overId_eq_castOver {B T X : Scheme.{0}} {ι : T ⟶ B} {f : X ⟶ B} (x : SchemeHomOver ι f) :
    overId x = castOver (Category.id_comp ι).symm x := Subtype.ext rfl

theorem ofFibrePt_one {R R' : Type} [CommRing R] [CommRing R'] {X : Scheme.{0}}
    {ι : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R)} {f : X ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) :
    ofFibrePt ((L.baseChange ι).one (𝟙 _)) = L.one ι := by
  apply Subtype.ext
  show (RelativeGroupLaw.baseChangePointToBase ι ((L.baseChange ι).one (𝟙 _))).1 = _
  rw [RelativeGroupLaw.baseChangePointToBase_one, one_castOver L (Category.id_comp ι).symm]
  rfl

omit [Fact (Nat.Prime p)] [NeZero p] in
theorem ext_unique_aux {X : Scheme.{0}} {f : X ⟶ base p} [IsSeparated f]
    (P Q : SchemeHomOver Λ.σA f) (h : barPt A ≫ P.1 = barPt A ≫ Q.1) : P = Q := by
  haveI : IsSeparated (RelativeGroupLaw.baseChangeStr Λ.σA f) := by
    show IsSeparated (pullback.snd f Λ.σA); infer_instance
  have key : toFibrePt P = toFibrePt Q := by
    refine AlgebraicGeometry.SchemeHomOver.ext_of_forall_algebraicClosure_point_of_isReduced_of_flat
      (R := ↥A) (AlgebraicClosure ℚ) (AlgebraicClosure ℚ) (gY := 𝟙 (Spec (CommRingCat.of ↥A)))
      (gX := RelativeGroupLaw.baseChangeStr Λ.σA f) (toFibrePt P) (toFibrePt Q) ?_
    intro z
    have hz : z.1 = barPt A := by first | simpa using z.2 | exact z.2
    rw [hz]
    show barPt A ≫ pullback.lift P.1 (𝟙 _) _ = barPt A ≫ pullback.lift Q.1 (𝟙 _) _
    apply pullback.hom_ext
    · simpa only [Category.assoc, pullback.lift_fst] using h
    · simp only [Category.assoc, pullback.lift_snd]
  apply Subtype.ext
  have h1 : P.1 = (toFibrePt P).1 ≫ pullback.fst f Λ.σA := by
    show P.1 = pullback.lift P.1 (𝟙 _) _ ≫ pullback.fst f Λ.σA
    rw [pullback.lift_fst]
  have h2 : Q.1 = (toFibrePt Q).1 ≫ pullback.fst f Λ.σA := by
    show Q.1 = pullback.lift Q.1 (𝟙 _) _ ≫ pullback.fst f Λ.σA
    rw [pullback.lift_fst]
  rw [h1, h2, key]

theorem ext_unique (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ)
    (P Q : SchemeHomOver Λ.σA O.g) (h : barPt A ≫ P.1 = barPt A ≫ Q.1) : P = Q := by
  haveI : IsSeparated O.g := O.separated
  exact ext_unique_aux P Q h

theorem pts_zero (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) : O.pts 0 = O.L.one (genPt p) :=
  eq_one_of_mul_self O.L _ _ (by rw [← O.pts_add, add_zero])

theorem pts_nsmul (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) (n : ℕ) (x : JZero (N₀ * p)) :
    O.pts (n • x) = O.L.nsmul (genPt p) n (O.pts x) := by
  induction n with
  | zero => rw [zero_nsmul, pts_zero, RelativeGroupLaw.nsmul_zero]
  | succ n ih => rw [succ_nsmul, O.pts_add, ih, RelativeGroupLaw.nsmul_succ]

theorem nsmul_eq_one_of_ext (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) {m : ℕ} (x : JZero (N₀ * p)) (hx : m • x = 0)
    (s : SchemeHomOver Λ.σA O.g) (hs : (O.pts x).1 = barPt A ≫ s.1) :
    O.L.nsmul Λ.σA m s = O.L.one Λ.σA := by
  apply ext_unique O
  have h1 := congrArg Subtype.val (O.L.nsmul_natural Λ.σA (barPt A ≫ Λ.σA) (barPt A) rfl m s)
  have h2 := congrArg Subtype.val (O.L.one_natural Λ.σA (barPt A ≫ Λ.σA) (barPt A) rfl)
  simp only [GoodReductionJacobian.schemeHomOverComp_coe] at h1 h2
  rw [h1, h2]
  have hx' : O.pts x = castOver Λ.hσA (GoodReductionJacobian.schemeHomOverComp (barPt A) rfl s) := Subtype.ext hs
  have h3 := pts_nsmul O m x
  rw [hx, pts_zero, hx', nsmul_castOver, one_castOver O.L Λ.hσA] at h3
  have h4 := congrArg Subtype.val h3
  exact h4.symm

omit [NeZero p] in
theorem neZero_of_coprime {m : ℕ} (hm : m.Coprime p) : NeZero m := by
  refine ⟨fun h => ?_⟩
  subst h
  rw [Nat.coprime_zero_left] at hm
  exact (Fact.out : p.Prime).one_lt.ne' hm

theorem pos_of_coprime {m : ℕ} (hm : m.Coprime p) : 0 < m :=
  Nat.pos_of_ne_zero (neZero_of_coprime hm).out

def secA (A : ValuationSubring (AlgebraicClosure ℚ)) (t m : ℕ) (χA : muCoord ↥A t m →ₐ[↥A] ↥A) :
    Spec (CommRingCat.of ↥A) ⟶ muScheme ↥A t m :=
  Spec.map (CommRingCat.ofHom χA.toRingHom)

omit [NeZero N₀] [Fact (Nat.Prime p)] [NeZero p] in
theorem secA_muStr (t m : ℕ) (χA : muCoord ↥A t m →ₐ[↥A] ↥A) : secA A t m χA ≫ muStr ↥A t m = 𝟙 _ := by
  rw [secA, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have h : χA.toRingHom.comp (algebraMap ↥A (muCoord ↥A t m)) = RingHom.id _ := by
    ext a; simp
  rw [h, CommRingCat.ofHom_id, Spec.map_id]

def toricExt (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) {m : ℕ} (hm : 0 < m) (χA : muCoord ↥A O.toricRank m →ₐ[↥A] ↥A) :
    SchemeHomOver Λ.σA O.g :=
  ⟨secA A O.toricRank m χA ≫ (O.toricLift m hm).1 ≫ pullback.fst O.g Λ.σA, by
    rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc (O.toricLift m hm).1, (O.toricLift m hm).2,
      ← Category.assoc, secA_muStr, Category.id_comp]⟩

theorem toricExt_coe (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) {m : ℕ} (hm : 0 < m) (χA : muCoord ↥A O.toricRank m →ₐ[↥A] ↥A) :
    (toricExt O hm χA).1 = secA A O.toricRank m χA ≫ (O.toricLift m hm).1 ≫ pullback.fst O.g Λ.σA := rfl

theorem barPt_toricExt (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) {m : ℕ} (hm : 0 < m)
    (χA : muCoord ↥A O.toricRank m →ₐ[↥A] ↥A) (χ : muCoord ↥A O.toricRank m →ₐ[↥A] AlgebraicClosure ℚ)
    (hχ : ∀ x, ((χA x : ↥A) : AlgebraicClosure ℚ) = χ x) :
    barPt A ≫ (toricExt O hm χA).1 = (muPt A O.toricRank m χ).1 ≫ (O.toricLift m hm).1 ≫ pullback.fst O.g Λ.σA := by
  have hr : χ.toRingHom = A.subtype.comp χA.toRingHom := RingHom.ext (fun x => (hχ x).symm)
  have hmu : (muPt A O.toricRank m χ).1 = barPt A ≫ secA A O.toricRank m χA := by
    show Spec.map (CommRingCat.ofHom χ.toRingHom) = Spec.map (CommRingCat.ofHom A.subtype) ≫ Spec.map (CommRingCat.ofHom χA.toRingHom)
    rw [hr, CommRingCat.ofHom_comp, Spec.map_comp]
  rw [toricExt_coe, hmu, Category.assoc]

theorem pts_toricPoint_coe (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) {m : ℕ} (hm : 0 < m)
    (χ : muCoord ↥A O.toricRank m →ₐ[↥A] AlgebraicClosure ℚ) :
    (O.pts (O.toricPoint m hm χ)).1 = (muPt A O.toricRank m χ).1 ≫ (O.toricLift m hm).1 ≫ pullback.fst O.g Λ.σA := by
  rw [toricPoint, Equiv.apply_symm_apply]
  rfl

def redChar (A : ValuationSubring (AlgebraicClosure ℚ)) (t m : ℕ) (χA : muCoord ↥A t m →ₐ[↥A] ↥A) :
    muCoord (ResidueField ↥A) t m →ₐ[ResidueField ↥A] ResidueField ↥A :=
  AddMonoidAlgebra.lift _ _ _
    (((residue ↥A).toMonoidHom.comp χA.toRingHom.toMonoidHom).comp (AddMonoidAlgebra.of ↥A (Fin t → ZMod m)))

omit [NeZero N₀] [Fact (Nat.Prime p)] [NeZero p] in
theorem redChar_single (t m : ℕ) (χA : muCoord ↥A t m →ₐ[↥A] ↥A) (g : Fin t → ZMod m) :
    redChar A t m χA (AddMonoidAlgebra.single g 1) = residue ↥A (χA (AddMonoidAlgebra.single g 1)) := by
  rw [redChar]
  erw [AddMonoidAlgebra.lift_single]
  simp [AddMonoidAlgebra.of_apply]

omit [NeZero N₀] [Fact (Nat.Prime p)] [NeZero p] in
theorem redChar_comp_mapRingHom (t m : ℕ) (χA : muCoord ↥A t m →ₐ[↥A] ↥A) :
    (redChar A t m χA).toRingHom.comp (AddMonoidAlgebra.mapRingHom (Fin t → ZMod m) (residue ↥A)) =
      (residue ↥A).comp χA.toRingHom := by
  apply AddMonoidAlgebra.ringHom_ext
  · intro b
    simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    have h1 : AddMonoidAlgebra.mapRingHom (Fin t → ZMod m) (residue ↥A) (AddMonoidAlgebra.single 0 b) =
        AddMonoidAlgebra.single 0 (residue ↥A b) := by
      simp [AddMonoidAlgebra.mapRingHom]
    have h2 : (AddMonoidAlgebra.single (0 : Fin t → ZMod m) (residue ↥A b) : muCoord (ResidueField ↥A) t m) =
        algebraMap (ResidueField ↥A) _ (residue ↥A b) := rfl
    have h3 : (AddMonoidAlgebra.single (0 : Fin t → ZMod m) b : muCoord ↥A t m) = algebraMap ↥A _ b := rfl
    rw [h1, h2, AlgHom.commutes, h3, AlgHom.commutes]
    rfl
  · intro g
    simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    have h1 : AddMonoidAlgebra.mapRingHom (Fin t → ZMod m) (residue ↥A) (AddMonoidAlgebra.single g 1) =
        AddMonoidAlgebra.single g 1 := by
      simp [AddMonoidAlgebra.mapRingHom]
    rw [h1, redChar_single]

omit [NeZero N₀] [Fact (Nat.Prime p)] [NeZero p] in
theorem resPt_secA (t m : ℕ) (χA : muCoord ↥A t m →ₐ[↥A] ↥A) :
    resPt A ≫ secA A t m χA =
      Spec.map (CommRingCat.ofHom (redChar A t m χA).toRingHom) ≫ muBaseChange (residue ↥A) t m := by
  show Spec.map (CommRingCat.ofHom (residue ↥A)) ≫ Spec.map (CommRingCat.ofHom χA.toRingHom) =
    Spec.map (CommRingCat.ofHom (redChar A t m χA).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapRingHom (Fin t → ZMod m) (residue ↥A)))
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, redChar_comp_mapRingHom]

def torusPtRed (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) {m : ℕ} (χA : muCoord ↥A O.toricRank m →ₐ[↥A] ↥A) :
    SchemeHomOver (𝟙 (Spec (CommRingCat.of (ResidueField ↥A)))) (torusStr (ResidueField ↥A) O.toricRank) :=
  ⟨Spec.map (CommRingCat.ofHom (redChar A O.toricRank m χA).toRingHom) ≫ muToTorus (ResidueField ↥A) O.toricRank m, by
    have h1 : muToTorus (ResidueField ↥A) O.toricRank m ≫ torusStr (ResidueField ↥A) O.toricRank =
        muStr (ResidueField ↥A) O.toricRank m := by
      show Spec.map _ ≫ Spec.map _ = Spec.map _
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 2
      exact (AddMonoidAlgebra.mapDomainAlgHom (ResidueField ↥A) (ResidueField ↥A)
        (AddMonoidHom.pi fun i => (Int.castAddHom (ZMod m)).comp (Pi.evalAddMonoidHom (fun _ : Fin O.toricRank => ℤ) i))).comp_algebraMap
    have h2 : Spec.map (CommRingCat.ofHom (redChar A O.toricRank m χA).toRingHom) ≫ muStr (ResidueField ↥A) O.toricRank m = 𝟙 _ := by
      show Spec.map _ ≫ Spec.map _ = _
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
      have h : (redChar A O.toricRank m χA).toRingHom.comp (algebraMap (ResidueField ↥A) (muCoord (ResidueField ↥A) O.toricRank m)) =
          RingHom.id _ := by
        ext a; simp
      rw [h, CommRingCat.ofHom_id, Spec.map_id]
    rw [Category.assoc, h1, h2]⟩

theorem toFibrePt_red_toricExt (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) {m : ℕ} (hm : 0 < m)
    (χA : muCoord ↥A O.toricRank m →ₐ[↥A] ↥A) :
    toFibrePt (GoodReductionJacobian.schemeHomOverComp (resPt A) rfl (toricExt O hm χA)) =
      NeronModelInfra.schemeHomOverComp (torusPtRed O χA) O.torusFibre := by
  apply Subtype.ext
  apply pullback.hom_ext
  · show pullback.lift _ (𝟙 _) _ ≫ pullback.fst _ _ = ((torusPtRed O χA).1 ≫ O.torusFibre.1) ≫ pullback.fst _ _
    rw [pullback.lift_fst]
    show resPt A ≫ (toricExt O hm χA).1 = _
    rw [toricExt_coe, ← Category.assoc (resPt A), resPt_secA, Category.assoc, Category.assoc, O.toricLift_special m hm]
    first | rfl | (simp only [Category.assoc]; rfl)
  · show pullback.lift _ (𝟙 _) _ ≫ pullback.snd _ _ = ((torusPtRed O χA).1 ≫ O.torusFibre.1) ≫ pullback.snd _ _
    rw [pullback.lift_snd, Category.assoc, O.torusFibre.2]
    exact (torusPtRed O χA).2.symm

theorem fibreMap_abqFibre_red_toricExt (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) {m : ℕ} (hm : 0 < m)
    (χA : muCoord ↥A O.toricRank m →ₐ[↥A] ↥A) (i : Fin 2) :
    fibreMap (O.abqFibre i) (GoodReductionJacobian.schemeHomOverComp (resPt A) rfl (toricExt O hm χA)) = Λ.L.one _ := by
  have h := (O.abqFibre_eq_one_iff (𝟙 _) (toFibrePt (GoodReductionJacobian.schemeHomOverComp (resPt A) rfl
    (toricExt O hm χA)))).mpr ⟨torusPtRed O χA, (toFibrePt_red_toricExt O hm χA).symm⟩ i
  unfold fibreMap
  rw [h, ofFibrePt_one]

theorem ptsSp_zero (hΛ : Λ.IsJacobian) : Λ.ptsSp 0 = Λ.L.one _ :=
  eq_one_of_mul_self Λ.L _ _ (by rw [← hΛ.2.2.2.2.1, add_zero])

theorem ptsSp_symm_one (hΛ : Λ.IsJacobian) : Λ.ptsSp.symm (Λ.L.one _) = 0 := by
  rw [← ptsSp_zero hΛ, Equiv.symm_apply_apply]

section killed

variable (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ)
  (abq : ∀ m : ℕ, m.Coprime p → (↥(O.finPts m) →+ (JZero N₀ × JZero N₀)))
  (habq : ∀ (m : ℕ) (hm : m.Coprime p) (x : ↥(O.finPts m)),
    abq m hm x ∈ Submodule.torsionBy ℤ (JZero N₀ × JZero N₀) (m : ℤ))
  (hformula : ∀ (m : ℕ) (hm : m.Coprime p) (x : ↥(O.finPts m)) (s : SchemeHomOver Λ.σA O.g),
    (O.pts (x : JZero (N₀ * p))).1 = barPt A ≫ s.1 →
      reductionModL A N₀ (abq m hm x).1 =
        Λ.ptsSp.symm (fibreMap (O.abqFibre 0)
          (GoodReductionJacobian.schemeHomOverComp (resPt A) rfl s)) ∧
      reductionModL A N₀ (abq m hm x).2 =
        Λ.ptsSp.symm (fibreMap (O.abqFibre 1)
          (GoodReductionJacobian.schemeHomOverComp (resPt A) rfl s)))

include habq hformula in

theorem abq_eq_zero_of_ext (hΛ : Λ.IsJacobian) {m : ℕ} (hm : m.Coprime p) (x : ↥(O.finPts m)) (s : SchemeHomOver Λ.σA O.g)
    (hs : (O.pts (x : JZero (N₀ * p))).1 = barPt A ≫ s.1)
    (h0 : fibreMap (O.abqFibre 0) (GoodReductionJacobian.schemeHomOverComp (resPt A) rfl s) = Λ.L.one _)
    (h1 : fibreMap (O.abqFibre 1) (GoodReductionJacobian.schemeHomOverComp (resPt A) rfl s) = Λ.L.one _) :
    abq m hm x = 0 := by
  have hinp := reductionInputsModL_of_not_dvd N₀ hpN₀ A hA
  have hpm : ¬ p ∣ m := fun h => by
    have h1 : p ∣ Nat.gcd m p := Nat.dvd_gcd h (dvd_refl p)
    rw [hm] at h1
    exact (Fact.out : p.Prime).one_lt.ne' (Nat.dvd_one.mp h1)
  obtain ⟨hf0, hf1⟩ := hformula m hm x s hs
  rw [h0, ptsSp_symm_one hΛ] at hf0
  rw [h1, ptsSp_symm_one hΛ] at hf1
  have ht := habq m hm x
  rw [Submodule.mem_torsionBy_iff, natCast_zsmul, Prod.ext_iff, Prod.smul_fst, Prod.smul_snd] at ht
  exact Prod.ext (eq_zero_of_reductionModL_eq_zero_of_nsmul_eq_zero N₀ hpN₀ A hA hinp m hpm _ ht.1 hf0)
    (eq_zero_of_reductionModL_eq_zero_of_nsmul_eq_zero N₀ hpN₀ A hA hinp m hpm _ ht.2 hf1)

include habq hformula in
theorem abq_toricPoint_eq_zero (hΛ : Λ.IsJacobian) {m : ℕ} (hm : m.Coprime p)
    (χ : muCoord ↥A O.toricRank m →ₐ[↥A] AlgebraicClosure ℚ)
    (hx : O.toricPoint m (pos_of_coprime hm) χ ∈ O.finPts m) :
    abq m hm ⟨O.toricPoint m (pos_of_coprime hm) χ, hx⟩ = 0 := by
  haveI : NeZero m := neZero_of_coprime hm
  obtain ⟨-, χA, hχ⟩ := ValuationSubring.addMonoidAlgebra_algHom_apply_mem_of_isOfFinAddOrder A
    (G := Fin O.toricRank → ZMod m) (fun g => isOfFinAddOrder_of_finite g) χ
  refine abq_eq_zero_of_ext O abq habq hformula hΛ hm _ (toricExt O (pos_of_coprime hm) χA) ?_
    (fibreMap_abqFibre_red_toricExt O (pos_of_coprime hm) χA 0) (fibreMap_abqFibre_red_toricExt O (pos_of_coprime hm) χA 1)
  rw [barPt_toricExt O (pos_of_coprime hm) χA χ hχ]
  exact pts_toricPoint_coe O (pos_of_coprime hm) χ

include habq hformula in

theorem abq_eq_zero_of_mem_toricPts (hΛ : Λ.IsJacobian) {m : ℕ} (hm : m.Coprime p) (x : ↥(O.finPts m))
    (hx : (x : JZero (N₀ * p)) ∈ O.toricPts m) : abq m hm x = 0 := by
  have hm0 := pos_of_coprime hm
  rw [toricPts_of_pos O hm0] at hx

  suffices H : ∀ y ∈ AddSubgroup.closure (Set.range (O.toricPoint m hm0)), ∀ hy : y ∈ O.finPts m, abq m hm ⟨y, hy⟩ = 0 by
    have := H x hx x.2
    simpa using this
  intro y hy
  induction hy using AddSubgroup.closure_induction with
  | mem z hz =>
      obtain ⟨χ, rfl⟩ := hz
      intro hy
      exact abq_toricPoint_eq_zero O abq habq hformula hΛ hm χ hy
  | zero =>
      intro hy
      have : (⟨0, hy⟩ : ↥(O.finPts m)) = 0 := Subtype.ext rfl
      rw [this, map_zero]
  | add a b ha hb iha ihb =>
      intro hy
      have ha' : a ∈ O.finPts m := toricPts_le_finPts O m ((toricPts_of_pos O hm0).symm ▸ ha)
      have hb' : b ∈ O.finPts m := toricPts_le_finPts O m ((toricPts_of_pos O hm0).symm ▸ hb)
      have : (⟨a + b, hy⟩ : ↥(O.finPts m)) = ⟨a, ha'⟩ + ⟨b, hb'⟩ := Subtype.ext rfl
      rw [this, map_add, iha ha', ihb hb', add_zero]
  | neg a ha iha =>
      intro hy
      have ha' : a ∈ O.finPts m := toricPts_le_finPts O m ((toricPts_of_pos O hm0).symm ▸ ha)
      have : (⟨-a, hy⟩ : ↥(O.finPts m)) = -⟨a, ha'⟩ := Subtype.ext rfl
      rw [this, map_neg, iha ha', neg_zero]

end killed

omit [NeZero N₀] [Fact (Nat.Prime p)] [NeZero p] in

theorem convMul_single {S K : Type} [CommRing S] [CommRing K] [Algebra S K] {G : Type} [AddCommGroup G]
    (χ ψ : WithConv (AddMonoidAlgebra S G →ₐ[S] K)) (g : G) :
    (χ * ψ).ofConv (AddMonoidAlgebra.single g 1) =
      χ.ofConv (AddMonoidAlgebra.single g 1) * ψ.ofConv (AddMonoidAlgebra.single g 1) := by
  rw [AlgHom.convMul_def]
  simp [AddMonoidAlgebra.comul_single, Algebra.TensorProduct.lmul'_apply_tmul]

omit [NeZero N₀] [Fact (Nat.Prime p)] [NeZero p] in
theorem convOne_single {S K : Type} [CommRing S] [CommRing K] [Algebra S K] {G : Type} [AddCommGroup G] (g : G) :
    (1 : WithConv (AddMonoidAlgebra S G →ₐ[S] K)).ofConv (AddMonoidAlgebra.single g 1) = 1 := by
  rw [AlgHom.convOne_def]
  simp [AddMonoidAlgebra.counit_single]

omit [NeZero N₀] [Fact (Nat.Prime p)] [NeZero p] in
theorem convPow_single {S K : Type} [CommRing S] [CommRing K] [Algebra S K] {G : Type} [AddCommGroup G]
    (χ : WithConv (AddMonoidAlgebra S G →ₐ[S] K)) (k : ℕ) (g : G) :
    (χ ^ k).ofConv (AddMonoidAlgebra.single g 1) = (χ.ofConv (AddMonoidAlgebra.single g 1)) ^ k := by
  induction k with
  | zero => rw [pow_zero, pow_zero, convOne_single]
  | succ k ih => rw [pow_succ, convMul_single, ih, pow_succ]

omit [NeZero N₀] [Fact (Nat.Prime p)] [NeZero p] in
theorem pow_mod_of_pow_eq_one {M : Type} [Monoid M] {u : M} {m : ℕ} (hu : u ^ m = 1) (n : ℕ) : u ^ (n % m) = u ^ n := by
  conv_rhs => rw [← Nat.mod_add_div n m, pow_add, pow_mul, hu, one_pow, mul_one]

omit [NeZero N₀] [NeZero p] in

theorem isUnit_natCast_of_not_dvd (hA : A.LiesOverPrime p) {m : ℕ} (hm : ¬ p ∣ m) : IsUnit ((m : ℕ) : ↥A) := by
  haveI := ValuationSubring.charP_residueField_of_liesOverPrime p A hA
  rw [← residue_ne_zero_iff_isUnit, map_natCast, Ne, CharP.cast_eq_zero_iff (ResidueField ↥A) p]
  exact hm

omit [NeZero N₀] [NeZero p] in

theorem exists_pow_eq_one_and_residue_eq (hA : A.LiesOverPrime p) {m : ℕ} (hm0 : 0 < m) (hm : ¬ p ∣ m)
    (u : ResidueField ↥A) (hu : u ^ m = 1) : ∃ ζ : ↥A, ζ ^ m = 1 ∧ residue ↥A ζ = u := by
  haveI : HenselianLocalRing ↥A := ValuationSubring.henselianLocalRing_of_isAlgClosed A
  obtain ⟨a₀, ha₀⟩ := residue_surjective u
  have hu0 : u ≠ 0 := by
    rintro rfl
    rw [zero_pow hm0.ne'] at hu
    exact zero_ne_one hu
  have ha₀u : IsUnit a₀ := (residue_ne_zero_iff_isUnit a₀).mp (ha₀ ▸ hu0)
  obtain ⟨a, hroot, hsub⟩ := HenselianLocalRing.is_henselian (Polynomial.X ^ m - Polynomial.C 1)
    (Polynomial.monic_X_pow_sub_C 1 hm0.ne') a₀ (by
      rw [← residue_eq_zero_iff]
      simp [ha₀, hu]) (by
      have hd : Polynomial.eval a₀ (Polynomial.derivative (Polynomial.X ^ m - Polynomial.C (1 : ↥A))) =
          (m : ↥A) * a₀ ^ (m - 1) := by
        rw [Polynomial.derivative_sub, Polynomial.derivative_C, sub_zero, Polynomial.derivative_X_pow,
          Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]
        first | rfl | simp | (congr 1; simp)
      rw [hd]
      exact (isUnit_natCast_of_not_dvd hA hm).mul (ha₀u.pow _))
  refine ⟨a, ?_, ?_⟩
  · have h := hroot
    simp only [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C] at h
    exact sub_eq_zero.mp h
  · rw [← ha₀, ← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
    exact hsub

def charOfRoots (A : ValuationSubring (AlgebraicClosure ℚ)) (t m : ℕ) [NeZero m] (ζ : Fin t → ↥A) (hζ : ∀ j, ζ j ^ m = 1) :
    muCoord ↥A t m →ₐ[↥A] ↥A :=
  AddMonoidAlgebra.lift ↥A ↥A (Fin t → ZMod m)
    { toFun := fun g => ∏ j, ζ j ^ (g.toAdd j).val
      map_one' := by simp
      map_mul' := fun g g' => by
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl (fun j _ => ?_)
        rw [← pow_add, toAdd_mul, Pi.add_apply, ZMod.val_add, pow_mod_of_pow_eq_one (hζ j)] }

omit [NeZero N₀] [Fact (Nat.Prime p)] [NeZero p] in
theorem charOfRoots_single (t m : ℕ) [NeZero m] (ζ : Fin t → ↥A) (hζ : ∀ j, ζ j ^ m = 1) (g : Fin t → ZMod m) :
    charOfRoots A t m ζ hζ (AddMonoidAlgebra.single g 1) = ∏ j, ζ j ^ (g j).val := by
  rw [charOfRoots]
  erw [AddMonoidAlgebra.lift_single]
  rw [one_smul]
  rfl

section grp
variable {R : Type} [CommRing R] {X T : Scheme.{0}} {f : X ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
  (t : T ⟶ Spec (CommRingCat.of R))

omit [NeZero N₀] [Fact (Nat.Prime p)] [NeZero p] in
theorem inv_unique (a b : SchemeHomOver t f) (h : L.mul t b a = L.one t) : b = L.inv t a := by
  calc b = L.mul t b (L.one t) := (L.mul_one t b).symm
    _ = L.mul t b (L.mul t a (L.inv t a)) := by rw [L.mul_inv_cancel]
    _ = L.mul t (L.mul t b a) (L.inv t a) := by rw [L.mul_assoc]
    _ = L.inv t a := by rw [h, L.one_mul]

omit [NeZero N₀] [Fact (Nat.Prime p)] [NeZero p] in
theorem eq_of_mul_inv_eq_one (a b : SchemeHomOver t f) (h : L.mul t a (L.inv t b) = L.one t) : a = b := by
  calc a = L.mul t a (L.one t) := (L.mul_one t a).symm
    _ = L.mul t a (L.mul t (L.inv t b) b) := by rw [L.inv_mul_cancel]
    _ = L.mul t (L.mul t a (L.inv t b)) b := by rw [L.mul_assoc]
    _ = b := by rw [h, L.one_mul]

omit [NeZero N₀] [Fact (Nat.Prime p)] [NeZero p] in
theorem inv_one : L.inv t (L.one t) = L.one t :=
  (inv_unique L t _ _ (L.mul_one t _)).symm

omit [NeZero N₀] [Fact (Nat.Prime p)] [NeZero p] in
theorem nsmul_mul_of_comm (hc : L.IsCommutative) (n : ℕ) (a b : SchemeHomOver t f) :
    L.nsmul t n (L.mul t a b) = L.mul t (L.nsmul t n a) (L.nsmul t n b) := by
  induction n with
  | zero => simp only [RelativeGroupLaw.nsmul_zero, L.one_mul]
  | succ n ih =>
      simp only [RelativeGroupLaw.nsmul_succ, ih]

      rw [L.mul_assoc, ← L.mul_assoc _ (L.nsmul t n b) a b, hc.mul_comm _ (L.nsmul t n b) a, L.mul_assoc, ← L.mul_assoc]

omit [NeZero N₀] [Fact (Nat.Prime p)] [NeZero p] in
theorem nsmul_inv_of_comm (hc : L.IsCommutative) (n : ℕ) (a : SchemeHomOver t f) :
    L.nsmul t n (L.inv t a) = L.inv t (L.nsmul t n a) := by
  apply inv_unique
  rw [← nsmul_mul_of_comm L t hc, L.inv_mul_cancel, RelativeGroupLaw.nsmul_unit]

omit [NeZero N₀] [Fact (Nat.Prime p)] [NeZero p] in
theorem inv_natural {T' : Scheme.{0}} (t' : T' ⟶ Spec (CommRingCat.of R)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t')
    (a : SchemeHomOver t f) :
    GoodReductionJacobian.schemeHomOverComp ψ hψ (L.inv t a) = L.inv t' (GoodReductionJacobian.schemeHomOverComp ψ hψ a) := by
  apply inv_unique
  rw [← L.mul_natural, L.inv_mul_cancel, L.one_natural]

end grp

section fib
variable {R R' : Type} [CommRing R] [CommRing R'] {X : Scheme.{0}}
    {ι : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R)} {f : X ⟶ Spec (CommRingCat.of R)}

omit [NeZero N₀] [Fact (Nat.Prime p)] [NeZero p] in
theorem ofFibrePt_toFibrePt (x : SchemeHomOver ι f) : ofFibrePt (toFibrePt x) = x := by
  apply Subtype.ext
  show (RelativeGroupLaw.baseChangePointToBase ι (RelativeGroupLaw.baseChangePointOfBase ι (overId x))).1 = x.1
  rw [RelativeGroupLaw.baseChangePointToBase_ofBase]
  rfl

omit [NeZero N₀] [Fact (Nat.Prime p)] [NeZero p] in
theorem toFibrePt_ofFibrePt (y : SchemeHomOver (𝟙 _) (RelativeGroupLaw.baseChangeStr ι f)) : toFibrePt (ofFibrePt y) = y := by
  apply Subtype.ext
  apply pullback.hom_ext
  · show pullback.lift (ofFibrePt y).1 (𝟙 _) _ ≫ pullback.fst _ _ = y.1 ≫ pullback.fst _ _
    rw [pullback.lift_fst]
    rfl
  · show pullback.lift (ofFibrePt y).1 (𝟙 _) _ ≫ pullback.snd _ _ = y.1 ≫ pullback.snd _ _
    rw [pullback.lift_snd]
    exact y.2.symm

omit [NeZero N₀] [Fact (Nat.Prime p)] [NeZero p] in
theorem toFibrePt_injective : Function.Injective (toFibrePt (ι := ι) (f := f)) := fun x y h => by
  rw [← ofFibrePt_toFibrePt x, ← ofFibrePt_toFibrePt y, h]

omit [NeZero N₀] [Fact (Nat.Prime p)] [NeZero p] in
theorem toFibrePt_one (L : RelativeGroupLaw R f) : toFibrePt (L.one ι) = (L.baseChange ι).one (𝟙 _) := by
  rw [← ofFibrePt_one L, toFibrePt_ofFibrePt]

omit [NeZero N₀] [Fact (Nat.Prime p)] [NeZero p] in
theorem toFibrePt_mul (L : RelativeGroupLaw R f) (u v : SchemeHomOver ι f) :
    toFibrePt (L.mul ι u v) = (L.baseChange ι).mul (𝟙 _) (toFibrePt u) (toFibrePt v) := by
  rw [RelativeGroupLaw.baseChange_mul]
  show RelativeGroupLaw.baseChangePointOfBase ι (overId (L.mul ι u v)) = _
  rw [toFibrePt, toFibrePt, RelativeGroupLaw.baseChangePointToBase_ofBase, RelativeGroupLaw.baseChangePointToBase_ofBase,
    overId_eq_castOver, overId_eq_castOver, overId_eq_castOver, mul_castOver]

omit [NeZero N₀] [Fact (Nat.Prime p)] [NeZero p] in
theorem toFibrePt_nsmul (L : RelativeGroupLaw R f) (n : ℕ) (u : SchemeHomOver ι f) :
    toFibrePt (L.nsmul ι n u) = (L.baseChange ι).nsmul (𝟙 _) n (toFibrePt u) := by
  induction n with
  | zero => rw [RelativeGroupLaw.nsmul_zero, RelativeGroupLaw.nsmul_zero, toFibrePt_one]
  | succ n ih => rw [RelativeGroupLaw.nsmul_succ, RelativeGroupLaw.nsmul_succ, toFibrePt_mul, ih]

end fib

section torus
variable (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ)

def torPt (ψ : WithConv (torusCoord (ResidueField ↥A) O.toricRank →ₐ[ResidueField ↥A] ResidueField ↥A)) :
    SchemeHomOver (𝟙 _) (RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) O.g) :=
  NeronModelInfra.schemeHomOverComp (torusPt _ _ ψ.ofConv) O.torusFibre

theorem torPt_mul (ψ ψ' : WithConv (torusCoord (ResidueField ↥A) O.toricRank →ₐ[ResidueField ↥A] ResidueField ↥A)) :
    torPt O (ψ * ψ') = (O.L.baseChange (resPt A ≫ Λ.σA)).mul _ (torPt O ψ) (torPt O ψ') :=
  O.torusFibre_mul ψ ψ'

theorem torPt_one : torPt O 1 = (O.L.baseChange (resPt A ≫ Λ.σA)).one _ :=
  eq_one_of_mul_self _ _ _ (by rw [← torPt_mul, mul_one])

theorem torPt_pow (ψ : WithConv (torusCoord (ResidueField ↥A) O.toricRank →ₐ[ResidueField ↥A] ResidueField ↥A)) (k : ℕ) :
    torPt O (ψ ^ k) = (O.L.baseChange (resPt A ≫ Λ.σA)).nsmul _ k (torPt O ψ) := by
  induction k with
  | zero => rw [pow_zero, torPt_one, RelativeGroupLaw.nsmul_zero]
  | succ k ih => rw [pow_succ, torPt_mul, ih, RelativeGroupLaw.nsmul_succ]

theorem torPt_injective : Function.Injective (torPt O) := by
  intro ψ ψ' h
  haveI : IsClosedImmersion O.torusFibre.1 := O.torusFibre_isClosedImmersion
  have h1 : (torusPt _ _ ψ.ofConv).1 ≫ O.torusFibre.1 = (torusPt _ _ ψ'.ofConv).1 ≫ O.torusFibre.1 := congrArg Subtype.val h
  have h2 : (torusPt _ _ ψ.ofConv).1 = (torusPt _ _ ψ'.ofConv).1 := (cancel_mono O.torusFibre.1).mp h1
  have h3 : CommRingCat.ofHom ψ.ofConv.toRingHom = CommRingCat.ofHom ψ'.ofConv.toRingHom := Spec.map_injective h2
  have h4 : ψ.ofConv.toRingHom = ψ'.ofConv.toRingHom := congrArg (fun g => g.hom) h3
  have h5 : ψ.ofConv = ψ'.ofConv := AlgHom.ext (fun z => RingHom.congr_fun h4 z)
  exact congrArg WithConv.toConv h5

theorem exists_eq_torusPt (y : SchemeHomOver (𝟙 _) (torusStr (ResidueField ↥A) O.toricRank)) :
    ∃ ψ : torusCoord (ResidueField ↥A) O.toricRank →ₐ[ResidueField ↥A] ResidueField ↥A, y = torusPt _ _ ψ := by
  let r : CommRingCat.of (torusCoord (ResidueField ↥A) O.toricRank) ⟶ CommRingCat.of (ResidueField ↥A) := Spec.preimage y.1
  have hr : Spec.map r = y.1 := Spec.map_preimage y.1
  have hcomm : r.hom.comp (algebraMap (ResidueField ↥A) (torusCoord (ResidueField ↥A) O.toricRank)) = RingHom.id _ := by
    have h2 := y.2
    rw [← hr] at h2
    change Spec.map r ≫ Spec.map _ = 𝟙 _ at h2
    rw [← Spec.map_comp, ← Spec.map_id] at h2
    have h3 := Spec.map_injective h2
    exact congrArg (fun g => g.hom) h3
  refine ⟨{ r.hom with commutes' := fun a => by simpa using congr($hcomm a) }, Subtype.ext ?_⟩
  rw [← hr]
  rfl

end torus

abbrev piMod (t m : ℕ) : (Fin t → ℤ) →+ (Fin t → ZMod m) :=
  AddMonoidHom.pi fun i => (Int.castAddHom (ZMod m)).comp (Pi.evalAddMonoidHom (fun _ : Fin t => ℤ) i)

omit [NeZero N₀] [Fact (Nat.Prime p)] [NeZero p] in
theorem piMod_single (t m : ℕ) (j : Fin t) : piMod t m (Pi.single j 1) = Pi.single j 1 := by
  ext i
  simp only [piMod, AddMonoidHom.pi_apply, AddMonoidHom.coe_comp, Function.comp_apply, Pi.evalAddMonoidHom_apply,
    Int.coe_castAddHom, Pi.single_apply]
  split_ifs <;> simp

omit [NeZero N₀] [Fact (Nat.Prime p)] [NeZero p] in

theorem torusCoord_algHom_ext {S : Type} [CommRing S] {t : ℕ} {φ₁ φ₂ : torusCoord S t →ₐ[S] S}
    (h : ∀ j : Fin t, φ₁ (AddMonoidAlgebra.single (Pi.single j 1) 1) = φ₂ (AddMonoidAlgebra.single (Pi.single j 1) 1)) :
    φ₁ = φ₂ := by

  let F : (torusCoord S t →ₐ[S] S) → ((Fin t → ℤ) →+ Additive S) := fun φ =>
    (MonoidHom.toAdditive ((φ : torusCoord S t →* S).comp (AddMonoidAlgebra.of S (Fin t → ℤ)))).comp
      (AddMonoidHom.id _ : (Fin t → ℤ) →+ Additive (Multiplicative (Fin t → ℤ)))
  have hF : ∀ φ : torusCoord S t →ₐ[S] S, ∀ v : Fin t → ℤ,
      Additive.toMul (F φ v) = φ (AddMonoidAlgebra.single v 1) := fun φ v => rfl
  have key : F φ₁ = F φ₂ := by
    apply AddMonoidHom.functions_ext
    intro j
    suffices hj : (F φ₁).comp (AddMonoidHom.single (fun _ : Fin t => ℤ) j) = (F φ₂).comp (AddMonoidHom.single _ j) by
      intro n; exact congr($hj n)
    apply AddMonoidHom.ext_int
    apply Additive.toMul.injective
    show Additive.toMul (F φ₁ (Pi.single j 1)) = Additive.toMul (F φ₂ (Pi.single j 1))
    rw [hF, hF]
    exact h j
  refine AddMonoidAlgebra.algHom_ext ?_ (Subsingleton.elim _ _)
  intro v
  have := congr($key v)
  rw [← hF φ₁ v, ← hF φ₂ v, this]

section lift
variable (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ)

theorem redChar_charOfRoots_comp {m : ℕ} [NeZero m] (ψ : torusCoord (ResidueField ↥A) O.toricRank →ₐ[ResidueField ↥A] ResidueField ↥A)
    (ζ : Fin O.toricRank → ↥A) (hζ : ∀ j, ζ j ^ m = 1)
    (hζψ : ∀ j, residue ↥A (ζ j) = ψ (AddMonoidAlgebra.single (Pi.single j 1) 1))
    (hψm : ∀ j, ψ (AddMonoidAlgebra.single (Pi.single j 1) 1) ^ m = 1) :
    (redChar A O.toricRank m (charOfRoots A O.toricRank m ζ hζ)).comp
        (AddMonoidAlgebra.mapDomainAlgHom (ResidueField ↥A) (ResidueField ↥A) (piMod O.toricRank m)) = ψ := by
  apply torusCoord_algHom_ext
  intro j
  rw [AlgHom.comp_apply, AddMonoidAlgebra.mapDomainAlgHom_apply, AddMonoidAlgebra.mapDomain_single]
  change redChar A O.toricRank m _ (AddMonoidAlgebra.single (piMod O.toricRank m (Pi.single j 1)) 1) = _
  rw [piMod_single, redChar_single, charOfRoots_single]
  rw [Finset.prod_eq_single j (fun i _ hij => by rw [Pi.single_apply, if_neg hij, ZMod.val_zero, pow_zero])
    (fun hj => absurd (Finset.mem_univ j) hj)]
  rw [Pi.single_eq_same, map_pow, hζψ, ZMod.val_one_eq_one_mod, pow_mod_of_pow_eq_one (hψm j), pow_one]

theorem torusPtRed_charOfRoots {m : ℕ} [NeZero m] (ψ : torusCoord (ResidueField ↥A) O.toricRank →ₐ[ResidueField ↥A] ResidueField ↥A)
    (ζ : Fin O.toricRank → ↥A) (hζ : ∀ j, ζ j ^ m = 1)
    (hζψ : ∀ j, residue ↥A (ζ j) = ψ (AddMonoidAlgebra.single (Pi.single j 1) 1))
    (hψm : ∀ j, ψ (AddMonoidAlgebra.single (Pi.single j 1) 1) ^ m = 1) :
    torusPtRed O (charOfRoots A O.toricRank m ζ hζ) = torusPt _ _ ψ := by
  apply Subtype.ext
  show Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  have h := congrArg AlgHom.toRingHom (redChar_charOfRoots_comp O ψ ζ hζ hζψ hψm)
  exact h

end lift

section totoric

variable (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ)
  (abq : ∀ m : ℕ, m.Coprime p → (↥(O.finPts m) →+ (JZero N₀ × JZero N₀)))
  (hformula : ∀ (m : ℕ) (hm : m.Coprime p) (x : ↥(O.finPts m)) (s : SchemeHomOver Λ.σA O.g),
    (O.pts (x : JZero (N₀ * p))).1 = barPt A ≫ s.1 →
      reductionModL A N₀ (abq m hm x).1 =
        Λ.ptsSp.symm (fibreMap (O.abqFibre 0)
          (GoodReductionJacobian.schemeHomOverComp (resPt A) rfl s)) ∧
      reductionModL A N₀ (abq m hm x).2 =
        Λ.ptsSp.symm (fibreMap (O.abqFibre 1)
          (GoodReductionJacobian.schemeHomOverComp (resPt A) rfl s)))

include hformula in
theorem mem_toricPts_of_abq_eq_zero (hΛ : Λ.IsJacobian) {m : ℕ} (hm : m.Coprime p) (x : ↥(O.finPts m))
    (h0 : abq m hm x = 0) : (x : JZero (N₀ * p)) ∈ O.toricPts m := by
  haveI : NeZero m := neZero_of_coprime hm
  have hm0 := pos_of_coprime hm
  have hpm : ¬ p ∣ m := fun h => by
    have h1 : p ∣ Nat.gcd m p := Nat.dvd_gcd h (dvd_refl p)
    rw [hm] at h1
    exact (Fact.out : p.Prime).one_lt.ne' (Nat.dvd_one.mp h1)

  obtain ⟨hxt, s, hs⟩ := (mem_finPts_iff O m (x : JZero (N₀ * p))).mp x.2
  have hxm : m • (x : JZero (N₀ * p)) = 0 := by
    have h2 := (Submodule.mem_torsionBy_iff _ _).mp hxt
    rwa [natCast_zsmul] at h2

  obtain ⟨hf0, hf1⟩ := hformula m hm x s hs
  rw [h0] at hf0 hf1
  simp only [Prod.fst_zero, Prod.snd_zero, map_zero] at hf0 hf1
  have hone : ∀ i : Fin 2, NeronModelInfra.schemeHomOverComp (toFibrePt (GoodReductionJacobian.schemeHomOverComp (resPt A) rfl s)) (O.abqFibre i) = (Λ.L.baseChange (resPt A ≫ Λ.σA)).one (𝟙 _) := by
    have e0 : fibreMap (O.abqFibre 0) (GoodReductionJacobian.schemeHomOverComp (resPt A) rfl s) = Λ.L.one (resPt A ≫ Λ.σA) := by
      rw [← ptsSp_zero hΛ]; exact (Λ.ptsSp.symm_apply_eq.mp hf0.symm)
    have e1 : fibreMap (O.abqFibre 1) (GoodReductionJacobian.schemeHomOverComp (resPt A) rfl s) = Λ.L.one (resPt A ≫ Λ.σA) := by
      rw [← ptsSp_zero hΛ]; exact (Λ.ptsSp.symm_apply_eq.mp hf1.symm)
    intro i
    fin_cases i
    · have := congrArg toFibrePt e0
      rwa [fibreMap, toFibrePt_ofFibrePt, toFibrePt_one] at this
    · have := congrArg toFibrePt e1
      rwa [fibreMap, toFibrePt_ofFibrePt, toFibrePt_one] at this

  obtain ⟨y, hy⟩ := (O.abqFibre_eq_one_iff (𝟙 _) (toFibrePt (GoodReductionJacobian.schemeHomOverComp (resPt A) rfl s))).mp hone
  obtain ⟨ψ, rfl⟩ := exists_eq_torusPt O y
  change torPt O (WithConv.toConv ψ) = toFibrePt (GoodReductionJacobian.schemeHomOverComp (resPt A) rfl s) at hy

  have hs_tors : O.L.nsmul Λ.σA m s = O.L.one Λ.σA := nsmul_eq_one_of_ext O _ hxm s hs
  have hr_tors : O.L.nsmul (resPt A ≫ Λ.σA) m (GoodReductionJacobian.schemeHomOverComp (resPt A) rfl s) = O.L.one (resPt A ≫ Λ.σA) := by
    rw [← O.L.nsmul_natural Λ.σA _ (resPt A) rfl m s, hs_tors, O.L.one_natural]
  have hψm : (WithConv.toConv ψ) ^ m = 1 := by
    apply torPt_injective O
    rw [torPt_pow, hy, ← toFibrePt_nsmul, hr_tors, toFibrePt_one, torPt_one]
  have huj : ∀ j : Fin O.toricRank, ψ (AddMonoidAlgebra.single (Pi.single j 1) 1) ^ m = 1 := by
    intro j
    have := congrArg (fun χ : WithConv (torusCoord (ResidueField ↥A) O.toricRank →ₐ[ResidueField ↥A] ResidueField ↥A) =>
      χ.ofConv (AddMonoidAlgebra.single (Pi.single j (1 : ℤ)) 1)) hψm
    simpa only [convPow_single, convOne_single] using this

  have hlift := fun j => exists_pow_eq_one_and_residue_eq hA hm0 hpm _ (huj j)
  choose ζ hζ hζψ using hlift
  let χA := charOfRoots A O.toricRank m ζ hζ

  have hred : GoodReductionJacobian.schemeHomOverComp (resPt A) rfl (toricExt O hm0 χA) =
      GoodReductionJacobian.schemeHomOverComp (resPt A) rfl s := by
    apply toFibrePt_injective
    rw [toFibrePt_red_toricExt, torusPtRed_charOfRoots O ψ ζ hζ hζψ huj, ← hy]
    rfl

  let χ' : muCoord ↥A O.toricRank m →ₐ[↥A] AlgebraicClosure ℚ := (Algebra.ofId ↥A (AlgebraicClosure ℚ)).comp χA
  have hχ' : ∀ z, ((χA z : ↥A) : AlgebraicClosure ℚ) = χ' z := fun z => rfl
  have ht_tors : O.L.nsmul Λ.σA m (toricExt O hm0 χA) = O.L.one Λ.σA := by
    refine nsmul_eq_one_of_ext O (O.toricPoint m hm0 χ') ?_ _ ?_
    · have hmem : O.toricPoint m hm0 χ' ∈ O.finPts m :=
        toricPts_le_finPts O m ((toricPts_of_pos O hm0).symm ▸ AddSubgroup.subset_closure ⟨χ', rfl⟩)
      have h2 := (Submodule.mem_torsionBy_iff _ _).mp ((mem_finPts_iff O m _).mp hmem).1
      rwa [natCast_zsmul] at h2
    · rw [pts_toricPoint_coe, barPt_toricExt O hm0 χA χ' hχ']
  have heq : s = toricExt O hm0 χA := by
    haveI : LocallyOfFiniteType O.g := O.locallyOfFiniteType
    apply eq_of_mul_inv_eq_one O.L
    refine GoodReductionJacobian.RelativeGroupLaw.eq_one_of_isTorsionPoint_of_comp_residue_eq O.L O.comm Λ.σA m
      (isUnit_natCast_of_not_dvd hA hpm) _ ?_ ?_
    · show O.L.nsmul Λ.σA m _ = O.L.one Λ.σA
      rw [nsmul_mul_of_comm O.L _ O.comm, nsmul_inv_of_comm O.L _ O.comm, hs_tors, ht_tors, inv_one, O.L.one_mul]
    · rw [O.L.mul_natural, inv_natural, hred, O.L.mul_inv_cancel, O.L.one_natural]

  have hpts : O.pts (x : JZero (N₀ * p)) = O.pts (O.toricPoint m hm0 χ') := by
    apply Subtype.ext
    rw [hs, heq, barPt_toricExt O hm0 χA χ' hχ', pts_toricPoint_coe]
  rw [O.pts.injective hpts, toricPts_of_pos O hm0]
  exact AddSubgroup.subset_closure ⟨χ', rfl⟩

end totoric

end ABQK

open ABQK in
theorem solution
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (Λ : JZeroNeronObjectAtP.LevelData N₀ p A) (hΛ : Λ.IsJacobian)
    (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ)
    (abq : ∀ m : ℕ, m.Coprime p → (↥(O.finPts m) →+ (JZero N₀ × JZero N₀)))
    (habq : ∀ (m : ℕ) (hm : m.Coprime p) (x : ↥(O.finPts m)),
      abq m hm x ∈ Submodule.torsionBy ℤ (JZero N₀ × JZero N₀) (m : ℤ))
    (hformula : ∀ (m : ℕ) (hm : m.Coprime p) (x : ↥(O.finPts m)) (s : SchemeHomOver Λ.σA O.g),
      (O.pts (x : JZero (N₀ * p))).1 = barPt A ≫ s.1 →
        reductionModL A N₀ (abq m hm x).1 =
          Λ.ptsSp.symm (fibreMap (O.abqFibre 0)
            (GoodReductionJacobian.schemeHomOverComp (resPt A) rfl s)) ∧
        reductionModL A N₀ (abq m hm x).2 =
          Λ.ptsSp.symm (fibreMap (O.abqFibre 1)
            (GoodReductionJacobian.schemeHomOverComp (resPt A) rfl s)))
    (m : ℕ) (hm : m.Coprime p) (x : ↥(O.finPts m)) :
    abq m hm x = 0 ↔ (x : JZero (N₀ * p)) ∈ O.toricPts m :=
  ⟨mem_toricPts_of_abq_eq_zero O abq hformula hΛ hm x, abq_eq_zero_of_mem_toricPts O abq habq hformula hΛ hm x⟩

end

end S_ModularCurve_JZeroNeronObjectAtP_abq_eq_zero_iff_mem_toricPts_of_forall_reductionModL_eq
end P2MW
export P2MW.S_ModularCurve_JZeroNeronObjectAtP_abq_eq_zero_iff_mem_toricPts_of_forall_reductionModL_eq (solution)
