-- Prove2me | solution 1 for ModularCurve.JZeroNeronObjectAtP.abq_smul_of_mem_decompositionSubgroup_of_forall_reductionModL_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/a565b257-d63a-5b92-9d6b-a49ba72ddb42

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_ModularCurve_JZeroNeronAtPData
import Definitions.Def_AlgebraicCurve_Repartitions
import Theorems.Thm_ModularCurve_reductionInputsModL_of_not_dvd
import Theorems.Thm_ModularCurve_eq_zero_of_reductionModL_eq_zero_of_nsmul_eq_zero
import Theorems.Thm_ModularCurve_JZeroNeronObjectAtP_mem_finPts_iff
import Theorems.Thm_AlgebraicGeometry_SchemeHomOver_ext_of_forall_algebraicClosure_point_of_isReduced_of_flat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JZeroNeronObjectAtP_abq_smul_of_mem_decompositionSubgroup_of_forall_reductionModL_eq
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular CuspForm.heckeAlgebra.instCommRing CuspForm.heckeAlgebra.instIsMulCommutative CuspForm.heckeAlgebra.instIsAddTorsionFree ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par HeckeEis.instFiniteIndexHeckeUpper"
p2m_attr_erase "simp" "AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply"
p2m_attr_erase "simp" "AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularCurve.cuspCount_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule HahnSeries.ramScale_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx"
p2m_attr_erase "simp" "WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right"
p2m_attr_erase "simp" "FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.dualHeckeRep_apply_apply ModularCurve.coe_segmentPath ModularCurve.cuspHeckeAeval_heckeGen ModularCurve.coe_periodLatticeRestrict_apply CuspForm.heckeAlgebra.coe_U CuspForm.heckeAlgebra.coe_T ModularForm.coe_heckeTLin_apply CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply ModularForm.coe_heckeULin_apply ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff"
p2m_attr_erase "simp" "FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero HeckeEis.coeffCoboundaryMap_apply HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero"

set_option autoImplicit false

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve IsLocalRing AlgebraicCurve ModularCurve.JZeroNeronObjectAtP

noncomputable section

namespace ABQD

variable {N₀ p : ℕ} [NeZero N₀] [Fact p.Prime] [NeZero p] {hpN₀ : ¬ p ∣ N₀}
  {A : ValuationSubring (AlgebraicClosure ℚ)} {hA : A.LiesOverPrime p} {Λ : LevelData N₀ p A}

abbrev sigA (A : ValuationSubring (AlgebraicClosure ℚ)) (σ : ↥(A.decompositionSubgroup ℚ)) : ↥A ≃+* ↥A :=
  MulSemiringAction.toRingAut _ ↥A σ

abbrev sigK (A : ValuationSubring (AlgebraicClosure ℚ)) (σ : ↥(A.decompositionSubgroup ℚ)) :
    ResidueField ↥A ≃+* ResidueField ↥A :=
  MulSemiringAction.toRingAut _ (ResidueField ↥A) σ

abbrev specSigA (A : ValuationSubring (AlgebraicClosure ℚ)) (σ : ↥(A.decompositionSubgroup ℚ)) :
    Spec (CommRingCat.of ↥A) ⟶ Spec (CommRingCat.of ↥A) :=
  Spec.map (CommRingCat.ofHom (sigA A σ).toRingHom)

abbrev specSigK (A : ValuationSubring (AlgebraicClosure ℚ)) (σ : ↥(A.decompositionSubgroup ℚ)) :
    Spec (CommRingCat.of (ResidueField ↥A)) ⟶ Spec (CommRingCat.of (ResidueField ↥A)) :=
  Spec.map (CommRingCat.ofHom (sigK A σ).toRingHom)

omit [NeZero N₀] [Fact (Nat.Prime p)] [NeZero p] in
theorem barPt_specSigA (σ : ↥(A.decompositionSubgroup ℚ)) :
    barPt A ≫ specSigA A σ =
      Spec.map (CommRingCat.ofHom ((σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫
        barPt A := by
  show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  rfl

omit [NeZero N₀] [Fact (Nat.Prime p)] [NeZero p] in
theorem resPt_specSigA (σ : ↥(A.decompositionSubgroup ℚ)) :
    resPt A ≫ specSigA A σ = specSigK A σ ≫ resPt A := by
  show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  congr 2

omit [Fact (Nat.Prime p)] in

theorem specSigA_σA (σ : ↥(A.decompositionSubgroup ℚ)) : specSigA A σ ≫ Λ.σA = Λ.σA := by

  let u : CommRingCat.of (baseRing p) ⟶ CommRingCat.of ↥A := Spec.preimage (specSigA A σ ≫ Λ.σA)
  let v : CommRingCat.of (baseRing p) ⟶ CommRingCat.of ↥A := Spec.preimage Λ.σA
  have hu : Spec.map u = specSigA A σ ≫ Λ.σA := Spec.map_preimage _
  have hv : Spec.map v = Λ.σA := Spec.map_preimage _
  have hgen : barPt A ≫ (specSigA A σ ≫ Λ.σA) = barPt A ≫ Λ.σA := by
    rw [← Category.assoc, barPt_specSigA, Category.assoc, Λ.hσA]
    show Spec.map _ ≫ Spec.map _ = _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext r
    show (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (algebraMap (baseRing p) (AlgebraicClosure ℚ) r) = algebraMap _ _ r
    have hr : algebraMap (baseRing p) (AlgebraicClosure ℚ) r = algebraMap ℚ (AlgebraicClosure ℚ) (r : ℚ) := rfl
    rw [hr, AlgEquiv.commutes]
  rw [← hu, ← hv] at hgen
  change Spec.map (CommRingCat.ofHom A.subtype) ≫ Spec.map u = Spec.map (CommRingCat.ofHom A.subtype) ≫ Spec.map v at hgen
  rw [← Spec.map_comp, ← Spec.map_comp] at hgen
  have h2 := Spec.map_injective hgen
  have h3 : u = v := by
    ext r
    have h2' : (u ≫ CommRingCat.ofHom A.subtype).hom r = (v ≫ CommRingCat.ofHom A.subtype).hom r := by rw [h2]
    first | exact h2' | exact Subtype.val_injective h2' | exact congrArg Subtype.val h2'
  rw [← hu, ← hv, h3]

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
    have hz : z.1 = barPt A := by have h__af := z.2; simp at h__af; exact h__af
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

def tauK (Λ : LevelData N₀ p A) (σ : ↥(A.decompositionSubgroup ℚ)) : SchemeHomOver (resPt A ≫ Λ.σA) (resPt A ≫ Λ.σA) :=
  ⟨specSigK A σ, by rw [← Category.assoc, ← resPt_specSigA, Category.assoc, specSigA_σA]⟩

def twistA (Λ : LevelData N₀ p A) {X : Scheme.{0}} {f : X ⟶ base p} (σ : ↥(A.decompositionSubgroup ℚ))
    (s : SchemeHomOver Λ.σA f) : SchemeHomOver Λ.σA f :=
  GoodReductionJacobian.schemeHomOverComp (specSigA A σ) (specSigA_σA σ) s

theorem barPt_twistA {X : Scheme.{0}} {f : X ⟶ base p} (σ : ↥(A.decompositionSubgroup ℚ)) (s : SchemeHomOver Λ.σA f) :
    barPt A ≫ (twistA Λ σ s).1 =
      Spec.map (CommRingCat.ofHom ((σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫
        barPt A ≫ s.1 := by
  show barPt A ≫ specSigA A σ ≫ s.1 = _
  rw [← Category.assoc, barPt_specSigA, Category.assoc]

theorem red_twistA {X : Scheme.{0}} {f : X ⟶ base p} (σ : ↥(A.decompositionSubgroup ℚ)) (s : SchemeHomOver Λ.σA f) :
    GoodReductionJacobian.schemeHomOverComp (resPt A) rfl (twistA Λ σ s) =
      GoodReductionJacobian.schemeHomOverComp (tauK Λ σ).1 (tauK Λ σ).2
        (GoodReductionJacobian.schemeHomOverComp (resPt A) rfl s) := by
  apply Subtype.ext
  show resPt A ≫ specSigA A σ ≫ s.1 = specSigK A σ ≫ resPt A ≫ s.1
  rw [← Category.assoc, resPt_specSigA, Category.assoc]

theorem ptsSp_reductionModL_smul (hpN₀ : ¬ p ∣ N₀) (hA : A.LiesOverPrime p) (hΛ : Λ.IsJacobian)
    (σ : ↥(A.decompositionSubgroup ℚ)) (w : JZero N₀) :
    Λ.ptsSp (reductionModL A N₀ ((σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) • w)) =
      GoodReductionJacobian.schemeHomOverComp (tauK Λ σ).1 (tauK Λ σ).2 (Λ.ptsSp (reductionModL A N₀ w)) := by
  have hinp := reductionInputsModL_of_not_dvd N₀ hpN₀ A hA
  have hROP := hΛ.2.2.2.2.2.1 hinp
  have hsep : IsSeparated Λ.f := by
    haveI : IsProper Λ.f := hΛ.1.proper
    infer_instance
  haveI := hsep

  obtain ⟨P, hPgen, hPsp⟩ := hROP w
  obtain ⟨P₀, hP₀gen, hP₀sp⟩ := hROP ((σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) • w)
  have hPgen1 : barPt A ≫ P.1 = (Λ.ptsA w).1 := congrArg Subtype.val hPgen
  have hPsp1 : resPt A ≫ P.1 = (Λ.ptsSp (reductionModL A N₀ w)).1 := congrArg Subtype.val hPsp
  have hP₀gen1 : barPt A ≫ P₀.1 = (Λ.ptsA ((σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) • w)).1 := congrArg Subtype.val hP₀gen
  have hP₀sp1 : resPt A ≫ P₀.1 = (Λ.ptsSp (reductionModL A N₀ ((σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) • w))).1 :=
    congrArg Subtype.val hP₀sp
  have hgen' : barPt A ≫ (twistA Λ σ P).1 = (Λ.ptsA ((σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) • w)).1 := by
    rw [barPt_twistA, hPgen1]
    show _ = (Λ.pts ((σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) • w)).1
    rw [hΛ.2.2.2.1]
    rfl
  have heq : twistA Λ σ P = P₀ := ext_unique_aux _ _ (hgen'.trans hP₀gen1.symm)
  apply Subtype.ext
  rw [← hP₀sp1, ← heq]
  show resPt A ≫ (twistA Λ σ P).1 = specSigK A σ ≫ (Λ.ptsSp (reductionModL A N₀ w)).1
  rw [← hPsp1]
  exact congrArg Subtype.val (red_twistA σ P)

end ABQD

set_option maxHeartbeats 3200000 in
open ABQD in
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
    (m : ℕ) (hm : m.Coprime p) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (hσ : σ ∈ A.decompositionSubgroup ℚ) (x : ↥(O.finPts m))
    (hx : σ • (x : JZero (N₀ * p)) ∈ O.finPts m) :
    abq m hm ⟨_, hx⟩ = (σ • (abq m hm x).1, σ • (abq m hm x).2) := by
  have hinp := reductionInputsModL_of_not_dvd N₀ hpN₀ A hA
  have hpm : ¬ p ∣ m := fun h => by
    have h1 : p ∣ Nat.gcd m p := Nat.dvd_gcd h (dvd_refl p)
    rw [hm] at h1
    exact (Fact.out : p.Prime).one_lt.ne' (Nat.dvd_one.mp h1)
  let σD : ↥(A.decompositionSubgroup ℚ) := ⟨σ, hσ⟩

  obtain ⟨-, s, hs⟩ := (mem_finPts_iff O m (x : JZero (N₀ * p))).mp x.2
  have hs' : (O.pts (σ • (x : JZero (N₀ * p)))).1 = barPt A ≫ (twistA Λ σD s).1 := by
    rw [barPt_twistA, ← hs, O.pts_galois]
  obtain ⟨f0, f1⟩ := hformula m hm x s hs
  obtain ⟨g0, g1⟩ := hformula m hm ⟨_, hx⟩ (twistA Λ σD s) hs'
  rw [red_twistA, O.abqFibre_twist] at g0 g1

  have e0 : reductionModL A N₀ (σ • (abq m hm x).1) = reductionModL A N₀ (abq m hm ⟨_, hx⟩).1 := by
    apply Λ.ptsSp.injective
    have h1 := ptsSp_reductionModL_smul hpN₀ hA hΛ σD (abq m hm x).1
    rw [f0, Equiv.apply_symm_apply] at h1
    have h2 := congrArg Λ.ptsSp g0
    rw [Equiv.apply_symm_apply] at h2
    exact h1.trans h2.symm
  have e1 : reductionModL A N₀ (σ • (abq m hm x).2) = reductionModL A N₀ (abq m hm ⟨_, hx⟩).2 := by
    apply Λ.ptsSp.injective
    have h1 := ptsSp_reductionModL_smul hpN₀ hA hΛ σD (abq m hm x).2
    rw [f1, Equiv.apply_symm_apply] at h1
    have h2 := congrArg Λ.ptsSp g1
    rw [Equiv.apply_symm_apply] at h2
    exact h1.trans h2.symm

  have ht := habq m hm x
  have ht' := habq m hm ⟨_, hx⟩
  rw [Submodule.mem_torsionBy_iff, natCast_zsmul, Prod.ext_iff, Prod.smul_fst, Prod.smul_snd, Prod.fst_zero, Prod.snd_zero] at ht ht'
  have hσt : ∀ w : JZero N₀, m • w = 0 → m • (σ • w) = 0 := fun w hw => by
    have h := map_nsmul (DistribSMul.toAddMonoidHom (JZero N₀) σ) m w
    simp only [DistribSMul.toAddMonoidHom_apply] at h
    rw [← h, hw, smul_zero]
  refine Prod.ext ?_ ?_
  · refine (sub_eq_zero.mp (eq_zero_of_reductionModL_eq_zero_of_nsmul_eq_zero N₀ hpN₀ A hA hinp m hpm _ ?_ ?_))
    · rw [nsmul_sub, ht'.1, hσt _ ht.1, sub_zero]
    · rw [map_sub, e0, sub_self]
  · refine (sub_eq_zero.mp (eq_zero_of_reductionModL_eq_zero_of_nsmul_eq_zero N₀ hpN₀ A hA hinp m hpm _ ?_ ?_))
    · rw [nsmul_sub, ht'.2, hσt _ ht.2, sub_zero]
    · rw [map_sub, e1, sub_self]

end

end S_ModularCurve_JZeroNeronObjectAtP_abq_smul_of_mem_decompositionSubgroup_of_forall_reductionModL_eq
end P2MW
export P2MW.S_ModularCurve_JZeroNeronObjectAtP_abq_smul_of_mem_decompositionSubgroup_of_forall_reductionModL_eq (solution)
