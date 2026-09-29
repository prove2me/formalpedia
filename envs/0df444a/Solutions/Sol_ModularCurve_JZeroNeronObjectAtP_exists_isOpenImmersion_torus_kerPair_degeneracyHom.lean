-- Prove2me | solution 1 for ModularCurve.JZeroNeronObjectAtP.exists_isOpenImmersion_torus_kerPair_degeneracyHom
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/f72a8ca6-f718-5a6a-b764-86eed63619b6

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKerPair

import Theorems.Thm_AlgebraicGeometry_isOpenImmersion_of_isClosedImmersion_of_isReduced_of_finite_index
import Theorems.Thm_AlgebraicGeometry_ext_of_forall_geometricPoint_comp_eq_of_flat
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField_algebraicClosure_rat
import Theorems.Thm_ModularCurve_JZeroNeronObjectAtP_finite_fixedPoints_frobSp_comp_self
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JZeroNeronObjectAtP_exists_isOpenImmersion_torus_kerPair_degeneracyHom
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular CuspForm.heckeAlgebra.instCommRing CuspForm.heckeAlgebra.instIsMulCommutative CuspForm.heckeAlgebra.instIsAddTorsionFree ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par HeckeEis.instFiniteIndexHeckeUpper"
p2m_attr_erase "simp" "ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe"
p2m_attr_erase "simp" "AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.cuspCount_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule HahnSeries.ramScale_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx"
p2m_attr_erase "simp" "WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right"
p2m_attr_erase "simp" "FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.dualHeckeRep_apply_apply ModularCurve.coe_segmentPath ModularCurve.cuspHeckeAeval_heckeGen ModularCurve.coe_periodLatticeRestrict_apply CuspForm.heckeAlgebra.coe_U CuspForm.heckeAlgebra.coe_T ModularForm.coe_heckeTLin_apply CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply ModularForm.coe_heckeULin_apply ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff"
p2m_attr_erase "simp" "FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero HeckeEis.coeffCoboundaryMap_apply HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing ModularCurve ModularCurve.JZeroNeronObjectAtP

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

namespace OPENT

section TorusPoints

variable (S : Type) [CommRing S] (t : ℕ)

theorem exists_torusPt_eq (τ : SchemeHomOver (𝟙 _) (torusStr S t)) :
    ∃ χ : torusCoord S t →ₐ[S] S, torusPt S t χ = τ := by
  let ψ : CommRingCat.of (torusCoord S t) ⟶ CommRingCat.of S := Spec.preimage τ.1
  have hψ : Spec.map ψ = τ.1 := Spec.map_preimage _
  have hcomp : (CommRingCat.ofHom (algebraMap S (torusCoord S t))) ≫ ψ = 𝟙 _ := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_id, hψ]
    exact τ.2
  refine ⟨{ ψ.hom with commutes' := fun r => ?_ }, ?_⟩
  · have := congrArg (fun g : CommRingCat.of S ⟶ CommRingCat.of S => g.hom r) hcomp
    simpa using this
  · apply Subtype.ext
    show Spec.map _ = τ.1
    rw [← hψ]
    rfl

variable {S t}

theorem convMul_single (χ χ' : WithConv (torusCoord S t →ₐ[S] S)) (v : Fin t → ℤ) :
    (χ * χ') (AddMonoidAlgebra.single v 1) = χ (AddMonoidAlgebra.single v 1) * χ' (AddMonoidAlgebra.single v 1) := by
  rw [AlgHom.convMul_apply, AddMonoidAlgebra.comul_single]
  simp [Algebra.TensorProduct.lift_tmul]

theorem convOne_single (v : Fin t → ℤ) :
    (1 : WithConv (torusCoord S t →ₐ[S] S)) (AddMonoidAlgebra.single v 1) = 1 := by
  rw [AlgHom.convOne_apply, AddMonoidAlgebra.counit_single]
  simp

theorem convPow_single (χ : WithConv (torusCoord S t →ₐ[S] S)) (n : ℕ) (v : Fin t → ℤ) :
    (χ ^ n) (AddMonoidAlgebra.single v 1) = χ (AddMonoidAlgebra.single v 1) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, convOne_single]
  | succ n ih => rw [pow_succ, pow_succ, convMul_single, ih]

theorem convPow_ofConv_toRingHom (χ : WithConv (torusCoord S t →ₐ[S] S)) (n : ℕ) :
    (χ ^ n).ofConv.toRingHom =
      χ.ofConv.toRingHom.comp (AddMonoidAlgebra.mapDomainRingHom S (n • AddMonoidHom.id (Fin t → ℤ))) := by
  have h : (χ ^ n).ofConv =
      χ.ofConv.comp (AddMonoidAlgebra.mapDomainAlgHom S S (n • AddMonoidHom.id (Fin t → ℤ))) := by
    refine AddMonoidAlgebra.algHom_ext ?_ (Subsingleton.elim _ _)
    intro v
    rw [AlgHom.comp_apply, AddMonoidAlgebra.mapDomainAlgHom_apply, AddMonoidAlgebra.mapDomain_single]
    show (χ ^ n) (AddMonoidAlgebra.single v 1) = χ.ofConv (AddMonoidAlgebra.single ((n • AddMonoidHom.id _) v) 1)
    rw [convPow_single, AddMonoidHom.smul_apply, AddMonoidHom.id_apply, ← one_pow n,
      ← AddMonoidAlgebra.single_pow, one_pow, map_pow]
  exact congrArg AlgHom.toRingHom h

theorem torusPt_pow_coe (χ : WithConv (torusCoord S t →ₐ[S] S)) (n : ℕ) :
    (torusPt S t (χ ^ n).ofConv).1 =
      (torusPt S t χ.ofConv).1 ≫
        Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapDomainRingHom S (n • AddMonoidHom.id (Fin t → ℤ)))) := by
  show Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← convPow_ofConv_toRingHom]

noncomputable def convInv (χ : WithConv (torusCoord S t →ₐ[S] S)) : WithConv (torusCoord S t →ₐ[S] S) :=
  WithConv.toConv (χ.ofConv.comp (AddMonoidAlgebra.mapDomainAlgHom S S (-AddMonoidHom.id (Fin t → ℤ))))

theorem convMul_convInv (χ : WithConv (torusCoord S t →ₐ[S] S)) : χ * convInv χ = 1 := by
  apply WithConv.ofConv_injective
  refine AddMonoidAlgebra.algHom_ext ?_ (Subsingleton.elim _ _)
  intro v
  show (χ * convInv χ) (AddMonoidAlgebra.single v 1) = (1 : WithConv (torusCoord S t →ₐ[S] S)) (AddMonoidAlgebra.single v 1)
  rw [convMul_single, convOne_single]
  show χ (AddMonoidAlgebra.single v 1) *
      χ.ofConv (AddMonoidAlgebra.mapDomainAlgHom S S (-AddMonoidHom.id (Fin t → ℤ)) (AddMonoidAlgebra.single v 1)) = 1
  rw [AddMonoidAlgebra.mapDomainAlgHom_apply, AddMonoidAlgebra.mapDomain_single]
  show χ.ofConv (AddMonoidAlgebra.single v 1) * χ.ofConv (AddMonoidAlgebra.single (-v) 1) = 1
  rw [← map_mul, AddMonoidAlgebra.single_mul_single, add_neg_cancel, mul_one]
  exact map_one χ.ofConv

end TorusPoints

end OPENT

namespace OPENT

section Generic

universe v

variable {R : Type v} [CommRing R] {X : Scheme.{v}} {f : X ⟶ Spec (CommRingCat.of R)}

theorem comp_schemeNsmul (G : RelativeGroupLaw R f) (n : ℕ) {T : Scheme.{v}} {t : T ⟶ Spec (CommRingCat.of R)}
    (x : SchemeHomOver t f) : x.1 ≫ G.schemeNsmul n = (G.nsmul t n x).1 := by
  have h := G.nsmul_natural f t x.1 x.2 n RelativeGroupLaw.idPoint
  have hx : schemeHomOverComp x.1 x.2 (RelativeGroupLaw.idPoint : SchemeHomOver f f) = x :=
    Subtype.ext (Category.comp_id _)
  rw [hx] at h
  exact (congrArg Subtype.val h)

theorem one_coe_idComp (G : RelativeGroupLaw R f) {T : Scheme.{v}} (c : T ⟶ Spec (CommRingCat.of R)) :
    (G.one (𝟙 T ≫ c)).1 = (G.one c).1 := by
  have h := G.one_natural c (𝟙 T ≫ c) (𝟙 T) rfl
  rw [← h, GoodReductionJacobian.schemeHomOverComp_coe, Category.id_comp]

end Generic

section Fibre

variable {N₀ p : ℕ} [NeZero N₀] [Fact p.Prime] [NeZero p] {hpN₀ : ¬ p ∣ N₀}
  {A : ValuationSubring (AlgebraicClosure ℚ)} {hA : A.LiesOverPrime p}
  {Λ : JZeroNeronObjectAtP.LevelData N₀ p A} (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ)

noncomputable abbrev Lκ : RelativeGroupLaw (ResidueField ↥A) (RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) O.g) :=
  O.L.baseChange (resPt A ≫ Λ.σA)

noncomputable abbrev dκ (i : Fin 2) :
    SchemeHomOver (RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) O.g)
      (RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) Λ.f) :=
  NeronSpecialFibreInfra.fibreRestrictAlong (resPt A ≫ Λ.σA) Λ.f O.g (O.degeneracyHom i)

theorem dκ_isHom (i : Fin 2) : RelativeGroupLaw.IsHom (Lκ O) (Λ.L.baseChange (resPt A ≫ Λ.σA)) (dκ O i) :=
  RelativeGroupLaw.IsHom.fibreRestrictAlong (resPt A ≫ Λ.σA) (fun t x y => O.degeneracyHom_mul i t x y)

noncomputable abbrev Hκ : Scheme.{0} := RelativeGroupLaw.kerPair (Λ.L.baseChange (resPt A ≫ Λ.σA)) (dκ O)

noncomputable abbrev HκStr : Hκ O ⟶ Spec (CommRingCat.of (ResidueField ↥A)) :=
  RelativeGroupLaw.kerPairStr (Λ.L.baseChange (resPt A ≫ Λ.σA)) (dκ O)

noncomputable abbrev LH : RelativeGroupLaw (ResidueField ↥A) (HκStr O) :=
  RelativeGroupLaw.kerPairLaw (Lκ O) (Λ.L.baseChange (resPt A ≫ Λ.σA)) (dκ O) (dκ_isHom O)

noncomputable abbrev eqv {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (ResidueField ↥A))) :=
  RelativeGroupLaw.kerPairPointEquiv (Λ.L.baseChange (resPt A ≫ Λ.σA)) (dκ O) t

noncomputable abbrev tpt (χ : WithConv (torusCoord (ResidueField ↥A) O.toricRank →ₐ[ResidueField ↥A] ResidueField ↥A)) :
    SchemeHomOver (𝟙 _) (RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) O.g) :=
  NeronModelInfra.schemeHomOverComp (torusPt _ _ χ.ofConv) O.torusFibre

theorem tpt_mul (χ χ' : WithConv (torusCoord (ResidueField ↥A) O.toricRank →ₐ[ResidueField ↥A] ResidueField ↥A)) :
    tpt O (χ * χ') = (Lκ O).mul (𝟙 _) (tpt O χ) (tpt O χ') :=
  O.torusFibre_mul χ χ'

theorem tpt_one : tpt O 1 = (Lκ O).one (𝟙 _) := by
  letI := (Lκ O).pointGroup (𝟙 (Spec (CommRingCat.of (ResidueField ↥A))))
  have h := tpt_mul O 1 1
  rw [one_mul] at h
  exact mul_eq_left.mp h.symm

theorem tpt_inv (χ : WithConv (torusCoord (ResidueField ↥A) O.toricRank →ₐ[ResidueField ↥A] ResidueField ↥A)) :
    (Lκ O).inv (𝟙 _) (tpt O χ) = tpt O (convInv χ) := by
  letI := (Lκ O).pointGroup (𝟙 (Spec (CommRingCat.of (ResidueField ↥A))))
  have h : tpt O χ * tpt O (convInv χ) = 1 := by
    show (Lκ O).mul _ _ _ = (Lκ O).one _
    rw [← tpt_mul, convMul_convInv, tpt_one]
  exact (eq_inv_of_mul_eq_one_right h).symm

theorem tpt_pow (χ : WithConv (torusCoord (ResidueField ↥A) O.toricRank →ₐ[ResidueField ↥A] ResidueField ↥A)) (n : ℕ) :
    (Lκ O).nsmul (𝟙 _) n (tpt O χ) = tpt O (χ ^ n) := by
  induction n with
  | zero => rw [RelativeGroupLaw.nsmul_zero, pow_zero, tpt_one]
  | succ n ih => rw [RelativeGroupLaw.nsmul_succ, ih, pow_succ, tpt_mul]

variable (hι : ∀ i : Fin 2, O.torusFibre.1 ≫
    (NeronSpecialFibreInfra.fibreRestrictAlong (resPt A ≫ Λ.σA) Λ.f O.g (O.degeneracyHom i)).1 =
  torusStr (ResidueField ↥A) O.toricRank ≫ ((Λ.L.baseChange (resPt A ≫ Λ.σA)).one (𝟙 _)).1)

include hι in
theorem torusFibre_mem (i : Fin 2) :
    NeronModelInfra.schemeHomOverComp O.torusFibre (dκ O i) =
      (Λ.L.baseChange (resPt A ≫ Λ.σA)).one (torusStr (ResidueField ↥A) O.toricRank) := by
  apply Subtype.ext
  rw [NeronModelInfra.schemeHomOverComp_coe, RelativeGroupLaw.one_coe_eq]
  exact hι i

noncomputable def ιHOver : SchemeHomOver (torusStr (ResidueField ↥A) O.toricRank) (HκStr O) :=
  (eqv O (torusStr (ResidueField ↥A) O.toricRank)).symm ⟨O.torusFibre, torusFibre_mem O hι⟩

theorem ιH_comp_kerPairι :
    (ιHOver O hι).1 ≫ RelativeGroupLaw.kerPairι (Λ.L.baseChange (resPt A ≫ Λ.σA)) (dκ O) = O.torusFibre.1 :=
  RelativeGroupLaw.kerPairPointEquiv_symm_apply_coe _ _ _ _

theorem ιH_over : (ιHOver O hι).1 ≫ HκStr O = torusStr (ResidueField ↥A) O.toricRank :=
  (ιHOver O hι).2

theorem eqv_torusPoint (τ : SchemeHomOver (𝟙 _) (torusStr (ResidueField ↥A) O.toricRank)) :
    (eqv O (𝟙 _) ⟨τ.1 ≫ (ιHOver O hι).1, by rw [Category.assoc, ιH_over, τ.2]⟩).1 =
      NeronModelInfra.schemeHomOverComp τ O.torusFibre := by
  apply Subtype.ext
  rw [RelativeGroupLaw.kerPairPointEquiv_apply_coe_coe, NeronModelInfra.schemeHomOverComp_coe, Category.assoc,
    ιH_comp_kerPairι]

theorem eq_of_eqv_eq {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of (ResidueField ↥A))}
    {z w : SchemeHomOver t (HκStr O)} (h : (eqv O t z).1 = (eqv O t w).1) : z = w :=
  (eqv O t).injective (Subtype.ext h)

theorem hmul (τ τ' : SchemeHomOver (𝟙 _) (torusStr (ResidueField ↥A) O.toricRank)) :
    ∃ τ'' : SchemeHomOver (𝟙 _) (torusStr (ResidueField ↥A) O.toricRank),
      (LH O).mul (𝟙 _) ⟨τ.1 ≫ (ιHOver O hι).1, by rw [Category.assoc, ιH_over, τ.2]⟩
          ⟨τ'.1 ≫ (ιHOver O hι).1, by rw [Category.assoc, ιH_over, τ'.2]⟩ =
        ⟨τ''.1 ≫ (ιHOver O hι).1, by rw [Category.assoc, ιH_over, τ''.2]⟩ := by
  obtain ⟨χ, rfl⟩ := exists_torusPt_eq _ _ τ
  obtain ⟨χ', rfl⟩ := exists_torusPt_eq _ _ τ'
  refine ⟨torusPt _ _ (WithConv.toConv χ * WithConv.toConv χ').ofConv, ?_⟩
  apply eq_of_eqv_eq O
  rw [RelativeGroupLaw.kerPairPointEquiv_mul, eqv_torusPoint, eqv_torusPoint, eqv_torusPoint]
  exact (tpt_mul O (WithConv.toConv χ) (WithConv.toConv χ')).symm

theorem hinv (τ : SchemeHomOver (𝟙 _) (torusStr (ResidueField ↥A) O.toricRank)) :
    ∃ τ' : SchemeHomOver (𝟙 _) (torusStr (ResidueField ↥A) O.toricRank),
      (LH O).inv (𝟙 _) ⟨τ.1 ≫ (ιHOver O hι).1, by rw [Category.assoc, ιH_over, τ.2]⟩ =
        ⟨τ'.1 ≫ (ιHOver O hι).1, by rw [Category.assoc, ιH_over, τ'.2]⟩ := by
  obtain ⟨χ, rfl⟩ := exists_torusPt_eq _ _ τ
  refine ⟨torusPt _ _ (convInv (WithConv.toConv χ)).ofConv, ?_⟩
  apply eq_of_eqv_eq O
  rw [RelativeGroupLaw.kerPairPointEquiv_inv, eqv_torusPoint, eqv_torusPoint]
  exact tpt_inv O (WithConv.toConv χ)

theorem eqv_nsmul_torusPt (χ : WithConv (torusCoord (ResidueField ↥A) O.toricRank →ₐ[ResidueField ↥A] ResidueField ↥A))
    (n : ℕ) :
    (eqv O (𝟙 _) ((LH O).nsmul (𝟙 _) n
        ⟨(torusPt _ _ χ.ofConv).1 ≫ (ιHOver O hι).1, by rw [Category.assoc, ιH_over, (torusPt _ _ χ.ofConv).2]⟩)).1 =
      tpt O (χ ^ n) := by
  rw [RelativeGroupLaw.kerPairPointEquiv_nsmul, eqv_torusPoint, tpt_pow]

scoped instance : IsReduced (Hκ O) := O.ker_degeneracyHom_special_isReduced

theorem hcomm : (LH O).IsCommutative :=
  RelativeGroupLaw.IsCommutative.kerPairLaw _ _ _ _ (RelativeGroupLaw.IsCommutative.baseChange (resPt A ≫ Λ.σA) O.comm)

scoped instance torus_locallyOfFiniteType (S : Type) [Field S] (t : ℕ) : LocallyOfFiniteType (torusStr S t) := by
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
  exact RingHom.finiteType_algebraMap.mpr inferInstance

scoped instance torus_isReduced (S : Type) [Field S] (t : ℕ) : IsReduced (torusScheme S t) := by
  infer_instance

theorem nT_over (S : Type) [CommRing S] (t n : ℕ) :
    Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapDomainRingHom S (n • AddMonoidHom.id (Fin t → ℤ)))) ≫
      torusStr S t = torusStr S t := by
  show Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  exact (AddMonoidAlgebra.mapDomainAlgHom S S (n • AddMonoidHom.id (Fin t → ℤ))).comp_algebraMap

end Fibre

end OPENT
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronObjectAtP_exists_isOpenImmersion_torus_kerPair_degeneracyHom.OPENT"

namespace OPENT
namespace Fib

variable {N₀ p : ℕ} [NeZero N₀] [Fact p.Prime] [NeZero p] {hpN₀ : ¬ p ∣ N₀}
  {A : ValuationSubring (AlgebraicClosure ℚ)} {hA : A.LiesOverPrime p}
  {Λ : LevelData N₀ p A}

theorem LevelData.ptsSp_zero (hΛ : Λ.IsJacobian) : Λ.ptsSp 0 = Λ.L.one (resPt A ≫ Λ.σA) := by
  letI := Λ.L.pointGroup (resPt A ≫ Λ.σA)
  have hadd := hΛ.2.2.2.2.1
  have h : Λ.ptsSp 0 * Λ.ptsSp 0 = Λ.ptsSp 0 := by
    change Λ.L.mul _ (Λ.ptsSp 0) (Λ.ptsSp 0) = Λ.ptsSp 0
    rw [← hadd, add_zero]
  exact mul_eq_left.mp h

theorem ribet_coords (hΛ : Λ.IsJacobian) (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ)
    (x : SchemeHomOver (resPt A ≫ Λ.σA) O.g)
    (h0 : NeronModelInfra.schemeHomOverComp x (O.degeneracyHom 0) = Λ.L.one (resPt A ≫ Λ.σA))
    (h1 : NeronModelInfra.schemeHomOverComp x (O.degeneracyHom 1) = Λ.L.one (resPt A ≫ Λ.σA)) :
    Λ.ptsSp.symm (fibreMap (O.abqFibre 0) x) + O.frobSp (Λ.ptsSp.symm (fibreMap (O.abqFibre 1) x)) = 0 ∧
    O.frobSp (Λ.ptsSp.symm (fibreMap (O.abqFibre 0) x)) + Λ.ptsSp.symm (fibreMap (O.abqFibre 1) x) = 0 := by
  have hz : Λ.ptsSp.symm (Λ.L.one (resPt A ≫ Λ.σA)) = 0 := by
    rw [Equiv.symm_apply_eq, LevelData.ptsSp_zero hΛ]
  obtain ⟨e0, e1⟩ := O.degeneracyHom_special x
  rw [h0, hz] at e0
  rw [h1, hz] at e1
  exact ⟨e0.symm, e1.symm⟩

theorem ribet_coords' (hΛ : Λ.IsJacobian) (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ)
    (x : SchemeHomOver (resPt A ≫ Λ.σA) O.g)
    (h0 : NeronModelInfra.schemeHomOverComp x (O.degeneracyHom 0) = Λ.L.one (resPt A ≫ Λ.σA))
    (h1 : NeronModelInfra.schemeHomOverComp x (O.degeneracyHom 1) = Λ.L.one (resPt A ≫ Λ.σA)) :
    Λ.ptsSp.symm (fibreMap (O.abqFibre 1) x) ∈ Function.fixedPoints (O.frobSp ∘ O.frobSp) ∧
    Λ.ptsSp.symm (fibreMap (O.abqFibre 0) x) = - O.frobSp (Λ.ptsSp.symm (fibreMap (O.abqFibre 1) x)) := by
  obtain ⟨e0, e1⟩ := ribet_coords hΛ O x h0 h1
  have ha₀ := eq_neg_of_add_eq_zero_left e0
  refine ⟨?_, ha₀⟩
  change O.frobSp (O.frobSp _) = _
  rw [ha₀, map_neg, neg_add_eq_zero] at e1
  exact e1

theorem ofFibrePt_injective {R R' : Type} [CommRing R] [CommRing R'] {X : Scheme.{0}}
    {ι : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R)} {f : X ⟶ Spec (CommRingCat.of R)} :
    Function.Injective (ofFibrePt (ι := ι) (f := f)) := by
  intro y y' h
  have h1 : (RelativeGroupLaw.baseChangePointToBase ι y).1 = (RelativeGroupLaw.baseChangePointToBase ι y').1 :=
    congrArg Subtype.val h
  exact (RelativeGroupLaw.baseChangePointEquiv ι (𝟙 _)).injective (Subtype.ext h1)

theorem exists_torus_mul_of_abqFibre_eq (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ)
    {x y : SchemeHomOver (resPt A ≫ Λ.σA) O.g}
    (h : ∀ i, fibreMap (O.abqFibre i) x = fibreMap (O.abqFibre i) y) :
    ∃ τ : SchemeHomOver (𝟙 _) (torusStr (ResidueField ↥A) O.toricRank),
      toFibrePt x = (O.L.baseChange (resPt A ≫ Λ.σA)).mul (𝟙 _)
        (NeronModelInfra.schemeHomOverComp τ O.torusFibre) (toFibrePt y) := by
  letI G1 := (O.L.baseChange (resPt A ≫ Λ.σA)).pointGroup (𝟙 (Spec (CommRingCat.of (ResidueField ↥A))))
  letI G2 := (Λ.L.baseChange (resPt A ≫ Λ.σA)).pointGroup (𝟙 (Spec (CommRingCat.of (ResidueField ↥A))))
  let φ : Fin 2 → (SchemeHomOver (𝟙 _) (RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) O.g) →*
      SchemeHomOver (𝟙 _) (RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) Λ.f)) := fun i =>
    MonoidHom.mk' (fun z => NeronModelInfra.schemeHomOverComp z (O.abqFibre i))
      (fun a b => O.abqFibre_mul i (𝟙 _) a b)
  have hxy : ∀ i, φ i (toFibrePt x) = φ i (toFibrePt y) := fun i => ofFibrePt_injective (h i)
  have hu : ∀ i, NeronModelInfra.schemeHomOverComp (toFibrePt x * (toFibrePt y)⁻¹) (O.abqFibre i) =
      (Λ.L.baseChange (resPt A ≫ Λ.σA)).one (𝟙 _) := by
    intro i
    change φ i (toFibrePt x * (toFibrePt y)⁻¹) = 1
    rw [map_mul, map_inv, hxy i, mul_inv_cancel]
  obtain ⟨τ, hτ⟩ := (O.abqFibre_eq_one_iff (𝟙 _) (toFibrePt x * (toFibrePt y)⁻¹)).mp hu
  refine ⟨τ, ?_⟩
  change toFibrePt x = (NeronModelInfra.schemeHomOverComp τ O.torusFibre) * toFibrePt y
  rw [hτ, inv_mul_cancel_right]

theorem exists_finset_kernel_coset_representatives (hΛ : Λ.IsJacobian) (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ)
    (hfin : (Function.fixedPoints (O.frobSp ∘ O.frobSp)).Finite) :
    ∃ S : Finset (SchemeHomOver (resPt A ≫ Λ.σA) O.g),
      (∀ s ∈ S, ∀ i, NeronModelInfra.schemeHomOverComp s (O.degeneracyHom i) = Λ.L.one (resPt A ≫ Λ.σA)) ∧
      ∀ x : SchemeHomOver (resPt A ≫ Λ.σA) O.g,
        (∀ i, NeronModelInfra.schemeHomOverComp x (O.degeneracyHom i) = Λ.L.one (resPt A ≫ Λ.σA)) →
        ∃ s ∈ S, ∃ τ : SchemeHomOver (𝟙 _) (torusStr (ResidueField ↥A) O.toricRank),
          toFibrePt x = (O.L.baseChange (resPt A ≫ Λ.σA)).mul (𝟙 _)
            (NeronModelInfra.schemeHomOverComp τ O.torusFibre) (toFibrePt s) := by
  classical

  let K : Set (SchemeHomOver (resPt A ≫ Λ.σA) O.g) :=
    {x | ∀ i, NeronModelInfra.schemeHomOverComp x (O.degeneracyHom i) = Λ.L.one (resPt A ≫ Λ.σA)}
  let a : SchemeHomOver (resPt A ≫ Λ.σA) O.g → JZeroC (ResidueField ↥A) N₀ :=
    fun x => Λ.ptsSp.symm (fibreMap (O.abqFibre 1) x)
  have haK : a '' K ⊆ Function.fixedPoints (O.frobSp ∘ O.frobSp) := by
    rintro _ ⟨x, hx, rfl⟩
    exact (ribet_coords' hΛ O x (hx 0) (hx 1)).1
  have hKfin : (a '' K).Finite := hfin.subset haK

  have hrep : ∀ e : a '' K, ∃ x ∈ K, a x = e := fun e => e.2
  choose rep hrepK hrepa using hrep
  haveI : Fintype (a '' K) := hKfin.fintype
  refine ⟨Finset.univ.image rep, ?_, ?_⟩
  · intro s hs
    obtain ⟨e, -, rfl⟩ := Finset.mem_image.mp hs
    exact hrepK e
  · intro x hx
    refine ⟨rep ⟨a x, x, hx, rfl⟩, Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩, ?_⟩
    apply exists_torus_mul_of_abqFibre_eq O

    have h1 : a x = a (rep ⟨a x, x, hx, rfl⟩) := (hrepa ⟨a x, x, hx, rfl⟩).symm
    have h0 : Λ.ptsSp.symm (fibreMap (O.abqFibre 0) x) =
        Λ.ptsSp.symm (fibreMap (O.abqFibre 0) (rep ⟨a x, x, hx, rfl⟩)) := by
      rw [(ribet_coords' hΛ O x (hx 0) (hx 1)).2,
        (ribet_coords' hΛ O _ (hrepK ⟨a x, x, hx, rfl⟩ 0) (hrepK ⟨a x, x, hx, rfl⟩ 1)).2]
      exact congrArg _ (congrArg _ h1)
    intro i
    fin_cases i
    · exact Λ.ptsSp.symm.injective h0
    · exact Λ.ptsSp.symm.injective h1

end OPENT.Fib
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronObjectAtP_exists_isOpenImmersion_torus_kerPair_degeneracyHom.OPENT"
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronObjectAtP_exists_isOpenImmersion_torus_kerPair_degeneracyHom.OPENT"

namespace OPENT
namespace Fib

variable {N₀ p : ℕ} [NeZero N₀] [Fact p.Prime] [NeZero p] {hpN₀ : ¬ p ∣ N₀}
  {A : ValuationSubring (AlgebraicClosure ℚ)} {hA : A.LiesOverPrime p}
  {Λ : LevelData N₀ p A}

section TorusPoints
variable (S : Type) [CommRing S] (t : ℕ)

theorem exists_torusPt_eq' (τ : SchemeHomOver (𝟙 _) (torusStr S t)) :
    ∃ χ : torusCoord S t →ₐ[S] S, torusPt S t χ = τ := by
  let ψ : CommRingCat.of (torusCoord S t) ⟶ CommRingCat.of S := Spec.preimage τ.1
  have hψ : Spec.map ψ = τ.1 := Spec.map_preimage _
  have hcomp : (CommRingCat.ofHom (algebraMap S (torusCoord S t))) ≫ ψ = 𝟙 _ := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_id, hψ]
    exact τ.2
  refine ⟨{ ψ.hom with commutes' := fun r => ?_ }, ?_⟩
  · have := congrArg (fun g : CommRingCat.of S ⟶ CommRingCat.of S => g.hom r) hcomp
    simpa using this
  · apply Subtype.ext
    show Spec.map _ = τ.1
    rw [← hψ]
    rfl
end TorusPoints
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronObjectAtP_exists_isOpenImmersion_torus_kerPair_degeneracyHom.OPENT"

scoped instance torus_locallyOfFiniteType' (S : Type) [Field S] (t : ℕ) : LocallyOfFiniteType (torusStr S t) := by
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
  exact RingHom.finiteType_algebraMap.mpr inferInstance

theorem toFibrePt_ofFibrePt {R R' : Type} [CommRing R] [CommRing R'] {X : Scheme.{0}}
    {ι : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R)} {f : X ⟶ Spec (CommRingCat.of R)}
    (y : SchemeHomOver (𝟙 _) (RelativeGroupLaw.baseChangeStr ι f)) : toFibrePt (ofFibrePt y) = y := by
  change RelativeGroupLaw.baseChangePointOfBase ι _ = y
  have h : overId (ofFibrePt y) = RelativeGroupLaw.baseChangePointToBase ι y := Subtype.ext rfl
  rw [h, RelativeGroupLaw.baseChangePointOfBase_toBase]

theorem torusFibre_comp_fibreRestrictAlong_degeneracyHom_eq (hΛ : Λ.IsJacobian)
    (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) (i : Fin 2) :
    O.torusFibre.1 ≫ (NeronSpecialFibreInfra.fibreRestrictAlong (resPt A ≫ Λ.σA) Λ.f O.g (O.degeneracyHom i)).1 =
      torusStr (ResidueField ↥A) O.toricRank ≫ ((Λ.L.baseChange (resPt A ≫ Λ.σA)).one (𝟙 _)).1 := by
  haveI : IsAlgClosed (ResidueField ↥A) := ValuationSubring.isAlgClosed_residueField_algebraicClosure_rat A
  haveI : IsSeparated Λ.f := hΛ.1.proper.toIsSeparated
  haveI : LocallyOfFinitePresentation (torusStr (ResidueField ↥A) O.toricRank) := inferInstance
  refine AlgebraicGeometry.ext_of_forall_geometricPoint_comp_eq_of_flat (RingHom.id (ResidueField ↥A))
    Function.injective_id (torusStr (ResidueField ↥A) O.toricRank)
    (RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) Λ.f) ?_ ?_ ?_
  · rw [Category.assoc, (NeronSpecialFibreInfra.fibreRestrictAlong _ _ _ _).2, O.torusFibre.2]
  · rw [Category.assoc, ((Λ.L.baseChange (resPt A ≫ Λ.σA)).one (𝟙 _)).2, Category.comp_id]
  intro y hy
  have hy' : y ≫ torusStr (ResidueField ↥A) O.toricRank = 𝟙 _ := by
    rw [hy]; change Spec.map (𝟙 _) = _; exact Spec.map_id _
  obtain ⟨χ, hχ⟩ := exists_torusPt_eq' _ _ ⟨y, hy'⟩
  have hyχ : y = (torusPt _ _ χ).1 := (congrArg Subtype.val hχ).symm

  let xb : SchemeHomOver (𝟙 _) (RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) O.g) :=
    NeronModelInfra.schemeHomOverComp (torusPt _ _ χ) O.torusFibre
  have habq : ∀ j, NeronModelInfra.schemeHomOverComp xb (O.abqFibre j) =
      (Λ.L.baseChange (resPt A ≫ Λ.σA)).one (𝟙 _) :=
    (O.abqFibre_eq_one_iff (𝟙 _) xb).mpr ⟨torusPt _ _ χ, rfl⟩
  let x : SchemeHomOver (resPt A ≫ Λ.σA) O.g := ofFibrePt xb
  have hone : ofFibrePt ((Λ.L.baseChange (resPt A ≫ Λ.σA)).one (𝟙 (Spec (CommRingCat.of (ResidueField ↥A))))) =
      Λ.L.one (resPt A ≫ Λ.σA) := by
    apply Subtype.ext
    change (RelativeGroupLaw.baseChangePointToBase (resPt A ≫ Λ.σA) ((Λ.L.baseChange (resPt A ≫ Λ.σA)).one (𝟙 _))).1 = _
    rw [RelativeGroupLaw.baseChangePointToBase_one, RelativeGroupLaw.one_coe_eq Λ.L (𝟙 _ ≫ (resPt A ≫ Λ.σA)),
      RelativeGroupLaw.one_coe_eq Λ.L (resPt A ≫ Λ.σA), Category.id_comp]
  have hfm : ∀ j, fibreMap (O.abqFibre j) x = Λ.L.one (resPt A ≫ Λ.σA) := by
    intro j
    change ofFibrePt (NeronModelInfra.schemeHomOverComp (toFibrePt (ofFibrePt xb)) (O.abqFibre j)) = _
    rw [toFibrePt_ofFibrePt, habq j, hone]

  have hz : Λ.ptsSp.symm (Λ.L.one (resPt A ≫ Λ.σA)) = 0 := by
    rw [Equiv.symm_apply_eq, LevelData.ptsSp_zero hΛ]
  have hdeg : NeronModelInfra.schemeHomOverComp x (O.degeneracyHom i) = Λ.L.one (resPt A ≫ Λ.σA) := by
    obtain ⟨e0, e1⟩ := O.degeneracyHom_special x
    rw [hfm 0, hfm 1, hz, map_zero, add_zero] at e0
    rw [hfm 0, hfm 1, hz, map_zero, zero_add] at e1
    fin_cases i
    · exact Λ.ptsSp.symm.injective (e0.trans hz.symm)
    · exact Λ.ptsSp.symm.injective (e1.trans hz.symm)

  have hdegb : NeronModelInfra.schemeHomOverComp xb
      (NeronSpecialFibreInfra.fibreRestrictAlong (resPt A ≫ Λ.σA) Λ.f O.g (O.degeneracyHom i)) =
      (Λ.L.baseChange (resPt A ≫ Λ.σA)).one (𝟙 _) := by
    apply (RelativeGroupLaw.baseChangePointEquiv (resPt A ≫ Λ.σA) (𝟙 _)).injective
    change RelativeGroupLaw.baseChangePointToBase _ _ = RelativeGroupLaw.baseChangePointToBase _ _
    rw [RelativeGroupLaw.baseChangePointToBase_comp_fibreRestrictAlong, RelativeGroupLaw.baseChangePointToBase_one]
    have h1 : RelativeGroupLaw.baseChangePointToBase (resPt A ≫ Λ.σA) xb = overId x := by
      rw [← toFibrePt_ofFibrePt xb]
      exact RelativeGroupLaw.baseChangePointToBase_ofBase _ _
    rw [h1]
    have h2 : NeronModelInfra.schemeHomOverComp (overId x) (O.degeneracyHom i) =
        overId (NeronModelInfra.schemeHomOverComp x (O.degeneracyHom i)) := Subtype.ext rfl
    rw [h2, hdeg]
    apply Subtype.ext
    change (Λ.L.one (resPt A ≫ Λ.σA)).1 = (Λ.L.one (𝟙 _ ≫ (resPt A ≫ Λ.σA))).1
    rw [RelativeGroupLaw.one_coe_eq Λ.L (𝟙 _ ≫ (resPt A ≫ Λ.σA)), RelativeGroupLaw.one_coe_eq Λ.L (resPt A ≫ Λ.σA),
      Category.id_comp]
  have := congrArg Subtype.val hdegb
  rw [NeronModelInfra.schemeHomOverComp_coe] at this
  change ((torusPt _ _ χ).1 ≫ O.torusFibre.1) ≫ _ = _ at this
  rw [hyχ, ← Category.assoc, this, ← Category.assoc, (torusPt _ _ χ).2, Category.id_comp]

end OPENT.Fib
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronObjectAtP_exists_isOpenImmersion_torus_kerPair_degeneracyHom.OPENT P2MW.S_ModularCurve_JZeroNeronObjectAtP_exists_isOpenImmersion_torus_kerPair_degeneracyHom.OPENT.Fib"
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronObjectAtP_exists_isOpenImmersion_torus_kerPair_degeneracyHom.OPENT"

open OPENT in
theorem solution
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (Λ : JZeroNeronObjectAtP.LevelData N₀ p A) (hΛ : Λ.IsJacobian)
    (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) :
    letI dκ := fun i : Fin 2 =>
      NeronSpecialFibreInfra.fibreRestrictAlong (resPt A ≫ Λ.σA) Λ.f O.g (O.degeneracyHom i)
    letI LH := GoodReductionJacobian.RelativeGroupLaw.kerPairLaw
      (O.L.baseChange (resPt A ≫ Λ.σA)) (Λ.L.baseChange (resPt A ≫ Λ.σA)) dκ
      (fun i => GoodReductionJacobian.RelativeGroupLaw.IsHom.fibreRestrictAlong (resPt A ≫ Λ.σA)
        (fun t x y => O.degeneracyHom_mul i t x y))
    ∃ ι : torusScheme (ResidueField ↥A) O.toricRank ⟶
        RelativeGroupLaw.kerPair (Λ.L.baseChange (resPt A ≫ Λ.σA)) dκ,
      ι ≫ RelativeGroupLaw.kerPairι (Λ.L.baseChange (resPt A ≫ Λ.σA)) dκ = O.torusFibre.1 ∧
      IsOpenImmersion ι ∧
      ∀ n : ℕ, ι ≫ LH.schemeNsmul n =
        Spec.map (CommRingCat.ofHom
          (AddMonoidAlgebra.mapDomainRingHom (ResidueField ↥A) (n • AddMonoidHom.id (Fin O.toricRank → ℤ)))) ≫ ι := by
  classical

  haveI : IsAlgClosed (ResidueField ↥A) := ValuationSubring.isAlgClosed_residueField_algebraicClosure_rat A
  haveI := O.locallyOfFiniteType
  haveI := O.quasiCompact
  haveI := O.separated
  haveI : IsSeparated Λ.f := hΛ.1.proper.toIsSeparated
  haveI := O.torusFibre_isClosedImmersion

  have hι : ∀ i : Fin 2, O.torusFibre.1 ≫
      (NeronSpecialFibreInfra.fibreRestrictAlong (resPt A ≫ Λ.σA) Λ.f O.g (O.degeneracyHom i)).1 =
      torusStr (ResidueField ↥A) O.toricRank ≫ ((Λ.L.baseChange (resPt A ≫ Λ.σA)).one (𝟙 _)).1 :=
    fun i => OPENT.Fib.torusFibre_comp_fibreRestrictAlong_degeneracyHom_eq hΛ O i
  obtain ⟨S, hSK, hS⟩ := OPENT.Fib.exists_finset_kernel_coset_representatives hΛ O
    (ModularCurve.JZeroNeronObjectAtP.finite_fixedPoints_frobSp_comp_self N₀ p hpN₀ A hA Λ O)

  let ι : torusScheme (ResidueField ↥A) O.toricRank ⟶ Hκ O := (ιHOver O hι).1
  have hιf : ι ≫ HκStr O = torusStr (ResidueField ↥A) O.toricRank := ιH_over O hι
  haveI : IsClosedImmersion ι := by
    have : IsClosedImmersion (ι ≫ RelativeGroupLaw.kerPairι (Λ.L.baseChange (resPt A ≫ Λ.σA)) (dκ O)) := by
      rw [ιH_comp_kerPairι]; infer_instance
    exact .of_comp ι (RelativeGroupLaw.kerPairι (Λ.L.baseChange (resPt A ≫ Λ.σA)) (dκ O))

  have hSK' : ∀ s ∈ S, ∀ i, NeronModelInfra.schemeHomOverComp (toFibrePt s) (dκ O i) =
      (Λ.L.baseChange (resPt A ≫ Λ.σA)).one (𝟙 _) := by
    intro s hs i
    apply (RelativeGroupLaw.baseChangePointEquiv (resPt A ≫ Λ.σA) (f := Λ.f) (𝟙 _)).injective
    show RelativeGroupLaw.baseChangePointToBase _ _ = RelativeGroupLaw.baseChangePointToBase _ _
    rw [RelativeGroupLaw.baseChangePointToBase_comp_fibreRestrictAlong, RelativeGroupLaw.baseChange_one,
      RelativeGroupLaw.baseChangePointToBase_ofBase]
    apply Subtype.ext
    rw [NeronModelInfra.schemeHomOverComp_coe, one_coe_idComp]
    show (RelativeGroupLaw.baseChangePointToBase (resPt A ≫ Λ.σA) (toFibrePt s)).1 ≫ _ = _
    rw [toFibrePt, RelativeGroupLaw.baseChangePointToBase_ofBase]
    exact congrArg Subtype.val (hSK s hs i)
  let rep : {s // s ∈ S} → SchemeHomOver (𝟙 _) (HκStr O) := fun s =>
    (eqv O (𝟙 _)).symm ⟨toFibrePt s.1, hSK' s.1 s.2⟩
  have rep_eqv : ∀ s : {s // s ∈ S}, (eqv O (𝟙 _) (rep s)).1 = toFibrePt s.1 := fun s => by
    simp only [rep, Equiv.apply_symm_apply]
  let S' : Finset (SchemeHomOver (𝟙 _) (HκStr O)) := S.attach.image rep
  have hS'card : S'.card ≤ S.card := Finset.card_image_le.trans (by rw [Finset.card_attach])

  have hidx : ∀ x : SchemeHomOver (𝟙 _) (HκStr O), ∃ s ∈ S',
      ∃ τ : SchemeHomOver (𝟙 _) (torusStr (ResidueField ↥A) O.toricRank),
        x = (LH O).mul (𝟙 _) s ⟨τ.1 ≫ ι, by rw [Category.assoc, hιf, τ.2]⟩ := by
    intro z
    let uz := (eqv O (𝟙 _) z).1
    let x : SchemeHomOver (resPt A ≫ Λ.σA) O.g :=
      ⟨(RelativeGroupLaw.baseChangePointToBase (resPt A ≫ Λ.σA) uz).1, by
        simpa only [Category.id_comp] using (RelativeGroupLaw.baseChangePointToBase (resPt A ≫ Λ.σA) uz).2⟩
    have hxu : overId x = RelativeGroupLaw.baseChangePointToBase (resPt A ≫ Λ.σA) uz := Subtype.ext rfl
    have htx : toFibrePt x = uz := by
      rw [toFibrePt, hxu, RelativeGroupLaw.baseChangePointOfBase_toBase]
    have hx : ∀ i, NeronModelInfra.schemeHomOverComp x (O.degeneracyHom i) = Λ.L.one (resPt A ≫ Λ.σA) := by
      intro i
      have hR : RelativeGroupLaw.baseChangePointToBase (resPt A ≫ Λ.σA)
          ((Λ.L.baseChange (resPt A ≫ Λ.σA)).one (𝟙 _)) = Λ.L.one (𝟙 _ ≫ (resPt A ≫ Λ.σA)) := by
        rw [RelativeGroupLaw.baseChange_one, RelativeGroupLaw.baseChangePointToBase_ofBase]
      have h := congrArg (RelativeGroupLaw.baseChangePointToBase (resPt A ≫ Λ.σA)) ((eqv O (𝟙 _) z).2 i)
      rw [RelativeGroupLaw.baseChangePointToBase_comp_fibreRestrictAlong, hR] at h
      change NeronModelInfra.schemeHomOverComp (RelativeGroupLaw.baseChangePointToBase (resPt A ≫ Λ.σA) uz)
        (O.degeneracyHom i) = _ at h
      rw [← hxu] at h
      apply Subtype.ext
      have h' := congrArg Subtype.val h
      rw [NeronModelInfra.schemeHomOverComp_coe, one_coe_idComp] at h'
      exact h'
    obtain ⟨s, hs, τ, hsτ⟩ := hS x hx
    refine ⟨rep ⟨s, hs⟩, Finset.mem_image_of_mem _ (Finset.mem_attach _ _), τ, ?_⟩
    apply eq_of_eqv_eq O
    rw [RelativeGroupLaw.kerPairPointEquiv_mul, rep_eqv, eqv_torusPoint]
    show uz = _
    rw [← htx, hsτ]
    exact RelativeGroupLaw.IsCommutative.mul_comm
      (RelativeGroupLaw.IsCommutative.baseChange (resPt A ≫ Λ.σA) O.comm) _ _ _

  haveI : IsOpenImmersion ι :=
    AlgebraicGeometry.isOpenImmersion_of_isClosedImmersion_of_isReduced_of_finite_index (HκStr O) (LH O)
      (torusStr (ResidueField ↥A) O.toricRank) ι hιf (hmul O hι) (hinv O hι) S' hidx

  have hιn : ∀ n : ℕ, ι ≫ (LH O).schemeNsmul n =
      Spec.map (CommRingCat.ofHom
        (AddMonoidAlgebra.mapDomainRingHom (ResidueField ↥A) (n • AddMonoidHom.id (Fin O.toricRank → ℤ)))) ≫ ι := by
    intro n
    haveI : LocallyOfFinitePresentation (torusStr (ResidueField ↥A) O.toricRank) := inferInstance
    refine AlgebraicGeometry.ext_of_forall_geometricPoint_comp_eq_of_flat (RingHom.id (ResidueField ↥A))
      Function.injective_id (torusStr (ResidueField ↥A) O.toricRank) (HκStr O) ?_ ?_ ?_
    · rw [Category.assoc, RelativeGroupLaw.schemeNsmul_over, hιf]
    · rw [Category.assoc, hιf, nT_over]
    intro y hy
    have hy' : y ≫ torusStr (ResidueField ↥A) O.toricRank = 𝟙 _ := by
      rw [hy]; change Spec.map (𝟙 _) = _; exact Spec.map_id _
    obtain ⟨χ, hχ⟩ := exists_torusPt_eq _ _ ⟨y, hy'⟩
    have hyχ : y = (torusPt _ _ χ).1 := (congrArg Subtype.val hχ).symm

    let w : SchemeHomOver (𝟙 _) (HκStr O) :=
      ⟨(torusPt _ _ χ).1 ≫ ι, by rw [Category.assoc, hιf, (torusPt _ _ χ).2]⟩
    have hl : y ≫ ι ≫ (LH O).schemeNsmul n = ((LH O).nsmul (𝟙 _) n w).1 := by
      rw [← Category.assoc, hyχ]
      exact comp_schemeNsmul (LH O) n w
    let w' : SchemeHomOver (𝟙 _) (HκStr O) :=
      ⟨(torusPt _ _ (WithConv.toConv χ ^ n).ofConv).1 ≫ ι, by
        rw [Category.assoc, hιf, (torusPt _ _ (WithConv.toConv χ ^ n).ofConv).2]⟩
    have hr : y ≫ Spec.map (CommRingCat.ofHom
        (AddMonoidAlgebra.mapDomainRingHom (ResidueField ↥A) (n • AddMonoidHom.id (Fin O.toricRank → ℤ)))) ≫ ι = w'.1 := by
      show _ = (torusPt _ _ (WithConv.toConv χ ^ n).ofConv).1 ≫ ι
      rw [torusPt_pow_coe, hyχ, Category.assoc]
    rw [hl, hr]
    congr 1
    apply eq_of_eqv_eq O
    rw [eqv_nsmul_torusPt O hι (WithConv.toConv χ) n, eqv_torusPoint]
  exact ⟨ι, ιH_comp_kerPairι O hι, inferInstance, hιn⟩

end S_ModularCurve_JZeroNeronObjectAtP_exists_isOpenImmersion_torus_kerPair_degeneracyHom
end P2MW
export P2MW.S_ModularCurve_JZeroNeronObjectAtP_exists_isOpenImmersion_torus_kerPair_degeneracyHom (solution)
