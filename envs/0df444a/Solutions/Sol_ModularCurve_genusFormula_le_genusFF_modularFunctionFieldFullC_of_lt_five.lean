-- Prove2me | solution 1 for ModularCurve.genusFormula_le_genusFF_modularFunctionFieldFullC_of_lt_five
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/651e0aff-8abc-5e58-9403-dda436858ca2

import Mathlib
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_ModularCurve_GenusNumerics
import Definitions.Def_ModularCurve_QAdicPlaceMod
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_PlacesOverDVR
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.Def_AlgebraicCurve_Differentials
import Theorems.Thm_ModularCurve_finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi
import Theorems.Thm_ModularCurve_dedekindPsi_pos
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldFullC
import Theorems.Thm_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg_fiberOver
import Theorems.Thm_AlgebraicCurve_Place_isSeparable_adjoin_of_ord_eq_one
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_AlgebraicCurve_sum_ordDiff_D_le_two_mul_genusFF_of_isSeparable
import Theorems.Thm_ModularCurve_card_poles_jqModC_modularFunctionFieldFullC_eq_cuspCount
import Theorems.Thm_ModularCurve_le_six_mul_sum_ordDiff_D_jqModC_of_lt_five
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_genusFormula_le_genusFF_modularFunctionFieldFullC_of_lt_five
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom"
p2m_attr_erase "instance" "AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois HahnSeries.ramScale_apply"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial"
p2m_attr_erase "simp" "WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace"
p2m_attr_erase "simp" "AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one"
p2m_attr_erase "simp" "FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff"

noncomputable section

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

p2m_open "AlgebraicCurve~genus ModularCurve IsDedekindDomain WithZero"

namespace W9SLtFive

section Engine

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem mem_of_ord_nonneg (w : Place K F) {f : F} (hf : f ≠ 0) (h : 0 ≤ w.ord f) :
    f ∈ w.toValuationSubring := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible w.toValuationSubring
  obtain ⟨u, hu⟩ := w.exists_unit_mul_zpow hf hπ
  rw [hu, show w.ord f = (((w.ord f).toNat : ℕ) : ℤ) from (Int.toNat_of_nonneg h).symm,
    zpow_natCast]
  exact mul_mem (u : w.toValuationSubring).2 (pow_mem (π : w.toValuationSubring).2 _)

theorem mem_of_ord_sub_pos (w : Place K F) {f : F} {c : K}
    (h : 0 < w.ord (f - algebraMap K F c)) : f ∈ w.toValuationSubring := by
  have hne : f - algebraMap K F c ≠ 0 := by
    intro h0
    rw [h0, Place.ord_zero] at h
    exact lt_irrefl _ h
  have := add_mem (mem_of_ord_nonneg w hne h.le) (w.algebraMap_mem' c)
  rwa [sub_add_cancel] at this

theorem ord_eq_one_of_valuation_eq (w : Place K F) {v' : Valuation F ℤᵐ⁰}
    (hv' : v'.valuationSubring = w.toValuationSubring) {x : F} (hx : v' x = exp (-1 : ℤ)) :
    w.ord x = 1 := by
  have hE := w.isEquiv_adicValuation_of_valuationSubring_eq hv'
  have hx0 : v' x ≠ 0 := by rw [hx]; exact exp_ne_zero
  have hu0 : w.adicValuation x ≠ 0 := (hE.eq_zero).ne.mp hx0
  have hlt : w.adicValuation x < 1 := by
    refine hE.lt_one_iff_lt_one.mp ?_
    rw [hx, ← exp_zero]
    exact exp_lt_exp.mpr (by norm_num)
  obtain ⟨ϖ, hϖ⟩ := w.heightOneSpectrum.valuation_exists_uniformizer F
  change w.adicValuation ϖ = exp (-1 : ℤ) at hϖ
  have hϖ0 : w.adicValuation ϖ ≠ 0 := by rw [hϖ]; exact exp_ne_zero
  have hϖlt : v' ϖ < 1 := by
    refine hE.lt_one_iff_lt_one.mpr ?_
    rw [hϖ, ← exp_zero]
    exact exp_lt_exp.mpr (by norm_num)
  have hϖ0' : v' ϖ ≠ 0 := (hE.eq_zero).ne.mpr hϖ0
  have hϖle : v' ϖ ≤ v' x := by
    rw [hx, ← log_le_iff_le_exp hϖ0']
    have hlog : log (v' ϖ) < 0 := (log_lt_iff_lt_exp hϖ0').mpr (by rw [exp_zero]; exact hϖlt)
    omega
  have hge : exp (-1 : ℤ) ≤ w.adicValuation x := by
    rw [← hϖ]
    exact (hE ϖ x).mp hϖle
  have hle' : log (w.adicValuation x) ≤ -1 := by
    have hlog : log (w.adicValuation x) < 0 :=
      (log_lt_iff_lt_exp hu0).mpr (by rw [exp_zero]; exact hlt)
    omega
  have hge' : -1 ≤ log (w.adicValuation x) := (le_log_iff_exp_le hu0).mpr hge
  simp only [Place.ord]
  omega

scoped instance instIsPrincipalIdealRingAdjoinSingleton (t : F) :
    IsPrincipalIdealRing (Algebra.adjoin K ({t} : Set F)) := by
  have hmem : ∀ p : Polynomial K, Polynomial.aeval t p ∈ Algebra.adjoin K ({t} : Set F) := by
    intro p
    rw [Algebra.adjoin_singleton_eq_range_aeval]
    exact ⟨p, rfl⟩
  refine IsPrincipalIdealRing.of_surjective
    ((Polynomial.aeval t).codRestrict (Algebra.adjoin K ({t} : Set F)) hmem) ?_
  rintro ⟨a, ha⟩
  obtain ⟨p, hp⟩ : ∃ p : Polynomial K, Polynomial.aeval t p = a := by
    rw [Algebra.adjoin_singleton_eq_range_aeval] at ha
    exact (AlgHom.mem_range _).mp ha
  exact ⟨p, Subtype.ext hp⟩

def linGen (t : F) (c : K) : Algebra.adjoin K ({t} : Set F) :=
  ⟨t, Algebra.self_mem_adjoin_singleton K t⟩ - algebraMap K _ c

@[scoped simp] theorem coe_linGen (t : F) (c : K) :
    ((linGen t c : Algebra.adjoin K ({t} : Set F)) : F) = t - algebraMap K F c := by
  simp [linGen]

section Transcendental

variable (t : F) (htr : Transcendental K t)

include htr in
theorem linGen_ne_zero (c : K) : linGen t c ≠ 0 := by
  intro h
  have h' := congrArg (fun a : Algebra.adjoin K ({t} : Set F) => (a : F)) h
  simp only [coe_linGen, ZeroMemClass.coe_zero, sub_eq_zero] at h'
  exact htr (by rw [h']; exact isAlgebraic_algebraMap c)

def polyEquiv : Polynomial K ≃ₐ[K] Algebra.adjoin K ({t} : Set F) :=
  (AlgEquiv.ofInjective (Polynomial.aeval t) (transcendental_iff_injective.mp htr)).trans
    (Subalgebra.equivOfEq _ _ (by rw [Algebra.adjoin_singleton_eq_range_aeval]))

theorem polyEquiv_X_sub_C (c : K) :
    polyEquiv t htr (Polynomial.X - Polynomial.C c) = linGen t c := by
  apply Subtype.ext
  rw [coe_linGen]
  simp [polyEquiv, Subalgebra.equivOfEq_apply, AlgEquiv.ofInjective_apply]

include htr in

theorem prime_linGen (c : K) : Prime (linGen t c) := by
  rw [← polyEquiv_X_sub_C t htr c, MulEquiv.prime_iff]
  exact Polynomial.prime_X_sub_C c

def linPrime (c : K) : HeightOneSpectrum (Algebra.adjoin K ({t} : Set F)) :=
  ⟨Ideal.span {linGen t c}, (Ideal.span_singleton_prime (linGen_ne_zero t htr c)).mpr
    (prime_linGen t htr c), by
      rw [ne_eq, Ideal.span_singleton_eq_bot]
      exact linGen_ne_zero t htr c⟩

open scoped IntermediateField.algebraAdjoinAdjoin

def basePlace (c : K) : Place K (IntermediateField.adjoin K ({t} : Set F)) :=
  Place.ofHeightOneSpectrum (K := K) (linPrime t htr c)

theorem algebraMap_linGen (c : K) :
    algebraMap (Algebra.adjoin K ({t} : Set F)) (IntermediateField.adjoin K ({t} : Set F))
        (linGen t c) =
      IntermediateField.AdjoinSimple.gen K t - algebraMap K _ c := by
  apply Subtype.ext
  rw [IntermediateField.algebraAdjoinAdjoin.coe_algebraMap, coe_linGen]
  simp

theorem ord_basePlace (c : K) :
    (basePlace t htr c).ord (IntermediateField.AdjoinSimple.gen K t - algebraMap K _ c) = 1 := by
  rw [← algebraMap_linGen]
  refine ord_eq_one_of_valuation_eq (basePlace t htr c)
    (v' := (linPrime t htr c).valuation (IntermediateField.adjoin K ({t} : Set F))) rfl ?_
  rw [HeightOneSpectrum.valuation_of_algebraMap]
  exact (linPrime t htr c).intValuation_singleton (linGen_ne_zero t htr c) rfl

theorem forall_algebraMap_mem (v : Place K (IntermediateField.adjoin K ({t} : Set F)))
    (ht : IntermediateField.AdjoinSimple.gen K t ∈ v.toValuationSubring)
    (r : Algebra.adjoin K ({t} : Set F)) :
    algebraMap (Algebra.adjoin K ({t} : Set F)) (IntermediateField.adjoin K ({t} : Set F)) r ∈
      v.toValuationSubring := by
  obtain ⟨x, hx⟩ := r
  show (⟨x, IntermediateField.algebra_adjoin_le_adjoin K _ hx⟩ :
      IntermediateField.adjoin K ({t} : Set F)) ∈ v.toValuationSubring
  induction hx using Algebra.adjoin_induction with
  | mem y hy =>
    have hy' : y = t := Set.mem_singleton_iff.mp hy
    subst hy'
    exact ht
  | algebraMap a => exact v.algebraMap_mem' a
  | add y z hy hz ihy ihz => exact add_mem ihy ihz
  | mul y z hy hz ihy ihz => exact mul_mem ihy ihz

include htr in

theorem eq_basePlace_of_ord_pos (v : Place K (IntermediateField.adjoin K ({t} : Set F))) (c : K)
    (hv : 0 < v.ord (IntermediateField.AdjoinSimple.gen K t - algebraMap K _ c)) :
    v = basePlace t htr c := by
  have ht : IntermediateField.AdjoinSimple.gen K t ∈ v.toValuationSubring := mem_of_ord_sub_pos v hv
  have hw := forall_algebraMap_mem t v ht
  have hmem : linGen t c ∈ Place.center (Algebra.adjoin K ({t} : Set F)) v hw := by
    rw [Place.mem_center_iff_ord_pos v hw (linGen_ne_zero t htr c), algebraMap_linGen]
    exact hv
  have hcenter : Place.center (Algebra.adjoin K ({t} : Set F)) v hw = Ideal.span {linGen t c} := by
    haveI : (Ideal.span {linGen t c}).IsPrime := (linPrime t htr c).isPrime
    have hmax : (Ideal.span {linGen t c}).IsMaximal :=
      IsPrime.to_maximal_ideal (linPrime t htr c).ne_bot
    exact (hmax.eq_of_le (Ideal.IsPrime.ne_top inferInstance)
      ((Ideal.span_singleton_le_iff_mem _).mpr hmem)).symm
  have hc : Place.centerHeightOneSpectrum (Algebra.adjoin K ({t} : Set F)) v hw =
      linPrime t htr c := HeightOneSpectrum.ext hcenter
  apply Place.ext
  rw [v.toValuationSubring_eq_of_forall_mem hw, hc,
    HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
  rfl

theorem algebraMap_gen_sub (c : K) :
    algebraMap (IntermediateField.adjoin K ({t} : Set F)) F
        (IntermediateField.AdjoinSimple.gen K t - algebraMap K _ c) =
      t - algebraMap K F c := by
  rw [map_sub, IntermediateField.AdjoinSimple.algebraMap_gen,
    ← IsScalarTower.algebraMap_apply]

variable [FiniteDimensional (IntermediateField.adjoin K ({t} : Set F)) F]

theorem ord_sub_eq_mul (w : Place K F) (c : K) :
    w.ord (t - algebraMap K F c) =
      w.ramificationIndex (IntermediateField.adjoin K ({t} : Set F)) *
        (w.restrict (IntermediateField.adjoin K ({t} : Set F))).ord
          (IntermediateField.AdjoinSimple.gen K t - algebraMap K _ c) := by
  rw [← algebraMap_gen_sub t c, Place.ord_restrict]

include htr in

theorem restrict_eq_basePlace_iff (w : Place K F) (c : K) :
    w.restrict (IntermediateField.adjoin K ({t} : Set F)) = basePlace t htr c ↔
      0 < w.ord (t - algebraMap K F c) := by
  constructor
  · intro h
    rw [ord_sub_eq_mul t w c, h, ord_basePlace, mul_one]
    exact_mod_cast w.ramificationIndex_pos (F := IntermediateField.adjoin K ({t} : Set F))
  · intro h
    refine eq_basePlace_of_ord_pos t htr _ c ?_
    rw [ord_sub_eq_mul t w c] at h
    exact (pos_iff_pos_of_mul_pos h).mp
      (by exact_mod_cast w.ramificationIndex_pos (F := IntermediateField.adjoin K ({t} : Set F)))

include htr in

theorem ramificationIndex_eq_ord (w : Place K F) (c : K) (h : 0 < w.ord (t - algebraMap K F c)) :
    (w.ramificationIndex (IntermediateField.adjoin K ({t} : Set F)) : ℤ) =
      w.ord (t - algebraMap K F c) := by
  rw [ord_sub_eq_mul t w c, (restrict_eq_basePlace_iff t htr w c).mpr h, ord_basePlace, mul_one]

theorem inertiaDeg_eq_one (w : Place K F) (hw : w.deg = 1) :
    w.inertiaDeg (IntermediateField.adjoin K ({t} : Set F)) = 1 := by
  have h := w.deg_restrict_mul_inertiaDeg (F := IntermediateField.adjoin K ({t} : Set F))
  rw [hw] at h
  exact Nat.eq_one_of_mul_eq_one_left h

variable [Algebra.IsSeparable (IntermediateField.adjoin K ({t} : Set F)) F]

include htr in

theorem sum_ord_sub_eq_finrank (hdeg : ∀ w : Place K F, w.deg = 1) (c : K)
    (S : Finset (Place K F)) (hS : ∀ w, w ∈ S ↔ 0 < w.ord (t - algebraMap K F c)) :
    ∑ w ∈ S, w.ord (t - algebraMap K F c) =
      Module.finrank (IntermediateField.adjoin K ({t} : Set F)) F := by
  have hSfib : S = (basePlace t htr c).fiberOver F := by
    ext w
    rw [hS, Place.mem_fiberOver, restrict_eq_basePlace_iff t htr]
  have hsum := Place.sum_ramificationIndex_mul_inertiaDeg_fiberOver (F' := F) (basePlace t htr c)
  rw [← hSfib] at hsum
  rw [← hsum]
  refine Finset.sum_congr rfl fun w hw => ?_
  rw [inertiaDeg_eq_one t w (hdeg w), Nat.cast_one, mul_one,
    ramificationIndex_eq_ord t htr w c ((hS w).mp hw)]

include htr in

theorem exists_finset_ord_sub_pos (c : K) :
    ∃ S : Finset (Place K F), ∀ w, w ∈ S ↔ 0 < w.ord (t - algebraMap K F c) :=
  ⟨(basePlace t htr c).fiberOver F, fun w => by
    rw [Place.mem_fiberOver, restrict_eq_basePlace_iff t htr]⟩

end Transcendental

end Engine

theorem genusFormula_le_of_hurwitz_wild (N : ℕ) {g t : ℕ} {s : ℤ}
    (ht : t = cuspCount N)
    (hC : 7 * (dedekindPsi N : ℤ) - 3 * (nuTwo N : ℤ) - 4 * (nuThree N : ℤ) ≤ 6 * s)
    (hRH : s + ((dedekindPsi N : ℤ) - t) ≤ 2 * (g : ℤ) - 2 + 2 * (dedekindPsi N : ℤ)) :
    genusFormula N ≤ (g : ℚ) := by
  have hC' : 7 * (dedekindPsi N : ℚ) - 3 * (nuTwo N : ℚ) - 4 * (nuThree N : ℚ) ≤ 6 * (s : ℚ) := by
    exact_mod_cast hC
  have hRH' : (s : ℚ) + ((dedekindPsi N : ℚ) - t) ≤ 2 * (g : ℚ) - 2 + 2 * (dedekindPsi N : ℚ) := by
    exact_mod_cast hRH
  subst ht
  unfold genusFormula
  linarith

section LowerBound

variable (K : Type*) [Field K] [IsAlgClosed K] (N : ℕ) [NeZero N]

abbrev JJ : modularFunctionFieldFullC K N := ⟨jqModC K, jqModC_mem_full K N⟩

omit [IsAlgClosed K] [NeZero N] in
theorem transcendental_JJ : Transcendental K (JJ K N) := by
  have h : Transcendental K
      (algebraMap (modularFunctionFieldFullC K N) (LaurentSeries K) (JJ K N)) :=
    ModularCurve.transcendental_jqModC K
  exact (transcendental_algebraMap_iff (FaithfulSMul.algebraMap_injective _ _)).mp h

omit [IsAlgClosed K] in
theorem finrank_adjoin_JJ (hN : (N : K) ≠ 0) :
    Module.finrank (IntermediateField.adjoin K ({JJ K N} : Set (modularFunctionFieldFullC K N)))
      (modularFunctionFieldFullC K N) = dedekindPsi N :=
  ModularCurve.finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi K N hN

omit [IsAlgClosed K] in
theorem finiteDimensional_adjoin_JJ (hN : (N : K) ≠ 0) :
    FiniteDimensional
      (IntermediateField.adjoin K ({JJ K N} : Set (modularFunctionFieldFullC K N)))
      (modularFunctionFieldFullC K N) :=
  Module.finite_of_finrank_pos
    (by rw [finrank_adjoin_JJ K N hN]; exact ModularCurve.dedekindPsi_pos N (NeZero.ne N))

omit [IsAlgClosed K] [NeZero N] in
theorem adjoin_inv_JJ_eq :
    IntermediateField.adjoin K ({(JJ K N)⁻¹} : Set (modularFunctionFieldFullC K N)) =
      IntermediateField.adjoin K ({JJ K N} : Set (modularFunctionFieldFullC K N)) := by
  apply le_antisymm
  · rw [IntermediateField.adjoin_simple_le_iff]
    exact inv_mem (IntermediateField.mem_adjoin_simple_self K _)
  · rw [IntermediateField.adjoin_simple_le_iff]
    have h := inv_mem (IntermediateField.mem_adjoin_simple_self K (JJ K N)⁻¹)
    rwa [inv_inv] at h

omit [IsAlgClosed K] [NeZero N] in

theorem ord_inftyPlace_inv_JJ :
    (qInftyPlaceMod K (jqModC_mem_full K N)).ord (JJ K N)⁻¹ = 1 := by
  rw [ord_qInftyPlaceMod]
  exact order_jModInvElt K (jqModC_mem_full K N)

theorem isSeparable_adjoin_JJ (hN : (N : K) ≠ 0) :
    Algebra.IsSeparable
      (IntermediateField.adjoin K ({JJ K N} : Set (modularFunctionFieldFullC K N)))
      (modularFunctionFieldFullC K N) := by
  haveI := finiteDimensional_adjoin_JJ K N hN
  haveI : Algebra.IsAlgebraic
      (IntermediateField.adjoin K ({JJ K N} : Set (modularFunctionFieldFullC K N)))
      (modularFunctionFieldFullC K N) := Algebra.IsAlgebraic.of_finite _ _
  have h := Place.isSeparable_adjoin_of_ord_eq_one (K := K) (JJ K N)
    (qInftyPlaceMod K (jqModC_mem_full K N)) (ord_inftyPlace_inv_JJ K N)
  rwa [adjoin_inv_JJ_eq] at h

theorem genusFormula_le_genusFF {ℓ : ℕ} [Fact ℓ.Prime] [CharP K ℓ] (hℓ : ℓ < 5)
    (hN : (N : K) ≠ 0) :
    genusFormula N ≤ (genusFF K (modularFunctionFieldFullC K N) : ℚ) := by
  classical
  haveI hfin := finiteDimensional_adjoin_JJ K N hN
  haveI hsep := isSeparable_adjoin_JJ K N hN
  have htr := transcendental_JJ K N
  have hψ := finrank_adjoin_JJ K N hN
  haveI := ModularCurve.isCurveOver_modularFunctionFieldFullC K N
  have hdeg : ∀ w : Place K (modularFunctionFieldFullC K N), w.deg = 1 :=
    IsCurveOver.forall_deg_eq_one_of_isAlgClosed

  obtain ⟨S0, hS0⟩ := exists_finset_ord_sub_pos (JJ K N) htr (0 : K)
  have hS0' : ∀ P, P ∈ S0 ↔ 0 < P.ord (JJ K N) := fun P => by
    rw [hS0, map_zero, sub_zero]

  have heq := adjoin_inv_JJ_eq K N
  haveI hfin' : FiniteDimensional
      (IntermediateField.adjoin K ({(JJ K N)⁻¹} : Set (modularFunctionFieldFullC K N)))
      (modularFunctionFieldFullC K N) := by rw [heq]; exact hfin
  haveI hsep' : Algebra.IsSeparable
      (IntermediateField.adjoin K ({(JJ K N)⁻¹} : Set (modularFunctionFieldFullC K N)))
      (modularFunctionFieldFullC K N) := by rw [heq]; exact hsep
  have htr' : Transcendental K (JJ K N)⁻¹ := fun h => htr (IsAlgebraic.inv_iff.mp h)
  have hψ' : Module.finrank
      (IntermediateField.adjoin K ({(JJ K N)⁻¹} : Set (modularFunctionFieldFullC K N)))
      (modularFunctionFieldFullC K N) = dedekindPsi N := by rw [heq]; exact hψ
  obtain ⟨T, hT⟩ := exists_finset_ord_sub_pos (JJ K N)⁻¹ htr' (0 : K)
  have hT' : ∀ P, P ∈ T ↔ P.ord (JJ K N) < 0 := fun P => by
    rw [hT, map_zero, sub_zero, Place.ord_inv, neg_pos]

  have hsumT : ∑ P ∈ T, (-P.ord (JJ K N)) = dedekindPsi N := by
    have h := sum_ord_sub_eq_finrank (JJ K N)⁻¹ htr' hdeg 0 T hT
    simp only [map_zero, sub_zero, Place.ord_inv] at h
    rw [hψ'] at h
    exact h
  have eT : ∑ P ∈ T, (-P.ord (JJ K N) - 1) = (dedekindPsi N : ℤ) - T.card := by
    rw [Finset.sum_sub_distrib, hsumT]
    simp

  have hcT : T.card = cuspCount N :=
    ModularCurve.card_poles_jqModC_modularFunctionFieldFullC_eq_cuspCount K N hN T hT'

  have hC := ModularCurve.le_six_mul_sum_ordDiff_D_jqModC_of_lt_five K N hN hℓ S0 hS0'

  have hRH := AlgebraicCurve.sum_ordDiff_D_le_two_mul_genusFF_of_isSeparable K (JJ K N) htr
    hfin hsep S0 (fun P hP => le_of_lt ((hS0' P).mp hP)) T (fun P hP => (hT' P).mp hP)
  rw [eT, hψ] at hRH
  exact genusFormula_le_of_hurwitz_wild N hcT hC hRH

end LowerBound

end W9SLtFive
p2m_reactivate "P2MW.S_ModularCurve_genusFormula_le_genusFF_modularFunctionFieldFullC_of_lt_five.W9SLtFive"

end
p2m_reactivate "P2MW.S_ModularCurve_genusFormula_le_genusFF_modularFunctionFieldFullC_of_lt_five.W9SLtFive"

p2m_open "AlgebraicCurve~genus" in open  ModularCurve in
theorem solution
    (K : Type*) [Field K] [IsAlgClosed K] (N : ℕ) [NeZero N] (hN : (N : K) ≠ 0)
    {ℓ : ℕ} [Fact ℓ.Prime] [CharP K ℓ] (hℓ : ℓ < 5) :
    genusFormula N ≤ (genusFF K (modularFunctionFieldFullC K N) : ℚ) :=
  W9SLtFive.genusFormula_le_genusFF K N hℓ hN

end S_ModularCurve_genusFormula_le_genusFF_modularFunctionFieldFullC_of_lt_five
end P2MW
export P2MW.S_ModularCurve_genusFormula_le_genusFF_modularFunctionFieldFullC_of_lt_five (solution)
