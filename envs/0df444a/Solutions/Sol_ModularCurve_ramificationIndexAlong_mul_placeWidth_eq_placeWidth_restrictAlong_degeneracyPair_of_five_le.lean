-- Prove2me | solution 1 for ModularCurve.ramificationIndexAlong_mul_placeWidth_eq_placeWidth_restrictAlong_degeneracyPair_of_five_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/86eb4a3b-3163-50bf-bf03-867b9678732f

import Mathlib
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_PlaceWidth
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_ModularCurve_CharLDegeneracyHecke
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_ModularCurve_CharLSpecialFibreLevelNDictionary
import Definitions.Def_AlgebraicCurve_PlacesOverDVR
import Theorems.Thm_ModularCurve_ramificationIndexAlong_mul_placeWidth_eq_placeWidth_restrictAlong_of_coe_eq
import Theorems.Thm_ModularCurve_placeRamificationJ_mul_jWidth_evalAt_jNGeomGen_eq_of_five_le
import Theorems.Thm_ModularCurve_charLDegeneracyRoof_eq_modularFunctionFieldFullC_mul
import Theorems.Thm_ModularCurve_modularFunctionFieldC_eq_modularFunctionFieldFullC_of_charP_pos
import Theorems.Thm_ModularCurve_finiteAlong_heckeAlphaC
import Theorems.Thm_AlgebraicCurve_Place_evalAt_algebraMap_eq_evalAt_restrict
import Theorems.Thm_ModularCurve_place_deg_eq_one_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_Place_isRational_iff_deg_eq_one
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Theorems.Thm_AlgebraicCurve_Place_mem_toValuationSubring_of_isIntegral_adjoin
import Theorems.Thm_ModularCurve_coeff_jqModC_neg_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_ramificationIndexAlong_mul_placeWidth_eq_placeWidth_restrictAlong_degeneracyPair_of_five_le
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange WeierstrassCurve.Affine.Point.instFinite GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup ModularCurve.instIsElliptic_tateLaurent ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver"
p2m_attr_erase "instance" "AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.cuspCount_one ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois HahnSeries.ramScale_apply AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply"
p2m_attr_erase "simp" "AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU LaurentSeries.coeff_heckeV LaurentSeries.coeff_heckeU FreyPackage.ModMCarrier.coe_rescaleLin_apply ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂"
p2m_attr_erase "simp" "ModularCurve.tatePowerSeries_a₃ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.ProjectiveLine.map_mk ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule"
p2m_attr_erase "simp" "WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty"
p2m_attr_erase "simp" "WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero"
p2m_attr_erase "simp" "WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero"
p2m_attr_erase "simp" "TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff"
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
open AlgebraicCurve ModularCurve

namespace A67Red

set_option linter.unusedSectionVars false

section Generic

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem mem_of_ord_nonneg (v : Place K F) {f : F} (hf : f ≠ 0) (h : 0 ≤ v.ord f) :
    f ∈ v.toValuationSubring := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  rw [hu, show v.ord f = (((v.ord f).toNat : ℕ) : ℤ) from (Int.toNat_of_nonneg h).symm, zpow_natCast]
  exact mul_mem (u : v.toValuationSubring).2 (pow_mem (π : v.toValuationSubring).2 _)

open IsLocalRing in

theorem ord_sub_pos_of_evalAt_eq (v : Place K F) (hv : v.IsRational) {f : F}
    (hf : f ∈ v.toValuationSubring) {a : K} (ha : v.evalAt f = a) (hfa : f ≠ algebraMap K F a) :
    0 < v.ord (f - algebraMap K F a) := by
  have hg0 : f - algebraMap K F a ≠ 0 := sub_ne_zero.mpr hfa
  have hgmem : f - algebraMap K F a ∈ v.toValuationSubring := sub_mem hf (v.algebraMap_mem' a)
  refine (v.mem_maximalIdeal_iff_ord_pos hg0 hgmem).mp ?_
  rw [← residue_eq_zero_iff]
  have hres : residue v.toValuationSubring ⟨f, hf⟩ = algebraMap K v.ResidueField a := by
    rw [← ha]; exact (v.algebraMap_evalAt hv hf).symm
  have hsplit : (⟨f - algebraMap K F a, hgmem⟩ : v.toValuationSubring)
      = ⟨f, hf⟩ - algebraMap K v.toValuationSubring a :=
    Subtype.ext (by show f - algebraMap K F a = f - algebraMap K F a; rfl)
  rw [hsplit, map_sub, hres]
  exact sub_eq_zero.mpr rfl

end Generic

section LevelN

variable (K : Type*) [Field K] (N : ℕ) [NeZero N]

theorem isRational [IsAlgClosed K] (x : Place K ↥(modularFunctionFieldC K N)) : x.IsRational :=
  (Place.isRational_iff_deg_eq_one x).mpr (place_deg_eq_one_of_isAlgClosed K N x)

theorem isIntegral_jNGeomGen :
    IsIntegral (Algebra.adjoin K ({jGeomGen K N} : Set ↥(modularFunctionFieldC K N))) (jNGeomGen K N) := by
  obtain ⟨data⟩ := nonempty_modularPolynomialData N
  set A := Algebra.adjoin K ({jGeomGen K N} : Set ↥(modularFunctionFieldC K N)) with hA
  have hjA : jGeomGen K N ∈ A := Algebra.subset_adjoin rfl
  let g : Polynomial ℤ →+* ↥A := Polynomial.eval₂RingHom (Int.castRingHom ↥A) ⟨jGeomGen K N, hjA⟩
  have hg : (algebraMap ↥A ↥(modularFunctionFieldC K N)).comp g
      = Polynomial.eval₂RingHom (Int.castRingHom ↥(modularFunctionFieldC K N)) (jGeomGen K N) := by
    refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
    simp [g]
  refine ⟨data.Φ.map g, data.monic.map g, ?_⟩
  rw [Polynomial.eval₂_map, hg]
  exact evalModularPair_jGeomGen_eq_zero K N data

theorem jNGeomGen_mem_of_jGeomGen_mem (x : Place K ↥(modularFunctionFieldC K N))
    (hj : jGeomGen K N ∈ x.toValuationSubring) : jNGeomGen K N ∈ x.toValuationSubring :=
  x.mem_toValuationSubring_of_isIntegral_adjoin hj (isIntegral_jNGeomGen K N)

theorem jGeomGen_ne_algebraMap' (c : K) :
    jGeomGen K N ≠ algebraMap K ↥(modularFunctionFieldC K N) c := by
  intro h
  have h1 := congrArg (fun z : ↥(modularFunctionFieldC K N) => (z : LaurentSeries K).coeff (-1 : ℤ)) h
  beta_reduce at h1
  have hl : ((jGeomGen K N : ↥(modularFunctionFieldC K N)) : LaurentSeries K).coeff (-1 : ℤ) = 1 :=
    coeff_jqModC_neg_one K
  have hr : ((algebraMap K ↥(modularFunctionFieldC K N) c : ↥(modularFunctionFieldC K N)) : LaurentSeries K).coeff (-1 : ℤ) = 0 := by
    rw [show ((algebraMap K ↥(modularFunctionFieldC K N) c : ↥(modularFunctionFieldC K N)) : LaurentSeries K)
        = algebraMap K (LaurentSeries K) c from rfl, algebraMap_laurentSeries_apply_eq_single,
      HahnSeries.coeff_single_of_ne (by decide)]
  rw [hl, hr] at h1
  exact one_ne_zero h1

end LevelN

end A67Red

namespace A67Red

set_option linter.unusedSectionVars false

section Iota

variable (M s q' : ℕ) [NeZero M] [NeZero s] [NeZero (M * s)] (hs : s.Prime) [Fact q'.Prime]
  (hsq' : s ≠ q') (hq'M : ¬ q' ∣ M)
  {k : Type*} [Field k] [CharP k q']

include hs hsq' hq'M in
theorem not_dvd_mul : ¬ q' ∣ M * s := by
  intro h
  rcases (Nat.Prime.dvd_mul (Fact.out)).mp h with h1 | h2
  · exact hq'M h1
  · exact hsq' ((Nat.prime_dvd_prime_iff_eq (Fact.out) hs).mp h2).symm

include hs hsq' hq'M in
theorem levelS_le : modularFunctionFieldC k s ≤ modularFunctionFieldC k (M * s) := by
  haveI : NeZero q' := ⟨(Fact.out : q'.Prime).ne_zero⟩
  rw [modularFunctionFieldC_eq_modularFunctionFieldFullC_of_charP_pos k q' (M * s)
    (not_dvd_mul M s q' hs hsq' hq'M)]
  unfold modularFunctionFieldC
  rw [IntermediateField.adjoin_le_iff]
  rintro x (rfl | rfl)
  · exact jqModC_mem_full k (M * s)
  · show jqNModC k s ∈ modularFunctionFieldFullC k (M * s)
    unfold jqNModC
    exact jqModCd_mem_full k (M * s) (Dvd.intro_left M rfl)

noncomputable def iota (hle : modularFunctionFieldC k s ≤ modularFunctionFieldC k (M * s)) :
    ↥(modularFunctionFieldC k s) →ₐ[k] ↥(modularFunctionFieldC k (M * s)) :=
  IntermediateField.inclusion hle

theorem coe_iota (hle : modularFunctionFieldC k s ≤ modularFunctionFieldC k (M * s)) (x : ↥(modularFunctionFieldC k s)) :
    ((iota M s hle x : ↥(modularFunctionFieldC k (M * s))) : LaurentSeries k) = x :=
  IntermediateField.coe_inclusion hle x

include hs hsq' hq'M in
theorem finiteAlong_iota (hle : modularFunctionFieldC k s ≤ modularFunctionFieldC k (M * s)) :
    FiniteAlong k (iota M s hle) := by
  haveI : NeZero q' := ⟨(Fact.out : q'.Prime).ne_zero⟩
  haveI : NeZero (s * M) := ⟨by rw [Nat.mul_comm]; exact NeZero.ne (M * s)⟩
  have hq'sM : ¬ q' ∣ s * M := by rw [Nat.mul_comm]; exact not_dvd_mul M s q' hs hsq' hq'M
  have key : ∀ (n : ℕ) [NeZero n], n = M * s → modularFunctionFieldC k n = modularFunctionFieldC k (M * s) := by
    intro n _ hn; subst hn; rfl
  have hC : modularFunctionFieldC k (s * M) = modularFunctionFieldC k (M * s) := key (s * M) (Nat.mul_comm s M)
  have hR : charLDegeneracyRoof k s M = modularFunctionFieldC k (M * s) := by
    rw [charLDegeneracyRoof_eq_modularFunctionFieldFullC_mul k q' s M hq'sM,
      ← modularFunctionFieldC_eq_modularFunctionFieldFullC_of_charP_pos k q' (s * M) hq'sM, hC]
  have hfin := finiteAlong_heckeAlphaC k s M

  have key : ∀ (E : IntermediateField k (LaurentSeries k)) (hE : charLDegeneracyRoof k s M = E)
      (ψ : ↥(modularFunctionFieldC k s) →ₐ[k] ↥E), (∀ x, ((ψ x : ↥E) : LaurentSeries k) = x) →
      FiniteAlong k ψ := by
    intro E hE ψ hψ
    subst hE
    have : heckeAlphaC k s M = ψ := AlgHom.ext fun x => Subtype.ext (by rw [coe_heckeAlphaC, hψ])
    rw [← this]; exact hfin
  exact key _ hR _ (coe_iota M s hle)

end Iota

section Beta

variable (M s q' : ℕ) [NeZero M] [NeZero s] [NeZero (M * s)] (hs : s.Prime) [Fact q'.Prime] (hq5 : 5 ≤ q')
  (hsq' : s ≠ q') (hq'M : ¬ q' ∣ M)
  {k : Type} [Field k] [CharP k q'] [IsAlgClosed k] [DecidableEq k]
  (φ₁ : ↥(modularFunctionFieldC k M) →ₐ[k] ↥(modularFunctionFieldC k (M * s)))
  (hφ₁ : φ₁.toRingHom.IsIntegral)
  (hφβ : ∀ x, ((φ₁ x : ↥(modularFunctionFieldC k (M * s))) : LaurentSeries k) = qExpand k s x)

include hs hq5 hsq' hq'M hφβ in
theorem beta_leg (p : Place k ↥(modularFunctionFieldC k (M * s)))
    (hdiv : placeRamificationJ (M * s) p ∣ jWidth (p.evalAt (jGeomGen k (M * s)))) :
    Place.ramificationIndexAlong φ₁ p * placeWidth (M * s) p = placeWidth M (Place.restrictAlong φ₁ hφ₁ p) := by
  have hsk : (s : k) ≠ 0 := fun h => by
    have := (CharP.cast_eq_zero_iff k q' s).mp h
    exact hsq' ((Nat.prime_dvd_prime_iff_eq (Fact.out) hs).mp this).symm

  have hle := levelS_le M s q' hs hsq' hq'M (k := k)
  set ι := iota M s hle with hι_def
  have hιcoe := coe_iota M s hle
  have hιint : ι.toRingHom.IsIntegral := by
    letI := algebraAlong ι
    haveI : Module.Finite ↥(modularFunctionFieldC k s) ↥(modularFunctionFieldC k (M * s)) :=
      finiteAlong_iota M s q' hs hsq' hq'M hle
    exact fun y => Algebra.IsIntegral.isIntegral y

  set a : k := p.evalAt (jGeomGen k (M * s)) with ha
  set e₁ : ℕ := Place.ramificationIndexAlong φ₁ p with he₁_def
  set eι : ℕ := Place.ramificationIndexAlong ι p with heι_def

  have hJ : ι (jGeomGen k s) = jGeomGen k (M * s) := Subtype.ext (hιcoe _)
  have hJs : ι (jNGeomGen k s) = φ₁ (jGeomGen k M) := Subtype.ext (by rw [hιcoe, hφβ]; rfl)

  have hrpos : 0 < placeRamificationJ (M * s) p := by
    rcases Nat.eq_zero_or_pos (placeRamificationJ (M * s) p) with h0 | h0
    · exfalso; rw [h0, zero_dvd_iff] at hdiv; exact (jWidth_pos a).ne' hdiv
    · exact h0
  have hordpos : 0 < p.ord (jGeomGen k (M * s) - algebraMap k _ a) := by
    have : 0 < (p.ord (jGeomGen k (M * s) - algebraMap k _ a)).toNat := hrpos
    omega
  have hsub0 : jGeomGen k (M * s) - algebraMap k _ a ≠ 0 := sub_ne_zero.mpr (jGeomGen_ne_algebraMap' k (M * s) a)
  have hjmem : jGeomGen k (M * s) ∈ p.toValuationSubring := by
    have h1 := mem_of_ord_nonneg p hsub0 hordpos.le
    have := add_mem h1 (p.algebraMap_mem' a)
    simpa using this

  letI instφ := algebraAlong φ₁
  haveI := isScalarTower_along φ₁
  haveI := isIntegral_along φ₁ hφ₁
  have hres₁ : Place.restrictAlong φ₁ hφ₁ p = p.restrict ↥(modularFunctionFieldC k M) := rfl
  set x₁ := p.restrict ↥(modularFunctionFieldC k M) with hx₁_def
  rw [hres₁]
  have he₁ : e₁ = p.ramificationIndex ↥(modularFunctionFieldC k M) := rfl
  have he₁pos : 0 < e₁ := he₁ ▸ p.ramificationIndex_pos
  have hx₁rat : x₁.IsRational := isRational k M x₁
  set a' : k := x₁.evalAt (jGeomGen k M) with ha'

  letI instι := algebraAlong ι
  haveI := isScalarTower_along ι
  haveI := isIntegral_along ι hιint
  have hresz : Place.restrictAlong ι hιint p = p.restrict ↥(modularFunctionFieldC k s) := rfl
  set z := p.restrict ↥(modularFunctionFieldC k s) with hz_def
  have hzrat : z.IsRational := isRational k s z
  have heι : eι = p.ramificationIndex ↥(modularFunctionFieldC k s) := rfl
  have heιpos : 0 < eι := heι ▸ p.ramificationIndex_pos

  have hjz : jGeomGen k s ∈ z.toValuationSubring := by
    rw [hz_def, Place.mem_restrict_iff, show algebraMap _ ↥(modularFunctionFieldC k (M * s)) (jGeomGen k s) = ι (jGeomGen k s) from rfl, hJ]
    exact hjmem
  have hjsz : jNGeomGen k s ∈ z.toValuationSubring := jNGeomGen_mem_of_jGeomGen_mem k s z hjz
  have hJsmem : (φ₁ (jGeomGen k M)) ∈ p.toValuationSubring := by
    rw [← hJs]
    exact (Place.mem_restrict_iff (w := p) (F := ↥(modularFunctionFieldC k s))).1 hjsz
  have hjx₁ : jGeomGen k M ∈ x₁.toValuationSubring :=
    (Place.mem_restrict_iff (w := p) (F := ↥(modularFunctionFieldC k M))).2 hJsmem

  have hza : z.evalAt (jGeomGen k s) = a := by
    rw [hz_def, ← Place.evalAt_algebraMap_eq_evalAt_restrict (F := ↥(modularFunctionFieldC k s)) p hzrat hjz,
      show algebraMap _ ↥(modularFunctionFieldC k (M * s)) (jGeomGen k s) = ι (jGeomGen k s) from rfl, hJ]
  have hpa' : p.evalAt (φ₁ (jGeomGen k M)) = a' :=
    Place.evalAt_algebraMap_eq_evalAt_restrict (F := ↥(modularFunctionFieldC k M)) p hx₁rat hjx₁
  have hza' : z.evalAt (jNGeomGen k s) = a' := by
    rw [hz_def, ← Place.evalAt_algebraMap_eq_evalAt_restrict (F := ↥(modularFunctionFieldC k s)) p hzrat hjsz,
      show algebraMap _ ↥(modularFunctionFieldC k (M * s)) (jNGeomGen k s) = ι (jNGeomGen k s) from rfl, hJs, hpa']

  have ht₁pos : 0 < x₁.ord (jGeomGen k M - algebraMap k ↥(modularFunctionFieldC k M) a') :=
    ord_sub_pos_of_evalAt_eq x₁ hx₁rat hjx₁ rfl (jGeomGen_ne_algebraMap' k M a')
  have hord₁ : p.ord ((φ₁ (jGeomGen k M)) - algebraMap k _ a') = e₁ * x₁.ord (jGeomGen k M - algebraMap k _ a') := by
    have : (φ₁ (jGeomGen k M)) - algebraMap k ↥(modularFunctionFieldC k (M * s)) a'
        = algebraMap ↥(modularFunctionFieldC k M) ↥(modularFunctionFieldC k (M * s))
            (jGeomGen k M - algebraMap k ↥(modularFunctionFieldC k M) a') := by
      rw [map_sub, ← IsScalarTower.algebraMap_apply k ↥(modularFunctionFieldC k M) ↥(modularFunctionFieldC k (M * s)) a']
      rfl
    rw [this, Place.ord_restrict, ← he₁]
  have hordι : p.ord (jGeomGen k (M * s) - algebraMap k _ a) = eι * z.ord (jGeomGen k s - algebraMap k _ a) := by
    have : jGeomGen k (M * s) - algebraMap k ↥(modularFunctionFieldC k (M * s)) a
        = ι (jGeomGen k s - algebraMap k ↥(modularFunctionFieldC k s) a) := by
      rw [map_sub, hJ, AlgHom.commutes]
    rw [this, Place.ord_restrictAlong ι hιint p, hresz]
  have hordιs : p.ord ((φ₁ (jGeomGen k M)) - algebraMap k _ a') = eι * z.ord (jNGeomGen k s - algebraMap k _ a') := by
    have : (φ₁ (jGeomGen k M)) - algebraMap k ↥(modularFunctionFieldC k (M * s)) a'
        = ι (jNGeomGen k s - algebraMap k ↥(modularFunctionFieldC k s) a') := by
      rw [map_sub, hJs, AlgHom.commutes]
    rw [this, Place.ord_restrictAlong ι hιint p, hresz]

  set A : ℕ := (z.ord (jGeomGen k s - algebraMap k ↥(modularFunctionFieldC k s) a)).toNat with hA_def
  set B : ℕ := (z.ord (jNGeomGen k s - algebraMap k ↥(modularFunctionFieldC k s) a')).toNat with hB_def
  set t₁ : ℕ := (x₁.ord (jGeomGen k M - algebraMap k ↥(modularFunctionFieldC k M) a')).toNat with ht₁_def
  have hAz : z.ord (jGeomGen k s - algebraMap k ↥(modularFunctionFieldC k s) a) = (A : ℤ) := by
    rw [hA_def, Int.toNat_of_nonneg]
    have := hordι ▸ hordpos
    exact (pos_of_mul_pos_right this (by exact_mod_cast heιpos.le)).le
  have hBz : z.ord (jNGeomGen k s - algebraMap k ↥(modularFunctionFieldC k s) a') = (B : ℤ) := by
    rw [hB_def, Int.toNat_of_nonneg]
    have h1 : 0 < p.ord ((φ₁ (jGeomGen k M)) - algebraMap k _ a') := by
      rw [hord₁]; exact mul_pos (by exact_mod_cast he₁pos) ht₁pos
    rw [hordιs] at h1
    exact (pos_of_mul_pos_right h1 (by exact_mod_cast heιpos.le)).le
  have ht₁z : x₁.ord (jGeomGen k M - algebraMap k ↥(modularFunctionFieldC k M) a') = (t₁ : ℤ) := by
    rw [ht₁_def, Int.toNat_of_nonneg ht₁pos.le]
  have hApos : 0 < A := by
    have := hordι ▸ hordpos
    rw [hAz] at this
    exact_mod_cast pos_of_mul_pos_right this (by exact_mod_cast heιpos.le)
  have ht₁pos' : 0 < t₁ := by
    have := ht₁z ▸ ht₁pos
    exact_mod_cast this

  have hkey : e₁ * t₁ = eι * B := by
    have h := hord₁.symm.trans hordιs
    rw [ht₁z, hBz] at h
    exact_mod_cast h

  have hrMs : placeRamificationJ (M * s) p = eι * A := by
    unfold placeRamificationJ
    rw [← ha, hordι, hAz, ← Nat.cast_mul, Int.toNat_natCast]
  have hrM : placeRamificationJ M x₁ = t₁ := by
    unfold placeRamificationJ
    rw [← ha']

  have hq's : ¬ q' ∣ s := fun h =>
    hsq' ((Nat.prime_dvd_prime_iff_eq (Fact.out) hs).mp h).symm
  have hW := placeRamificationJ_mul_jWidth_evalAt_jNGeomGen_eq_of_five_le q' hq5 s hq's k z
  have hWz : A * jWidth a' = B * jWidth a := by
    unfold placeRamificationJ at hW
    rw [hza, hza'] at hW
    rw [hA_def, hB_def]
    exact hW

  rw [hrMs] at hdiv
  obtain ⟨c, hc⟩ := hdiv
  have hWa' : jWidth a' = e₁ * t₁ * c := by
    have h2 : A * jWidth a' = A * (eι * B * c) := by
      rw [hWz, hc]; ring
    have h3 := Nat.eq_of_mul_eq_mul_left hApos h2
    rw [h3, show eι * B = e₁ * t₁ from hkey.symm]
  show e₁ * (jWidth a / placeRamificationJ (M * s) p) = jWidth (x₁.evalAt (jGeomGen k M)) / placeRamificationJ M x₁
  rw [hrMs, hrM, ← ha', hc, hWa', Nat.mul_div_cancel_left c (Nat.mul_pos heιpos hApos),
    show e₁ * t₁ * c = t₁ * (e₁ * c) by ring, Nat.mul_div_cancel_left (e₁ * c) ht₁pos']

end Beta

end A67Red

open A67Red in
theorem solution
    (M s q' : ℕ) [NeZero M] [NeZero s] (hs : s.Prime) [Fact q'.Prime] (hq5 : 5 ≤ q')
    (hsq' : s ≠ q') (hq'M : ¬ q' ∣ M)
    {k : Type} [Field k] [CharP k q'] [IsAlgClosed k] [DecidableEq k] :
    haveI : NeZero (M * s) := ⟨Nat.mul_ne_zero (NeZero.ne M) (NeZero.ne s)⟩
    ∀ [Fintype ↥(ssPlaces q' (M * s) k)] [Fintype ↥(ssPlaces q' M k)]
      [DecidableEq ↥(ssPlaces q' (M * s) k)] [DecidableEq ↥(ssPlaces q' M k)],
    ∀ (ab : Fin 2 → ↥(ssPlaces q' (M * s) k) → ↥(ssPlaces q' M k))
      (m : Fin 2 → ↥(ssPlaces q' (M * s) k) → ℕ)
      (φ : Fin 2 → (↥(modularFunctionFieldC k M) →ₐ[k] ↥(modularFunctionFieldC k (M * s))))
      (hφ : ∀ i, (φ i).toRingHom.IsIntegral)
      (hφα : ∀ x, ((φ 0 x : ↥(modularFunctionFieldC k (M * s))) : LaurentSeries k) = x)
      (hφβ : ∀ x, ((φ 1 x : ↥(modularFunctionFieldC k (M * s))) : LaurentSeries k) = qExpand k s x)
      (hab : ∀ i p, (ab i p : Place k (modularFunctionFieldC k M))
        = Place.restrictAlong (φ i) (hφ i) ↑p)
      (hm : ∀ i p, m i p = Place.ramificationIndexAlong (φ i)
        (p : Place k (modularFunctionFieldC k (M * s)))),
    ∀ (i : Fin 2) (p : ↥(ssPlaces q' (M * s) k)),
      placeRamificationJ (M * s) (p : Place k (modularFunctionFieldC k (M * s)))
          ∣ jWidth ((p : Place k (modularFunctionFieldC k (M * s))).evalAt (jGeomGen k (M * s))) →
      m i p * placeWidth (M * s)
          (p : Place k (modularFunctionFieldC k (M * s)))
        = placeWidth M (ab i p : Place k (modularFunctionFieldC k M)) := by
  haveI : NeZero (M * s) := ⟨Nat.mul_ne_zero (NeZero.ne M) (NeZero.ne s)⟩
  intro _ _ _ _ ab m φ hφ hφα hφβ hab hm i p hdiv
  rw [hm, hab]
  fin_cases i
  · exact ramificationIndexAlong_mul_placeWidth_eq_placeWidth_restrictAlong_of_coe_eq M (M * s) (φ 0) (hφ 0) hφα p hdiv
  · exact beta_leg M s q' hs hq5 hsq' hq'M (φ 1) (hφ 1) hφβ p hdiv

end S_ModularCurve_ramificationIndexAlong_mul_placeWidth_eq_placeWidth_restrictAlong_degeneracyPair_of_five_le
end P2MW
export P2MW.S_ModularCurve_ramificationIndexAlong_mul_placeWidth_eq_placeWidth_restrictAlong_degeneracyPair_of_five_le (solution)
