-- Prove2me | solution 1 for ModularForm.exists_linearIndependent_int_qCoeff_dimFormula_le_card
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/f48723b3-a514-54bb-9791-b9b0c234ce4a

import Mathlib
import Definitions.Def_CuspForm_ModPForms
import Definitions.Def_ModularCurve_GenusNumerics
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_ModPFormFn
import Definitions.Def_ModularCurve_QExpansionDiff
import Theorems.Thm_ModularCurve_exists_linearIndependent_isModPFormFn_rat_dimFormula_le_card
import Theorems.Thm_ModularCurve_exists_modularForm_qExpansion_eq_mul_thetaL_pow_of_isIntegral
import Theorems.Thm_ModularCurve_exists_ne_zero_coeffMap_eq_mul_of_isModPFormFn
import Theorems.Thm_ModularCurve_IsModPFormFn_coeffMap
import Theorems.Thm_ModularCurve_isModPFormFn_zero_and_add_and_smul
import Theorems.Thm_ModularCurve_thetaL_coeffMap_eq_coeffMap_single_mul_derivative
import Theorems.Thm_LinearIndependent_exists_det_submatrix_ne_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularForm_exists_linearIndependent_int_qCoeff_dimFormula_le_card
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular"
p2m_attr_erase "simp" "ModularCurve.qExpandAlgHomC_apply AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois ModularCurve.coe_cuspidalDivisor₀ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul HahnSeries.ramScale_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec"
p2m_attr_erase "simp" "WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁"
p2m_attr_erase "simp" "PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃"
p2m_attr_erase "simp" "WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero"
p2m_attr_erase "simp" "WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero"
p2m_attr_erase "simp" "FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff"

p2m_open "UpperHalfPlane ModularCurve~coeffEmb_jq"
open scoped MatrixGroups ModularForm Manifold

set_option autoImplicit false

noncomputable section

namespace B2Head

def Nice (f : ℍ → ℂ) : Prop :=
  Function.Periodic (f ∘ ofComplex) 1 ∧ MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f ∧ IsBoundedAtImInfty f

theorem Nice.mul {f g : ℍ → ℂ} (hf : Nice f) (hg : Nice g) : Nice (f * g) :=
  ⟨by simpa [Function.comp_def] using hf.1.mul hg.1, hf.2.1.mul hg.2.1, hf.2.2.mul hg.2.2⟩

theorem Nice.add {f g : ℍ → ℂ} (hf : Nice f) (hg : Nice g) : Nice (f + g) :=
  ⟨by simpa [Function.comp_def] using hf.1.add hg.1, hf.2.1.add hg.2.1, hf.2.2.add hg.2.2⟩

theorem Nice.const (c : ℂ) : Nice (fun _ => c) :=
  ⟨fun _ => rfl, mdifferentiable_const, Filter.const_boundedAtFilter _ _⟩

def niceSubalgebra : Subalgebra ℂ (ℍ → ℂ) where
  carrier := {f | Nice f}
  mul_mem' hf hg := hf.mul hg
  add_mem' hf hg := hf.add hg
  algebraMap_mem' c := Nice.const c

local notation "𝒩" => niceSubalgebra

theorem an (f : 𝒩) : AnalyticAt ℂ (cuspFunction 1 (f : ℍ → ℂ)) 0 :=
  UpperHalfPlane.analyticAt_cuspFunction_zero one_pos f.2.1 f.2.2.1 f.2.2.2

def qexpHom : 𝒩 →ₐ[ℂ] PowerSeries ℂ where
  toFun f := qExpansion 1 (f : ℍ → ℂ)
  map_one' := UpperHalfPlane.qExpansion_one 1
  map_mul' f g := UpperHalfPlane.qExpansion_mul (an f) (an g)
  map_zero' := UpperHalfPlane.qExpansion_zero 1
  map_add' f g := UpperHalfPlane.qExpansion_add (an f) (an g)
  commutes' c := by
    have h1 : ((algebraMap ℂ (ℍ → ℂ) c : ℍ → ℂ)) = c • (1 : ℍ → ℂ) := by
      funext z; simp
    have a1 : AnalyticAt ℂ (cuspFunction 1 (1 : ℍ → ℂ)) 0 := an (1 : 𝒩)
    change qExpansion 1 (algebraMap ℂ (ℍ → ℂ) c) = _
    rw [h1, UpperHalfPlane.qExpansion_smul a1 c, UpperHalfPlane.qExpansion_one,
      Algebra.algebraMap_eq_smul_one]

theorem qexpHom_apply (f : 𝒩) : qexpHom f = qExpansion 1 (f : ℍ → ℂ) := rfl

def ψ : 𝒩 →ₐ[ℂ] LaurentSeries ℂ :=
  { (HahnSeries.ofPowerSeries ℤ ℂ).comp qexpHom.toRingHom with
    commutes' := fun c => by
      change HahnSeries.ofPowerSeries ℤ ℂ (qexpHom (algebraMap ℂ 𝒩 c)) = _
      rw [qexpHom.commutes, HahnSeries.algebraMap_apply'] }

theorem ψ_apply (f : 𝒩) : ψ f = HahnSeries.ofPowerSeries ℤ ℂ (qExpansion 1 (f : ℍ → ℂ)) := rfl

theorem ψ_injective : Function.Injective ψ := by
  intro f g hfg
  rw [ψ_apply, ψ_apply] at hfg
  have h := HahnSeries.ofPowerSeries_injective hfg
  have h' : qExpansion 1 ((f : ℍ → ℂ) - (g : ℍ → ℂ)) = 0 := by
    rw [UpperHalfPlane.qExpansion_sub (an f) (an g), h, sub_self]
  have hn : Nice ((f : ℍ → ℂ) - (g : ℍ → ℂ)) := (f - g).2
  have h0 := (UpperHalfPlane.qExpansion_eq_zero_iff one_pos hn.1 hn.2.1 hn.2.2).mp h'
  exact Subtype.ext (sub_eq_zero.mp h0)

theorem ψ_eq_zero_iff (f : 𝒩) : ψ f = 0 ↔ f = 0 :=
  ⟨fun h => ψ_injective (by rw [h, map_zero]), fun h => by rw [h, map_zero]⟩

def toC : 𝒩 →ₐ[ℂ] (ℂ → ℂ) where
  toFun f := (f : ℍ → ℂ) ∘ ofComplex
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

theorem toC_apply (f : 𝒩) : toC f = (f : ℍ → ℂ) ∘ ofComplex := rfl

theorem analyticAt_toC (f : 𝒩) (τ : ℍ) : AnalyticAt ℂ (toC f) (τ : ℂ) := by
  have hd : DifferentiableOn ℂ ((f : ℍ → ℂ) ∘ ofComplex) {z : ℂ | 0 < z.im} :=
    UpperHalfPlane.mdifferentiable_iff.mp f.2.2.1
  exact hd.analyticAt ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds τ.im_pos)

theorem nice_of_modularForm {F : Type*} {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} [FunLike F ℍ ℂ]
    [ModularFormClass F Γ k] (f : F) (h1 : (1 : ℝ) ∈ Γ.strictPeriods) : Nice (f : ℍ → ℂ) := by
  haveI : Fact (IsCusp OnePoint.infty Γ) := ⟨Subgroup.isCusp_of_mem_strictPeriods one_pos h1⟩
  refine ⟨?_, ModularFormClass.holo f, ModularFormClass.bdd_at_infty f⟩
  simpa using SlashInvariantFormClass.periodic_comp_ofComplex (h := 1) f h1

def ofMF {F : Type*} {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} [FunLike F ℍ ℂ]
    [ModularFormClass F Γ k] (f : F) (h1 : (1 : ℝ) ∈ Γ.strictPeriods) : 𝒩 :=
  ⟨f, nice_of_modularForm f h1⟩

@[scoped simp] theorem coe_ofMF {F : Type*} {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} [FunLike F ℍ ℂ]
    [ModularFormClass F Γ k] (f : F) (h1 : (1 : ℝ) ∈ Γ.strictPeriods) :
    ((ofMF f h1 : 𝒩) : ℍ → ℂ) = f := rfl

theorem one_mem_strictPeriods_gamma0 (N : ℕ) :
    (1 : ℝ) ∈ (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (CongruenceSubgroup.Gamma0 N)).strictPeriods := by
  rw [CongruenceSubgroup.strictPeriods_Gamma0]
  exact AddSubgroup.mem_zmultiples 1

theorem coe_sum_smul {N : ℕ} {k : ℤ} {d : ℕ} (g : Fin d → ℂ)
    (f : Fin d → ModularForm (CongruenceSubgroup.Gamma0 N) k) :
    (⇑(∑ j, g j • f j) : ℍ → ℂ) = ∑ j, g j • (⇑(f j) : ℍ → ℂ) := by
  rw [show (⇑(∑ j, g j • f j) : ℍ → ℂ) =
      FunLike.coeAddMonoidHom (ModularForm (CongruenceSubgroup.Gamma0 N) k) ℍ ℂ (∑ j, g j • f j) from rfl,
    map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  change ⇑(g j • f j) = _
  funext z
  simp

theorem qExpansion_sum_smul {N : ℕ} {k : ℤ} {d : ℕ} (g : Fin d → ℂ)
    (f : Fin d → ModularForm (CongruenceSubgroup.Gamma0 N) k) :
    qExpansion 1 (⇑(∑ j, g j • f j) : ℍ → ℂ) = ∑ j, g j • qExpansion 1 (⇑(f j) : ℍ → ℂ) := by
  have h1 := one_mem_strictPeriods_gamma0 N
  have hR : ((∑ j, g j • ofMF (f j) h1 : 𝒩) : ℍ → ℂ) = ∑ j, g j • (⇑(f j) : ℍ → ℂ) := by
    change niceSubalgebra.val (∑ j, g j • ofMF (f j) h1) = _
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul]
    rfl
  calc qExpansion 1 (⇑(∑ j, g j • f j) : ℍ → ℂ) = qexpHom (∑ j, g j • ofMF (f j) h1) := by
        rw [qexpHom_apply, hR, coe_sum_smul]
    _ = ∑ j, g j • qexpHom (ofMF (f j) h1) := by rw [map_sum]; simp only [map_smul]
    _ = ∑ j, g j • qExpansion 1 (⇑(f j) : ℍ → ℂ) := rfl

theorem smul_eq_algebraMap_mul' {K : Type*} [Field K] (c : K) (G : LaurentSeries K) :
    c • G = algebraMap K (LaurentSeries K) c * G := by
  rw [ModularCurve.algebraMap_laurentSeries_eq_single, HahnSeries.single_zero_mul_eq_smul]

theorem coeffEmb_coeffMap_int (Z : LaurentSeries ℤ) :
    coeffEmb ℂ (coeffMap (Int.castRingHom ℚ) Z) = coeffMap (Int.castRingHom ℂ) Z := by
  change coeffMap (algebraMap ℚ ℂ) (coeffMap (Int.castRingHom ℚ) Z) = _
  rw [coeffMap_coeffMap]
  exact coeffMap_congr (RingHom.ext_int _ _) Z

theorem coeffEmb_jq_eq_coeffMap_int : coeffEmb ℂ jq = coeffMap (Int.castRingHom ℂ) (jqModC ℤ) := by
  have h : jq = coeffMap (Int.castRingHom ℚ) (jqModC ℤ) := by
    rw [← jqModC_rat, jqModC_eq_map_intCast]; rfl
  rw [h, coeffEmb_coeffMap_int]

theorem coeffEmb_jq : coeffEmb ℂ jq = jqModC ℂ := by
  change (jqModC ℚ).map (algebraMap ℚ ℂ) = jqModC ℂ
  exact map_jqModC _

theorem thetaL_coeffEmb_jq :
    thetaL ℂ (coeffEmb ℂ jq) =
      coeffMap (Int.castRingHom ℂ) (HahnSeries.single (1 : ℤ) (1 : ℤ) * LaurentSeries.derivative ℤ (jqModC ℤ)) := by
  rw [coeffEmb_jq_eq_coeffMap_int, ModularCurve.thetaL_coeffMap_eq_coeffMap_single_mul_derivative]

theorem thetaL_coeffEmb_jq_ne_zero : thetaL ℂ (coeffEmb ℂ jq) ≠ 0 := by
  intro h
  have hc : (thetaL ℂ (coeffEmb ℂ jq)).coeff (-1) = -1 := by
    rw [thetaL_apply, show (-1 : ℤ) = -2 + 1 by norm_num, HahnSeries.coeff_single_mul_add, one_mul,
      LaurentSeries.derivative_apply]
    simp [coeffEmb_coeff, coeff_jq_neg_one]
  rw [h] at hc
  simp at hc

theorem linearIndependent_coeffMap {k₀ k : Type*} [Field k₀] [Field k] (σ : k₀ →+* k) {n : ℕ}
    (v : Fin n → LaurentSeries k₀) (hv : LinearIndependent k₀ v) :
    LinearIndependent k (fun i => coeffMap σ (v i)) := by
  classical

  have hf : LinearIndependent k₀ (fun j => fun t : ℤ => (v j).coeff t) := by
    rw [Fintype.linearIndependent_iff] at hv ⊢
    intro g hg
    apply hv g
    ext t
    have := congrFun hg t
    simpa [Finset.sum_apply, Pi.smul_apply, HahnSeries.coeff_sum, HahnSeries.coeff_smul] using this
  obtain ⟨s, _, hdet⟩ := LinearIndependent.exists_det_submatrix_ne_zero _ hf
  rw [Fintype.linearIndependent_iff]
  intro g hg

  set M : Matrix (Fin n) (Fin n) k₀ := Matrix.of fun l j => (v j).coeff (s l) with hM
  have hdet' : (σ.mapMatrix M).det ≠ 0 := by
    rw [← RingHom.map_det]
    exact (map_ne_zero_iff σ σ.injective).mpr hdet
  have hmul : (σ.mapMatrix M).mulVec g = 0 := by
    ext l
    have := congrArg (fun x : LaurentSeries k => x.coeff (s l)) hg
    simp only [HahnSeries.coeff_sum, HahnSeries.coeff_smul, coeffMap_coeff, smul_eq_mul, HahnSeries.coeff_zero] at this
    rw [Matrix.mulVec, Pi.zero_apply, ← this]
    simp [dotProduct, hM, mul_comm]
  have := Matrix.eq_zero_of_mulVec_eq_zero hdet' hmul
  exact fun i => congrFun this i

end B2Head
p2m_reactivate "P2MW.S_ModularForm_exists_linearIndependent_int_qCoeff_dimFormula_le_card.B2Head"

open B2Head in
theorem solution (N : ℕ) [NeZero N] (m : ℕ) (hm : 1 ≤ m) :
    ∃ (d : ℕ) (f : Fin d → ModularForm (CongruenceSubgroup.Gamma0 N) (2 * (m : ℤ))) (a : Fin d → ℕ → ℤ),
      (∀ i n, ModularFormClass.qCoeff (f i) n = (a i n : ℂ)) ∧ LinearIndependent ℂ f ∧
      (2 * (m : ℚ) - 1) * (ModularCurve.genusFormula N - 1)
        + ((m / 2 : ℕ) : ℚ) * (ModularCurve.nuTwo N : ℚ) + ((2 * m / 3 : ℕ) : ℚ) * (ModularCurve.nuThree N : ℚ)
        + (m : ℚ) * (ModularCurve.cuspCount N : ℚ) ≤ (d : ℚ) := by
  classical

  obtain ⟨d, Y, hYF, hYB, hYli, hd⟩ := ModularCurve.exists_linearIndependent_isModPFormFn_rat_dimFormula_le_card N m hm

  choose c Z hc hZ using fun i => ModularCurve.exists_ne_zero_coeffMap_eq_mul_of_isModPFormFn N m (Y i) (hYF i) (hYB i)

  set v : Fin d → LaurentSeries ℚ := fun i => algebraMap ℚ (LaurentSeries ℚ) (c i : ℚ) * Y i with hv
  set X : Fin d → LaurentSeries ℂ := fun i => coeffEmb ℂ (v i) with hX
  have hXmem : ∀ i, X i ∈ laurentBaseChange ℂ (modularFunctionFieldFull N) := fun i =>
    coeffEmb_mem_laurentBaseChange ℂ (mul_mem (IntermediateField.algebraMap_mem _ _) (hYF i))
  have hvB : ∀ i, IsModPFormFn ℚ m (v i) := fun i => by
    have h := (ModularCurve.isModPFormFn_zero_and_add_and_smul ℚ m).2.2 (c i : ℚ) (Y i) (hYB i)
    rwa [smul_eq_algebraMap_mul'] at h
  have hXB : ∀ i, IsModPFormFn ℂ m (X i) := fun i =>
    ModularCurve.IsModPFormFn.coeffMap (algebraMap ℚ ℂ) m (v i) (hvB i)

  have hf : ∀ i, ∃ f : ModularForm (CongruenceSubgroup.Gamma0 N) (2 * (m : ℤ)),
      HahnSeries.ofPowerSeries ℤ ℂ (qExpansion 1 f) = X i * thetaL ℂ (coeffEmb ℂ jq) ^ m := fun i => by
    have h := hXB i
    unfold IsModPFormFn at h
    rw [← coeffEmb_jq] at h
    exact ModularCurve.exists_modularForm_qExpansion_eq_mul_thetaL_pow_of_isIntegral N m hm (X i) (hXmem i) h.1 h.2
  choose f hf using hf

  set W : Fin d → LaurentSeries ℤ := fun i =>
    Z i * (HahnSeries.single (1 : ℤ) (1 : ℤ) * LaurentSeries.derivative ℤ (jqModC ℤ)) ^ m with hW
  have hWX : ∀ i, coeffMap (Int.castRingHom ℂ) (W i) = X i * thetaL ℂ (coeffEmb ℂ jq) ^ m := fun i => by
    show coeffMap (Int.castRingHom ℂ) (Z i * (HahnSeries.single (1 : ℤ) (1 : ℤ) *
      LaurentSeries.derivative ℤ (jqModC ℤ)) ^ m) = coeffEmb ℂ (algebraMap ℚ (LaurentSeries ℚ) (c i : ℚ) * Y i) * _
    rw [map_mul, map_pow, ← thetaL_coeffEmb_jq, ← coeffEmb_coeffMap_int, hZ i]
  refine ⟨d, f, fun i n => (W i).coeff n, ?_, ?_, hd⟩
  · intro i n
    simp only [ModularFormClass.qCoeff]
    rw [← HahnSeries.ofPowerSeries_apply_coeff (Γ := ℤ), hf i, ← hWX i, coeffMap_coeff, eq_intCast]
  ·
    rw [Fintype.linearIndependent_iff]
    intro g hg

    have h1 : ∑ j, g j • qExpansion 1 (⇑(f j) : ℍ → ℂ) = 0 := by
      rw [← qExpansion_sum_smul, hg, ModularForm.coe_zero, UpperHalfPlane.qExpansion_zero]
    have h2 : (∑ j, g j • X j) * thetaL ℂ (coeffEmb ℂ jq) ^ m = 0 := by
      have := congrArg (HahnSeries.ofPowerSeries ℤ ℂ) h1
      rw [map_sum, map_zero] at this
      rw [Finset.sum_mul, ← this]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [PowerSeries.smul_eq_C_mul, map_mul, HahnSeries.ofPowerSeries_C, hf j, ← HahnSeries.C_mul_eq_smul, mul_assoc]
    have h3 : ∑ j, g j • X j = 0 :=
      (mul_eq_zero.mp h2).resolve_right (pow_ne_zero _ thetaL_coeffEmb_jq_ne_zero)

    have hvli : LinearIndependent ℚ v := by
      rw [Fintype.linearIndependent_iff] at hYli ⊢
      intro g' hg' i
      have h' : ∑ j, (g' j * (c j : ℚ)) • Y j = 0 := by
        rw [← hg']
        refine Finset.sum_congr rfl fun j _ => ?_
        show (g' j * (c j : ℚ)) • Y j = g' j • (algebraMap ℚ (LaurentSeries ℚ) (c j : ℚ) * Y j)
        rw [mul_smul, smul_eq_algebraMap_mul' (c j : ℚ)]
      have := hYli _ h' i
      exact (mul_eq_zero.mp this).resolve_right (Int.cast_ne_zero.mpr (hc i))
    have hXli : LinearIndependent ℂ X := linearIndependent_coeffMap (algebraMap ℚ ℂ) v hvli
    exact (Fintype.linearIndependent_iff.mp hXli) g h3

end
p2m_reactivate "P2MW.S_ModularForm_exists_linearIndependent_int_qCoeff_dimFormula_le_card.B2Head"

end S_ModularForm_exists_linearIndependent_int_qCoeff_dimFormula_le_card
end P2MW
export P2MW.S_ModularForm_exists_linearIndependent_int_qCoeff_dimFormula_le_card (solution)
