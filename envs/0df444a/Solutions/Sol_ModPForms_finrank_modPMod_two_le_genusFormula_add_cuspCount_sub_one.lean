-- Prove2me | solution 1 for ModPForms.finrank_modPMod_two_le_genusFormula_add_cuspCount_sub_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/a11588c1-6ad1-57ef-a49a-224525531fef

import Definitions.Def_CuspForm_ModPForms
import Definitions.Def_ModularCurve_GenusNumerics
import Theorems.Thm_ModPForms_card_le_finrank_modPMod_of_linearIndependent
import Theorems.Thm_ModPForms_exists_isModPFormFn_qexpOfWeight_eq_of_mem_modPMod
import Theorems.Thm_ModularCurve_modularFunctionFieldC_eq_modularFunctionFieldFullC
import Theorems.Thm_ModularCurve_card_le_dimFormula_of_isModPFormFn_of_linearIndependent
import Definitions.Def_ModularCurve_ModPFormFn
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModPForms_finrank_modPMod_two_le_genusFormula_add_cuspCount_sub_one
p2m_attr_erase "instance" "ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup ModularCurve.instIsElliptic_tateLaurent ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff"
p2m_attr_erase "simp" "ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.ProjectiveLine.map_mk ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule HahnSeries.ramScale_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial"
p2m_attr_erase "simp" "WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace"
p2m_attr_erase "simp" "AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU"
p2m_attr_erase "simp" "WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero"
p2m_attr_erase "simp" "TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff"

set_option autoImplicit false

namespace AnchorRed

open scoped MatrixGroups

private theorem ar_T_mem (N : ℕ) : ModularGroup.T ∈ CongruenceSubgroup.Gamma0 N := by
  simp [CongruenceSubgroup.Gamma0_mem, ModularGroup.coe_T]

private theorem ar_one_mem (N : ℕ) :
    (1 : ℝ) ∈ (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  rw [← Subgroup.strictWidthInfty_eq_one_of_T_mem (ar_T_mem N)]
  exact Subgroup.strictWidthInfty_mem_strictPeriods _

private theorem ar_qCoeff_add (N : ℕ) (f g : ModularForm (CongruenceSubgroup.Gamma0 N) 2) (n : ℕ) :
    ModularFormClass.qCoeff (⇑(f + g)) n = ModularFormClass.qCoeff (⇑f) n + ModularFormClass.qCoeff (⇑g) n := by
  unfold ModularFormClass.qCoeff
  rw [ModularForm.coe_add, UpperHalfPlane.qExpansion_add
    (ModularFormClass.analyticAt_cuspFunction_zero f one_pos (ar_one_mem N))
    (ModularFormClass.analyticAt_cuspFunction_zero g one_pos (ar_one_mem N)), map_add]

private theorem ar_qCoeff_smul (N : ℕ) (c : ℂ) (f : ModularForm (CongruenceSubgroup.Gamma0 N) 2) (n : ℕ) :
    ModularFormClass.qCoeff (⇑(c • f)) n = c * ModularFormClass.qCoeff (⇑f) n := by
  unfold ModularFormClass.qCoeff
  rw [ModularForm.IsGLPos.coe_smul, UpperHalfPlane.qExpansion_smul
    (ModularFormClass.analyticAt_cuspFunction_zero f one_pos (ar_one_mem N)) c, map_smul, smul_eq_mul]

private noncomputable def ar_L (N : ℕ) : ModularForm (CongruenceSubgroup.Gamma0 N) 2 →ₗ[ℂ] (ℕ → ℂ) where
  toFun f := fun n => ModularFormClass.qCoeff (⇑f) n
  map_add' f g := funext fun n => ar_qCoeff_add N f g n
  map_smul' c f := funext fun n => by
    rw [RingHom.id_apply, Pi.smul_apply, smul_eq_mul]
    exact ar_qCoeff_smul N c f n

private theorem ar_L_apply (N : ℕ) (f : ModularForm (CongruenceSubgroup.Gamma0 N) 2) (n : ℕ) :
    ar_L N f n = ModularFormClass.qCoeff (⇑f) n :=
  rfl

private theorem ar_int_li {ι : Type} (F : Type) [Field F] (a : ι → ℕ → ℤ)
    (h : LinearIndependent F (fun i => (fun n => (a i n : F)))) :
    LinearIndependent ℤ a := by
  rw [linearIndependent_iff'] at h ⊢
  suffices key : ∀ (k : ℕ) (s : Finset ι) (m : ι → ℤ), (∑ i ∈ s, (m i).natAbs) = k →
      ∑ i ∈ s, m i • a i = 0 → ∀ i ∈ s, m i = 0 from
    fun s m hm => key _ s m rfl hm
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro s m hk hm

  have hF : ∑ i ∈ s, ((m i : ℤ) : F) • (fun n => (a i n : F)) = 0 := by
    funext n
    have h1 := congrFun hm n
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h1 ⊢
    have h2 := congrArg (Int.cast : ℤ → F) h1
    push_cast at h2
    exact h2
  have hzero : ∀ i ∈ s, ((m i : ℤ) : F) = 0 := h s _ hF
  obtain ⟨p, hp⟩ := CharP.exists F
  rcases Nat.eq_zero_or_pos p with rfl | hpos
  · haveI : CharZero F := CharP.charP_to_charZero F
    intro i hi
    exact_mod_cast hzero i hi
  · have hprime : p.Prime := (CharP.char_is_prime_or_zero F p).resolve_right hpos.ne'
    have hdvd : ∀ i ∈ s, (p : ℤ) ∣ m i := fun i hi => (CharP.intCast_eq_zero_iff F p (m i)).mp (hzero i hi)
    by_cases hm0 : ∀ i ∈ s, m i = 0
    · exact hm0
    ·
      obtain ⟨j, hj, hj0⟩ : ∃ j, j ∈ s ∧ ¬ m j = 0 := by
        simpa only [not_forall, Classical.not_imp, exists_prop] using hm0
      classical
      let m' : ι → ℤ := fun i => if hi : i ∈ s then (hdvd i hi).choose else 0
      have hm' : ∀ i ∈ s, m i = (p : ℤ) * m' i := fun i hi => by
        simp only [m', dif_pos hi]
        exact (hdvd i hi).choose_spec
      have hsum : ∑ i ∈ s, m' i • a i = 0 := by
        have hps : (p : ℤ) • ∑ i ∈ s, m' i • a i = 0 := by
          rw [Finset.smul_sum]
          have : ∑ i ∈ s, (p : ℤ) • m' i • a i = ∑ i ∈ s, m i • a i :=
            Finset.sum_congr rfl fun i hi => by rw [smul_smul, ← hm' i hi]
          rw [this, hm]
        rcases smul_eq_zero.mp hps with h0 | h0
        · exact absurd (by exact_mod_cast h0 : p = 0) hprime.ne_zero
        · exact h0
      have hle : ∀ i ∈ s, (m' i).natAbs ≤ (m i).natAbs := fun i hi => by
        rw [hm' i hi, Int.natAbs_mul, Int.natAbs_natCast]
        exact Nat.le_mul_of_pos_left _ hpos
      have hj' : m' j ≠ 0 := fun h0 => hj0 (by rw [hm' j hj, h0, mul_zero])
      have hltj : (m' j).natAbs < (m j).natAbs := by
        rw [hm' j hj, Int.natAbs_mul, Int.natAbs_natCast]
        have hpos' : 0 < (m' j).natAbs := Int.natAbs_pos.mpr hj'
        calc (m' j).natAbs = 1 * (m' j).natAbs := (one_mul _).symm
          _ < p * (m' j).natAbs := Nat.mul_lt_mul_of_pos_right hprime.one_lt hpos'
      have hlt : (∑ i ∈ s, (m' i).natAbs) < k := by
        rw [← hk]
        exact Finset.sum_lt_sum hle ⟨j, hj, hltj⟩
      have hzero' := ih _ hlt s m' rfl hsum
      intro i hi
      rw [hm' i hi, hzero' i hi, mul_zero]

private theorem ar_rat_li {ι : Type} (a : ι → ℕ → ℤ) (h : LinearIndependent ℤ a) :
    LinearIndependent ℚ (fun i => (fun n => (a i n : ℚ))) := by
  let j : (ℕ → ℤ) →ₗ[ℤ] (ℕ → ℚ) := ((Int.castRingHom ℚ).compLeft ℕ).toIntLinearMap
  have hj : LinearMap.ker j = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro v hv
    funext n
    have := congrFun hv n
    simpa [j] using this
  have h1 : LinearIndependent ℤ (fun i => (fun n => (a i n : ℚ))) := by
    have := h.map' j hj
    convert this using 1 <;> first | rfl | exact Subsingleton.elim _ _
  exact (LinearIndependent.iff_fractionRing ℤ ℚ).mp h1

private theorem ar_complex_li {ι : Type} (w : ι → ℕ → ℚ) (h : LinearIndependent ℚ w) :
    LinearIndependent ℂ (fun i => (fun n => (w i n : ℂ))) := by
  rw [linearIndependent_iff'] at h ⊢
  intro s g hg i hi
  let B := Module.Basis.ofVectorSpace ℚ ℂ
  refine B.ext_elem fun α => ?_
  rw [map_zero, Finsupp.zero_apply]
  have key : ∑ j ∈ s, (B.repr (g j) α) • w j = 0 := by
    funext n
    have h1 := congrFun hg n
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h1 ⊢
    have h2 := congrArg (B.coord α) h1
    rw [map_sum, map_zero] at h2
    have h3 : ∀ j, (B.coord α) (g j * (w j n : ℂ)) = w j n * (B.repr (g j)) α := fun j => by
      rw [mul_comm, ← Rat.smul_def, map_smul, smul_eq_mul, Module.Basis.coord_apply]
    simpa only [h3, mul_comm (w _ n)] using h2
  exact h s _ key i hi

private theorem ar_ofPowerSeries_smul (K : Type) [Field K] (c : K) (φ : PowerSeries K) :
    HahnSeries.ofPowerSeries ℤ K (c • φ) = c • HahnSeries.ofPowerSeries ℤ K φ := by
  rw [PowerSeries.smul_eq_C_mul, map_mul, HahnSeries.ofPowerSeries_C, HahnSeries.C_mul_eq_smul]

private noncomputable def ar_Lps (K : Type) [Field K] : PowerSeries K →ₗ[K] LaurentSeries K where
  toFun := HahnSeries.ofPowerSeries ℤ K
  map_add' := map_add _
  map_smul' c φ := ar_ofPowerSeries_smul K c φ

private theorem ar_Lps_ker (K : Type) [Field K] : LinearMap.ker (ar_Lps K) = ⊥ :=
  LinearMap.ker_eq_bot.mpr HahnSeries.ofPowerSeries_injective

set_option synthInstance.maxHeartbeats 1600000 in
open ModPForms in

private theorem ar_bound (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (N : ℕ) [NeZero N] (hpN : ¬ p ∣ N)
    (K : Type) [Field K] [CharP K p] [IsAlgClosed K] :
    (Module.finrank K ↥(modPMod N 2 K) : ℚ) ≤ ModularCurve.genusFormula N + (ModularCurve.cuspCount N : ℚ) - 1 := by
  classical

  have hRHS : (0 : ℚ) ≤ ModularCurve.genusFormula N + (ModularCurve.cuspCount N : ℚ) - 1 := by
    have h := ModularCurve.card_le_dimFormula_of_isModPFormFn_of_linearIndependent p hp5 N hpN K 1 le_rfl
      (ι := PEmpty) (fun i => i.elim) (fun i => i.elim) linearIndependent_empty_type
    norm_num at h
    linarith
  by_cases hfin : Module.Finite K ↥(modPMod N 2 K)
  swap
  · rw [Module.finrank_of_not_finite hfin, Nat.cast_zero]
    exact hRHS

  set S : Set (PowerSeries K) := {φ | ∃ (f : ModularForm (CongruenceSubgroup.Gamma0 N) 2) (a : ℕ → ℤ),
      (∀ n, ModularFormClass.qCoeff f n = (a n : ℂ)) ∧ φ = PowerSeries.mk fun n => ((a n : ℤ) : K)} with hS
  have hV : modPMod N 2 K = Submodule.span K S := rfl
  obtain ⟨t, htS, hspan, hli⟩ := exists_linearIndependent K S
  have hrange : Set.range ((↑) : t → PowerSeries K) = t := Subtype.range_coe
  let bV : Module.Basis t K ↥(Submodule.span K S) :=
    (Module.Basis.span hli).map (LinearEquiv.ofEq _ _ (by rw [hrange, hspan]))
  haveI : Module.Finite K ↥(Submodule.span K S) := hfin
  haveI : Finite t := Module.Finite.finite_basis bV
  letI : Fintype t := Fintype.ofFinite t
  have hfr : Module.finrank K ↥(modPMod N 2 K) = Fintype.card t := by
    rw [hV, Module.finrank_eq_card_basis bV]

  have hmem : ∀ φ : t, (φ : PowerSeries K) ∈ modPMod N (2 * ((1 : ℕ) : ℤ)) K := fun φ => by
    have h2 : (2 * ((1 : ℕ) : ℤ)) = 2 := by norm_num
    rw [h2, hV]
    exact Submodule.subset_span (htS φ.2)
  choose G hG hq using fun φ : t =>
    ModPForms.exists_isModPFormFn_qexpOfWeight_eq_of_mem_modPMod p N hpN K 1 (φ : PowerSeries K) (hmem φ)

  have hGθ : ∀ i : t, (G i : LaurentSeries K) * ModularCurve.thetaJ K =
      HahnSeries.ofPowerSeries ℤ K (i : PowerSeries K) := fun i => by
    rw [← pow_one (ModularCurve.thetaJ K), ← zpow_natCast]
    exact hq i
  have hliG : LinearIndependent K G := by
    rw [linearIndependent_iff']
    intro s c hc i hi
    refine (linearIndependent_iff'.mp hli) s c ?_ i hi
    apply HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := K)
    have h := congrArg
      (fun x : ↥(ModularCurve.modularFunctionFieldC K N) => (x : LaurentSeries K) * ModularCurve.thetaJ K) hc
    simp only [ZeroMemClass.coe_zero, zero_mul] at h
    rw [map_sum, map_zero, ← h, AddSubmonoidClass.coe_finsetSum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    have e1 : HahnSeries.ofPowerSeries ℤ K (c i • (i : PowerSeries K)) =
        algebraMap K (LaurentSeries K) (c i) * HahnSeries.ofPowerSeries ℤ K (i : PowerSeries K) := by
      rw [Algebra.smul_def, map_mul]
      rfl
    have e2 : ((c i • G i : ↥(ModularCurve.modularFunctionFieldC K N)) : LaurentSeries K) =
        algebraMap K (LaurentSeries K) (c i) * (G i : LaurentSeries K) := by
      rw [Algebra.smul_def, MulMemClass.coe_mul]
      congr 1
    rw [e1, e2, mul_assoc, hGθ i]

  have hCF := ModularCurve.modularFunctionFieldC_eq_modularFunctionFieldFullC K p N hpN
  clear hGθ hq
  revert G hG hliG
  rw [hCF]
  intro G hG hliG
  have h4 := ModularCurve.card_le_dimFormula_of_isModPFormFn_of_linearIndependent p hp5 N hpN K 1 le_rfl G hG hliG
  rw [hfr]
  generalize ((Fintype.card t : ℕ) : ℚ) = d at h4 ⊢
  norm_num at h4
  linarith

end AnchorRed

open ModPForms AnchorRed in

theorem solution (N : ℕ) [NeZero N]
    (F : Type) [Field F] :
    (Module.finrank F ↥(modPMod N 2 F) : ℚ) ≤
      ModularCurve.genusFormula N + (ModularCurve.cuspCount N : ℚ) - 1 := by
  classical

  set S : Set (PowerSeries F) := {φ | ∃ (f : ModularForm (CongruenceSubgroup.Gamma0 N) 2) (a : ℕ → ℤ),
      (∀ n, ModularFormClass.qCoeff f n = (a n : ℂ)) ∧ φ = PowerSeries.mk fun n => ((a n : ℤ) : F)} with hS
  have hV : modPMod N 2 F = Submodule.span F S := rfl

  obtain ⟨p, hpge, hpr⟩ := Nat.exists_infinite_primes (max N 4 + 1)
  haveI : Fact p.Prime := ⟨hpr⟩
  have hp5 : 5 ≤ p := by
    have := le_max_right N 4
    omega
  have hpN : ¬ p ∣ N := fun h => by
    have := Nat.le_of_dvd (NeZero.pos N) h
    have := le_max_left N 4
    omega
  have hbound := ar_bound p hp5 N hpN (AlgebraicClosure (ZMod p))
  by_cases hfin : Module.Finite F ↥(modPMod N 2 F)
  swap
  · rw [Module.finrank_of_not_finite hfin, Nat.cast_zero]
    exact (Nat.cast_nonneg _).trans hbound

  obtain ⟨b, hbS, hspan, hli⟩ := exists_linearIndependent F S
  have hrange : Set.range ((↑) : b → PowerSeries F) = b := Subtype.range_coe
  let bV : Module.Basis b F ↥(Submodule.span F S) :=
    (Module.Basis.span hli).map (LinearEquiv.ofEq _ _ (by rw [hrange, hspan]))
  haveI : Module.Finite F ↥(Submodule.span F S) := hfin
  haveI : Finite b := Module.Finite.finite_basis bV
  letI : Fintype b := Fintype.ofFinite b

  have hb : ∀ φ : b, ∃ (f : ModularForm (CongruenceSubgroup.Gamma0 N) 2) (a : ℕ → ℤ),
      (∀ n, ModularFormClass.qCoeff f n = (a n : ℂ)) ∧
        (φ : PowerSeries F) = PowerSeries.mk fun n => ((a n : ℤ) : F) :=
    fun φ => hbS φ.2
  choose f a hfa hφ using hb

  have hliF : LinearIndependent F (fun φ : b => fun n => (a φ n : F)) := by
    let L : PowerSeries F →ₗ[F] (ℕ → F) := LinearMap.pi fun n => PowerSeries.coeff n
    have hinj : LinearMap.ker L = ⊥ := by
      rw [LinearMap.ker_eq_bot']
      intro ψ hψ
      ext n
      simpa [L] using congrFun hψ n
    have hL : ∀ φ : b, L (φ : PowerSeries F) = fun n => (a φ n : F) := fun φ => by
      funext n
      simp only [L, LinearMap.pi_apply, hφ φ, PowerSeries.coeff_mk]
    have := hli.map' L hinj
    convert this using 1 <;> first | rfl | exact Subsingleton.elim _ _ | (funext φ; exact (hL φ).symm)

  have hliC : LinearIndependent ℂ (fun φ : b => fun n => (a φ n : ℂ)) := by
    have h1 := ar_complex_li _ (ar_rat_li a (ar_int_li F a hliF))
    simpa only [Rat.cast_intCast] using h1
  have hlif : LinearIndependent ℂ f := by
    apply LinearIndependent.of_comp (ar_L N)
    convert hliC using 1
    funext φ n
    rw [Function.comp_apply, ar_L_apply]
    exact hfa φ n

  have hfr : Module.finrank F ↥(modPMod N 2 F) = Fintype.card b := by
    rw [hV, Module.finrank_eq_card_basis bV]
  have hcard : Fintype.card b ≤ Module.finrank (AlgebraicClosure (ZMod p)) ↥(modPMod N 2 (AlgebraicClosure (ZMod p))) :=
    ModPForms.card_le_finrank_modPMod_of_linearIndependent N 2 (AlgebraicClosure (ZMod p)) f a hfa hlif
  rw [hfr]
  exact le_trans (by exact_mod_cast hcard) hbound

end S_ModPForms_finrank_modPMod_two_le_genusFormula_add_cuspCount_sub_one
end P2MW
export P2MW.S_ModPForms_finrank_modPMod_two_le_genusFormula_add_cuspCount_sub_one (solution)
