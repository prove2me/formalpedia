-- Prove2me | solution 1 for ModularCurve.exists_linearIndependent_isModPFormFn_rat_dimFormula_le_card
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/5eead2a8-c566-5f58-b0e6-ff0665b239b2

import Mathlib
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_ModPFormFn
import Definitions.Def_ModularCurve_GenusNumerics
import Theorems.Thm_ModularCurve_exists_linearIndependent_isModPFormFn_algebraicClosure_dimFormula_le_card
import Theorems.Thm_ModularCurve_exists_isGalois_forall_coeffMap_eq_of_mem_laurentBaseChange
import Theorems.Thm_ModularCurve_exists_rational_basis_isModPFormFn_of_forall_coeffMap_mem
import Theorems.Thm_ModularCurve_isModPFormFn_zero_and_add_and_smul
import Theorems.Thm_ModularCurve_IsModPFormFn_coeffMap
import Theorems.Thm_ModularCurve_IsModPFormFn_of_coeffMap_algebraMap
import Theorems.Thm_ModularCurve_laurentBaseChange_modularFunctionFieldFull_eq_modularFunctionFieldFullC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_linearIndependent_isModPFormFn_rat_dimFormula_le_card
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular"
p2m_attr_erase "simp" "AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois ModularCurve.coe_cuspidalDivisor₀ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul HahnSeries.ramScale_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂"
p2m_attr_erase "simp" "PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen"
p2m_attr_erase "simp" "ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluQuotientOfSums_a₂"
p2m_attr_erase "simp" "WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq"
p2m_attr_erase "simp" "WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff"
set_option autoImplicit false
p2m_open "ModularCurve P2MW.S_ModularCurve_exists_linearIndependent_isModPFormFn_rat_dimFormula_le_card.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "modularFunctionFieldFull IsModPFormFn nuTwo nuThree cuspCount genusFormula exists_linearIndependent_isModPFormFn_algebraicClosure_dimFormula_le_card modularFunctionFieldFullC coeffMap coeffMap_coeff algebraMap_laurentSeries_eq_single coeffEmb laurentBaseChange coeffMap_mem_laurentBaseChange exists_isGalois_forall_coeffMap_eq_of_mem_laurentBaseChange exists_rational_basis_isModPFormFn_of_forall_coeffMap_mem isModPFormFn_zero_and_add_and_smul IsModPFormFn.coeffMap IsModPFormFn.of_coeffMap_algebraMap laurentBaseChange_modularFunctionFieldFull_eq_modularFunctionFieldFullC"
p2m_open "ModularCurve"

private theorem coeffMap_algEquiv_smul {E : Type*} [Field E] [Algebra ℚ E] (σ : E ≃ₐ[ℚ] E) (a : E) (x : LaurentSeries E) :
    coeffMap (σ : E →+* E) (a • x) = σ a • coeffMap (σ : E →+* E) x := by
  ext k
  simp [coeffMap_coeff]

private theorem coeffMap_algEquiv_mul {E : Type*} [Field E] [Algebra ℚ E] (σ τ : E ≃ₐ[ℚ] E) (x : LaurentSeries E) :
    coeffMap ((σ * τ : E ≃ₐ[ℚ] E) : E →+* E) x = coeffMap (σ : E →+* E) (coeffMap (τ : E →+* E) x) := by
  ext k
  simp [coeffMap_coeff, AlgEquiv.mul_apply]

private theorem coeffMap_algEquiv_one {E : Type*} [Field E] [Algebra ℚ E] (x : LaurentSeries E) :
    coeffMap ((1 : E ≃ₐ[ℚ] E) : E →+* E) x = x := by
  ext k
  simp [coeffMap_coeff]

private theorem coeffMap_mem_span_orbit {E : Type*} [Field E] [Algebra ℚ E] {d : ℕ} (y : Fin d → LaurentSeries E)
    (σ : E ≃ₐ[ℚ] E) (x : LaurentSeries E)
    (hx : x ∈ Submodule.span E (Set.range fun p : (E ≃ₐ[ℚ] E) × Fin d => coeffMap (p.1 : E →+* E) (y p.2))) :
    coeffMap (σ : E →+* E) x ∈
      Submodule.span E (Set.range fun p : (E ≃ₐ[ℚ] E) × Fin d => coeffMap (p.1 : E →+* E) (y p.2)) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨τ, i⟩, rfl⟩ := hx
    refine Submodule.subset_span ⟨(σ * τ, i), ?_⟩
    exact coeffMap_algEquiv_mul σ τ (y i)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x x' _ _ hx hx' => rw [map_add]; exact Submodule.add_mem _ hx hx'
  | smul a x _ hx => rw [coeffMap_algEquiv_smul]; exact Submodule.smul_mem _ _ hx

private theorem mem_laurentBaseChange_of_mem_span_orbit {E : Type*} [Field E] [Algebra ℚ E]
    (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) {d : ℕ} (y : Fin d → LaurentSeries E)
    (hyF : ∀ i, y i ∈ laurentBaseChange E F₀) (x : LaurentSeries E)
    (hx : x ∈ Submodule.span E (Set.range fun p : (E ≃ₐ[ℚ] E) × Fin d => coeffMap (p.1 : E →+* E) (y p.2))) :
    x ∈ laurentBaseChange E F₀ := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨τ, i⟩, rfl⟩ := hx
    exact coeffMap_mem_laurentBaseChange τ (hyF i)
  | zero => exact zero_mem _
  | add x x' _ _ hx hx' => exact add_mem hx hx'
  | smul a x _ hx =>
    have h1 : a • x = algebraMap E (LaurentSeries E) a * x := by
      ext k
      rw [algebraMap_laurentSeries_eq_single]
      simp
    rw [h1]
    exact mul_mem (IntermediateField.algebraMap_mem _ a) hx

private theorem isModPFormFn_of_mem_span_orbit {E : Type*} [Field E] [Algebra ℚ E] (m : ℕ) {d : ℕ}
    (y : Fin d → LaurentSeries E) (hyB : ∀ i, IsModPFormFn E m (y i)) (x : LaurentSeries E)
    (hx : x ∈ Submodule.span E (Set.range fun p : (E ≃ₐ[ℚ] E) × Fin d => coeffMap (p.1 : E →+* E) (y p.2))) :
    IsModPFormFn E m x := by
  obtain ⟨h0, hadd, hsmul⟩ := isModPFormFn_zero_and_add_and_smul E m
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨τ, i⟩, rfl⟩ := hx
    exact IsModPFormFn.coeffMap (τ : E →+* E) m (y i) (hyB i)
  | zero => exact h0
  | add x x' _ _ hx hx' => exact hadd x x' hx hx'
  | smul a x _ hx => exact hsmul a x hx

private theorem linearIndependent_of_coeffMap {E K : Type*} [Field E] [Field K] (φ : E →+* K) {d : ℕ}
    (y : Fin d → LaurentSeries E) (x : Fin d → LaurentSeries K) (hyx : ∀ i, coeffMap φ (y i) = x i)
    (hx : ∀ c : Fin d → K, ∑ i, algebraMap K (LaurentSeries K) (c i) * x i = 0 → ∀ i, c i = 0) :
    LinearIndependent E y := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have h := congrArg (coeffMap φ) hg
  rw [map_sum, map_zero] at h
  have h' : ∑ j, algebraMap K (LaurentSeries K) (φ (g j)) * x j = 0 := by
    rw [← h]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← hyx j, algebraMap_laurentSeries_eq_single]
    ext k
    simp [coeffMap_coeff]
  exact (map_eq_zero_iff φ φ.injective).mp (hx _ h' i)

private theorem card_le_of_linearIndependent_of_mem_span {E : Type*} [Field E] {M : Type*} [AddCommGroup M] [Module E M]
    {d n : ℕ} (y : Fin d → M) (hy : LinearIndependent E y) (b : Fin n → M) (hb : LinearIndependent E b)
    (hmem : ∀ i, y i ∈ Submodule.span E (Set.range b)) : d ≤ n := by
  classical
  haveI : Module.Finite E (Submodule.span E (Set.range b)) := FiniteDimensional.span_of_finite E (Set.finite_range b)
  have hli : LinearIndependent E (fun i => (⟨y i, hmem i⟩ : Submodule.span E (Set.range b))) :=
    LinearIndependent.of_comp (Submodule.span E (Set.range b)).subtype (by exact hy)
  have h1 := hli.fintype_card_le_finrank
  rw [finrank_span_eq_card hb, Fintype.card_fin, Fintype.card_fin] at h1
  exact h1

end ModularCurve

namespace ModularCurve
p2m_export "ModularCurve" "modularFunctionFieldFull IsModPFormFn nuTwo nuThree cuspCount genusFormula exists_linearIndependent_isModPFormFn_algebraicClosure_dimFormula_le_card modularFunctionFieldFullC coeffMap coeffMap_coeff algebraMap_laurentSeries_eq_single coeffEmb laurentBaseChange coeffMap_mem_laurentBaseChange exists_isGalois_forall_coeffMap_eq_of_mem_laurentBaseChange exists_rational_basis_isModPFormFn_of_forall_coeffMap_mem isModPFormFn_zero_and_add_and_smul IsModPFormFn.coeffMap IsModPFormFn.of_coeffMap_algebraMap laurentBaseChange_modularFunctionFieldFull_eq_modularFunctionFieldFullC"
p2m_open "ModularCurve"

private theorem exists_rational_family_of_definedOver {E K : Type*} [Field E] [Algebra ℚ E] [FiniteDimensional ℚ E]
    [IsGalois ℚ E] [Field K] [Algebra E K] [Algebra.IsAlgebraic E K]
    (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) (m d : ℕ) (y : Fin d → LaurentSeries E)
    (hyF : ∀ i, y i ∈ laurentBaseChange E F₀)
    (x : Fin d → LaurentSeries K) (hyx : ∀ i, coeffMap (algebraMap E K) (y i) = x i)
    (hxB : ∀ i, IsModPFormFn K m (x i))
    (hxli : ∀ c : Fin d → K, ∑ i, algebraMap K (LaurentSeries K) (c i) * x i = 0 → ∀ i, c i = 0) :
    ∃ (n : ℕ) (Y : Fin n → LaurentSeries ℚ),
      (∀ i, Y i ∈ F₀) ∧ (∀ i, IsModPFormFn ℚ m (Y i)) ∧ LinearIndependent ℚ Y ∧ d ≤ n := by
  classical

  have hyB : ∀ i, IsModPFormFn E m (y i) := fun i =>
    IsModPFormFn.of_coeffMap_algebraMap (K₀ := E) (K := K) m (y i) ((hyx i).symm ▸ hxB i)

  haveI : FiniteDimensional E
      (Submodule.span E (Set.range fun p : (E ≃ₐ[ℚ] E) × Fin d => coeffMap (p.1 : E →+* E) (y p.2))) :=
    FiniteDimensional.span_of_finite E (Set.finite_range _)
  obtain ⟨n, Y, hYF, hYB, hYli, hYliL, hspan⟩ :=
    ModularCurve.exists_rational_basis_isModPFormFn_of_forall_coeffMap_mem E F₀ m
      (Submodule.span E (Set.range fun p : (E ≃ₐ[ℚ] E) × Fin d => coeffMap (p.1 : E →+* E) (y p.2)))
      (fun σ x hx => coeffMap_mem_span_orbit y σ x hx)
      (fun x hx => mem_laurentBaseChange_of_mem_span_orbit F₀ y hyF x hx)
      (fun x hx => isModPFormFn_of_mem_span_orbit m y hyB x hx)

  have hyli : LinearIndependent E y := linearIndependent_of_coeffMap (algebraMap E K) y x hyx hxli
  have hymem : ∀ i, y i ∈ Submodule.span E (Set.range fun i => coeffEmb E (Y i)) := fun i => by
    rw [hspan]
    exact Submodule.subset_span ⟨(1, i), coeffMap_algEquiv_one (y i)⟩
  exact ⟨n, Y, hYF, hYB, hYli, card_le_of_linearIndependent_of_mem_span y hyli _ hYliL hymem⟩

end ModularCurve

theorem solution
    (N : ℕ) [NeZero N] (m : ℕ) (hm : 1 ≤ m) :
    ∃ (d : ℕ) (Y : Fin d → LaurentSeries ℚ),
      (∀ i, Y i ∈ modularFunctionFieldFull N) ∧ (∀ i, IsModPFormFn ℚ m (Y i)) ∧ LinearIndependent ℚ Y ∧
      (2 * (m : ℚ) - 1) * (ModularCurve.genusFormula N - 1)
        + ((m / 2 : ℕ) : ℚ) * (ModularCurve.nuTwo N : ℚ) + ((2 * m / 3 : ℕ) : ℚ) * (ModularCurve.nuThree N : ℚ)
        + (m : ℚ) * (ModularCurve.cuspCount N : ℚ) ≤ (d : ℚ) := by
  classical
  haveI hAlg : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ

  obtain ⟨d, G, hGli, hGB, hd⟩ :=
    ModularCurve.exists_linearIndependent_isModPFormFn_algebraicClosure_dimFormula_le_card N m hm

  have hx : ∀ i, (G i : LaurentSeries (AlgebraicClosure ℚ)) ∈
      laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N) := fun i => by
    rw [laurentBaseChange_modularFunctionFieldFull_eq_modularFunctionFieldFullC]
    exact (G i).2

  obtain ⟨E, hEfd, hEgal, y, hyF, hyx⟩ :=
    ModularCurve.exists_isGalois_forall_coeffMap_eq_of_mem_laurentBaseChange (modularFunctionFieldFull N)
      (fun i => (G i : LaurentSeries (AlgebraicClosure ℚ))) hx
  haveI := hEfd
  haveI := hEgal
  haveI : Algebra.IsAlgebraic E (AlgebraicClosure ℚ) := inferInstance

  have hGli' : ∀ c : Fin d → AlgebraicClosure ℚ,
      ∑ i, algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) (c i) *
        (G i : LaurentSeries (AlgebraicClosure ℚ)) = 0 → ∀ i, c i = 0 := by
    intro c hc
    have h1 : ∀ i, ((c i • G i : modularFunctionFieldFullC (AlgebraicClosure ℚ) N) : LaurentSeries (AlgebraicClosure ℚ)) =
        algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) (c i) *
          (G i : LaurentSeries (AlgebraicClosure ℚ)) := fun i => by
      rfl
    have ht : (∑ i, c i • G i : modularFunctionFieldFullC (AlgebraicClosure ℚ) N) = 0 := by
      apply Subtype.ext
      rw [AddSubmonoidClass.coe_finsetSum]
      simp only [h1, hc, ZeroMemClass.coe_zero]
    exact Fintype.linearIndependent_iff.mp hGli c ht

  obtain ⟨n, Y, hYF, hYB, hYli, hdn⟩ :=
    ModularCurve.exists_rational_family_of_definedOver (modularFunctionFieldFull N) m d y hyF
      (fun i => (G i : LaurentSeries (AlgebraicClosure ℚ))) hyx hGB hGli'
  exact ⟨n, Y, hYF, hYB, hYli, hd.trans (by exact_mod_cast hdn)⟩

end S_ModularCurve_exists_linearIndependent_isModPFormFn_rat_dimFormula_le_card
end P2MW
export P2MW.S_ModularCurve_exists_linearIndependent_isModPFormFn_rat_dimFormula_le_card (solution)
