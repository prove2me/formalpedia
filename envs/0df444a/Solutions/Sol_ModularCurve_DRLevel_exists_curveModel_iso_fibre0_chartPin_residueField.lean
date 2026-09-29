-- Prove2me | solution 1 for ModularCurve.DRLevel.exists_curveModel_iso_fibre0_chartPin_residueField
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/b6803bf4-80c3-5654-9091-6c89b0f3145f

import Definitions.Def_ModularCurve_DRModelPackageLevel
import Theorems.Thm_ModularCurve_IgusaScheme_exists_algEquiv_residueField_tensor_chartAlg_chartRing_compat
import Theorems.Thm_AlgebraicCurve_CurveModel_isProper_smooth_places_affineCover_glued
import Theorems.Thm_ModularCurve_IgusaScheme_exists_iso_glued_pullback_igusaTo_of_algEquiv_chartAlg_chartRing
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_ModularCurve_finiteDimensional_adjoin_jqModC
import Theorems.Thm_ModularCurve_modularFunctionFieldFullC_eq_modularFunctionFieldC_residueField
import Theorems.Thm_ModularCurve_isSeparable_adjoin_jqModC_of_isAlgebraic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRLevel_exists_curveModel_iso_fibre0_chartPin_residueField
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular"
p2m_attr_erase "simp" "ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq"
p2m_attr_erase "simp" "GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.cuspCount_one ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar HahnSeries.ramScale_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one"
p2m_attr_erase "simp" "compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU"
p2m_attr_erase "simp" "WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero"
p2m_attr_erase "simp" "TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.PlaceSpecialization.mk.injEq ModularCurve.PlaceSpecialization.mk.sizeOf_spec"

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve NeronModelInfra
open ModularCurve ModularCurve.IgusaScheme ModularCurve.DRLevel IsLocalRing
open scoped TensorProduct

noncomputable section

namespace F6P

section Model

variable (p : ℕ) [NeZero p] (ℓ : ℕ) [Fact ℓ.Prime] (A : ValuationSubring (AlgebraicClosure ℚ))
  [CharP (ResidueField ↥A) ℓ] [IsAlgClosed (ResidueField ↥A)]

private abbrev jt : ↥(modularFunctionFieldFullC (ResidueField ↥A) p) :=
  ⟨jqModC (ResidueField ↥A), jqModC_mem_full (ResidueField ↥A) p⟩

omit [NeZero p] [IsAlgClosed (ResidueField ↥A)] in
private lemma jt_ne_zero : jt p A ≠ 0 := fun h =>
  jqModC_ne_zero_def (ResidueField ↥A) (congrArg Subtype.val h)

omit [NeZero p] [IsAlgClosed (ResidueField ↥A)] in
private lemma transcendental_jt : Transcendental (ResidueField ↥A) (jt p A) := fun h =>
  transcendental_jqModC (ResidueField ↥A)
    ((isAlgebraic_algHom_iff (modularFunctionFieldFullC (ResidueField ↥A) p).val Subtype.val_injective).mpr h)

private lemma finiteDimensional_adjoin_jt (hℓp : ¬ ℓ ∣ p) (hA : A.LiesOverPrime ℓ) :
    FiniteDimensional ↥(IntermediateField.adjoin (ResidueField ↥A) ({jt p A} : Set ↥(modularFunctionFieldFullC (ResidueField ↥A) p)))
      ↥(modularFunctionFieldFullC (ResidueField ↥A) p) := by
  have key : ∀ (E : IntermediateField (ResidueField ↥A) (LaurentSeries (ResidueField ↥A)))
      (hE : E = modularFunctionFieldC (ResidueField ↥A) p) (hx : jqModC (ResidueField ↥A) ∈ E),
      FiniteDimensional ↥(IntermediateField.adjoin (ResidueField ↥A) ({(⟨jqModC (ResidueField ↥A), hx⟩ : ↥E)} : Set ↥E)) ↥E := by
    rintro E rfl hx
    exact finiteDimensional_adjoin_jqModC (N := p) A
  exact key _ (modularFunctionFieldFullC_eq_modularFunctionFieldC_residueField p ℓ hℓp A hA) _

private lemma isSeparable_adjoin_jt (hℓp : ¬ ℓ ∣ p) (hA : A.LiesOverPrime ℓ) :
    Algebra.IsSeparable
      ↥(IntermediateField.adjoin (ResidueField ↥A) ({jt p A} : Set ↥(modularFunctionFieldFullC (ResidueField ↥A) p)))
      ↥(modularFunctionFieldFullC (ResidueField ↥A) p) := by
  haveI := finiteDimensional_adjoin_jt p ℓ A hℓp hA
  exact isSeparable_adjoin_jqModC_of_isAlgebraic (ResidueField ↥A) (modularFunctionFieldFullC (ResidueField ↥A) p)
    (jqModC_mem_full (ResidueField ↥A) p)

end Model

section Read

open AlgebraicCurve.CurveModel

variable (K : Type) [Field K] {L : Type} [Field L] [Algebra K L] (t : L) [Fact (t ≠ 0)]
  [FiniteDimensional ↥(IntermediateField.adjoin K ({t} : Set L)) L]

private lemma gluedFunctionFieldEquiv_symm_germToFunctionField_app
    {Y : Scheme.{0}} (g : glued K t ⟶ Y) {B : Type} [CommRing B]
    (ι : Spec (CommRingCat.of B) ⟶ Y) [IsOpenImmersion ι]
    (φ : B →+* ↥(chartRing K ({t} : Set L)))
    (hsq : ι₀ K t ≫ g = Spec.map (CommRingCat.ofHom φ) ≫ ι) (b : B)
    [hne : Nonempty (Scheme.Opens.toScheme ((g ⁻¹ᵁ (ι ''ᵁ ⊤))))] :
    (gluedFunctionFieldEquiv K t).symm
        ((glued K t).germToFunctionField (g ⁻¹ᵁ (ι ''ᵁ ⊤))
          ((g.app (ι ''ᵁ ⊤)).hom ((ι.appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of B)).inv b)))) =
      ((φ b : ↥(chartRing K ({t} : Set L))) : L) := by

  let p₀ : X₀ K t := genericPoint (X₀ K t)
  have hx : (ι₀ K t).base p₀ ∈ g ⁻¹ᵁ (ι ''ᵁ ⊤) := by
    show (ι₀ K t ≫ g) p₀ ∈ ι ''ᵁ ⊤
    rw [hsq, Scheme.Hom.image_top_eq_opensRange]
    exact ⟨_, rfl⟩
  set σ : Γ(Y, ι ''ᵁ ⊤) := (ι.appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of B)).inv b) with hσ
  set s : Γ(glued K t, g ⁻¹ᵁ (ι ''ᵁ ⊤)) := (g.app (ι ''ᵁ ⊤)).hom σ with hs

  have h1 : (glued K t).germToFunctionField (g ⁻¹ᵁ (ι ''ᵁ ⊤)) s =
      algebraMap ((glued K t).presheaf.stalk ((ι₀ K t).base p₀)) (glued K t).functionField
        ((glued K t).presheaf.germ (g ⁻¹ᵁ (ι ''ᵁ ⊤)) ((ι₀ K t).base p₀) hx s) := by
    change (glued K t).presheaf.germ _ (genericPoint (glued K t)) _ s =
      ((glued K t).presheaf.stalkSpecializes (genericPoint_specializes ((ι₀ K t).base p₀)))
        ((glued K t).presheaf.germ (g ⁻¹ᵁ (ι ''ᵁ ⊤)) ((ι₀ K t).base p₀) hx s)
    rw [TopCat.Presheaf.germ_stalkSpecializes_apply]
  rw [h1, ffEquiv_symm_algebraMap_stalk K t (chartRing K ({t} : Set L)) (incl₀ K t) (ι₀ K t) (ιU_eq K t).symm p₀]

  rw [Scheme.Hom.germ_stalkMap_apply]

  have e1 : ((ι₀ K t).app (g ⁻¹ᵁ (ι ''ᵁ ⊤))).hom s = ((ι₀ K t ≫ g).app (ι ''ᵁ ⊤)).hom σ := by
    rw [hs, Scheme.Hom.comp_app]; rfl
  rw [e1, Scheme.Hom.congr_app hsq (ι ''ᵁ ⊤)]
  erw [TopCat.Presheaf.germ_res_apply]
  change thetaHom K t (chartRing K ({t} : Set L)) (incl₀ K t) p₀
      ((X₀ K t).presheaf.germ ((Spec.map (CommRingCat.ofHom φ)) ⁻¹ᵁ (ι ⁻¹ᵁ (ι ''ᵁ ⊤))) p₀ _
        (((Spec.map (CommRingCat.ofHom φ)).app (ι ⁻¹ᵁ (ι ''ᵁ ⊤))).hom ((ι.app (ι ''ᵁ ⊤)).hom σ))) = _
  erw [← Scheme.Hom.germ_stalkMap_apply (Spec.map (CommRingCat.ofHom φ)) (ι ⁻¹ᵁ (ι ''ᵁ ⊤)) p₀]

  have h3 : (ι.app (ι ''ᵁ ⊤)).hom σ =
      (Spec (CommRingCat.of B)).presheaf.map (eqToHom (ι.preimage_image_eq ⊤)).op
        ((Scheme.ΓSpecIso (CommRingCat.of B)).inv b) := by
    rw [hσ, ← CommRingCat.comp_apply, Scheme.Hom.appIso_inv_app]
  rw [h3]
  erw [TopCat.Presheaf.germ_res_apply]

  change thetaHom K t (chartRing K ({t} : Set L)) (incl₀ K t) p₀
      (((Spec.map (CommRingCat.ofHom φ)).stalkMap p₀)
        (StructureSheaf.toStalk B ((Spec.map (CommRingCat.ofHom φ)).base p₀) b)) = _
  erw [AlgebraicGeometry.stalkMap_toStalk_apply (CommRingCat.ofHom φ) p₀ b]
  exact thetaHom_toStalk K t (chartRing K ({t} : Set L)) (incl₀ K t) (fun a => rfl) p₀ (φ b)

end Read

section Core

private theorem core
    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    [CharP (ResidueField ↥A) q] [IsAlgClosed (ResidueField ↥A)]
    (ρ : DRLevel.R q →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (DRLevel.R q) (AlgebraicClosure ℚ))
    (Lsub : IntermediateField (ResidueField ↥A) (LaurentSeries (ResidueField ↥A)))
    (hmem : jqModC (ResidueField ↥A) ∈ Lsub) (hmemN : jqNModC (ResidueField ↥A) N₀ ∈ Lsub)
    (hL : modularFunctionFieldFullC (ResidueField ↥A) N₀ = Lsub) :
    ∃ (M : CurveModel (ResidueField ↥A) ↥(Lsub)) (e : M.C ⟶ DRLevel.fibre0 (N₀ := N₀) ((residue ↥A).comp ρ)) (_ : IsIso e)
      (_ : Nonempty (Scheme.Opens.toScheme ((e ≫ pullback.fst (DRLevel.toBase0 N₀ q) (Spec.map (CommRingCat.ofHom ((residue ↥A).comp ρ)))) ⁻¹ᵁ
        ((IgusaScheme.ιFin N₀ q) ''ᵁ ⊤)))),
      e ≫ pullback.snd _ _ = M.toBase ∧
      ∀ b : ↥(IgusaScheme.chartAlgFin N₀ q),
        let readb : ↥(Lsub) :=
          M.ffEquiv.symm
            (M.C.germToFunctionField
              ((e ≫ pullback.fst (DRLevel.toBase0 N₀ q) (Spec.map (CommRingCat.ofHom ((residue ↥A).comp ρ)))) ⁻¹ᵁ ((IgusaScheme.ιFin N₀ q) ''ᵁ ⊤))
              (((e ≫ pullback.fst (DRLevel.toBase0 N₀ q) (Spec.map (CommRingCat.ofHom ((residue ↥A).comp ρ)))).app ((IgusaScheme.ιFin N₀ q) ''ᵁ ⊤)).hom
                (((IgusaScheme.ιFin N₀ q).appIso ⊤).inv
                  ((Scheme.ΓSpecIso (CommRingCat.of ↥(IgusaScheme.chartAlgFin N₀ q))).inv b))))
        ((b = IgusaScheme.jChartFin N₀ q → readb = (⟨jqModC (ResidueField ↥A), hmem⟩ : ↥Lsub)) ∧
          (((b : ↥(modularFunctionFieldFull N₀)) : LaurentSeries ℚ) = qExpand ℚ N₀ jq → readb = (⟨jqNModC (ResidueField ↥A) N₀, hmemN⟩ : ↥Lsub))) := by
  subst hL
  haveI : Fact (jt N₀ A ≠ 0) := ⟨jt_ne_zero N₀ A⟩
  letI instAlg : Algebra ↥(GaloisRep.ratLocalizedAt q) (ResidueField ↥A) := ((residue ↥A).comp ρ).toAlgebra
  obtain ⟨esF, esI, hj, hjInv, hjN, -, hcompat⟩ :=
    IgusaScheme.exists_algEquiv_residueField_tensor_chartAlg_chartRing_compat N₀ q hqN A hA ρ hρ
  haveI hfdK := finiteDimensional_adjoin_jt N₀ q A hqN hA
  haveI hsepK := isSeparable_adjoin_jt N₀ q A hqN hA
  obtain ⟨hPr, hSm, ⟨P, hPbij, hPst⟩, hAff⟩ :=
    AlgebraicCurve.CurveModel.isProper_smooth_places_affineCover_glued (ResidueField ↥A)
      (L := ↥(modularFunctionFieldFullC (ResidueField ↥A) N₀)) (jt N₀ A) (transcendental_jt N₀ A)
  obtain ⟨es, hes_iso, hes, hpinF, hpinI⟩ :=
    IgusaScheme.exists_iso_glued_pullback_igusaTo_of_algEquiv_chartAlg_chartRing N₀ q (ResidueField ↥A)
      (jt N₀ A) esF esI hj hjInv hcompat
  let M : CurveModel (ResidueField ↥A) ↥(modularFunctionFieldFullC (ResidueField ↥A) N₀) :=
    { C := AlgebraicCurve.CurveModel.glued (ResidueField ↥A) (jt N₀ A)
      toBase := AlgebraicCurve.CurveModel.gluedToBase (ResidueField ↥A) (jt N₀ A)
      isProper := hPr
      smooth := hSm
      ffEquiv := AlgebraicCurve.CurveModel.gluedFunctionFieldEquiv (ResidueField ↥A) (jt N₀ A)
      ffEquiv_algebraMap :=
        AlgebraicCurve.CurveModel.gluedFunctionFieldEquiv_algebraMap (ResidueField ↥A) (jt N₀ A)
      placeOfPoint := P
      placeOfPoint_bijective := hPbij
      range_stalk_eq := hPst
      finset_subset_affineOpen := hAff }

  have hne : Nonempty (Scheme.Opens.toScheme
      ((es ≫ pullback.fst (DRLevel.toBase0 N₀ q) (Spec.map (CommRingCat.ofHom ((residue ↥A).comp ρ)))) ⁻¹ᵁ
        ((IgusaScheme.ιFin N₀ q) ''ᵁ ⊤))) := by
    let p₀ : AlgebraicCurve.CurveModel.X₀ (ResidueField ↥A) (jt N₀ A) := Classical.arbitrary _
    refine ⟨⟨(AlgebraicCurve.CurveModel.ι₀ (ResidueField ↥A) (jt N₀ A)).base p₀, ?_⟩⟩
    show ((AlgebraicCurve.CurveModel.ι₀ (ResidueField ↥A) (jt N₀ A)) ≫ es ≫
        pullback.fst (DRLevel.toBase0 N₀ q) (Spec.map (CommRingCat.ofHom ((residue ↥A).comp ρ)))) p₀ ∈
      (IgusaScheme.ιFin N₀ q) ''ᵁ ⊤
    rw [hpinF, Scheme.Hom.image_top_eq_opensRange]
    exact ⟨_, rfl⟩
  refine ⟨M, es, hes_iso, hne, hes, ?_⟩
  intro b
  have hread := gluedFunctionFieldEquiv_symm_germToFunctionField_app (ResidueField ↥A) (jt N₀ A)
    (es ≫ pullback.fst (DRLevel.toBase0 N₀ q) (Spec.map (CommRingCat.ofHom ((residue ↥A).comp ρ))))
    (IgusaScheme.ιFin N₀ q)
    (esF.toAlgHom.toRingHom.comp
      (Algebra.TensorProduct.includeRight (R := ↥(GaloisRep.ratLocalizedAt q)) (A := ResidueField ↥A)
        (B := ↥(IgusaScheme.chartAlgFin N₀ q))).toRingHom) hpinF b
  intro readb
  have hrb : readb = (esF ((1 : ResidueField ↥A) ⊗ₜ[↥(GaloisRep.ratLocalizedAt q)] b)).1 := hread
  refine ⟨fun hb => ?_, fun hb => ?_⟩
  · rw [hrb, hb]; exact hj
  · rw [hrb]
    apply Subtype.ext
    exact hjN b hb

end Core

end F6P

theorem solution
    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀)

    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    [CharP (ResidueField ↥A) q] [IsAlgClosed (ResidueField ↥A)] [DecidableEq (ResidueField ↥A)]
    (ρ : DRLevel.R q →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (DRLevel.R q) (AlgebraicClosure ℚ)) :
    ∃ (M : CurveModel (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) N₀)) (e : M.C ⟶ DRLevel.fibre0 (N₀ := N₀) ((residue ↥A).comp ρ)) (_ : IsIso e)
      (_ : Nonempty (Scheme.Opens.toScheme ((e ≫ pullback.fst (DRLevel.toBase0 N₀ q) (Spec.map (CommRingCat.ofHom ((residue ↥A).comp ρ)))) ⁻¹ᵁ
        ((IgusaScheme.ιFin N₀ q) ''ᵁ ⊤)))),
      e ≫ pullback.snd _ _ = M.toBase ∧
      ∀ b : ↥(IgusaScheme.chartAlgFin N₀ q),
        let readb : ↥(modularFunctionFieldC (ResidueField ↥A) N₀) :=
          M.ffEquiv.symm
            (M.C.germToFunctionField
              ((e ≫ pullback.fst (DRLevel.toBase0 N₀ q) (Spec.map (CommRingCat.ofHom ((residue ↥A).comp ρ)))) ⁻¹ᵁ ((IgusaScheme.ιFin N₀ q) ''ᵁ ⊤))
              (((e ≫ pullback.fst (DRLevel.toBase0 N₀ q) (Spec.map (CommRingCat.ofHom ((residue ↥A).comp ρ)))).app ((IgusaScheme.ιFin N₀ q) ''ᵁ ⊤)).hom
                (((IgusaScheme.ιFin N₀ q).appIso ⊤).inv
                  ((Scheme.ΓSpecIso (CommRingCat.of ↥(IgusaScheme.chartAlgFin N₀ q))).inv b))))
        ((b = IgusaScheme.jChartFin N₀ q → readb = jGeomGen (ResidueField ↥A) N₀) ∧
          (((b : ↥(modularFunctionFieldFull N₀)) : LaurentSeries ℚ) = qExpand ℚ N₀ jq → readb = jNGeomGen (ResidueField ↥A) N₀)) := by
  have h := F6P.core N₀ q hqN A hA ρ hρ (modularFunctionFieldC (ResidueField ↥A) N₀)
    (jqModC_mem (ResidueField ↥A) N₀) (jqNModC_mem (ResidueField ↥A) N₀)
    (modularFunctionFieldFullC_eq_modularFunctionFieldC_residueField N₀ q hqN A hA)
  exact h

end

end S_ModularCurve_DRLevel_exists_curveModel_iso_fibre0_chartPin_residueField
end P2MW
export P2MW.S_ModularCurve_DRLevel_exists_curveModel_iso_fibre0_chartPin_residueField (solution)
