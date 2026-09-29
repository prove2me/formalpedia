-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.exists_inertiaStable_pic0Mk_eq_of_inertiaStable_of_isModel
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/8c9aa126-bd5e-59e1-94ce-82fa9e367791

import Mathlib
import Definitions.Def_ModularCurve_JZeroSemistableSpecialization
import Definitions.Def_ModularCurve_NodeDepth
import Definitions.Def_ModularCurve_GlueData
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ValuationSubring_ReduceAt
import Definitions.Def_ModularCurve_PlaceWidthChar
import Definitions.Def_ModularCurve_ProlongationTuple
import Theorems.Thm_ModularCurve_PlaceSpecialization_reduceFst_arithmeticGalois_smul
import Theorems.Thm_ModularCurve_PlaceSpecialization_reduceSnd_arithmeticGalois_smul
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_nodeValueLaw_of_regularityLaw
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_ord_eq_one_forall_isStrict_reduceFst_reduceSnd_notMem_forall_inertia_smul_eq_of_isModel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_exists_inertiaStable_pic0Mk_eq_of_inertiaStable_of_isModel
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.numberField_of_finiteDimensional"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.Gamma0Pair.map_toCurve WeierstrassCurve.mapPoint_eq_ratPointMap ModularCurve.Gamma0Pair.map_gen ModularCurve.Gamma0Pair.map_eq_gamma0PairMap ModularCurve.ModuliPoint.map_eq_moduliPointMapRingHom ModularCurve.ModuliPoint.map_mk WeierstrassCurve.mapPointHom_apply WeierstrassCurve.mapPoint_zero AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁"
p2m_attr_erase "simp" "WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluX_empty WeierstrassCurve.vcInvEmbedding_apply ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply"
p2m_attr_erase "simp" "ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero"
p2m_attr_erase "simp" "TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero ModularCurve.cuspCount_one WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero HahnSeries.ramScale_apply AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one"
p2m_attr_erase "simp" "AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.sizeOf_spec ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₂_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₁_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.injEq ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf"
p2m_attr_erase "simp" "ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ ModularCurve.symPoly_zero"
set_option autoImplicit false
open AlgebraicCurve IsLocalRing ModularCurve

section AvpOrbit

open AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {Γ : Type*} [Group Γ] (ρ : Γ →* SemilinearAut K F) (I : Subgroup Γ)

private def avp_orbit (V₀ : Place K F) : Set (Place K F) := {W | ∃ σ ∈ I, ρ σ • V₀ = W}

private theorem avp_self_mem_orbit (V₀ : Place K F) : V₀ ∈ avp_orbit ρ I V₀ := ⟨1, one_mem _, by rw [map_one, one_smul]⟩

private theorem avp_smul_mem_orbit {V₀ W : Place K F} {σ : Γ} (hσ : σ ∈ I) (hW : W ∈ avp_orbit ρ I V₀) :
    ρ σ • W ∈ avp_orbit ρ I V₀ := by
  obtain ⟨τ, hτ, rfl⟩ := hW
  exact ⟨σ * τ, mul_mem hσ hτ, by rw [map_mul, mul_smul]⟩

private theorem avp_orbit_subset_support {D : Divisor K F} (hD : ∀ σ ∈ I, ρ σ • D = D) {V₀ : Place K F}
    (hV₀ : V₀ ∈ D.support) : avp_orbit ρ I V₀ ⊆ ↑D.support := by
  rintro W ⟨σ, hσ, rfl⟩
  rw [Finset.mem_coe, Finsupp.mem_support_iff, ← hD σ hσ, SemilinearAut.divisor_smul_apply, inv_smul_smul]
  exact Finsupp.mem_support_iff.mp hV₀

private theorem avp_orbit_finite_of_mem_support {D : Divisor K F} (hD : ∀ σ ∈ I, ρ σ • D = D) {V₀ : Place K F}
    (hV₀ : V₀ ∈ D.support) : (avp_orbit ρ I V₀).Finite :=
  (D.support.finite_toSet).subset (avp_orbit_subset_support ρ I hD hV₀)

open Classical in

private noncomputable def avp_tr (V₀ W : Place K F) : Γ :=
  if h : W ∈ avp_orbit ρ I V₀ then Classical.choose h else 1

private theorem avp_tr_mem {V₀ W : Place K F} (h : W ∈ avp_orbit ρ I V₀) : avp_tr ρ I V₀ W ∈ I := by
  unfold avp_tr; rw [dif_pos h]; exact (Classical.choose_spec h).1

private theorem avp_tr_smul {V₀ W : Place K F} (h : W ∈ avp_orbit ρ I V₀) : ρ (avp_tr ρ I V₀ W) • V₀ = W := by
  unfold avp_tr; rw [dif_pos h]; exact (Classical.choose_spec h).2

private theorem avp_smul_eq_smul_of_smul_eq {V₀ : Place K F} {f : F}
    (hf : ∀ σ ∈ I, ρ σ • V₀ = V₀ → ρ σ • f = f)
    {σ σ' : Γ} (hσ : σ ∈ I) (hσ' : σ' ∈ I) (h : ρ σ • V₀ = ρ σ' • V₀) : ρ σ • f = ρ σ' • f := by
  have key : ρ (σ⁻¹ * σ') • f = f := by
    apply hf _ (mul_mem (inv_mem hσ) hσ')
    rw [map_mul, mul_smul, ← h, map_inv, inv_smul_smul]
  rw [map_mul, map_inv, mul_smul, inv_smul_eq_iff] at key
  exact key.symm

private theorem avp_smul_ne_zero_of_ne_zero (g : SemilinearAut K F) {f : F} (hf : f ≠ 0) : g • f ≠ 0 := by
  rw [SemilinearAut.smul_def]
  exact (map_ne_zero_iff _ (SemilinearAut.toRingAut g).injective).mpr hf

section Norm

variable {ρ I}
variable {V₀ : Place K F} (hfin : (avp_orbit ρ I V₀).Finite) (f : F)

private noncomputable def avp_orbitNorm : F := ∏ W ∈ hfin.toFinset, ρ (avp_tr ρ I V₀ W) • f

private theorem avp_orbitNorm_ne_zero (hf0 : f ≠ 0) : avp_orbitNorm hfin f ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun _ _ => avp_smul_ne_zero_of_ne_zero _ hf0

private theorem avp_smul_orbitNorm (hf : ∀ σ ∈ I, ρ σ • V₀ = V₀ → ρ σ • f = f) {σ : Γ} (hσ : σ ∈ I) :
    ρ σ • avp_orbitNorm hfin f = avp_orbitNorm hfin f := by
  classical
  unfold avp_orbitNorm
  rw [Finset.smul_prod']

  refine Finset.prod_nbij (fun W => ρ σ • W) (fun W hW => ?_) (fun W₁ _ W₂ _ h => smul_left_cancel _ h)
    (fun W hW => ?_) (fun W hW => ?_)
  · simp only [Set.Finite.mem_toFinset] at hW ⊢
    exact avp_smul_mem_orbit ρ I hσ hW
  · simp only [Finset.mem_coe, Set.Finite.mem_toFinset] at hW ⊢
    refine ⟨(ρ σ)⁻¹ • W, ?_, smul_inv_smul _ _⟩
    rw [Finset.mem_coe, Set.Finite.mem_toFinset, ← map_inv]
    exact avp_smul_mem_orbit ρ I (inv_mem hσ) hW
  · simp only [Set.Finite.mem_toFinset] at hW
    rw [← mul_smul, ← map_mul]
    apply avp_smul_eq_smul_of_smul_eq ρ I hf (mul_mem hσ (avp_tr_mem ρ I hW)) (avp_tr_mem ρ I (avp_smul_mem_orbit ρ I hσ hW))
    rw [map_mul, mul_smul, avp_tr_smul ρ I hW, avp_tr_smul ρ I (avp_smul_mem_orbit ρ I hσ hW)]

private theorem avp_ord_finset_prod {ι : Type*} (s : Finset ι) (g : ι → F) (hg : ∀ i ∈ s, g i ≠ 0) (W' : Place K F) :
    W'.ord (∏ i ∈ s, g i) = ∑ i ∈ s, W'.ord (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      W'.ord_mul (hg a (Finset.mem_insert_self a s))
        (Finset.prod_ne_zero_iff.mpr fun i hi => hg i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hg i (Finset.mem_insert_of_mem hi)]

private theorem avp_ord_orbitNorm (hf0 : f ≠ 0) (W' : Place K F) :
    W'.ord (avp_orbitNorm hfin f) = ∑ W ∈ hfin.toFinset, ((ρ (avp_tr ρ I V₀ W))⁻¹ • W').ord f := by
  unfold avp_orbitNorm
  rw [avp_ord_finset_prod _ _ (fun _ _ => avp_smul_ne_zero_of_ne_zero _ hf0)]
  refine Finset.sum_congr rfl fun W _ => ?_
  have h := SemilinearAut.ord_smul (ρ (avp_tr ρ I V₀ W)) ((ρ (avp_tr ρ I V₀ W))⁻¹ • W') f
  rw [smul_inv_smul] at h
  exact h

end Norm

section Coefficients

variable {ρ I}
variable {V₀ : Place K F} (hfin : (avp_orbit ρ I V₀).Finite) {f : F} (hf0 : f ≠ 0)
  {bad : Place K F → Prop} (hbad : ∀ σ ∈ I, ∀ W, bad (ρ σ • W) ↔ bad W) (hV₀ : bad V₀)
  (hR : ∀ W, W.ord f ≠ 0 → W ≠ V₀ → ¬ bad W) (h1 : V₀.ord f = 1)

include hbad hV₀ in
private theorem avp_bad_of_mem_orbit {W : Place K F} (hW : W ∈ avp_orbit ρ I V₀) : bad W := by
  obtain ⟨σ, hσ, rfl⟩ := hW
  exact (hbad σ hσ V₀).mpr hV₀

include hbad hR in

private theorem avp_ord_transport_eq_zero {W W' : Place K F} (hW : W ∈ avp_orbit ρ I V₀) (hW' : bad W') (hne : W ≠ W') :
    ((ρ (avp_tr ρ I V₀ W))⁻¹ • W').ord f = 0 := by
  by_contra h
  have hU : bad ((ρ (avp_tr ρ I V₀ W))⁻¹ • W') := by
    have := hbad _ (avp_tr_mem ρ I hW) ((ρ (avp_tr ρ I V₀ W))⁻¹ • W')
    rw [smul_inv_smul] at this
    exact this.mp hW'
  refine hR _ h (fun heq => hne ?_) hU
  rw [inv_smul_eq_iff] at heq
  rw [heq, avp_tr_smul ρ I hW]

include hf0 hbad hV₀ hR h1 in

private theorem avp_ord_orbitNorm_of_mem_orbit {W' : Place K F} (hW' : W' ∈ avp_orbit ρ I V₀) : W'.ord (avp_orbitNorm hfin f) = 1 := by
  classical
  rw [avp_ord_orbitNorm hfin f hf0, Finset.sum_eq_single_of_mem W' ((Set.Finite.mem_toFinset _).mpr hW')]
  · have : (ρ (avp_tr ρ I V₀ W'))⁻¹ • W' = V₀ := by rw [inv_smul_eq_iff, avp_tr_smul ρ I hW']
    rw [this, h1]
  · intro W hW hne
    exact avp_ord_transport_eq_zero hbad hR ((Set.Finite.mem_toFinset _).mp hW) (avp_bad_of_mem_orbit hbad hV₀ hW') hne

include hf0 hbad hR in

private theorem avp_ord_orbitNorm_of_bad_of_not_mem {W' : Place K F} (hW' : bad W') (hW'o : W' ∉ avp_orbit ρ I V₀) :
    W'.ord (avp_orbitNorm hfin f) = 0 := by
  rw [avp_ord_orbitNorm hfin f hf0]
  refine Finset.sum_eq_zero fun W hW => ?_
  exact avp_ord_transport_eq_zero hbad hR ((Set.Finite.mem_toFinset _).mp hW) hW' (fun h => hW'o (h ▸ (Set.Finite.mem_toFinset _).mp hW))

end Coefficients

end AvpOrbit

section AvpAssembly

open ModularCurve.PlaceSpecialization

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  (P : PlaceSpecialization A q N data hKr k red hα hβ)

private def avp_Bad (T : Finset (Place k ↥(modularFunctionFieldC k N)))
    (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) : Prop :=
  ¬ (P.IsStrictFst V ∨ P.IsStrictSnd V ∨ P.reduceFst V ∈ T)

private theorem avp_bad_smul_iff (T : Finset (Place k ↥(modularFunctionFieldC k N)))
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ∈ A.inertiaSubgroupIn ℚ)
    (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) :
    avp_Bad P T (arithmeticGalois (modularFunctionFieldFull (N * q)) σ • V) ↔ avp_Bad P T V := by
  unfold avp_Bad PlaceSpecialization.IsStrictFst PlaceSpecialization.IsStrictSnd
  rw [P.reduceFst_arithmeticGalois_smul σ hσ V, P.reduceSnd_arithmeticGalois_smul σ hσ V]

private def avp_Mover (T : Finset (Place k ↥(modularFunctionFieldC k N))) : Prop :=
  ∀ V₀ : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), avp_Bad P T V₀ →
    ∃ (f : ↥(modularFunctionFieldBar (N * q))) (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))),
      f ≠ 0 ∧ (∀ V, D V = V.ord f) ∧ D V₀ = 1 ∧
        (∀ V ∈ D.support, V ≠ V₀ → ¬ avp_Bad P T V) ∧
        ∀ σ ∈ A.inertiaSubgroupIn ℚ,
          arithmeticGalois (modularFunctionFieldFull (N * q)) σ • V₀ = V₀ →
            arithmeticGalois (modularFunctionFieldFull (N * q)) σ • f = f

variable {P}

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in

private theorem avp_exists_orbit_corrector [HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))]
    {T : Finset (Place k ↥(modularFunctionFieldC k N))} (hmov : avp_Mover P T)
    {D₀ : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))}
    (hst : ∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (N * q)) σ • D₀ = D₀)
    {V₀ : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))} (hV₀D : V₀ ∈ D₀.support) (hV₀ : avp_Bad P T V₀) :
    ∃ E : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
      E ∈ Divisor.principal (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N * q))) ∧
      E ∈ Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N * q))) ∧
      (∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (N * q)) σ • E = E) ∧
      (∀ W ∈ avp_orbit (arithmeticGalois (modularFunctionFieldFull (N * q))) (A.inertiaSubgroupIn ℚ) V₀, E W = 1) ∧
      ∀ W, avp_Bad P T W → W ∉ avp_orbit (arithmeticGalois (modularFunctionFieldFull (N * q))) (A.inertiaSubgroupIn ℚ) V₀ →
        E W = 0 := by
  obtain ⟨f, D, hf0, hD, hD1, hgood, hinv⟩ := hmov V₀ hV₀
  set ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* SemilinearAut (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) :=
    arithmeticGalois (modularFunctionFieldFull (N * q)) with hρ
  have hfin := avp_orbit_finite_of_mem_support ρ (A.inertiaSubgroupIn ℚ) hst hV₀D
  set gN := avp_orbitNorm hfin f with hgN
  have hgN0 : gN ≠ 0 := avp_orbitNorm_ne_zero hfin f hf0
  obtain ⟨E, hE, hEdeg⟩ := HasPrincipalDivisors.exists_divisor (K := AlgebraicClosure ℚ) gN hgN0
  have hbad : ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ W, avp_Bad P T (ρ σ • W) ↔ avp_Bad P T W := fun σ hσ W => avp_bad_smul_iff P T σ hσ W
  have hR : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), W.ord f ≠ 0 → W ≠ V₀ → ¬ avp_Bad P T W := by
    intro W hW hne hb
    have hWD : W ∈ D.support := by rw [Finsupp.mem_support_iff, hD]; exact hW
    exact hgood W hWD hne hb
  have h1 : V₀.ord f = 1 := by rw [← hD, hD1]
  refine ⟨E, ⟨gN, hgN0, hE⟩, (Divisor.mem_degZero).mpr hEdeg, ?_, ?_, ?_⟩
  · intro σ hσ
    ext W
    rw [SemilinearAut.divisor_smul_apply, hE, hE, ← map_inv]
    have hgNinv : ρ σ⁻¹ • gN = gN := avp_smul_orbitNorm hfin f hinv (inv_mem hσ)
    conv_lhs => rw [← hgNinv]
    exact SemilinearAut.ord_smul _ _ _
  · intro W hW
    rw [hE]
    exact avp_ord_orbitNorm_of_mem_orbit hfin hf0 hbad hV₀ hR h1 hW
  · intro W hWb hWo
    rw [hE]
    exact avp_ord_orbitNorm_of_bad_of_not_mem hfin hf0 hbad hR hWb hWo

omit [Fact q.Prime] [NeZero N] in

private theorem avp_apply_eq_of_mem_orbit {D₀ : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))}
    (hst : ∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (N * q)) σ • D₀ = D₀)
    {V₀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))}
    (hW : W ∈ avp_orbit (arithmeticGalois (modularFunctionFieldFull (N * q))) (A.inertiaSubgroupIn ℚ) V₀) :
    D₀ W = D₀ V₀ := by
  obtain ⟨σ, hσ, rfl⟩ := hW
  conv_lhs => rw [← hst σ hσ]
  exact SemilinearAut.divisor_smul_apply_smul _ _ _

set_option maxHeartbeats 3200000 in
open Classical in

private theorem avp_exists_corrector [HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))]
    {T : Finset (Place k ↥(modularFunctionFieldC k N))} (hmov : avp_Mover P T) :
    ∀ (n : ℕ) (D₀ : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))),
      (D₀.support.filter (avp_Bad P T)).card ≤ n →
      (∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (N * q)) σ • D₀ = D₀) →
      ∃ C : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
        C ∈ Divisor.principal (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N * q))) ∧
        C ∈ Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N * q))) ∧
        (∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (N * q)) σ • C = C) ∧
        ∀ W ∈ (D₀ - C).support, ¬ avp_Bad P T W := by
  intro n
  induction n with
  | zero =>
    intro D₀ hcard _
    refine ⟨0, zero_mem _, zero_mem _, fun σ _ => smul_zero _, ?_⟩
    intro W hW hb
    rw [sub_zero] at hW
    have : W ∈ D₀.support.filter (avp_Bad P T) := Finset.mem_filter.mpr ⟨hW, hb⟩
    rw [Nat.le_zero, Finset.card_eq_zero] at hcard
    rw [hcard] at this
    exact absurd this (Finset.notMem_empty W)
  | succ n ih =>
    intro D₀ hcard hst
    by_cases hex : ∃ V₀ ∈ D₀.support, avp_Bad P T V₀
    swap
    · push Not at hex
      exact ⟨0, zero_mem _, zero_mem _, fun σ _ => smul_zero _, fun W hW => hex W (by rwa [sub_zero] at hW)⟩
    obtain ⟨V₀, hV₀D, hV₀⟩ := hex
    obtain ⟨E, hEp, hEd, hEst, hE1, hE0⟩ := avp_exists_orbit_corrector hmov hst hV₀D hV₀
    set D₁ : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) := D₀ - D₀ V₀ • E with hD₁
    have hst₁ : ∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (N * q)) σ • D₁ = D₁ := by
      intro σ hσ
      rw [hD₁, smul_sub, smul_comm, hst σ hσ, hEst σ hσ]

    have hsub : D₁.support.filter (avp_Bad P T) ⊆ (D₀.support.filter (avp_Bad P T)).erase V₀ := by
      intro W hW
      obtain ⟨hWD₁, hWb⟩ := Finset.mem_filter.mp hW
      rw [Finsupp.mem_support_iff, hD₁, Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul] at hWD₁
      by_cases hWo : W ∈ avp_orbit (arithmeticGalois (modularFunctionFieldFull (N * q))) (A.inertiaSubgroupIn ℚ) V₀
      · exfalso
        apply hWD₁
        rw [hE1 W hWo, mul_one, avp_apply_eq_of_mem_orbit hst hWo, sub_self]
      · rw [hE0 W hWb hWo, mul_zero, sub_zero] at hWD₁
        refine Finset.mem_erase.mpr ⟨fun h => hWo ?_, Finset.mem_filter.mpr ⟨Finsupp.mem_support_iff.mpr hWD₁, hWb⟩⟩
        rw [h]; exact avp_self_mem_orbit _ _ V₀
    have hcard₁ : (D₁.support.filter (avp_Bad P T)).card ≤ n := by
      have h1 := Finset.card_le_card hsub
      have h2 := Finset.card_erase_of_mem (Finset.mem_filter.mpr ⟨hV₀D, hV₀⟩)
      omega
    obtain ⟨C', hC'p, hC'd, hC'st, hC'good⟩ := ih D₁ hcard₁ hst₁
    refine ⟨D₀ V₀ • E + C', add_mem (zsmul_mem hEp _) hC'p, add_mem (zsmul_mem hEd _) hC'd, fun σ hσ => ?_, fun W hW => ?_⟩
    · rw [smul_add, smul_comm, hEst σ hσ, hC'st σ hσ]
    · apply hC'good W
      rwa [hD₁, sub_sub]

end AvpAssembly

open ModularCurve.PlaceSpecialization in
theorem solution
    (q : ℕ) [Fact q.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (N : ℕ) [NeZero N] (k : Type*) [Field k]
    [CharP k q] (red : A →+* k) (data : ModularPolynomialData q)
    (hKr : KroneckerCongruence q data) (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q)
    (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q) [IsAlgClosed k]
    [DecidableEq k] (hqN : ¬ q ∣ N)
    (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (W : Finset (Place k (modularFunctionFieldC k N)))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N k)
    (R : ProlongationTuple P) (hR : R.IsModel) (hRL : R.RegularityLaw W)
    (hO : R.OrderLawFixed) :
      ∀ D₀ : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N * q)))),
        (∀ σ ∈ A.inertiaSubgroupIn ℚ,
          arithmeticGalois (modularFunctionFieldFull (N * q)) σ •
            (D₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) = D₀) →
        ∃ D : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N * q)))),
          Pic0.mk D = Pic0.mk D₀ ∧
          (∀ σ ∈ A.inertiaSubgroupIn ℚ,
            arithmeticGalois (modularFunctionFieldFull (N * q)) σ •
              (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) = D) ∧
          (∀ V ∈ (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))).support,
            P.IsStrictFst V ∨ P.IsStrictSnd V ∨ P.reduceFst V ∈ W) := by
  intro D₀ hD₀
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  haveI := ModularCurve.isCurveOver_modularFunctionFieldBar (N * q)

  have hval : R.NodeValueLaw W :=
    ModularCurve.PlaceSpecialization.ProlongationTuple.nodeValueLaw_of_regularityLaw P hqN hW R hRL

  have hmov : avp_Mover P W := by
    intro V₀ hV₀
    have hT : ∀ t ∈ ({P.reduceFst V₀} : Finset (Place k ↥(modularFunctionFieldC k N))),
        t ∉ ssPlaces q N k := by
      intro t ht hss
      rw [Finset.mem_singleton] at ht
      subst ht
      exact hV₀ (Or.inr (Or.inr ((hW _).mpr hss)))
    obtain ⟨f, D, hf0, -, hD, hD1, hstrict, -, hinv⟩ :=
      ModularCurve.PlaceSpecialization.ProlongationTuple.exists_ord_eq_one_forall_isStrict_reduceFst_reduceSnd_notMem_forall_inertia_smul_eq_of_isModel
        q A N k red data hKr hα hβ hqN P W hW R hR hRL hval hO {P.reduceFst V₀} hT V₀ (Or.inl (Finset.mem_singleton_self _))
    refine ⟨f, D, hf0, hD, hD1, fun V hVD hne hb => ?_, hinv⟩
    exact hb ((hstrict V hVD hne).elim Or.inl fun h => Or.inr (Or.inl h))

  obtain ⟨C, hCp, hCd, hCst, hCgood⟩ :=
    avp_exists_corrector hmov _ (D₀ : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) le_rfl hD₀
  refine ⟨⟨(D₀ : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) - C, sub_mem D₀.2 hCd⟩, ?_, ?_, ?_⟩
  ·
    show (QuotientAddGroup.mk _ : Pic0 _ _) = QuotientAddGroup.mk _
    rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
    have hcoe : ((-(⟨(D₀ : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) - C, sub_mem D₀.2 hCd⟩ :
        ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N * q))))) + D₀ :
          ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N * q))))) :
        Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) =
          -((D₀ : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) - C) + D₀ := rfl
    rw [hcoe, neg_sub, sub_add_cancel]
    exact hCp
  ·
    intro σ hσ
    show arithmeticGalois (modularFunctionFieldFull (N * q)) σ •
        ((D₀ : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) - C) = (D₀ : Divisor _ _) - C
    rw [smul_sub, hD₀ σ hσ, hCst σ hσ]
  ·
    intro V hV
    by_contra h
    exact hCgood V hV h

end S_ModularCurve_PlaceSpecialization_exists_inertiaStable_pic0Mk_eq_of_inertiaStable_of_isModel
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_exists_inertiaStable_pic0Mk_eq_of_inertiaStable_of_isModel (solution)
