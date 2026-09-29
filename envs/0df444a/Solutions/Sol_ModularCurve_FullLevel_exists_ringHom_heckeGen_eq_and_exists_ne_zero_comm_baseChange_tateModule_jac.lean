-- Prove2me | solution 1 for ModularCurve.FullLevel.exists_ringHom_heckeGen_eq_and_exists_ne_zero_comm_baseChange_tateModule_jac
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/5ac30510-9fd8-54af-b6d3-93c913554559

import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_CuspForm_AdelicLift
import Definitions.Def_CuspForm_HeckeAlgebra
import Definitions.Def_CuspForm_Newforms
import Definitions.Def_LocalNewvector_AdelicSpanCarrier
import Definitions.Def_LocalNewvector_ReductionFunctor
import Theorems.Thm_Module_End_exists_ne_zero_forall_apply_eq_smul_of_dual_comp_eq_smul
import Theorems.Thm_CuspidalType_IsCuspidalOfType_exists_linearEquiv_comm_of_isCuspidalOfType
import Theorems.Thm_CuspidalType_IsCuspidalOfType_dual
import Theorems.Thm_ModularCurve_FullLevel_exists_galoisRep_isAdicContinuous_heckeRep_gl2Rep_baseChange_tateModule_jac
import Theorems.Thm_ModularCurve_FullLevel_exists_injective_dual_baseChange_tateModule_jac_of_isNewform_of_range_eq_span
import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_exists_ringHom_heckeGen_eq_and_exists_ne_zero_comm_baseChange_tateModule_jac
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicCurve.CellDissection.fintypeV AlgebraicCurve.CellDissection.fintypeC AlgebraicCurve.CellDissection.fintypeE AlgebraicCurve.CellDissection.decEqV AlgebraicCurve.CellDissection.decEqC"
p2m_attr_erase "instance" "AlgebraicCurve.CellDissection.decEqE CuspForm.GammaH_finiteIndex FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 Ihara.instGroupIharaAmalgam HeckeIntegralSeam.finite_padicInt_quotient_span_p ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0 HeckeEis.instFiniteIndexHeckeUpper HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par"
p2m_attr_erase "simp" "AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.abelJacobiDiv_single AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.AnalyticCoord.mk.injEq AlgebraicCurve.Cell.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.injEq AlgebraicCurve.CellDissection.mk.sizeOf_spec AlgebraicCurve.Cell.mk.injEq AlgebraicCurve.CellDissection.mk.injEq AlgebraicCurve.AnalyticCoord.mk.sizeOf_spec AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.dualHeckeRep_apply_apply ModularCurve.coe_segmentPath ModularCurve.cuspHeckeAeval_heckeGen ModularCurve.coe_periodLatticeRestrict_apply ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one FreyPackage.ModMCarrier.coe_rescaleLin_apply ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero Ihara.wConj_coe Ihara.wConj_symm_coe Ihara.coe_iota1 Ihara.coe_iota1SL Ihara.iota1Mat_apply_one_zero Ihara.iota1Mat_apply_zero_zero Ihara.iota1Mat_apply_zero_one Ihara.iota1Mat_apply_one_one Ihara.coe_iota0 Ihara.iharaEdge_one Ihara.pairFamily_zero Ihara.iharaEdge_zero Ihara.pairFamily_one"
p2m_attr_erase "simp" "Ihara.coe_amalgamToGamma0Away Ihara.coe_vertexZero Ihara.coe_slToAway CuspForm.Gamma1Hecke.redMatrix_apply_one_one CuspForm.Gamma1Hecke.redMatrix_apply_one_zero CuspForm.Gamma1Hecke.lift_infty CuspForm.Gamma1Hecke.heckeRep_infty CuspForm.Gamma1Hecke.heckeRep_coe CuspForm.Gamma1Hecke.wt_infty CuspForm.Gamma1Hecke.redMatrix_apply_zero_one CuspForm.coe_slashLinOfMemGamma0_apply CuspForm.Gamma1Hecke.wt_coe CuspForm.Gamma1Hecke.lift_coe CuspForm.Gamma1Hecke.redMatrix_apply_zero_zero CuspForm.coe_heckeTOne CuspForm.coe_heckeTLinOne_apply CuspForm.coe_slashOfMemGamma0 CuspForm.PeterssonCoset.mapGL_apply AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv AutomorphicForm.classSq_apply AutomorphicForm.classRepEmbedding_one AutomorphicForm.finIdeleExponentAt_one AutomorphicForm.classRepFinIdele_one AutomorphicForm.productionPinsGeneralOf_D AutomorphicForm.productionPinsGeneral_D AutomorphicForm.productionPinsGeneralOf_μ AutomorphicForm.productionPinsGeneralOf_U ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply ModularCurve.ComplexPlaceDictionaryOf.pt_ofGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.injEq"
p2m_attr_erase "simp" "ModularCurve.ComplexPlaceDictionaryOf.pt_toGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.sizeOf_spec ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec CohCarrier.jConjGammaH_jConjGammaH CohCarrier.coe_jConjGammaH CohCarrier.charInvolution_apply ModularCurve.Period.jConjMat_apply_zero_one ModularCurve.Period.jConjSL_coe ModularCurve.Period.jConjMat_apply_one_zero ModularCurve.Period.jConjMat_apply_one_one ModularCurve.Period.jConjGamma0_coe ModularCurve.Period.charInvolution_apply ModularCurve.Period.jConjMat_apply_zero_zero ModularCurve.qExpandAlgHomC_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff"
p2m_attr_erase "simp" "ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero"
p2m_attr_erase "simp" "ModularCurve.LevelN.coe_jGen HeckeEis.coeffCoboundaryMap_apply"

set_option autoImplicit false
open scoped TensorProduct

noncomputable section

namespace Ws41
namespace W7

open LocalNewvector

theorem exists_equivariant_section {G : Type*} [Group G] [Fintype G]
    {X Y : Type*} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    (ρX : Representation ℂ G X) (ρY : Representation ℂ G Y)
    (L : Y →ₗ[ℂ] X) (hL : ∀ g, L ∘ₗ ρY g = ρX g ∘ₗ L) (hsurj : Function.Surjective L) :
    ∃ φ : X →ₗ[ℂ] Y, L ∘ₗ φ = LinearMap.id ∧ ∀ g, φ ∘ₗ ρX g = ρY g ∘ₗ φ := by
  classical
  obtain ⟨φ₀, hφ₀⟩ := L.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hsurj)
  have hφ₀' : ∀ x, L (φ₀ x) = x := fun x => LinearMap.congr_fun hφ₀ x
  have hL' : ∀ g y, L (ρY g y) = ρX g (L y) := fun g y => LinearMap.congr_fun (hL g) y
  have hcard : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have hinv : ∀ (g : G) (x : X), ρX g (ρX g⁻¹ x) = x := fun g x => by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have hinvY : ∀ (g : G) (y : Y), ρY g (ρY g⁻¹ y) = y := fun g y => by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  let φ : X →ₗ[ℂ] Y := (Fintype.card G : ℂ)⁻¹ • ∑ g : G, ρY g ∘ₗ φ₀ ∘ₗ ρX g⁻¹
  have hφ_apply : ∀ x, φ x = (Fintype.card G : ℂ)⁻¹ • ∑ g : G, ρY g (φ₀ (ρX g⁻¹ x)) := fun x => by
    simp only [φ, LinearMap.smul_apply, LinearMap.coe_sum, Finset.sum_apply, LinearMap.comp_apply]
  refine ⟨φ, ?_, ?_⟩
  · refine LinearMap.ext fun x => ?_
    rw [LinearMap.comp_apply, hφ_apply, map_smul, map_sum, LinearMap.id_apply]
    simp only [hL', hφ₀', hinv, Finset.sum_const, Finset.card_univ]
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hcard, one_smul]
  · intro h
    refine LinearMap.ext fun x => ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hφ_apply, hφ_apply, map_smul, map_sum]
    congr 1
    refine Fintype.sum_equiv (Equiv.mulLeft h⁻¹) _ _ (fun g => ?_)
    simp only [Equiv.coe_mulLeft, mul_inv_rev, inv_inv, map_mul, Module.End.mul_apply, hinvY]

theorem trace_comp_coeigen {K : Type*} [Field K] {W Y : Type*} [AddCommGroup W] [Module K W] [AddCommGroup Y] [Module K Y]
    (L : Y →ₗ[K] W) (T : Y →ₗ[K] Y) (c : K) (hLT : L ∘ₗ T = c • L) (φ : W →ₗ[K] Y) :
    LinearMap.trace K W (L ∘ₗ (T ∘ₗ φ)) = c * LinearMap.trace K W (L ∘ₗ φ) := by
  rw [← LinearMap.comp_assoc, hLT, LinearMap.smul_comp, map_smul, smul_eq_mul]

theorem closing_core {G : Type*} [Group G] [Fintype G] {R : Type*} [CommRing R]
    {Y : Type*} [AddCommGroup Y] [Module ℂ Y] [FiniteDimensional ℂ Y]
    {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρD : G →* Module.End ℂ Y) (TD : R →+* Module.End ℂ Y)
    (χ : Representation ℂ G W) (hk : R →+* ℂ)
    (I : Submodule ℂ (W →ₗ[ℂ] Y)) (hI : ∀ φ : W →ₗ[ℂ] Y, (∀ x, φ ∘ₗ χ x = ρD x ∘ₗ φ) → φ ∈ I)
    (TI : R →+* Module.End ℂ ↥I) (hTI : ∀ (t : R) (f : ↥I), ((TI t f : ↥I) : W →ₗ[ℂ] Y) = TD t ∘ₗ (f : W →ₗ[ℂ] Y))
    (s : W ≃ₗ[ℂ] Module.Dual ℂ W) (hs : ∀ (g : G) (w : W), s (χ g w) = χ.dual g (s w))
    (hW : (Module.finrank ℂ W : ℂ) ≠ 0)
    (Φ : Y →ₗ[ℂ] Module.Dual ℂ W) (hΦ_surj : Function.Surjective Φ)
    (hΦ_G : ∀ x, Φ ∘ₗ ρD x = χ.dual x ∘ₗ Φ) (hΦ_T : ∀ t, Φ ∘ₗ TD t = hk t • Φ) :
    ∃ f : ↥I, f ≠ 0 ∧ ∀ t, TI t f = hk t • f := by
  classical

  let L : Y →ₗ[ℂ] W := s.symm.toLinearMap ∘ₗ Φ
  have hs' : ∀ x (η : Module.Dual ℂ W), s.symm (χ.dual x η) = χ x (s.symm η) := by
    intro x η
    apply s.injective
    rw [LinearEquiv.apply_symm_apply, hs, LinearEquiv.apply_symm_apply]
  have hL_G : ∀ x, L ∘ₗ ρD x = χ x ∘ₗ L := by
    intro x
    refine LinearMap.ext fun y => ?_
    show s.symm (Φ (ρD x y)) = χ x (s.symm (Φ y))
    rw [← hs', ← LinearMap.comp_apply Φ, hΦ_G, LinearMap.comp_apply]
  have hL_T : ∀ t, L ∘ₗ TD t = hk t • L := by
    intro t
    show (s.symm.toLinearMap ∘ₗ Φ) ∘ₗ TD t = hk t • (s.symm.toLinearMap ∘ₗ Φ)
    rw [LinearMap.comp_assoc, hΦ_T, LinearMap.comp_smul]
  have hL_surj : Function.Surjective L := s.symm.surjective.comp hΦ_surj
  obtain ⟨φ₁, hLφ₁, hφ₁G⟩ := exists_equivariant_section χ ρD L hL_G hL_surj
  have hφ₁mem : φ₁ ∈ I := hI φ₁ hφ₁G
  obtain ⟨μ, hμ_apply⟩ : ∃ μ : Module.Dual ℂ ↥I, ∀ f, μ f = LinearMap.trace ℂ W (L ∘ₗ (f : W →ₗ[ℂ] Y)) :=
    ⟨{ toFun := fun f => LinearMap.trace ℂ W (L ∘ₗ (f : W →ₗ[ℂ] Y))
       map_add' := fun f g => by rw [Submodule.coe_add, LinearMap.comp_add, map_add]
       map_smul' := fun c f => by rw [Submodule.coe_smul, LinearMap.comp_smul, map_smul, RingHom.id_apply] },
     fun _ => rfl⟩
  have hμne : μ ≠ 0 := by
    intro h0
    have h1 : μ ⟨φ₁, hφ₁mem⟩ = 0 := by rw [h0]; rfl
    rw [hμ_apply] at h1
    change LinearMap.trace ℂ W (L ∘ₗ φ₁) = 0 at h1
    rw [hLφ₁, LinearMap.trace_id] at h1
    exact hW h1
  have hμco : ∀ t : R, μ ∘ₗ (TI t : ↥I →ₗ[ℂ] ↥I) = hk t • μ := by
    intro t
    refine LinearMap.ext fun f => ?_
    rw [LinearMap.comp_apply, LinearMap.smul_apply, hμ_apply, hμ_apply, hTI]
    exact trace_comp_coeigen L _ (hk t) (hL_T t) _
  exact Module.End.exists_ne_zero_forall_apply_eq_smul_of_dual_comp_eq_smul TI hk μ hμne hμco

section Bridge

variable {R : Type*} [CommRing R] {A : Type} [CommRing A] [Algebra R A] [Algebra A ℂ] [Algebra R ℂ]
  [IsScalarTower R A ℂ] {N : Type*} [AddCommGroup N] [Module R N]

def bridge : ℂ ⊗[A] (A ⊗[R] N) ≃ₗ[ℂ] ℂ ⊗[R] N :=
  TensorProduct.AlgebraTensorModule.cancelBaseChange R A ℂ ℂ N

theorem bridge_tmul (c : ℂ) (a : A) (n : N) :
    bridge (R := R) (c ⊗ₜ[A] (a ⊗ₜ[R] n)) = (a • c) ⊗ₜ[R] n :=
  rfl

theorem bridge_comp_baseChange (F : Module.End A (A ⊗[R] N)) (F₀ : Module.End R N)
    (hF : ∀ (a : A) (n : N), F (a ⊗ₜ[R] n) = a ⊗ₜ[R] F₀ n) :
    (bridge (R := R) (A := A) (N := N)).toLinearMap ∘ₗ F.baseChange ℂ =
      F₀.baseChange ℂ ∘ₗ (bridge (R := R) (A := A) (N := N)).toLinearMap := by
  refine TensorProduct.AlgebraTensorModule.ext fun c y => ?_
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.baseChange_tmul]
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a n => rw [hF, bridge_tmul, bridge_tmul, LinearMap.baseChange_tmul]
  | add y₁ y₂ h₁ h₂ => rw [map_add, TensorProduct.tmul_add, map_add, h₁, h₂, TensorProduct.tmul_add, map_add, map_add]

theorem dualMap_bridge_dualMap (F : Module.End A (A ⊗[R] N)) (F₀ : Module.End R N)
    (hF : ∀ (a : A) (n : N), F (a ⊗ₜ[R] n) = a ⊗ₜ[R] F₀ n) (η : Module.Dual ℂ (ℂ ⊗[R] N)) :
    (bridge (R := R) (A := A) (N := N)).toLinearMap.dualMap ((F₀.baseChange ℂ).dualMap η) =
      (F.baseChange ℂ).dualMap ((bridge (R := R) (A := A) (N := N)).toLinearMap.dualMap η) := by
  refine LinearMap.ext fun z => ?_
  simp only [LinearMap.dualMap_apply, LinearEquiv.coe_coe]
  exact congrArg η (LinearMap.congr_fun (bridge_comp_baseChange F F₀ hF) z).symm

end Bridge

section Equivariant

variable {G : Type*} [Group G] {R : Type*} [CommRing R]
  {W : Type*} [AddCommGroup W] [Module ℂ W] {Y : Type*} [AddCommGroup Y] [Module ℂ Y]
  (χ : Representation ℂ G W) (ρD : G →* Module.End ℂ Y)

def equivariantMaps : Submodule ℂ (W →ₗ[ℂ] Y) where
  carrier := {φ | ∀ x, φ ∘ₗ χ x = ρD x ∘ₗ φ}
  add_mem' {φ ψ} hφ hψ x := by rw [LinearMap.add_comp, LinearMap.comp_add, hφ x, hψ x]
  zero_mem' x := by rw [LinearMap.zero_comp, LinearMap.comp_zero]
  smul_mem' c φ hφ x := by rw [LinearMap.smul_comp, LinearMap.comp_smul, hφ x]

theorem mem_equivariantMaps_iff (φ : W →ₗ[ℂ] Y) : φ ∈ equivariantMaps χ ρD ↔ ∀ x, φ ∘ₗ χ x = ρD x ∘ₗ φ :=
  Iff.rfl

variable (TD : R →+* Module.End ℂ Y) (hcomm : ∀ (t : R) (x : G), TD t * ρD x = ρD x * TD t)

theorem comp_mem_equivariantMaps {S : Module.End ℂ Y} (hS : ∀ x, S * ρD x = ρD x * S)
    {φ : W →ₗ[ℂ] Y} (hφ : φ ∈ equivariantMaps χ ρD) : S ∘ₗ φ ∈ equivariantMaps χ ρD := fun x => by
  rw [LinearMap.comp_assoc, hφ x, ← LinearMap.comp_assoc, ← Module.End.mul_eq_comp, hS x, Module.End.mul_eq_comp,
    LinearMap.comp_assoc]

def postComp (S : Module.End ℂ Y) (hS : ∀ x, S * ρD x = ρD x * S) : Module.End ℂ ↥(equivariantMaps χ ρD) :=
  (LinearMap.llcomp ℂ W Y Y S).restrict fun φ hφ => comp_mem_equivariantMaps χ ρD hS hφ

theorem coe_postComp_apply (S : Module.End ℂ Y) (hS : ∀ x, S * ρD x = ρD x * S) (f : ↥(equivariantMaps χ ρD)) :
    ((postComp χ ρD S hS f : ↥(equivariantMaps χ ρD)) : W →ₗ[ℂ] Y) = S ∘ₗ (f : W →ₗ[ℂ] Y) := rfl

include hcomm in

theorem exists_postCompHom :
    ∃ TI : R →+* Module.End ℂ ↥(equivariantMaps χ ρD),
      ∀ (t : R) (f : ↥(equivariantMaps χ ρD)), ((TI t f : ↥(equivariantMaps χ ρD)) : W →ₗ[ℂ] Y) = TD t ∘ₗ (f : W →ₗ[ℂ] Y) := by
  refine ⟨{ toFun := fun t => postComp χ ρD (TD t) (hcomm t)
            map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }, fun _ _ => rfl⟩
  · refine LinearMap.ext fun f => Subtype.ext ?_
    rw [coe_postComp_apply, map_one, Module.End.one_apply, Module.End.one_eq_id, LinearMap.id_comp]
  · intro s t
    refine LinearMap.ext fun f => Subtype.ext ?_
    rw [coe_postComp_apply, map_mul, Module.End.mul_apply, coe_postComp_apply, coe_postComp_apply, Module.End.mul_eq_comp,
      LinearMap.comp_assoc]
  · refine LinearMap.ext fun f => Subtype.ext ?_
    rw [coe_postComp_apply, map_zero, LinearMap.zero_comp, LinearMap.zero_apply, Submodule.coe_zero]
  · intro s t
    refine LinearMap.ext fun f => Subtype.ext ?_
    rw [coe_postComp_apply, map_add, LinearMap.add_comp, LinearMap.add_apply, Submodule.coe_add, coe_postComp_apply,
      coe_postComp_apply]

end Equivariant

section Card

theorem exists_baseChangeHoms {G : Type*} [Group G] {R : Type*} [CommRing R] {A : Type} [CommRing A] [Algebra A ℂ]
    {X : Type*} [AddCommGroup X] [Module A X] (Gh : G →* Module.End A X) (Th : R →+* Module.End A X)
    (hTG : ∀ (t : R) (x : G), Th t * Gh x = Gh x * Th t) :
    ∃ (ρD : G →* Module.End ℂ (ℂ ⊗[A] X)) (TD : R →+* Module.End ℂ (ℂ ⊗[A] X)),
      (∀ x, ρD x = (Gh x).baseChange ℂ) ∧ (∀ t, TD t = (Th t).baseChange ℂ) ∧
      (∀ t x, TD t * ρD x = ρD x * TD t) := by
  refine ⟨{ toFun := fun x => (Gh x).baseChange ℂ
            map_one' := by simp only [map_one, LinearMap.baseChange_one]
            map_mul' := fun x y => by simp only [map_mul, LinearMap.baseChange_mul] },
          { toFun := fun t => (Th t).baseChange ℂ
            map_one' := by simp only [map_one, LinearMap.baseChange_one]
            map_mul' := fun s t => by simp only [map_mul, LinearMap.baseChange_mul]
            map_zero' := by simp only [map_zero, LinearMap.baseChange_zero]
            map_add' := fun s t => by simp only [map_add, LinearMap.baseChange_add] },
          fun _ => rfl, fun _ => rfl, fun t x => ?_⟩
  show (Th t).baseChange ℂ * (Gh x).baseChange ℂ = (Gh x).baseChange ℂ * (Th t).baseChange ℂ
  rw [← LinearMap.baseChange_mul, ← LinearMap.baseChange_mul, hTG]

end Card

end Ws41.W7

open LocalNewvector Ws41.W7 in
theorem solution
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M') (lam : ℕ) [Fact lam.Prime]
    (O' : Type) [CommRing O'] [IsLocalRing O'] [Algebra ℤ_[lam] O']
    (hlamO' : (lam : O') ∈ IsLocalRing.maximalIdeal O')
    (T : ModularCurve.HeckeAlg →+*
      Module.End O' (O' ⊗[ℤ_[lam]] TateModule lam (ModularCurve.FullLevel.Jac q M')))
    (hT : ∀ (t : ModularCurve.HeckeAlg) (a : O') (x : TateModule lam (ModularCurve.FullLevel.Jac q M')),
      T t (a ⊗ₜ[ℤ_[lam]] x) = a ⊗ₜ[ℤ_[lam]] ModularCurve.FullLevel.tateHecke q M' lam t x)
    (G : CuspidalType.GL2 q →*
      Module.End O' (O' ⊗[ℤ_[lam]] TateModule lam (ModularCurve.FullLevel.Jac q M')))
    (hG : ∀ (x : CuspidalType.GL2 q) (a : O') (y : TateModule lam (ModularCurve.FullLevel.Jac q M')),
      G x (a ⊗ₜ[ℤ_[lam]] y) = a ⊗ₜ[ℤ_[lam]] ModularCurve.FullLevel.tateGL2 q M' lam x y)
    (hTG : ∀ (t : ModularCurve.HeckeAlg) (x : CuspidalType.GL2 q), T t * G x = G x * T t)
    (hLA : ModularCurve.FullLevel.LevelAutInputs q M') (hHC : ModularCurve.FullLevel.HeckeGenCommute q M')
    (hGL : ModularCurve.FullLevel.GL2Laws q M')
    (hin : ModularCurve.HeckeDiamondInputsHAll (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M'))
    [Algebra O' ℂ]
    (g : CuspForm (CongruenceSubgroup.Gamma0 (q ^ 2 * M')) 2) (hg : g.IsNewform)
    (S : Finset ℕ) (chig : CuspForm.heckeAlgebra (q ^ 2 * M') 2 (↑S : Set ℕ) →+* ℂ)
    (hchig : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ q ^ 2 * M') (hℓS : ℓ ∉ (↑S : Set ℕ)),
      chig (CuspForm.heckeAlgebra.T hℓ hℓM hℓS) = ModularFormClass.qCoeff g ℓ)
    (Φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ) (hΦg : g.IsAdelicLiftOf Φ)
    (V : Type) [AddCommGroup V] [Module ℂ V] [DistribMulAction (GL (Fin 2) ℚ_[q]) V]
    [SMulCommClass (GL (Fin 2) ℚ_[q]) ℂ V]
    [FiniteDimensional ℂ
      ↥(LocalNewvector.fixedSubmodule (FLT.SmoothVectors.gl2CongruenceSubgroup q 1) V)]
    (f : V →ₗ[ℂ] LocalNewvector.AdelicSpan Φ)
    (hf : ∀ (x : GL (Fin 2) ℚ_[q]) (v : V), f (x • v) = x • f v) (hfinj : Function.Injective f)
    (hfrange : LinearMap.range f =
      Submodule.span ℂ (Set.range fun x : GL (Fin 2) ℚ_[q] => x • LocalNewvector.AdelicSpan.self Φ))
    (θ : (GaloisField q 2)ˣ →* ℂˣ)
    (W : Subrepresentation (LocalNewvector.gl2ReductionRep q V))
    (hθ : CuspidalType.IsCuspidalOfType θ W.toRepresentation) :
    ∃ hk : ModularCurve.HeckeAlg →+* ℂ,
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ q ^ 2 * M') (hℓS : ℓ ∉ (↑S : Set ℕ)),
          hk (ModularCurve.heckeGen ⟨ℓ, hℓ⟩) = chig (CuspForm.heckeAlgebra.T hℓ hℓM hℓS)) ∧
      ∃ φ : ↥W.toSubmodule →ₗ[ℂ] ℂ ⊗[O'] (O' ⊗[ℤ_[lam]] TateModule lam (ModularCurve.FullLevel.Jac q M')),
        φ ≠ 0 ∧
        (∀ x : CuspidalType.GL2 q, φ ∘ₗ W.toRepresentation x = (G x).baseChange ℂ ∘ₗ φ) ∧
        (∀ t : ModularCurve.HeckeAlg, (T t).baseChange ℂ ∘ₗ φ = hk t • φ) := by
  classical

  obtain ⟨hfinT, -, -⟩ :=
    ModularCurve.FullLevel.exists_galoisRep_isAdicContinuous_heckeRep_gl2Rep_baseChange_tateModule_jac q M' lam
  haveI := hfinT

  letI algZC : Algebra ℤ_[lam] ℂ := ((algebraMap O' ℂ).comp (algebraMap ℤ_[lam] O')).toAlgebra
  haveI : IsScalarTower ℤ_[lam] O' ℂ := IsScalarTower.of_algebraMap_eq fun _ => rfl

  let a : Nat.Primes → ℂ := fun ℓ => if (ℓ : ℕ) ∣ q * M' then 0 else ModularFormClass.qCoeff g ℓ
  let hk : ModularCurve.HeckeAlg →+* ℂ := (MvPolynomial.aeval (R := ℤ) a).toRingHom
  have hk_gen : ∀ ℓ : Nat.Primes, hk (ModularCurve.heckeGen ℓ) = a ℓ := fun ℓ =>
    ModularCurve.aeval_heckeGen a ℓ
  refine ⟨hk, fun ℓ hℓ hℓM hℓS => ?_, ?_⟩
  · rw [hk_gen]
    have hnd : ¬ ℓ ∣ q * M' := fun h => hℓM (by rw [pow_two, mul_assoc]; exact Dvd.dvd.mul_left h q)
    show (if ℓ ∣ q * M' then (0 : ℂ) else ModularFormClass.qCoeff g ℓ) = _
    rw [if_neg hnd, hchig ℓ hℓ hℓM hℓS]

  obtain ⟨ρD, TD, hρD, hTD, hcomm⟩ := exists_baseChangeHoms G T hTG

  obtain ⟨ψ₀, hψ₀inj, hψ₀G, hψ₀T⟩ :=
    ModularCurve.FullLevel.exists_injective_dual_baseChange_tateModule_jac_of_isNewform_of_range_eq_span
      q M' hqM' lam hLA hHC hGL hin hg hΦg V f hf hfinj hfrange
  let β := (bridge (R := ℤ_[lam]) (A := O') (N := TateModule lam (ModularCurve.FullLevel.Jac q M'))).toLinearMap.dualMap
  have hβinj : Function.Injective β :=
    LinearMap.dualMap_injective_of_surjective (LinearEquiv.surjective _)
  let ψ : ↥(fixedSubmodule (FLT.SmoothVectors.gl2CongruenceSubgroup q 1) V) →ₗ[ℂ]
      Module.Dual ℂ (ℂ ⊗[O'] (O' ⊗[ℤ_[lam]] TateModule lam (ModularCurve.FullLevel.Jac q M'))) := β ∘ₗ ψ₀
  have hψinj : Function.Injective ψ := hβinj.comp hψ₀inj
  have hψG : ∀ (x : CuspidalType.GL2 q) (v : ↥(fixedSubmodule (FLT.SmoothVectors.gl2CongruenceSubgroup q 1) V)),
      ψ (gl2ReductionRep q V x v) = (ρD x⁻¹).dualMap (ψ v) := fun x v => by
    show β (ψ₀ (gl2ReductionRep q V x v)) = (ρD x⁻¹).dualMap (β (ψ₀ v))
    rw [hψ₀G, hρD]
    exact dualMap_bridge_dualMap (G x⁻¹) _ (hG x⁻¹) _
  have hψT : ∀ (ℓ : Nat.Primes) (v : ↥(fixedSubmodule (FLT.SmoothVectors.gl2CongruenceSubgroup q 1) V)),
      (TD (ModularCurve.heckeGen ℓ)).dualMap (ψ v) = a ℓ • ψ v := fun ℓ v => by
    show (TD (ModularCurve.heckeGen ℓ)).dualMap (β (ψ₀ v)) = a ℓ • β (ψ₀ v)
    rw [hTD, ← dualMap_bridge_dualMap (T (ModularCurve.heckeGen ℓ)) _ (hT _) _, hψ₀T, map_smul]

  set χ : Representation ℂ (CuspidalType.GL2 q) ↥W.toSubmodule := W.toRepresentation with hχ
  obtain ⟨TI, hTI⟩ := exists_postCompHom χ ρD TD hcomm

  let ψW : ↥W.toSubmodule →ₗ[ℂ] Module.Dual ℂ (ℂ ⊗[O'] (O' ⊗[ℤ_[lam]] TateModule lam (ModularCurve.FullLevel.Jac q M'))) :=
    ψ ∘ₗ W.toSubmodule.subtype
  have hψW_inj : Function.Injective ψW := hψinj.comp Subtype.val_injective
  have hψW_G : ∀ (x : CuspidalType.GL2 q) (w : ↥W.toSubmodule), ψW (χ x w) = (ρD x⁻¹).dualMap (ψW w) :=
    fun x w => hψG x (w : ↥(fixedSubmodule (FLT.SmoothVectors.gl2CongruenceSubgroup q 1) V))
  obtain ⟨Φd, hΦ_apply, hΦ_surj⟩ : ∃ Φd : ℂ ⊗[O'] (O' ⊗[ℤ_[lam]] TateModule lam (ModularCurve.FullLevel.Jac q M')) →ₗ[ℂ]
      Module.Dual ℂ ↥W.toSubmodule, (∀ y w, Φd y w = ψW w y) ∧ Function.Surjective Φd :=
    ⟨ψW.flip, fun _ _ => rfl, (LinearMap.flip_surjective_iff₁).2 hψW_inj⟩
  have hΦ_G : ∀ x, Φd ∘ₗ ρD x = χ.dual x ∘ₗ Φd := by
    intro x
    refine LinearMap.ext fun y => LinearMap.ext fun w => ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hΦ_apply, Representation.dual_apply]
    show ψW w (ρD x y) = Φd y (χ x⁻¹ w)
    rw [hΦ_apply, hψW_G, inv_inv, LinearMap.dualMap_apply]
  have hΦ_gen : ∀ ℓ : Nat.Primes, Φd ∘ₗ TD (ModularCurve.heckeGen ℓ) = a ℓ • Φd := by
    intro ℓ
    refine LinearMap.ext fun y => LinearMap.ext fun w => ?_
    rw [LinearMap.comp_apply, hΦ_apply, LinearMap.smul_apply, LinearMap.smul_apply, hΦ_apply]
    have h1 := congrArg (fun η : Module.Dual ℂ _ => η y)
      (hψT ℓ (w : ↥(fixedSubmodule (FLT.SmoothVectors.gl2CongruenceSubgroup q 1) V)))
    simp only [LinearMap.dualMap_apply, LinearMap.smul_apply] at h1
    exact h1
  have hΦ_T : ∀ t, Φd ∘ₗ TD t = hk t • Φd := by
    intro t
    induction t using MvPolynomial.induction_on with
    | C c =>
      rw [eq_intCast MvPolynomial.C c, map_intCast TD c, map_intCast hk c]
      refine LinearMap.ext fun y => ?_
      rw [LinearMap.comp_apply, Module.End.intCast_apply, LinearMap.smul_apply, map_zsmul]
      exact (Int.cast_smul_eq_zsmul ℂ c (Φd y)).symm
    | add p₁ p₂ h₁ h₂ => rw [map_add, map_add, LinearMap.comp_add, h₁, h₂, add_smul]
    | mul_X p ℓ hp =>
      have hX : (MvPolynomial.X ℓ : ModularCurve.HeckeAlg) = ModularCurve.heckeGen ℓ := rfl
      rw [map_mul, map_mul, Module.End.mul_eq_comp, ← LinearMap.comp_assoc, hp, LinearMap.smul_comp, hX,
        hΦ_gen, hk_gen, smul_smul]

  obtain ⟨s, hs⟩ := CuspidalType.IsCuspidalOfType.exists_linearEquiv_comm_of_isCuspidalOfType hθ hθ.dual
  have hW : (Module.finrank ℂ ↥W.toSubmodule : ℂ) ≠ 0 := by
    have hpos : 0 < Module.finrank ℂ ↥W.toSubmodule := by
      rw [hθ.finrank_eq]; have := (Fact.out : q.Prime).two_le; omega
    exact Nat.cast_ne_zero.2 hpos.ne'

  obtain ⟨fI, hfne, hfI⟩ := closing_core ρD TD χ hk (equivariantMaps χ ρD)
    (fun φ hφ => (mem_equivariantMaps_iff χ ρD φ).2 hφ) TI hTI s hs hW Φd hΦ_surj hΦ_G hΦ_T
  refine ⟨(fI : ↥W.toSubmodule →ₗ[ℂ] _), fun h => hfne ((Submodule.coe_eq_zero).1 h), fun x => ?_, fun t => ?_⟩
  · rw [← hρD]; exact fI.2 x
  · have := congrArg Subtype.val (hfI t)
    rw [hTI, Submodule.coe_smul, hTD] at this
    exact this

end

end S_ModularCurve_FullLevel_exists_ringHom_heckeGen_eq_and_exists_ne_zero_comm_baseChange_tateModule_jac
end P2MW
export P2MW.S_ModularCurve_FullLevel_exists_ringHom_heckeGen_eq_and_exists_ne_zero_comm_baseChange_tateModule_jac (solution)
