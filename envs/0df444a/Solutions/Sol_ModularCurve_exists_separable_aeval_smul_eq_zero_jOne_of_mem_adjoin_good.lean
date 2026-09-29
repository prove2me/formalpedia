-- Prove2me | solution 1 for ModularCurve.exists_separable_aeval_smul_eq_zero_jOne_of_mem_adjoin_good
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/20bac6d1-7468-57df-ad09-c37d8fa7f69d

import Mathlib
import Definitions.Def_CuspForm_PrimitiveFormGamma1
import Definitions.Def_ModularCurve_X1HeckeModule
import Definitions.Def_CuspForm_Gamma1HeckeOperators
import Definitions.Def_EllipticCurve_TateModule
import Theorems.Thm_UpperHalfPlane_eq_of_forall_qCoeff_eq
import Theorems.Thm_CuspForm_qCoeff_heckeTLinOne
import Theorems.Thm_CuspForm_HasNebentypus_diamondLinOne_apply_eq_smul
import Theorems.Thm_ModularCurve_exists_injective_ringHom_adjoin_heckeDiamondGenBar_cuspForm
import Theorems.Thm_CuspForm_exists_basis_hasNebentypus_qCoeff_hecke_eigen
import Theorems.Thm_ModularCurve_exists_map_eq_charpoly_heckeTLinOne_and_charpoly_tateHeckeRepOne_jOne_eq_map_sq
import Theorems.Thm_CuspForm_finiteDimensional_Gamma1
import Theorems.Thm_ModularCurve_moduleFinite_padicInt_tateModule_jOne
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_separable_aeval_smul_eq_zero_jOne_of_mem_adjoin_good
p2m_attr_erase "instance" "ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicCurve.CellDissection.fintypeV"
p2m_attr_erase "instance" "AlgebraicCurve.CellDissection.fintypeC AlgebraicCurve.CellDissection.fintypeE AlgebraicCurve.CellDissection.decEqV AlgebraicCurve.CellDissection.decEqC AlgebraicCurve.CellDissection.decEqE CohCarrier.iotaDeg_range_finiteIndex CohCarrier.Gamma0Upper_finiteIndex ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime CuspForm.heckeAlgebra.instCommRing CuspForm.heckeAlgebra.instIsMulCommutative CuspForm.heckeAlgebra.instIsAddTorsionFree CuspForm.GammaH_finiteIndex ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0 HeckeEis.instFiniteIndexHeckeUpper HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par"
p2m_attr_erase "simp" "ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff"
p2m_attr_erase "simp" "ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers"
p2m_attr_erase "simp" "AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.abelJacobiDiv_single AlgebraicCurve.AnalyticCoord.mk.injEq AlgebraicCurve.Cell.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.injEq AlgebraicCurve.CellDissection.mk.sizeOf_spec AlgebraicCurve.Cell.mk.injEq AlgebraicCurve.CellDissection.mk.injEq AlgebraicCurve.AnalyticCoord.mk.sizeOf_spec ModularCurve.JH.torsionGaloisRep_apply CohCarrier.conjUpperMat_apply_11 CohCarrier.conjUpperMat_apply_10 CohCarrier.mem_Gamma0Upper CohCarrier.val_gamma0Units ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.qExpandAlgHomC_apply WeierstrassCurve.reducePoint_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.LevelN.coe_jGen PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄"
p2m_attr_erase "simp" "ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring HahnSeries.ramScale_apply ModularCurve.ProjectiveLine.map_mk FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero ModularCurve.coe_heckeAlphaHBar ModularCurve.coe_heckeBetaHBarOf CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq ModularCurve.dualHeckeRep_apply_apply ModularCurve.coe_segmentPath ModularCurve.cuspHeckeAeval_heckeGen ModularCurve.coe_periodLatticeRestrict_apply CuspForm.heckeAlgebra.coe_U CuspForm.heckeAlgebra.coe_T ModularForm.coe_heckeTLin_apply CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply ModularForm.coe_heckeULin_apply ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one CohCarrier.jConjGammaH_jConjGammaH CohCarrier.coe_jConjGammaH CohCarrier.charInvolution_apply ModularCurve.Period.jConjMat_apply_zero_one ModularCurve.Period.jConjSL_coe ModularCurve.Period.jConjMat_apply_one_zero ModularCurve.Period.jConjMat_apply_one_one ModularCurve.Period.jConjGamma0_coe ModularCurve.Period.charInvolution_apply ModularCurve.Period.jConjMat_apply_zero_zero"
p2m_attr_erase "simp" "ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply ModularCurve.ComplexPlaceDictionaryOf.pt_ofGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.injEq ModularCurve.ComplexPlaceDictionaryOf.pt_toGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.sizeOf_spec ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero HeckeEis.coeffCoboundaryMap_apply"

set_option autoImplicit false
open scoped TensorProduct

noncomputable section

namespace C2aI

open Polynomial Module

theorem exists_int_separable_annihilator {K V : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V]
    {n : ℕ} (b : Basis (Fin n) K V) (T : Module.End K V) (μ : Fin n → K)
    (hT : ∀ i, T (b i) = μ i • b i) (hint : ∀ i, IsIntegral ℤ (μ i)) :
    ∃ P : ℤ[X], P ≠ 0 ∧ (P.map (Int.castRingHom ℚ)).Separable ∧ Polynomial.aeval T P = 0 := by
  classical
  letI : Algebra ℚ K := (algebraMap ℚ K).toAlgebra

  let s : Finset ℤ[X] := Finset.univ.image fun i => minpoly ℤ (μ i)
  refine ⟨∏ q ∈ s, q, ?_, ?_, ?_⟩
  ·
    rw [Finset.prod_ne_zero_iff]
    intro q hq
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hq
    exact minpoly.ne_zero (hint i)
  ·
    rw [Polynomial.map_prod]
    refine Polynomial.separable_prod' ?_ ?_
    · intro q hq q' hq' hne
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hq
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hq'
      have hi : (minpoly ℤ (μ i)).map (Int.castRingHom ℚ) = minpoly ℚ (μ i) :=
        (minpoly.isIntegrallyClosed_eq_field_fractions' ℚ (hint i)).symm
      have hj : (minpoly ℤ (μ j)).map (Int.castRingHom ℚ) = minpoly ℚ (μ j) :=
        (minpoly.isIntegrallyClosed_eq_field_fractions' ℚ (hint j)).symm
      rw [hi, hj]
      have hne' : minpoly ℚ (μ i) ≠ minpoly ℚ (μ j) := by
        intro h; apply hne; rw [← Polynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective |>.eq_iff, hi, hj, h]
      have hirr_i := minpoly.irreducible (hint i).tower_top (A := ℚ)
      have hirr_j := minpoly.irreducible (hint j).tower_top (A := ℚ)
      refine (hirr_i.coprime_iff_not_dvd).2 fun hdvd => hne' ?_
      exact eq_of_monic_of_associated (minpoly.monic ((hint i).tower_top)) (minpoly.monic ((hint j).tower_top))
        (hirr_i.associated_of_dvd hirr_j hdvd)
    · intro q hq
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hq
      rw [show (minpoly ℤ (μ i)).map (Int.castRingHom ℚ) = minpoly ℚ (μ i) from
        (minpoly.isIntegrallyClosed_eq_field_fractions' ℚ (hint i)).symm]
      exact (minpoly.irreducible ((hint i).tower_top (A := ℚ))).separable
  ·
    refine b.ext fun i => ?_
    rw [LinearMap.zero_apply]
    have hev : Module.End.HasEigenvector T (μ i) (b i) :=
      ⟨Module.End.mem_eigenspace_iff.2 (hT i), b.ne_zero i⟩
    rw [← Polynomial.aeval_map_algebraMap K, Module.End.aeval_apply_of_hasEigenvector hev]
    have hdvd : minpoly ℤ (μ i) ∣ ∏ q ∈ s, q :=
      Finset.dvd_prod_of_mem _ (Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩)
    have h0 : Polynomial.aeval (μ i) (∏ q ∈ s, q) = 0 :=
      Polynomial.aeval_eq_zero_of_dvd_aeval_eq_zero hdvd (minpoly.aeval ℤ (μ i))
    rw [Polynomial.eval_map_algebraMap, h0, zero_smul]

section QExp

open CongruenceSubgroup ModularForm ModularFormClass UpperHalfPlane Filter Function
open scoped MatrixGroups ModularForm

local notation "Γ₁ℝ" M => ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

variable {M : ℕ} {k : ℤ}

theorem one_mem_strictPeriods (M : ℕ) : (1 : ℝ) ∈ (Γ₁ℝ M).strictPeriods := by
  rw [CongruenceSubgroup.strictPeriods_Gamma1]; exact AddSubgroup.mem_zmultiples _

theorem cusp_periodic (F : CuspForm (Γ₁ℝ M) k) : Periodic (⇑F ∘ ofComplex) 1 :=
  SlashInvariantFormClass.periodic_comp_ofComplex F (one_mem_strictPeriods M)

theorem cusp_holo (F : CuspForm (Γ₁ℝ M) k) :
    MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) (⇑F) := F.holo'

theorem cusp_bdd (F : CuspForm (Γ₁ℝ M) k) : IsBoundedAtImInfty (⇑F : ℍ → ℂ) := by
  haveI : Fact (IsCusp OnePoint.infty (Γ₁ℝ M)) :=
    ⟨(Γ₁ℝ M).isCusp_of_mem_strictPeriods one_pos (one_mem_strictPeriods M)⟩
  exact ModularFormClass.bdd_at_infty F

theorem cusp_ext_of_qCoeff {F G : CuspForm (Γ₁ℝ M) k} (h : ∀ n : ℕ, qCoeff (⇑F) n = qCoeff (⇑G) n) :
    F = G :=
  DFunLike.coe_injective (UpperHalfPlane.eq_of_forall_qCoeff_eq (cusp_periodic F) (cusp_holo F)
    (cusp_bdd F) (cusp_periodic G) (cusp_holo G) (cusp_bdd G) h)

theorem analyticAt_cuspFunction (F : CuspForm (Γ₁ℝ M) k) : AnalyticAt ℂ (cuspFunction 1 (⇑F)) 0 :=
  analyticAt_cuspFunction_zero one_pos (cusp_periodic F) (cusp_holo F) (cusp_bdd F)

theorem qCoeff_smul (c : ℂ) (F : CuspForm (Γ₁ℝ M) k) (n : ℕ) :
    qCoeff (⇑(c • F)) n = c * qCoeff (⇑F) n := by
  rw [qCoeff, qCoeff, CuspForm.IsGLPos.coe_smul, qExpansion_smul (analyticAt_cuspFunction F) c, map_smul,
    smul_eq_mul]

end QExp

section Cusp

open CongruenceSubgroup ModularForm ModularFormClass
open scoped MatrixGroups ModularForm

variable {M : ℕ} [NeZero M]

omit [NeZero M] in

theorem hecke_eigen_of_rel {ε : DirichletCharacter ℂ M} {f : CuspForm (Gamma1 M) 2}
    (hneb : CuspForm.HasNebentypus ε f) {p : ℕ} (hp : p.Prime) (hpM : ¬ p ∣ M) (lam : ℂ)
    (hrel : ∀ m : ℕ, qCoeff (⇑f) (p * m) +
        ε (p : ZMod M) * (p : ℂ) ^ ((2 : ℤ) - 1) * (if p ∣ m then qCoeff (⇑f) (m / p) else 0) =
      lam * qCoeff (⇑f) m) :
    CuspForm.heckeTLinOne 2 hp hpM f = lam • f := by
  refine cusp_ext_of_qCoeff fun m => ?_
  rw [CuspForm.qCoeff_heckeTLinOne 2 hp hpM f m,
    hneb.diamondLinOne_apply_eq_smul ((Nat.Prime.coprime_iff_not_dvd hp).2 hpM), qCoeff_smul, qCoeff_smul,
    ← hrel m]
  split_ifs <;> ring

omit [NeZero M] in
theorem dirichlet_pow_totient (χ : DirichletCharacter ℂ M) {ℓ : ℕ} (hℓ : Nat.Coprime ℓ M) :
    χ (ℓ : ZMod M) ^ Nat.totient M = 1 := by
  rw [← ZMod.coe_unitOfCoprime ℓ hℓ, ← map_pow, ← Units.val_pow_eq_pow_val, ZMod.pow_totient,
    Units.val_one, map_one]

theorem isIntegral_dirichlet (χ : DirichletCharacter ℂ M) {ℓ : ℕ} (hℓ : Nat.Coprime ℓ M) :
    IsIntegral ℤ (χ (ℓ : ZMod M)) :=
  IsIntegral.of_pow (Nat.totient_pos.2 (NeZero.pos M)) (by rw [dirichlet_pow_totient χ hℓ]; exact isIntegral_one)

theorem noZeroSMulDivisors_tateModule (p : ℕ) [Fact p.Prime] (J : Type) [AddCommGroup J] :
    NoZeroSMulDivisors ℤ_[p] (TateModule p J) := by
  refine ⟨fun {a x} hax => ?_⟩
  by_cases ha : a = 0
  · exact Or.inl ha
  right
  obtain ⟨k, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha (PadicInt.irreducible_p (p := p))
  have hpk : ((p : ℤ_[p]) ^ k) • x = 0 := by
    have := congrArg (fun y => ((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) • y) hax
    simp only [smul_zero] at this
    rwa [← mul_smul, ← mul_assoc, Units.inv_mul, one_mul] at this
  apply Subtype.ext
  funext n
  have h1 := TateModule.compat_pow x n k
  have h2 : (((((p ^ k : ℕ) : ℤ_[p])) • x : TateModule p J) : ℕ → J) (n + k) = 0 := by
    rw [Nat.cast_pow, hpk]; rfl
  rw [TateModule.natCast_padicInt_smul_apply] at h2
  rw [← h1, h2]
  rfl

theorem free_tateModule (p : ℕ) [Fact p.Prime] (J : Type) [AddCommGroup J] [Module.Finite ℤ_[p] (TateModule p J)] :
    Module.Free ℤ_[p] (TateModule p J) := by
  haveI := noZeroSMulDivisors_tateModule p J
  exact Module.free_of_finite_type_torsion_free'

theorem isIntegral_heckeT_eigenvalue (M : ℕ) [NeZero M] {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M)
    {f : CuspForm (Gamma1 M) 2} (hf : f ≠ 0) {lam : ℂ}
    (h : CuspForm.heckeTLinOne 2 hℓ hℓM f = lam • f) : IsIntegral ℤ lam := by
  haveI : FiniteDimensional ℂ (CuspForm (CongruenceSubgroup.Gamma1 M) 2) := CuspForm.finiteDimensional_Gamma1 M 2
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Module.Finite ℤ_[2] (TateModule 2 (ModularCurve.JOne M)) :=
    ModularCurve.moduleFinite_padicInt_tateModule_jOne M 2
  haveI : Module.Free ℤ_[2] (TateModule 2 (ModularCurve.JOne M)) := free_tateModule 2 _
  obtain ⟨Q, hQm, hQc, -⟩ :=
    ModularCurve.exists_map_eq_charpoly_heckeTLinOne_and_charpoly_tateHeckeRepOne_jOne_eq_map_sq M 2 hℓ hℓM
  refine ⟨Q, hQm, ?_⟩
  have hCH := LinearMap.aeval_self_charpoly (CuspForm.heckeTLinOne 2 hℓ hℓM)
  rw [← hQc] at hCH
  have hev : Module.End.HasEigenvector (CuspForm.heckeTLinOne 2 hℓ hℓM) lam f :=
    ⟨Module.End.mem_eigenspace_iff.2 h, hf⟩
  have happ := congrArg (fun g => g f) hCH
  simp only [LinearMap.zero_apply] at happ
  rw [Module.End.aeval_apply_of_hasEigenvector hev, smul_eq_zero] at happ
  rcases happ with h0 | h0
  · rwa [Polynomial.eval_map_algebraMap] at h0
  · exact absurd h0 hf

end Cusp

end C2aI

section Main

p2m_open "CongruenceSubgroup ModularCurve~IsCusp P2MW.S_ModularCurve_exists_separable_aeval_smul_eq_zero_jOne_of_mem_adjoin_good.C2aI"

set_option maxHeartbeats 2400000 in
theorem solution
    (M : ℕ) [NeZero M] (hin : ModularCurve.HeckeDiamondInputsAll M) (hcomm : ModularCurve.HeckeDiamondCommuteBar M)
    (S : Finset ℕ) :
    letI := ModularCurve.heckeModuleOneBar M
    ∀ w ∈ (Algebra.adjoin ℤ
        {x : ModularCurve.HeckeAlgOne |
          ∃ ℓ : Nat.Primes, ¬ (ℓ : ℕ) ∣ M ∧ (ℓ : ℕ) ∉ S ∧
            (x = ModularCurve.heckeGenOne ℓ ∨ x = ModularCurve.diamondGen (ℓ : ℕ))}),
      ∃ P : Polynomial ℤ, P ≠ 0 ∧ (P.map (Int.castRingHom ℚ)).Separable ∧
        ∀ x : ModularCurve.JOne M, (Polynomial.aeval w P : ModularCurve.HeckeAlgOne) • x = 0 := by
  letI := ModularCurve.heckeModuleOneBar M
  intro w hw
  classical
  obtain ⟨Φ, hΦinj, hΦT, hΦd⟩ := ModularCurve.exists_injective_ringHom_adjoin_heckeDiamondGenBar_cuspForm M hin hcomm
  obtain ⟨n, b, hb⟩ := CuspForm.exists_basis_hasNebentypus_qCoeff_hecke_eigen M 2
  choose ε hneb lamf hlam using hb

  obtain ⟨ψ, hψ⟩ : ∃ ψ : ModularCurve.HeckeAlgOne →+* Module.End ℂ (CuspForm (Gamma1 M) 2),
      ∀ t, ψ t = Φ (ModularCurve.heckeEvalOneBarAux hcomm t) :=
    ⟨Φ.comp (ModularCurve.heckeEvalOneBarAux hcomm).toRingHom, fun _ => rfl⟩

  have diag : ∀ t ∈ (Algebra.adjoin ℤ
        {x : ModularCurve.HeckeAlgOne |
          ∃ ℓ : Nat.Primes, ¬ (ℓ : ℕ) ∣ M ∧ (ℓ : ℕ) ∉ S ∧
            (x = ModularCurve.heckeGenOne ℓ ∨ x = ModularCurve.diamondGen (ℓ : ℕ))}),
      ∃ μ : Fin n → ℂ, (∀ i, IsIntegral ℤ (μ i)) ∧ ∀ i, ψ t (b i) = μ i • b i := by
    intro t ht
    induction ht using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨ℓ, hℓM, -, hx⟩ := hx
      have hcop : Nat.Coprime (ℓ : ℕ) M := (Nat.Prime.coprime_iff_not_dvd ℓ.prop).2 hℓM
      rcases hx with rfl | rfl
      ·
        have e0 : ModularCurve.heckeEvalOneBarAux hcomm (ModularCurve.heckeGenOne ℓ) =
            ⟨ModularCurve.heckeOperatorOneBar M ℓ, Algebra.subset_adjoin (Set.mem_range_self (Sum.inl ℓ))⟩ := by
          show ModularCurve.heckeEvalOneBarAux hcomm (MvPolynomial.X (Sum.inl ℓ)) = _
          rw [ModularCurve.heckeEvalOneBarAux_X]
          exact Subtype.ext (ModularCurve.heckeDiamondGenBar_inl M ℓ)
        have hT : ∀ i, CuspForm.heckeTLinOne 2 ℓ.prop hℓM (b i) = lamf i ℓ ℓ.prop hℓM • b i := fun i =>
          hecke_eigen_of_rel (hneb i) ℓ.prop hℓM _ (hlam i ℓ ℓ.prop hℓM)
        refine ⟨fun i => lamf i ℓ ℓ.prop hℓM, fun i => isIntegral_heckeT_eigenvalue M ℓ.prop hℓM (b.ne_zero i) (hT i),
          fun i => ?_⟩
        rw [hψ, e0, hΦT ℓ hℓM, hT]
      ·
        have e0 : ModularCurve.heckeEvalOneBarAux hcomm (ModularCurve.diamondGen (ℓ : ℕ)) =
            ⟨ModularCurve.diamondOneBar M ℓ, Algebra.subset_adjoin (Set.mem_range_self (Sum.inr (ℓ : ℕ)))⟩ := by
          show ModularCurve.heckeEvalOneBarAux hcomm (MvPolynomial.X (Sum.inr (ℓ : ℕ))) = _
          rw [ModularCurve.heckeEvalOneBarAux_X]
          exact Subtype.ext (ModularCurve.heckeDiamondGenBar_inr M ℓ)
        refine ⟨fun i => ε i ((ℓ : ℕ) : ZMod M), fun i => isIntegral_dirichlet (ε i) hcop, fun i => ?_⟩
        rw [hψ, e0, hΦd ℓ hcop, (hneb i).diamondLinOne_apply_eq_smul hcop]
    | algebraMap r =>
      refine ⟨fun _ => (r : ℂ), fun _ => ?_, fun i => ?_⟩
      · exact (isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := r))
      · rw [eq_intCast (algebraMap ℤ ModularCurve.HeckeAlgOne) r, map_intCast, Module.End.intCast_apply]
        exact (Int.cast_smul_eq_zsmul ℂ r (b i)).symm
    | add x y hx hy ihx ihy =>
      obtain ⟨μ₁, h₁i, h₁⟩ := ihx
      obtain ⟨μ₂, h₂i, h₂⟩ := ihy
      refine ⟨fun i => μ₁ i + μ₂ i, fun i => (h₁i i).add (h₂i i), fun i => ?_⟩
      rw [map_add, LinearMap.add_apply, h₁, h₂, add_smul]
    | mul x y hx hy ihx ihy =>
      obtain ⟨μ₁, h₁i, h₁⟩ := ihx
      obtain ⟨μ₂, h₂i, h₂⟩ := ihy
      refine ⟨fun i => μ₁ i * μ₂ i, fun i => (h₁i i).mul (h₂i i), fun i => ?_⟩
      rw [map_mul, Module.End.mul_apply, h₂, map_smul, h₁, smul_smul, mul_comm]
  obtain ⟨μ, hμint, hμ⟩ := diag w hw
  obtain ⟨P, hP0, hPsep, hPT⟩ := exists_int_separable_annihilator b (ψ w) μ hμ hμint
  refine ⟨P, hP0, hPsep, fun x => ?_⟩
  have h1 : ψ (Polynomial.aeval w P) = 0 := by
    have h := Polynomial.aeval_algHom_apply ψ.toIntAlgHom w P
    rw [RingHom.toIntAlgHom_apply, RingHom.toIntAlgHom_apply] at h
    rw [← h]
    exact hPT
  have h2 : ModularCurve.heckeEvalOneBarAux hcomm (Polynomial.aeval w P) = 0 :=
    hΦinj (by rw [← hψ, h1, map_zero])
  rw [ModularCurve.heckeModuleOneBar_smul_def hcomm, ModularCurve.heckeEvalOneBar_apply, h2]
  rfl

end Main

end
end S_ModularCurve_exists_separable_aeval_smul_eq_zero_jOne_of_mem_adjoin_good
end P2MW
export P2MW.S_ModularCurve_exists_separable_aeval_smul_eq_zero_jOne_of_mem_adjoin_good (solution)
