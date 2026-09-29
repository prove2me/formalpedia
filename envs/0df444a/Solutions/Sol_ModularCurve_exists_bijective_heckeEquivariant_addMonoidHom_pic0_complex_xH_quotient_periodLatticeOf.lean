-- Prove2me | solution 1 for ModularCurve.exists_bijective_heckeEquivariant_addMonoidHom_pic0_complex_xH_quotient_periodLatticeOf
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/972aed07-44ae-51aa-8ce7-5fc51f9c7cf9

import Mathlib
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_CuspForm_HeckeOperatorFormsGammaH
import Definitions.Def_ModularCurve_PeriodOf
import Definitions.Def_GaloisRep_ComplexConjugation
import Definitions.Def_ModularCurve_ComplexPlaceDictionaryOf
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_CohCarrier_CharInvolution
import Definitions.Def_ModularCurve_JqCoeff
import Theorems.Thm_ModularCurve_exists_complexPlaceDictionaryOf
import Theorems.Thm_ModularCurve_ComplexPlaceDictionaryOf_exists_pt_eq_of_mem
import Theorems.Thm_ModularCurve_addSubgroupClosure_range_periodAlongOf_eq_top
import Theorems.Thm_ModularCurve_exists_hasEquivariantPrimitiveOf
import Theorems.Thm_ModularCurve_JOneES_exists_transcendental_finiteDimensional_laurentBaseChange
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_isAlgClosed_of_transcendental
import Theorems.Thm_ModularCurve_ComplexPlaceDictionaryOf_abelJacobi_mem_periodLatticeOf_gammaH_of_isPrincipal
import Theorems.Thm_ModularCurve_ComplexPlaceDictionaryOf_isPrincipal_of_abelJacobi_mem_periodLatticeOf_gammaH
import Theorems.Thm_ModularCurve_ComplexPlaceDictionaryOf_exists_mapDomain_eq_heckeDivHBar_abelJacobi_sub_mem_periodLatticeOf
import Theorems.Thm_ModularCurve_ComplexPlaceDictionaryOf_ofAlgAut_smul_pt_eq_pt_inv_smul
import Theorems.Thm_ModularCurve_ComplexPlaceDictionaryOf_arithmeticGalois_complexConjAlgEquiv_smul_pt
import Theorems.Thm_AlgebraicCurve_Place_exists_forall_ord_eq
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Theorems.Thm_ModularCurve_periodAlongOf_eq_neg_conj_periodAlongOf_J_smul
import Theorems.Thm_CuspForm_stableD
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_bijective_heckeEquivariant_addMonoidHom_pic0_complex_xH_quotient_periodLatticeOf
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0 HeckeEis.instFiniteIndexHeckeUpper FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions"
p2m_attr_erase "instance" "FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.qExpandAlgHomC_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single"
p2m_attr_erase "simp" "ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mem_poleSubmodule HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero ModularCurve.LevelN.coe_jGen AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero HeckeEis.coeffCoboundaryMap_apply"

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open UpperHalfPlane AlgebraicCurve
open scoped MatrixGroups Topology ModularForm

namespace ModularCurve
p2m_export "ModularCurve" "heckeAlphaHBar heckeBetaHBar HeckeAlphaHBarIntegral HeckeBetaHBarIntegral heckeDivHBar heckePic0HBar HeckeInputsHAlong heckeOperatorHAlong heckeOperatorHAlong_eq translation_mem_GammaH xHFunctionField xHTopFunctionFieldC IsIntegralQExp intSeriesC qExpFunctionFieldC intFormRatiosC_subset div_mem_qExpFunctionFieldC arithmeticGalois galois_smul_pic0_def coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange intervalIntegrable_periodIntegrandOf periodAlongOf periodAlongOf_apply periodLatticeOf clamp01_of_mem segmentPoint continuous_segmentPoint segmentPath coe_segmentPath ComplexPlaceDictionaryOf Period.jConjSL jqModC map_jqModC exists_complexPlaceDictionaryOf ComplexPlaceDictionaryOf.exists_pt_eq_of_mem addSubgroupClosure_range_periodAlongOf_eq_top exists_hasEquivariantPrimitiveOf JOneES.exists_transcendental_finiteDimensional_laurentBaseChange ComplexPlaceDictionaryOf.abelJacobi_mem_periodLatticeOf_gammaH_of_isPrincipal ComplexPlaceDictionaryOf.isPrincipal_of_abelJacobi_mem_periodLatticeOf_gammaH ComplexPlaceDictionaryOf.exists_mapDomain_eq_heckeDivHBar_abelJacobi_sub_mem_periodLatticeOf ComplexPlaceDictionaryOf.ofAlgAut_smul_pt_eq_pt_inv_smul ComplexPlaceDictionaryOf.arithmeticGalois_complexConjAlgEquiv_smul_pt jqModC_mem_intFormRatiosC periodAlongOf_eq_neg_conj_periodAlongOf_J_smul"
namespace AbelJacobiHGlue
p2m_open "ModularCurve"

section FTC

variable (Γ : Subgroup SL(2, ℤ))

theorem hasDerivAt_affine (a b : ℂ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (1 - (s : ℂ)) * a + (s : ℂ) * b) (b - a) t := by
  have h1 : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := Complex.ofRealCLM.hasDerivAt
  have h2 : HasDerivAt (fun s : ℝ => (1 - (s : ℂ)) * a) (-(1 : ℂ) * a) t := by
    simpa using ((hasDerivAt_const t (1 : ℂ)).sub h1).mul_const a
  have h3 : HasDerivAt (fun s : ℝ => (s : ℂ) * b) (1 * b) t := h1.mul_const b
  have := h2.add h3
  convert this using 1 <;> try rfl
  ring

omit Γ in
theorem segmentPoint_eq_of_mem {τ₀ τ₁ : ℍ} {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ModularCurve.segmentPoint τ₀ τ₁ t = (1 - (t : ℂ)) * (τ₀ : ℂ) + (t : ℂ) * (τ₁ : ℂ) := by
  simp only [ModularCurve.segmentPoint, ModularCurve.clamp01_of_mem ht, Complex.real_smul,
    Complex.ofReal_sub, Complex.ofReal_one]

theorem periodAlongOf_eq_sub (f : CuspForm Γ 2)
    {F : ℍ → ℂ} (hF : ∀ τ : ℍ, HasDerivAt (F ∘ ofComplex) (f τ) ↑τ) (τ₀ τ₁ : ℍ) :
    ModularCurve.periodAlongOf Γ τ₀ τ₁ f = F τ₁ - F τ₀ := by
  rw [ModularCurve.periodAlongOf_apply]
  set g : ℝ → ℂ := fun t => F (ModularCurve.segmentPath τ₀ τ₁ t) with hg
  have hgF : ∀ t, g t = (F ∘ ofComplex) (ModularCurve.segmentPoint τ₀ τ₁ t) := by
    intro t
    simp only [hg, Function.comp]
    congr 1
    rw [← ModularCurve.coe_segmentPath, ofComplex_apply]
  have hg0 : g 0 = F τ₀ := by
    rw [hgF]
    have : ModularCurve.segmentPoint τ₀ τ₁ 0 = (τ₀ : ℂ) := by
      rw [segmentPoint_eq_of_mem ⟨le_rfl, zero_le_one⟩]; push_cast; ring
    simp only [Function.comp, this, ofComplex_apply]
  have hg1 : g 1 = F τ₁ := by
    rw [hgF]
    have : ModularCurve.segmentPoint τ₀ τ₁ 1 = (τ₁ : ℂ) := by
      rw [segmentPoint_eq_of_mem ⟨zero_le_one, le_rfl⟩]; push_cast; ring
    simp only [Function.comp, this, ofComplex_apply]
  have hFcont : ∀ τ : ℍ, ContinuousAt (F ∘ ofComplex) (τ : ℂ) := fun τ => (hF τ).continuousAt
  have hgcont : Continuous g := by
    have : g = (F ∘ ofComplex) ∘ ModularCurve.segmentPoint τ₀ τ₁ := funext hgF
    rw [this]
    refine continuous_iff_continuousAt.mpr fun t => ?_
    refine ContinuousAt.comp ?_ (ModularCurve.continuous_segmentPoint τ₀ τ₁).continuousAt
    have := hFcont (ModularCurve.segmentPath τ₀ τ₁ t)
    rwa [ModularCurve.coe_segmentPath] at this
  have hderiv : ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivAt g (f (ModularCurve.segmentPath τ₀ τ₁ t) * ((τ₁ : ℂ) - τ₀)) t := by
    intro t ht
    have hpath : HasDerivAt (ModularCurve.segmentPoint τ₀ τ₁) ((τ₁ : ℂ) - τ₀) t := by
      refine (hasDerivAt_affine (τ₀ : ℂ) (τ₁ : ℂ) t).congr_of_eventuallyEq ?_
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
      exact segmentPoint_eq_of_mem (Set.Ioo_subset_Icc_self hs)
    have hFat : HasDerivAt (F ∘ ofComplex) (f (ModularCurve.segmentPath τ₀ τ₁ t))
        (ModularCurve.segmentPoint τ₀ τ₁ t) := by
      have := hF (ModularCurve.segmentPath τ₀ τ₁ t)
      rwa [ModularCurve.coe_segmentPath] at this
    have hcomp := hFat.comp t hpath
    have : g = (F ∘ ofComplex) ∘ ModularCurve.segmentPoint τ₀ τ₁ := funext hgF
    rw [this]
    exact hcomp
  have hint : IntervalIntegrable
      (fun t => f (ModularCurve.segmentPath τ₀ τ₁ t) * ((τ₁ : ℂ) - τ₀)) MeasureTheory.volume 0 1 :=
    ModularCurve.intervalIntegrable_periodIntegrandOf Γ τ₀ τ₁ f 0 1
  have key := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one
    hgcont.continuousOn hderiv hint
  rw [key, hg0, hg1]

variable [Γ.FiniteIndex]

theorem exists_primitive (f : CuspForm Γ 2) :
    ∃ F : ℍ → ℂ, ∀ τ : ℍ, HasDerivAt (F ∘ ofComplex) (f τ) ↑τ := by
  obtain ⟨F, hF⟩ := ModularCurve.exists_hasEquivariantPrimitiveOf Γ f
  exact ⟨F, hF.1⟩

theorem periodAlongOf_eq_periodAlongOf_I_sub (τ₀ τ₁ : ℍ) :
    ModularCurve.periodAlongOf Γ τ₀ τ₁ =
      ModularCurve.periodAlongOf Γ I τ₁ - ModularCurve.periodAlongOf Γ I τ₀ := by
  refine LinearMap.ext fun f => ?_
  obtain ⟨F, hF⟩ := exists_primitive Γ f
  rw [LinearMap.sub_apply, periodAlongOf_eq_sub Γ f hF, periodAlongOf_eq_sub Γ f hF,
    periodAlongOf_eq_sub Γ f hF]
  ring

omit [Γ.FiniteIndex] in

theorem hasDerivAt_smul_ofComplex (γ : SL(2, ℤ)) (τ : ℍ) :
    HasDerivAt (fun z : ℂ => ((γ • ofComplex z : ℍ) : ℂ))
      (denom (Matrix.SpecialLinearGroup.mapGL ℝ γ) ↑τ ^ (-2 : ℤ)) ↑τ := by
  set G : GL (Fin 2) ℝ := Matrix.SpecialLinearGroup.mapGL ℝ γ with hG
  have hdet : (G : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply, hG, Matrix.SpecialLinearGroup.det_mapGL,
      Units.val_one]
  have hpos : (0:ℝ) < (G : Matrix (Fin 2) (Fin 2) ℝ).det := by rw [hdet]; norm_num
  have h1 := (UpperHalfPlane.hasStrictDerivAt_smul hpos τ).hasDerivAt
  have h2 : (fun z : ℂ => ((G • ofComplex z : ℍ) : ℂ))
      = fun z : ℂ => ((γ • ofComplex z : ℍ) : ℂ) := by
    funext z
    rw [MulAction.compHom_smul_def]
  rw [h2] at h1
  convert h1 using 1 <;> try rfl
  rw [hdet]
  push_cast
  rw [zpow_neg, one_div]
  norm_cast

omit [Γ.FiniteIndex] in

theorem hasDerivAt_comp_smul {G : ℍ → ℂ} {g : ℍ → ℂ}
    (hG : ∀ τ : ℍ, HasDerivAt (G ∘ ofComplex) (g τ) ↑τ) (γ : SL(2, ℤ)) (τ : ℍ) :
    HasDerivAt (fun z : ℂ => G (γ • ofComplex z)) ((g ∣[(2:ℤ)] γ) τ) ↑τ := by
  have hfun : (fun z : ℂ => G (γ • ofComplex z))
      = (G ∘ ofComplex) ∘ (fun z : ℂ => ((γ • ofComplex z : ℍ) : ℂ)) := by
    funext z
    simp only [Function.comp_apply, ofComplex_apply]
  have houter : HasDerivAt (G ∘ ofComplex) (g (γ • τ))
      ((fun z : ℂ => ((γ • ofComplex z : ℍ) : ℂ)) ↑τ) := by
    simpa only [ofComplex_apply] using hG (γ • τ)
  have hcomp := houter.comp (↑τ : ℂ) (hasDerivAt_smul_ofComplex γ τ)
  rw [← hfun] at hcomp
  convert hcomp using 1 <;> try rfl
  exact ModularForm.SL_slash_apply (g : ℍ → ℂ) γ τ

theorem periodAlongOf_I_slash (γ : SL(2, ℤ)) (f f' : CuspForm Γ 2)
    (h : (⇑f' : ℍ → ℂ) = (⇑f : ℍ → ℂ) ∣[(2:ℤ)] γ) (τ : ℍ) :
    ModularCurve.periodAlongOf Γ I τ f' = ModularCurve.periodAlongOf Γ (γ • I) (γ • τ) f := by
  obtain ⟨F, hF⟩ := exists_primitive Γ f
  have hG : ∀ σ : ℍ, HasDerivAt ((fun w : ℍ => F (γ • w)) ∘ ofComplex) (f' σ) ↑σ := by
    intro σ
    have := hasDerivAt_comp_smul (G := F) (g := (⇑f : ℍ → ℂ)) hF γ σ
    rw [← h] at this
    exact this
  rw [periodAlongOf_eq_sub Γ f' hG I τ, periodAlongOf_eq_sub Γ f hF (γ • I) (γ • τ)]

theorem periodAlongOf_I_smul_sub (γ : SL(2, ℤ)) (f f' : CuspForm Γ 2)
    (h : (⇑f' : ℍ → ℂ) = (⇑f : ℍ → ℂ) ∣[(2:ℤ)] γ) (τ : ℍ) :
    ModularCurve.periodAlongOf Γ I (γ • τ) f - ModularCurve.periodAlongOf Γ I τ f' =
      ModularCurve.periodAlongOf Γ I (γ • I) f := by
  rw [periodAlongOf_I_slash Γ γ f f' h τ, periodAlongOf_eq_periodAlongOf_I_sub Γ (γ • I) (γ • τ),
    LinearMap.sub_apply]
  ring

end FTC

section AJ

variable (Γ : Subgroup SL(2, ℤ))

def aj : (ℍ →₀ ℤ) →+ Module.Dual ℂ (CuspForm Γ 2) :=
  Finsupp.liftAddHom fun τ => zmultiplesHom _ (ModularCurve.periodAlongOf Γ I τ)

theorem aj_apply (c : ℍ →₀ ℤ) :
    aj Γ c = c.sum fun τ n => n • ModularCurve.periodAlongOf Γ I τ := by
  simp only [aj, Finsupp.liftAddHom_apply]
  rfl

@[scoped simp]
theorem aj_single (τ : ℍ) (n : ℤ) : aj Γ (Finsupp.single τ n) = n • ModularCurve.periodAlongOf Γ I τ := by
  simp [aj_apply]

theorem aj_mapDomain (g : ℍ → ℍ) (c : ℍ →₀ ℤ) :
    aj Γ (Finsupp.mapDomain g c) = c.sum fun τ n => n • ModularCurve.periodAlongOf Γ I (g τ) := by
  classical
  induction c using Finsupp.induction with
  | zero => simp
  | single_add a b f _ _ ih =>
    rw [Finsupp.mapDomain_add, map_add, Finsupp.mapDomain_single, aj_single, ih,
      Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by simp [add_smul]),
      Finsupp.sum_single_index (by simp)]

theorem sum_mapDomain (g : ℍ → ℍ) (c : ℍ →₀ ℤ) :
    ((Finsupp.mapDomain g c).sum fun _ n => n) = c.sum fun _ n => n :=
  Finsupp.sum_mapDomain_index (fun _ => rfl) (fun _ _ _ => rfl)

variable [Γ.FiniteIndex]

theorem aj_mapDomain_smul_apply (γ : SL(2, ℤ)) (f f' : CuspForm Γ 2)
    (h : (⇑f' : ℍ → ℂ) = (⇑f : ℍ → ℂ) ∣[(2:ℤ)] γ) (c : ℍ →₀ ℤ) (hc : (c.sum fun _ n => n) = 0) :
    aj Γ (Finsupp.mapDomain (fun τ => γ • τ) c) f = aj Γ c f' := by
  classical
  have key : ∀ τ : ℍ, ModularCurve.periodAlongOf Γ I (γ • τ) f =
      ModularCurve.periodAlongOf Γ I τ f' + ModularCurve.periodAlongOf Γ I (γ • I) f := by
    intro τ
    have := periodAlongOf_I_smul_sub Γ γ f f' h τ
    rw [sub_eq_iff_eq_add] at this
    rw [this, add_comm]
  rw [aj_mapDomain, aj_apply]
  simp only [Finsupp.sum, LinearMap.sum_apply, LinearMap.smul_apply]
  rw [Finset.sum_congr rfl (fun x _ => by rw [key x, smul_add]), Finset.sum_add_distrib,
    ← Finset.sum_smul]
  have hc' : (∑ x ∈ c.support, c x) = 0 := hc
  rw [hc', zero_smul, add_zero]

end AJ

section DVR

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem mem_of_ord_nonneg (v : Place K F) {f : F} (hf : f ≠ 0) (h : 0 ≤ v.ord f) :
    f ∈ v.toValuationSubring := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  rw [hu, show v.ord f = (((v.ord f).toNat : ℕ) : ℤ) from (Int.toNat_of_nonneg h).symm,
    zpow_natCast]
  exact mul_mem (u : v.toValuationSubring).2 (pow_mem (π : v.toValuationSubring).2 _)

end DVR

section Curve

variable (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)

local notation "𝔽" => (laurentBaseChange ℂ (xHFunctionField M H))
local notation "Γ" => (CohCarrier.GammaH M H)

scoped instance instIsCurveOver : IsCurveOver ℂ (laurentBaseChange ℂ (xHFunctionField M H)) := by
  have h : ∃ x : 𝔽, Transcendental ℂ x ∧
      FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set 𝔽)) 𝔽 :=
    ModularCurve.JOneES.exists_transcendental_finiteDimensional_laurentBaseChange ℂ
      (CohCarrier.GammaH M H) (translation_mem_GammaH M H)
  obtain ⟨x, hx, hfd⟩ := h
  haveI := hfd
  exact AlgebraicCurve.isCurveOver_of_isAlgClosed_of_transcendental x hx

variable {M H}

theorem deg_eq_one (v : Place ℂ 𝔽) : v.deg = 1 :=
  IsCurveOver.deg_eq_one_of_isAlgClosed v

variable (M H) in

def jH : laurentBaseChange ℂ (xHFunctionField M H) :=
  ⟨ModularCurve.coeffEmb ℂ (ModularCurve.jqModC ℚ),
    ModularCurve.coeffEmb_mem_laurentBaseChange ℂ
      (ModularCurve.intFormRatiosC_subset ℚ (CohCarrier.GammaH M H)
        (ModularCurve.jqModC_mem_intFormRatiosC ℚ (CohCarrier.GammaH M H)))⟩

theorem coe_jH : ((jH M H : 𝔽) : LaurentSeries ℂ) = ModularCurve.jqModC ℂ := by
  show ModularCurve.coeffEmb ℂ (ModularCurve.jqModC ℚ) = _
  exact ModularCurve.map_jqModC (algebraMap ℚ ℂ)

theorem exists_pt_eq (D : ModularCurve.ComplexPlaceDictionaryOf Γ (xHFunctionField M H))
    (P : Place ℂ 𝔽) (hP : jH M H ∈ P.toValuationSubring) : ∃ τ : ℍ, D.pt τ = P :=
  ModularCurve.ComplexPlaceDictionaryOf.exists_pt_eq_of_mem (CohCarrier.GammaH M H)
    (translation_mem_GammaH M H) (xHFunctionField M H) rfl D P (jH M H) coe_jH hP

theorem exists_div (x : 𝔽) (hx : x ≠ 0) :
    ∃ Dx : Divisor ℂ 𝔽, (∀ v, Dx v = v.ord x) ∧ Divisor.degree Dx = 0 :=
  HasPrincipalDivisors.exists_divisor x hx

theorem exists_finset_cusps :
    ∃ S : Finset (Place ℂ 𝔽), ∀ v : Place ℂ 𝔽, jH M H ∉ v.toValuationSubring → v ∈ S := by
  by_cases hj : jH M H = 0
  · exact ⟨∅, fun v hv => (hv (by rw [hj]; exact zero_mem _)).elim⟩
  obtain ⟨Dj, hDj, -⟩ := exists_div (jH M H) hj
  refine ⟨Dj.support, fun v hv => ?_⟩
  by_contra hvS
  have h0 : Dj v = 0 := Finsupp.notMem_support_iff.mp hvS
  exact hv (mem_of_ord_nonneg v hj (by rw [← hDj v, h0]))

theorem exists_decomp (D : ModularCurve.ComplexPlaceDictionaryOf Γ (xHFunctionField M H))
    (E : Divisor ℂ 𝔽) :
    ∃ (x : 𝔽) (c : ℍ →₀ ℤ), x ≠ 0 ∧ ∀ v, E v = v.ord x + Finsupp.mapDomain D.pt c v := by
  classical
  obtain ⟨S, hS⟩ := exists_finset_cusps (M := M) (H := H)

  obtain ⟨x, hx0, hx⟩ := AlgebraicCurve.Place.exists_forall_ord_eq S (fun v => E v)
  obtain ⟨Dx, hDx, -⟩ := exists_div x hx0
  set E' : Divisor ℂ 𝔽 := E - Dx with hE'
  have hE'cusp : ∀ v, jH M H ∉ v.toValuationSubring → E' v = 0 := by
    intro v hv
    simp only [hE', Finsupp.coe_sub, Pi.sub_apply, hDx v, hx v (hS v hv), sub_self]

  let lift : Place ℂ 𝔽 → ℍ := fun v =>
    if h : jH M H ∈ v.toValuationSubring then (exists_pt_eq D v h).choose else I
  have hlift : ∀ v ∈ E'.support, D.pt (lift v) = v := by
    intro v hv
    have hj : jH M H ∈ v.toValuationSubring := by
      by_contra h
      exact (Finsupp.mem_support_iff.mp hv) (hE'cusp v h)
    simp only [lift, dif_pos hj]
    exact (exists_pt_eq D v hj).choose_spec
  refine ⟨x, Finsupp.mapDomain lift E', hx0, fun v => ?_⟩
  have hcomp : Finsupp.mapDomain D.pt (Finsupp.mapDomain lift E') = E' := by
    rw [← Finsupp.mapDomain_comp]
    rw [Finsupp.mapDomain_congr (g := id) (fun v hv => by simp [Function.comp, hlift v hv]),
      Finsupp.mapDomain_id]
  rw [hcomp, hE']
  simp [hDx v]

theorem degree_mapDomain_pt (D : ModularCurve.ComplexPlaceDictionaryOf Γ (xHFunctionField M H))
    (c : ℍ →₀ ℤ) :
    Divisor.degree (Finsupp.mapDomain D.pt c) = c.sum fun _ n => n := by
  classical
  induction c using Finsupp.induction with
  | zero => simp
  | single_add a b f _ _ ih =>
    rw [Finsupp.mapDomain_add, map_add, Finsupp.mapDomain_single, ih,
      Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), Finsupp.sum_single_index rfl,
      Divisor.degree_single, deg_eq_one]
    simp

end Curve

section AJClass

variable {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ}
variable (D : ModularCurve.ComplexPlaceDictionaryOf (CohCarrier.GammaH M H) (xHFunctionField M H))

local notation "𝔽" => (laurentBaseChange ℂ (xHFunctionField M H))
local notation "Γ" => (CohCarrier.GammaH M H)
local notation "Λ" => ModularCurve.periodLatticeOf (CohCarrier.GammaH M H)

theorem aj_mem_of_forall_eq_ord {c : ℍ →₀ ℤ} {x : 𝔽} (hx : x ≠ 0)
    (h : ∀ v, Finsupp.mapDomain D.pt c v = v.ord x) : aj Γ c ∈ Λ := by
  rw [aj_apply]
  exact ModularCurve.ComplexPlaceDictionaryOf.abelJacobi_mem_periodLatticeOf_gammaH_of_isPrincipal
    M H D c ⟨x, hx, h⟩

theorem mk_aj_eq_of_rel {c₁ c₂ : ℍ →₀ ℤ} {x : 𝔽} (hx : x ≠ 0)
    (h : ∀ v, Finsupp.mapDomain D.pt c₁ v = Finsupp.mapDomain D.pt c₂ v + v.ord x) :
    (Submodule.Quotient.mk (aj Γ c₁) : _ ⧸ Λ) = Submodule.Quotient.mk (aj Γ c₂) := by
  rw [Submodule.Quotient.eq, ← map_sub]
  refine aj_mem_of_forall_eq_ord D hx fun v => ?_
  rw [Finsupp.mapDomain_sub, Finsupp.coe_sub, Pi.sub_apply, h v]
  ring

def fn (E : Divisor ℂ 𝔽) : 𝔽 := (exists_decomp D E).choose

private def _root_.ModularCurve.AbelJacobiHGlue.lift (E : Divisor ℂ 𝔽) : ℍ →₀ ℤ := (exists_decomp D E).choose_spec.choose

p2m_export "ModularCurve.AbelJacobiHGlue" "lift"
theorem fn_ne_zero (E : Divisor ℂ 𝔽) : fn D E ≠ 0 :=
  (exists_decomp D E).choose_spec.choose_spec.1

theorem decomp_spec (E : Divisor ℂ 𝔽) (v : Place ℂ 𝔽) :
    E v = v.ord (fn D E) + Finsupp.mapDomain D.pt (lift D E) v :=
  (exists_decomp D E).choose_spec.choose_spec.2 v

def ajClassFun (E : Divisor ℂ 𝔽) : Module.Dual ℂ (CuspForm Γ 2) ⧸ Λ :=
  Submodule.Quotient.mk (aj Γ (lift D E))

theorem ajClassFun_eq {E : Divisor ℂ 𝔽} {x : 𝔽} {c : ℍ →₀ ℤ} (hx : x ≠ 0)
    (h : ∀ v, E v = v.ord x + Finsupp.mapDomain D.pt c v) :
    ajClassFun D E = Submodule.Quotient.mk (aj Γ c) := by
  refine mk_aj_eq_of_rel D (x := x * (fn D E)⁻¹) (mul_ne_zero hx (inv_ne_zero (fn_ne_zero D E)))
    fun v => ?_
  have h1 := decomp_spec D E v
  have h2 := h v
  rw [v.ord_mul hx (inv_ne_zero (fn_ne_zero D E)), v.ord_inv]
  linarith

theorem ajClassFun_add (E₁ E₂ : Divisor ℂ 𝔽) :
    ajClassFun D (E₁ + E₂) = ajClassFun D E₁ + ajClassFun D E₂ := by
  have h : ∀ v, (E₁ + E₂) v = v.ord (fn D E₁ * fn D E₂) +
      Finsupp.mapDomain D.pt (lift D E₁ + lift D E₂) v := by
    intro v
    rw [Finsupp.coe_add, Pi.add_apply, decomp_spec D E₁ v, decomp_spec D E₂ v,
      v.ord_mul (fn_ne_zero D E₁) (fn_ne_zero D E₂), Finsupp.mapDomain_add,
      Finsupp.coe_add, Pi.add_apply]
    ring
  rw [ajClassFun_eq D (mul_ne_zero (fn_ne_zero D E₁) (fn_ne_zero D E₂)) h, map_add,
    Submodule.Quotient.mk_add]
  rfl

def ajClass : Divisor ℂ 𝔽 →+ Module.Dual ℂ (CuspForm Γ 2) ⧸ Λ :=
  AddMonoidHom.mk' (ajClassFun D) (ajClassFun_add D)

theorem ajClass_apply (E : Divisor ℂ 𝔽) : ajClass D E = ajClassFun D E := rfl

theorem ajClass_mapDomain (c : ℍ →₀ ℤ) :
    ajClass D (Finsupp.mapDomain D.pt c) = Submodule.Quotient.mk (aj Γ c) :=
  ajClassFun_eq D (x := 1) one_ne_zero fun v => by simp

theorem ajClass_eq_zero_of_mem_principal {E : Divisor ℂ 𝔽}
    (hE : E ∈ Divisor.principal (K := ℂ) (F := 𝔽)) : ajClass D E = 0 := by
  obtain ⟨x, hx, h⟩ := hE
  rw [ajClass_apply, ajClassFun_eq D (c := 0) hx fun v => by simp [h v], map_zero,
    Submodule.Quotient.mk_zero]

theorem degree_mapDomain_lift_eq_zero {E : Divisor ℂ 𝔽} (hE : Divisor.degree E = 0) :
    Divisor.degree (Finsupp.mapDomain D.pt (lift D E)) = 0 := by
  obtain ⟨Dx, hDx, hdeg⟩ := exists_div (fn D E) (fn_ne_zero D E)
  have : Finsupp.mapDomain D.pt (lift D E) = E - Dx := by
    ext v
    rw [Finsupp.coe_sub, Pi.sub_apply, decomp_spec D E v, hDx v]
    ring
  rw [this, map_sub, hE, hdeg, sub_zero]

theorem exists_eq_add_mapDomain_lift (E : Divisor.degZero (K := ℂ) (F := 𝔽)) :
    ∃ Dx : Divisor ℂ 𝔽, Dx ∈ Divisor.principal (K := ℂ) (F := 𝔽) ∧
      (E : Divisor ℂ 𝔽) = Dx + Finsupp.mapDomain D.pt (lift D E) ∧
      ((lift D (E : Divisor ℂ 𝔽)).sum fun _ n => n) = 0 := by
  obtain ⟨Dx, hDx, hdegx⟩ := exists_div (fn D E) (fn_ne_zero D E)
  refine ⟨Dx, ⟨fn D E, fn_ne_zero D E, hDx⟩, ?_, ?_⟩
  · ext v
    rw [Finsupp.coe_add, Pi.add_apply, decomp_spec D E v, hDx v]
  · rw [← degree_mapDomain_pt D]
    exact degree_mapDomain_lift_eq_zero D E.2

end AJClass

section Pic0

variable {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ}
variable (D : ModularCurve.ComplexPlaceDictionaryOf (CohCarrier.GammaH M H) (xHFunctionField M H))

local notation "𝔽" => (laurentBaseChange ℂ (xHFunctionField M H))
local notation "Γ" => (CohCarrier.GammaH M H)
local notation "Λ" => ModularCurve.periodLatticeOf (CohCarrier.GammaH M H)

def abelJacobi : Pic0 ℂ 𝔽 →+ Module.Dual ℂ (CuspForm Γ 2) ⧸ Λ :=
  QuotientAddGroup.lift _ ((ajClass D).comp (Divisor.degZero (K := ℂ) (F := 𝔽)).subtype)
    (by
      intro E hE
      rw [AddSubgroup.mem_addSubgroupOf] at hE
      exact ajClass_eq_zero_of_mem_principal D hE)

theorem abelJacobi_mk (E : Divisor.degZero (K := ℂ) (F := 𝔽)) :
    abelJacobi D (Pic0.mk E) = ajClass D (E : Divisor ℂ 𝔽) :=
  rfl

theorem abelJacobi_injective : Function.Injective (abelJacobi D) := by
  refine (injective_iff_map_eq_zero _).mpr fun z hz => ?_
  obtain ⟨E, rfl⟩ := Pic0.mk_surjective z
  rw [abelJacobi_mk, ajClass_apply, ajClassFun, Submodule.Quotient.mk_eq_zero, aj_apply] at hz
  have hdeg := degree_mapDomain_lift_eq_zero D (E := (E : Divisor ℂ 𝔽)) E.2
  obtain ⟨y, hy, hEy⟩ :=
    ModularCurve.ComplexPlaceDictionaryOf.isPrincipal_of_abelJacobi_mem_periodLatticeOf_gammaH
      M H D _ hdeg hz
  refine (QuotientAddGroup.eq_zero_iff _).mpr ?_
  rw [AddSubgroup.mem_addSubgroupOf]
  refine ⟨fn D E * y, mul_ne_zero (fn_ne_zero D E) hy, fun v => ?_⟩
  rw [v.ord_mul (fn_ne_zero D E) hy, ← hEy v]
  exact decomp_spec D E v

def twoPoint (τ₀ τ₁ : ℍ) : Divisor.degZero (K := ℂ) (F := 𝔽) :=
  ⟨Finsupp.mapDomain D.pt (Finsupp.single τ₁ 1 - Finsupp.single τ₀ 1), by
    rw [Divisor.mem_degZero, degree_mapDomain_pt, Finsupp.sum_sub_index (fun _ _ _ => rfl)]
    simp⟩

theorem abelJacobi_twoPoint (τ₀ τ₁ : ℍ) :
    abelJacobi D (Pic0.mk (twoPoint D τ₀ τ₁)) =
      Submodule.Quotient.mk (ModularCurve.periodAlongOf Γ τ₀ τ₁) := by
  rw [abelJacobi_mk, twoPoint, ajClass_mapDomain, map_sub, aj_single, aj_single, one_smul,
    one_smul, periodAlongOf_eq_periodAlongOf_I_sub Γ τ₀ τ₁]

theorem abelJacobi_surjective : Function.Surjective (abelJacobi D) := by
  intro y
  obtain ⟨φ, rfl⟩ := Submodule.Quotient.mk_surjective (ModularCurve.periodLatticeOf Γ) y
  have key : AddSubgroup.closure (Set.range fun p : ℍ × ℍ => ModularCurve.periodAlongOf Γ p.1 p.2) ≤
      (abelJacobi D).range.comap (ModularCurve.periodLatticeOf Γ).mkQ.toAddMonoidHom := by
    refine (AddSubgroup.closure_le _).mpr ?_
    rintro _ ⟨p, rfl⟩
    exact ⟨Pic0.mk (twoPoint D p.1 p.2), abelJacobi_twoPoint D p.1 p.2⟩
  have hφ : φ ∈ AddSubgroup.closure
      (Set.range fun p : ℍ × ℍ => ModularCurve.periodAlongOf Γ p.1 p.2) := by
    rw [ModularCurve.addSubgroupClosure_range_periodAlongOf_eq_top Γ]; trivial
  exact key hφ

theorem abelJacobi_heckePic0HBar {ℓ : ℕ} [NeZero ℓ]
    (hα : ModularCurve.HeckeAlphaHBarIntegral ℂ M H ℓ) (hβ : ModularCurve.HeckeBetaHBarIntegral ℂ M H ℓ)
    [HasPrincipalDivisors ℂ (laurentBaseChange ℂ (xHTopFunctionFieldC ℚ M H (M * ℓ)))]
    (hFI : FundamentalIdentityAlong ℂ (ModularCurve.heckeBetaHBar ℂ M H ℓ) hβ)
    (hfin : FiniteAlong ℂ (ModularCurve.heckeAlphaHBar ℂ M H ℓ))
    (hN : NormFormulaAlong ℂ (ModularCurve.heckeAlphaHBar ℂ M H ℓ) hfin)
    (Tdual : Module.Dual ℂ (CuspForm Γ 2) →ₗ[ℂ] Module.Dual ℂ (CuspForm Γ 2))
    (hst : ∀ v ∈ ModularCurve.periodLatticeOf Γ, Tdual v ∈ ModularCurve.periodLatticeOf Γ)
    (hcard : ∀ c : ℍ →₀ ℤ, Divisor.degree (Finsupp.mapDomain D.pt c) = 0 →
      ∃ c' : ℍ →₀ ℤ, Finsupp.mapDomain D.pt c' = ModularCurve.heckeDivHBar hα hβ (Finsupp.mapDomain D.pt c) ∧
        (c'.sum fun τ n => n • ModularCurve.periodAlongOf Γ I τ) -
            Tdual (c.sum fun τ n => n • ModularCurve.periodAlongOf Γ I τ) ∈
          ModularCurve.periodLatticeOf Γ)
    (z : Pic0 ℂ 𝔽) (φ : Module.Dual ℂ (CuspForm Γ 2))
    (hz : abelJacobi D z = Submodule.Quotient.mk φ) :
    abelJacobi D (ModularCurve.heckePic0HBar hα hβ hFI hfin hN z) =
      Submodule.Quotient.mk (Tdual φ) := by
  obtain ⟨E, rfl⟩ := Pic0.mk_surjective z
  rw [ModularCurve.heckePic0HBar, Pic0.correspondence_mk, abelJacobi_mk, Pic0.coe_degZeroCorrespondence]
  change ajClass D (ModularCurve.heckeDivHBar hα hβ (E : Divisor ℂ 𝔽)) = _
  rw [abelJacobi_mk] at hz

  obtain ⟨Dx, hprinx, hE, -⟩ := exists_eq_add_mapDomain_lift D E
  have hdeg := degree_mapDomain_lift_eq_zero D (E := (E : Divisor ℂ 𝔽)) E.2

  have hprin : ModularCurve.heckeDivHBar hα hβ Dx ∈ Divisor.principal (K := ℂ) (F := 𝔽) :=
    Divisor.correspondence_mem_principal _ _ hβ hα hfin hN hprinx
  obtain ⟨c', hc', hmem⟩ := hcard (lift D E) hdeg
  rw [hE, map_add, map_add, ajClass_eq_zero_of_mem_principal D hprin, zero_add, ← hc',
    ajClass_mapDomain]

  rw [ajClass_apply, ajClassFun, Submodule.Quotient.eq] at hz
  rw [Submodule.Quotient.eq]
  have h1 : aj Γ c' - Tdual (aj Γ (lift D E)) ∈ ModularCurve.periodLatticeOf Γ := by
    simpa only [aj_apply] using hmem
  have h2 := hst _ hz
  rw [map_sub] at h2
  have := add_mem h1 h2
  convert this using 1
  abel

end Pic0

section Transport

variable {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ}
variable (D : ModularCurve.ComplexPlaceDictionaryOf (CohCarrier.GammaH M H) (xHFunctionField M H))

local notation "𝔽" => (laurentBaseChange ℂ (xHFunctionField M H))
local notation "Γ" => (CohCarrier.GammaH M H)
local notation "Λ" => ModularCurve.periodLatticeOf (CohCarrier.GammaH M H)

theorem smul_mapDomain_pt (g : SemilinearAut ℂ 𝔽) (m : ℍ → ℍ)
    (hg : ∀ τ : ℍ, g • D.pt τ = D.pt (m τ)) (c : ℍ →₀ ℤ) :
    g • Finsupp.mapDomain D.pt c = Finsupp.mapDomain D.pt (Finsupp.mapDomain m c) := by
  rw [SemilinearAut.divisor_smul_def, ← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
  congr 1
  funext τ
  simp only [Function.comp_apply, hg]

theorem abelJacobi_smul_eq (g : SemilinearAut ℂ 𝔽) (m : ℍ → ℍ)
    (hg : ∀ τ : ℍ, g • D.pt τ = D.pt (m τ)) (E : Divisor.degZero (K := ℂ) (F := 𝔽)) :
    abelJacobi D (g • Pic0.mk E) =
      Submodule.Quotient.mk (aj Γ (Finsupp.mapDomain m (lift D (E : Divisor ℂ 𝔽)))) := by
  rw [SemilinearAut.pic0_smul_mk, abelJacobi_mk, SemilinearAut.coe_degZeroSMulHom]
  obtain ⟨Dx, hprinx, hE, -⟩ := exists_eq_add_mapDomain_lift D E
  have h1 : g • (E : Divisor ℂ 𝔽) =
      g • Dx + Finsupp.mapDomain D.pt (Finsupp.mapDomain m (lift D (E : Divisor ℂ 𝔽))) := by
    conv_lhs => rw [hE]
    rw [smul_add, smul_mapDomain_pt D g m hg]
  rw [h1, map_add, ajClass_eq_zero_of_mem_principal D (SemilinearAut.smul_mem_principal g hprinx),
    zero_add, ajClass_mapDomain]

end Transport

section DiamondConj

variable {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ}
variable (D : ModularCurve.ComplexPlaceDictionaryOf (CohCarrier.GammaH M H) (xHFunctionField M H))

local notation "𝔽" => (laurentBaseChange ℂ (xHFunctionField M H))
local notation "Γ" => (CohCarrier.GammaH M H)
local notation "Λ" => ModularCurve.periodLatticeOf (CohCarrier.GammaH M H)

def gammaUL (M : ℕ) [NeZero M] (d : (ZMod M)ˣ) : CongruenceSubgroup.Gamma0 M :=
  CuspForm.gammaLift M d⁻¹

theorem gammaUL_apply_00 (d : (ZMod M)ˣ) :
    ((((gammaUL M d : CongruenceSubgroup.Gamma0 M) : SL(2, ℤ)) 0 0 : ℤ) : ZMod M) = (d : ZMod M) := by
  have h1 : CohCarrier.gamma0Units M (gammaUL M d) = d⁻¹ := CuspForm.gamma0Units_gammaLift d⁻¹
  have h2 : ((CohCarrier.gamma0Units M (gammaUL M d))⁻¹ : (ZMod M)ˣ) = d := by rw [h1, inv_inv]
  have h3 := congrArg (fun u : (ZMod M)ˣ => (u : ZMod M)) h2
  simpa [CohCarrier.gamma0Units] using h3

def gammaULInv (M : ℕ) [NeZero M] (d : (ZMod M)ˣ) : CongruenceSubgroup.Gamma0 M :=
  (gammaUL M d)⁻¹

theorem coe_gammaULInv (d : (ZMod M)ˣ) :
    ((gammaULInv M d : CongruenceSubgroup.Gamma0 M) : SL(2, ℤ)) =
      ((gammaUL M d : CongruenceSubgroup.Gamma0 M) : SL(2, ℤ))⁻¹ := rfl

theorem gamma0Units_gammaULInv (d : (ZMod M)ˣ) : CohCarrier.gamma0Units M (gammaULInv M d) = d := by
  rw [gammaULInv, map_inv, show CohCarrier.gamma0Units M (gammaUL M d) = d⁻¹ from
    CuspForm.gamma0Units_gammaLift d⁻¹, inv_inv]

theorem coe_diamondLinH_eq (d : (ZMod M)ˣ) (f : CuspForm Γ 2) :
    (⇑(CuspForm.diamondLinH 2 d f) : ℍ → ℂ) =
      (⇑f : ℍ → ℂ) ∣[(2 : ℤ)] (((gammaUL M d : CongruenceSubgroup.Gamma0 M) : SL(2, ℤ))⁻¹) := by
  rw [CuspForm.coe_diamondLinH_eq_slash 2 (CuspForm.stableD M H 2) d (gammaULInv M d)
    (gamma0Units_gammaULInv d) f]
  rfl

theorem abelJacobi_diamond
    (hstD : ∀ (d : (ZMod M)ˣ), ∀ v ∈ ModularCurve.periodLatticeOf Γ,
      (CuspForm.diamondLinH 2 d).dualMap v ∈ ModularCurve.periodLatticeOf Γ)
    (d : (ZMod M)ˣ) (σ : 𝔽 ≃ₐ[ℂ] 𝔽)
    (hσ : ∀ (k : ℤ) (f g : ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k)
        (pf pg : PowerSeries ℤ) (hf : ModularCurve.IsIntegralQExp f pf) (hg : ModularCurve.IsIntegralQExp g pg)
        (hg0 : ModularCurve.intSeriesC ℚ pg ≠ 0) (γ : SL(2, ℤ)),
        γ ∈ CongruenceSubgroup.Gamma0 M → ((γ 0 0 : ℤ) : ZMod M) = (d : ZMod M) →
        ((σ ⟨ModularCurve.coeffEmb ℂ (ModularCurve.intSeriesC ℚ pf / ModularCurve.intSeriesC ℚ pg),
              ModularCurve.coeffEmb_mem_laurentBaseChange ℂ
                (ModularCurve.div_mem_qExpFunctionFieldC f g hf hg hg0)⟩ : 𝔽) : LaurentSeries ℂ) *
            HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑g ∣[k] (γ : GL (Fin 2) ℝ))) =
          HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑f ∣[k] (γ : GL (Fin 2) ℝ))))
    (z : Pic0 ℂ 𝔽) (φ : Module.Dual ℂ (CuspForm Γ 2))
    (hz : abelJacobi D z = Submodule.Quotient.mk φ) :
    abelJacobi D (SemilinearAut.ofAlgAut σ • z) =
      Submodule.Quotient.mk ((CuspForm.diamondLinH 2 d).dualMap φ) := by
  set γ : SL(2, ℤ) := ((gammaUL M d : CongruenceSubgroup.Gamma0 M) : SL(2, ℤ)) with hγdef
  have hγ : γ ∈ CongruenceSubgroup.Gamma0 M := (gammaUL M d).2

  have htr : ∀ τ : ℍ, SemilinearAut.ofAlgAut σ • D.pt τ = D.pt (γ⁻¹ • τ) := fun τ =>
    ModularCurve.ComplexPlaceDictionaryOf.ofAlgAut_smul_pt_eq_pt_inv_smul M H D σ γ hγ
      (fun k f g pf pg hf hg hg0 => hσ k f g pf pg hf hg hg0 γ hγ (gammaUL_apply_00 d)) τ
  obtain ⟨E, rfl⟩ := Pic0.mk_surjective z
  rw [abelJacobi_smul_eq D (SemilinearAut.ofAlgAut σ) (fun τ => γ⁻¹ • τ) htr E]
  rw [abelJacobi_mk, ajClass_apply, ajClassFun, Submodule.Quotient.eq] at hz
  rw [Submodule.Quotient.eq]

  obtain ⟨-, -, -, hsum⟩ := exists_eq_add_mapDomain_lift D E
  have key : aj Γ (Finsupp.mapDomain (fun τ => γ⁻¹ • τ) (lift D (E : Divisor ℂ 𝔽))) =
      (CuspForm.diamondLinH 2 d).dualMap (aj Γ (lift D (E : Divisor ℂ 𝔽))) := by
    refine LinearMap.ext fun f => ?_
    rw [LinearMap.dualMap_apply]
    exact aj_mapDomain_smul_apply Γ γ⁻¹ f (CuspForm.diamondLinH 2 d f) (coe_diamondLinH_eq d f)
      _ hsum
  rw [key, ← map_sub]
  exact hstD d _ hz

theorem J_smul_I : UpperHalfPlane.J • UpperHalfPlane.I = UpperHalfPlane.I := by
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.coe_J_smul, UpperHalfPlane.coe_I, Complex.conj_I, neg_neg]

theorem J_smul_J_smul (τ : ℍ) : UpperHalfPlane.J • UpperHalfPlane.J • τ = τ := by
  rw [← mul_smul, ← sq, UpperHalfPlane.J_sq, one_smul]

theorem jStable : ∀ γ ∈ CohCarrier.GammaH M H, ModularCurve.Period.jConjSL γ ∈ CohCarrier.GammaH M H :=
  fun _ hγ => CohCarrier.jConjSL_mem_GammaH M H hγ

def IsPartner (φ φ' : Module.Dual ℂ (CuspForm Γ 2)) : Prop :=
  ∀ f g : CuspForm Γ 2,
    (∀ τ : UpperHalfPlane, g τ = (starRingEnd ℂ) (f (UpperHalfPlane.J • τ))) →
      φ' g = -(starRingEnd ℂ) (φ f)

omit [NeZero M] in
theorem IsPartner.sub {φ φ' ψ ψ' : Module.Dual ℂ (CuspForm Γ 2)} (h₁ : IsPartner φ φ')
    (h₂ : IsPartner ψ ψ') : IsPartner (φ - ψ) (φ' - ψ') := by
  intro f g hfg
  rw [LinearMap.sub_apply, LinearMap.sub_apply, h₁ f g hfg, h₂ f g hfg, map_sub]
  ring

omit [NeZero M] in

theorem isPartner_aj_mapDomain_J (c : ℍ →₀ ℤ) :
    IsPartner (aj Γ c) (aj Γ (Finsupp.mapDomain (fun τ => UpperHalfPlane.J • τ) c)) := by
  classical
  intro f g hfg
  have key : ∀ τ : ℍ, ModularCurve.periodAlongOf Γ I (UpperHalfPlane.J • τ) g =
      -(starRingEnd ℂ) (ModularCurve.periodAlongOf Γ I τ f) := by
    intro τ
    rw [ModularCurve.periodAlongOf_eq_neg_conj_periodAlongOf_J_smul Γ f g hfg I (UpperHalfPlane.J • τ),
      J_smul_I, J_smul_J_smul]
  rw [aj_mapDomain, aj_apply]
  simp only [Finsupp.sum, LinearMap.sum_apply, LinearMap.smul_apply]
  rw [Finset.sum_congr rfl (fun x _ => by rw [key x]), map_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [zsmul_eq_mul, zsmul_eq_mul, map_mul, map_intCast, mul_neg]

theorem abelJacobi_conj
    (hstC : ∀ (φ φ' : Module.Dual ℂ (CuspForm Γ 2)), IsPartner φ φ' →
      φ ∈ ModularCurve.periodLatticeOf Γ → φ' ∈ ModularCurve.periodLatticeOf Γ)
    (z : Pic0 ℂ 𝔽) (φ φ' : Module.Dual ℂ (CuspForm Γ 2)) (hφ : IsPartner φ φ')
    (hz : abelJacobi D z = Submodule.Quotient.mk φ) :
    abelJacobi D (complexConjAlgEquiv • z) = Submodule.Quotient.mk φ' := by

  have htr : ∀ τ : ℍ, ModularCurve.arithmeticGalois (xHFunctionField M H) complexConjAlgEquiv • D.pt τ =
      D.pt (UpperHalfPlane.J • τ) := fun τ =>
    ModularCurve.ComplexPlaceDictionaryOf.arithmeticGalois_complexConjAlgEquiv_smul_pt
      (CohCarrier.GammaH M H) (translation_mem_GammaH M H) (xHFunctionField M H) rfl D τ
  obtain ⟨E, rfl⟩ := Pic0.mk_surjective z
  rw [ModularCurve.galois_smul_pic0_def,
    abelJacobi_smul_eq D (ModularCurve.arithmeticGalois (xHFunctionField M H) complexConjAlgEquiv)
      (fun τ => UpperHalfPlane.J • τ) htr E]
  rw [abelJacobi_mk, ajClass_apply, ajClassFun, Submodule.Quotient.eq] at hz
  rw [Submodule.Quotient.eq]
  exact hstC _ _ ((isPartner_aj_mapDomain_J (lift D (E : Divisor ℂ 𝔽))).sub hφ) hz

end DiamondConj

end ModularCurve.AbelJacobiHGlue
p2m_reactivate "P2MW.S_ModularCurve_exists_bijective_heckeEquivariant_addMonoidHom_pic0_complex_xH_quotient_periodLatticeOf.ModularCurve P2MW.S_ModularCurve_exists_bijective_heckeEquivariant_addMonoidHom_pic0_complex_xH_quotient_periodLatticeOf.ModularCurve.AbelJacobiHGlue"
p2m_reactivate "P2MW.S_ModularCurve_exists_bijective_heckeEquivariant_addMonoidHom_pic0_complex_xH_quotient_periodLatticeOf.ModularCurve"

end
p2m_reactivate "P2MW.S_ModularCurve_exists_bijective_heckeEquivariant_addMonoidHom_pic0_complex_xH_quotient_periodLatticeOf.ModularCurve P2MW.S_ModularCurve_exists_bijective_heckeEquivariant_addMonoidHom_pic0_complex_xH_quotient_periodLatticeOf.ModularCurve.AbelJacobiHGlue"

open scoped MatrixGroups ModularForm in
open ModularCurve.AbelJacobiHGlue in
theorem solution
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (hinC : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩;
      ModularCurve.HeckeInputsHAlong ℂ M H ℓ)
    (hstT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M), ∀ v ∈ ModularCurve.periodLatticeOf (CohCarrier.GammaH M H),
      (CuspForm.heckeTLinH 2 hℓ hℓM).dualMap v ∈ ModularCurve.periodLatticeOf (CohCarrier.GammaH M H))
    (hstU : ∀ (q : ℕ), q.Prime → q ∣ M → ∀ v ∈ ModularCurve.periodLatticeOf (CohCarrier.GammaH M H),
      (CuspForm.heckeULinH 2 q).dualMap v ∈ ModularCurve.periodLatticeOf (CohCarrier.GammaH M H))
    (hstD : ∀ (d : (ZMod M)ˣ), ∀ v ∈ ModularCurve.periodLatticeOf (CohCarrier.GammaH M H),
      (CuspForm.diamondLinH 2 d).dualMap v ∈ ModularCurve.periodLatticeOf (CohCarrier.GammaH M H))
    (hstC : ∀ (φ φ' : Module.Dual ℂ (CuspForm (CohCarrier.GammaH M H) 2)),
      (∀ f g : CuspForm (CohCarrier.GammaH M H) 2,
        (∀ τ : UpperHalfPlane, g τ = (starRingEnd ℂ) (f (UpperHalfPlane.J • τ))) →
          φ' g = -(starRingEnd ℂ) (φ f)) →
      φ ∈ ModularCurve.periodLatticeOf (CohCarrier.GammaH M H) →
        φ' ∈ ModularCurve.periodLatticeOf (CohCarrier.GammaH M H)) :
    ∃ v : AlgebraicCurve.Pic0 ℂ ↥(ModularCurve.laurentBaseChange ℂ (ModularCurve.xHFunctionField M H)) →+
        (Module.Dual ℂ (CuspForm (CohCarrier.GammaH M H) 2) ⧸ ModularCurve.periodLatticeOf (CohCarrier.GammaH M H)),
      Function.Bijective v ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M)
          (z : AlgebraicCurve.Pic0 ℂ ↥(ModularCurve.laurentBaseChange ℂ (ModularCurve.xHFunctionField M H)))
          (φ : Module.Dual ℂ (CuspForm (CohCarrier.GammaH M H) 2)),
        v z = Submodule.Quotient.mk φ →
        v ((haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩; ModularCurve.heckeOperatorHAlong ℂ M H ℓ) z) =
          Submodule.Quotient.mk ((CuspForm.heckeTLinH 2 hℓ hℓM).dualMap φ)) ∧
      (∀ (q : ℕ) (hq : q.Prime), q ∣ M →
          ∀ (z : AlgebraicCurve.Pic0 ℂ ↥(ModularCurve.laurentBaseChange ℂ (ModularCurve.xHFunctionField M H)))
          (φ : Module.Dual ℂ (CuspForm (CohCarrier.GammaH M H) 2)),
        v z = Submodule.Quotient.mk φ →
        v ((haveI : NeZero q := ⟨hq.ne_zero⟩; ModularCurve.heckeOperatorHAlong ℂ M H q) z) =
          Submodule.Quotient.mk ((CuspForm.heckeULinH 2 q).dualMap φ)) ∧
      (∀ (d : (ZMod M)ˣ)
          (σ : ↥(ModularCurve.laurentBaseChange ℂ (ModularCurve.xHFunctionField M H)) ≃ₐ[ℂ]
            ↥(ModularCurve.laurentBaseChange ℂ (ModularCurve.xHFunctionField M H))),
        (∀ (k : ℤ) (f g : ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k)
            (pf pg : PowerSeries ℤ) (hf : ModularCurve.IsIntegralQExp f pf) (hg : ModularCurve.IsIntegralQExp g pg)
            (hg0 : ModularCurve.intSeriesC ℚ pg ≠ 0) (γ : SL(2, ℤ)),
            γ ∈ CongruenceSubgroup.Gamma0 M → ((γ 0 0 : ℤ) : ZMod M) = (d : ZMod M) →
            ((σ ⟨ModularCurve.coeffEmb ℂ (ModularCurve.intSeriesC ℚ pf / ModularCurve.intSeriesC ℚ pg),
                  ModularCurve.coeffEmb_mem_laurentBaseChange ℂ
                    (ModularCurve.div_mem_qExpFunctionFieldC f g hf hg hg0)⟩ :
                ↥(ModularCurve.laurentBaseChange ℂ (ModularCurve.xHFunctionField M H))) : LaurentSeries ℂ) *
                HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑g ∣[k] (γ : GL (Fin 2) ℝ))) =
              HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑f ∣[k] (γ : GL (Fin 2) ℝ)))) →
        ∀ (z : AlgebraicCurve.Pic0 ℂ ↥(ModularCurve.laurentBaseChange ℂ (ModularCurve.xHFunctionField M H)))
          (φ : Module.Dual ℂ (CuspForm (CohCarrier.GammaH M H) 2)),
          v z = Submodule.Quotient.mk φ →
          v (AlgebraicCurve.SemilinearAut.ofAlgAut σ • z) =
            Submodule.Quotient.mk ((CuspForm.diamondLinH 2 d).dualMap φ)) ∧
      ∀ (z : AlgebraicCurve.Pic0 ℂ ↥(ModularCurve.laurentBaseChange ℂ (ModularCurve.xHFunctionField M H)))
        (φ φ' : Module.Dual ℂ (CuspForm (CohCarrier.GammaH M H) 2)),
        (∀ f g : CuspForm (CohCarrier.GammaH M H) 2,
          (∀ τ : UpperHalfPlane, g τ = (starRingEnd ℂ) (f (UpperHalfPlane.J • τ))) →
            φ' g = -(starRingEnd ℂ) (φ f)) →
        v z = Submodule.Quotient.mk φ →
        v (complexConjAlgEquiv • z) = Submodule.Quotient.mk φ' := by
  obtain ⟨D⟩ := ModularCurve.exists_complexPlaceDictionaryOf (CohCarrier.GammaH M H)
    (ModularCurve.translation_mem_GammaH M H) (ModularCurve.xHFunctionField M H) rfl
  refine ⟨abelJacobi D, ⟨abelJacobi_injective D, abelJacobi_surjective D⟩, ?_, ?_, ?_, ?_⟩
  ·
    intro ℓ hℓ hℓM z φ hz
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    obtain ⟨h0, hα, hβ, hP, hfin, hFI, hN⟩ := hinC ℓ hℓ
    show abelJacobi D (ModularCurve.heckeOperatorHAlong ℂ M H ℓ z) = _
    rw [ModularCurve.heckeOperatorHAlong_eq h0 hα hβ hFI hfin hN]
    refine abelJacobi_heckePic0HBar D hα hβ hFI hfin hN (CuspForm.heckeTLinH 2 hℓ hℓM).dualMap
      (hstT ℓ hℓ hℓM) (fun c hc => ?_) z φ hz
    obtain ⟨c', hc', hT, -⟩ :=
      ModularCurve.ComplexPlaceDictionaryOf.exists_mapDomain_eq_heckeDivHBar_abelJacobi_sub_mem_periodLatticeOf
        M H D ℓ hℓ h0 hα hβ c hc
    exact ⟨c', hc', hT hℓM⟩
  ·
    intro q hq hqM z φ hz
    haveI : NeZero q := ⟨hq.ne_zero⟩
    obtain ⟨h0, hα, hβ, hP, hfin, hFI, hN⟩ := hinC q hq
    show abelJacobi D (ModularCurve.heckeOperatorHAlong ℂ M H q z) = _
    rw [ModularCurve.heckeOperatorHAlong_eq h0 hα hβ hFI hfin hN]
    refine abelJacobi_heckePic0HBar D hα hβ hFI hfin hN (CuspForm.heckeULinH 2 q).dualMap
      (hstU q hq hqM) (fun c hc => ?_) z φ hz
    obtain ⟨c', hc', -, hU⟩ :=
      ModularCurve.ComplexPlaceDictionaryOf.exists_mapDomain_eq_heckeDivHBar_abelJacobi_sub_mem_periodLatticeOf
        M H D q hq h0 hα hβ c hc
    exact ⟨c', hc', hU hqM⟩
  ·
    intro d σ hσ z φ hz
    exact abelJacobi_diamond D hstD d σ hσ z φ hz
  ·
    intro z φ φ' hφ hz
    exact abelJacobi_conj D hstC z φ φ' hφ hz

end S_ModularCurve_exists_bijective_heckeEquivariant_addMonoidHom_pic0_complex_xH_quotient_periodLatticeOf
end P2MW
export P2MW.S_ModularCurve_exists_bijective_heckeEquivariant_addMonoidHom_pic0_complex_xH_quotient_periodLatticeOf (solution)
