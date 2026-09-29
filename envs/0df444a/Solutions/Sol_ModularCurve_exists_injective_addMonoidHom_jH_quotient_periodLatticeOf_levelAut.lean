-- Prove2me | solution 1 for ModularCurve.exists_injective_addMonoidHom_jH_quotient_periodLatticeOf_levelAut
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/9fca4bee-78b0-5647-964d-516628eb3480

import Mathlib
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_PeriodOf
import Definitions.Def_CuspForm_HeckeOperatorFormsGammaH
import Definitions.Def_GaloisRep_ComplexConjugation
import Theorems.Thm_ModularCurve_heckeInputsHAlong
import Theorems.Thm_ModularCurve_exists_injective_heckeEquivariant_addMonoidHom_jH_pic0_complex
import Theorems.Thm_ModularCurve_exists_bijective_heckeEquivariant_addMonoidHom_pic0_complex_xH_quotient_periodLatticeOf_slash
import Theorems.Thm_CuspForm_stableD
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_injective_addMonoidHom_jH_quotient_periodLatticeOf_levelAut
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z"
p2m_attr_erase "instance" "ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0 HeckeEis.instFiniteIndexHeckeUpper FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.ComplexPlaceDictionaryOf.pt_ofGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.injEq ModularCurve.ComplexPlaceDictionaryOf.pt_toGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.sizeOf_spec ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec CohCarrier.jConjGammaH_jConjGammaH CohCarrier.coe_jConjGammaH CohCarrier.charInvolution_apply ModularCurve.Period.jConjMat_apply_zero_one ModularCurve.Period.jConjSL_coe ModularCurve.Period.jConjMat_apply_one_zero ModularCurve.Period.jConjMat_apply_one_one ModularCurve.Period.jConjGamma0_coe ModularCurve.Period.charInvolution_apply ModularCurve.Period.jConjMat_apply_zero_zero ModularCurve.qExpandAlgHomC_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul"
p2m_attr_erase "simp" "ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂"
p2m_attr_erase "simp" "PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero ModularCurve.LevelN.coe_jGen FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero"
p2m_attr_erase "simp" "HeckeEis.coeffCoboundaryMap_apply"

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open scoped MatrixGroups ModularForm

namespace AJHLevelGlue

open CohCarrier ModularCurve ModularCurve.FullLevel UpperHalfPlane Matrix.SpecialLinearGroup AlgebraicCurve CongruenceSubgroup

section Generators

local notation "Qb" => AlgebraicClosure ℚ

theorem complexEmbedding_comp_algebraMap :
    (complexEmbedding : Qb →ₐ[ℚ] ℂ).toRingHom.comp (algebraMap ℚ Qb) = algebraMap ℚ ℂ :=
  complexEmbedding.comp_algebraMap

theorem coeffMap_complexEmbedding_coeffEmb (z : LaurentSeries ℚ) :
    coeffMap (complexEmbedding : Qb →ₐ[ℚ] ℂ).toRingHom (coeffEmb Qb z) = coeffEmb ℂ z := by
  rw [coeffEmb, coeffEmb, coeffMap_coeffMap]
  exact coeffMap_congr complexEmbedding_comp_algebraMap z

end Generators

section Root

variable (q : ℕ) [Fact q.Prime]

local notation "Qb" => AlgebraicClosure ℚ

theorem exists_idx_complexEmbedding_eq :
    ∃ ζ₀ : Idx q, (complexEmbedding : Qb →ₐ[ℚ] ℂ) ζ₀.val = Complex.exp (2 * Real.pi * Complex.I / q) := by
  have hq : q.Prime := Fact.out
  haveI : NeZero q := ⟨hq.ne_zero⟩

  obtain ⟨ζ₁, hζ₁⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Qb q

  have hinj : Function.Injective (complexEmbedding : Qb →ₐ[ℚ] ℂ) := (complexEmbedding : Qb →ₐ[ℚ] ℂ).injective
  have hζ₁' : IsPrimitiveRoot ((complexEmbedding : Qb →ₐ[ℚ] ℂ) ζ₁) q := hζ₁.map_of_injective hinj

  have hμ : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / q)) q := Complex.isPrimitiveRoot_exp q hq.ne_zero
  obtain ⟨a, -, ha⟩ := hζ₁'.eq_pow_of_pow_eq_one hμ.pow_eq_one
  have hprim : IsPrimitiveRoot (ζ₁ ^ a) q := by
    refine IsPrimitiveRoot.of_map_of_injective (f := (complexEmbedding : Qb →ₐ[ℚ] ℂ)) ?_ hinj
    rw [map_pow, ha]
    exact hμ
  exact ⟨Idx.mk (ζ₁ ^ a) hprim, by rw [Idx.val_mk, map_pow, ha]⟩

end Root

section Sharp

variable (q : ℕ) [Fact q.Prime]

theorem qne : (q : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
theorem qneZ : (q : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero

def Dr : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(q : ℝ), 0; 0, 1]
    (by rw [Matrix.det_fin_two_of]; simp [qne q])

@[scoped simp] theorem Dr_coe : ((Dr q : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![(q : ℝ), 0; 0, 1] := rfl

@[scoped simp] theorem conjElem_coe (γ : SL(2, ℤ)) : ((conjElem q γ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
    !![((γ 0 0 : ℤ) : ℝ), ((γ 0 1 : ℤ) : ℝ) / q; (q : ℝ) * ((γ 1 0 : ℤ) : ℝ), ((γ 1 1 : ℤ) : ℝ)] := rfl

theorem Dr_mul_conjElem (γ : SL(2, ℤ)) : Dr q * conjElem q γ = (γ : GL (Fin 2) ℝ) * Dr q := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  simp only [Matrix.GeneralLinearGroup.coe_mul, Dr_coe, conjElem_coe]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, mul_div_assoc', mul_div_cancel_left₀ _ (qne q), mul_comm]

theorem conjElem_eq (γ : SL(2, ℤ)) : conjElem q γ = (Dr q)⁻¹ * (γ : GL (Fin 2) ℝ) * Dr q := by
  rw [mul_assoc, ← Dr_mul_conjElem, inv_mul_cancel_left]

theorem det_coeSL (γ : SL(2, ℤ)) : ((γ : GL (Fin 2) ℝ)).det = 1 := by
  ext
  simp

theorem det_conjElem (γ : SL(2, ℤ)) : (conjElem q γ).det = 1 := by
  rw [conjElem_eq, map_mul, map_mul, map_inv, det_coeSL, mul_one, inv_mul_cancel]

theorem det_conjElem_pos (γ : SL(2, ℤ)) : 0 < ((conjElem q γ).det : ℝ) := by
  rw [det_conjElem]; exact one_pos

variable {q}

def downMat (ε : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ := !![ε 0 0, ε 0 1 / q; (q : ℤ) * ε 1 0, ε 1 1]

theorem det_downMat (ε : SL(2, ℤ)) (h : (q : ℤ) ∣ ε 0 1) : (downMat (q := q) ε).det = 1 := by
  obtain ⟨b, hb⟩ := h
  have hdet := Matrix.SpecialLinearGroup.det_coe ε
  rw [Matrix.det_fin_two] at hdet ⊢
  have h1 : (q : ℤ) * b / q = b := by rw [mul_comm]; exact Int.mul_ediv_cancel b (qneZ q)
  simp only [downMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, hb, h1] at hdet ⊢
  linear_combination hdet

def downSL (ε : SL(2, ℤ)) (h : (q : ℤ) ∣ ε 0 1) : SL(2, ℤ) := ⟨downMat (q := q) ε, det_downMat ε h⟩

theorem downSL_coe (ε : SL(2, ℤ)) (h : (q : ℤ) ∣ ε 0 1) :
    Dr q * ((downSL ε h : SL(2, ℤ)) : GL (Fin 2) ℝ) = (ε : GL (Fin 2) ℝ) * Dr q := by
  obtain ⟨b, hb⟩ := h
  have h1 : (q : ℤ) * b / q = b := by rw [mul_comm]; exact Int.mul_ediv_cancel b (qneZ q)
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  simp only [Matrix.GeneralLinearGroup.coe_mul, Dr_coe]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, downSL, downMat, hb, h1] <;> ring

def Tq (q : ℕ) : SL(2, ℤ) := ModularGroup.T ^ (q : ℤ)

theorem Tq_apply : (Tq q : Matrix (Fin 2) (Fin 2) ℤ) = !![1, (q : ℤ); 0, 1] := by
  rw [Tq]
  exact ModularGroup.coe_T_zpow (q : ℤ)

theorem coeGL_apply (γ : SL(2, ℤ)) (i j : Fin 2) :
    ((γ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i j = ((γ i j : ℤ) : ℝ) := by
  simp

theorem Tq_coe : Dr q * (ModularGroup.T : GL (Fin 2) ℝ) = ((Tq q : SL(2, ℤ)) : GL (Fin 2) ℝ) * Dr q := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Matrix.mul_apply]
  simp only [Fin.sum_univ_two, coeGL_apply, Dr_coe, Tq_apply, ModularGroup.coe_T]
  fin_cases i <;> fin_cases j <;> simp

def epsT (γ : SL(2, ℤ)) : SL(2, ℤ) := γ * Tq q * γ⁻¹

theorem epsT_apply (γ : SL(2, ℤ)) :
    (epsT (q := q) γ : Matrix (Fin 2) (Fin 2) ℤ) =
      !![1 - (q : ℤ) * (γ 0 0) * (γ 1 0), (q : ℤ) * (γ 0 0) * (γ 0 0);
        -((q : ℤ) * (γ 1 0) * (γ 1 0)), 1 + (q : ℤ) * (γ 0 0) * (γ 1 0)] := by
  have hdet := Matrix.SpecialLinearGroup.det_coe γ
  rw [Matrix.det_fin_two] at hdet
  rw [epsT, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, Tq_apply]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination hdet
  · ring
  · ring
  · linear_combination hdet

theorem epsT_apply_01 (γ : SL(2, ℤ)) : (epsT (q := q) γ) 0 1 = (q : ℤ) * (γ 0 0) * (γ 0 0) := by
  have := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℤ => A 0 1) (epsT_apply (q := q) γ)
  simpa using this

theorem epsT_apply_10 (γ : SL(2, ℤ)) : (epsT (q := q) γ) 1 0 = -((q : ℤ) * (γ 1 0) * (γ 1 0)) := by
  have := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℤ => A 1 0) (epsT_apply (q := q) γ)
  simpa using this

theorem epsT_apply_11 (γ : SL(2, ℤ)) : (epsT (q := q) γ) 1 1 = 1 + (q : ℤ) * (γ 0 0) * (γ 1 0) := by
  have := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℤ => A 1 1) (epsT_apply (q := q) γ)
  simpa using this

theorem q_dvd_epsT_01 (γ : SL(2, ℤ)) : (q : ℤ) ∣ (epsT (q := q) γ) 0 1 :=
  ⟨(γ 0 0) * (γ 0 0), by rw [epsT_apply_01]; ring⟩

theorem conjElem_T_conjElem_inv (γ : SL(2, ℤ)) :
    conjElem q γ * (ModularGroup.T : GL (Fin 2) ℝ) * (conjElem q γ)⁻¹ =
      ((downSL (epsT (q := q) γ) (q_dvd_epsT_01 γ) : SL(2, ℤ)) : GL (Fin 2) ℝ) := by
  have e1 : ((downSL (epsT (q := q) γ) (q_dvd_epsT_01 γ) : SL(2, ℤ)) : GL (Fin 2) ℝ) =
      (Dr q)⁻¹ * ((epsT (q := q) γ : SL(2, ℤ)) : GL (Fin 2) ℝ) * Dr q := by
    rw [mul_assoc, ← downSL_coe, inv_mul_cancel_left]
  have e2 : ((epsT (q := q) γ : SL(2, ℤ)) : GL (Fin 2) ℝ) =
      (γ : GL (Fin 2) ℝ) * ((Tq q : SL(2, ℤ)) : GL (Fin 2) ℝ) * ((γ : GL (Fin 2) ℝ))⁻¹ := by
    simp only [epsT, map_mul, map_inv]
  have e3 : ((Tq q : SL(2, ℤ)) : GL (Fin 2) ℝ) = Dr q * (ModularGroup.T : GL (Fin 2) ℝ) * (Dr q)⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq]
    exact (Tq_coe (q := q)).symm
  rw [e1, e2, e3, conjElem_eq]
  group

variable (M' : ℕ)

theorem mem_GH_iff (A : SL(2, ℤ)) :
    A ∈ CohCarrier.GammaH (q ^ 2 * M') (levelH q M') ↔
      ((A 1 0 : ℤ) : ZMod (q ^ 2 * M')) = 0 ∧ ((A 1 1 : ℤ) : ZMod q) = 1 := by
  rw [CohCarrier.mem_GammaH_iff]
  constructor
  · rintro ⟨hA, hH⟩
    refine ⟨Gamma0_mem.mp hA, ?_⟩
    rw [mem_levelH_iff] at hH
    have := congrArg (fun u : (ZMod q)ˣ => (u : ZMod q)) hH
    simpa [ZMod.unitsMap_def, CohCarrier.gamma0Units, Gamma0Map] using this
  · rintro ⟨h10, h11⟩
    refine ⟨Gamma0_mem.mpr h10, ?_⟩
    rw [mem_levelH_iff]
    ext
    simp [ZMod.unitsMap_def, CohCarrier.gamma0Units, Gamma0Map, h11]

theorem conjElem_T_conjElem_inv_mem (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M') :
    conjElem q γ * (ModularGroup.T : GL (Fin 2) ℝ) * (conjElem q γ)⁻¹ ∈
      (CohCarrier.GammaH (q ^ 2 * M') (levelH q M') : Subgroup (GL (Fin 2) ℝ)) := by
  rw [conjElem_T_conjElem_inv]
  refine Subgroup.mem_map_of_mem _ ?_
  rw [mem_GH_iff]
  constructor
  · show ((((q : ℤ) * (epsT (q := q) γ) 1 0 : ℤ)) : ZMod (q ^ 2 * M')) = 0
    rw [epsT_apply_10, ZMod.intCast_zmod_eq_zero_iff_dvd]
    have hc : (M' : ℤ) ∣ γ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp hγ)
    obtain ⟨c, hc⟩ := hc
    refine ⟨-(c * (γ 1 0)), ?_⟩
    rw [hc]; push_cast; ring
  · show (((epsT (q := q) γ) 1 1 : ℤ) : ZMod q) = 1
    rw [epsT_apply_11]
    push_cast
    rw [ZMod.natCast_self]
    ring

end Sharp

section Diamond

variable {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ}

def gammaUL (M : ℕ) [NeZero M] (d : (ZMod M)ˣ) : Gamma0 M :=
  CuspForm.gammaLift M d⁻¹

theorem gammaUL_apply_00 (d : (ZMod M)ˣ) :
    ((((gammaUL M d : Gamma0 M) : SL(2, ℤ)) 0 0 : ℤ) : ZMod M) = (d : ZMod M) := by
  have h1 : CohCarrier.gamma0Units M (gammaUL M d) = d⁻¹ := CuspForm.gamma0Units_gammaLift d⁻¹
  have h2 : ((CohCarrier.gamma0Units M (gammaUL M d))⁻¹ : (ZMod M)ˣ) = d := by rw [h1, inv_inv]
  have h3 := congrArg (fun u : (ZMod M)ˣ => (u : ZMod M)) h2
  simpa [CohCarrier.gamma0Units] using h3

def gammaULInv (M : ℕ) [NeZero M] (d : (ZMod M)ˣ) : Gamma0 M :=
  (gammaUL M d)⁻¹

theorem gamma0Units_gammaULInv (d : (ZMod M)ˣ) : CohCarrier.gamma0Units M (gammaULInv M d) = d := by
  rw [gammaULInv, map_inv, show CohCarrier.gamma0Units M (gammaUL M d) = d⁻¹ from
    CuspForm.gamma0Units_gammaLift d⁻¹, inv_inv]

theorem coe_diamondLinH_eq (d : (ZMod M)ˣ) (f : CuspForm (CohCarrier.GammaH M H) 2) :
    (⇑(CuspForm.diamondLinH 2 d f) : ℍ → ℂ) =
      (⇑f : ℍ → ℂ) ∣[(2 : ℤ)] (((gammaUL M d : Gamma0 M) : SL(2, ℤ)) : GL (Fin 2) ℝ)⁻¹ := by
  rw [CuspForm.coe_diamondLinH_eq_slash 2 (CuspForm.stableD M H 2) d (gammaULInv M d)
    (gamma0Units_gammaULInv d) f]
  rw [show ((gammaULInv M d : Gamma0 M) : SL(2, ℤ)) = ((gammaUL M d : Gamma0 M) : SL(2, ℤ))⁻¹ from rfl,
    map_inv]
  rfl

theorem conj_T_mem (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) :
    (γ : GL (Fin 2) ℝ) * (ModularGroup.T : GL (Fin 2) ℝ) * ((γ : GL (Fin 2) ℝ))⁻¹ ∈
      (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) := by
  have h : γ * ModularGroup.T * γ⁻¹ ∈ CohCarrier.GammaH M H :=
    CohCarrier.conj_mem_GammaH M H ⟨γ, hγ⟩ ⟨ModularGroup.T, translation_mem_GammaH M H⟩
  refine ⟨γ * ModularGroup.T * γ⁻¹, h, ?_⟩
  simp only [map_mul, map_inv]
  rfl

theorem det_coeSL_pos (γ : SL(2, ℤ)) : 0 < (((γ : GL (Fin 2) ℝ)).det : ℝ) := by
  have : ((γ : GL (Fin 2) ℝ)).det = 1 := by ext; simp
  rw [this]; exact one_pos

end Diamond

section General

local notation "Qb" => AlgebraicClosure ℚ

variable (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)

local notation "𝔽" => (laurentBaseChange ℂ (xHFunctionField M H))
local notation "Λ" => (ModularCurve.periodLatticeOf (CohCarrier.GammaH M H))

theorem hinC : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩; HeckeInputsHAlong ℂ M H ℓ :=
  fun ℓ hℓ => by
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    exact ModularCurve.heckeInputsHAlong ℂ M H ℓ

variable {M H}

theorem autClause_of
    (φb : ↥(xHFunctionFieldBar M H) →+* ↥𝔽) (ι : JH M H →+ Pic0 ℂ ↥𝔽)
    (hφb : ∀ y : ↥(xHFunctionFieldBar M H),
      ((φb y : ↥𝔽) : LaurentSeries ℂ) =
        coeffMap (complexEmbedding : Qb →ₐ[ℚ] ℂ).toRingHom (y : LaurentSeries Qb))
    (hιg : ∀ (g : SemilinearAut Qb ↥(xHFunctionFieldBar M H)) (g' : SemilinearAut ℂ ↥𝔽),
      (∀ y : ↥(xHFunctionFieldBar M H), g' • φb y = φb (g • y)) → ∀ x : JH M H, ι (g • x) = g' • ι x)
    (hιext : ∀ σ : ↥(xHFunctionFieldBar M H) ≃ₐ[Qb] ↥(xHFunctionFieldBar M H),
      ∃ σ' : ↥𝔽 ≃ₐ[ℂ] ↥𝔽, ∀ y : ↥(xHFunctionFieldBar M H), σ' (φb y) = φb (σ y))
    (v : Pic0 ℂ ↥𝔽 →+ (Module.Dual ℂ (CuspForm (CohCarrier.GammaH M H) 2) ⧸ Λ))
    (hvA : ∀ (α : GL (Fin 2) ℝ), 0 < (α.det : ℝ) →
        α * (ModularGroup.T : GL (Fin 2) ℝ) * α⁻¹ ∈ (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) →
      ∀ (σ : ↥𝔽 ≃ₐ[ℂ] ↥𝔽),
      (∀ (k : ℤ) (f g : ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k)
          (pf pg : PowerSeries ℤ) (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg)
          (hg0 : intSeriesC ℚ pg ≠ 0),
          ((σ ⟨coeffEmb ℂ (intSeriesC ℚ pf / intSeriesC ℚ pg),
                coeffEmb_mem_laurentBaseChange ℂ (div_mem_qExpFunctionFieldC f g hf hg hg0)⟩ : ↥𝔽) :
              LaurentSeries ℂ) *
              HahnSeries.ofPowerSeries ℤ ℂ (qExpansion 1 (⇑g ∣[k] α)) =
            HahnSeries.ofPowerSeries ℤ ℂ (qExpansion 1 (⇑f ∣[k] α))) →
      ∀ (P : CuspForm (CohCarrier.GammaH M H) 2 →ₗ[ℂ] CuspForm (CohCarrier.GammaH M H) 2),
        (∀ f : CuspForm (CohCarrier.GammaH M H) 2, ⇑(P f) = ⇑f ∣[(2 : ℤ)] α⁻¹) →
        (∀ w ∈ Λ, P.dualMap w ∈ Λ) →
      ∀ (z : Pic0 ℂ ↥𝔽) (φ : Module.Dual ℂ (CuspForm (CohCarrier.GammaH M H) 2)),
        v z = Submodule.Quotient.mk φ →
        v (SemilinearAut.ofAlgAut σ • z) = Submodule.Quotient.mk (P.dualMap φ))
    (α : GL (Fin 2) ℝ) (hα : 0 < (α.det : ℝ))
    (hTα : α * (ModularGroup.T : GL (Fin 2) ℝ) * α⁻¹ ∈ (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)))
    (P : CuspForm (CohCarrier.GammaH M H) 2 →ₗ[ℂ] CuspForm (CohCarrier.GammaH M H) 2)
    (hP : ∀ f : CuspForm (CohCarrier.GammaH M H) 2, ⇑(P f) = ⇑f ∣[(2 : ℤ)] α⁻¹)
    (hstP : ∀ w ∈ Λ, P.dualMap w ∈ Λ)
    (τ : ↥(xHFunctionFieldBar M H) ≃ₐ[Qb] ↥(xHFunctionFieldBar M H))
    (hτ : ∀ (k : ℤ) (f g : ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k)
        (pf pg : PowerSeries ℤ) (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg)
        (hg0 : intSeriesC ℚ pg ≠ 0),
        coeffMap (complexEmbedding : Qb →ₐ[ℚ] ℂ).toRingHom
            ((τ ⟨coeffEmb Qb (intSeriesC ℚ pf / intSeriesC ℚ pg),
                coeffEmb_mem_laurentBaseChange Qb (div_mem_qExpFunctionFieldC f g hf hg hg0)⟩ :
                ↥(xHFunctionFieldBar M H)) : LaurentSeries Qb) *
            HahnSeries.ofPowerSeries ℤ ℂ (qExpansion 1 (⇑g ∣[k] α)) =
          HahnSeries.ofPowerSeries ℤ ℂ (qExpansion 1 (⇑f ∣[k] α)))
    (x : JH M H) (φ : Module.Dual ℂ (CuspForm (CohCarrier.GammaH M H) 2))
    (hx : v (ι x) = Submodule.Quotient.mk φ) :
    v (ι (SemilinearAut.ofAlgAut τ • x)) = Submodule.Quotient.mk (P.dualMap φ) := by
  obtain ⟨τ', hτ'⟩ := hιext τ
  have hcompat : ∀ y : ↥(xHFunctionFieldBar M H),
      SemilinearAut.ofAlgAut τ' • φb y = φb (SemilinearAut.ofAlgAut τ • y) :=
    fun y => by rw [SemilinearAut.ofAlgAut_smul, SemilinearAut.ofAlgAut_smul, hτ']
  rw [hιg (SemilinearAut.ofAlgAut τ) (SemilinearAut.ofAlgAut τ') hcompat x]
  refine hvA α hα hTα τ' ?_ P hP hstP (ι x) φ hx

  intro k f g pf pg hf hg hg0
  have heC : (⟨coeffEmb ℂ (intSeriesC ℚ pf / intSeriesC ℚ pg),
        coeffEmb_mem_laurentBaseChange ℂ (div_mem_qExpFunctionFieldC f g hf hg hg0)⟩ : ↥𝔽) =
      φb ⟨coeffEmb Qb (intSeriesC ℚ pf / intSeriesC ℚ pg),
        coeffEmb_mem_laurentBaseChange Qb (div_mem_qExpFunctionFieldC f g hf hg hg0)⟩ :=
    Subtype.ext (by rw [hφb]; exact (coeffMap_complexEmbedding_coeffEmb _).symm)
  rw [heC, hτ', hφb]
  exact hτ k f g pf pg hf hg hg0

theorem diamondClause_of (hin : ModularCurve.HeckeDiamondInputsHAll M H)
    (hstD : ∀ (d : (ZMod M)ˣ), ∀ v ∈ ModularCurve.periodLatticeOf (CohCarrier.GammaH M H),
      (CuspForm.diamondLinH 2 d).dualMap v ∈ ModularCurve.periodLatticeOf (CohCarrier.GammaH M H))
    (φb : ↥(xHFunctionFieldBar M H) →+* ↥𝔽) (ι : JH M H →+ Pic0 ℂ ↥𝔽)
    (hφb : ∀ y : ↥(xHFunctionFieldBar M H),
      ((φb y : ↥𝔽) : LaurentSeries ℂ) =
        coeffMap (complexEmbedding : Qb →ₐ[ℚ] ℂ).toRingHom (y : LaurentSeries Qb))
    (hιg : ∀ (g : SemilinearAut Qb ↥(xHFunctionFieldBar M H)) (g' : SemilinearAut ℂ ↥𝔽),
      (∀ y : ↥(xHFunctionFieldBar M H), g' • φb y = φb (g • y)) → ∀ x : JH M H, ι (g • x) = g' • ι x)
    (hιext : ∀ σ : ↥(xHFunctionFieldBar M H) ≃ₐ[Qb] ↥(xHFunctionFieldBar M H),
      ∃ σ' : ↥𝔽 ≃ₐ[ℂ] ↥𝔽, ∀ y : ↥(xHFunctionFieldBar M H), σ' (φb y) = φb (σ y))
    (v : Pic0 ℂ ↥𝔽 →+ (Module.Dual ℂ (CuspForm (CohCarrier.GammaH M H) 2) ⧸ Λ))
    (hvA : ∀ (α : GL (Fin 2) ℝ), 0 < (α.det : ℝ) →
        α * (ModularGroup.T : GL (Fin 2) ℝ) * α⁻¹ ∈ (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) →
      ∀ (σ : ↥𝔽 ≃ₐ[ℂ] ↥𝔽),
      (∀ (k : ℤ) (f g : ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k)
          (pf pg : PowerSeries ℤ) (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg)
          (hg0 : intSeriesC ℚ pg ≠ 0),
          ((σ ⟨coeffEmb ℂ (intSeriesC ℚ pf / intSeriesC ℚ pg),
                coeffEmb_mem_laurentBaseChange ℂ (div_mem_qExpFunctionFieldC f g hf hg hg0)⟩ : ↥𝔽) :
              LaurentSeries ℂ) *
              HahnSeries.ofPowerSeries ℤ ℂ (qExpansion 1 (⇑g ∣[k] α)) =
            HahnSeries.ofPowerSeries ℤ ℂ (qExpansion 1 (⇑f ∣[k] α))) →
      ∀ (P : CuspForm (CohCarrier.GammaH M H) 2 →ₗ[ℂ] CuspForm (CohCarrier.GammaH M H) 2),
        (∀ f : CuspForm (CohCarrier.GammaH M H) 2, ⇑(P f) = ⇑f ∣[(2 : ℤ)] α⁻¹) →
        (∀ w ∈ Λ, P.dualMap w ∈ Λ) →
      ∀ (z : Pic0 ℂ ↥𝔽) (φ : Module.Dual ℂ (CuspForm (CohCarrier.GammaH M H) 2)),
        v z = Submodule.Quotient.mk φ →
        v (SemilinearAut.ofAlgAut σ • z) = Submodule.Quotient.mk (P.dualMap φ))
    (d : (ZMod M)ˣ) (x : JH M H) (φ : Module.Dual ℂ (CuspForm (CohCarrier.GammaH M H) 2))
    (hx : v (ι x) = Submodule.Quotient.mk φ) :
    v (ι (ModularCurve.diamondHBar M H d x)) = Submodule.Quotient.mk ((CuspForm.diamondLinH 2 d).dualMap φ) := by
  have hσd : IsDiamondAutHBar M H d (diamondAutHBar M H d) := hin.isDiamondAutHBar d
  have hγ : ((gammaUL M d : Gamma0 M) : SL(2, ℤ)) ∈ Gamma0 M := (gammaUL M d).2
  rw [diamondHBar_apply]
  refine autClause_of φb ι hφb hιg hιext v hvA ((((gammaUL M d : Gamma0 M) : SL(2, ℤ))) : GL (Fin 2) ℝ)
    (det_coeSL_pos _) (conj_T_mem _ hγ) (CuspForm.diamondLinH 2 d) (fun f => coe_diamondLinH_eq d f) (hstD d)
    (diamondAutHBar M H d) ?_ x φ hx

  intro k f g pf pg hf hg hg0
  obtain ⟨y, -, hyσ, hyq⟩ := hσd k f g pf pg hf hg hg0 ((gammaUL M d : Gamma0 M) : SL(2, ℤ)) hγ
    (gammaUL_apply_00 d)
  rw [hyσ, coeffMap_complexEmbedding_coeffEmb]
  exact hyq

variable (M H)

theorem mainGeneral (hin : ModularCurve.HeckeDiamondInputsHAll M H)
    (hstT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M), ∀ v ∈ ModularCurve.periodLatticeOf (CohCarrier.GammaH M H),
      (CuspForm.heckeTLinH 2 hℓ hℓM).dualMap v ∈ ModularCurve.periodLatticeOf (CohCarrier.GammaH M H))
    (hstU : ∀ (p : ℕ), p.Prime → p ∣ M → ∀ v ∈ ModularCurve.periodLatticeOf (CohCarrier.GammaH M H),
      (CuspForm.heckeULinH 2 p).dualMap v ∈ ModularCurve.periodLatticeOf (CohCarrier.GammaH M H))
    (hstD : ∀ (d : (ZMod M)ˣ), ∀ v ∈ ModularCurve.periodLatticeOf (CohCarrier.GammaH M H),
      (CuspForm.diamondLinH 2 d).dualMap v ∈ ModularCurve.periodLatticeOf (CohCarrier.GammaH M H))
    {I : Type*} (α : I → GL (Fin 2) ℝ) (hα : ∀ i, 0 < ((α i).det : ℝ))
    (hTα : ∀ i, α i * (ModularGroup.T : GL (Fin 2) ℝ) * (α i)⁻¹ ∈ (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)))
    (Lf : I → (CuspForm (CohCarrier.GammaH M H) 2 →ₗ[ℂ] CuspForm (CohCarrier.GammaH M H) 2))
    (hLf : ∀ (i : I) (f : CuspForm (CohCarrier.GammaH M H) 2), ⇑(Lf i f) = ⇑f ∣[(2 : ℤ)] (α i)⁻¹)
    (hstL : ∀ (i : I), ∀ v ∈ ModularCurve.periodLatticeOf (CohCarrier.GammaH M H),
      (Lf i).dualMap v ∈ ModularCurve.periodLatticeOf (CohCarrier.GammaH M H)) :
    ∃ u : ModularCurve.JH M H →+
        (Module.Dual ℂ (CuspForm (CohCarrier.GammaH M H) 2) ⧸ ModularCurve.periodLatticeOf (CohCarrier.GammaH M H)),
      Function.Injective u ∧
      (∀ y, IsOfFinAddOrder y → y ∈ u.range) ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (x : ModularCurve.JH M H)
          (φ : Module.Dual ℂ (CuspForm (CohCarrier.GammaH M H) 2)),
        u x = Submodule.Quotient.mk φ →
        u ((haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩;
            ModularCurve.heckeOperatorHAlong (AlgebraicClosure ℚ) M H ℓ) x) =
          Submodule.Quotient.mk ((CuspForm.heckeTLinH 2 hℓ hℓM).dualMap φ)) ∧
      (∀ (p : ℕ) (hp : p.Prime), p ∣ M → ∀ (x : ModularCurve.JH M H)
          (φ : Module.Dual ℂ (CuspForm (CohCarrier.GammaH M H) 2)),
        u x = Submodule.Quotient.mk φ →
        u ((haveI : NeZero p := ⟨hp.ne_zero⟩;
            ModularCurve.heckeOperatorHAlong (AlgebraicClosure ℚ) M H p) x) =
          Submodule.Quotient.mk ((CuspForm.heckeULinH 2 p).dualMap φ)) ∧
      (∀ (d : (ZMod M)ˣ) (x : ModularCurve.JH M H) (φ : Module.Dual ℂ (CuspForm (CohCarrier.GammaH M H) 2)),
        u x = Submodule.Quotient.mk φ →
        u (ModularCurve.diamondHBar M H d x) =
          Submodule.Quotient.mk ((CuspForm.diamondLinH 2 d).dualMap φ)) ∧
      ∀ (i : I) (τ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H)),
        (∀ (k : ℤ) (f g : ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k)
            (pf pg : PowerSeries ℤ) (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg)
            (hg0 : intSeriesC ℚ pg ≠ 0),
            coeffMap (complexEmbedding : Qb →ₐ[ℚ] ℂ).toRingHom
                ((τ ⟨coeffEmb Qb (intSeriesC ℚ pf / intSeriesC ℚ pg),
                    coeffEmb_mem_laurentBaseChange Qb (div_mem_qExpFunctionFieldC f g hf hg hg0)⟩ :
                    ↥(xHFunctionFieldBar M H)) : LaurentSeries Qb) *
                HahnSeries.ofPowerSeries ℤ ℂ (qExpansion 1 (⇑g ∣[k] α i)) =
              HahnSeries.ofPowerSeries ℤ ℂ (qExpansion 1 (⇑f ∣[k] α i))) →
        ∀ (x : ModularCurve.JH M H) (φ : Module.Dual ℂ (CuspForm (CohCarrier.GammaH M H) 2)),
          u x = Submodule.Quotient.mk φ →
          u (AlgebraicCurve.SemilinearAut.ofAlgAut τ • x) = Submodule.Quotient.mk ((Lf i).dualMap φ) := by

  obtain ⟨φb, ι, hφb, hιinj, hιtors, hιT, hιg, hιext⟩ :=
    ModularCurve.exists_injective_heckeEquivariant_addMonoidHom_jH_pic0_complex M H

  obtain ⟨v, hvbij, hvT, hvU, hvA, -⟩ :=
    ModularCurve.exists_bijective_heckeEquivariant_addMonoidHom_pic0_complex_xH_quotient_periodLatticeOf_slash
      M H (hinC M H) hstT hstU
  refine ⟨v.comp ι, hvbij.1.comp hιinj, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro y hy
    obtain ⟨z, rfl⟩ := hvbij.2 y
    have hz : IsOfFinAddOrder z := by
      obtain ⟨n, hn, hny⟩ := hy.exists_nsmul_eq_zero
      refine isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨n, hn, hvbij.1 ?_⟩
      rw [map_nsmul, map_zero]
      exact hny
    obtain ⟨x, rfl⟩ := hιtors z hz
    exact ⟨x, rfl⟩
  ·
    intro ℓ hℓ hℓM x φ hx
    have key := @hιT ℓ ⟨hℓ.ne_zero⟩ (hin.1 ℓ hℓ) (hinC M H ℓ hℓ) x
    rw [AddMonoidHom.comp_apply] at hx ⊢
    rw [key]
    exact hvT ℓ hℓ hℓM (ι x) φ hx
  ·
    intro p hp hpM x φ hx
    have key := @hιT p ⟨hp.ne_zero⟩ (hin.1 p hp) (hinC M H p hp) x
    rw [AddMonoidHom.comp_apply] at hx ⊢
    rw [key]
    exact hvU p hp hpM (ι x) φ hx
  ·
    intro d x φ hx
    rw [AddMonoidHom.comp_apply] at hx ⊢
    exact diamondClause_of hin hstD φb ι hφb hιg hιext v hvA d x φ hx
  ·
    intro i τ hτ x φ hx
    rw [AddMonoidHom.comp_apply] at hx ⊢
    exact autClause_of φb ι hφb hιg hιext v hvA (α i) (hα i) (hTα i) (Lf i) (hLf i) (hstL i) τ hτ x φ hx

end General

section Main

local notation "Qb" => AlgebraicClosure ℚ

variable (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M']

theorem mainThm
    (hin : ModularCurve.HeckeDiamondInputsHAll (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M'))
    (hstT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ q ^ 2 * M'),
      ∀ v ∈ ModularCurve.periodLatticeOf (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')),
        (CuspForm.heckeTLinH 2 hℓ hℓM).dualMap v ∈
          ModularCurve.periodLatticeOf (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')))
    (hstU : ∀ (p : ℕ), p.Prime → p ∣ q ^ 2 * M' →
      ∀ v ∈ ModularCurve.periodLatticeOf (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')),
        (CuspForm.heckeULinH 2 p).dualMap v ∈
          ModularCurve.periodLatticeOf (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')))
    (hstD : ∀ (d : (ZMod (q ^ 2 * M'))ˣ),
      ∀ v ∈ ModularCurve.periodLatticeOf (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')),
        (CuspForm.diamondLinH 2 d).dualMap v ∈
          ModularCurve.periodLatticeOf (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')))
    (L : ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
      (CuspForm (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')) 2 →ₗ[ℂ]
        CuspForm (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')) 2))
    (hL : ∀ (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M')
      (f : CuspForm (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')) 2),
      ⇑(L γ hγ f) = ⇑f ∣[(2 : ℤ)] (ModularCurve.FullLevel.conjElem q γ)⁻¹)
    (hstL : ∀ (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M'),
      ∀ v ∈ ModularCurve.periodLatticeOf (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')),
        (L γ hγ).dualMap v ∈
          ModularCurve.periodLatticeOf (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M'))) :
    ∃ u : ModularCurve.FullLevel.jacComp q M' →+
        (Module.Dual ℂ (CuspForm (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')) 2) ⧸
          ModularCurve.periodLatticeOf (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M'))),
      Function.Injective u ∧
      (∀ y, IsOfFinAddOrder y → y ∈ u.range) ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ q ^ 2 * M') (x : ModularCurve.FullLevel.jacComp q M')
          (φ : Module.Dual ℂ (CuspForm (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')) 2)),
        u x = Submodule.Quotient.mk φ →
        u ((haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩;
            ModularCurve.heckeOperatorHAlong (AlgebraicClosure ℚ) (q ^ 2 * M')
              (ModularCurve.FullLevel.levelH q M') ℓ) x) =
          Submodule.Quotient.mk ((CuspForm.heckeTLinH 2 hℓ hℓM).dualMap φ)) ∧
      (∀ (p : ℕ) (hp : p.Prime), p ∣ q ^ 2 * M' → ∀ (x : ModularCurve.FullLevel.jacComp q M')
          (φ : Module.Dual ℂ (CuspForm (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')) 2)),
        u x = Submodule.Quotient.mk φ →
        u ((haveI : NeZero p := ⟨hp.ne_zero⟩;
            ModularCurve.heckeOperatorHAlong (AlgebraicClosure ℚ) (q ^ 2 * M')
              (ModularCurve.FullLevel.levelH q M') p) x) =
          Submodule.Quotient.mk ((CuspForm.heckeULinH 2 p).dualMap φ)) ∧
      (∀ (d : (ZMod (q ^ 2 * M'))ˣ) (x : ModularCurve.FullLevel.jacComp q M')
          (φ : Module.Dual ℂ (CuspForm (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')) 2)),
        u x = Submodule.Quotient.mk φ →
        u (ModularCurve.diamondHBar (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M') d x) =
          Submodule.Quotient.mk ((CuspForm.diamondLinH 2 d).dualMap φ)) ∧
      ∃ ζ₀ : ModularCurve.FullLevel.Idx q,
        ∀ (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M')
          (τ : ModularCurve.FullLevel.fieldBar q M' ≃ₐ[AlgebraicClosure ℚ] ModularCurve.FullLevel.fieldBar q M'),
          ModularCurve.FullLevel.IsLevelAutBar q M' ζ₀ γ τ →
          ∀ (x : ModularCurve.FullLevel.jacComp q M')
            (φ : Module.Dual ℂ (CuspForm (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')) 2)),
            u x = Submodule.Quotient.mk φ →
            u (AlgebraicCurve.SemilinearAut.ofAlgAut τ • x) = Submodule.Quotient.mk ((L γ hγ).dualMap φ) := by

  obtain ⟨ζ₀, hζ₀⟩ := exists_idx_complexEmbedding_eq q

  obtain ⟨u, hinj, htors, hT, hU, hD, hA⟩ :=
    mainGeneral (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M') hin hstT hstU hstD
      (I := {γ : SL(2, ℤ) // γ ∈ CongruenceSubgroup.Gamma0 M'})
      (fun γ => conjElem q γ.1) (fun γ => det_conjElem_pos q γ.1)
      (fun γ => conjElem_T_conjElem_inv_mem M' γ.1 γ.2)
      (fun γ => L γ.1 γ.2) (fun γ f => hL γ.1 γ.2 f) (fun γ => hstL γ.1 γ.2)
  refine ⟨u, hinj, htors, hT, hU, hD, ζ₀, fun γ hγ τ hτ x φ hx => ?_⟩
  exact hA ⟨γ, hγ⟩ τ (fun k f g pf pg hf hg hg0 => hτ k f g pf pg hf hg hg0 _ hζ₀) x φ hx

end Main

end AJHLevelGlue
p2m_reactivate "P2MW.S_ModularCurve_exists_injective_addMonoidHom_jH_quotient_periodLatticeOf_levelAut.AJHLevelGlue"

end
p2m_reactivate "P2MW.S_ModularCurve_exists_injective_addMonoidHom_jH_quotient_periodLatticeOf_levelAut.AJHLevelGlue"

open scoped MatrixGroups ModularForm TensorProduct in
theorem solution
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M']
    (hin : ModularCurve.HeckeDiamondInputsHAll (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M'))
    (hstT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ q ^ 2 * M'),
      ∀ v ∈ ModularCurve.periodLatticeOf (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')),
        (CuspForm.heckeTLinH 2 hℓ hℓM).dualMap v ∈
          ModularCurve.periodLatticeOf (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')))
    (hstU : ∀ (p : ℕ), p.Prime → p ∣ q ^ 2 * M' →
      ∀ v ∈ ModularCurve.periodLatticeOf (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')),
        (CuspForm.heckeULinH 2 p).dualMap v ∈
          ModularCurve.periodLatticeOf (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')))
    (hstD : ∀ (d : (ZMod (q ^ 2 * M'))ˣ),
      ∀ v ∈ ModularCurve.periodLatticeOf (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')),
        (CuspForm.diamondLinH 2 d).dualMap v ∈
          ModularCurve.periodLatticeOf (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')))
    (L : ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
      (CuspForm (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')) 2 →ₗ[ℂ]
        CuspForm (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')) 2))
    (hL : ∀ (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M')
      (f : CuspForm (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')) 2),
      ⇑(L γ hγ f) = ⇑f ∣[(2 : ℤ)] (ModularCurve.FullLevel.conjElem q γ)⁻¹)
    (hstL : ∀ (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M'),
      ∀ v ∈ ModularCurve.periodLatticeOf (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')),
        (L γ hγ).dualMap v ∈
          ModularCurve.periodLatticeOf (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M'))) :
    ∃ u : ModularCurve.FullLevel.jacComp q M' →+
        (Module.Dual ℂ (CuspForm (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')) 2) ⧸
          ModularCurve.periodLatticeOf (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M'))),
      Function.Injective u ∧
      (∀ y, IsOfFinAddOrder y → y ∈ u.range) ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ q ^ 2 * M') (x : ModularCurve.FullLevel.jacComp q M')
          (φ : Module.Dual ℂ (CuspForm (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')) 2)),
        u x = Submodule.Quotient.mk φ →
        u ((haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩;
            ModularCurve.heckeOperatorHAlong (AlgebraicClosure ℚ) (q ^ 2 * M')
              (ModularCurve.FullLevel.levelH q M') ℓ) x) =
          Submodule.Quotient.mk ((CuspForm.heckeTLinH 2 hℓ hℓM).dualMap φ)) ∧
      (∀ (p : ℕ) (hp : p.Prime), p ∣ q ^ 2 * M' → ∀ (x : ModularCurve.FullLevel.jacComp q M')
          (φ : Module.Dual ℂ (CuspForm (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')) 2)),
        u x = Submodule.Quotient.mk φ →
        u ((haveI : NeZero p := ⟨hp.ne_zero⟩;
            ModularCurve.heckeOperatorHAlong (AlgebraicClosure ℚ) (q ^ 2 * M')
              (ModularCurve.FullLevel.levelH q M') p) x) =
          Submodule.Quotient.mk ((CuspForm.heckeULinH 2 p).dualMap φ)) ∧
      (∀ (d : (ZMod (q ^ 2 * M'))ˣ) (x : ModularCurve.FullLevel.jacComp q M')
          (φ : Module.Dual ℂ (CuspForm (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')) 2)),
        u x = Submodule.Quotient.mk φ →
        u (ModularCurve.diamondHBar (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M') d x) =
          Submodule.Quotient.mk ((CuspForm.diamondLinH 2 d).dualMap φ)) ∧
      ∃ ζ₀ : ModularCurve.FullLevel.Idx q,
        ∀ (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M')
          (τ : ModularCurve.FullLevel.fieldBar q M' ≃ₐ[AlgebraicClosure ℚ] ModularCurve.FullLevel.fieldBar q M'),
          ModularCurve.FullLevel.IsLevelAutBar q M' ζ₀ γ τ →
          ∀ (x : ModularCurve.FullLevel.jacComp q M')
            (φ : Module.Dual ℂ (CuspForm (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')) 2)),
            u x = Submodule.Quotient.mk φ →
            u (AlgebraicCurve.SemilinearAut.ofAlgAut τ • x) = Submodule.Quotient.mk ((L γ hγ).dualMap φ) :=
  AJHLevelGlue.mainThm q M' hin hstT hstU hstD L hL hstL

end S_ModularCurve_exists_injective_addMonoidHom_jH_quotient_periodLatticeOf_levelAut
end P2MW
export P2MW.S_ModularCurve_exists_injective_addMonoidHom_jH_quotient_periodLatticeOf_levelAut (solution)
