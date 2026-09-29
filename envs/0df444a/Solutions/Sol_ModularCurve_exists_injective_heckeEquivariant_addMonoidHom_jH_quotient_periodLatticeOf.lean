-- Prove2me | solution 1 for ModularCurve.exists_injective_heckeEquivariant_addMonoidHom_jH_quotient_periodLatticeOf
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/eb126e88-e192-5be1-988d-3414ee537daf

import Mathlib
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_CuspForm_HeckeOperatorFormsGammaH
import Definitions.Def_ModularCurve_PeriodOf
import Definitions.Def_GaloisRep_ComplexConjugation
import Definitions.Def_CohCarrier_CharInvolution
import Theorems.Thm_ModularCurve_heckeInputsHAlong
import Theorems.Thm_ModularCurve_exists_injective_heckeEquivariant_addMonoidHom_jH_pic0_complex
import Theorems.Thm_ModularCurve_exists_bijective_heckeEquivariant_addMonoidHom_pic0_complex_xH_quotient_periodLatticeOf
import Theorems.Thm_CuspForm_exists_apply_eq_conj_apply_J_smul_of_forall_jConjSL_mem
import Theorems.Thm_ModularCurve_periodAlongOf_eq_neg_conj_periodAlongOf_J_smul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_injective_heckeEquivariant_addMonoidHom_jH_quotient_periodLatticeOf
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z"
p2m_attr_erase "instance" "ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0 HeckeEis.instFiniteIndexHeckeUpper FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.ComplexPlaceDictionaryOf.pt_ofGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.injEq ModularCurve.ComplexPlaceDictionaryOf.pt_toGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.sizeOf_spec ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec ModularCurve.qExpandAlgHomC_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow"
p2m_attr_erase "simp" "ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe"
p2m_attr_erase "simp" "AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero ModularCurve.LevelN.coe_jGen FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero HeckeEis.coeffCoboundaryMap_apply"

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open scoped MatrixGroups ModularForm ComplexConjugate

namespace AJHGlue

open CohCarrier ModularCurve UpperHalfPlane Matrix.SpecialLinearGroup AlgebraicCurve

section ConjSide

variable (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)

abbrev Lat : Submodule ℤ (Module.Dual ℂ (CuspForm (GammaH M H) 2)) := periodLatticeOf (GammaH M H)

theorem J_smul_I : UpperHalfPlane.J • UpperHalfPlane.I = UpperHalfPlane.I := by
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.coe_J_smul, UpperHalfPlane.coe_I, Complex.conj_I, neg_neg]

theorem J_smul_J_smul (τ : ℍ) : UpperHalfPlane.J • UpperHalfPlane.J • τ = τ := by
  rw [← mul_smul, ← sq, UpperHalfPlane.J_sq, one_smul]

theorem J_inv_mul_mapGL_mul_J (γ : SL(2, ℤ)) :
    UpperHalfPlane.J⁻¹ * (mapGL ℝ γ : GL (Fin 2) ℝ) * UpperHalfPlane.J =
      (mapGL ℝ (ModularCurve.Period.jConjSL γ) : GL (Fin 2) ℝ) := by
  have hJ : UpperHalfPlane.J⁻¹ = UpperHalfPlane.J := by
    rw [inv_eq_iff_mul_eq_one, ← sq, UpperHalfPlane.J_sq]
  rw [hJ]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [UpperHalfPlane.J, Matrix.mul_apply, Fin.sum_univ_two, ModularCurve.Period.jConjMat,
      Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.vecMul, dotProduct]

theorem J_smul_sl_smul (γ : SL(2, ℤ)) (τ : ℍ) :
    UpperHalfPlane.J • (γ • τ) = ModularCurve.Period.jConjSL γ • (UpperHalfPlane.J • τ) := by
  have hJ : UpperHalfPlane.J⁻¹ = UpperHalfPlane.J := by
    rw [inv_eq_iff_mul_eq_one, ← sq, UpperHalfPlane.J_sq]
  have h := J_inv_mul_mapGL_mul_J γ
  rw [hJ] at h
  have h2 : UpperHalfPlane.J * (mapGL ℝ γ : GL (Fin 2) ℝ) =
      (mapGL ℝ (ModularCurve.Period.jConjSL γ) : GL (Fin 2) ℝ) * UpperHalfPlane.J := by
    rw [← h, mul_assoc, mul_assoc, ← sq, UpperHalfPlane.J_sq, mul_one]
  rw [MulAction.compHom_smul_def, MulAction.compHom_smul_def, ← mul_smul, ← mul_smul]
  exact congrArg (· • τ) h2

theorem jStable : ∀ γ ∈ GammaH M H, ModularCurve.Period.jConjSL γ ∈ GammaH M H :=
  fun _ hγ => CohCarrier.jConjSL_mem_GammaH M H hγ

def conjF (f : CuspForm (GammaH M H) 2) : CuspForm (GammaH M H) 2 :=
  Classical.choose
    (CuspForm.exists_apply_eq_conj_apply_J_smul_of_forall_jConjSL_mem (GammaH M H) (jStable M H) 2 f)

theorem conjF_apply (f : CuspForm (GammaH M H) 2) (τ : ℍ) :
    conjF M H f τ = conj (f (UpperHalfPlane.J • τ)) :=
  Classical.choose_spec
    (CuspForm.exists_apply_eq_conj_apply_J_smul_of_forall_jConjSL_mem (GammaH M H) (jStable M H) 2 f) τ

theorem conjF_add (f g : CuspForm (GammaH M H) 2) : conjF M H (f + g) = conjF M H f + conjF M H g :=
  CuspForm.ext fun τ => by simp only [conjF_apply, CuspForm.add_apply, map_add]

theorem conjF_smul (a : ℂ) (f : CuspForm (GammaH M H) 2) : conjF M H (a • f) = conj a • conjF M H f :=
  CuspForm.ext fun τ => by
    rw [conjF_apply, CuspForm.IsGLPos.smul_apply, CuspForm.IsGLPos.smul_apply, smul_eq_mul, smul_eq_mul,
      map_mul, conjF_apply]

def Rdual (φ : Module.Dual ℂ (CuspForm (GammaH M H) 2)) : Module.Dual ℂ (CuspForm (GammaH M H) 2) where
  toFun f := -conj (φ (conjF M H f))
  map_add' f g := by rw [conjF_add, map_add, map_add, neg_add]
  map_smul' a f := by
    show -conj (φ (conjF M H (a • f))) = a • (-conj (φ (conjF M H f)))
    rw [conjF_smul, LinearMap.map_smul, smul_eq_mul, map_mul, Complex.conj_conj, smul_eq_mul, mul_neg]

theorem Rdual_apply (φ : Module.Dual ℂ (CuspForm (GammaH M H) 2)) (f : CuspForm (GammaH M H) 2) :
    Rdual M H φ f = -conj (φ (conjF M H f)) := rfl

def R : Module.Dual ℂ (CuspForm (GammaH M H) 2) →+ Module.Dual ℂ (CuspForm (GammaH M H) 2) where
  toFun := Rdual M H
  map_zero' := LinearMap.ext fun f => by
    rw [Rdual_apply, LinearMap.zero_apply, map_zero, neg_zero, LinearMap.zero_apply]
  map_add' φ ψ := LinearMap.ext fun f => by
    simp only [Rdual_apply, LinearMap.add_apply, map_add, neg_add]

theorem R_apply_apply (φ : Module.Dual ℂ (CuspForm (GammaH M H) 2)) (f : CuspForm (GammaH M H) 2) :
    R M H φ f = -conj (φ (conjF M H f)) := rfl

theorem eq_R_of_pairing (φ φ' : Module.Dual ℂ (CuspForm (GammaH M H) 2))
    (hpair : ∀ f g : CuspForm (GammaH M H) 2,
      (∀ τ : ℍ, g τ = conj (f (UpperHalfPlane.J • τ))) → φ' g = -conj (φ f)) :
    φ' = R M H φ :=
  LinearMap.ext fun g => by
    rw [R_apply_apply]
    refine hpair (conjF M H g) g fun τ => ?_
    rw [conjF_apply, Complex.conj_conj, J_smul_J_smul]

theorem R_periodOf (δ : ↥(GammaH M H)) :
    R M H (periodOf (GammaH M H) δ) = periodOf (GammaH M H) (jConjGammaH M H δ) := by
  refine LinearMap.ext fun f => ?_
  rw [R_apply_apply]
  show -conj (periodAlongOf (GammaH M H) UpperHalfPlane.I ((δ : SL(2, ℤ)) • UpperHalfPlane.I) (conjF M H f)) =
    periodAlongOf (GammaH M H) UpperHalfPlane.I
      ((ModularCurve.Period.jConjSL (δ : SL(2, ℤ))) • UpperHalfPlane.I) f
  rw [ModularCurve.periodAlongOf_eq_neg_conj_periodAlongOf_J_smul (GammaH M H) f (conjF M H f)
      (conjF_apply M H f), map_neg, Complex.conj_conj, neg_neg, J_smul_sl_smul, J_smul_I]

theorem map_mem_of_forall {T : Module.Dual ℂ (CuspForm (GammaH M H) 2) →+ Module.Dual ℂ (CuspForm (GammaH M H) 2)}
    (hT : ∀ δ : ↥(GammaH M H), T (periodOf (GammaH M H) δ) ∈ Lat M H) :
    ∀ v ∈ Lat M H, T v ∈ Lat M H := by
  intro v hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨δ, rfl⟩ := hx
    exact hT δ
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul n x _ hx => rw [map_zsmul]; exact Submodule.smul_mem _ n hx

theorem R_mem : ∀ v ∈ Lat M H, R M H v ∈ Lat M H :=
  map_mem_of_forall M H fun δ => by
    rw [R_periodOf]
    exact periodOf_mem_periodLatticeOf _ _

theorem partner_mem (φ φ' : Module.Dual ℂ (CuspForm (GammaH M H) 2))
    (hpair : ∀ f g : CuspForm (GammaH M H) 2,
      (∀ τ : ℍ, g τ = conj (f (UpperHalfPlane.J • τ))) → φ' g = -conj (φ f))
    (hφ : φ ∈ Lat M H) : φ' ∈ Lat M H := by
  rw [eq_R_of_pairing M H φ φ' hpair]
  exact R_mem M H φ hφ

end ConjSide

section Generators

local notation "Qb" => AlgebraicClosure ℚ

theorem complexEmbedding_comp_algebraMap :
    (complexEmbedding : Qb →ₐ[ℚ] ℂ).toRingHom.comp (algebraMap ℚ Qb) = algebraMap ℚ ℂ :=
  complexEmbedding.comp_algebraMap

theorem coeffMap_complexEmbedding_coeffEmb (z : LaurentSeries ℚ) :
    coeffMap (complexEmbedding : Qb →ₐ[ℚ] ℂ).toRingHom (coeffEmb Qb z) = coeffEmb ℂ z := by
  rw [coeffEmb, coeffEmb, coeffMap_coeffMap]
  exact coeffMap_congr complexEmbedding_comp_algebraMap z

theorem coeffEmb_complex_eq (y : LaurentSeries ℚ) : coeffEmb ℂ y = coeffMap (algebraMap ℚ ℂ) y := rfl

end Generators

section Main

local notation "Qb" => AlgebraicClosure ℚ

variable (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)

theorem hinC : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩; HeckeInputsHAlong ℂ M H ℓ :=
  fun ℓ hℓ => by
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    exact ModularCurve.heckeInputsHAlong ℂ M H ℓ

theorem mainThm (hin : ModularCurve.HeckeDiamondInputsHAll M H)
    (hstT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M), ∀ v ∈ ModularCurve.periodLatticeOf (CohCarrier.GammaH M H),
      (CuspForm.heckeTLinH 2 hℓ hℓM).dualMap v ∈ ModularCurve.periodLatticeOf (CohCarrier.GammaH M H))
    (hstU : ∀ (q : ℕ), q.Prime → q ∣ M → ∀ v ∈ ModularCurve.periodLatticeOf (CohCarrier.GammaH M H),
      (CuspForm.heckeULinH 2 q).dualMap v ∈ ModularCurve.periodLatticeOf (CohCarrier.GammaH M H))
    (hstD : ∀ (d : (ZMod M)ˣ), ∀ v ∈ ModularCurve.periodLatticeOf (CohCarrier.GammaH M H),
      (CuspForm.diamondLinH 2 d).dualMap v ∈ ModularCurve.periodLatticeOf (CohCarrier.GammaH M H)) :
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
      (∀ (q : ℕ) (hq : q.Prime), q ∣ M → ∀ (x : ModularCurve.JH M H)
          (φ : Module.Dual ℂ (CuspForm (CohCarrier.GammaH M H) 2)),
        u x = Submodule.Quotient.mk φ →
        u ((haveI : NeZero q := ⟨hq.ne_zero⟩;
            ModularCurve.heckeOperatorHAlong (AlgebraicClosure ℚ) M H q) x) =
          Submodule.Quotient.mk ((CuspForm.heckeULinH 2 q).dualMap φ)) ∧
      ∀ (d : (ZMod M)ˣ) (x : ModularCurve.JH M H) (φ : Module.Dual ℂ (CuspForm (CohCarrier.GammaH M H) 2)),
        u x = Submodule.Quotient.mk φ →
        u (ModularCurve.diamondHBar M H d x) =
          Submodule.Quotient.mk ((CuspForm.diamondLinH 2 d).dualMap φ) := by

  obtain ⟨φb, ι, hφb, hιinj, hιtors, hιT, hιg, hιext⟩ :=
    ModularCurve.exists_injective_heckeEquivariant_addMonoidHom_jH_pic0_complex M H

  obtain ⟨v, hvbij, hvT, hvU, hvD, -⟩ :=
    ModularCurve.exists_bijective_heckeEquivariant_addMonoidHom_pic0_complex_xH_quotient_periodLatticeOf M H
      (hinC M H) hstT hstU hstD (fun φ φ' hpair hφ => partner_mem M H φ φ' hpair hφ)
  refine ⟨v.comp ι, hvbij.1.comp hιinj, ?_, ?_, ?_, ?_⟩
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
    intro q hq hqM x φ hx
    have key := @hιT q ⟨hq.ne_zero⟩ (hin.1 q hq) (hinC M H q hq) x
    rw [AddMonoidHom.comp_apply] at hx ⊢
    rw [key]
    exact hvU q hq hqM (ι x) φ hx
  ·
    intro d x φ hx
    have hσd : IsDiamondAutHBar M H d (diamondAutHBar M H d) := hin.isDiamondAutHBar d
    obtain ⟨σ', hσ'⟩ := hιext (diamondAutHBar M H d)
    have hcompat : ∀ y : ↥(xHFunctionFieldBar M H),
        SemilinearAut.ofAlgAut σ' • φb y = φb (SemilinearAut.ofAlgAut (diamondAutHBar M H d) • y) :=
      fun y => by rw [SemilinearAut.ofAlgAut_smul, SemilinearAut.ofAlgAut_smul, hσ']
    rw [AddMonoidHom.comp_apply] at hx ⊢
    rw [diamondHBar_apply,
      hιg (SemilinearAut.ofAlgAut (diamondAutHBar M H d)) (SemilinearAut.ofAlgAut σ') hcompat x]
    refine hvD d σ' ?_ (ι x) φ hx

    intro k f g pf pg hf hg hg0 γ hγ hd
    obtain ⟨y, -, hyσ, hyq⟩ := hσd k f g pf pg hf hg hg0 γ hγ hd

    have heC : (⟨coeffEmb ℂ (intSeriesC ℚ pf / intSeriesC ℚ pg),
          coeffEmb_mem_laurentBaseChange ℂ (div_mem_qExpFunctionFieldC f g hf hg hg0)⟩ :
          ↥(laurentBaseChange ℂ (xHFunctionField M H))) =
        φb ⟨coeffEmb Qb (intSeriesC ℚ pf / intSeriesC ℚ pg),
          coeffEmb_mem_laurentBaseChange Qb (div_mem_qExpFunctionFieldC f g hf hg hg0)⟩ :=
      Subtype.ext (by rw [hφb]; exact (coeffMap_complexEmbedding_coeffEmb _).symm)
    have step : ((σ' ⟨coeffEmb ℂ (intSeriesC ℚ pf / intSeriesC ℚ pg),
          coeffEmb_mem_laurentBaseChange ℂ (div_mem_qExpFunctionFieldC f g hf hg hg0)⟩ :
          ↥(laurentBaseChange ℂ (xHFunctionField M H))) : LaurentSeries ℂ) =
        coeffMap (algebraMap ℚ ℂ) y := by
      rw [heC, hσ', hφb, hyσ, coeffMap_complexEmbedding_coeffEmb]
      rfl
    rw [step]
    exact hyq

end Main

end AJHGlue

end

theorem solution
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (hin : ModularCurve.HeckeDiamondInputsHAll M H)
    (hstT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M), ∀ v ∈ ModularCurve.periodLatticeOf (CohCarrier.GammaH M H),
      (CuspForm.heckeTLinH 2 hℓ hℓM).dualMap v ∈ ModularCurve.periodLatticeOf (CohCarrier.GammaH M H))
    (hstU : ∀ (q : ℕ), q.Prime → q ∣ M → ∀ v ∈ ModularCurve.periodLatticeOf (CohCarrier.GammaH M H),
      (CuspForm.heckeULinH 2 q).dualMap v ∈ ModularCurve.periodLatticeOf (CohCarrier.GammaH M H))
    (hstD : ∀ (d : (ZMod M)ˣ), ∀ v ∈ ModularCurve.periodLatticeOf (CohCarrier.GammaH M H),
      (CuspForm.diamondLinH 2 d).dualMap v ∈ ModularCurve.periodLatticeOf (CohCarrier.GammaH M H)) :
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
      (∀ (q : ℕ) (hq : q.Prime), q ∣ M → ∀ (x : ModularCurve.JH M H)
          (φ : Module.Dual ℂ (CuspForm (CohCarrier.GammaH M H) 2)),
        u x = Submodule.Quotient.mk φ →
        u ((haveI : NeZero q := ⟨hq.ne_zero⟩;
            ModularCurve.heckeOperatorHAlong (AlgebraicClosure ℚ) M H q) x) =
          Submodule.Quotient.mk ((CuspForm.heckeULinH 2 q).dualMap φ)) ∧
      ∀ (d : (ZMod M)ˣ) (x : ModularCurve.JH M H) (φ : Module.Dual ℂ (CuspForm (CohCarrier.GammaH M H) 2)),
        u x = Submodule.Quotient.mk φ →
        u (ModularCurve.diamondHBar M H d x) =
          Submodule.Quotient.mk ((CuspForm.diamondLinH 2 d).dualMap φ) :=
  AJHGlue.mainThm M H hin hstT hstU hstD

end S_ModularCurve_exists_injective_heckeEquivariant_addMonoidHom_jH_quotient_periodLatticeOf
end P2MW
export P2MW.S_ModularCurve_exists_injective_heckeEquivariant_addMonoidHom_jH_quotient_periodLatticeOf (solution)
