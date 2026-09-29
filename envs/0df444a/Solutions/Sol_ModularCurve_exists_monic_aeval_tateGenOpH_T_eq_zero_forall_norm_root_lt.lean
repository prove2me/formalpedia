-- Prove2me | solution 1 for ModularCurve.exists_monic_aeval_tateGenOpH_T_eq_zero_forall_norm_root_lt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/ed4ffed5-36bd-5caf-8fad-02c14175008c

import Mathlib
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_EllipticCurve_TateModule
import Definitions.Def_ModularCurve_PeriodOf
import Definitions.Def_CuspForm_HeckeOperatorFormsGammaH
import Definitions.Def_CuspForm_PrimitiveFormGamma1
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_ModularCurve_XH
import Theorems.Thm_ModularCurve_exists_heckeEquivariant_linearEquiv_tateModule_jH_padicInt_tensor_periodLatticeOf
import Theorems.Thm_ModularCurve_exists_basis_periodLatticeOf_linearIndependent_real_span_eq_top_of_isCongruenceSubgroup
import Theorems.Thm_ModularCurve_periodMapOf_gammaH_eq_heckeT_of_coe_eq_heckeU_add_slash
import Theorems.Thm_CuspForm_stableT
import Theorems.Thm_CuspForm_stableD
import Theorems.Thm_ModularCurve_periodMapOf_apply_eq_periodOf
import Theorems.Thm_ModularCurve_periodMapOf_mem_parabolicHoms
import Theorems.Thm_CuspForm_exists_basis_hasNebentypus_qCoeff_hecke_eigen
import Theorems.Thm_CuspForm_norm_sq_lt_of_hasNebentypus_qCoeff_hecke_eigen
import Theorems.Thm_CuspForm_qCoeff_heckeTLinH_eq_qCoeff_mul_add_pow_mul_qCoeff_diamondLinH
import Theorems.Thm_ModularFormClass_eq_of_forall_qCoeff_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_monic_aeval_tateGenOpH_T_eq_zero_forall_norm_root_lt
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z"
p2m_attr_erase "instance" "ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0 HeckeEis.instFiniteIndexHeckeUpper FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par"
p2m_attr_erase "simp" "ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply CohCarrier.jConjGammaH_jConjGammaH CohCarrier.coe_jConjGammaH CohCarrier.charInvolution_apply ModularCurve.Period.jConjMat_apply_zero_one ModularCurve.Period.jConjSL_coe ModularCurve.Period.jConjMat_apply_one_zero ModularCurve.Period.jConjMat_apply_one_one ModularCurve.Period.jConjGamma0_coe ModularCurve.Period.charInvolution_apply ModularCurve.Period.jConjMat_apply_zero_zero AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero"
p2m_attr_erase "simp" "ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.ComplexPlaceDictionaryOf.pt_ofGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.injEq ModularCurve.ComplexPlaceDictionaryOf.pt_toGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.sizeOf_spec ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec ModularCurve.qExpandAlgHomC_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply"
p2m_attr_erase "simp" "ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁"
p2m_attr_erase "simp" "PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero"
p2m_attr_erase "simp" "ModularCurve.LevelN.coe_jGen FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero HeckeEis.coeffCoboundaryMap_apply CuspForm.PeterssonCoset.mapGL_apply"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

noncomputable section

open scoped TensorProduct MatrixGroups ModularForm ComplexConjugate

namespace SpecTpRed

section Naturality

open CohCarrier

variable (M : ℕ) (H : Subgroup (ZMod M)ˣ) (ℓ : ℕ) [NeZero ℓ]
variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]

theorem heckeT_apply_eq_sum (φ : H1 M H A) (u : ↥(GammaH M H))
    [Fintype (Quotient (MulAction.orbitRel (Subgroup.zpowers u)
      (↥(GammaH M H) ⧸ GammaHUpper M H ℓ)))] :
    heckeT M H ℓ A φ (Additive.ofMul u) =
      ∑ O : Quotient (MulAction.orbitRel (Subgroup.zpowers u)
          (↥(GammaH M H) ⧸ GammaHUpper M H ℓ)),
        φ (Additive.ofMul (conjL M H ℓ
          ⟨O.out.out⁻¹ * u ^ Function.minimalPeriod (u • ·) O.out * O.out.out,
            QuotientGroup.out_conj_pow_minimalPeriod_mem _ u O.out⟩)) := by
  change Multiplicative.toAdd (MonoidHom.transfer
    ((AddMonoidHom.toMultiplicativeRight φ).comp (conjL M H ℓ)) u) = _
  rw [MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot, toAdd_prod]
  rfl

theorem heckeT_comp (h : A →+ B) (φ : H1 M H A) :
    heckeT M H ℓ B (h.comp φ) = h.comp (heckeT M H ℓ A φ) := by
  classical
  refine AddMonoidHom.ext fun a => ?_
  set u := Additive.toMul a with hu
  have ha : a = Additive.ofMul u := rfl
  haveI : Fintype (Quotient (MulAction.orbitRel (Subgroup.zpowers u)
      (↥(GammaH M H) ⧸ GammaHUpper M H ℓ))) := Fintype.ofFinite _
  rw [ha, AddMonoidHom.comp_apply, heckeT_apply_eq_sum, heckeT_apply_eq_sum, map_sum]
  rfl

end Naturality

section PeriodSide

p2m_open "CohCarrier ModularCurve~baseChangeHom"

variable (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)

theorem isCongruenceSubgroup_gammaH : CongruenceSubgroup.IsCongruenceSubgroup (GammaH M H) :=
  CongruenceSubgroup.isCongruenceSubgroup_trans _ _ (ModularCurve.Gamma1_le_GammaH M H)
    (CongruenceSubgroup.Gamma1_is_congruence M)

scoped instance finiteIndex_gammaH : (GammaH M H).FiniteIndex := (isCongruenceSubgroup_gammaH M H).finiteIndex

abbrev Lat : Submodule ℤ (Module.Dual ℂ (CuspForm (GammaH M H) 2)) := periodLatticeOf (GammaH M H)

def perL (δ : ↥(GammaH M H)) : ↥(Lat M H) :=
  ⟨periodOf (GammaH M H) δ, periodOf_mem_periodLatticeOf (GammaH M H) δ⟩

@[scoped simp] theorem coe_perL (δ : ↥(GammaH M H)) :
    ((perL M H δ : ↥(Lat M H)) : Module.Dual ℂ (CuspForm (GammaH M H) 2)) = periodOf (GammaH M H) δ := rfl

theorem periodOf_mul (γ δ : ↥(GammaH M H)) :
    periodOf (GammaH M H) (γ * δ) = periodOf (GammaH M H) γ + periodOf (GammaH M H) δ := by
  refine LinearMap.ext fun f => ?_
  rw [LinearMap.add_apply, ← periodMapOf_apply_eq_periodOf, ← periodMapOf_apply_eq_periodOf,
    ← periodMapOf_apply_eq_periodOf, ofMul_mul, map_add]

theorem periodOf_one : periodOf (GammaH M H) 1 = 0 := by
  have h := periodOf_mul M H 1 1
  rw [mul_one] at h
  exact left_eq_add.mp h

theorem periodOf_eq_zero_of_trace_sq (γ : ↥(GammaH M H))
    (hγ : ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 = 4) :
    periodOf (GammaH M H) γ = 0 := by
  refine LinearMap.ext fun f => ?_
  rw [← periodMapOf_apply_eq_periodOf, LinearMap.zero_apply]
  exact (Period.mem_parabolicHoms_iff.mp (periodMapOf_mem_parabolicHoms (GammaH M H) f)) γ hγ

def perHom : H1 M H ↥(Lat M H) where
  toFun a := perL M H (Additive.toMul a)
  map_zero' := Subtype.ext (periodOf_one M H)
  map_add' a b := Subtype.ext (periodOf_mul M H (Additive.toMul a) (Additive.toMul b))

@[scoped simp] theorem perHom_apply (δ : ↥(GammaH M H)) : perHom M H (Additive.ofMul δ) = perL M H δ := rfl

def evalL (f : CuspForm (GammaH M H) 2) : ↥(Lat M H) →+ ℂ where
  toFun v := (v : Module.Dual ℂ (CuspForm (GammaH M H) 2)) f
  map_zero' := rfl
  map_add' _ _ := rfl

theorem evalL_comp_perHom (f : CuspForm (GammaH M H) 2) :
    (evalL M H f).comp (perHom M H) = periodMapOf (GammaH M H) f := by
  ext a
  show periodOf (GammaH M H) (Additive.toMul a) f = periodMapOf (GammaH M H) f a
  rw [← periodMapOf_apply_eq_periodOf]
  rfl

theorem periodMapOf_heckeTLinH {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (f : CuspForm (GammaH M H) 2) :
    periodMapOf (GammaH M H) (CuspForm.heckeTLinH 2 hℓ hℓM f) =
      (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩; heckeT M H ℓ ℂ (periodMapOf (GammaH M H) f)) :=
  periodMapOf_gammaH_eq_heckeT_of_coe_eq_heckeU_add_slash M H hℓ hℓM
    (CuspForm.gammaLift M (CuspForm.unitOfPrimeNotDvd hℓ hℓM)) (CuspForm.gammaLift_apply_11 hℓ hℓM) f _
    (CuspForm.coe_heckeTLinH_apply 2 hℓ hℓM (CuspForm.stableT M H 2 hℓ hℓM) f)

theorem dualMap_heckeTLinH_periodOf {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (δ : ↥(GammaH M H)) :
    (CuspForm.heckeTLinH 2 hℓ hℓM).dualMap (periodOf (GammaH M H) δ) =
      (((haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩; heckeT M H ℓ ↥(Lat M H) (perHom M H)) (Additive.ofMul δ) : ↥(Lat M H)) :
        Module.Dual ℂ (CuspForm (GammaH M H) 2)) := by
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  refine LinearMap.ext fun f => ?_
  rw [LinearMap.dualMap_apply, ← periodMapOf_apply_eq_periodOf, periodMapOf_heckeTLinH,
    ← evalL_comp_perHom, heckeT_comp]
  rfl

theorem dualMap_mem_of_forall {T : CuspForm (GammaH M H) 2 →ₗ[ℂ] CuspForm (GammaH M H) 2}
    (hT : ∀ δ : ↥(GammaH M H), T.dualMap (periodOf (GammaH M H) δ) ∈ Lat M H) :
    ∀ v ∈ Lat M H, T.dualMap v ∈ Lat M H := by
  intro v hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨δ, rfl⟩ := hx
    exact hT δ
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul n x _ hx => rw [map_zsmul]; exact Submodule.smul_mem _ n hx

theorem dualMap_heckeTLinH_mem {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) :
    ∀ v ∈ Lat M H, (CuspForm.heckeTLinH 2 hℓ hℓM).dualMap v ∈ Lat M H :=
  dualMap_mem_of_forall M H fun δ => by
    rw [dualMap_heckeTLinH_periodOf]
    exact Subtype.mem _

theorem span_perL_eq_top : Submodule.span ℤ (Set.range (perL M H)) = ⊤ := by
  apply Submodule.map_injective_of_injective (Lat M H).injective_subtype
  rw [Submodule.map_span, Submodule.map_subtype_top, ← Set.range_comp]
  rfl

variable {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M)

def TV : Module.Dual ℂ (CuspForm (GammaH M H) 2) →ₗ[ℂ] Module.Dual ℂ (CuspForm (GammaH M H) 2) :=
  (CuspForm.heckeTLinH 2 hℓ hℓM).dualMap

theorem TV_mem : ∀ v ∈ Lat M H, TV M H hℓ hℓM v ∈ Lat M H := dualMap_heckeTLinH_mem M H hℓ hℓM

def TΛ : ↥(Lat M H) →ₗ[ℤ] ↥(Lat M H) :=
  ((TV M H hℓ hℓM).restrictScalars ℤ).restrict (TV_mem M H hℓ hℓM)

theorem coe_TΛ (l : ↥(Lat M H)) :
    ((TΛ M H hℓ hℓM l : ↥(Lat M H)) : Module.Dual ℂ (CuspForm (GammaH M H) 2)) = TV M H hℓ hℓM l := rfl

variable {p : ℕ} [Fact p.Prime]

theorem chi_TΛ_perL (S : Set ℕ) (hℓS : ℓ ∉ S) (ψ : H1 M H ℤ_[p]) (χ : ↥(Lat M H) →ₗ[ℤ] ℤ_[p])
    (hχ : ∀ δ : ↥(GammaH M H), χ (perL M H δ) = ψ (Additive.ofMul δ)) (δ : ↥(GammaH M H)) :
    χ (TΛ M H hℓ hℓM (perL M H δ)) = opFamily M H S ℤ_[p] (.T ℓ hℓ hℓS hℓM) ψ (Additive.ofMul δ) := by
  have hcomp : χ.toAddMonoidHom.comp (perHom M H) = ψ := by
    ext a
    exact hχ (Additive.toMul a)
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  have hval : TΛ M H hℓ hℓM (perL M H δ) = heckeT M H ℓ ↥(Lat M H) (perHom M H) (Additive.ofMul δ) :=
    Subtype.ext (dualMap_heckeTLinH_periodOf M H hℓ hℓM δ)
  rw [hval]
  show χ.toAddMonoidHom (heckeT M H ℓ ↥(Lat M H) (perHom M H) (Additive.ofMul δ)) = _
  rw [← AddMonoidHom.comp_apply, ← heckeT_comp, hcomp]
  rfl

def psiOf (χ : ↥(Lat M H) →ₗ[ℤ] ℤ_[p]) : H1 M H ℤ_[p] := χ.toAddMonoidHom.comp (perHom M H)

theorem psiOf_apply (χ : ↥(Lat M H) →ₗ[ℤ] ℤ_[p]) (δ : ↥(GammaH M H)) :
    psiOf M H χ (Additive.ofMul δ) = χ (perL M H δ) := rfl

theorem psiOf_mem (χ : ↥(Lat M H) →ₗ[ℤ] ℤ_[p]) :
    psiOf M H χ ∈ Period.parabolicHoms ℤ_[p] (GammaH M H) ℤ_[p] := by
  rw [Period.mem_parabolicHoms_iff]
  intro γ hγ
  rw [psiOf_apply]
  have : perL M H γ = 0 := Subtype.ext (periodOf_eq_zero_of_trace_sq M H γ hγ)
  rw [this, map_zero]

end PeriodSide

section Transport

p2m_open "CohCarrier ModularCurve~baseChangeHom"

variable (N : ℕ) [NeZero N] (H : Subgroup (ZMod N)ˣ) (p : ℕ) [Fact p.Prime]
variable {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (S : Set ℕ) (hℓS : ℓ ∉ S)

theorem liftBaseChange_comp_baseChange {R A M P : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module R M] [AddCommGroup P] [Module R P] [Module A P] [IsScalarTower R A P]
    (χ : M →ₗ[R] P) (T : M →ₗ[R] M) (y : A ⊗[R] M) :
    (χ ∘ₗ T).liftBaseChange A y = χ.liftBaseChange A (T.baseChange A y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a l => simp only [LinearMap.baseChange_tmul, LinearMap.liftBaseChange_tmul, LinearMap.comp_apply]
  | add y z hy hz => simp only [map_add, hy, hz]

theorem exists_equiv_intertwining (hin : HeckeDiamondInputsHAll N H) :
    ∃ e : TateModule p (JH N H) ≃ₗ[ℤ_[p]] ℤ_[p] ⊗[ℤ] ↥(Lat N H),
      ∀ x : TateModule p (JH N H),
        e (tateGenOpH N H S p (.T ℓ hℓ hℓS hℓN) x) = (TΛ N H hℓ hℓN).baseChange ℤ_[p] (e x) := by
  classical
  obtain ⟨e, he⟩ :=
    ModularCurve.exists_heckeEquivariant_linearEquiv_tateModule_jH_padicInt_tensor_periodLatticeOf N p H S hin
  obtain ⟨n, b, -, -⟩ :=
    ModularCurve.exists_basis_periodLatticeOf_linearIndependent_real_span_eq_top_of_isCongruenceSubgroup
      (GammaH N H) (isCongruenceSubgroup_gammaH N H)
  refine ⟨e, fun x => ?_⟩
  set B := Algebra.TensorProduct.basis ℤ_[p] b with hB

  let χ : Fin n → (↥(Lat N H) →ₗ[ℤ] ℤ_[p]) := fun i => (Algebra.linearMap ℤ ℤ_[p]) ∘ₗ b.coord i
  have hcoord : ∀ (i : Fin n) (y : ℤ_[p] ⊗[ℤ] ↥(Lat N H)), B.coord i y = (χ i).liftBaseChange ℤ_[p] y := by
    intro i y
    induction y using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul a l =>
      rw [LinearMap.liftBaseChange_tmul]
      simp only [Module.Basis.coord_apply, χ, LinearMap.comp_apply, Algebra.linearMap_apply, hB,
        Algebra.TensorProduct.basis_repr_tmul, Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul]
    | add y z hy hz => simp only [map_add, hy, hz]
  refine B.ext_elem fun i => ?_
  rw [← Module.Basis.coord_apply, ← Module.Basis.coord_apply, hcoord, hcoord]
  have key := he (.T ℓ hℓ hℓS hℓN) (psiOf N H (χ i)) (psiOf_mem N H (χ i)) (χ i) (χ i ∘ₗ TΛ N H hℓ hℓN)
    (fun δ => rfl) (fun δ => chi_TΛ_perL N H hℓ hℓN S hℓS (psiOf N H (χ i)) (χ i) (fun _ => rfl) δ) x
  exact key.symm.trans (liftBaseChange_comp_baseChange _ _ _)

theorem baseChangeHom_eq {R A M : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module R M] (f : Module.End R M) :
    Module.End.baseChangeHom R A M f = f.baseChange A := rfl

theorem aeval_charpoly_eq_zero_of_intertwine {R A X L : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup X] [Module A X] [Module R X] [SMulCommClass A R X] [IsScalarTower R A X]
    [AddCommGroup L] [Module R L] [Module.Free R L] [Module.Finite R L]
    (T : Module.End A X) (TL : L →ₗ[R] L) (e : X ≃ₗ[A] A ⊗[R] L)
    (he : ∀ x, e (T x) = TL.baseChange A (e x)) :
    Polynomial.aeval T TL.charpoly = 0 := by
  have hT : T = e.symm.conjAlgEquiv R (Module.End.baseChangeHom R A L TL) := by
    refine LinearMap.ext fun x => ?_
    rw [LinearEquiv.conjAlgEquiv_apply, baseChangeHom_eq, LinearMap.comp_apply, LinearMap.comp_apply,
      LinearEquiv.coe_coe, LinearEquiv.coe_coe, LinearEquiv.symm_symm, ← he, LinearEquiv.symm_apply_apply]
  rw [hT, Polynomial.aeval_algHom_apply, Polynomial.aeval_algHom_apply, LinearMap.aeval_self_charpoly, map_zero,
    map_zero]

theorem aeval_tateGenOpH_charpoly (hin : HeckeDiamondInputsHAll N H)
    [Module.Free ℤ ↥(Lat N H)] [Module.Finite ℤ ↥(Lat N H)] :
    Polynomial.aeval (tateGenOpH N H S p (.T ℓ hℓ hℓS hℓN)) (TΛ N H hℓ hℓN).charpoly = 0 := by
  obtain ⟨e, he⟩ := exists_equiv_intertwining N H p hℓ hℓN S hℓS hin
  exact aeval_charpoly_eq_zero_of_intertwine _ _ e he

end Transport

section Spectral

variable {W : Type*} [AddCommGroup W] [Module ℂ W]

def comb {n : ℕ} (u : Fin n → W) : (Fin n → ℂ) →ₗ[ℂ] W := Fintype.linearCombination ℂ u

theorem comb_apply {n : ℕ} (u : Fin n → W) (c : Fin n → ℂ) : comb u c = ∑ i, c i • u i :=
  Fintype.linearCombination_apply ℂ u c

theorem apply_comb_eq {n : ℕ} (u : Fin n → W) (T : W →ₗ[ℂ] W) (A : Matrix (Fin n) (Fin n) ℤ)
    (hT : ∀ j, T (u j) = ∑ i, ((A i j : ℤ) : ℂ) • u i) (c : Fin n → ℂ) :
    T (comb u c) = comb u ((A.map (Int.castRingHom ℂ)).mulVec c) := by
  rw [comb_apply, comb_apply, map_sum]
  simp_rw [map_smul, hT, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_smul]
  congr 1
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, eq_intCast]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem mulVec_conj {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (c : Fin n → ℂ) :
    (A.map (Int.castRingHom ℂ)).mulVec (fun j => conj (c j)) =
      fun i => conj ((A.map (Int.castRingHom ℂ)).mulVec c i) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, eq_intCast, map_sum, map_mul, map_intCast]

theorem comb_ne_zero_or {n : ℕ} (u : Fin n → W) (hli : LinearIndependent ℝ u) (c : Fin n → ℂ) (hc : c ≠ 0) :
    comb u c ≠ 0 ∨ comb u (fun j => conj (c j)) ≠ 0 := by
  by_contra h
  push Not at h
  obtain ⟨h1, h2⟩ := h
  apply hc
  have hre : ∀ i, 2 * (c i).re = 0 := by
    have hsum : ∑ i, (2 * (c i).re) • u i = 0 := by
      have : comb u c + comb u (fun j => conj (c j)) = 0 := by rw [h1, h2, add_zero]
      rw [comb_apply, comb_apply, ← Finset.sum_add_distrib] at this
      simp_rw [← add_smul, Complex.add_conj, Complex.coe_smul] at this
      exact this
    exact Fintype.linearIndependent_iff.mp hli _ hsum
  have him : ∀ i, 2 * (c i).im = 0 := by
    have hsum : Complex.I • ∑ i, (2 * (c i).im) • u i = 0 := by
      have : comb u c - comb u (fun j => conj (c j)) = 0 := by rw [h1, h2, sub_zero]
      rw [comb_apply, comb_apply, ← Finset.sum_sub_distrib] at this
      simp_rw [← sub_smul, Complex.sub_conj] at this
      rw [Finset.smul_sum]
      simp_rw [← Complex.coe_smul, smul_smul, mul_comm Complex.I]
      exact this
    rw [smul_eq_zero] at hsum
    exact Fintype.linearIndependent_iff.mp hli _ (hsum.resolve_left Complex.I_ne_zero)
  funext i
  apply Complex.ext
  · simpa using hre i
  · simpa using him i

variable (Λ : Submodule ℤ W) {n : ℕ} (b : Module.Basis (Fin n) ℤ Λ)
  (TV : W →ₗ[ℂ] W) (hst : ∀ v ∈ Λ, TV v ∈ Λ)

theorem exists_eigen_of_aeval_charpoly_restrict_eq_zero [Module.Free ℤ Λ] [Module.Finite ℤ Λ]
    (hli : LinearIndependent ℝ (fun i => ((b i : Λ) : W)))
    (z : ℂ) (hz : Polynomial.aeval z ((TV.restrictScalars ℤ).restrict hst).charpoly = 0) :
    ∃ μ : ℂ, (μ = z ∨ μ = conj z) ∧ ∃ w : W, w ≠ 0 ∧ TV w = μ • w := by
  classical
  set TΛ : Λ →ₗ[ℤ] Λ := (TV.restrictScalars ℤ).restrict hst with hTΛ
  set A : Matrix (Fin n) (Fin n) ℤ := LinearMap.toMatrix b b TΛ with hA
  set u : Fin n → W := fun i => ((b i : Λ) : W) with hu

  have hTu : ∀ j, TV (u j) = ∑ i, ((A i j : ℤ) : ℂ) • u i := by
    intro j
    have h1 : TΛ (b j) = ∑ i, A i j • b i := by
      rw [hA, ← Matrix.toLin_self b b (LinearMap.toMatrix b b TΛ) j, Matrix.toLin_toMatrix]
    have h2 : ((TΛ (b j) : Λ) : W) = TV (u j) := rfl
    rw [← h2, h1, Submodule.coe_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Submodule.coe_smul_of_tower, Int.cast_smul_eq_zsmul]

  have hdet : (Matrix.scalar (Fin n) z - A.map (Int.castRingHom ℂ)).det = 0 := by
    rw [← Matrix.eval_charpoly, Matrix.charpoly_map, Polynomial.eval_map, hA, LinearMap.charpoly_toMatrix,
      ← algebraMap_int_eq, ← Polynomial.aeval_def, hz]
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hAv : (A.map (Int.castRingHom ℂ)).mulVec v = z • v := by
    rw [Matrix.sub_mulVec, sub_eq_zero] at hv
    rw [← hv]
    ext i
    simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]

  have hw : TV (comb u v) = z • comb u v := by
    rw [apply_comb_eq u TV A hTu, hAv, map_smul]
  have hw' : TV (comb u fun j => conj (v j)) = conj z • comb u fun j => conj (v j) := by
    rw [apply_comb_eq u TV A hTu, mulVec_conj, ← map_smul]
    congr 1
    funext i
    rw [hAv, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, map_mul]
  rcases comb_ne_zero_or u hli v hv0 with h | h
  · exact ⟨z, Or.inl rfl, _, h, hw⟩
  · exact ⟨conj z, Or.inr rfl, _, h, hw'⟩

theorem exists_eigenvector_of_dualMap {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (T : V →ₗ[ℂ] V) (μ : ℂ) (φ : Module.Dual ℂ V) (hφ : φ ≠ 0) (h : T.dualMap φ = μ • φ) :
    ∃ f : V, f ≠ 0 ∧ T f = μ • f := by
  by_contra hne
  push Not at hne
  have hinj : Function.Injective (T - μ • (LinearMap.id : V →ₗ[ℂ] V)) := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro f hf
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] at hf
    by_contra hf0
    exact hne f hf0 hf
  have hsurj : Function.Surjective (T - μ • (LinearMap.id : V →ₗ[ℂ] V)) := LinearMap.injective_iff_surjective.mp hinj
  apply hφ
  refine LinearMap.ext fun g => ?_
  obtain ⟨f, rfl⟩ := hsurj g
  have := LinearMap.congr_fun h f
  rw [LinearMap.dualMap_apply, LinearMap.smul_apply] at this
  rw [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, map_sub, map_smul, this, LinearMap.zero_apply,
    sub_self]

end Spectral

section HeckeBound

open CongruenceSubgroup

variable (N : ℕ) [NeZero N] (H : Subgroup (ZMod N)ˣ) (k : ℤ)

local notation "Γ₁ℝ" M => ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))
local notation "Γₕℝ" M ";" K => ((CohCarrier.GammaH M K : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

theorem one_mem_strictPeriods_gamma1 : (1 : ℝ) ∈ (Γ₁ℝ N).strictPeriods := by
  rw [CongruenceSubgroup.strictPeriods_Gamma1]; exact AddSubgroup.mem_zmultiples _

theorem gamma1GL_le_gammaHGL : (Γ₁ℝ N) ≤ (Γₕℝ N ; H) :=
  Subgroup.map_mono (ModularCurve.Gamma1_le_GammaH N H)

def resG1 (f : CuspForm (Γₕℝ N ; H) k) : CuspForm (Γ₁ℝ N) k where
  toFun := f
  slash_action_eq' γ hγ := SlashInvariantFormClass.slash_action_eq f γ (gamma1GL_le_gammaHGL N H hγ)
  holo' := CuspFormClass.holo f
  zero_at_cusps' hc := CuspFormClass.zero_at_cusps f (hc.mono (gamma1GL_le_gammaHGL N H))

@[scoped simp] theorem coe_resG1 (f : CuspForm (Γₕℝ N ; H) k) : ⇑(resG1 N H k f) = ⇑f := rfl

def resLin : CuspForm (Γₕℝ N ; H) k →ₗ[ℂ] CuspForm (Γ₁ℝ N) k where
  toFun := resG1 N H k
  map_add' f g := DFunLike.coe_injective rfl
  map_smul' c f := DFunLike.coe_injective rfl

theorem resLin_injective : Function.Injective (resLin N H k) := by
  intro f g h
  apply DFunLike.coe_injective
  have h1 : (⇑(resLin N H k f) : UpperHalfPlane → ℂ) = ⇑(resLin N H k g) := by rw [h]
  exact h1

theorem finiteDimensional_gammaH : FiniteDimensional ℂ (CuspForm (Γₕℝ N ; H) k) := by
  obtain ⟨n, b, -⟩ := CuspForm.exists_basis_hasNebentypus_qCoeff_hecke_eigen N k
  haveI : FiniteDimensional ℂ (CuspForm (Γ₁ℝ N) k) := Module.Finite.of_basis b
  exact FiniteDimensional.of_injective (resLin N H k) (resLin_injective N H k)

def qCoeffLin (m : ℕ) : CuspForm (Γ₁ℝ N) k →ₗ[ℂ] ℂ where
  toFun f := ModularFormClass.qCoeff f m
  map_add' f g := by
    change (UpperHalfPlane.qExpansion 1 (⇑(f + g))).coeff m = (UpperHalfPlane.qExpansion 1 ⇑f).coeff m + (UpperHalfPlane.qExpansion 1 ⇑g).coeff m
    rw [CuspForm.coe_add, ModularForm.qExpansion_add one_pos (one_mem_strictPeriods_gamma1 N) f g, map_add]
  map_smul' a f := by
    change (UpperHalfPlane.qExpansion 1 (⇑(a • f))).coeff m = a * (UpperHalfPlane.qExpansion 1 ⇑f).coeff m
    rw [CuspForm.IsGLPos.coe_smul, ModularForm.qExpansion_smul one_pos (one_mem_strictPeriods_gamma1 N) a f,
      map_smul, smul_eq_mul]

@[scoped simp] theorem qCoeffLin_apply (m : ℕ) (f : CuspForm (Γ₁ℝ N) k) :
    qCoeffLin N k m f = ModularFormClass.qCoeff f m := rfl

def coeLin : CuspForm (Γ₁ℝ N) k →ₗ[ℂ] (UpperHalfPlane → ℂ) where
  toFun f := ⇑f
  map_add' f g := CuspForm.coe_add f g
  map_smul' c f := FunLike.coe_smul c f

@[scoped simp] theorem coeLin_apply (f : CuspForm (Γ₁ℝ N) k) : coeLin N k f = ⇑f := rfl

variable {N k}

theorem slash_eq_smul_of_hasNebentypus {ε : DirichletCharacter ℂ N} {g : CuspForm (Γ₁ℝ N) k}
    (hg : CuspForm.HasNebentypus ε g) (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 N) :
    (⇑g : UpperHalfPlane → ℂ) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) =
      ε ((γ 1 1 : ℤ) : ZMod N) • ⇑g := by
  funext τ
  have hpt := hg γ hγ τ
  have e0 : (⇑g : UpperHalfPlane → ℂ) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) = ⇑g ∣[k] γ := rfl
  rw [e0, ModularForm.SL_slash_apply, Pi.smul_apply, smul_eq_mul]
  have hden : UpperHalfPlane.denom (Matrix.SpecialLinearGroup.toGL
      ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) γ)) (τ : ℂ)
      = ((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ) := by
    simp [UpperHalfPlane.denom]
  rw [hden]
  have hne : ((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ) ≠ 0 := by
    rw [← hden]; exact UpperHalfPlane.denom_ne_zero _ τ
  rw [hpt, zpow_neg]
  field_simp

theorem sum_slash {α : Type*} (s : Finset α) (F : α → UpperHalfPlane → ℂ) (k : ℤ) (A : GL (Fin 2) ℝ) :
    (∑ a ∈ s, F a) ∣[k] A = ∑ a ∈ s, F a ∣[k] A := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [SlashAction.zero_slash]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, SlashAction.add_slash, ih]

theorem smul_slash_mapGL (F : UpperHalfPlane → ℂ) (γ : SL(2, ℤ)) (a : ℂ) (k : ℤ) :
    (a • F) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) =
      a • F ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) :=
  ModularForm.SL_smul_slash k γ F a

variable (N k)

theorem norm_sq_lt_of_heckeTLinH_eq_smul {p : ℕ} (hp : p.Prime) (hpN : ¬ p ∣ N)
    (f : CuspForm (Γₕℝ N ; H) k) (hf : f ≠ 0) (μ : ℂ)
    (hμ : CuspForm.heckeTLinH k hp hpN f = μ • f) :
    ‖μ‖ ^ 2 < ((p : ℝ) + 1) ^ 2 * (p : ℝ) ^ (k - 2) := by
  classical

  obtain ⟨n, b, hb⟩ := CuspForm.exists_basis_hasNebentypus_qCoeff_hecke_eigen N k
  choose ε hε hlam using hb
  choose lam hlam using fun i => hlam i p hp hpN

  set g : CuspForm (Γ₁ℝ N) k := resG1 N H k f with hg
  set c : Fin n → ℂ := fun i => b.repr g i with hc
  have hgsum : g = ∑ i, c i • b i := (b.sum_repr g).symm
  have hcoeg : (⇑f : UpperHalfPlane → ℂ) = ∑ i, c i • ⇑(b i) := by
    rw [← coe_resG1 N H k f, ← hg, hgsum, ← coeLin_apply, map_sum]
    simp only [map_smul, coeLin_apply]

  have hqf : ∀ m, ModularFormClass.qCoeff (⇑f) m = ∑ i, c i * ModularFormClass.qCoeff (⇑(b i)) m := by
    intro m
    rw [← coe_resG1 N H k f, ← hg, ← qCoeffLin_apply, hgsum, map_sum]
    simp only [map_smul, qCoeffLin_apply, smul_eq_mul]

  set σ : Gamma0 N := CuspForm.gammaLift N (CuspForm.unitOfPrimeNotDvd hp hpN) with hσ
  set D : CuspForm (Γ₁ℝ N) k := ∑ i, (c i * ε i (p : ZMod N)) • b i with hD
  have hcoeD : ⇑(CuspForm.diamondLinH k (CuspForm.unitOfPrimeNotDvd hp hpN) f) = ⇑D := by
    rw [CuspForm.coe_diamondLinH_apply k (CuspForm.stableD N H k), hcoeg, sum_slash, hD, ← coeLin_apply, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, coeLin_apply, smul_slash_mapGL,
      slash_eq_smul_of_hasNebentypus (hε i) (σ : SL(2, ℤ)) σ.2, smul_smul]
    congr 1
    rw [hσ, CuspForm.gammaLift_apply_11 hp hpN]
  have hqD : ∀ m, ModularFormClass.qCoeff (⇑(CuspForm.diamondLinH k (CuspForm.unitOfPrimeNotDvd hp hpN) f)) m =
      ∑ i, c i * ε i (p : ZMod N) * ModularFormClass.qCoeff (⇑(b i)) m := by
    intro m
    rw [hcoeD, ← qCoeffLin_apply, hD, map_sum]
    simp only [map_smul, qCoeffLin_apply, smul_eq_mul]

  have hqT : ∀ m, ModularFormClass.qCoeff (⇑(CuspForm.heckeTLinH k hp hpN f)) m =
      μ * ∑ i, c i * ModularFormClass.qCoeff (⇑(b i)) m := by
    intro m
    have : (⇑(CuspForm.heckeTLinH k hp hpN f) : UpperHalfPlane → ℂ) = ⇑(μ • g) := by
      rw [hμ, CuspForm.IsGLPos.coe_smul, CuspForm.IsGLPos.coe_smul, hg, coe_resG1]
    rw [this, ← qCoeffLin_apply, map_smul, smul_eq_mul, qCoeffLin_apply, hg, coe_resG1, hqf]

  have key : ∀ m, ∑ i, (c i * (lam i - μ)) * ModularFormClass.qCoeff (⇑(b i)) m = 0 := by
    intro m
    have h1 := CuspForm.qCoeff_heckeTLinH_eq_qCoeff_mul_add_pow_mul_qCoeff_diamondLinH N H k hp hpN f m
    rw [hqT, hqf] at h1
    have h2 : ∀ i, ModularFormClass.qCoeff (⇑(b i)) (p * m) +
        ε i (p : ZMod N) * (p : ℂ) ^ (k - 1) *
          (if p ∣ m then ModularFormClass.qCoeff (⇑(b i)) (m / p) else 0) =
        lam i * ModularFormClass.qCoeff (⇑(b i)) m := fun i => hlam i m
    have h3 : ∑ i, c i * (lam i * ModularFormClass.qCoeff (⇑(b i)) m) =
        μ * ∑ i, c i * ModularFormClass.qCoeff (⇑(b i)) m := by
      simp_rw [← h2]
      rw [h1]
      split_ifs with hpm
      · rw [hqD]
        simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum, mul_comm m p]
        congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
      · simp only [mul_zero, add_zero, mul_comm m p]
    have h4 : ∑ i, (c i * (lam i - μ)) * ModularFormClass.qCoeff (⇑(b i)) m =
        ∑ i, c i * (lam i * ModularFormClass.qCoeff (⇑(b i)) m) - μ * ∑ i, c i * ModularFormClass.qCoeff (⇑(b i)) m := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [h4, h3, sub_self]

  have hlin : ∑ i, (c i * (lam i - μ)) • b i = 0 := by
    refine ModularFormClass.eq_of_forall_qCoeff_eq (one_mem_strictPeriods_gamma1 N) fun m => ?_
    rw [← qCoeffLin_apply, map_sum, ← qCoeffLin_apply, map_zero]
    simp only [map_smul, qCoeffLin_apply, smul_eq_mul]
    exact key m
  have hci : ∀ i, c i * (lam i - μ) = 0 := Fintype.linearIndependent_iff.mp b.linearIndependent _ hlin

  have hg0 : g ≠ 0 := by
    intro h0
    apply hf
    apply DFunLike.coe_injective
    have h1 : (⇑g : UpperHalfPlane → ℂ) = 0 := by rw [h0]; rfl
    rw [hg, coe_resG1] at h1
    show (⇑f : UpperHalfPlane → ℂ) = ⇑(0 : CuspForm (Γₕℝ N ; H) k)
    rw [CuspForm.coe_zero]
    exact h1
  obtain ⟨i, hi⟩ : ∃ i, c i ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hg0
    rw [hgsum]
    exact Finset.sum_eq_zero fun i _ => by rw [hall i, zero_smul]
  have hμi : μ = lam i := by
    have := hci i
    rw [mul_eq_zero, sub_eq_zero] at this
    exact (this.resolve_left hi).symm
  rw [hμi]
  exact CuspForm.norm_sq_lt_of_hasNebentypus_qCoeff_hecke_eigen N k (ε i) (b i) (b.ne_zero i) (hε i) hp hpN
    (lam i) (hlam i)

end HeckeBound

section Assembly

p2m_open "CohCarrier ModularCurve~baseChangeHom"

theorem mainThm (N p : ℕ) [NeZero N] [Fact p.Prime] (hpN : ¬ p ∣ N) (H : Subgroup (ZMod N)ˣ)
    (S : Set ℕ) (hpS : p ∉ S) (hin : ModularCurve.HeckeDiamondInputsHAll N H) :
    ∃ P : Polynomial ℤ, P.Monic ∧
      Polynomial.aeval (ModularCurve.tateGenOpH N H S p (.T p Fact.out hpS hpN)) P = 0 ∧
      ∀ z : ℂ, Polynomial.aeval z P = 0 → ‖z‖ < (p + 1 : ℕ) := by
  classical
  have hp : p.Prime := Fact.out

  obtain ⟨n, b, hli, -⟩ :=
    ModularCurve.exists_basis_periodLatticeOf_linearIndependent_real_span_eq_top_of_isCongruenceSubgroup
      (GammaH N H) (isCongruenceSubgroup_gammaH N H)
  haveI : Module.Free ℤ ↥(Lat N H) := Module.Free.of_basis b
  haveI : Module.Finite ℤ ↥(Lat N H) := Module.Finite.of_basis b
  refine ⟨(TΛ N H hp hpN).charpoly, LinearMap.charpoly_monic _,
    aeval_tateGenOpH_charpoly N H p hp hpN S hpS hin, fun z hz => ?_⟩

  obtain ⟨μ, hμz, φ, hφ0, hφ⟩ :=
    exists_eigen_of_aeval_charpoly_restrict_eq_zero (Lat N H) b (TV N H hp hpN) (TV_mem N H hp hpN) hli z hz

  haveI := finiteDimensional_gammaH N H 2
  obtain ⟨f, hf0, hf⟩ := exists_eigenvector_of_dualMap (CuspForm.heckeTLinH 2 hp hpN) μ φ hφ0 hφ

  have hbd := norm_sq_lt_of_heckeTLinH_eq_smul N H 2 hp hpN f hf0 μ hf
  have hnorm : ‖z‖ = ‖μ‖ := by
    rcases hμz with rfl | rfl
    · rfl
    · exact (Complex.norm_conj z).symm
  rw [hnorm, Nat.cast_add, Nat.cast_one]
  rw [sub_self, zpow_zero, mul_one] at hbd
  exact lt_of_pow_lt_pow_left₀ 2 (by positivity) hbd

end Assembly

end SpecTpRed
p2m_reactivate "P2MW.S_ModularCurve_exists_monic_aeval_tateGenOpH_T_eq_zero_forall_norm_root_lt.SpecTpRed"

end
p2m_reactivate "P2MW.S_ModularCurve_exists_monic_aeval_tateGenOpH_T_eq_zero_forall_norm_root_lt.SpecTpRed"

theorem solution
    (N p : ℕ) [NeZero N] [Fact p.Prime] (hpN : ¬ p ∣ N) (H : Subgroup (ZMod N)ˣ)
    (S : Set ℕ) (hpS : p ∉ S)
    (hin : ModularCurve.HeckeDiamondInputsHAll N H) :
    ∃ P : Polynomial ℤ, P.Monic ∧
      Polynomial.aeval (ModularCurve.tateGenOpH N H S p (.T p Fact.out hpS hpN)) P = 0 ∧
      ∀ z : ℂ, Polynomial.aeval z P = 0 → ‖z‖ < (p + 1 : ℕ) :=
  SpecTpRed.mainThm N p hpN H S hpS hin

end S_ModularCurve_exists_monic_aeval_tateGenOpH_T_eq_zero_forall_norm_root_lt
end P2MW
export P2MW.S_ModularCurve_exists_monic_aeval_tateGenOpH_T_eq_zero_forall_norm_root_lt (solution)
