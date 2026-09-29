-- Prove2me | solution 1 for ModularCurve.FullLevel.exists_injective_cuspForm_dual_baseChange_tateModule_jacComp_comm
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/707a40f7-4195-580f-9d5d-a1bda7227844

import Mathlib
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_PeriodOf
import Definitions.Def_CuspForm_HeckeOperatorFormsGammaH
import Theorems.Thm_ModularCurve_exists_linearEquiv_tateModule_jH_padicInt_tensor_periodLatticeOf_levelAut
import Theorems.Thm_ModularCurve_periodMapOf_gammaH_eq_comp_of_coe_eq_slash
import Theorems.Thm_ModularCurve_periodMapOf_gammaH_eq_heckeT_of_coe_eq_heckeU_add_slash
import Theorems.Thm_ModularCurve_periodMapOf_gammaH_eq_diamondRaw_of_coe_eq_slash
import Theorems.Thm_CuspForm_stableT
import Theorems.Thm_CuspForm_stableD
import Theorems.Thm_ModularCurve_exists_basis_periodLatticeOf_linearIndependent_real_span_eq_top_of_isCongruenceSubgroup
import Theorems.Thm_ModularCurve_periodMapOf_apply_eq_periodOf
import Theorems.Thm_ModularCurve_periodMapOf_mem_parabolicHoms
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_exists_injective_cuspForm_dual_baseChange_tateModule_jacComp_comm
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z"
p2m_attr_erase "instance" "ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0 HeckeEis.instFiniteIndexHeckeUpper FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par"
p2m_attr_erase "simp" "ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.ComplexPlaceDictionaryOf.pt_ofGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.injEq ModularCurve.ComplexPlaceDictionaryOf.pt_toGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.sizeOf_spec ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec CohCarrier.jConjGammaH_jConjGammaH CohCarrier.coe_jConjGammaH CohCarrier.charInvolution_apply ModularCurve.Period.jConjMat_apply_zero_one ModularCurve.Period.jConjSL_coe ModularCurve.Period.jConjMat_apply_one_zero ModularCurve.Period.jConjMat_apply_one_one ModularCurve.Period.jConjGamma0_coe ModularCurve.Period.charInvolution_apply ModularCurve.Period.jConjMat_apply_zero_zero ModularCurve.qExpandAlgHomC_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply"
p2m_attr_erase "simp" "ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁"
p2m_attr_erase "simp" "PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero"
p2m_attr_erase "simp" "ModularCurve.LevelN.coe_jGen FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero HeckeEis.coeffCoboundaryMap_apply"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

noncomputable section

open scoped TensorProduct MatrixGroups ModularForm

namespace E4aFullLevel

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

omit [NeZero ℓ] in

theorem diamondRaw_comp (σ : CongruenceSubgroup.Gamma0 M) (h : A →+ B) (φ : H1 M H A) :
    diamondRaw M H B σ (h.comp φ) = h.comp (diamondRaw M H A σ φ) :=
  AddMonoidHom.ext fun _ => rfl

end Naturality

section PeriodSide

open CohCarrier ModularCurve

variable (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)

theorem isCongruenceSubgroup_gammaH : CongruenceSubgroup.IsCongruenceSubgroup (GammaH M H) :=
  CongruenceSubgroup.isCongruenceSubgroup_trans _ _ (ModularCurve.Gamma1_le_GammaH M H)
    (CongruenceSubgroup.Gamma1_is_congruence M)

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

theorem periodOf_eq_zero_of_trace_sq (δ : ↥(GammaH M H))
    (hδ : ((δ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 = 4) :
    periodOf (GammaH M H) δ = 0 := by
  refine LinearMap.ext fun f => ?_
  rw [← periodMapOf_apply_eq_periodOf, LinearMap.zero_apply]
  exact periodMapOf_mem_parabolicHoms (GammaH M H) f δ hδ

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

theorem periodMapOf_diamondLinH (d : (ZMod M)ˣ) (f : CuspForm (GammaH M H) 2) :
    periodMapOf (GammaH M H) (CuspForm.diamondLinH 2 d f) =
      diamondRaw M H ℂ (CuspForm.gammaLift M d) (periodMapOf (GammaH M H) f) :=
  periodMapOf_gammaH_eq_diamondRaw_of_coe_eq_slash M H (CuspForm.gammaLift M d) f _
    (CuspForm.coe_diamondLinH_apply 2 (CuspForm.stableD M H 2) d f)

theorem dualMap_heckeTLinH_periodOf {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (δ : ↥(GammaH M H)) :
    (CuspForm.heckeTLinH 2 hℓ hℓM).dualMap (periodOf (GammaH M H) δ) =
      (((haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩; heckeT M H ℓ ↥(Lat M H) (perHom M H)) (Additive.ofMul δ) : ↥(Lat M H)) :
        Module.Dual ℂ (CuspForm (GammaH M H) 2)) := by
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  refine LinearMap.ext fun f => ?_
  rw [LinearMap.dualMap_apply, ← periodMapOf_apply_eq_periodOf, periodMapOf_heckeTLinH,
    ← evalL_comp_perHom, heckeT_comp]
  rfl

theorem dualMap_diamondLinH_periodOf (d : (ZMod M)ˣ) (δ : ↥(GammaH M H)) :
    (CuspForm.diamondLinH 2 d).dualMap (periodOf (GammaH M H) δ) =
      ((diamondRaw M H ↥(Lat M H) (CuspForm.gammaLift M d) (perHom M H) (Additive.ofMul δ) : ↥(Lat M H)) :
        Module.Dual ℂ (CuspForm (GammaH M H) 2)) := by
  refine LinearMap.ext fun f => ?_
  rw [LinearMap.dualMap_apply, ← periodMapOf_apply_eq_periodOf, periodMapOf_diamondLinH,
    ← evalL_comp_perHom, diamondRaw_comp]
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

theorem dualMap_diamondLinH_mem (d : (ZMod M)ˣ) :
    ∀ v ∈ Lat M H, (CuspForm.diamondLinH (H := H) 2 d).dualMap v ∈ Lat M H :=
  dualMap_mem_of_forall M H fun δ => by
    rw [dualMap_diamondLinH_periodOf]
    exact Subtype.mem _

theorem span_perL_eq_top : Submodule.span ℤ (Set.range (perL M H)) = ⊤ := by
  apply Submodule.map_injective_of_injective (Lat M H).injective_subtype
  rw [Submodule.map_span, Submodule.map_subtype_top, ← Set.range_comp]
  rfl

def TΛT {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) : ↥(Lat M H) →ₗ[ℤ] ↥(Lat M H) :=
  (((CuspForm.heckeTLinH (H := H) 2 hℓ hℓM).dualMap).restrictScalars ℤ).restrict
    (dualMap_heckeTLinH_mem M H hℓ hℓM)

theorem coe_TΛT {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (l : ↥(Lat M H)) :
    ((TΛT M H hℓ hℓM l : ↥(Lat M H)) : Module.Dual ℂ (CuspForm (GammaH M H) 2)) =
      (CuspForm.heckeTLinH 2 hℓ hℓM).dualMap l := rfl

def TΛD (d : (ZMod M)ˣ) : ↥(Lat M H) →ₗ[ℤ] ↥(Lat M H) :=
  (((CuspForm.diamondLinH (H := H) 2 d).dualMap).restrictScalars ℤ).restrict (dualMap_diamondLinH_mem M H d)

theorem coe_TΛD (d : (ZMod M)ˣ) (l : ↥(Lat M H)) :
    ((TΛD M H d l : ↥(Lat M H)) : Module.Dual ℂ (CuspForm (GammaH M H) 2)) =
      (CuspForm.diamondLinH 2 d).dualMap l := rfl

variable {p : ℕ} [Fact p.Prime]

def psiOf (χ : ↥(Lat M H) →ₗ[ℤ] ℤ_[p]) : H1 M H ℤ_[p] :=
  χ.toAddMonoidHom.comp (perHom M H)

theorem psiOf_apply (χ : ↥(Lat M H) →ₗ[ℤ] ℤ_[p]) (δ : ↥(GammaH M H)) :
    psiOf M H χ (Additive.ofMul δ) = χ (perL M H δ) := rfl

theorem psiOf_mem (χ : ↥(Lat M H) →ₗ[ℤ] ℤ_[p]) :
    psiOf M H χ ∈ ModularCurve.Period.parabolicHoms ℤ_[p] (GammaH M H) ℤ_[p] := by
  intro δ hδ
  have h0 : perL M H δ = 0 := Subtype.ext (periodOf_eq_zero_of_trace_sq M H δ hδ)
  rw [psiOf_apply, h0, map_zero]

theorem chi_TΛT_perL {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (S : Set ℕ) (hℓS : ℓ ∉ S)
    (χ : ↥(Lat M H) →ₗ[ℤ] ℤ_[p]) (δ : ↥(GammaH M H)) :
    (χ ∘ₗ TΛT M H hℓ hℓM) (perL M H δ) =
      opFamily M H S ℤ_[p] (.T ℓ hℓ hℓS hℓM) (psiOf M H χ) (Additive.ofMul δ) := by
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  have hval : TΛT M H hℓ hℓM (perL M H δ) = heckeT M H ℓ ↥(Lat M H) (perHom M H) (Additive.ofMul δ) :=
    Subtype.ext (dualMap_heckeTLinH_periodOf M H hℓ hℓM δ)
  rw [LinearMap.comp_apply, hval]
  show χ.toAddMonoidHom (heckeT M H ℓ ↥(Lat M H) (perHom M H) (Additive.ofMul δ)) = _
  rw [← AddMonoidHom.comp_apply, ← heckeT_comp]
  rfl

theorem chi_TΛD_perL (d : (ZMod M)ˣ) (S : Set ℕ) (χ : ↥(Lat M H) →ₗ[ℤ] ℤ_[p]) (δ : ↥(GammaH M H)) :
    (χ ∘ₗ TΛD M H d) (perL M H δ) =
      opFamily M H S ℤ_[p] (.dia d) (psiOf M H χ) (Additive.ofMul δ) := by
  have hval : TΛD M H d (perL M H δ) =
      diamondRaw M H ↥(Lat M H) (CuspForm.gammaLift M d) (perHom M H) (Additive.ofMul δ) :=
    Subtype.ext (dualMap_diamondLinH_periodOf M H d δ)
  rw [LinearMap.comp_apply, hval]
  show χ.toAddMonoidHom (diamondRaw M H ↥(Lat M H) _ (perHom M H) (Additive.ofMul δ)) = _
  rw [← AddMonoidHom.comp_apply, ← diamondRaw_comp]
  rfl

end PeriodSide

section LevelSide

open CohCarrier ModularCurve ModularCurve.FullLevel CongruenceSubgroup

variable (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M']

theorem val_det_conjElem (γ : SL(2, ℤ)) :
    ((Matrix.GeneralLinearGroup.det (conjElem q γ) : ℝˣ) : ℝ) = 1 := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, conjElem, Matrix.GeneralLinearGroup.val_mkOfDetNeZero,
    Matrix.det_fin_two_of]
  have hq : (q : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
  have hdet : ((γ 0 0 : ℤ) : ℝ) * ((γ 1 1 : ℤ) : ℝ) - ((γ 0 1 : ℤ) : ℝ) * ((γ 1 0 : ℤ) : ℝ) = 1 := by
    have h := Matrix.SpecialLinearGroup.det_coe γ
    rw [Matrix.det_fin_two] at h
    exact_mod_cast h
  have : ((γ 0 0 : ℤ) : ℝ) * ((γ 1 1 : ℤ) : ℝ) - ((γ 0 1 : ℤ) : ℝ) / q * ((q : ℝ) * ((γ 1 0 : ℤ) : ℝ)) =
      ((γ 0 0 : ℤ) : ℝ) * ((γ 1 1 : ℤ) : ℝ) - ((γ 0 1 : ℤ) : ℝ) * ((γ 1 0 : ℤ) : ℝ) := by
    field_simp
  rw [this, hdet]

theorem det_conjElem (γ : SL(2, ℤ)) : Matrix.GeneralLinearGroup.det (conjElem q γ) = 1 :=
  Units.ext (val_det_conjElem q γ)

theorem det_conjElem_inv_pos (γ : SL(2, ℤ)) :
    0 < ((Matrix.GeneralLinearGroup.det (conjElem q γ)⁻¹ : ℝˣ) : ℝ) := by
  rw [map_inv, Units.val_inv_eq_inv_val, val_det_conjElem, inv_one]
  exact one_pos

scoped instance neZero_sq_mul : NeZero (q ^ 2 * M') :=
  ⟨mul_ne_zero (pow_ne_zero 2 (Fact.out : q.Prime).ne_zero) (NeZero.ne M')⟩

theorem mem_GH_iff (A : SL(2, ℤ)) :
    A ∈ GammaH (q ^ 2 * M') (levelH q M') ↔
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

variable {q M'}

theorem qneZ : (q : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
theorem qneR : (q : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero

theorem dvd_entry10 {δ : SL(2, ℤ)} (hδ : δ ∈ GammaH (q ^ 2 * M') (levelH q M')) :
    ((q : ℤ) ^ 2 * M') ∣ (δ 1 0 : ℤ) := by
  obtain ⟨h10, _⟩ := (mem_GH_iff q M' δ).1 hδ
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h10
  push_cast at h10
  exact h10

theorem entry11_mod {δ : SL(2, ℤ)} (hδ : δ ∈ GammaH (q ^ 2 * M') (levelH q M')) :
    ((δ 1 1 : ℤ) : ZMod q) = 1 :=
  ((mem_GH_iff q M' δ).1 hδ).2

theorem entry00_mod {δ : SL(2, ℤ)} (hδ : δ ∈ GammaH (q ^ 2 * M') (levelH q M')) :
    ((δ 0 0 : ℤ) : ZMod q) = 1 := by
  have h11 := entry11_mod hδ
  have hq10 : ((δ 1 0 : ℤ) : ZMod q) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact dvd_trans (Dvd.intro ((q : ℤ) * M') (by ring)) (dvd_entry10 hδ)
  have hdet := Matrix.SpecialLinearGroup.det_coe δ
  rw [Matrix.det_fin_two] at hdet
  have := congrArg (fun z : ℤ => (z : ZMod q)) hdet
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_one, hq10, h11, mul_one, mul_zero, sub_zero] at this
  exact this

theorem dvd_entry00_sub {δ : SL(2, ℤ)} (hδ : δ ∈ GammaH (q ^ 2 * M') (levelH q M')) :
    (q : ℤ) ∣ (δ 0 0 : ℤ) - δ 1 1 := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [entry00_mod hδ, entry11_mod hδ, sub_self]

variable (q M')

def kc (δ : SL(2, ℤ)) : ℤ := (δ 1 0 : ℤ) / ((q : ℤ) ^ 2 * M')

variable {M'} in

def kad (δ : SL(2, ℤ)) : ℤ := ((δ 0 0 : ℤ) - δ 1 1) / q

variable {q M'}

theorem kc_spec {δ : SL(2, ℤ)} (hδ : δ ∈ GammaH (q ^ 2 * M') (levelH q M')) :
    (δ 1 0 : ℤ) = (q : ℤ) ^ 2 * M' * kc q M' δ :=
  (Int.mul_ediv_cancel' (dvd_entry10 hδ)).symm

theorem kad_spec {δ : SL(2, ℤ)} (hδ : δ ∈ GammaH (q ^ 2 * M') (levelH q M')) :
    (δ 0 0 : ℤ) = δ 1 1 + q * kad q δ := by
  have := Int.mul_ediv_cancel' (dvd_entry00_sub hδ)
  rw [kad]
  linear_combination -this

variable (q M')

def conjMat (γ δ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![γ 1 1 * δ 0 0 * γ 0 0 + γ 1 1 * δ 0 1 * q * γ 1 0 - γ 0 1 * γ 0 0 * (q * M' * kc q M' δ) -
        γ 0 1 * δ 1 1 * γ 1 0,
      γ 0 1 * γ 1 1 * kad q δ + δ 0 1 * γ 1 1 ^ 2 - γ 0 1 ^ 2 * (M' * kc q M' δ);
    q * γ 1 0 * γ 0 0 * (δ 1 1 - δ 0 0) - q ^ 2 * γ 1 0 ^ 2 * δ 0 1 + δ 1 0 * γ 0 0 ^ 2,
      -(γ 1 0 * δ 0 0 * γ 0 1) - q * γ 1 0 * δ 0 1 * γ 1 1 + γ 0 0 * γ 0 1 * (q * M' * kc q M' δ) +
        γ 0 0 * δ 1 1 * γ 1 1]

def conjInv (γ : SL(2, ℤ)) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero
    !![((γ 1 1 : ℤ) : ℝ), -(((γ 0 1 : ℤ) : ℝ) / q); -((q : ℝ) * ((γ 1 0 : ℤ) : ℝ)), ((γ 0 0 : ℤ) : ℝ)]
    (by
      have hdet : ((γ 0 0 : ℤ) : ℝ) * ((γ 1 1 : ℤ) : ℝ) - ((γ 0 1 : ℤ) : ℝ) * ((γ 1 0 : ℤ) : ℝ) = 1 := by
        have h := Matrix.SpecialLinearGroup.det_coe γ
        rw [Matrix.det_fin_two] at h
        exact_mod_cast h
      have hq : (q : ℝ) ≠ 0 := qneR
      rw [Matrix.det_fin_two_of]
      have : ((γ 1 1 : ℤ) : ℝ) * ((γ 0 0 : ℤ) : ℝ) - -(((γ 0 1 : ℤ) : ℝ) / q) * -((q : ℝ) * ((γ 1 0 : ℤ) : ℝ)) =
          ((γ 0 0 : ℤ) : ℝ) * ((γ 1 1 : ℤ) : ℝ) - ((γ 0 1 : ℤ) : ℝ) * ((γ 1 0 : ℤ) : ℝ) := by
        field_simp
      rw [this, hdet]
      exact one_ne_zero)

@[scoped simp] theorem conjInv_coe (γ : SL(2, ℤ)) : ((conjInv q γ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
    !![((γ 1 1 : ℤ) : ℝ), -(((γ 0 1 : ℤ) : ℝ) / q); -((q : ℝ) * ((γ 1 0 : ℤ) : ℝ)), ((γ 0 0 : ℤ) : ℝ)] := rfl

@[scoped simp] theorem conjElem_coe (γ : SL(2, ℤ)) : ((conjElem q γ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
    !![((γ 0 0 : ℤ) : ℝ), ((γ 0 1 : ℤ) : ℝ) / q; (q : ℝ) * ((γ 1 0 : ℤ) : ℝ), ((γ 1 1 : ℤ) : ℝ)] := rfl

theorem conjElem_mul_conjInv (γ : SL(2, ℤ)) : conjElem q γ * conjInv q γ = 1 := by
  have hdet : ((γ 0 0 : ℤ) : ℝ) * ((γ 1 1 : ℤ) : ℝ) - ((γ 0 1 : ℤ) : ℝ) * ((γ 1 0 : ℤ) : ℝ) = 1 := by
    have h := Matrix.SpecialLinearGroup.det_coe γ
    rw [Matrix.det_fin_two] at h
    exact_mod_cast h
  have hq : (q : ℝ) ≠ 0 := qneR
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  simp only [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, conjElem_coe, conjInv_coe,
    Units.val_one]
  fin_cases i <;> fin_cases j <;> simp <;> field_simp <;>
    first | ring1 | linear_combination hdet

theorem conjElem_inv_eq (γ : SL(2, ℤ)) : (conjElem q γ)⁻¹ = conjInv q γ :=
  inv_eq_of_mul_eq_one_right (conjElem_mul_conjInv q γ)

theorem conjMat_real (γ : SL(2, ℤ)) {δ : SL(2, ℤ)} (hδ : δ ∈ GammaH (q ^ 2 * M') (levelH q M')) :
    (Int.castRingHom ℝ).mapMatrix (conjMat q M' γ δ) =
      (((conjElem q γ)⁻¹ * (δ : GL (Fin 2) ℝ) * conjElem q γ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) := by
  have hc : ((δ 1 0 : ℤ) : ℝ) = (q : ℝ) ^ 2 * M' * kc q M' δ := by exact_mod_cast kc_spec hδ
  have had : ((δ 0 0 : ℤ) : ℝ) = ((δ 1 1 : ℤ) : ℝ) + q * kad q δ := by exact_mod_cast kad_spec hδ
  have hq : (q : ℝ) ≠ 0 := qneR
  rw [conjElem_inv_eq]
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply,
    Fin.sum_univ_two, conjElem_coe, conjInv_coe]
  fin_cases i <;> fin_cases j <;> simp [conjMat, hc, had] <;> field_simp <;> ring

theorem det_conjMat (γ : SL(2, ℤ)) {δ : SL(2, ℤ)} (hδ : δ ∈ GammaH (q ^ 2 * M') (levelH q M')) :
    (conjMat q M' γ δ).det = 1 := by
  have h : ((conjMat q M' γ δ).det : ℝ) = 1 := by
    rw [show ((conjMat q M' γ δ).det : ℝ) = Int.castRingHom ℝ (conjMat q M' γ δ).det from rfl,
      RingHom.map_det, conjMat_real q M' γ hδ, ← Matrix.GeneralLinearGroup.val_det_apply, map_mul, map_mul,
      map_inv, det_conjElem, inv_one, one_mul, mul_one]
    have : Matrix.GeneralLinearGroup.det ((δ : SL(2, ℤ)) : GL (Fin 2) ℝ) = 1 := by
      ext
      simp
    rw [this, Units.val_one]
  exact_mod_cast h

def conjSL (γ : SL(2, ℤ)) (δ : SL(2, ℤ)) (hδ : δ ∈ GammaH (q ^ 2 * M') (levelH q M')) : SL(2, ℤ) :=
  ⟨conjMat q M' γ δ, det_conjMat q M' γ hδ⟩

theorem conjSL_coe (γ : SL(2, ℤ)) {δ : SL(2, ℤ)} (hδ : δ ∈ GammaH (q ^ 2 * M') (levelH q M')) :
    ((conjSL q M' γ δ hδ : SL(2, ℤ)) : GL (Fin 2) ℝ) = (conjElem q γ)⁻¹ * (δ : GL (Fin 2) ℝ) * conjElem q γ := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  have h := congrFun (congrFun (conjMat_real q M' γ hδ) i) j
  rw [RingHom.mapMatrix_apply, Matrix.map_apply] at h
  rw [← h]
  simp [conjSL]

theorem conjSL_mem {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M') {δ : SL(2, ℤ)}
    (hδ : δ ∈ GammaH (q ^ 2 * M') (levelH q M')) :
    conjSL q M' γ δ hδ ∈ GammaH (q ^ 2 * M') (levelH q M') := by
  rw [mem_GH_iff]
  have hM : ((γ 1 0 : ℤ) : ZMod M') = 0 := Gamma0_mem.mp hγ
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hM
  obtain ⟨kγ, hkγ⟩ := hM
  have had := kad_spec hδ
  have hc := kc_spec hδ
  have h11 := entry11_mod hδ
  have hdetγ : (γ 0 0 : ℤ) * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have h := Matrix.SpecialLinearGroup.det_coe γ
    rw [Matrix.det_fin_two] at h
    exact h
  constructor
  · have e10 : (conjSL q M' γ δ hδ : SL(2, ℤ)) 1 0 =
        q * γ 1 0 * γ 0 0 * (δ 1 1 - δ 0 0) - q ^ 2 * γ 1 0 ^ 2 * δ 0 1 + δ 1 0 * γ 0 0 ^ 2 := rfl
    rw [e10, ZMod.intCast_zmod_eq_zero_iff_dvd]
    refine ⟨-(kγ * γ 0 0 * kad q δ) - M' * kγ ^ 2 * δ 0 1 + kc q M' δ * γ 0 0 ^ 2, ?_⟩
    rw [hc, hkγ, had]
    push_cast
    ring
  · have e11 : (conjSL q M' γ δ hδ : SL(2, ℤ)) 1 1 =
        -(γ 1 0 * δ 0 0 * γ 0 1) - q * γ 1 0 * δ 0 1 * γ 1 1 + γ 0 0 * γ 0 1 * (q * M' * kc q M' δ) +
          γ 0 0 * δ 1 1 * γ 1 1 := rfl
    have e11' : (conjSL q M' γ δ hδ : SL(2, ℤ)) 1 1 =
        δ 1 1 + q * (-(γ 1 0 * γ 0 1 * kad q δ) - γ 1 0 * δ 0 1 * γ 1 1 + γ 0 0 * γ 0 1 * M' * kc q M' δ) := by
      rw [e11, had]
      linear_combination (δ 1 1 : ℤ) * hdetγ
    rw [e11']
    push_cast
    rw [h11, ZMod.natCast_self, zero_mul, add_zero]

theorem coeGL_injective : Function.Injective fun A : SL(2, ℤ) => (A : GL (Fin 2) ℝ) := by
  intro A B h
  ext i j
  have := congrArg (fun g : GL (Fin 2) ℝ => (g : Matrix (Fin 2) (Fin 2) ℝ) i j) h
  simpa using this

def conjFun (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M') (δ : ↥(GammaH (q ^ 2 * M') (levelH q M'))) :
    ↥(GammaH (q ^ 2 * M') (levelH q M')) :=
  ⟨conjSL q M' γ δ.1 δ.2, conjSL_mem q M' hγ δ.2⟩

theorem conjFun_coe (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M') (δ : ↥(GammaH (q ^ 2 * M') (levelH q M'))) :
    (((conjFun q M' γ hγ δ : ↥(GammaH (q ^ 2 * M') (levelH q M'))) : SL(2, ℤ)) : GL (Fin 2) ℝ) =
      (conjElem q γ)⁻¹ * ((δ : SL(2, ℤ)) : GL (Fin 2) ℝ) * conjElem q γ :=
  conjSL_coe q M' γ δ.2

def conjHom (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M') :
    ↥(GammaH (q ^ 2 * M') (levelH q M')) →* ↥(GammaH (q ^ 2 * M') (levelH q M')) where
  toFun := conjFun q M' γ hγ
  map_one' := by
    refine Subtype.ext (coeGL_injective ?_)
    show (((conjFun q M' γ hγ 1 : ↥(GammaH (q ^ 2 * M') (levelH q M'))) : SL(2, ℤ)) : GL (Fin 2) ℝ) =
      (((1 : ↥(GammaH (q ^ 2 * M') (levelH q M'))) : SL(2, ℤ)) : GL (Fin 2) ℝ)
    simp only [conjFun_coe, OneMemClass.coe_one, map_one, mul_one, inv_mul_cancel]
  map_mul' δ₁ δ₂ := by
    refine Subtype.ext (coeGL_injective ?_)
    show (((conjFun q M' γ hγ (δ₁ * δ₂) : ↥(GammaH (q ^ 2 * M') (levelH q M'))) : SL(2, ℤ)) : GL (Fin 2) ℝ) =
      (((conjFun q M' γ hγ δ₁ * conjFun q M' γ hγ δ₂ : ↥(GammaH (q ^ 2 * M') (levelH q M'))) : SL(2, ℤ)) :
        GL (Fin 2) ℝ)
    simp only [MulMemClass.coe_mul, map_mul, conjFun_coe]
    group

theorem conjHom_coe (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M') (δ : ↥(GammaH (q ^ 2 * M') (levelH q M'))) :
    (((conjHom q M' γ hγ δ : ↥(GammaH (q ^ 2 * M') (levelH q M'))) : SL(2, ℤ)) : GL (Fin 2) ℝ) =
      (conjElem q γ)⁻¹ * ((δ : SL(2, ℤ)) : GL (Fin 2) ℝ) * conjElem q γ :=
  conjSL_coe q M' γ δ.2

theorem periodMapOf_L
    (L : ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
      (CuspForm (GammaH (q ^ 2 * M') (levelH q M')) 2 →ₗ[ℂ] CuspForm (GammaH (q ^ 2 * M') (levelH q M')) 2))
    (hL : ∀ (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M')
      (f : CuspForm (GammaH (q ^ 2 * M') (levelH q M')) 2), ⇑(L γ hγ f) = ⇑f ∣[(2 : ℤ)] (conjElem q γ)⁻¹)
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M')
    (f : CuspForm (GammaH (q ^ 2 * M') (levelH q M')) 2) :
    periodMapOf (GammaH (q ^ 2 * M') (levelH q M')) (L γ hγ f) =
      (periodMapOf (GammaH (q ^ 2 * M') (levelH q M')) f).comp (MonoidHom.toAdditive (conjHom q M' γ hγ)) :=
  periodMapOf_gammaH_eq_comp_of_coe_eq_slash (q ^ 2 * M') (levelH q M') (conjElem q γ)⁻¹
    (det_conjElem_inv_pos q γ) (conjHom q M' γ hγ) (fun δ => by rw [inv_inv]; exact conjHom_coe q M' γ hγ δ)
    f _ (hL γ hγ f)

theorem dualMap_L_periodOf
    (L : ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
      (CuspForm (GammaH (q ^ 2 * M') (levelH q M')) 2 →ₗ[ℂ] CuspForm (GammaH (q ^ 2 * M') (levelH q M')) 2))
    (hL : ∀ (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M')
      (f : CuspForm (GammaH (q ^ 2 * M') (levelH q M')) 2), ⇑(L γ hγ f) = ⇑f ∣[(2 : ℤ)] (conjElem q γ)⁻¹)
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M')
    (δ : ↥(GammaH (q ^ 2 * M') (levelH q M'))) :
    (L γ hγ).dualMap (periodOf (GammaH (q ^ 2 * M') (levelH q M')) δ) =
      periodOf (GammaH (q ^ 2 * M') (levelH q M')) (conjHom q M' γ hγ δ) := by
  refine LinearMap.ext fun f => ?_
  rw [LinearMap.dualMap_apply, ← periodMapOf_apply_eq_periodOf, periodMapOf_L q M' L hL γ hγ f,
    AddMonoidHom.comp_apply, ← periodMapOf_apply_eq_periodOf]
  rfl

def LΛ
    (L : ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
      (CuspForm (GammaH (q ^ 2 * M') (levelH q M')) 2 →ₗ[ℂ] CuspForm (GammaH (q ^ 2 * M') (levelH q M')) 2))
    (hstL : ∀ (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M'),
      ∀ v ∈ Lat (q ^ 2 * M') (levelH q M'), (L γ hγ).dualMap v ∈ Lat (q ^ 2 * M') (levelH q M'))
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M') :
    ↥(Lat (q ^ 2 * M') (levelH q M')) →ₗ[ℤ] ↥(Lat (q ^ 2 * M') (levelH q M')) :=
  (((L γ hγ).dualMap).restrictScalars ℤ).restrict (hstL γ hγ)

theorem coe_LΛ
    (L : ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
      (CuspForm (GammaH (q ^ 2 * M') (levelH q M')) 2 →ₗ[ℂ] CuspForm (GammaH (q ^ 2 * M') (levelH q M')) 2))
    (hstL : ∀ (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M'),
      ∀ v ∈ Lat (q ^ 2 * M') (levelH q M'), (L γ hγ).dualMap v ∈ Lat (q ^ 2 * M') (levelH q M'))
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M') (l : ↥(Lat (q ^ 2 * M') (levelH q M'))) :
    ((LΛ q M' L hstL γ hγ l : ↥(Lat (q ^ 2 * M') (levelH q M'))) :
      Module.Dual ℂ (CuspForm (GammaH (q ^ 2 * M') (levelH q M')) 2)) = (L γ hγ).dualMap l := rfl

theorem LΛ_perL
    (L : ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
      (CuspForm (GammaH (q ^ 2 * M') (levelH q M')) 2 →ₗ[ℂ] CuspForm (GammaH (q ^ 2 * M') (levelH q M')) 2))
    (hL : ∀ (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M')
      (f : CuspForm (GammaH (q ^ 2 * M') (levelH q M')) 2), ⇑(L γ hγ f) = ⇑f ∣[(2 : ℤ)] (conjElem q γ)⁻¹)
    (hstL : ∀ (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M'),
      ∀ v ∈ Lat (q ^ 2 * M') (levelH q M'), (L γ hγ).dualMap v ∈ Lat (q ^ 2 * M') (levelH q M'))
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M')
    (δ : ↥(GammaH (q ^ 2 * M') (levelH q M'))) :
    LΛ q M' L hstL γ hγ (perL (q ^ 2 * M') (levelH q M') δ) =
      perL (q ^ 2 * M') (levelH q M') (conjHom q M' γ hγ δ) :=
  Subtype.ext (dualMap_L_periodOf q M' L hL γ hγ δ)

end LevelSide

section TensorAlgebra

variable {p : ℕ} [Fact p.Prime]

theorem liftBaseChange_baseChange {Λ : Type*} [AddCommGroup Λ] [Module ℤ Λ]
    {N : Type*} [AddCommGroup N] [Module ℤ_[p] N]
    (T : Λ →ₗ[ℤ] Λ) (χ χ' : Λ →ₗ[ℤ] N)
    (hkey : χ ∘ₗ T = χ') (z : ℤ_[p] ⊗[ℤ] Λ) :
    χ'.liftBaseChange ℤ_[p] z = χ.liftBaseChange ℤ_[p] (T.baseChange ℤ_[p] z) := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | tmul a v =>
    rw [LinearMap.baseChange_tmul, LinearMap.liftBaseChange_tmul, LinearMap.liftBaseChange_tmul, ← hkey,
      LinearMap.comp_apply]
  | add z w hz hw => rw [map_add, map_add, map_add, hz, hw]

theorem eq_of_forall_liftBaseChange_eq {Λ : Type*} [AddCommGroup Λ] [Module ℤ Λ] {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℤ Λ) {z z' : ℤ_[p] ⊗[ℤ] Λ}
    (h : ∀ χ : Λ →ₗ[ℤ] ℤ_[p], χ.liftBaseChange ℤ_[p] z = χ.liftBaseChange ℤ_[p] z') : z = z' := by
  set B := Algebra.TensorProduct.basis ℤ_[p] b with hB
  refine B.ext_elem fun i => ?_
  have key : ∀ w : ℤ_[p] ⊗[ℤ] Λ,
      B.repr w i = ((Algebra.linearMap ℤ ℤ_[p]).comp (b.coord i)).liftBaseChange ℤ_[p] w := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero, Finsupp.zero_apply]
    | tmul a v =>
      rw [hB, Algebra.TensorProduct.basis_repr_tmul, LinearMap.liftBaseChange_tmul]
      simp [Finsupp.smul_apply, Finsupp.mapRange_apply, Algebra.linearMap_apply]
    | add x y hx hy => rw [map_add, map_add, Finsupp.add_apply, hx, hy]
  rw [key, key, h]

theorem apply_eq_baseChange_of_forall {Λ : Type*} [AddCommGroup Λ] [Module ℤ Λ] {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℤ Λ) {T : Type*} [AddCommGroup T] [Module ℤ_[p] T]
    (e : T ≃ₗ[ℤ_[p]] ℤ_[p] ⊗[ℤ] Λ) (A : T →ₗ[ℤ_[p]] T) (TΛ : Λ →ₗ[ℤ] Λ)
    (h : ∀ (χ : Λ →ₗ[ℤ] ℤ_[p]) (x : T),
      (χ ∘ₗ TΛ).liftBaseChange ℤ_[p] (e x) = χ.liftBaseChange ℤ_[p] (e (A x)))
    (x : T) : e (A x) = TΛ.baseChange ℤ_[p] (e x) :=
  eq_of_forall_liftBaseChange_eq b fun χ => by
    rw [← h χ x, liftBaseChange_baseChange TΛ χ _ rfl]

end TensorAlgebra

section Theta

variable {p : ℕ} [Fact p.Prime] [Algebra ℤ_[p] ℂ]
variable {V : Type*} [AddCommGroup V] [Module ℂ V] (Λ : Submodule ℤ V)
variable {T : Type*} [AddCommGroup T] [Module ℤ_[p] T]

def iotaC : ℂ ⊗[ℤ] ↥Λ →ₗ[ℂ] V := (Λ.subtype).liftBaseChange ℂ

@[scoped simp] theorem iotaC_tmul (c : ℂ) (v : ↥Λ) : iotaC Λ (c ⊗ₜ v) = c • (v : V) :=
  LinearMap.liftBaseChange_tmul ℂ _ c v

def cancelC : ℂ ⊗[ℤ_[p]] (ℤ_[p] ⊗[ℤ] ↥Λ) ≃ₗ[ℂ] ℂ ⊗[ℤ] ↥Λ :=
  TensorProduct.AlgebraTensorModule.cancelBaseChange ℤ ℤ_[p] ℂ ℂ ↥Λ

theorem cancelC_tmul (c : ℂ) (a : ℤ_[p]) (v : ↥Λ) :
    cancelC (p := p) Λ (c ⊗ₜ (a ⊗ₜ v)) = (a • c) ⊗ₜ v :=
  TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul ℤ ℤ_[p] ℂ c v a

theorem iotaC_cancelC_baseChange (B : V →ₗ[ℂ] V) (TΛ : ↥Λ →ₗ[ℤ] ↥Λ)
    (hTΛ : ∀ v : ↥Λ, ((TΛ v : ↥Λ) : V) = B v) (c : ℂ) (z : ℤ_[p] ⊗[ℤ] ↥Λ) :
    iotaC Λ (cancelC Λ (c ⊗ₜ[ℤ_[p]] TΛ.baseChange ℤ_[p] z)) = B (iotaC Λ (cancelC Λ (c ⊗ₜ[ℤ_[p]] z))) := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, TensorProduct.tmul_zero, map_zero, map_zero, map_zero]
  | tmul a v =>
    rw [LinearMap.baseChange_tmul, cancelC_tmul, cancelC_tmul, iotaC_tmul, iotaC_tmul, hTΛ, map_smul]
  | add z w hz hw =>
    rw [map_add, TensorProduct.tmul_add, map_add, map_add, hz, hw, TensorProduct.tmul_add, map_add, map_add,
      map_add]

def Theta (e : T ≃ₗ[ℤ_[p]] ℤ_[p] ⊗[ℤ] ↥Λ) : ℂ ⊗[ℤ_[p]] T →ₗ[ℂ] V :=
  (iotaC Λ) ∘ₗ (cancelC Λ).toLinearMap ∘ₗ (e.toLinearMap.baseChange ℂ)

theorem Theta_tmul (e : T ≃ₗ[ℤ_[p]] ℤ_[p] ⊗[ℤ] ↥Λ) (c : ℂ) (x : T) :
    Theta Λ e (c ⊗ₜ x) = iotaC Λ (cancelC Λ (c ⊗ₜ e x)) := by
  simp only [Theta, LinearMap.comp_apply, LinearMap.baseChange_tmul, LinearEquiv.coe_coe]

theorem Theta_baseChange (e : T ≃ₗ[ℤ_[p]] ℤ_[p] ⊗[ℤ] ↥Λ) (A : T →ₗ[ℤ_[p]] T) (B : V →ₗ[ℂ] V)
    (TΛ : ↥Λ →ₗ[ℤ] ↥Λ) (hTΛ : ∀ v : ↥Λ, ((TΛ v : ↥Λ) : V) = B v)
    (hop : ∀ x, e (A x) = TΛ.baseChange ℤ_[p] (e x)) (w : ℂ ⊗[ℤ_[p]] T) :
    Theta Λ e (A.baseChange ℂ w) = B (Theta Λ e w) := by
  induction w using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul c x => rw [LinearMap.baseChange_tmul, Theta_tmul, Theta_tmul, hop, iotaC_cancelC_baseChange Λ B TΛ hTΛ]
  | add z w hz hw => simp only [map_add, hz, hw]

theorem Theta_one_tmul_symm (e : T ≃ₗ[ℤ_[p]] ℤ_[p] ⊗[ℤ] ↥Λ) (v : ↥Λ) :
    Theta Λ e ((1 : ℂ) ⊗ₜ e.symm ((1 : ℤ_[p]) ⊗ₜ v)) = (v : V) := by
  rw [Theta_tmul, LinearEquiv.apply_symm_apply, cancelC_tmul, one_smul, iotaC_tmul, one_smul]

end Theta

section Psi

variable {p : ℕ} [Fact p.Prime] [Algebra ℤ_[p] ℂ]
variable {S : Type*} [AddCommGroup S] [Module ℂ S] (Λ : Submodule ℤ (Module.Dual ℂ S))
variable {T : Type*} [AddCommGroup T] [Module ℤ_[p] T]

def Psi (e : T ≃ₗ[ℤ_[p]] ℤ_[p] ⊗[ℤ] ↥Λ) : S →ₗ[ℂ] Module.Dual ℂ (ℂ ⊗[ℤ_[p]] T) :=
  (Theta Λ e).dualMap ∘ₗ Module.Dual.eval ℂ S

theorem Psi_apply (e : T ≃ₗ[ℤ_[p]] ℤ_[p] ⊗[ℤ] ↥Λ) (F : S) (w : ℂ ⊗[ℤ_[p]] T) :
    Psi Λ e F w = Theta Λ e w F := rfl

theorem dualMap_Psi (e : T ≃ₗ[ℤ_[p]] ℤ_[p] ⊗[ℤ] ↥Λ) (A : T →ₗ[ℤ_[p]] T) (Bs : S →ₗ[ℂ] S)
    (TΛ : ↥Λ →ₗ[ℤ] ↥Λ) (hTΛ : ∀ v : ↥Λ, ((TΛ v : ↥Λ) : Module.Dual ℂ S) = Bs.dualMap v)
    (hop : ∀ x, e (A x) = TΛ.baseChange ℤ_[p] (e x)) (F : S) :
    (A.baseChange ℂ).dualMap (Psi Λ e F) = Psi Λ e (Bs F) := by
  refine LinearMap.ext fun w => ?_
  rw [LinearMap.dualMap_apply, Psi_apply, Psi_apply, Theta_baseChange Λ e A Bs.dualMap TΛ hTΛ hop w,
    LinearMap.dualMap_apply]

theorem Psi_injective (e : T ≃ₗ[ℤ_[p]] ℤ_[p] ⊗[ℤ] ↥Λ) {ι : Type*} (b : ι → ↥Λ)
    (hspan : Submodule.span ℝ (Set.range fun i => ((b i : ↥Λ) : Module.Dual ℂ S)) = ⊤) :
    Function.Injective (Psi Λ e) := by
  rw [injective_iff_map_eq_zero]
  intro F hF
  have hΛ : ∀ v : ↥Λ, (v : Module.Dual ℂ S) F = 0 := fun v => by
    have h := congrArg (fun ψ : Module.Dual ℂ (ℂ ⊗[ℤ_[p]] T) => ψ ((1 : ℂ) ⊗ₜ e.symm ((1 : ℤ_[p]) ⊗ₜ v))) hF
    rwa [Psi_apply, Theta_one_tmul_symm, LinearMap.zero_apply] at h
  have hall : ∀ φ : Module.Dual ℂ S, φ F = 0 := by
    intro φ
    have hφ : φ ∈ Submodule.span ℝ (Set.range fun i => ((b i : ↥Λ) : Module.Dual ℂ S)) := by
      rw [hspan]; trivial
    induction hφ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact hΛ (b i)
    | zero => rfl
    | add x y _ _ hx hy => rw [LinearMap.add_apply, hx, hy, add_zero]
    | smul r x _ hx =>
      have : (r • x) F = (r : ℂ) * x F := rfl
      rw [this, hx, mul_zero]
  exact (Module.forall_dual_apply_eq_zero_iff ℂ F).1 hall

end Psi

section Main

p2m_open "CohCarrier ModularCurve ModularCurve.FullLevel AlgebraicCurve~H1"

variable (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (lam : ℕ) [Fact lam.Prime] [Algebra ℤ_[lam] ℂ]

theorem mainThm
    (hin : ModularCurve.HeckeDiamondInputsHAll (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M'))
    (hLA : ModularCurve.FullLevel.LevelAutInputs q M')
    (L : ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
      (CuspForm (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')) 2 →ₗ[ℂ] CuspForm (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')) 2))
    (hL : ∀ (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M') (f : CuspForm (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')) 2),
      ⇑(L γ hγ f) = ⇑f ∣[(2 : ℤ)] (ModularCurve.FullLevel.conjElem q γ)⁻¹)
    (hstL : ∀ (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M'),
      ∀ v ∈ ModularCurve.periodLatticeOf (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')), (L γ hγ).dualMap v ∈ ModularCurve.periodLatticeOf (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M'))) :
    ∃ (ζ₀ : ModularCurve.FullLevel.Idx q)
      (Ψ : CuspForm (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')) 2 →ₗ[ℂ] Module.Dual ℂ (ℂ ⊗[ℤ_[lam]] TateModule lam (ModularCurve.FullLevel.jacComp q M'))),
      Function.Injective Ψ ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ q ^ 2 * M') (F : CuspForm (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')) 2),
        ((TateModule.rep lam (ModularCurve.FullLevel.jacComp q M') (AddMonoid.End (ModularCurve.FullLevel.jacComp q M'))
            (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩;
              (ModularCurve.heckeOperatorHAlong (AlgebraicClosure ℚ) (q ^ 2 * M')
                (ModularCurve.FullLevel.levelH q M') ℓ : AddMonoid.End (ModularCurve.FullLevel.jacComp q M')))).baseChange ℂ).dualMap (Ψ F) =
          Ψ (CuspForm.heckeTLinH 2 hℓ hℓM F)) ∧
      (∀ (d : (ZMod (q ^ 2 * M'))ˣ) (F : CuspForm (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')) 2),
        ((TateModule.rep lam (ModularCurve.FullLevel.jacComp q M') (AddMonoid.End (ModularCurve.FullLevel.jacComp q M'))
            (ModularCurve.diamondHBar (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M') d :
              AddMonoid.End (ModularCurve.FullLevel.jacComp q M'))).baseChange ℂ).dualMap (Ψ F) =
          Ψ (CuspForm.diamondLinH 2 d F)) ∧
      (∀ (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M') (F : CuspForm (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')) 2),
        ((TateModule.rep lam (ModularCurve.FullLevel.jacComp q M') (AddMonoid.End (ModularCurve.FullLevel.jacComp q M'))
            (ModularCurve.FullLevel.levelOp q M' ζ₀ γ : AddMonoid.End (ModularCurve.FullLevel.jacComp q M'))).baseChange ℂ).dualMap (Ψ F) =
          Ψ (L γ hγ F)) := by
  classical

  refine (ModularCurve.exists_linearEquiv_tateModule_jH_padicInt_tensor_periodLatticeOf_levelAut q M' (∅ : Set ℕ)
      lam hin L hL hstL).elim fun e he => ?_
  have h1 := he.1
  refine he.2.elim fun ζ₀ h2 => ?_

  refine (ModularCurve.exists_basis_periodLatticeOf_linearIndependent_real_span_eq_top_of_isCongruenceSubgroup
      (GammaH (q ^ 2 * M') (levelH q M')) (isCongruenceSubgroup_gammaH (q ^ 2 * M') (levelH q M'))).elim
    fun n hn => hn.elim fun b hb => ?_
  refine ⟨ζ₀, Psi (Lat (q ^ 2 * M') (levelH q M')) e,
    Psi_injective (Lat (q ^ 2 * M') (levelH q M')) e (fun i => b i) hb.2, ?_, ?_, ?_⟩
  ·
    intro ℓ hℓ hℓM F
    have hop := apply_eq_baseChange_of_forall b e
      (TateModule.rep lam (jacComp q M') (AddMonoid.End (jacComp q M'))
        (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩;
          (ModularCurve.heckeOperatorHAlong (AlgebraicClosure ℚ) (q ^ 2 * M') (levelH q M') ℓ :
            AddMonoid.End (jacComp q M'))))
      (TΛT (q ^ 2 * M') (levelH q M') hℓ hℓM)
      (fun χ x => h1 (.T ℓ hℓ (fun h => h) hℓM) (psiOf _ _ χ) (psiOf_mem _ _ χ) χ
        (χ ∘ₗ TΛT (q ^ 2 * M') (levelH q M') hℓ hℓM) (fun δ => rfl)
        (fun δ => chi_TΛT_perL (q ^ 2 * M') (levelH q M') hℓ hℓM ∅ (fun h => h) χ δ) x)
    exact dualMap_Psi (Lat (q ^ 2 * M') (levelH q M')) e _ (CuspForm.heckeTLinH 2 hℓ hℓM)
      (TΛT (q ^ 2 * M') (levelH q M') hℓ hℓM) (fun _ => rfl) hop F
  ·
    intro d F
    have hop := apply_eq_baseChange_of_forall b e
      (TateModule.rep lam (jacComp q M') (AddMonoid.End (jacComp q M'))
        (ModularCurve.diamondHBar (q ^ 2 * M') (levelH q M') d : AddMonoid.End (jacComp q M')))
      (TΛD (q ^ 2 * M') (levelH q M') d)
      (fun χ x => h1 (.dia d) (psiOf _ _ χ) (psiOf_mem _ _ χ) χ
        (χ ∘ₗ TΛD (q ^ 2 * M') (levelH q M') d) (fun δ => rfl)
        (fun δ => chi_TΛD_perL (q ^ 2 * M') (levelH q M') d ∅ χ δ) x)
    exact dualMap_Psi (Lat (q ^ 2 * M') (levelH q M')) e _ (CuspForm.diamondLinH 2 d)
      (TΛD (q ^ 2 * M') (levelH q M') d) (fun _ => rfl) hop F
  ·
    intro γ hγ F
    have hop := apply_eq_baseChange_of_forall b e
      (TateModule.rep lam (jacComp q M') (AddMonoid.End (jacComp q M'))
        (levelOp q M' ζ₀ γ : AddMonoid.End (jacComp q M')))
      (LΛ q M' L hstL γ hγ)
      (fun χ x => h2 γ hγ (conjHom q M' γ hγ) (conjHom_coe q M' γ hγ) (levelAutBar q M' ζ₀ γ)
        (isLevelAutBar_levelAutBar (hLA ζ₀ γ hγ)) χ (χ ∘ₗ LΛ q M' L hstL γ hγ)
        (fun δ => by
          rw [LinearMap.comp_apply]
          exact congrArg χ (LΛ_perL q M' L hL hstL γ hγ δ)) x)
    exact dualMap_Psi (Lat (q ^ 2 * M') (levelH q M')) e _ (L γ hγ)
      (LΛ q M' L hstL γ hγ) (fun _ => rfl) hop F

end Main

end E4aFullLevel
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_exists_injective_cuspForm_dual_baseChange_tateModule_jacComp_comm.E4aFullLevel"

theorem solution
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (lam : ℕ) [Fact lam.Prime] [Algebra ℤ_[lam] ℂ]
    (hin : ModularCurve.HeckeDiamondInputsHAll (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M'))
    (hLA : ModularCurve.FullLevel.LevelAutInputs q M')
    (L : ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
      (CuspForm (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')) 2 →ₗ[ℂ] CuspForm (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')) 2))
    (hL : ∀ (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M') (f : CuspForm (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')) 2),
      ⇑(L γ hγ f) = ⇑f ∣[(2 : ℤ)] (ModularCurve.FullLevel.conjElem q γ)⁻¹)
    (hstL : ∀ (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M'),
      ∀ v ∈ ModularCurve.periodLatticeOf (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')), (L γ hγ).dualMap v ∈ ModularCurve.periodLatticeOf (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M'))) :
    ∃ (ζ₀ : ModularCurve.FullLevel.Idx q)
      (Ψ : CuspForm (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')) 2 →ₗ[ℂ] Module.Dual ℂ (ℂ ⊗[ℤ_[lam]] TateModule lam (ModularCurve.FullLevel.jacComp q M'))),
      Function.Injective Ψ ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ q ^ 2 * M') (F : CuspForm (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')) 2),
        ((TateModule.rep lam (ModularCurve.FullLevel.jacComp q M') (AddMonoid.End (ModularCurve.FullLevel.jacComp q M'))
            (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩;
              (ModularCurve.heckeOperatorHAlong (AlgebraicClosure ℚ) (q ^ 2 * M')
                (ModularCurve.FullLevel.levelH q M') ℓ : AddMonoid.End (ModularCurve.FullLevel.jacComp q M')))).baseChange ℂ).dualMap (Ψ F) =
          Ψ (CuspForm.heckeTLinH 2 hℓ hℓM F)) ∧
      (∀ (d : (ZMod (q ^ 2 * M'))ˣ) (F : CuspForm (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')) 2),
        ((TateModule.rep lam (ModularCurve.FullLevel.jacComp q M') (AddMonoid.End (ModularCurve.FullLevel.jacComp q M'))
            (ModularCurve.diamondHBar (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M') d :
              AddMonoid.End (ModularCurve.FullLevel.jacComp q M'))).baseChange ℂ).dualMap (Ψ F) =
          Ψ (CuspForm.diamondLinH 2 d F)) ∧
      (∀ (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M') (F : CuspForm (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')) 2),
        ((TateModule.rep lam (ModularCurve.FullLevel.jacComp q M') (AddMonoid.End (ModularCurve.FullLevel.jacComp q M'))
            (ModularCurve.FullLevel.levelOp q M' ζ₀ γ : AddMonoid.End (ModularCurve.FullLevel.jacComp q M'))).baseChange ℂ).dualMap (Ψ F) =
          Ψ (L γ hγ F)) :=
  E4aFullLevel.mainThm q M' lam hin hLA L hL hstL

end
end S_ModularCurve_FullLevel_exists_injective_cuspForm_dual_baseChange_tateModule_jacComp_comm
end P2MW
export P2MW.S_ModularCurve_FullLevel_exists_injective_cuspForm_dual_baseChange_tateModule_jacComp_comm (solution)
