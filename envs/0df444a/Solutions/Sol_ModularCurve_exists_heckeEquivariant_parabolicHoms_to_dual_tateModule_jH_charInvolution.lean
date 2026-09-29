-- Prove2me | solution 1 for ModularCurve.exists_heckeEquivariant_parabolicHoms_to_dual_tateModule_jH_charInvolution
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/207e3069-b879-542a-a899-9b610276510d

import Mathlib
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_ModularCurve_PeriodOf
import Definitions.Def_CohCarrier_CharInvolution
import Definitions.Def_GaloisRep_ComplexConjugation
import Theorems.Thm_ModularCurve_exists_heckeEquivariant_linearEquiv_tateModule_jH_padicInt_tensor_periodLatticeOf_charInvolution
import Theorems.Thm_ModularCurve_exists_linearEquiv_parabolicHoms_dual_periodLatticeOf_apply_periodOf_of_isCongruenceSubgroup
import Theorems.Thm_ModularCurve_exists_basis_periodLatticeOf_linearIndependent_real_span_eq_top_of_isCongruenceSubgroup
import Theorems.Thm_ModularCurve_Period_exists_basis_parabolicHoms_of_isAddTorsionFree
import Theorems.Thm_CohCarrier_H1_moduleFinite
import Theorems.Thm_ModularGroup_exists_eq_conj_T_zpow_of_trace_sq_eq_four
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_heckeEquivariant_parabolicHoms_to_dual_tateModule_jH_charInvolution
p2m_attr_erase "instance" "CuspForm.GammaH_finiteIndex AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.Period.parabolicHoms_int_moduleFinite"
p2m_attr_erase "instance" "ModularCurve.Period.instGroupFG_SL2Z ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0 HeckeEis.instFiniteIndexHeckeUpper FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.ComplexPlaceDictionaryOf.pt_ofGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.injEq ModularCurve.ComplexPlaceDictionaryOf.pt_toGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.sizeOf_spec ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec ModularCurve.qExpandAlgHomC_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow"
p2m_attr_erase "simp" "ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe"
p2m_attr_erase "simp" "AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero ModularCurve.LevelN.coe_jGen FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero HeckeEis.coeffCoboundaryMap_apply"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups TensorProduct

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "tateGenOpH HeckeDiamondInputsHAll Gamma1_le_GammaH JH JH.tateGaloisRep periodOf periodLatticeOf periodOf_mem_periodLatticeOf period Period.IsParabolicHom Period.parabolicHoms Period.mem_parabolicHoms_iff Period.jConjMat_trace Period.jConjSL_coe exists_heckeEquivariant_linearEquiv_tateModule_jH_padicInt_tensor_periodLatticeOf_charInvolution exists_linearEquiv_parabolicHoms_dual_periodLatticeOf_apply_periodOf_of_isCongruenceSubgroup exists_basis_periodLatticeOf_linearIndependent_real_span_eq_top_of_isCongruenceSubgroup Period.exists_basis_parabolicHoms_of_isAddTorsionFree"
namespace JCompConjRed
p2m_open "ModularCurve"

section Stable

open CohCarrier

variable (M : ℕ) (Hs : Subgroup (ZMod M)ˣ) (ℓ : ℕ) [NeZero ℓ] {A : Type*} [AddCommGroup A]

theorem heckeT_apply_eq_sum (φ : H1 M Hs A) (u : ↥(GammaH M Hs))
    [Fintype (Quotient (MulAction.orbitRel (Subgroup.zpowers u)
      (↥(GammaH M Hs) ⧸ GammaHUpper M Hs ℓ)))] :
    heckeT M Hs ℓ A φ (Additive.ofMul u) =
      ∑ O : Quotient (MulAction.orbitRel (Subgroup.zpowers u)
          (↥(GammaH M Hs) ⧸ GammaHUpper M Hs ℓ)),
        φ (Additive.ofMul (conjL M Hs ℓ
          ⟨O.out.out⁻¹ * u ^ Function.minimalPeriod (u • ·) O.out * O.out.out,
            QuotientGroup.out_conj_pow_minimalPeriod_mem _ u O.out⟩)) := by
  change Multiplicative.toAdd (MonoidHom.transfer
    ((AddMonoidHom.toMultiplicativeRight φ).comp (conjL M Hs ℓ)) u) = _
  rw [MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot, toAdd_prod]
  rfl

theorem trace_conjUpperMat (X : SL(2, ℤ)) (hX : (ℓ : ℤ) ∣ X 0 1) :
    ((conjUpperMat ℓ X hX : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace =
      ((X : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace := by
  rw [Matrix.trace_fin_two, Matrix.trace_fin_two]
  simp [conjUpperMat]

theorem trace_sq_conj_pow (γ r : SL(2, ℤ)) (m : ℕ)
    (hγ : (((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace) ^ 2 = 4) :
    (((r⁻¹ * γ ^ m * r : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace) ^ 2 = 4 := by
  obtain ⟨ε, δ, h, hε, rfl⟩ := ModularGroup.exists_eq_conj_T_zpow_of_trace_sq_eq_four γ hγ
  have hu : ∀ n : ℕ, ((r⁻¹ * (δ * ModularGroup.T ^ h * δ⁻¹) ^ n * r : SL(2, ℤ)) :
      Matrix (Fin 2) (Fin 2) ℤ).trace = 2 := by
    intro n
    rw [conj_pow, ← zpow_natCast, ← _root_.zpow_mul,
      show r⁻¹ * (δ * ModularGroup.T ^ (h * (n : ℤ)) * δ⁻¹) * r =
        (r⁻¹ * δ) * (ModularGroup.T ^ (h * (n : ℤ)) * (r⁻¹ * δ)⁻¹) by group,
      Matrix.SpecialLinearGroup.coe_mul, Matrix.trace_mul_comm, ← Matrix.SpecialLinearGroup.coe_mul,
      show ModularGroup.T ^ (h * (n : ℤ)) * (r⁻¹ * δ)⁻¹ * (r⁻¹ * δ) = ModularGroup.T ^ (h * (n : ℤ)) by group,
      ModularGroup.coe_T_zpow, Matrix.trace_fin_two_of]
    ring
  rcases hε with rfl | rfl
  · rw [one_mul, hu]; norm_num
  · rw [neg_one_mul, neg_pow]
    rcases neg_one_pow_eq_or SL(2, ℤ) m with h1 | h1
    · rw [h1, one_mul, hu]; norm_num
    · rw [h1, neg_one_mul, mul_neg, neg_mul, Matrix.SpecialLinearGroup.coe_neg, Matrix.trace_neg,
        neg_sq, hu]
      norm_num

theorem heckeT_isParabolicHom (φ : H1 M Hs A)
    (hφ : ModularCurve.Period.IsParabolicHom (GammaH M Hs) φ) :
    ModularCurve.Period.IsParabolicHom (GammaH M Hs) (heckeT M Hs ℓ A φ) := by
  classical
  intro γ hγ
  haveI : Fintype (Quotient (MulAction.orbitRel (Subgroup.zpowers γ)
      (↥(GammaH M Hs) ⧸ GammaHUpper M Hs ℓ))) := Fintype.ofFinite _
  rw [heckeT_apply_eq_sum]
  refine Finset.sum_eq_zero fun O _ => hφ _ ?_
  set x : ↥(GammaHUpper M Hs ℓ) := ⟨O.out.out⁻¹ * γ ^ Function.minimalPeriod (γ • ·) O.out * O.out.out,
    QuotientGroup.out_conj_pow_minimalPeriod_mem _ γ O.out⟩ with hxdef
  have hx : ((conjL M Hs ℓ x : ↥(GammaH M Hs)) : SL(2, ℤ)) =
      conjUpperMat ℓ ((x : ↥(GammaH M Hs)) : SL(2, ℤ)) (dvd_of_mem_GammaHUpper M Hs ℓ x) := rfl
  rw [hx, trace_conjUpperMat, hxdef]
  show ((((O.out.out⁻¹ * γ ^ Function.minimalPeriod (γ • ·) O.out * O.out.out : ↥(GammaH M Hs)) :
    SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace) ^ 2 = 4
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow]
  exact trace_sq_conj_pow _ _ _ hγ

theorem diamondRaw_isParabolicHom (σ : Gamma0 M) (φ : H1 M Hs A)
    (hφ : ModularCurve.Period.IsParabolicHom (GammaH M Hs) φ) :
    ModularCurve.Period.IsParabolicHom (GammaH M Hs) (diamondRaw M Hs A σ φ) := by
  intro γ hγ
  show φ (Additive.ofMul (conjHom M Hs σ γ)) = 0
  refine hφ _ ?_
  show ((((σ : SL(2, ℤ)) * (γ : SL(2, ℤ)) * (σ : SL(2, ℤ))⁻¹ : SL(2, ℤ)) :
    Matrix (Fin 2) (Fin 2) ℤ).trace) ^ 2 = 4
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.trace_mul_comm, ← Matrix.SpecialLinearGroup.coe_mul,
    show (σ : SL(2, ℤ))⁻¹ * ((σ : SL(2, ℤ)) * (γ : SL(2, ℤ))) = γ by group]
  exact hγ

theorem charInvolution_isParabolicHom (R : Type*) [Semiring R] [Module R A] (φ : H1 M Hs A)
    (hφ : ModularCurve.Period.IsParabolicHom (GammaH M Hs) φ) :
    ModularCurve.Period.IsParabolicHom (GammaH M Hs) (charInvolution M Hs A R φ) := by
  intro γ hγ
  rw [charInvolution_apply, toMul_ofMul]
  refine hφ _ ?_
  rw [coe_jConjGammaH, ModularCurve.Period.jConjSL_coe, ModularCurve.Period.jConjMat_trace]
  exact hγ

end Stable

section OpStable

open CohCarrier

variable (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (S : Set ℕ) (𝒪 : Type) [CommRing 𝒪]

theorem opFamily_mem_parabolicHoms (g : Gen M S) (v : H1 M H 𝒪)
    (hv : v ∈ ModularCurve.Period.parabolicHoms 𝒪 (GammaH M H) 𝒪) :
    opFamily M H S 𝒪 g v ∈ ModularCurve.Period.parabolicHoms 𝒪 (GammaH M H) 𝒪 := by
  rw [ModularCurve.Period.mem_parabolicHoms_iff] at hv ⊢
  cases g with
  | T ℓ hℓ hℓS hℓM =>
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    show ModularCurve.Period.IsParabolicHom _ (heckeTL M H 𝒪 ℓ v)
    rw [heckeTL_apply]
    exact heckeT_isParabolicHom M H ℓ v hv
  | U q hq hqM =>
    haveI : NeZero q := ⟨hq.ne_zero⟩
    show ModularCurve.Period.IsParabolicHom _ (heckeTL M H 𝒪 q v)
    rw [heckeTL_apply]
    exact heckeT_isParabolicHom M H q v hv
  | dia d =>
    show ModularCurve.Period.IsParabolicHom _ (diamondL M H 𝒪 d v)
    exact diamondRaw_isParabolicHom M H _ v hv

theorem charInvolution_mem_parabolicHoms (v : H1 M H 𝒪)
    (hv : v ∈ ModularCurve.Period.parabolicHoms 𝒪 (GammaH M H) 𝒪) :
    charInvolution M H 𝒪 𝒪 v ∈ ModularCurve.Period.parabolicHoms 𝒪 (GammaH M H) 𝒪 := by
  rw [ModularCurve.Period.mem_parabolicHoms_iff] at hv ⊢
  exact charInvolution_isParabolicHom M H 𝒪 v hv

def opC : Option (Gen M S) → Module.End 𝒪 (H1 M H 𝒪)
  | some g => opFamily M H S 𝒪 g
  | none => charInvolution M H 𝒪 𝒪

@[scoped simp] theorem opC_some (g : Gen M S) : opC M H S 𝒪 (some g) = opFamily M H S 𝒪 g := rfl

@[scoped simp] theorem opC_none : opC M H S 𝒪 none = charInvolution M H 𝒪 𝒪 := rfl

theorem opC_mem_parabolicHoms (g : Option (Gen M S)) (v : H1 M H 𝒪)
    (hv : v ∈ ModularCurve.Period.parabolicHoms 𝒪 (GammaH M H) 𝒪) :
    opC M H S 𝒪 g v ∈ ModularCurve.Period.parabolicHoms 𝒪 (GammaH M H) 𝒪 := by
  cases g with
  | some g => exact opFamily_mem_parabolicHoms M H S 𝒪 g v hv
  | none => exact charInvolution_mem_parabolicHoms M H 𝒪 v hv

end OpStable

section TateSide

variable (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (S : Set ℕ) (p : ℕ) [Fact p.Prime]

def tateC : Option (CohCarrier.Gen M S) → Module.End ℤ_[p] (TateModule p (ModularCurve.JH M H))
  | some g => ModularCurve.tateGenOpH M H S p g
  | none => ModularCurve.JH.tateGaloisRep M H p complexConjugation

@[scoped simp] theorem tateC_some (g : CohCarrier.Gen M S) :
    tateC M H S p (some g) = ModularCurve.tateGenOpH M H S p g := rfl

@[scoped simp] theorem tateC_none :
    tateC M H S p none = ModularCurve.JH.tateGaloisRep M H p complexConjugation := rfl

end TateSide

section Engine

variable (p : ℕ) [Fact p.Prime]
variable (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]
variable (Λ : Type) [AddCommGroup Λ] [Module.Free ℤ Λ] [Module.Finite ℤ Λ]
variable (per : Γ → Λ)
variable (EV : ModularCurve.Period.parabolicHoms ℤ Γ ℤ ≃ₗ[ℤ] Module.Dual ℤ Λ)

def EvalProp : Prop :=
  ∀ (ψ : ModularCurve.Period.parabolicHoms ℤ Γ ℤ) (δ : Γ), EV ψ (per δ) = (ψ : Additive Γ →+ ℤ) (Additive.ofMul δ)

abbrev ParZ : Submodule ℤ (Additive Γ →+ ℤ) := ModularCurve.Period.parabolicHoms ℤ Γ ℤ

abbrev ParP : Submodule ℤ_[p] (Additive Γ →+ ℤ_[p]) := ModularCurve.Period.parabolicHoms ℤ_[p] Γ ℤ_[p]

structure BasisDatum where
  n : ℕ
  b : Module.Basis (Fin n) ℤ (ParZ Γ)
  bP : Module.Basis (Fin n) ℤ_[p] (ParP p Γ)
  hbP : ∀ i, (bP i : Additive Γ →+ ℤ_[p]) = (Int.castAddHom ℤ_[p]).comp (b i : Additive Γ →+ ℤ)

theorem nonempty_basisDatum : Nonempty (BasisDatum p Γ) := by
  obtain ⟨n, b, hb⟩ := ModularCurve.Period.exists_basis_parabolicHoms_of_isAddTorsionFree Γ
  obtain ⟨bP, hbP⟩ := hb ℤ_[p]
  exact ⟨⟨n, b, bP, hbP⟩⟩

variable (B : BasisDatum p Γ)

def iota : ParP p Γ ≃ₗ[ℤ_[p]] ℤ_[p] ⊗[ℤ] ParZ Γ :=
  B.bP.repr.trans (Algebra.TensorProduct.basis ℤ_[p] B.b).repr.symm

theorem iota_bP (i : Fin B.n) : iota p Γ B (B.bP i) = 1 ⊗ₜ (B.b i) := by
  rw [iota, LinearEquiv.trans_apply, Module.Basis.repr_self]
  rw [LinearEquiv.symm_apply_eq, Algebra.TensorProduct.basis_repr_tmul, one_smul,
    Module.Basis.repr_self]
  ext j
  simp [Finsupp.mapRange_single]

def toD : ℤ_[p] ⊗[ℤ] Module.Dual ℤ Λ ≃ₗ[ℤ_[p]] Module.Dual ℤ_[p] (ℤ_[p] ⊗[ℤ] Λ) :=
  (TensorProduct.isBaseChange ℤ Λ ℤ_[p]).toDualBaseChange

theorem toD_tmul (a : ℤ_[p]) (f : Module.Dual ℤ Λ) (v : Λ) :
    toD p Λ (a ⊗ₜ f) (1 ⊗ₜ v) = a * (f v : ℤ_[p]) := by
  have := (TensorProduct.isBaseChange ℤ Λ ℤ_[p]).toDualBaseChange_tmul a f v
  (first | exact this | simpa using this | (have h__ := this; simp at h__; exact h__))

def Theta : ParP p Γ ≃ₗ[ℤ_[p]] Module.Dual ℤ_[p] (ℤ_[p] ⊗[ℤ] Λ) :=
  (iota p Γ B).trans ((EV.baseChange ℤ ℤ_[p] _ _).trans (toD p Λ))

theorem Theta_apply_tmul_per (hEV : EvalProp Γ Λ per EV) (v : ParP p Γ) (δ : Γ) :
    Theta p Γ Λ EV B v (1 ⊗ₜ per δ) = (v : Additive Γ →+ ℤ_[p]) (Additive.ofMul δ) := by

  let L₁ : ParP p Γ →ₗ[ℤ_[p]] ℤ_[p] :=
    (LinearMap.applyₗ (1 ⊗ₜ[ℤ] per δ)) ∘ₗ (Theta p Γ Λ EV B).toLinearMap
  let L₂ : ParP p Γ →ₗ[ℤ_[p]] ℤ_[p] :=
    { toFun := fun v => (v : Additive Γ →+ ℤ_[p]) (Additive.ofMul δ)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  suffices h : L₁ = L₂ from LinearMap.congr_fun h v
  refine B.bP.ext fun i => ?_
  show Theta p Γ Λ EV B (B.bP i) (1 ⊗ₜ per δ) = (B.bP i : Additive Γ →+ ℤ_[p]) (Additive.ofMul δ)
  rw [Theta, LinearEquiv.trans_apply, LinearEquiv.trans_apply, iota_bP, LinearEquiv.baseChange_tmul,
    toD_tmul, one_mul, hEV, B.hbP]
  rfl

def chiOf (v : ParP p Γ) : Λ →ₗ[ℤ] ℤ_[p] :=
  (Theta p Γ Λ EV B v).restrictScalars ℤ ∘ₗ ((TensorProduct.mk ℤ ℤ_[p] Λ) 1).restrictScalars ℤ

theorem chiOf_apply (v : ParP p Γ) (x : Λ) : chiOf p Γ Λ EV B v x = Theta p Γ Λ EV B v (1 ⊗ₜ x) := rfl

theorem chiOf_per (hEV : EvalProp Γ Λ per EV) (v : ParP p Γ) (δ : Γ) :
    chiOf p Γ Λ EV B v (per δ) = (v : Additive Γ →+ ℤ_[p]) (Additive.ofMul δ) := by
  rw [chiOf_apply, Theta_apply_tmul_per p Γ Λ per EV B hEV]

theorem liftBaseChange_chiOf (v : ParP p Γ) :
    (chiOf p Γ Λ EV B v).liftBaseChange ℤ_[p] = Theta p Γ Λ EV B v := by
  refine TensorProduct.AlgebraTensorModule.ext fun a x => ?_
  rw [LinearMap.liftBaseChange_tmul, chiOf_apply, ← map_smul, TensorProduct.smul_tmul', smul_eq_mul,
    mul_one]

variable (T : Type) [AddCommGroup T] [Module ℤ_[p] T] (e : T ≃ₗ[ℤ_[p]] ℤ_[p] ⊗[ℤ] Λ)

def PhiPar : ParP p Γ ≃ₗ[ℤ_[p]] Module.Dual ℤ_[p] T :=
  (Theta p Γ Λ EV B).trans e.dualMap

theorem PhiPar_apply (v : ParP p Γ) (x : T) :
    PhiPar p Γ Λ EV B T e v x = Theta p Γ Λ EV B v (e x) := rfl

variable [Module.Finite ℤ_[p] (Additive Γ →+ ℤ_[p])]

theorem isTorsionFree_quotient :
    Module.IsTorsionFree ℤ_[p] ((Additive Γ →+ ℤ_[p]) ⧸ (ParP p Γ)) := by
  rw [Module.isTorsionFree_iff_smul_eq_zero]
  intro a x hax
  rcases eq_or_ne a 0 with ha | ha
  · exact Or.inl ha
  right
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [Submodule.Quotient.mk_eq_zero]
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hax
  intro γ hγ
  have h := hax γ hγ
  change a • v (Additive.ofMul γ) = 0 at h
  rw [smul_eq_mul] at h
  exact (mul_eq_zero.mp h).resolve_left ha

theorem exists_retraction :
    ∃ π : (Additive Γ →+ ℤ_[p]) →ₗ[ℤ_[p]] ParP p Γ, ∀ v : ParP p Γ, π v = v := by
  haveI := isTorsionFree_quotient p Γ
  haveI : Module.Finite ℤ_[p] ((Additive Γ →+ ℤ_[p]) ⧸ (ParP p Γ)) := inferInstance
  haveI : Module.Free ℤ_[p] ((Additive Γ →+ ℤ_[p]) ⧸ (ParP p Γ)) :=
    Module.free_of_finite_type_torsion_free'
  obtain ⟨s, hs⟩ := (ParP p Γ).mkQ.exists_rightInverse_of_surjective (Submodule.range_mkQ _)
  have hsapp : ∀ y, (ParP p Γ).mkQ (s y) = y := fun y => LinearMap.congr_fun hs y
  refine ⟨LinearMap.codRestrict (ParP p Γ) (LinearMap.id - s ∘ₗ (ParP p Γ).mkQ) (fun x => ?_), fun v => ?_⟩
  · rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, LinearMap.sub_apply, map_sub,
      LinearMap.comp_apply, hsapp, LinearMap.id_apply, sub_self]
  · apply Subtype.ext
    simp only [LinearMap.codRestrict_apply, LinearMap.sub_apply, LinearMap.id_apply,
      LinearMap.comp_apply, Submodule.mkQ_apply]
    rw [(Submodule.Quotient.mk_eq_zero _).mpr v.2, map_zero, sub_zero]

theorem main (B : BasisDatum p Γ) (hEV : EvalProp Γ Λ per EV)
    {G : Type} (op : G → Module.End ℤ_[p] (Additive Γ →+ ℤ_[p]))
    (hop : ∀ (g : G) (v : Additive Γ →+ ℤ_[p]), v ∈ ParP p Γ → op g v ∈ ParP p Γ)
    (Tg : G → Module.End ℤ_[p] T)
    (hcompat : ∀ (g : G) (ψ : Additive Γ →+ ℤ_[p]), ψ ∈ ParP p Γ →
      ∀ (χ χ' : Λ →ₗ[ℤ] ℤ_[p]),
        (∀ δ : Γ, χ (per δ) = ψ (Additive.ofMul δ)) →
        (∀ δ : Γ, χ' (per δ) = op g ψ (Additive.ofMul δ)) →
        ∀ x : T, χ'.liftBaseChange ℤ_[p] (e x) = χ.liftBaseChange ℤ_[p] (e (Tg g x))) :
    ∃ Φ : (Additive Γ →+ ℤ_[p]) →ₗ[ℤ_[p]] Module.Dual ℤ_[p] T,
      (∀ (g : G) (v : Additive Γ →+ ℤ_[p]), v ∈ ParP p Γ → Φ (op g v) = (Φ v) ∘ₗ Tg g) ∧
      (ParP p Γ).map Φ = ⊤ ∧
      (∀ v ∈ ParP p Γ, Φ v = 0 → v = 0) := by
  obtain ⟨π, hπ⟩ := exists_retraction p Γ
  set E := PhiPar p Γ Λ EV B T e with hE
  have hΦpar : ∀ v : Additive Γ →+ ℤ_[p], ∀ hv : v ∈ ParP p Γ,
      (E.toLinearMap ∘ₗ π) v = E ⟨v, hv⟩ := fun v hv => by
    rw [LinearMap.comp_apply, hπ ⟨v, hv⟩]
    rfl
  refine ⟨E.toLinearMap ∘ₗ π, ?_, ?_, ?_⟩
  ·
    intro g v hv
    rw [hΦpar v hv, hΦpar (op g v) (hop g v hv)]
    apply LinearMap.ext
    intro x
    rw [LinearMap.comp_apply, hE, PhiPar_apply, PhiPar_apply]
    have h1 := hcompat g v hv (chiOf p Γ Λ EV B ⟨v, hv⟩) (chiOf p Γ Λ EV B ⟨op g v, hop g v hv⟩)
      (fun δ => chiOf_per p Γ Λ per EV B hEV ⟨v, hv⟩ δ)
      (fun δ => chiOf_per p Γ Λ per EV B hEV ⟨op g v, hop g v hv⟩ δ) x
    rwa [liftBaseChange_chiOf, liftBaseChange_chiOf] at h1
  ·
    rw [eq_top_iff]
    intro μ _
    refine ⟨(E.symm μ : ParP p Γ), (E.symm μ).2, ?_⟩
    rw [hΦpar _ (E.symm μ).2]
    simp
  ·
    intro v hv h0
    rw [hΦpar v hv] at h0
    have : (⟨v, hv⟩ : ParP p Γ) = 0 := E.injective (by rw [h0, LinearEquiv.map_zero])
    exact congrArg Subtype.val this

end Engine

end ModularCurve.JCompConjRed
p2m_reactivate "P2MW.S_ModularCurve_exists_heckeEquivariant_parabolicHoms_to_dual_tateModule_jH_charInvolution.ModularCurve P2MW.S_ModularCurve_exists_heckeEquivariant_parabolicHoms_to_dual_tateModule_jH_charInvolution.ModularCurve.JCompConjRed"
p2m_reactivate "P2MW.S_ModularCurve_exists_heckeEquivariant_parabolicHoms_to_dual_tateModule_jH_charInvolution.ModularCurve"

end
p2m_reactivate "P2MW.S_ModularCurve_exists_heckeEquivariant_parabolicHoms_to_dual_tateModule_jH_charInvolution.ModularCurve P2MW.S_ModularCurve_exists_heckeEquivariant_parabolicHoms_to_dual_tateModule_jH_charInvolution.ModularCurve.JCompConjRed"

namespace ModularCurve
p2m_export "ModularCurve" "tateGenOpH HeckeDiamondInputsHAll Gamma1_le_GammaH JH JH.tateGaloisRep periodOf periodLatticeOf periodOf_mem_periodLatticeOf period Period.IsParabolicHom Period.parabolicHoms Period.mem_parabolicHoms_iff Period.jConjMat_trace Period.jConjSL_coe exists_heckeEquivariant_linearEquiv_tateModule_jH_padicInt_tensor_periodLatticeOf_charInvolution exists_linearEquiv_parabolicHoms_dual_periodLatticeOf_apply_periodOf_of_isCongruenceSubgroup exists_basis_periodLatticeOf_linearIndependent_real_span_eq_top_of_isCongruenceSubgroup Period.exists_basis_parabolicHoms_of_isAddTorsionFree"
namespace JCompConjRed
p2m_open "ModularCurve"

theorem assemble (M p : ℕ) [NeZero M] [Fact p.Prime] (H : Subgroup (ZMod M)ˣ) (S : Set ℕ)
    {m : ℕ} (c : Module.Basis (Fin m) ℤ (ModularCurve.periodLatticeOf (CohCarrier.GammaH M H)))
    (EV : ModularCurve.Period.parabolicHoms ℤ (CohCarrier.GammaH M H) ℤ ≃ₗ[ℤ]
      Module.Dual ℤ (ModularCurve.periodLatticeOf (CohCarrier.GammaH M H)))
    (hEV : ∀ (ψ : ModularCurve.Period.parabolicHoms ℤ (CohCarrier.GammaH M H) ℤ)
      (δ : CohCarrier.GammaH M H),
      EV ψ ⟨ModularCurve.periodOf (CohCarrier.GammaH M H) δ,
        ModularCurve.periodOf_mem_periodLatticeOf (CohCarrier.GammaH M H) δ⟩ =
        (ψ : Additive (CohCarrier.GammaH M H) →+ ℤ) (Additive.ofMul δ))
    (e : TateModule p (ModularCurve.JH M H) ≃ₗ[ℤ_[p]]
        ℤ_[p] ⊗[ℤ] ModularCurve.periodLatticeOf (CohCarrier.GammaH M H))
    (he : ∀ (g : Option (CohCarrier.Gen M S)) (ψ : CohCarrier.H1 M H ℤ_[p]),
        ψ ∈ ModularCurve.Period.parabolicHoms ℤ_[p] (CohCarrier.GammaH M H) ℤ_[p] →
        ∀ (χ χ' : ModularCurve.periodLatticeOf (CohCarrier.GammaH M H) →ₗ[ℤ] ℤ_[p]),
          (∀ δ : CohCarrier.GammaH M H,
            χ ⟨ModularCurve.periodOf (CohCarrier.GammaH M H) δ,
              ModularCurve.periodOf_mem_periodLatticeOf (CohCarrier.GammaH M H) δ⟩ =
              ψ (Additive.ofMul δ)) →
          (∀ δ : CohCarrier.GammaH M H,
            χ' ⟨ModularCurve.periodOf (CohCarrier.GammaH M H) δ,
              ModularCurve.periodOf_mem_periodLatticeOf (CohCarrier.GammaH M H) δ⟩ =
              opC M H S ℤ_[p] g ψ (Additive.ofMul δ)) →
          ∀ x : TateModule p (ModularCurve.JH M H),
            χ'.liftBaseChange ℤ_[p] (e x) =
              χ.liftBaseChange ℤ_[p] (e (tateC M H S p g x))) :
    ∃ Φ : CohCarrier.H1 M H ℤ_[p] →ₗ[ℤ_[p]]
        (TateModule p (ModularCurve.JH M H) →ₗ[ℤ_[p]] ℤ_[p]),
      (∀ (g : CohCarrier.Gen M S) (v : CohCarrier.H1 M H ℤ_[p]),
        v ∈ ModularCurve.Period.parabolicHoms ℤ_[p] (CohCarrier.GammaH M H) ℤ_[p] →
          Φ (CohCarrier.opFamily M H S ℤ_[p] g v) = (Φ v) ∘ₗ ModularCurve.tateGenOpH M H S p g) ∧
      (∀ v ∈ ModularCurve.Period.parabolicHoms ℤ_[p] (CohCarrier.GammaH M H) ℤ_[p],
        Φ (CohCarrier.charInvolution M H ℤ_[p] ℤ_[p] v) =
          (Φ v) ∘ₗ ModularCurve.JH.tateGaloisRep M H p complexConjugation) ∧
      (ModularCurve.Period.parabolicHoms ℤ_[p] (CohCarrier.GammaH M H) ℤ_[p]).map Φ = ⊤ ∧
      (∀ v ∈ ModularCurve.Period.parabolicHoms ℤ_[p] (CohCarrier.GammaH M H) ℤ_[p], Φ v = 0 → v = 0) := by
  have hcong : CongruenceSubgroup.IsCongruenceSubgroup (CohCarrier.GammaH M H) :=
    CongruenceSubgroup.isCongruenceSubgroup_trans _ _ (ModularCurve.Gamma1_le_GammaH M H)
      (CongruenceSubgroup.Gamma1_is_congruence M)
  haveI : (CohCarrier.GammaH M H).FiniteIndex := hcong.finiteIndex
  haveI := Module.Free.of_basis c
  haveI := Module.Finite.of_basis c
  haveI : Module.Finite ℤ_[p] (Additive (CohCarrier.GammaH M H) →+ ℤ_[p]) :=
    CohCarrier.H1_moduleFinite M H ℤ_[p] ℤ_[p]
  obtain ⟨B⟩ := nonempty_basisDatum p (CohCarrier.GammaH M H)
  refine (main p (CohCarrier.GammaH M H)
    (ModularCurve.periodLatticeOf (CohCarrier.GammaH M H))
    (fun δ => ⟨ModularCurve.periodOf (CohCarrier.GammaH M H) δ,
      ModularCurve.periodOf_mem_periodLatticeOf (CohCarrier.GammaH M H) δ⟩)
    EV (TateModule p (ModularCurve.JH M H)) e B hEV
    (opC M H S ℤ_[p]) (opC_mem_parabolicHoms M H S ℤ_[p]) (tateC M H S p) he).elim fun Φ h => ?_
  exact ⟨Φ, fun g v hv => h.1 (some g) v hv, fun v hv => h.1 none v hv, h.2.1, h.2.2⟩

end ModularCurve.JCompConjRed
p2m_reactivate "P2MW.S_ModularCurve_exists_heckeEquivariant_parabolicHoms_to_dual_tateModule_jH_charInvolution.ModularCurve P2MW.S_ModularCurve_exists_heckeEquivariant_parabolicHoms_to_dual_tateModule_jH_charInvolution.ModularCurve.JCompConjRed"
p2m_reactivate "P2MW.S_ModularCurve_exists_heckeEquivariant_parabolicHoms_to_dual_tateModule_jH_charInvolution.ModularCurve P2MW.S_ModularCurve_exists_heckeEquivariant_parabolicHoms_to_dual_tateModule_jH_charInvolution.ModularCurve.JCompConjRed"

theorem solution
    (M p : ℕ) [NeZero M] [Fact p.Prime] (H : Subgroup (ZMod M)ˣ) (S : Set ℕ)
    (hin : ModularCurve.HeckeDiamondInputsHAll M H) :
    ∃ Φ : CohCarrier.H1 M H ℤ_[p] →ₗ[ℤ_[p]]
        (TateModule p (ModularCurve.JH M H) →ₗ[ℤ_[p]] ℤ_[p]),
      (∀ (g : CohCarrier.Gen M S) (v : CohCarrier.H1 M H ℤ_[p]),
        v ∈ ModularCurve.Period.parabolicHoms ℤ_[p] (CohCarrier.GammaH M H) ℤ_[p] →
          Φ (CohCarrier.opFamily M H S ℤ_[p] g v) = (Φ v) ∘ₗ ModularCurve.tateGenOpH M H S p g) ∧
      (∀ v ∈ ModularCurve.Period.parabolicHoms ℤ_[p] (CohCarrier.GammaH M H) ℤ_[p],
        Φ (CohCarrier.charInvolution M H ℤ_[p] ℤ_[p] v) =
          (Φ v) ∘ₗ ModularCurve.JH.tateGaloisRep M H p complexConjugation) ∧
      (ModularCurve.Period.parabolicHoms ℤ_[p] (CohCarrier.GammaH M H) ℤ_[p]).map Φ = ⊤ ∧
      (∀ v ∈ ModularCurve.Period.parabolicHoms ℤ_[p] (CohCarrier.GammaH M H) ℤ_[p], Φ v = 0 → v = 0) := by
  have hcong : CongruenceSubgroup.IsCongruenceSubgroup (CohCarrier.GammaH M H) :=
    CongruenceSubgroup.isCongruenceSubgroup_trans _ _ (ModularCurve.Gamma1_le_GammaH M H)
      (CongruenceSubgroup.Gamma1_is_congruence M)

  refine (ModularCurve.exists_basis_periodLatticeOf_linearIndependent_real_span_eq_top_of_isCongruenceSubgroup
      (CohCarrier.GammaH M H) hcong).elim fun m hm => hm.elim fun c _ => ?_

  refine (ModularCurve.exists_linearEquiv_parabolicHoms_dual_periodLatticeOf_apply_periodOf_of_isCongruenceSubgroup
      (CohCarrier.GammaH M H) hcong).elim fun EV hEV => ?_

  refine (ModularCurve.exists_heckeEquivariant_linearEquiv_tateModule_jH_padicInt_tensor_periodLatticeOf_charInvolution
      M p H S hin).elim fun e he => ?_
  refine ModularCurve.JCompConjRed.assemble M p H S c EV hEV e ?_
  rintro (_ | g) ψ hψ χ χ' hχ hχ' x
  · exact he.2 ψ hψ χ χ' hχ hχ' x
  · exact he.1 g ψ hψ χ χ' hχ hχ' x

end S_ModularCurve_exists_heckeEquivariant_parabolicHoms_to_dual_tateModule_jH_charInvolution
end P2MW
export P2MW.S_ModularCurve_exists_heckeEquivariant_parabolicHoms_to_dual_tateModule_jH_charInvolution (solution)
