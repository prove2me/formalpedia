-- Prove2me | solution 1 for ModularCurve.XHDRLevel.map_span_natCast_eq_maximalIdeal_of_mem_minimalPrimes_chartAlg_gammaH
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/056e4eaf-7576-5f23-a25d-119de04ba682

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_GaloisRep_RatLocalizedAtResidue
import Definitions.Def_ModularCurve_LaurentCoeff
import Theorems.Thm_GaloisRep_isDiscreteValuationRing_ratLocalizedAt
import Theorems.Thm_GaloisRep_ratLocalizedAt_maximalIdeal_eq_span_natCast
import Theorems.Thm_GaloisRep_isFractionRing_ratLocalizedAt
import Theorems.Thm_GaloisRep_isLocalization_ratLocalizedAt
import Theorems.Thm_ModularCurve_transcendental_of_coe_eq_coeffEmb_jq
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_mem_minimalPrimes_span_iff_of_valuationSubring_pair
import Theorems.Thm_ModularCurve_XHDRLevel_exists_valuationSubring_pair_gammaH
import Theorems.Thm_ModularCurve_finiteDimensional_and_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_map_span_eq_maximalIdeal_localization_atPrime_of_forall_valuationSubring_mul_inv_mem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRLevel_map_span_natCast_eq_maximalIdeal_of_mem_minimalPrimes_chartAlg_gammaH
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation"
p2m_attr_erase "simp" "ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero"
p2m_attr_erase "simp" "ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.ProjectiveLine.map_mk ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single"
p2m_attr_erase "simp" "ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring"

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

p2m_open "ModularCurve P2MW.S_ModularCurve_XHDRLevel_map_span_natCast_eq_maximalIdeal_of_mem_minimalPrimes_chartAlg_gammaH.ModularCurve ModularCurve.XHDRLevel P2MW.S_ModularCurve_XHDRLevel_map_span_natCast_eq_maximalIdeal_of_mem_minimalPrimes_chartAlg_gammaH.ModularCurve.XHDRLevel AlgebraicCurve.TwoChartIntegralModel"
open scoped MatrixGroups

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "qExpFunctionFieldC jq coeffEmb coeffEmb_coeff laurentBaseChange jqModC transcendental_of_coe_eq_coeffEmb_jq XHDRLevel.exists_valuationSubring_pair_gammaH finiteDimensional_and_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index"
namespace XHDRLevel
p2m_export "ModularCurve.XHDRLevel" "R jAt coe_jAt X chartAlgFin chartAlgInf exists_valuationSubring_pair_gammaH"
namespace KerMinH
p2m_open "ModularCurve.XHDRLevel ModularCurve"

variable (p : ℕ) [Fact p.Prime]

scoped instance instDVR_R : IsDiscreteValuationRing ↥(GaloisRep.ratLocalizedAt p) := GaloisRep.isDiscreteValuationRing_ratLocalizedAt p Fact.out

theorem maximalIdeal_R : IsLocalRing.maximalIdeal ↥(GaloisRep.ratLocalizedAt p) = Ideal.span {((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p))} :=
  GaloisRep.ratLocalizedAt.maximalIdeal_eq_span_natCast p Fact.out

theorem mem_maximalIdeal_iff_mem_span (a : ↥(GaloisRep.ratLocalizedAt p)) :
    a ∈ IsLocalRing.maximalIdeal ↥(GaloisRep.ratLocalizedAt p) ↔ a ∈ Ideal.span {((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p))} := by rw [maximalIdeal_R]

theorem p_ne_zero_R : ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero

theorem irreducible_p : Irreducible ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)) :=
  IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal _ (p_ne_zero_R p) (maximalIdeal_R p)

theorem prime_p : Prime ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)) := (irreducible_p p).prime

theorem res_eq_zero_iff (r : ↥(GaloisRep.ratLocalizedAt p)) : GaloisRep.ratLocalizedAtResidue p r = 0 ↔ ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)) ∣ r := by
  rw [← Ideal.mem_span_singleton, ← maximalIdeal_R]
  constructor
  · intro hr
    by_contra h
    have hu : IsUnit r := by rwa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] at h
    exact (hu.map (GaloisRep.ratLocalizedAtResidue p)).ne_zero hr
  · intro hr
    rw [maximalIdeal_R, Ideal.mem_span_singleton] at hr
    obtain ⟨t, rfl⟩ := hr
    rw [map_mul, map_natCast, ZMod.natCast_self, zero_mul]

theorem residue_eq_zero_iff' (r : ↥(GaloisRep.ratLocalizedAt p)) :
    IsLocalRing.residue ↥(GaloisRep.ratLocalizedAt p) r = 0 ↔ GaloisRep.ratLocalizedAtResidue p r = 0 := by
  rw [IsLocalRing.residue_eq_zero_iff, res_eq_zero_iff, ← Ideal.mem_span_singleton, maximalIdeal_R]

theorem map_residue_ne_zero_iff (Q : Polynomial ↥(GaloisRep.ratLocalizedAt p)) :
    Q.map (IsLocalRing.residue ↥(GaloisRep.ratLocalizedAt p)) ≠ 0 ↔ Q.map (GaloisRep.ratLocalizedAtResidue p) ≠ 0 := by
  refine not_congr ⟨fun h => ?_, fun h => ?_⟩ <;> ext n <;> have hn := congrArg (fun P : Polynomial _ => P.coeff n) h <;>
    simp only [Polynomial.coeff_map, Polynomial.coeff_zero] at hn ⊢
  · exact (residue_eq_zero_iff' p _).mp hn
  · exact (residue_eq_zero_iff' p _).mpr hn

theorem map_ne_zero_iff_not_C_dvd (Q : Polynomial ↥(GaloisRep.ratLocalizedAt p)) :
    Q.map (GaloisRep.ratLocalizedAtResidue p) ≠ 0 ↔ ¬ (Polynomial.C ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)) ∣ Q) := by
  rw [Polynomial.C_dvd_iff_dvd_coeff]
  refine not_congr ⟨fun h n => (res_eq_zero_iff p _).mp ?_, fun h => ?_⟩
  · have hn := congrArg (fun P : Polynomial _ => P.coeff n) h
    simpa only [Polynomial.coeff_map, Polynomial.coeff_zero] using hn
  · ext n
    rw [Polynomial.coeff_map, Polynomial.coeff_zero]
    exact (res_eq_zero_iff p _).mpr (h n)

scoped instance instIsFractionRing_R : IsFractionRing ↥(GaloisRep.ratLocalizedAt p) ℚ := GaloisRep.isFractionRing_ratLocalizedAt p

theorem ringHom_ext_R {S : Type*} [Semiring S] (f g : ↥(GaloisRep.ratLocalizedAt p) →+* S) : f = g := by
  haveI := GaloisRep.isLocalization_ratLocalizedAt (p := p) Fact.out
  exact IsLocalization.ringHom_ext (Ideal.span {(p : ℤ)}).primeCompl (RingHom.ext_int _ _)

theorem isScalarTower_R (Γ : Subgroup SL(2, ℤ)) (inst : Algebra ℚ ↥(qExpFunctionFieldC ℚ Γ)) :
    @IsScalarTower ↥(GaloisRep.ratLocalizedAt p) ℚ ↥(qExpFunctionFieldC ℚ Γ) _ (@Algebra.toSMul _ _ _ _ inst) _ :=
  @IsScalarTower.of_algebraMap_eq ↥(GaloisRep.ratLocalizedAt p) ℚ ↥(qExpFunctionFieldC ℚ Γ) _ _ _ _ inst _ fun a =>
    RingHom.congr_fun (ringHom_ext_R p (algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ))
      ((@algebraMap ℚ ↥(qExpFunctionFieldC ℚ Γ) _ _ inst).comp (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ))) a

scoped instance instIsScalarTower (Γ : Subgroup SL(2, ℤ)) : IsScalarTower ↥(GaloisRep.ratLocalizedAt p) ℚ ↥(qExpFunctionFieldC ℚ Γ) :=
  isScalarTower_R p Γ inferInstance

theorem coeffEmb_rat (x : LaurentSeries ℚ) : coeffEmb ℚ x = x := by
  ext k
  rw [coeffEmb_coeff]
  rfl

theorem coe_jAt_eq_coeffEmb (Γ : Subgroup SL(2, ℤ)) (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))) :
    ((jAt Γ hj : ↥(qExpFunctionFieldC ℚ Γ)) : LaurentSeries ℚ) = coeffEmb ℚ jq := by
  rw [coeffEmb_rat, coe_jAt]
  rfl

theorem transcendental_iff_of_inst (Γ : Subgroup SL(2, ℤ)) (i₁ i₂ : Algebra ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ))
    (x : ↥(qExpFunctionFieldC ℚ Γ)) :
    @Transcendental ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) _ _ i₁ x ↔
      @Transcendental ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) _ _ i₂ x := by
  have h : @algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) _ _ i₁ =
      @algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) _ _ i₂ := ringHom_ext_R p _ _
  unfold Transcendental IsAlgebraic
  refine not_congr ⟨?_, ?_⟩ <;> rintro ⟨q, hq, hx⟩ <;> refine ⟨q, hq, ?_⟩
  · rw [@Polynomial.aeval_def _ _ _ _ i₂, ← h, ← @Polynomial.aeval_def _ _ _ _ i₁]; exact hx
  · rw [@Polynomial.aeval_def _ _ _ _ i₁, h, ← @Polynomial.aeval_def _ _ _ _ i₂]; exact hx

p2m_attr_erase "instance" "DivisionRing.toRatAlgebra in"

theorem transcendental_jAt_IF (Γ : Subgroup SL(2, ℤ)) (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))) :
    Transcendental ↥(GaloisRep.ratLocalizedAt p) (jAt Γ hj) := by
  have hst := IsScalarTower.of_algebraMap_eq (R := ↥(GaloisRep.ratLocalizedAt p)) (S := ℚ)
    (A := ↥(qExpFunctionFieldC ℚ Γ)) (fun _ => rfl)
  exact @ModularCurve.transcendental_of_coe_eq_coeffEmb_jq ℚ _ _ (qExpFunctionFieldC ℚ Γ) ↥(GaloisRep.ratLocalizedAt p)
    _ _ _ _ _ hst (jAt Γ hj) (coe_jAt_eq_coeffEmb Γ hj)

theorem transcendental_jAt (Γ : Subgroup SL(2, ℤ)) (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))) :
    Transcendental ↥(GaloisRep.ratLocalizedAt p) (jAt Γ hj) :=
  (transcendental_iff_of_inst p Γ _ _ _).mp (transcendental_jAt_IF p Γ hj)

universe u in
theorem minimalPrimes_span_natCast_chartAlgFin_gammaH
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (hFD : FiniteDimensional ↥(IntermediateField.adjoin ℚ ({jAt (CohCarrier.GammaH M H) hj} : Set ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))))
      ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))
    (hsep : Algebra.IsSeparable ↥(IntermediateField.adjoin ℚ ({jAt (CohCarrier.GammaH M H) hj} : Set ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))))
      ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) :
    ∃ W₀ W₁ : ValuationSubring ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)),

      (∀ i : Fin 2, (∀ a : ↥(GaloisRep.ratLocalizedAt p), algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) a ∈ (![W₀, W₁] i)) ∧
        ∀ a ∈ Ideal.span {((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p))}, algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) a ∈ (![W₀, W₁] i).nonunits) ∧
      W₀ ≠ W₁ ∧
      (∀ i : Fin 2, ∀ x : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)), x ∈ (![W₀, W₁] i).nonunits →
        x * (algebraMap ↥(GaloisRep.ratLocalizedAt p) _ ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)))⁻¹ ∈ (![W₀, W₁] i)) ∧

      (∀ 𝔭 ∈ (Ideal.span {((p : ℕ) : ↥(chartAlgFin p (CohCarrier.GammaH M H) hj))}).minimalPrimes,
        (∀ b : ↥(chartAlgFin p (CohCarrier.GammaH M H) hj), b ∈ 𝔭 ↔ (b : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) ∈ W₀.nonunits) ∨
        (∀ b : ↥(chartAlgFin p (CohCarrier.GammaH M H) hj), b ∈ 𝔭 ↔ (b : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) ∈ W₁.nonunits)) ∧

      (∀ i : Fin 2, ∃ 𝔭 ∈ (Ideal.span {((p : ℕ) : ↥(chartAlgFin p (CohCarrier.GammaH M H) hj))}).minimalPrimes,
        ∀ b : ↥(chartAlgFin p (CohCarrier.GammaH M H) hj), b ∈ 𝔭 ↔ (b : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) ∈ (![W₀, W₁] i).nonunits) ∧

      (∃ b : ↥(chartAlgFin p (CohCarrier.GammaH M H) hj), (b : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) ∈ W₀.nonunits ∧
          (b : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) ∉ W₁.nonunits) ∧
      (∃ b : ↥(chartAlgFin p (CohCarrier.GammaH M H) hj), (b : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) ∈ W₁.nonunits ∧
          (b : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) ∉ W₀.nonunits) := by
  obtain ⟨W₀, W₁, h1, h2, h3, h5, h6⟩ := ModularCurve.XHDRLevel.exists_valuationSubring_pair_gammaH p M H hpM hpM2 hHp hj

  have h1' : ∀ i : Fin 2, (∀ a : ↥(GaloisRep.ratLocalizedAt p), algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) a ∈ (![W₀, W₁] i)) ∧
      ∀ a ∈ IsLocalRing.maximalIdeal ↥(GaloisRep.ratLocalizedAt p), algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) a ∈ (![W₀, W₁] i).nonunits :=
    fun i => ⟨(h1 i).1, fun a ha => (h1 i).2 a ((mem_maximalIdeal_iff_mem_span p a).mp ha)⟩
  have h2' : ∀ i : Fin 2, ∀ Q : Polynomial ↥(GaloisRep.ratLocalizedAt p), Q.map (IsLocalRing.residue ↥(GaloisRep.ratLocalizedAt p)) ≠ 0 →
      Polynomial.aeval (jAt (CohCarrier.GammaH M H) hj) Q ∈ (![W₀, W₁] i) ∧ (Polynomial.aeval (jAt (CohCarrier.GammaH M H) hj) Q)⁻¹ ∈ (![W₀, W₁] i) :=
    fun i Q hQ => h2 i Q ((map_residue_ne_zero_iff p Q).mp hQ)
  have h5' : ∀ V : ValuationSubring ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)),
      (∀ a : ↥(GaloisRep.ratLocalizedAt p), algebraMap ↥(GaloisRep.ratLocalizedAt p) _ a ∈ V) → (∀ a ∈ IsLocalRing.maximalIdeal ↥(GaloisRep.ratLocalizedAt p), algebraMap ↥(GaloisRep.ratLocalizedAt p) _ a ∈ V.nonunits) →
      (∀ Q : Polynomial ↥(GaloisRep.ratLocalizedAt p), Q.map (IsLocalRing.residue ↥(GaloisRep.ratLocalizedAt p)) ≠ 0 →
        Polynomial.aeval (jAt (CohCarrier.GammaH M H) hj) Q ∈ V ∧ (Polynomial.aeval (jAt (CohCarrier.GammaH M H) hj) Q)⁻¹ ∈ V) →
      V = W₀ ∨ V = W₁ :=
    fun V hV1 hV1' hV2 => h5 V hV1 (fun a ha => hV1' a ((mem_maximalIdeal_iff_mem_span p a).mpr ha))
      (fun Q hQ => hV2 Q ((map_residue_ne_zero_iff p Q).mpr hQ))
  haveI := hFD; haveI := hsep
  haveI := instIsScalarTower p (CohCarrier.GammaH M H)
  have hϖ : Ideal.span {algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(chartAlgFin p (CohCarrier.GammaH M H) hj) ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p))} =
      Ideal.span {((p : ℕ) : ↥(chartAlgFin p (CohCarrier.GammaH M H) hj))} := by rw [map_natCast]
  obtain ⟨hi, hii, hiii⟩ :=
    AlgebraicCurve.TwoChartIntegralModel.mem_minimalPrimes_span_iff_of_valuationSubring_pair
      ↥(GaloisRep.ratLocalizedAt p) ℚ ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) (jAt (CohCarrier.GammaH M H) hj)
      (transcendental_jAt p _ hj) hFD hsep ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)) (maximalIdeal_R p) W₀ W₁ h1' h2' h3 h5'
  rw [hϖ] at hi hii
  exact ⟨W₀, W₁, h1, h3, h6, hi, hii, hiii⟩

theorem kerMin_of_pair
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (hFD : FiniteDimensional ↥(IntermediateField.adjoin ℚ ({jAt (CohCarrier.GammaH M H) hj} : Set ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))
    (hsep : Algebra.IsSeparable ↥(IntermediateField.adjoin ℚ ({jAt (CohCarrier.GammaH M H) hj} : Set ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))
    (W₀ W₁ : ValuationSubring ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))
    (hW1 : ∀ i : Fin 2, (∀ a : ↥(GaloisRep.ratLocalizedAt p), algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) a ∈ (![W₀, W₁] i)) ∧
      ∀ a ∈ Ideal.span {((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p))}, algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) a ∈ (![W₀, W₁] i).nonunits)
    (hW2 : ∀ i : Fin 2, ∀ Q : Polynomial ↥(GaloisRep.ratLocalizedAt p), Q.map (GaloisRep.ratLocalizedAtResidue p) ≠ 0 →
      Polynomial.aeval (jAt (CohCarrier.GammaH M H) hj) Q ∈ (![W₀, W₁] i) ∧ (Polynomial.aeval (jAt (CohCarrier.GammaH M H) hj) Q)⁻¹ ∈ (![W₀, W₁] i))
    (hW3 : W₀ ≠ W₁)
    (hW5 : ∀ V : ValuationSubring ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)),
      (∀ a : ↥(GaloisRep.ratLocalizedAt p), algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) a ∈ V) →
      (∀ a ∈ Ideal.span {((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p))}, algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) a ∈ V.nonunits) →
      (∀ Q : Polynomial ↥(GaloisRep.ratLocalizedAt p), Q.map (GaloisRep.ratLocalizedAtResidue p) ≠ 0 →
        Polynomial.aeval (jAt (CohCarrier.GammaH M H) hj) Q ∈ V ∧ (Polynomial.aeval (jAt (CohCarrier.GammaH M H) hj) Q)⁻¹ ∈ V) →
      V = W₀ ∨ V = W₁) :
    (∀ 𝔭 ∈ (Ideal.span {((p : ℕ) : ↥(chartAlgFin p (CohCarrier.GammaH M H) hj))}).minimalPrimes,
      (∀ b : ↥(chartAlgFin p (CohCarrier.GammaH M H) hj), b ∈ 𝔭 ↔ ((b : ↥(chartAlgFin p (CohCarrier.GammaH M H) hj)) : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) ∈ W₀.nonunits) ∨
      (∀ b : ↥(chartAlgFin p (CohCarrier.GammaH M H) hj), b ∈ 𝔭 ↔ ((b : ↥(chartAlgFin p (CohCarrier.GammaH M H) hj)) : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) ∈ W₁.nonunits)) ∧
    (∀ i : Fin 2, ∃ 𝔭 ∈ (Ideal.span {((p : ℕ) : ↥(chartAlgFin p (CohCarrier.GammaH M H) hj))}).minimalPrimes,
      ∀ b : ↥(chartAlgFin p (CohCarrier.GammaH M H) hj), b ∈ 𝔭 ↔ ((b : ↥(chartAlgFin p (CohCarrier.GammaH M H) hj)) : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) ∈ (![W₀, W₁] i).nonunits) ∧
    (∃ b : ↥(chartAlgFin p (CohCarrier.GammaH M H) hj), ((b : ↥(chartAlgFin p (CohCarrier.GammaH M H) hj)) : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) ∈ W₀.nonunits ∧ ((b : ↥(chartAlgFin p (CohCarrier.GammaH M H) hj)) : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) ∉ W₁.nonunits) ∧
    (∃ b : ↥(chartAlgFin p (CohCarrier.GammaH M H) hj), ((b : ↥(chartAlgFin p (CohCarrier.GammaH M H) hj)) : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) ∈ W₁.nonunits ∧ ((b : ↥(chartAlgFin p (CohCarrier.GammaH M H) hj)) : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) ∉ W₀.nonunits) := by
  have h1' : ∀ i : Fin 2, (∀ a : ↥(GaloisRep.ratLocalizedAt p), algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) a ∈ (![W₀, W₁] i)) ∧
      ∀ a ∈ IsLocalRing.maximalIdeal ↥(GaloisRep.ratLocalizedAt p), algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) a ∈ (![W₀, W₁] i).nonunits :=
    fun i => ⟨(hW1 i).1, fun a ha => (hW1 i).2 a ((mem_maximalIdeal_iff_mem_span p a).mp ha)⟩
  have h2' : ∀ i : Fin 2, ∀ Q : Polynomial ↥(GaloisRep.ratLocalizedAt p), Q.map (IsLocalRing.residue ↥(GaloisRep.ratLocalizedAt p)) ≠ 0 →
      Polynomial.aeval (jAt (CohCarrier.GammaH M H) hj) Q ∈ (![W₀, W₁] i) ∧ (Polynomial.aeval (jAt (CohCarrier.GammaH M H) hj) Q)⁻¹ ∈ (![W₀, W₁] i) :=
    fun i Q hQ => hW2 i Q ((map_residue_ne_zero_iff p Q).mp hQ)
  have h5' : ∀ V : ValuationSubring ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)),
      (∀ a : ↥(GaloisRep.ratLocalizedAt p), algebraMap ↥(GaloisRep.ratLocalizedAt p) _ a ∈ V) → (∀ a ∈ IsLocalRing.maximalIdeal ↥(GaloisRep.ratLocalizedAt p), algebraMap ↥(GaloisRep.ratLocalizedAt p) _ a ∈ V.nonunits) →
      (∀ Q : Polynomial ↥(GaloisRep.ratLocalizedAt p), Q.map (IsLocalRing.residue ↥(GaloisRep.ratLocalizedAt p)) ≠ 0 →
        Polynomial.aeval (jAt (CohCarrier.GammaH M H) hj) Q ∈ V ∧ (Polynomial.aeval (jAt (CohCarrier.GammaH M H) hj) Q)⁻¹ ∈ V) →
      V = W₀ ∨ V = W₁ :=
    fun V hV1 hV1' hV2 => hW5 V hV1 (fun a ha => hV1' a ((mem_maximalIdeal_iff_mem_span p a).mpr ha))
      (fun Q hQ => hV2 Q ((map_residue_ne_zero_iff p Q).mpr hQ))
  haveI := hFD; haveI := hsep
  haveI := instIsScalarTower p (CohCarrier.GammaH M H)
  have hϖ : Ideal.span {algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(chartAlgFin p (CohCarrier.GammaH M H) hj) ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p))} = Ideal.span {((p : ℕ) : ↥(chartAlgFin p (CohCarrier.GammaH M H) hj))} := by rw [map_natCast]
  obtain ⟨hi, hii, hiii⟩ :=
    AlgebraicCurve.TwoChartIntegralModel.mem_minimalPrimes_span_iff_of_valuationSubring_pair
      ↥(GaloisRep.ratLocalizedAt p) ℚ ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) (jAt (CohCarrier.GammaH M H) hj) (transcendental_jAt p _ hj) hFD hsep ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)) (maximalIdeal_R p) W₀ W₁ h1' h2' hW3 h5'
  rw [hϖ] at hi hii
  exact ⟨hi, hii, hiii⟩

theorem finiteDimensional_adjoin_jAt (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))) :
    FiniteDimensional ↥(IntermediateField.adjoin ℚ ({jAt Γ hj} : Set ↥(qExpFunctionFieldC ℚ Γ))) ↥(qExpFunctionFieldC ℚ Γ) := by

  have h := (ModularCurve.finiteDimensional_and_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index ℚ Γ hT Γ le_rfl
    (fun γ hγ => Or.inl hγ) (jAt Γ hj) (coe_jAt Γ hj)).1
  convert h <;> exact Subsingleton.elim _ _

theorem isSeparable_adjoin_jAt (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))) :
    Algebra.IsSeparable ↥(IntermediateField.adjoin ℚ ({jAt Γ hj} : Set ↥(qExpFunctionFieldC ℚ Γ))) ↥(qExpFunctionFieldC ℚ Γ) := by
  haveI := finiteDimensional_adjoin_jAt Γ hT hj
  infer_instance

end ModularCurve.XHDRLevel.KerMinH
p2m_reactivate "P2MW.S_ModularCurve_XHDRLevel_map_span_natCast_eq_maximalIdeal_of_mem_minimalPrimes_chartAlg_gammaH.ModularCurve P2MW.S_ModularCurve_XHDRLevel_map_span_natCast_eq_maximalIdeal_of_mem_minimalPrimes_chartAlg_gammaH.ModularCurve.XHDRLevel P2MW.S_ModularCurve_XHDRLevel_map_span_natCast_eq_maximalIdeal_of_mem_minimalPrimes_chartAlg_gammaH.ModularCurve.XHDRLevel.KerMinH"
p2m_reactivate "P2MW.S_ModularCurve_XHDRLevel_map_span_natCast_eq_maximalIdeal_of_mem_minimalPrimes_chartAlg_gammaH.ModularCurve P2MW.S_ModularCurve_XHDRLevel_map_span_natCast_eq_maximalIdeal_of_mem_minimalPrimes_chartAlg_gammaH.ModularCurve.XHDRLevel"
p2m_reactivate "P2MW.S_ModularCurve_XHDRLevel_map_span_natCast_eq_maximalIdeal_of_mem_minimalPrimes_chartAlg_gammaH.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "qExpFunctionFieldC jq coeffEmb coeffEmb_coeff laurentBaseChange jqModC transcendental_of_coe_eq_coeffEmb_jq XHDRLevel.exists_valuationSubring_pair_gammaH finiteDimensional_and_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index"
namespace XHDRLevel
p2m_export "ModularCurve.XHDRLevel" "R jAt coe_jAt X chartAlgFin chartAlgInf exists_valuationSubring_pair_gammaH"
namespace MultOneH
p2m_open "ModularCurve.XHDRLevel ModularCurve"

variable (p : ℕ) [Fact p.Prime]

theorem gamma1_le_gammaH (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) : CongruenceSubgroup.Gamma1 M ≤ CohCarrier.GammaH M H := by
  intro γ hγ
  obtain ⟨-, h11, h10⟩ := (CongruenceSubgroup.Gamma1_mem M γ).mp hγ
  refine CohCarrier.mem_GammaH_iff.mpr ⟨CongruenceSubgroup.Gamma0_mem.mpr h10, ?_⟩
  have h1 : CohCarrier.gamma0Units M ⟨γ, CongruenceSubgroup.Gamma0_mem.mpr h10⟩ = 1 :=
    Units.ext (by rw [CohCarrier.val_gamma0Units, Units.val_one]; exact h11)
  rw [h1]
  exact Subgroup.one_mem _

theorem T_mem_gammaH (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) : ModularGroup.T ∈ CohCarrier.GammaH M H :=
  gamma1_le_gammaH M H (by rw [CongruenceSubgroup.Gamma1_mem]; refine ⟨?_, ?_, ?_⟩ <;> simp [ModularGroup.T])

scoped instance finiteIndex_gammaH (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) : (CohCarrier.GammaH M H).FiniteIndex := by
  haveI : (CongruenceSubgroup.Gamma1 M).FiniteIndex := CongruenceSubgroup.instFiniteIndexGamma1 M
  exact Subgroup.finiteIndex_of_le (gamma1_le_gammaH M H)

theorem C_dvd_reverse_iff {R : Type*} [CommRing R] (ϖ : R) (Q : Polynomial R) :
    Polynomial.C ϖ ∣ Q.reverse ↔ Polynomial.C ϖ ∣ Q := by
  rw [Polynomial.C_dvd_iff_dvd_coeff, Polynomial.C_dvd_iff_dvd_coeff]
  constructor
  · intro h n
    by_cases hn : n ≤ Q.natDegree
    · have := h (Polynomial.revAt Q.natDegree n)
      rwa [Polynomial.coeff_reverse, Polynomial.revAt_invol] at this
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_not_ge hn)]
      exact dvd_zero _
  · intro h n
    rw [Polynomial.coeff_reverse]
    exact h _

theorem aeval_mem_of_aeval_inv_mem {R F : Type*} [CommRing R] [Field F] [Algebra R F] (j : F) (hj : j ≠ 0) (ϖ : R)
    (V : ValuationSubring F)
    (hV : ∀ P : Polynomial R, ¬ (Polynomial.C ϖ ∣ P) → Polynomial.aeval j⁻¹ P ∈ V ∧ (Polynomial.aeval j⁻¹ P)⁻¹ ∈ V)
    (hX : ¬ (Polynomial.C ϖ ∣ (Polynomial.X : Polynomial R))) :
    ∀ Q : Polynomial R, ¬ (Polynomial.C ϖ ∣ Q) → Polynomial.aeval j Q ∈ V ∧ (Polynomial.aeval j Q)⁻¹ ∈ V := by
  intro Q hQ
  obtain ⟨hjinv, hj'⟩ := hV Polynomial.X hX
  rw [Polynomial.aeval_X] at hjinv hj'
  rw [inv_inv] at hj'
  obtain ⟨h1, h2⟩ := hV Q.reverse ((C_dvd_reverse_iff ϖ Q).not.mpr hQ)
  letI : Invertible j := invertibleOfNonzero hj
  have e : Polynomial.aeval j Q = Polynomial.aeval j⁻¹ Q.reverse * j ^ Q.natDegree := by
    rw [Polynomial.aeval_def, Polynomial.aeval_def, ← invOf_eq_inv, Polynomial.eval₂_reverse_mul_pow]
  refine ⟨?_, ?_⟩
  · rw [e]; exact mul_mem h1 (pow_mem hj' _)
  · rw [e, mul_inv, ← inv_pow]; exact mul_mem h2 (pow_mem hjinv _)

end ModularCurve.XHDRLevel.MultOneH
p2m_reactivate "P2MW.S_ModularCurve_XHDRLevel_map_span_natCast_eq_maximalIdeal_of_mem_minimalPrimes_chartAlg_gammaH.ModularCurve P2MW.S_ModularCurve_XHDRLevel_map_span_natCast_eq_maximalIdeal_of_mem_minimalPrimes_chartAlg_gammaH.ModularCurve.XHDRLevel P2MW.S_ModularCurve_XHDRLevel_map_span_natCast_eq_maximalIdeal_of_mem_minimalPrimes_chartAlg_gammaH.ModularCurve.XHDRLevel.KerMinH P2MW.S_ModularCurve_XHDRLevel_map_span_natCast_eq_maximalIdeal_of_mem_minimalPrimes_chartAlg_gammaH.ModularCurve.XHDRLevel.MultOneH"
p2m_reactivate "P2MW.S_ModularCurve_XHDRLevel_map_span_natCast_eq_maximalIdeal_of_mem_minimalPrimes_chartAlg_gammaH.ModularCurve P2MW.S_ModularCurve_XHDRLevel_map_span_natCast_eq_maximalIdeal_of_mem_minimalPrimes_chartAlg_gammaH.ModularCurve.XHDRLevel P2MW.S_ModularCurve_XHDRLevel_map_span_natCast_eq_maximalIdeal_of_mem_minimalPrimes_chartAlg_gammaH.ModularCurve.XHDRLevel.KerMinH"
p2m_reactivate "P2MW.S_ModularCurve_XHDRLevel_map_span_natCast_eq_maximalIdeal_of_mem_minimalPrimes_chartAlg_gammaH.ModularCurve P2MW.S_ModularCurve_XHDRLevel_map_span_natCast_eq_maximalIdeal_of_mem_minimalPrimes_chartAlg_gammaH.ModularCurve.XHDRLevel P2MW.S_ModularCurve_XHDRLevel_map_span_natCast_eq_maximalIdeal_of_mem_minimalPrimes_chartAlg_gammaH.ModularCurve.XHDRLevel.KerMinH"

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve ModularCurve P2MW.S_ModularCurve_XHDRLevel_map_span_natCast_eq_maximalIdeal_of_mem_minimalPrimes_chartAlg_gammaH.ModularCurve ModularCurve.XHDRLevel P2MW.S_ModularCurve_XHDRLevel_map_span_natCast_eq_maximalIdeal_of_mem_minimalPrimes_chartAlg_gammaH.ModularCurve.XHDRLevel"
open scoped MatrixGroups

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))) :
    (∀ (P : Ideal ↥(TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) (jAt (CohCarrier.GammaH M H) hj))) [P.IsPrime],
      P ∈ (Ideal.span {((p : ℕ) : ↥(TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) (jAt (CohCarrier.GammaH M H) hj)))}).minimalPrimes →
        Ideal.map (algebraMap ↥(TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) (jAt (CohCarrier.GammaH M H) hj)) (Localization.AtPrime P)) (Ideal.span {((p : ℕ) : ↥(TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) (jAt (CohCarrier.GammaH M H) hj)))}) =
          IsLocalRing.maximalIdeal (Localization.AtPrime P)) ∧
    (∀ (P : Ideal ↥(TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) (jAt (CohCarrier.GammaH M H) hj))) [P.IsPrime],
      P ∈ (Ideal.span {((p : ℕ) : ↥(TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) (jAt (CohCarrier.GammaH M H) hj)))}).minimalPrimes →
        Ideal.map (algebraMap ↥(TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) (jAt (CohCarrier.GammaH M H) hj)) (Localization.AtPrime P)) (Ideal.span {((p : ℕ) : ↥(TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) (jAt (CohCarrier.GammaH M H) hj)))}) =
          IsLocalRing.maximalIdeal (Localization.AtPrime P)) := by
  classical

  haveI := ModularCurve.XHDRLevel.KerMinH.instDVR_R p
  have hT := ModularCurve.XHDRLevel.MultOneH.T_mem_gammaH M H
  have hFD := ModularCurve.XHDRLevel.KerMinH.finiteDimensional_adjoin_jAt (CohCarrier.GammaH M H) hT hj
  have hsep := ModularCurve.XHDRLevel.KerMinH.isSeparable_adjoin_jAt (CohCarrier.GammaH M H) hT hj
  have htj := ModularCurve.XHDRLevel.KerMinH.transcendental_jAt p (CohCarrier.GammaH M H) hj
  have hprime := ModularCurve.XHDRLevel.KerMinH.prime_p p
  have hX : ¬ (Polynomial.C ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)) ∣ (Polynomial.X : Polynomial ↥(GaloisRep.ratLocalizedAt p))) := by
    rw [Polynomial.C_dvd_iff_dvd_coeff]
    intro h
    have := h 1
    rw [Polynomial.coeff_X_one] at this
    exact hprime.not_unit (isUnit_of_dvd_one this)

  obtain ⟨W₀, W₁, h1, h2, hne, h5, h6⟩ :=
    ModularCurve.XHDRLevel.exists_valuationSubring_pair_gammaH p M H hpM hpM2 hHp hj

  have hmult : ∀ V : ValuationSubring ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)), (∀ r : ↥(GaloisRep.ratLocalizedAt p), algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) r ∈ V) →
      algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)) ∈ V.nonunits →
      (∀ P : Polynomial ↥(GaloisRep.ratLocalizedAt p), ¬ (Polynomial.C ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)) ∣ P) →
        Polynomial.aeval (jAt (CohCarrier.GammaH M H) hj) P ∈ V ∧ (Polynomial.aeval (jAt (CohCarrier.GammaH M H) hj) P)⁻¹ ∈ V) →
      ∀ x : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)), x ∈ V.nonunits → x * (algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)))⁻¹ ∈ V := by
    intro V hRV hϖV hPV x hx

    have hV1' : ∀ a ∈ Ideal.span {((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p))}, algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) a ∈ V.nonunits := by
      intro a ha
      obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
      rw [map_mul]
      set P₀ : ↥V := ⟨_, V.nonunits_subset hϖV⟩ with hP₀
      set B₀ : ↥V := ⟨_, hRV b⟩ with hB₀
      have hx1 : P₀ ∈ IsLocalRing.maximalIdeal ↥V := (ValuationSubring.coe_mem_nonunits_iff (A := V)).mp hϖV
      have hx2 : B₀ * P₀ ∈ IsLocalRing.maximalIdeal ↥V := Ideal.mul_mem_left _ _ hx1
      have := (ValuationSubring.coe_mem_nonunits_iff (A := V)).mpr hx2
      exact this
    have hV2 : ∀ Q : Polynomial ↥(GaloisRep.ratLocalizedAt p), Q.map (GaloisRep.ratLocalizedAtResidue p) ≠ 0 →
        Polynomial.aeval (jAt (CohCarrier.GammaH M H) hj) Q ∈ V ∧ (Polynomial.aeval (jAt (CohCarrier.GammaH M H) hj) Q)⁻¹ ∈ V :=
      fun Q hQ => hPV Q ((ModularCurve.XHDRLevel.KerMinH.map_ne_zero_iff_not_C_dvd p Q).mp hQ)
    rcases h5 V hRV hV1' hV2 with rfl | rfl
    · exact h6 0 x hx
    · exact h6 1 x hx
  have hspanF : Ideal.span {((p : ℕ) : ↥(TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) (jAt (CohCarrier.GammaH M H) hj)))} = Ideal.span {algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) (jAt (CohCarrier.GammaH M H) hj)) ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p))} := by
    rw [map_natCast]
  refine ⟨fun P _ hP => ?_, fun P _ hP => ?_⟩
  ·
    rw [hspanF] at hP ⊢
    exact AlgebraicCurve.TwoChartIntegralModel.map_span_eq_maximalIdeal_localization_atPrime_of_forall_valuationSubring_mul_inv_mem
      ↥(GaloisRep.ratLocalizedAt p) ℚ ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) (jAt (CohCarrier.GammaH M H) hj) htj hFD hsep ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)) hprime hmult P hP
  ·
    haveI hfact : Fact (((jAt (CohCarrier.GammaH M H) hj))⁻¹ ≠ 0) := ⟨inv_ne_zero (Fact.out : (jAt (CohCarrier.GammaH M H) hj) ≠ 0)⟩
    have htj' : Transcendental ↥(GaloisRep.ratLocalizedAt p) ((jAt (CohCarrier.GammaH M H) hj))⁻¹ := fun h => htj (by simpa using h.inv)
    have hadj : IntermediateField.adjoin ℚ ({((jAt (CohCarrier.GammaH M H) hj))⁻¹} : Set ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) = IntermediateField.adjoin ℚ ({(jAt (CohCarrier.GammaH M H) hj)} : Set ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) := by
      apply le_antisymm
      · rw [IntermediateField.adjoin_simple_le_iff]
        exact inv_mem (IntermediateField.mem_adjoin_simple_self ℚ _)
      · rw [IntermediateField.adjoin_simple_le_iff]
        have h := inv_mem (IntermediateField.mem_adjoin_simple_self ℚ ((jAt (CohCarrier.GammaH M H) hj)⁻¹))
        rwa [inv_inv] at h
    have hFD' : FiniteDimensional ↥(IntermediateField.adjoin ℚ ({((jAt (CohCarrier.GammaH M H) hj))⁻¹} : Set ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) := by rw [hadj]; exact hFD
    have hsep' : Algebra.IsSeparable ↥(IntermediateField.adjoin ℚ ({((jAt (CohCarrier.GammaH M H) hj))⁻¹} : Set ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) := by rw [hadj]; exact hsep
    have hmult' : ∀ V : ValuationSubring ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)), (∀ r : ↥(GaloisRep.ratLocalizedAt p), algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) r ∈ V) →
        algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)) ∈ V.nonunits →
        (∀ P : Polynomial ↥(GaloisRep.ratLocalizedAt p), ¬ (Polynomial.C ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)) ∣ P) →
          Polynomial.aeval ((jAt (CohCarrier.GammaH M H) hj))⁻¹ P ∈ V ∧ (Polynomial.aeval ((jAt (CohCarrier.GammaH M H) hj))⁻¹ P)⁻¹ ∈ V) →
        ∀ x : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)), x ∈ V.nonunits → x * (algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)))⁻¹ ∈ V :=
      fun V hRV hϖV hPV => hmult V hRV hϖV
        (ModularCurve.XHDRLevel.MultOneH.aeval_mem_of_aeval_inv_mem (jAt (CohCarrier.GammaH M H) hj) (Fact.out : (jAt (CohCarrier.GammaH M H) hj) ≠ 0) _ V hPV hX)
    have hspanI : Ideal.span {((p : ℕ) : ↥(TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) (jAt (CohCarrier.GammaH M H) hj)))} =
        Ideal.span {algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) ((jAt (CohCarrier.GammaH M H) hj))⁻¹) ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p))} := by
      rw [map_natCast]
    rw [hspanI] at hP ⊢
    exact AlgebraicCurve.TwoChartIntegralModel.map_span_eq_maximalIdeal_localization_atPrime_of_forall_valuationSubring_mul_inv_mem
      ↥(GaloisRep.ratLocalizedAt p) ℚ ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) ((jAt (CohCarrier.GammaH M H) hj))⁻¹ htj' hFD' hsep' ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)) hprime hmult' P hP

end
p2m_reactivate "P2MW.S_ModularCurve_XHDRLevel_map_span_natCast_eq_maximalIdeal_of_mem_minimalPrimes_chartAlg_gammaH.ModularCurve P2MW.S_ModularCurve_XHDRLevel_map_span_natCast_eq_maximalIdeal_of_mem_minimalPrimes_chartAlg_gammaH.ModularCurve.XHDRLevel P2MW.S_ModularCurve_XHDRLevel_map_span_natCast_eq_maximalIdeal_of_mem_minimalPrimes_chartAlg_gammaH.ModularCurve.XHDRLevel.KerMinH P2MW.S_ModularCurve_XHDRLevel_map_span_natCast_eq_maximalIdeal_of_mem_minimalPrimes_chartAlg_gammaH.ModularCurve.XHDRLevel.MultOneH"

end S_ModularCurve_XHDRLevel_map_span_natCast_eq_maximalIdeal_of_mem_minimalPrimes_chartAlg_gammaH
end P2MW
export P2MW.S_ModularCurve_XHDRLevel_map_span_natCast_eq_maximalIdeal_of_mem_minimalPrimes_chartAlg_gammaH (solution)
