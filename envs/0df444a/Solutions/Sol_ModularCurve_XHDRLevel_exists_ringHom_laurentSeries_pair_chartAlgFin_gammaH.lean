-- Prove2me | solution 1 for ModularCurve.XHDRLevel.exists_ringHom_laurentSeries_pair_chartAlgFin_gammaH
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/61f51dd4-b93f-512e-9223-c0e5351d7360

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Theorems.Thm_ModularCurve_exists_valuationSubring_ringHom_laurentSeries_qExpFunctionFieldC_of_liesOverPrime
import Theorems.Thm_ModularCurve_qExpFunctionFieldC_gammaH_le_qExpFunctionFieldC_gammaH_infSubgroup
import Theorems.Thm_ModularCurve_exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed
import Theorems.Thm_ModularCurve_exists_coeffMap_eq_coe_of_mem_chartAlg_twoChartIntegralModel_qExpFunctionFieldC
import Theorems.Thm_GaloisRep_ratLocalizedAt_maximalIdeal_eq_span_natCast
import Theorems.Thm_GaloisRep_isLocalization_ratLocalizedAt
import Theorems.Thm_GaloisRep_isDiscreteValuationRing_ratLocalizedAt
import Theorems.Thm_ModularCurve_order_jqModC
import Theorems.Thm_ModularCurve_XHDRLevel_exists_valuationSubring_pair_gammaH
import Definitions.Def_GaloisRep_RatLocalizedAtResidue
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ModularCurve_QExpFrobeniusModL
import Definitions.Def_ModularCurve_LaurentCoeff
import Theorems.Thm_GaloisRep_isFractionRing_ratLocalizedAt
import Theorems.Thm_ModularCurve_transcendental_of_coe_eq_coeffEmb_jq
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_mem_minimalPrimes_span_iff_of_valuationSubring_pair
import Theorems.Thm_ModularCurve_finiteDimensional_and_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRLevel_exists_ringHom_laurentSeries_pair_chartAlgFin_gammaH
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation"
p2m_attr_erase "simp" "AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ"
p2m_attr_erase "simp" "ModularCurve.ProjectiveLine.map_mk ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring"

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

p2m_open "CategoryTheory AlgebraicCurve ModularCurve P2MW.S_ModularCurve_XHDRLevel_exists_ringHom_laurentSeries_pair_chartAlgFin_gammaH.ModularCurve ModularCurve.XHDRLevel P2MW.S_ModularCurve_XHDRLevel_exists_ringHom_laurentSeries_pair_chartAlgFin_gammaH.ModularCurve.XHDRLevel CongruenceSubgroup IsLocalRing"
open scoped MatrixGroups TensorProduct

section KerMinHGlue
p2m_open "ModularCurve P2MW.S_ModularCurve_XHDRLevel_exists_ringHom_laurentSeries_pair_chartAlgFin_gammaH.ModularCurve ModularCurve.XHDRLevel P2MW.S_ModularCurve_XHDRLevel_exists_ringHom_laurentSeries_pair_chartAlgFin_gammaH.ModularCurve.XHDRLevel AlgebraicCurve.TwoChartIntegralModel"
open scoped MatrixGroups
noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "Gamma1_le_GammaH qExpFunctionFieldC qExpand jq coeffMap coeffMap_coeff coeffMap_coeffMap coeffEmb coeffEmb_coeff qExpand_eq_pow_of_coeff_fixed jqModC coeffMap_qExpand exists_valuationSubring_ringHom_laurentSeries_qExpFunctionFieldC_of_liesOverPrime qExpFunctionFieldC_gammaH_le_qExpFunctionFieldC_gammaH_infSubgroup exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed exists_coeffMap_eq_coe_of_mem_chartAlg_twoChartIntegralModel_qExpFunctionFieldC order_jqModC XHDRLevel.exists_valuationSubring_pair_gammaH coeffSemilinearAut.coeffMap_qExpand coeffSemilinearAut transcendental_of_coe_eq_coeffEmb_jq finiteDimensional_and_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index"
namespace XHDRLevel
p2m_export "ModularCurve.XHDRLevel" "R jAt coe_jAt X chartAlgFin jChartFin ΓN ΓM exists_valuationSubring_pair_gammaH"
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
p2m_reactivate "P2MW.S_ModularCurve_XHDRLevel_exists_ringHom_laurentSeries_pair_chartAlgFin_gammaH.ModularCurve P2MW.S_ModularCurve_XHDRLevel_exists_ringHom_laurentSeries_pair_chartAlgFin_gammaH.ModularCurve.XHDRLevel P2MW.S_ModularCurve_XHDRLevel_exists_ringHom_laurentSeries_pair_chartAlgFin_gammaH.ModularCurve.XHDRLevel.KerMinH"
p2m_reactivate "P2MW.S_ModularCurve_XHDRLevel_exists_ringHom_laurentSeries_pair_chartAlgFin_gammaH.ModularCurve P2MW.S_ModularCurve_XHDRLevel_exists_ringHom_laurentSeries_pair_chartAlgFin_gammaH.ModularCurve.XHDRLevel"
p2m_reactivate "P2MW.S_ModularCurve_XHDRLevel_exists_ringHom_laurentSeries_pair_chartAlgFin_gammaH.ModularCurve"

end
p2m_reactivate "P2MW.S_ModularCurve_XHDRLevel_exists_ringHom_laurentSeries_pair_chartAlgFin_gammaH.ModularCurve P2MW.S_ModularCurve_XHDRLevel_exists_ringHom_laurentSeries_pair_chartAlgFin_gammaH.ModularCurve.XHDRLevel P2MW.S_ModularCurve_XHDRLevel_exists_ringHom_laurentSeries_pair_chartAlgFin_gammaH.ModularCurve.XHDRLevel.KerMinH"
end KerMinHGlue
p2m_reactivate "P2MW.S_ModularCurve_XHDRLevel_exists_ringHom_laurentSeries_pair_chartAlgFin_gammaH.ModularCurve P2MW.S_ModularCurve_XHDRLevel_exists_ringHom_laurentSeries_pair_chartAlgFin_gammaH.ModularCurve.XHDRLevel P2MW.S_ModularCurve_XHDRLevel_exists_ringHom_laurentSeries_pair_chartAlgFin_gammaH.ModularCurve.XHDRLevel.KerMinH"

namespace ThetaPairH

theorem Gamma1_le_GammaH (N : ℕ) (H : Subgroup (ZMod N)ˣ) : Gamma1 N ≤ CohCarrier.GammaH N H := by
  intro A hA
  rw [CohCarrier.mem_GammaH_iff]
  have hA' := (Gamma1_mem N A).mp hA
  have h0 : A ∈ Gamma0 N := by rw [Gamma0_mem]; exact hA'.2.2
  refine ⟨h0, ?_⟩
  have : CohCarrier.gamma0Units N ⟨A, h0⟩ = 1 := by
    ext
    rw [CohCarrier.val_gamma0Units]
    show ((A 1 1 : ℤ) : ZMod N) = ((1 : (ZMod N)ˣ) : ZMod N)
    rw [hA'.2.1, Units.val_one]
  rw [this]; exact one_mem H

scoped instance finiteIndex_GammaH (N : ℕ) [NeZero N] (H : Subgroup (ZMod N)ˣ) : (CohCarrier.GammaH N H).FiniteIndex :=
  Subgroup.finiteIndex_of_le (Gamma1_le_GammaH N H)

theorem T_mem_GammaH (N : ℕ) [NeZero N] (H : Subgroup (ZMod N)ˣ) : ModularGroup.T ∈ CohCarrier.GammaH N H := by
  rw [CohCarrier.mem_GammaH_iff]
  have h0 : ModularGroup.T ∈ Gamma0 N := by rw [Gamma0_mem]; simp [ModularGroup.T]
  refine ⟨h0, ?_⟩
  have : CohCarrier.gamma0Units N ⟨ModularGroup.T, h0⟩ = 1 := by
    ext
    rw [CohCarrier.val_gamma0Units]
    show ((ModularGroup.T 1 1 : ℤ) : ZMod N) = ((1 : (ZMod N)ˣ) : ZMod N)
    simp [ModularGroup.T]
  rw [this]; exact one_mem H

theorem comap_mem_minimalPrimes_of_inverse {A : Type*} [CommRing A] (I : Ideal A)
    (φ ψ : A →+* A) (h1 : ∀ a, ψ (φ a) = a) (h2 : ∀ b, φ (ψ b) = b)
    (hIφ : I ≤ I.comap φ) (hIψ : I ≤ I.comap ψ)
    {P : Ideal A} (hP : P ∈ I.minimalPrimes) : P.comap φ ∈ I.minimalPrimes := by
  have hPpr : P.IsPrime := hP.1.1
  refine ⟨⟨Ideal.IsPrime.comap φ, hIφ.trans (Ideal.comap_mono hP.1.2)⟩, ?_⟩
  rintro Q ⟨hQ, hIQ⟩ hle
  have hle' : Q.comap ψ ≤ P := by
    intro b hb
    rw [Ideal.mem_comap] at hb
    have := hle hb
    rw [Ideal.mem_comap, h2] at this
    exact this
  have hge : P ≤ Q.comap ψ := hP.2 ⟨Ideal.IsPrime.comap ψ, hIψ.trans (Ideal.comap_mono hIQ)⟩ hle'
  intro a ha
  rw [Ideal.mem_comap] at ha
  have := hge ha
  rw [Ideal.mem_comap, h1] at this
  exact this

end ThetaPairH
p2m_reactivate "P2MW.S_ModularCurve_XHDRLevel_exists_ringHom_laurentSeries_pair_chartAlgFin_gammaH.ModularCurve P2MW.S_ModularCurve_XHDRLevel_exists_ringHom_laurentSeries_pair_chartAlgFin_gammaH.ModularCurve.XHDRLevel P2MW.S_ModularCurve_XHDRLevel_exists_ringHom_laurentSeries_pair_chartAlgFin_gammaH.ModularCurve.XHDRLevel.KerMinH P2MW.S_ModularCurve_XHDRLevel_exists_ringHom_laurentSeries_pair_chartAlgFin_gammaH.ThetaPairH"

open ThetaPairH in
set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (iota0 : ↥(chartAlgFin p (ΓN p M H hpM) hj) →ₐ[R p] ↥(chartAlgFin p (ΓM M H) hj))
    (iota0_spec : ∀ b, (((iota0 b : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) =
      ((b : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ))
    (theta : ↥(chartAlgFin p (ΓM M H) hj) ≃ₐ[R p] ↥(chartAlgFin p (ΓM M H) hj))
    (htheta : ∀ b : ↥(chartAlgFin p (ΓN p M H hpM) hj),
      (((theta (iota0 b) : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) =
        qExpand ℚ p ((b : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ))
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ)) :
    ∃ θ : Fin 2 → (↥(chartAlgFin p (ΓM M H) hj) →+* LaurentSeries (IsLocalRing.ResidueField ↥A)),
      (∀ c, θ 1 c = θ 0 (theta c)) ∧
      (∀ (c : ↥(chartAlgFin p (ΓM M H) hj)) (y : LaurentSeries ↥A),
        coeffMap A.subtype y = coeffEmb (AlgebraicClosure ℚ) (((c : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) →
        θ 0 c = coeffMap (IsLocalRing.residue ↥A) y) ∧
      RingHom.ker (θ 0) ≠ RingHom.ker (θ 1) ∧
      (Ideal.span {((p : ℕ) : ↥(chartAlgFin p (ΓM M H) hj))}).minimalPrimes = {RingHom.ker (θ 0), RingHom.ker (θ 1)} ∧
      (∀ b : ↥(chartAlgFin p (ΓN p M H hpM) hj), θ 0 (theta (iota0 b)) = θ 0 (iota0 b) ^ p) ∧
      (∀ b : ↥(chartAlgFin p (ΓN p M H hpM) hj), θ 0 (theta (iota0 b)) = qExpand (IsLocalRing.ResidueField ↥A) p (θ 0 (iota0 b))) ∧
      (∀ c : R p, θ 0 (algebraMap (R p) ↥(chartAlgFin p (ΓM M H) hj) c) = HahnSeries.C ((IsLocalRing.residue ↥A) (ρ c))) ∧
      (∀ c : ↥(chartAlgFin p (ΓM M H) hj), θ 0 c ∈ qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM)) := by
  have hp : p.Prime := Fact.out
  haveI : IsDiscreteValuationRing (R p) := GaloisRep.isDiscreteValuationRing_ratLocalizedAt p hp

  obtain ⟨x, hx, -, -⟩ := ModularCurve.exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed
    (IsLocalRing.ResidueField ↥A) (ΓM M H) (T_mem_GammaH M H)

  obtain ⟨V, hRV, ρV, hpV, hgauss, hvan, hconst, hjV, hadj, hmemV, hreadV⟩ :=
    ModularCurve.exists_valuationSubring_ringHom_laurentSeries_qExpFunctionFieldC_of_liesOverPrime (ΓM M H)
      (T_mem_GammaH M H) p (jAt (ΓM M H) hj) (coe_jAt _ _) A hA ρ hρ x hx

  have hjmem : (jAt (ΓM M H) hj : ↥(qExpFunctionFieldC ℚ (ΓM M H))) ∈ V := by
    have h := (hgauss Polynomial.X ?_).1
    · simpa using h
    · intro hdvd
      rw [Polynomial.C_dvd_iff_dvd_coeff] at hdvd
      have h1 := hdvd 1
      rw [Polynomial.coeff_X_one] at h1
      have hu : IsUnit ((p : ℕ) : R p) := isUnit_of_dvd_one h1
      have hmem : ((p : ℕ) : R p) ∈ IsLocalRing.maximalIdeal (R p) := by
        rw [GaloisRep.ratLocalizedAt.maximalIdeal_eq_span_natCast p hp]
        exact Ideal.subset_span rfl
      exact (IsLocalRing.mem_maximalIdeal _).mp hmem hu

  let VS : Subalgebra (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) :=
    { carrier := V
      mul_mem' := fun ha hb => V.mul_mem _ _ ha hb
      one_mem' := V.one_mem
      add_mem' := fun ha hb => V.add_mem _ _ ha hb
      zero_mem' := V.zero_mem
      algebraMap_mem' := hRV }
  have hadjV : Algebra.adjoin (R p) ({(jAt (ΓM M H) hj : ↥(qExpFunctionFieldC ℚ (ΓM M H)))} : Set ↥(qExpFunctionFieldC ℚ (ΓM M H))) ≤ VS :=
    Algebra.adjoin_le (Set.singleton_subset_iff.mpr hjmem)
  have hOV : ∀ c : ↥(chartAlgFin p (ΓM M H) hj), ((c : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) ∈ V := by
    intro c
    have hint : IsIntegral ↥(Algebra.adjoin (R p) ({(jAt (ΓM M H) hj : ↥(qExpFunctionFieldC ℚ (ΓM M H)))} : Set ↥(qExpFunctionFieldC ℚ (ΓM M H)))) (c : ↥(qExpFunctionFieldC ℚ (ΓM M H))) :=
      (TwoChartIntegralModel.mem_chartAlg_iff (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H))).mp c.2

    let φ : ↥(Algebra.adjoin (R p) ({(jAt (ΓM M H) hj : ↥(qExpFunctionFieldC ℚ (ΓM M H)))} : Set ↥(qExpFunctionFieldC ℚ (ΓM M H)))) →+* ↥V :=
      (Algebra.adjoin (R p) ({(jAt (ΓM M H) hj : ↥(qExpFunctionFieldC ℚ (ΓM M H)))} : Set ↥(qExpFunctionFieldC ℚ (ΓM M H)))).val.toRingHom.codRestrict V
        (fun a => hadjV a.2)
    obtain ⟨P, hPm, hP0⟩ := hint
    have hintV : IsIntegral ↥V (c : ↥(qExpFunctionFieldC ℚ (ΓM M H))) := by
      refine ⟨P.map φ, hPm.map φ, ?_⟩
      rw [Polynomial.eval₂_map]
      exact hP0
    obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ↥V) (K := ↥(qExpFunctionFieldC ℚ (ΓM M H)))).mp hintV
    rw [← hy]
    exact y.2

  let incl : ↥(chartAlgFin p (ΓM M H) hj) →+* ↥V := (chartAlgFin p (ΓM M H) hj).val.toRingHom.codRestrict V hOV
  let θ₀ : ↥(chartAlgFin p (ΓM M H) hj) →+* LaurentSeries (IsLocalRing.ResidueField ↥A) := ρV.comp incl
  let θ₁ : ↥(chartAlgFin p (ΓM M H) hj) →+* LaurentSeries (IsLocalRing.ResidueField ↥A) := θ₀.comp theta.toRingEquiv.toRingHom
  have hθ₀ : ∀ c : ↥(chartAlgFin p (ΓM M H) hj), θ₀ c = ρV ⟨(c : ↥(qExpFunctionFieldC ℚ (ΓM M H))), hOV c⟩ := fun c => rfl

  have hread : ∀ (c : ↥(chartAlgFin p (ΓM M H) hj)) (y : LaurentSeries ↥A),
      coeffMap A.subtype y = coeffEmb (AlgebraicClosure ℚ) (((c : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) →
      θ₀ c = coeffMap (IsLocalRing.residue ↥A) y := by
    intro c y hy
    rw [hθ₀]
    have h := hreadV ⟨(c : ↥(qExpFunctionFieldC ℚ (ΓM M H))), hOV c⟩ 1 y (by rw [map_one]; exact one_ne_zero) (by rw [map_one, mul_one]; exact hy.symm)
    rwa [map_one, mul_one] at h

  have hlift := (ModularCurve.exists_coeffMap_eq_coe_of_mem_chartAlg_twoChartIntegralModel_qExpFunctionFieldC
    (ΓN p M H hpM) p (jAt (ΓN p M H hpM) hj) (coe_jAt _ _)).1

  have hext : ∀ {T : Type} [CommRing T] (f g : R p →+* T), f = g := by
    intro T _ f g
    haveI := GaloisRep.isLocalization_ratLocalizedAt (p := p) hp
    exact IsLocalization.ringHom_ext (Ideal.primeCompl (Ideal.span {(p : ℤ)})) (Subsingleton.elim _ _)
  have hAρ : ∀ y : LaurentSeries (R p), coeffMap A.subtype (coeffMap ρ y) =
      coeffEmb (AlgebraicClosure ℚ) (coeffMap (algebraMap (R p) ℚ) y) := by
    intro y
    show coeffMap A.subtype (coeffMap ρ y) = coeffMap (algebraMap ℚ (AlgebraicClosure ℚ)) (coeffMap (algebraMap (R p) ℚ) y)
    rw [ModularCurve.coeffMap_coeffMap, ModularCurve.coeffMap_coeffMap, hρ,
      hext (algebraMap (R p) (AlgebraicClosure ℚ)) ((algebraMap ℚ (AlgebraicClosure ℚ)).comp (algebraMap (R p) ℚ))]
  have hfix : ∀ (y : LaurentSeries (R p)) (k : ℤ),
      ((coeffMap ((IsLocalRing.residue ↥A).comp ρ) y).coeff k) ^ p = (coeffMap ((IsLocalRing.residue ↥A).comp ρ) y).coeff k := by
    intro y k
    rw [ModularCurve.coeffMap_coeff]
    have h := congrArg (fun f : R p →+* IsLocalRing.ResidueField ↥A => f (y.coeff k))
      (hext ((frobenius (IsLocalRing.ResidueField ↥A) p).comp ((IsLocalRing.residue ↥A).comp ρ)) ((IsLocalRing.residue ↥A).comp ρ))
    simpa [frobenius] using h
  have hfrob : ∀ b : ↥(chartAlgFin p (ΓN p M H hpM) hj), θ₀ (theta (iota0 b)) = θ₀ (iota0 b) ^ p ∧
      θ₀ (theta (iota0 b)) = qExpand (IsLocalRing.ResidueField ↥A) p (θ₀ (iota0 b)) := by
    intro b
    obtain ⟨y, hy⟩ := hlift b
    have h0 : θ₀ (iota0 b) = coeffMap ((IsLocalRing.residue ↥A).comp ρ) y := by
      rw [← ModularCurve.coeffMap_coeffMap]
      apply hread (iota0 b) (coeffMap ρ y)
      rw [hAρ, hy, iota0_spec]
    have h1 : θ₀ (theta (iota0 b)) = coeffMap ((IsLocalRing.residue ↥A).comp ρ) (qExpand (R p) p y) := by
      rw [← ModularCurve.coeffMap_coeffMap]
      apply hread (theta (iota0 b)) (coeffMap ρ (qExpand (R p) p y))
      rw [hAρ, ModularCurve.coeffSemilinearAut.coeffMap_qExpand, hy, htheta]
    have h2 : θ₀ (theta (iota0 b)) = qExpand (IsLocalRing.ResidueField ↥A) p (θ₀ (iota0 b)) := by
      rw [h1, h0, ModularCurve.coeffSemilinearAut.coeffMap_qExpand]
    refine ⟨?_, h2⟩
    rw [h2, h0, ModularCurve.qExpand_eq_pow_of_coeff_fixed (IsLocalRing.ResidueField ↥A) p _ (hfix y)]

  have hne : RingHom.ker θ₀ ≠ RingHom.ker θ₁ := by
    intro heq
    have hiff : ∀ u : ↥(chartAlgFin p (ΓM M H) hj), θ₀ u = 0 ↔ θ₀ (theta u) = 0 := by
      intro u
      have := SetLike.ext_iff.mp heq u
      simp only [RingHom.mem_ker] at this
      exact this

    set b : ↥(chartAlgFin p (ΓN p M H hpM) hj) := jChartFin p (ΓN p M H hpM) hj with hb
    set c : ↥(chartAlgFin p (ΓM M H) hj) := iota0 b with hc
    have hcj : ((c : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) = jAt (ΓM M H) hj := by
      apply Subtype.ext
      rw [hc, iota0_spec]
      rfl
    have hθc : θ₀ c = jqModC (IsLocalRing.ResidueField ↥A) := by
      rw [hθ₀]
      exact hjV ⟨(c : ↥(qExpFunctionFieldC ℚ (ΓM M H))), hOV c⟩ hcj

    have hu : θ₀ (theta c - c ^ p) = 0 := by
      rw [map_sub, map_pow, (hfrob b).1, sub_self]
    have hu' : θ₀ (theta.symm (theta c - c ^ p)) = 0 := by
      rw [hiff, AlgEquiv.apply_symm_apply]
      exact hu
    rw [map_sub, map_pow, AlgEquiv.symm_apply_apply, map_sub, map_pow, sub_eq_zero, hθc] at hu'

    have hord := congrArg HahnSeries.order hu'
    rw [ModularCurve.order_jqModC, HahnSeries.order_pow] at hord
    have hp2 : (2 : ℤ) ≤ p := by exact_mod_cast hp.two_le
    have : (p : ℤ) ∣ (-1 : ℤ) := ⟨_, by rw [hord, nsmul_eq_mul]⟩
    have h1 : (p : ℤ) ∣ 1 := (Int.dvd_neg).mp this
    have := Int.le_of_dvd one_pos h1
    omega

  have hker0 : ∀ b : ↥(chartAlgFin p (ΓM M H) hj), b ∈ RingHom.ker θ₀ ↔ ((b : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) ∈ V.nonunits := by
    intro b
    rw [RingHom.mem_ker]
    constructor
    · intro hb0
      by_contra hnu

      have hv1 : V.valuation ((b : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) = 1 :=
        le_antisymm (V.valuation_le_one ⟨_, hOV b⟩) (not_lt.mp (fun h => hnu ((V.mem_nonunits_iff).mpr h)))
      have hu : IsUnit (⟨((b : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))), hOV b⟩ : ↥V) := (V.valuation_eq_one_iff _).mpr hv1
      have := hu.map ρV
      rw [← hθ₀, hb0] at this
      exact not_isUnit_zero this
    · intro hb
      rw [hθ₀]
      exact hvan _ hb
  have hker1 : RingHom.ker θ₁ = (RingHom.ker θ₀).comap theta.toRingEquiv.toRingHom := by
    rw [RingHom.comap_ker]

  obtain ⟨W₀, W₁, hW1, hW2, hW3, hW5, hW6⟩ :=
    ModularCurve.XHDRLevel.exists_valuationSubring_pair_gammaH p M H hpM hpM2 hHp hj
  have kermin :
      (∀ 𝔭 ∈ (Ideal.span {((p : ℕ) : ↥(chartAlgFin p (ΓM M H) hj))}).minimalPrimes,
        (∀ b : ↥(chartAlgFin p (ΓM M H) hj), b ∈ 𝔭 ↔ ((b : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) ∈ W₀.nonunits) ∨
        (∀ b : ↥(chartAlgFin p (ΓM M H) hj), b ∈ 𝔭 ↔ ((b : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) ∈ W₁.nonunits)) ∧
      (∀ i : Fin 2, ∃ 𝔭 ∈ (Ideal.span {((p : ℕ) : ↥(chartAlgFin p (ΓM M H) hj))}).minimalPrimes,
        ∀ b : ↥(chartAlgFin p (ΓM M H) hj), b ∈ 𝔭 ↔ ((b : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) ∈ (![W₀, W₁] i).nonunits) ∧
      (∃ b : ↥(chartAlgFin p (ΓM M H) hj), ((b : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) ∈ W₀.nonunits ∧ ((b : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) ∉ W₁.nonunits) ∧
      (∃ b : ↥(chartAlgFin p (ΓM M H) hj), ((b : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) ∈ W₁.nonunits ∧ ((b : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) ∉ W₀.nonunits) := by
    exact ModularCurve.XHDRLevel.KerMinH.kerMin_of_pair p M H hj
      (ModularCurve.XHDRLevel.KerMinH.finiteDimensional_adjoin_jAt (ΓM M H) (T_mem_GammaH M H) hj)
      (ModularCurve.XHDRLevel.KerMinH.isSeparable_adjoin_jAt (ΓM M H) (T_mem_GammaH M H) hj) W₀ W₁ hW1 hW2 hW3 hW5
  obtain ⟨kmi, kmii, kmiii0, kmiii1⟩ := kermin

  have hVW : V = W₀ ∨ V = W₁ := by
    refine hW5 V hRV ?_ ?_
    · intro a ha
      rw [Ideal.mem_span_singleton] at ha
      obtain ⟨t, rfl⟩ := ha
      have hx : V.valuation (algebraMap (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) ((p : ℕ) : R p)) < 1 := (V.mem_nonunits_iff).mp hpV
      have hy : V.valuation (algebraMap (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) t) ≤ 1 := V.valuation_le_one ⟨_, hRV t⟩
      rw [V.mem_nonunits_iff, map_mul, map_mul]
      calc V.valuation (algebraMap (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) ((p : ℕ) : R p)) * V.valuation (algebraMap (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) t)
          ≤ V.valuation (algebraMap (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) ((p : ℕ) : R p)) * 1 := mul_le_mul_right hy _
        _ < 1 := by rw [mul_one]; exact hx
    · intro Q hQ
      apply hgauss Q
      rintro ⟨Q', rfl⟩
      apply hQ
      rw [Polynomial.map_mul, Polynomial.map_C, map_natCast, ZMod.natCast_self, map_zero, zero_mul]
  refine ⟨![θ₀, θ₁], fun c => rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    exact hread
  · exact hne
  ·
    show (Ideal.span {((p : ℕ) : ↥(chartAlgFin p (ΓM M H) hj))}).minimalPrimes = {RingHom.ker θ₀, RingHom.ker θ₁}
    obtain ⟨𝔭₀, h𝔭₀min, h𝔭₀mem⟩ := kmii 0
    obtain ⟨𝔭₁, h𝔭₁min, h𝔭₁mem⟩ := kmii 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h𝔭₀mem h𝔭₁mem
    have uniq0 : ∀ Q : Ideal ↥(chartAlgFin p (ΓM M H) hj), (∀ b, b ∈ Q ↔ ((b : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) ∈ W₀.nonunits) → Q = 𝔭₀ :=
      fun Q hQ => Ideal.ext fun b => (hQ b).trans (h𝔭₀mem b).symm
    have uniq1 : ∀ Q : Ideal ↥(chartAlgFin p (ΓM M H) hj), (∀ b, b ∈ Q ↔ ((b : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) ∈ W₁.nonunits) → Q = 𝔭₁ :=
      fun Q hQ => Ideal.ext fun b => (hQ b).trans (h𝔭₁mem b).symm
    have h𝔭ne : 𝔭₀ ≠ 𝔭₁ := by
      obtain ⟨b, hb0, hb1⟩ := kmiii0
      intro heq
      exact hb1 ((h𝔭₁mem b).mp (heq ▸ (h𝔭₀mem b).mpr hb0))

    have hk0 : RingHom.ker θ₀ = 𝔭₀ ∨ RingHom.ker θ₀ = 𝔭₁ := by
      rcases hVW with hV | hV
      · left; exact uniq0 _ (fun b => by rw [hker0, hV])
      · right; exact uniq1 _ (fun b => by rw [hker0, hV])
    have hk0min : RingHom.ker θ₀ ∈ (Ideal.span {((p : ℕ) : ↥(chartAlgFin p (ΓM M H) hj))}).minimalPrimes := by
      rcases hk0 with h | h <;> rw [h]
      · exact h𝔭₀min
      · exact h𝔭₁min

    have hpfix : ∀ (e : ↥(chartAlgFin p (ΓM M H) hj) ≃ₐ[R p] ↥(chartAlgFin p (ΓM M H) hj)), (Ideal.span {((p : ℕ) : ↥(chartAlgFin p (ΓM M H) hj))}) ≤ (Ideal.span {((p : ℕ) : ↥(chartAlgFin p (ΓM M H) hj))}).comap e.toRingEquiv.toRingHom := by
      intro e
      rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap]
      have : e.toRingEquiv.toRingHom ((p : ℕ) : ↥(chartAlgFin p (ΓM M H) hj)) = ((p : ℕ) : ↥(chartAlgFin p (ΓM M H) hj)) := map_natCast _ p
      rw [this]
      exact Ideal.subset_span rfl
    have hk1min : RingHom.ker θ₁ ∈ (Ideal.span {((p : ℕ) : ↥(chartAlgFin p (ΓM M H) hj))}).minimalPrimes := by
      rw [hker1]
      exact comap_mem_minimalPrimes_of_inverse _ theta.toRingEquiv.toRingHom theta.symm.toRingEquiv.toRingHom
        (fun a => theta.symm_apply_apply a) (fun b => theta.apply_symm_apply b) (hpfix theta) (hpfix theta.symm) hk0min
    have hk1 : RingHom.ker θ₁ = 𝔭₀ ∨ RingHom.ker θ₁ = 𝔭₁ := by
      rcases kmi _ hk1min with h | h
      · left; exact uniq0 _ h
      · right; exact uniq1 _ h

    have hmin : (Ideal.span {((p : ℕ) : ↥(chartAlgFin p (ΓM M H) hj))}).minimalPrimes = {𝔭₀, 𝔭₁} := by
      ext Q
      constructor
      · intro hQ
        rcases kmi Q hQ with h | h
        · rw [uniq0 Q h]; exact Set.mem_insert _ _
        · rw [uniq1 Q h]; exact Set.mem_insert_of_mem _ rfl
      · intro hQ
        rcases hQ with h | h
        · rw [h]; exact h𝔭₀min
        · rw [Set.mem_singleton_iff.mp h]; exact h𝔭₁min
    rw [hmin]

    rcases hk0 with h0 | h0 <;> rcases hk1 with h1 | h1
    · exact absurd (h0.trans h1.symm) hne
    · rw [h0, h1]
    · rw [h0, h1, Set.pair_comm]
    · exact absurd (h0.trans h1.symm) hne
  ·
    intro b
    obtain ⟨hb, hb'⟩ := hfrob b
    exact hb
  ·
    intro b
    exact (hfrob b).2
  ·
    intro c
    show θ₀ _ = _
    rw [hθ₀]
    have e1 : (⟨((algebraMap (R p) ↥(chartAlgFin p (ΓM M H) hj) c : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))), hOV _⟩ : ↥V) =
        ⟨algebraMap (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) c, hRV c⟩ := Subtype.ext rfl
    rw [e1, hconst c]
    have t1 : @algebraMap (R p) (IsLocalRing.ResidueField ↥A) _ _ ((IsLocalRing.residue ↥A).comp ρ).toAlgebra c = (IsLocalRing.residue ↥A) (ρ c) :=
      rfl
    have t2 : ∀ z : IsLocalRing.ResidueField ↥A, algebraMap (IsLocalRing.ResidueField ↥A) (LaurentSeries (IsLocalRing.ResidueField ↥A)) z = HahnSeries.C z := fun z => by
      simp [HahnSeries.algebraMap_apply']
    rw [t1, t2]
  ·
    intro c
    show θ₀ c ∈ _
    have hle := ModularCurve.qExpFunctionFieldC_gammaH_le_qExpFunctionFieldC_gammaH_infSubgroup p M hpM hpM2 H hHp (IsLocalRing.ResidueField ↥A)
    apply hle
    rw [← hadj, hθ₀]
    exact IntermediateField.subset_adjoin _ _ ⟨_, rfl⟩

end S_ModularCurve_XHDRLevel_exists_ringHom_laurentSeries_pair_chartAlgFin_gammaH
end P2MW
export P2MW.S_ModularCurve_XHDRLevel_exists_ringHom_laurentSeries_pair_chartAlgFin_gammaH (solution)
