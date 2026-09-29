-- Prove2me | solution 1 for ModularCurve.XHDRLevel.coe_theta_eq_of_forall_coe_iota0_of_qExpand
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/c9135adf-739a-5f4c-b158-dc64743274b6

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_GaloisRep_RatLocalizedAtResidue
import Theorems.Thm_ModularCurve_XHDRLevel_algEquiv_eq_refl_of_forall_coe_eq_gammaH_infSubgroup
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isFractionRing_chartAlg
import Theorems.Thm_GaloisRep_isDiscreteValuationRing_ratLocalizedAt
import Theorems.Thm_GaloisRep_ratLocalizedAt_maximalIdeal_eq_span_natCast
import Theorems.Thm_GaloisRep_isFractionRing_ratLocalizedAt
import Theorems.Thm_GaloisRep_isLocalization_ratLocalizedAt
import Theorems.Thm_ModularCurve_transcendental_of_coe_eq_coeffEmb_jq
import Theorems.Thm_ModularCurve_finiteDimensional_and_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_mem_minimalPrimes_span_iff_of_valuationSubring_pair
import Theorems.Thm_ModularCurve_XHDRLevel_exists_valuationSubring_pair_gammaH
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRLevel_coe_theta_eq_of_forall_coe_iota0_of_qExpand
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid"
p2m_attr_erase "simp" "ModularCurve.coe_jqNGen ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk"
p2m_attr_erase "simp" "ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.ProjectiveLine.map_mk"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve ModularCurve P2MW.S_ModularCurve_XHDRLevel_coe_theta_eq_of_forall_coe_iota0_of_qExpand.ModularCurve ModularCurve.XHDRLevel P2MW.S_ModularCurve_XHDRLevel_coe_theta_eq_of_forall_coe_iota0_of_qExpand.ModularCurve.XHDRLevel"
open scoped MatrixGroups TensorProduct

set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "infSubgroup qExpFunctionFieldC qExpand jq coeffEmb coeffEmb_coeff jqModC XHDRLevel.algEquiv_eq_refl_of_forall_coe_eq_gammaH_infSubgroup transcendental_of_coe_eq_coeffEmb_jq finiteDimensional_and_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index XHDRLevel.exists_valuationSubring_pair_gammaH"
namespace XHDRLevel
p2m_export "ModularCurve.XHDRLevel" "R jAt coe_jAt chartAlgFin ΓN ΓM algEquiv_eq_refl_of_forall_coe_eq_gammaH_infSubgroup exists_valuationSubring_pair_gammaH"
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
p2m_reactivate "P2MW.S_ModularCurve_XHDRLevel_coe_theta_eq_of_forall_coe_iota0_of_qExpand.ModularCurve P2MW.S_ModularCurve_XHDRLevel_coe_theta_eq_of_forall_coe_iota0_of_qExpand.ModularCurve.XHDRLevel P2MW.S_ModularCurve_XHDRLevel_coe_theta_eq_of_forall_coe_iota0_of_qExpand.ModularCurve.XHDRLevel.KerMinH"
p2m_reactivate "P2MW.S_ModularCurve_XHDRLevel_coe_theta_eq_of_forall_coe_iota0_of_qExpand.ModularCurve P2MW.S_ModularCurve_XHDRLevel_coe_theta_eq_of_forall_coe_iota0_of_qExpand.ModularCurve.XHDRLevel"
p2m_reactivate "P2MW.S_ModularCurve_XHDRLevel_coe_theta_eq_of_forall_coe_iota0_of_qExpand.ModularCurve"

namespace HDictS1

p2m_open "ModularCurve P2MW.S_ModularCurve_XHDRLevel_coe_theta_eq_of_forall_coe_iota0_of_qExpand.ModularCurve ModularCurve.XHDRLevel P2MW.S_ModularCurve_XHDRLevel_coe_theta_eq_of_forall_coe_iota0_of_qExpand.ModularCurve.XHDRLevel"

variable (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ)

theorem gamma1_le_gammaH : CongruenceSubgroup.Gamma1 M ≤ CohCarrier.GammaH M H := by
  intro A hA
  rw [CongruenceSubgroup.Gamma1_mem] at hA
  obtain ⟨h00, h11, h10⟩ := hA
  have hA0 : A ∈ CongruenceSubgroup.Gamma0 M := CongruenceSubgroup.Gamma0_mem.mpr h10
  refine CohCarrier.mem_GammaH_iff.mpr ⟨hA0, ?_⟩
  have : CohCarrier.gamma0Units M ⟨A, hA0⟩ = 1 := by
    apply Units.ext
    rw [CohCarrier.val_gamma0Units, Units.val_one]
    exact h11
  rw [this]; exact one_mem _

scoped instance finiteIndex_gammaH : (CohCarrier.GammaH M H).FiniteIndex :=
  Subgroup.finiteIndex_of_le (gamma1_le_gammaH M H)

theorem T_mem_gammaH : ModularGroup.T ∈ CohCarrier.GammaH M H := by
  apply gamma1_le_gammaH
  rw [CongruenceSubgroup.Gamma1_mem]
  simp [ModularGroup.T]

end HDictS1
p2m_reactivate "P2MW.S_ModularCurve_XHDRLevel_coe_theta_eq_of_forall_coe_iota0_of_qExpand.ModularCurve P2MW.S_ModularCurve_XHDRLevel_coe_theta_eq_of_forall_coe_iota0_of_qExpand.ModularCurve.XHDRLevel P2MW.S_ModularCurve_XHDRLevel_coe_theta_eq_of_forall_coe_iota0_of_qExpand.ModularCurve.XHDRLevel.KerMinH P2MW.S_ModularCurve_XHDRLevel_coe_theta_eq_of_forall_coe_iota0_of_qExpand.HDictS1"

namespace RigTheta

p2m_open "ModularCurve P2MW.S_ModularCurve_XHDRLevel_coe_theta_eq_of_forall_coe_iota0_of_qExpand.ModularCurve ModularCurve.XHDRLevel P2MW.S_ModularCurve_XHDRLevel_coe_theta_eq_of_forall_coe_iota0_of_qExpand.ModularCurve.XHDRLevel"

theorem commutes_rat {F : Type*} [Field F] [CharZero F] [Algebra ℚ F] (g : F →+* F) (r : ℚ) :
    g (algebraMap ℚ F r) = algebraMap ℚ F r := by
  rw [show algebraMap ℚ F = (Rat.castHom F : ℚ →+* F) from Subsingleton.elim _ _]
  exact map_ratCast g r

end RigTheta
p2m_reactivate "P2MW.S_ModularCurve_XHDRLevel_coe_theta_eq_of_forall_coe_iota0_of_qExpand.ModularCurve P2MW.S_ModularCurve_XHDRLevel_coe_theta_eq_of_forall_coe_iota0_of_qExpand.ModularCurve.XHDRLevel P2MW.S_ModularCurve_XHDRLevel_coe_theta_eq_of_forall_coe_iota0_of_qExpand.ModularCurve.XHDRLevel.KerMinH P2MW.S_ModularCurve_XHDRLevel_coe_theta_eq_of_forall_coe_iota0_of_qExpand.HDictS1"

open _root_.ModularCurve.XHDRLevel _root_.P2MW.S_ModularCurve_XHDRLevel_coe_theta_eq_of_forall_coe_iota0_of_qExpand.ModularCurve.XHDRLevel in
theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (iota0 : ↥(chartAlgFin p (ΓN p M H hpM) hj) →ₐ[R p] ↥(chartAlgFin p (ΓM M H) hj))
    (iota0_spec : ∀ b, (((iota0 b : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) = ((b : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ))
    (theta : ↥(chartAlgFin p (ΓM M H) hj) ≃ₐ[R p] ↥(chartAlgFin p (ΓM M H) hj))
    (htheta : ∀ b : ↥(chartAlgFin p (ΓN p M H hpM) hj),
      (((theta (iota0 b) : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) = qExpand ℚ p ((b : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ))
    (σ : ↥(qExpFunctionFieldC ℚ (ΓM M H)) ≃ₐ[ℚ] ↥(qExpFunctionFieldC ℚ (ΓM M H)))
    (hσ : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ∀ (f : ↥(qExpFunctionFieldC ℚ (ΓM M H))) (u : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))), (f : LaurentSeries ℚ) = (u : LaurentSeries ℚ) →
        ((σ f : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) = qExpand ℚ p (u : LaurentSeries ℚ)) :
    ∀ b : ↥(chartAlgFin p (ΓM M H) hj), ((theta b : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) = σ ((b : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  haveI : NeZero (M / p) := ⟨(Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne M)) hpM) (Fact.out : p.Prime).pos).ne'⟩
  let F : Type := ↥(qExpFunctionFieldC ℚ (ΓM M H))
  let FN : Type := ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))
  let O : Type := ↥(chartAlgFin p (ΓM M H) hj)
  let ON : Type := ↥(chartAlgFin p (ΓN p M H hpM) hj)

  haveI : (CohCarrier.GammaH M H).FiniteIndex := HDictS1.finiteIndex_gammaH M H
  haveI : (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)).FiniteIndex := HDictS1.finiteIndex_gammaH (M / p) _
  haveI := ModularCurve.XHDRLevel.KerMinH.instIsScalarTower p (ΓM M H)
  haveI := ModularCurve.XHDRLevel.KerMinH.instIsScalarTower p (ΓN p M H hpM)
  haveI hFDM := ModularCurve.XHDRLevel.KerMinH.finiteDimensional_adjoin_jAt (ΓM M H) (HDictS1.T_mem_gammaH M H) hj
  haveI hFDN := ModularCurve.XHDRLevel.KerMinH.finiteDimensional_adjoin_jAt (ΓN p M H hpM) (HDictS1.T_mem_gammaH (M / p) _) hj
  haveI : Algebra.IsAlgebraic ↥(IntermediateField.adjoin ℚ ({jAt (ΓM M H) hj} : Set F)) F := Algebra.IsAlgebraic.of_finite _ _
  haveI : Algebra.IsAlgebraic ↥(IntermediateField.adjoin ℚ ({jAt (ΓN p M H hpM) hj} : Set FN)) FN := Algebra.IsAlgebraic.of_finite _ _
  haveI hfracM : IsFractionRing O F := AlgebraicCurve.TwoChartIntegralModel.isFractionRing_chartAlg (R p) ℚ F ({jAt (ΓM M H) hj} : Set F)
  haveI hfracN : IsFractionRing ON FN := AlgebraicCurve.TwoChartIntegralModel.isFractionRing_chartAlg (R p) ℚ FN ({jAt (ΓN p M H hpM) hj} : Set FN)

  let g : O →+* F := (algebraMap O F).comp theta.toRingEquiv.toRingHom
  let g' : O →+* F := (algebraMap O F).comp theta.symm.toRingEquiv.toRingHom
  have hg : Function.Injective g := (IsFractionRing.injective O F).comp theta.injective
  have hg' : Function.Injective g' := (IsFractionRing.injective O F).comp theta.symm.injective
  let θF : F →+* F := IsFractionRing.lift hg
  let θF' : F →+* F := IsFractionRing.lift hg'
  have hθF : ∀ b : O, θF (b : F) = ((theta b : O) : F) := fun b => IsFractionRing.lift_algebraMap hg b
  have hθF' : ∀ b : O, θF' (b : F) = ((theta.symm b : O) : F) := fun b => IsFractionRing.lift_algebraMap hg' b
  have h1 : θF.comp θF' = RingHom.id F := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors O)
    refine RingHom.ext fun b => ?_
    show θF (θF' (b : F)) = (b : F)
    rw [hθF', hθF, AlgEquiv.apply_symm_apply]
  have h2 : θF'.comp θF = RingHom.id F := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors O)
    refine RingHom.ext fun b => ?_
    show θF' (θF (b : F)) = (b : F)
    rw [hθF, hθF', AlgEquiv.symm_apply_apply]
  let θE : F ≃ₐ[ℚ] F :=
    { (RingEquiv.ofRingHom θF θF' h1 h2 : F ≃+* F) with
      commutes' := fun r => RigTheta.commutes_rat θF r }
  have hθE : ∀ f : F, θE f = θF f := fun f => rfl

  let τ : F ≃ₐ[ℚ] F := θE.trans σ.symm
  have hτ : ∀ (f : F) (u : FN), (f : LaurentSeries ℚ) = (u : LaurentSeries ℚ) → τ f = f := by
    intro f u hfu

    obtain ⟨a, d, hd, hu⟩ := IsFractionRing.div_surjective (A := ON) u
    have hd0 : ((d : ON) : FN) ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd

    have hιa : (((iota0 a : O) : F) : LaurentSeries ℚ) = ((a : ON) : FN) := iota0_spec a
    have hιd : (((iota0 d : O) : F) : LaurentSeries ℚ) = ((d : ON) : FN) := iota0_spec d
    have hιd0 : ((iota0 d : O) : F) ≠ 0 := by
      intro h0
      apply hd0
      apply Subtype.ext
      have := congrArg (fun x : F => (x : LaurentSeries ℚ)) h0
      simp only [ZeroMemClass.coe_zero] at this
      rw [hιd] at this
      exact this
    have hf : f = ((iota0 a : O) : F) / ((iota0 d : O) : F) := by
      apply Subtype.ext
      rw [IntermediateField.coe_div, hιa, hιd, hfu, ← hu, IntermediateField.coe_div]
      rfl

    have hagree : ∀ b : ON, θF ((iota0 b : O) : F) = σ ((iota0 b : O) : F) := by
      intro b
      rw [hθF]
      apply Subtype.ext
      rw [htheta b, hσ ((iota0 b : O) : F) (b : FN) (iota0_spec b)]
    show σ.symm (θE f) = f
    rw [AlgEquiv.symm_apply_eq, hθE, hf, map_div₀, map_div₀, hagree, hagree]

  have key := ModularCurve.XHDRLevel.algEquiv_eq_refl_of_forall_coe_eq_gammaH_infSubgroup p M H hpM hpM2 hHp τ hτ
  intro b
  have hb : τ (b : F) = (b : F) := by rw [key]; rfl
  change σ.symm (θE (b : F)) = (b : F) at hb
  rw [AlgEquiv.symm_apply_eq, hθE, hθF] at hb
  exact hb

end
p2m_reactivate "P2MW.S_ModularCurve_XHDRLevel_coe_theta_eq_of_forall_coe_iota0_of_qExpand.ModularCurve P2MW.S_ModularCurve_XHDRLevel_coe_theta_eq_of_forall_coe_iota0_of_qExpand.ModularCurve.XHDRLevel P2MW.S_ModularCurve_XHDRLevel_coe_theta_eq_of_forall_coe_iota0_of_qExpand.ModularCurve.XHDRLevel.KerMinH P2MW.S_ModularCurve_XHDRLevel_coe_theta_eq_of_forall_coe_iota0_of_qExpand.HDictS1"

end S_ModularCurve_XHDRLevel_coe_theta_eq_of_forall_coe_iota0_of_qExpand
end P2MW
export P2MW.S_ModularCurve_XHDRLevel_coe_theta_eq_of_forall_coe_iota0_of_qExpand (solution)
