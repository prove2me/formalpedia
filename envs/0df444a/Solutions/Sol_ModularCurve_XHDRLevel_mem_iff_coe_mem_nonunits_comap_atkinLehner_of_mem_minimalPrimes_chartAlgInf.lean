-- Prove2me | solution 1 for ModularCurve.XHDRLevel.mem_iff_coe_mem_nonunits_comap_atkinLehner_of_mem_minimalPrimes_chartAlgInf
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/b4202480-6038-57aa-ae3b-d8bd2e4cdd55

import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_GaloisRep_RatLocalizedAtResidue
import Theorems.Thm_GaloisRep_isDiscreteValuationRing_ratLocalizedAt
import Theorems.Thm_GaloisRep_isFractionRing_ratLocalizedAt
import Theorems.Thm_GaloisRep_ratLocalizedAt_maximalIdeal_eq_span_natCast
import Theorems.Thm_GaloisRep_isLocalization_ratLocalizedAt
import Theorems.Thm_ModularCurve_transcendental_of_coe_eq_coeffEmb_jq
import Theorems.Thm_ModularCurve_finiteDimensional_and_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index
import Theorems.Thm_ModularCurve_XHDRLevel_exists_valuationSubring_gauss_qExpFunctionFieldC
import Theorems.Thm_ModularCurve_XHDRLevel_comap_atkinLehner_valuationSubring_gauss_gammaH
import Theorems.Thm_ModularCurve_XHDRLevel_valuationSubring_eq_gauss_or_eq_comap_atkinLehner_gammaH
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_mem_minimalPrimes_span_iff_of_valuationSubring_pair
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRLevel_mem_iff_coe_mem_nonunits_comap_atkinLehner_of_mem_minimalPrimes_chartAlgInf
p2m_attr_erase "instance" "ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid"
p2m_attr_erase "simp" "ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces AlgebraicCurve.ConstantReduction.toRegularProlongation_residue"
p2m_attr_erase "simp" "AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.ProjectiveLine.map_mk ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

universe u

noncomputable section

open ModularCurve ModularCurve.XHDRLevel AlgebraicCurve.TwoChartIntegralModel
open scoped MatrixGroups

namespace Ws47N5Q
namespace KerMin

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

end Ws47N5Q.KerMin
p2m_reactivate "P2MW.S_ModularCurve_XHDRLevel_mem_iff_coe_mem_nonunits_comap_atkinLehner_of_mem_minimalPrimes_chartAlgInf.Ws47N5Q P2MW.S_ModularCurve_XHDRLevel_mem_iff_coe_mem_nonunits_comap_atkinLehner_of_mem_minimalPrimes_chartAlgInf.Ws47N5Q.KerMin"
p2m_reactivate "P2MW.S_ModularCurve_XHDRLevel_mem_iff_coe_mem_nonunits_comap_atkinLehner_of_mem_minimalPrimes_chartAlgInf.Ws47N5Q"

namespace Ws47N5Q
namespace MultOne

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

end Ws47N5Q.MultOne
p2m_reactivate "P2MW.S_ModularCurve_XHDRLevel_mem_iff_coe_mem_nonunits_comap_atkinLehner_of_mem_minimalPrimes_chartAlgInf.Ws47N5Q P2MW.S_ModularCurve_XHDRLevel_mem_iff_coe_mem_nonunits_comap_atkinLehner_of_mem_minimalPrimes_chartAlgInf.Ws47N5Q.KerMin P2MW.S_ModularCurve_XHDRLevel_mem_iff_coe_mem_nonunits_comap_atkinLehner_of_mem_minimalPrimes_chartAlgInf.Ws47N5Q.MultOne"
p2m_reactivate "P2MW.S_ModularCurve_XHDRLevel_mem_iff_coe_mem_nonunits_comap_atkinLehner_of_mem_minimalPrimes_chartAlgInf.Ws47N5Q P2MW.S_ModularCurve_XHDRLevel_mem_iff_coe_mem_nonunits_comap_atkinLehner_of_mem_minimalPrimes_chartAlgInf.Ws47N5Q.KerMin"

namespace Ws47N5Q
namespace KerMin

variable (p : ℕ) [Fact p.Prime]

theorem kerMin_inf_of_pair
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
    (∀ 𝔭 ∈ (Ideal.span {((p : ℕ) : ↥(chartAlgInf p (CohCarrier.GammaH M H) hj))}).minimalPrimes,
      (∀ b : ↥(chartAlgInf p (CohCarrier.GammaH M H) hj), b ∈ 𝔭 ↔ ((b : ↥(chartAlgInf p (CohCarrier.GammaH M H) hj)) : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) ∈ W₀.nonunits) ∨
      (∀ b : ↥(chartAlgInf p (CohCarrier.GammaH M H) hj), b ∈ 𝔭 ↔ ((b : ↥(chartAlgInf p (CohCarrier.GammaH M H) hj)) : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) ∈ W₁.nonunits)) ∧
    (∀ i : Fin 2, ∃ 𝔭 ∈ (Ideal.span {((p : ℕ) : ↥(chartAlgInf p (CohCarrier.GammaH M H) hj))}).minimalPrimes,
      ∀ b : ↥(chartAlgInf p (CohCarrier.GammaH M H) hj), b ∈ 𝔭 ↔ ((b : ↥(chartAlgInf p (CohCarrier.GammaH M H) hj)) : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) ∈ (![W₀, W₁] i).nonunits) ∧
    (∃ b : ↥(chartAlgInf p (CohCarrier.GammaH M H) hj), ((b : ↥(chartAlgInf p (CohCarrier.GammaH M H) hj)) : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) ∈ W₀.nonunits ∧ ((b : ↥(chartAlgInf p (CohCarrier.GammaH M H) hj)) : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) ∉ W₁.nonunits) ∧
    (∃ b : ↥(chartAlgInf p (CohCarrier.GammaH M H) hj), ((b : ↥(chartAlgInf p (CohCarrier.GammaH M H) hj)) : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) ∈ W₁.nonunits ∧ ((b : ↥(chartAlgInf p (CohCarrier.GammaH M H) hj)) : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) ∉ W₀.nonunits) := by
  classical
  have hj0 : (jAt (CohCarrier.GammaH M H) hj) ≠ 0 := Fact.out
  haveI hfact : Fact ((jAt (CohCarrier.GammaH M H) hj)⁻¹ ≠ 0) := ⟨inv_ne_zero hj0⟩
  have htj := transcendental_jAt p (CohCarrier.GammaH M H) hj
  have htj' : Transcendental ↥(GaloisRep.ratLocalizedAt p) ((jAt (CohCarrier.GammaH M H) hj))⁻¹ := fun h => htj (by simpa using h.inv)
  have hadj : IntermediateField.adjoin ℚ ({((jAt (CohCarrier.GammaH M H) hj))⁻¹} : Set ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) =
      IntermediateField.adjoin ℚ ({(jAt (CohCarrier.GammaH M H) hj)} : Set ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) := by
    apply le_antisymm
    · rw [IntermediateField.adjoin_simple_le_iff]
      exact inv_mem (IntermediateField.mem_adjoin_simple_self ℚ _)
    · rw [IntermediateField.adjoin_simple_le_iff]
      have h := inv_mem (IntermediateField.mem_adjoin_simple_self ℚ ((jAt (CohCarrier.GammaH M H) hj)⁻¹))
      rwa [inv_inv] at h
  have hFD' : FiniteDimensional ↥(IntermediateField.adjoin ℚ ({((jAt (CohCarrier.GammaH M H) hj))⁻¹} : Set ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) := by
    rw [hadj]; exact hFD
  have hsep' : Algebra.IsSeparable ↥(IntermediateField.adjoin ℚ ({((jAt (CohCarrier.GammaH M H) hj))⁻¹} : Set ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) := by
    rw [hadj]; exact hsep
  have hprime := prime_p p
  have hX : ¬ (Polynomial.C ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)) ∣ (Polynomial.X : Polynomial ↥(GaloisRep.ratLocalizedAt p))) := by
    rw [Polynomial.C_dvd_iff_dvd_coeff]
    intro h
    have := h 1
    rw [Polynomial.coeff_X_one] at this
    exact hprime.not_unit (isUnit_of_dvd_one this)
  have hbr : ∀ Q : Polynomial ↥(GaloisRep.ratLocalizedAt p),
      Q.map (IsLocalRing.residue ↥(GaloisRep.ratLocalizedAt p)) ≠ 0 ↔ ¬ (Polynomial.C ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)) ∣ Q) :=
    fun Q => (map_residue_ne_zero_iff p Q).trans (map_ne_zero_iff_not_C_dvd p Q)
  have h1' : ∀ i : Fin 2, (∀ a : ↥(GaloisRep.ratLocalizedAt p), algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) a ∈ (![W₀, W₁] i)) ∧
      ∀ a ∈ IsLocalRing.maximalIdeal ↥(GaloisRep.ratLocalizedAt p), algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) a ∈ (![W₀, W₁] i).nonunits :=
    fun i => ⟨(hW1 i).1, fun a ha => (hW1 i).2 a ((mem_maximalIdeal_iff_mem_span p a).mp ha)⟩
  have h2' : ∀ i : Fin 2, ∀ Q : Polynomial ↥(GaloisRep.ratLocalizedAt p), Q.map (IsLocalRing.residue ↥(GaloisRep.ratLocalizedAt p)) ≠ 0 →
      Polynomial.aeval ((jAt (CohCarrier.GammaH M H) hj))⁻¹ Q ∈ (![W₀, W₁] i) ∧ (Polynomial.aeval ((jAt (CohCarrier.GammaH M H) hj))⁻¹ Q)⁻¹ ∈ (![W₀, W₁] i) := by
    intro i Q hQ
    refine Ws47N5Q.MultOne.aeval_mem_of_aeval_inv_mem ((jAt (CohCarrier.GammaH M H) hj))⁻¹ (inv_ne_zero hj0)
      ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)) (![W₀, W₁] i) ?_ hX Q ((hbr Q).mp hQ)
    intro P hP
    rw [inv_inv]
    exact hW2 i P ((map_ne_zero_iff_not_C_dvd p P).mpr hP)
  have h5' : ∀ V : ValuationSubring ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)),
      (∀ a : ↥(GaloisRep.ratLocalizedAt p), algebraMap ↥(GaloisRep.ratLocalizedAt p) _ a ∈ V) →
      (∀ a ∈ IsLocalRing.maximalIdeal ↥(GaloisRep.ratLocalizedAt p), algebraMap ↥(GaloisRep.ratLocalizedAt p) _ a ∈ V.nonunits) →
      (∀ Q : Polynomial ↥(GaloisRep.ratLocalizedAt p), Q.map (IsLocalRing.residue ↥(GaloisRep.ratLocalizedAt p)) ≠ 0 →
        Polynomial.aeval ((jAt (CohCarrier.GammaH M H) hj))⁻¹ Q ∈ V ∧ (Polynomial.aeval ((jAt (CohCarrier.GammaH M H) hj))⁻¹ Q)⁻¹ ∈ V) →
      V = W₀ ∨ V = W₁ := by
    intro V hV1 hV1' hV2
    refine hW5 V hV1 (fun a ha => hV1' a ((mem_maximalIdeal_iff_mem_span p a).mpr ha)) ?_
    intro Q hQ
    exact Ws47N5Q.MultOne.aeval_mem_of_aeval_inv_mem (jAt (CohCarrier.GammaH M H) hj) hj0
      ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)) V (fun P hP => hV2 P ((hbr P).mpr hP)) hX Q
      ((map_ne_zero_iff_not_C_dvd p Q).mp hQ)
  haveI := hFD'; haveI := hsep'
  haveI := instIsScalarTower p (CohCarrier.GammaH M H)
  have hϖ : Ideal.span {algebraMap ↥(GaloisRep.ratLocalizedAt p)
      ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) ((jAt (CohCarrier.GammaH M H) hj))⁻¹)
      ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p))} = Ideal.span {((p : ℕ) : ↥(chartAlgInf p (CohCarrier.GammaH M H) hj))} := by
    rw [map_natCast]
  obtain ⟨hi, hii, hiii⟩ :=
    AlgebraicCurve.TwoChartIntegralModel.mem_minimalPrimes_span_iff_of_valuationSubring_pair
      ↥(GaloisRep.ratLocalizedAt p) ℚ ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) ((jAt (CohCarrier.GammaH M H) hj))⁻¹ htj' hFD' hsep'
      ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)) (maximalIdeal_R p) W₀ W₁ h1' h2' hW3 h5'
  rw [hϖ] at hi hii
  exact ⟨hi, hii, hiii⟩

end Ws47N5Q.KerMin
p2m_reactivate "P2MW.S_ModularCurve_XHDRLevel_mem_iff_coe_mem_nonunits_comap_atkinLehner_of_mem_minimalPrimes_chartAlgInf.Ws47N5Q P2MW.S_ModularCurve_XHDRLevel_mem_iff_coe_mem_nonunits_comap_atkinLehner_of_mem_minimalPrimes_chartAlgInf.Ws47N5Q.KerMin P2MW.S_ModularCurve_XHDRLevel_mem_iff_coe_mem_nonunits_comap_atkinLehner_of_mem_minimalPrimes_chartAlgInf.Ws47N5Q.MultOne"
p2m_reactivate "P2MW.S_ModularCurve_XHDRLevel_mem_iff_coe_mem_nonunits_comap_atkinLehner_of_mem_minimalPrimes_chartAlgInf.Ws47N5Q P2MW.S_ModularCurve_XHDRLevel_mem_iff_coe_mem_nonunits_comap_atkinLehner_of_mem_minimalPrimes_chartAlgInf.Ws47N5Q.KerMin P2MW.S_ModularCurve_XHDRLevel_mem_iff_coe_mem_nonunits_comap_atkinLehner_of_mem_minimalPrimes_chartAlgInf.Ws47N5Q.MultOne"

end
p2m_reactivate "P2MW.S_ModularCurve_XHDRLevel_mem_iff_coe_mem_nonunits_comap_atkinLehner_of_mem_minimalPrimes_chartAlgInf.Ws47N5Q P2MW.S_ModularCurve_XHDRLevel_mem_iff_coe_mem_nonunits_comap_atkinLehner_of_mem_minimalPrimes_chartAlgInf.Ws47N5Q.KerMin P2MW.S_ModularCurve_XHDRLevel_mem_iff_coe_mem_nonunits_comap_atkinLehner_of_mem_minimalPrimes_chartAlgInf.Ws47N5Q.MultOne"

open ModularCurve ModularCurve.XHDRLevel AlgebraicCurve.TwoChartIntegralModel
open scoped MatrixGroups

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 1600000 in
theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))

    (σ : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) ≃ₐ[ℚ] ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))
    (hσ : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ∀ (f : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) (u : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)))),
        (f : LaurentSeries ℚ) = (u : LaurentSeries ℚ) →
          ((σ f : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) : LaurentSeries ℚ) = qExpand ℚ p (u : LaurentSeries ℚ))
    (hσ' : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ∀ (c : (ZMod (M / p))ˣ), (c : ZMod (M / p)) = (p : ZMod (M / p)) →
        ∀ (f : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) (u : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)))),
          (f : LaurentSeries ℚ) = qExpand ℚ p (u : LaurentSeries ℚ) →
            coeffEmb (AlgebraicClosure ℚ) ((σ f : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) : LaurentSeries ℚ) =
              ((diamondAutHBar (M / p) (infSubgroup p M H hpM) c
                  ⟨coeffEmb (AlgebraicClosure ℚ) (u : LaurentSeries ℚ), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) u.2⟩ :
                  ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) : LaurentSeries (AlgebraicClosure ℚ)))

    (W₀ : ValuationSubring ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))
    (hW₀ : ∀ f : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)), f ∈ W₀ ↔
      ∃ a a' : PowerSeries ↥(GaloisRep.ratLocalizedAt p), a'.map (GaloisRep.ratLocalizedAtResidue p) ≠ 0 ∧
        (f : LaurentSeries ℚ) * HahnSeries.ofPowerSeries ℤ ℚ (a'.map (GaloisRep.ratLocalizedAt p).subtype) =
          HahnSeries.ofPowerSeries ℤ ℚ (a.map (GaloisRep.ratLocalizedAt p).subtype))

    (P : Ideal ↥(chartAlgInf p (CohCarrier.GammaH M H) hj))
    (hP : P ∈ (Ideal.span {((p : ℕ) : ↥(chartAlgInf p (CohCarrier.GammaH M H) hj))}).minimalPrimes)
    (hP' : ∃ b ∈ P, ((b : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))) ∉ W₀.nonunits) :
    ∀ b : ↥(chartAlgInf p (CohCarrier.GammaH M H) hj),
      b ∈ P ↔ ((b : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))) ∈ (W₀.comap σ.toAlgHom.toRingHom).nonunits := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩

  obtain ⟨W, hWpin, hWR, hWp, hWj, -⟩ :=
    ModularCurve.XHDRLevel.exists_valuationSubring_gauss_qExpFunctionFieldC p (CohCarrier.GammaH M H) hj
  have hWW₀ : W = W₀ := by
    ext f; exact (hWpin f).trans (hW₀ f).symm
  subst hWW₀

  obtain ⟨⟨hc1, hc1'⟩, hc2, -, hcne⟩ :=
    ModularCurve.XHDRLevel.comap_atkinLehner_valuationSubring_gauss_gammaH p M H hpM hpM2 hHp hj σ hσ W hWpin
  have hW1 : ∀ i : Fin 2, (∀ a : ↥(GaloisRep.ratLocalizedAt p), algebraMap ↥(GaloisRep.ratLocalizedAt p)
        ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) a ∈ (![W, W.comap σ.toAlgHom.toRingHom] i)) ∧
      ∀ a ∈ Ideal.span {((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p))}, algebraMap ↥(GaloisRep.ratLocalizedAt p)
        ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) a ∈ (![W, W.comap σ.toAlgHom.toRingHom] i).nonunits := by
    intro i; fin_cases i
    · exact ⟨hWR, hWp⟩
    · exact ⟨hc1, hc1'⟩
  have hW2 : ∀ i : Fin 2, ∀ Q : Polynomial ↥(GaloisRep.ratLocalizedAt p), Q.map (GaloisRep.ratLocalizedAtResidue p) ≠ 0 →
      Polynomial.aeval (jAt (CohCarrier.GammaH M H) hj) Q ∈ (![W, W.comap σ.toAlgHom.toRingHom] i) ∧
      (Polynomial.aeval (jAt (CohCarrier.GammaH M H) hj) Q)⁻¹ ∈ (![W, W.comap σ.toAlgHom.toRingHom] i) := by
    intro i; fin_cases i
    · exact hWj
    · exact hc2
  have hW3 : W ≠ W.comap σ.toAlgHom.toRingHom := fun h => hcne h.symm
  have hW5 : ∀ V : ValuationSubring ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)),
      (∀ a : ↥(GaloisRep.ratLocalizedAt p), algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) a ∈ V) →
      (∀ a ∈ Ideal.span {((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p))}, algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) a ∈ V.nonunits) →
      (∀ Q : Polynomial ↥(GaloisRep.ratLocalizedAt p), Q.map (GaloisRep.ratLocalizedAtResidue p) ≠ 0 →
        Polynomial.aeval (jAt (CohCarrier.GammaH M H) hj) Q ∈ V ∧ (Polynomial.aeval (jAt (CohCarrier.GammaH M H) hj) Q)⁻¹ ∈ V) →
      V = W ∨ V = W.comap σ.toAlgHom.toRingHom :=
    fun V a b c => ModularCurve.XHDRLevel.valuationSubring_eq_gauss_or_eq_comap_atkinLehner_gammaH p M H hpM hpM2 hHp hj σ hσ W hWpin V a b c

  haveI : (CohCarrier.GammaH M H).FiniteIndex := Ws47N5Q.MultOne.finiteIndex_gammaH M H
  have hT := Ws47N5Q.MultOne.T_mem_gammaH M H
  have hFD := Ws47N5Q.KerMin.finiteDimensional_adjoin_jAt (CohCarrier.GammaH M H) hT hj
  have hsep := Ws47N5Q.KerMin.isSeparable_adjoin_jAt (CohCarrier.GammaH M H) hT hj
  obtain ⟨hi, -, -, -⟩ :=
    Ws47N5Q.KerMin.kerMin_inf_of_pair p M H hj hFD hsep W (W.comap σ.toAlgHom.toRingHom) hW1 hW2 hW3 hW5
  rcases hi P hP with h | h
  · exfalso
    obtain ⟨b, hbP, hb⟩ := hP'
    exact hb ((h b).mp hbP)
  · exact h

end S_ModularCurve_XHDRLevel_mem_iff_coe_mem_nonunits_comap_atkinLehner_of_mem_minimalPrimes_chartAlgInf
end P2MW
export P2MW.S_ModularCurve_XHDRLevel_mem_iff_coe_mem_nonunits_comap_atkinLehner_of_mem_minimalPrimes_chartAlgInf (solution)
