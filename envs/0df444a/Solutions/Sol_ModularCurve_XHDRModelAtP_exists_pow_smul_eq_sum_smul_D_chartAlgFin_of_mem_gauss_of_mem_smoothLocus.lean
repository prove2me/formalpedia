-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.exists_pow_smul_eq_sum_smul_D_chartAlgFin_of_mem_gauss_of_mem_smoothLocus
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/b50eaf2d-8f79-54a0-aaf0-d9382c46f28f

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_GaloisRep_RatLocalizedAtResidue
import Theorems.Thm_ModularCurve_XHDRLevel_exists_valuationSubring_gauss_qExpFunctionFieldC
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_le_and_height_eq_one_and_exists_div_of_valuationSubring_of_transcendental
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isFractionRing_chartAlg
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isIntegrallyClosed_chartAlg
import Theorems.Thm_IsIntegrallyClosed_exists_valuationSubring_mem_iff_and_nonunits_iff_of_height_eq_one
import Theorems.Thm_IsIntegrallyClosed_mem_range_algebraMap_of_forall_height_eq_one
import Theorems.Thm_Ideal_height_eq_one_iff_mem_minimalPrimes_span_singleton_of_mem
import Theorems.Thm_ModularCurve_finiteType_chartAlgFin_and_chartAlgInf_twoChartIntegralModel_qExpFunctionFieldC
import Theorems.Thm_ModularCurve_transcendental_of_coe_eq_coeffEmb_jq
import Theorems.Thm_ModularCurve_finiteDimensional_and_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index
import Theorems.Thm_KaehlerDifferential_D_ne_zero_of_transcendental
import Theorems.Thm_GaloisRep_isDiscreteValuationRing_ratLocalizedAt
import Theorems.Thm_GaloisRep_isFractionRing_ratLocalizedAt
import Theorems.Thm_GaloisRep_ratLocalizedAt_maximalIdeal_eq_span_natCast
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_exists_pow_smul_eq_sum_smul_D_chartAlgFin_of_mem_gauss_of_mem_smoothLocus
p2m_attr_erase "instance" "ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve ModularCurve ModularCurve.XHDRLevel
open scoped MatrixGroups

noncomputable section

namespace E2Body

section Generic

variable {K : Type*} [Field K] {F : Type*} [Field F] [Algebra K F]

theorem smul_D_injective {t : F} (ht : KaehlerDifferential.D K F t ≠ 0) {a b : F}
    (h : a • KaehlerDifferential.D K F t = b • KaehlerDifferential.D K F t) : a = b :=
  smul_left_injective F ht h

theorem exists_D_mul_inv_eq_smul {t a s ca cs : F}
    (ha : KaehlerDifferential.D K F a = ca • KaehlerDifferential.D K F t)
    (hs : KaehlerDifferential.D K F s = cs • KaehlerDifferential.D K F t) :
    KaehlerDifferential.D K F (a * s⁻¹) = (s⁻¹ * ca - a * s⁻¹ * s⁻¹ * cs) • KaehlerDifferential.D K F t := by
  by_cases hs0 : s = 0
  · subst hs0
    simp
  have hinv : KaehlerDifferential.D K F s⁻¹ = -(s⁻¹ ^ 2) • KaehlerDifferential.D K F s :=
    (KaehlerDifferential.D K F).leibniz_of_mul_eq_one (inv_mul_cancel₀ hs0)
  rw [Derivation.leibniz, hinv, hs, ha]
  module

theorem D_eq_of_D_inv_eq {x t c : F} (hx : x ≠ 0)
    (h : KaehlerDifferential.D K F x⁻¹ = c • KaehlerDifferential.D K F t) :
    KaehlerDifferential.D K F x = (-(x ^ 2) * c) • KaehlerDifferential.D K F t := by
  rw [(KaehlerDifferential.D K F).leibniz_of_mul_eq_one (mul_inv_cancel₀ hx), h, smul_smul]

theorem D_ne_zero_of_D_eq_smul {x t c : F} (hx : KaehlerDifferential.D K F x ≠ 0)
    (h : KaehlerDifferential.D K F x = c • KaehlerDifferential.D K F t) : KaehlerDifferential.D K F t ≠ 0 := by
  intro h0
  exact hx (by rw [h, h0, smul_zero])

theorem smul_D_eq_of_D_eq {η : Ω[F⁄K]} {g x e t : F} (hη : η = g • KaehlerDifferential.D K F x)
    (h : KaehlerDifferential.D K F x = e • KaehlerDifferential.D K F t) :
    η = (g * e) • KaehlerDifferential.D K F t := by
  rw [hη, h, smul_smul]

theorem clear_denominators {η : Ω[F⁄K]} {φ t a₁ s₁ aφ sφ : F}
    (hη : η = φ • KaehlerDifferential.D K F t) (ht : t = a₁ * s₁⁻¹) (hφ : φ * sφ = aφ)
    (hst : s₁ ≠ 0) (hsφ : sφ ≠ 0) :
    (sφ * s₁ ^ 2) • η =
      (aφ * s₁) • KaehlerDifferential.D K F a₁ + (-(aφ * a₁)) • KaehlerDifferential.D K F s₁ := by
  have hφ' : φ = aφ * sφ⁻¹ := by rw [← hφ, mul_assoc, mul_inv_cancel₀ hsφ, mul_one]
  have hinv : KaehlerDifferential.D K F s₁⁻¹ = -(s₁⁻¹ ^ 2) • KaehlerDifferential.D K F s₁ :=
    (KaehlerDifferential.D K F).leibniz_of_mul_eq_one (inv_mul_cancel₀ hst)
  rw [hη, ht, Derivation.leibniz, hinv, hφ']
  match_scalars <;> field_simp

theorem transcendental_congr_inst {L : Type*} [Field L] {i₁ i₂ : Algebra L F} (x : F)
    (h : @Transcendental L F _ _ i₁ x) (hsub : i₁ = i₂) : @Transcendental L F _ _ i₂ x := by
  subst hsub; exact h

theorem isSeparable_adjoin_congr_inst {L : Type*} [Field L] {i₁ i₂ : Algebra L F} (x : F)
    (h : letI := i₁; Algebra.IsSeparable ↥(IntermediateField.adjoin L ({x} : Set F)) F) (hsub : i₁ = i₂) :
    letI := i₂; Algebra.IsSeparable ↥(IntermediateField.adjoin L ({x} : Set F)) F := by
  subst hsub; exact h

end Generic

section Setting

variable (p : ℕ) [Fact p.Prime] (Γ : Subgroup SL(2, ℤ))
  (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))

abbrev FF : Type := ↥(qExpFunctionFieldC ℚ Γ)

abbrev instQ : Algebra ℚ (FF Γ) := ModularCurve.instAlgebraIntermediateFieldLaurent (qExpFunctionFieldC ℚ Γ)

abbrev AA : Subalgebra (R p) (FF Γ) := chartAlgFin p Γ hj

end Setting

section BaseRing

variable (p : ℕ) [Fact p.Prime]

scoped instance instDVR_R : IsDiscreteValuationRing (R p) :=
  GaloisRep.isDiscreteValuationRing_ratLocalizedAt p Fact.out

scoped instance instIsFractionRing_R : IsFractionRing (R p) ℚ := GaloisRep.isFractionRing_ratLocalizedAt p

theorem maximalIdeal_R : IsLocalRing.maximalIdeal (R p) = Ideal.span {((p : ℕ) : R p)} :=
  GaloisRep.ratLocalizedAt.maximalIdeal_eq_span_natCast p Fact.out

theorem map_ratLocalizedAtResidue_ne_zero {P : Polynomial (R p)}
    (hP : P.map (IsLocalRing.residue (R p)) ≠ 0) : P.map (GaloisRep.ratLocalizedAtResidue p) ≠ 0 := by
  obtain ⟨i, hi⟩ : ∃ i, (P.map (IsLocalRing.residue (R p))).coeff i ≠ 0 := by
    by_contra h
    push Not at h
    exact hP (Polynomial.ext (by simpa using h))
  rw [Polynomial.coeff_map] at hi
  have hu : IsUnit (P.coeff i) := by
    by_contra hnu
    exact hi ((IsLocalRing.residue_eq_zero_iff _).mpr ((IsLocalRing.mem_maximalIdeal _).mpr hnu))
  intro h0
  have := congrArg (fun Q => Q.coeff i) h0
  simp only [Polynomial.coeff_map, Polynomial.coeff_zero] at this
  exact (hu.map (GaloisRep.ratLocalizedAtResidue p)).ne_zero this

end BaseRing

section Gauss

variable (p : ℕ) [Fact p.Prime] (Γ : Subgroup SL(2, ℤ))
  (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
  (W₀ : ValuationSubring (FF Γ))
  (hW₀ : ∀ f₀ : FF Γ, f₀ ∈ W₀ ↔
    ∃ a a' : PowerSeries ↥(GaloisRep.ratLocalizedAt p), a'.map (GaloisRep.ratLocalizedAtResidue p) ≠ 0 ∧
      (f₀ : LaurentSeries ℚ) * HahnSeries.ofPowerSeries ℤ ℚ (a'.map (GaloisRep.ratLocalizedAt p).subtype) =
        HahnSeries.ofPowerSeries ℤ ℚ (a.map (GaloisRep.ratLocalizedAt p).subtype))

include hW₀ in

theorem gauss_props :
    (∀ a : R p, algebraMap (R p) (FF Γ) a ∈ W₀) ∧
    (∀ a ∈ Ideal.span {((p : ℕ) : R p)}, algebraMap (R p) (FF Γ) a ∈ W₀.nonunits) ∧
    (∀ Q : Polynomial (R p), Q.map (GaloisRep.ratLocalizedAtResidue p) ≠ 0 →
      Polynomial.aeval (jAt Γ hj) Q ∈ W₀ ∧ (Polynomial.aeval (jAt Γ hj) Q)⁻¹ ∈ W₀) ∧
    (∀ x : FF Γ, x ∈ W₀.nonunits → x * (algebraMap (R p) (FF Γ) ((p : ℕ) : R p))⁻¹ ∈ W₀) := by
  obtain ⟨W, hW, h1, h1', h2, h6⟩ := ModularCurve.XHDRLevel.exists_valuationSubring_gauss_qExpFunctionFieldC p Γ hj
  have : W₀ = W := by
    ext f
    rw [hW₀, hW]
  subst this
  exact ⟨h1, h1', h2, h6⟩

include hW₀ in
theorem jAt_mem_gauss : (jAt Γ hj : FF Γ) ∈ W₀ ∧ (jAt Γ hj : FF Γ)⁻¹ ∈ W₀ := by
  have h := (gauss_props p Γ hj W₀ hW₀).2.2.1 Polynomial.X (by
    rw [Polynomial.map_X]; exact Polynomial.X_ne_zero)
  simpa using h

include hW₀ in

theorem aeval_inv_jAt_mem_gauss (Q : Polynomial (R p)) (hQ : Q.map (GaloisRep.ratLocalizedAtResidue p) ≠ 0) :
    Polynomial.aeval (jAt Γ hj : FF Γ)⁻¹ Q ∈ W₀ ∧ (Polynomial.aeval (jAt Γ hj : FF Γ)⁻¹ Q)⁻¹ ∈ W₀ := by
  obtain ⟨-, -, h2, -⟩ := gauss_props p Γ hj W₀ hW₀
  obtain ⟨hjW, hjiW⟩ := jAt_mem_gauss p Γ hj W₀ hW₀
  set j : FF Γ := jAt Γ hj with hjdef
  have hj0 : j ≠ 0 := (fact_jAt_ne_zero Γ hj).out

  have hrev : Q.reverse.map (GaloisRep.ratLocalizedAtResidue p) ≠ 0 := by
    obtain ⟨i, hi⟩ : ∃ i, (Q.map (GaloisRep.ratLocalizedAtResidue p)).coeff i ≠ 0 := by
      by_contra h
      push Not at h
      exact hQ (Polynomial.ext (by simpa using h))
    rw [Polynomial.coeff_map] at hi
    have hile : i ≤ Q.natDegree := by
      by_contra hlt
      push Not at hlt
      exact hi (by rw [Polynomial.coeff_eq_zero_of_natDegree_lt hlt, map_zero])
    intro h0
    have := congrArg (fun P => P.coeff (Polynomial.revAt Q.natDegree i)) h0
    simp only [Polynomial.coeff_map, Polynomial.coeff_zero, Polynomial.coeff_reverse,
      Polynomial.revAt_invol] at this
    exact hi this
  obtain ⟨hrW, hriW⟩ := h2 Q.reverse hrev

  haveI : Invertible (j⁻¹) := invertibleOfNonzero (inv_ne_zero hj0)
  have key : Polynomial.aeval j⁻¹ Q = Polynomial.aeval j Q.reverse * (j⁻¹) ^ Q.natDegree := by
    have h := Polynomial.eval₂_reverse_mul_pow (algebraMap (R p) (FF Γ)) j⁻¹ Q
    rw [invOf_eq_inv, inv_inv] at h
    rw [Polynomial.aeval_def, Polynomial.aeval_def, ← h]
  have hpow : (j⁻¹) ^ Q.natDegree ∈ W₀ := pow_mem hjiW _
  have hpowi : ((j⁻¹) ^ Q.natDegree)⁻¹ ∈ W₀ := by
    rw [← inv_pow, inv_inv]; exact pow_mem hjW _
  refine ⟨?_, ?_⟩
  · rw [key]; exact mul_mem hrW hpow
  · rw [key, mul_inv]; exact mul_mem hriW hpowi

end Gauss

section Centre

variable (p : ℕ) [Fact p.Prime] (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ)
  (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
  (W₀ : ValuationSubring (FF Γ))
  (hW₀ : ∀ f₀ : FF Γ, f₀ ∈ W₀ ↔
    ∃ a a' : PowerSeries ↥(GaloisRep.ratLocalizedAt p), a'.map (GaloisRep.ratLocalizedAtResidue p) ≠ 0 ∧
      (f₀ : LaurentSeries ℚ) * HahnSeries.ofPowerSeries ℤ ℚ (a'.map (GaloisRep.ratLocalizedAt p).subtype) =
        HahnSeries.ofPowerSeries ℤ ℚ (a.map (GaloisRep.ratLocalizedAt p).subtype))

theorem transcendental_jAt : Transcendental (R p) (jAt Γ hj : FF Γ) := by
  have hjq : ((jAt Γ hj : FF Γ) : LaurentSeries ℚ) = coeffEmb ℚ ModularCurve.jq := by
    rw [coe_jAt, jqModC_rat]
    ext k
    rw [coeffEmb_coeff]
    simp
  exact @ModularCurve.transcendental_of_coe_eq_coeffEmb_jq ℚ _ _ (qExpFunctionFieldC ℚ Γ) (R p) _ _ _ inferInstance _
    (@IsScalarTower.of_algebraMap_eq (R p) ℚ (FF Γ) _ _ _ _
      (SubalgebraClass.toAlgebra (qExpFunctionFieldC ℚ Γ)) _ fun x =>
        (IsScalarTower.algebraMap_apply (R p) ℚ (FF Γ) x).trans
          (RingHom.congr_fun (Subsingleton.elim _ _) _))
    (jAt Γ hj) hjq

theorem transcendental_jAt_inv : Transcendental (R p) (jAt Γ hj : FF Γ)⁻¹ := fun h =>
  transcendental_jAt p Γ hj (IsAlgebraic.inv_iff.mp h)

theorem finiteDimensional_adjoin_congr_inst {F : Type*} [Field F] {i₁ i₂ : Algebra ℚ F} (x : F)
    (h : letI := i₁; FiniteDimensional ↥(IntermediateField.adjoin ℚ ({x} : Set F)) F) :
    letI := i₂; FiniteDimensional ↥(IntermediateField.adjoin ℚ ({x} : Set F)) F := by
  have : i₁ = i₂ := Subsingleton.elim _ _
  subst this
  exact h

include hT in

theorem finiteDimensional_adjoin :
    FiniteDimensional ↥(IntermediateField.adjoin ℚ ({(jAt Γ hj : FF Γ)} : Set (FF Γ))) (FF Γ) := by
  have h0 := (ModularCurve.finiteDimensional_and_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index ℚ Γ hT Γ le_rfl
    (fun γ h => Or.inl h) (jAt Γ hj) (coe_jAt _ hj)).1
  exact finiteDimensional_adjoin_congr_inst (i₁ := SubalgebraClass.toAlgebra (qExpFunctionFieldC ℚ Γ)) _ h0

include hT hW₀ in

theorem centre :
    (∀ b : ↥(AA p Γ hj), (b : FF Γ) ∈ W₀) ∧
    ∃ 𝔓 : Ideal ↥(AA p Γ hj), 𝔓.IsPrime ∧ 𝔓.height = 1 ∧
      (∀ b : ↥(AA p Γ hj), b ∈ 𝔓 ↔ (b : FF Γ) ∈ W₀.nonunits) ∧
      (algebraMap (R p) ↥(AA p Γ hj) ((p : ℕ) : R p) ∈ 𝔓) ∧
      (∀ f : FF Γ, f ∈ W₀ ↔ ∃ a b : ↥(AA p Γ hj), b ∉ 𝔓 ∧ f * (b : FF Γ) = (a : FF Γ)) := by
  obtain ⟨hR, hpW, hgen2, -⟩ := gauss_props p Γ hj W₀ hW₀
  have hVm : ∀ a ∈ IsLocalRing.maximalIdeal (R p), algebraMap (R p) (FF Γ) a ∈ W₀.nonunits := by
    intro a ha
    rw [maximalIdeal_R] at ha
    exact hpW a ha
  have hVj : ∀ P : Polynomial (R p), P.map (IsLocalRing.residue (R p)) ≠ 0 →
      Polynomial.aeval (jAt Γ hj : FF Γ) P ∈ W₀ ∧ (Polynomial.aeval (jAt Γ hj : FF Γ) P)⁻¹ ∈ W₀ :=
    fun P hP => hgen2 P (map_ratLocalizedAtResidue_ne_zero p hP)
  have hFD := finiteDimensional_adjoin Γ hT hj
  haveI : CharZero ↥(IntermediateField.adjoin ℚ ({(jAt Γ hj : FF Γ)} : Set (FF Γ))) :=
    charZero_of_injective_algebraMap (algebraMap ℚ _).injective
  haveI := hFD
  haveI : Algebra.IsAlgebraic ↥(IntermediateField.adjoin ℚ ({(jAt Γ hj : FF Γ)} : Set (FF Γ))) (FF Γ) :=
    Algebra.IsAlgebraic.of_finite _ _
  have hsep : Algebra.IsSeparable ↥(IntermediateField.adjoin ℚ ({(jAt Γ hj : FF Γ)} : Set (FF Γ))) (FF Γ) :=
    inferInstance
  obtain ⟨hAW, ⟨𝔓, h𝔓, hht, hmem, hmR, hloc⟩, -⟩ :=
    AlgebraicCurve.TwoChartIntegralModel.le_and_height_eq_one_and_exists_div_of_valuationSubring_of_transcendental
      (R p) ℚ (FF Γ) (jAt Γ hj : FF Γ) (transcendental_jAt p Γ hj) hFD hsep W₀ hR hVm hVj
  refine ⟨hAW, 𝔓, h𝔓, hht, hmem, ?_, hloc⟩
  apply hmR
  rw [maximalIdeal_R]
  exact Ideal.subset_span rfl

variable {p Γ hj W₀} in

theorem centre_le (hAW : ∀ b : ↥(AA p Γ hj), (b : FF Γ) ∈ W₀) {𝔓 : Ideal ↥(AA p Γ hj)}
    (hmem : ∀ b : ↥(AA p Γ hj), b ∈ 𝔓 ↔ (b : FF Γ) ∈ W₀.nonunits)
    (𝔭 : PrimeSpectrum ↥(AA p Γ hj))
    (hx0 : ∀ s : ↥(AA p Γ hj), s ∉ 𝔭.asIdeal → ((s : FF Γ))⁻¹ ∈ W₀) :
    𝔓 ≤ 𝔭.asIdeal := by
  intro b hb
  by_contra hb'
  have hinv := hx0 b hb'
  have hbW := hAW b
  have hnu : (b : FF Γ) ∈ W₀.nonunits := (hmem b).mp hb
  rw [ValuationSubring.mem_nonunits_iff] at hnu
  have h1 : W₀.valuation ((b : FF Γ)⁻¹) ≤ 1 := (W₀.valuation_le_one_iff _).mpr hinv
  have hb0 : (b : FF Γ) ≠ 0 := by
    intro h
    rw [h, inv_zero] at hinv
    rw [h] at hnu

    exact hb' (by
      have : b = 0 := Subtype.ext h
      rw [this]; exact Ideal.zero_mem _)
  have := mul_lt_one_of_lt_of_le hnu h1
  rw [← map_mul, mul_inv_cancel₀ hb0, map_one] at this
  exact lt_irrefl _ this

end Centre

section ChartRing

variable (p : ℕ) [Fact p.Prime] (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ)
  (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))

include hT in
theorem isNoetherianRing_A : IsNoetherianRing ↥(AA p Γ hj) := by
  haveI : Algebra.FiniteType (R p) ↥(AA p Γ hj) :=
    (ModularCurve.finiteType_chartAlgFin_and_chartAlgInf_twoChartIntegralModel_qExpFunctionFieldC p Γ hT
      (jAt Γ hj) (coe_jAt _ hj)).1
  exact Algebra.FiniteType.isNoetherianRing (R p) _

theorem isIntegrallyClosed_A : IsIntegrallyClosed ↥(AA p Γ hj) :=
  AlgebraicCurve.TwoChartIntegralModel.isIntegrallyClosed_chartAlg (R p) (FF Γ) _

include hT in
theorem isFractionRing_A : IsFractionRing ↥(AA p Γ hj) (FF Γ) := by
  haveI := finiteDimensional_adjoin Γ hT hj
  haveI : Algebra.IsAlgebraic ↥(IntermediateField.adjoin ℚ ({(jAt Γ hj : FF Γ)} : Set (FF Γ))) (FF Γ) :=
    Algebra.IsAlgebraic.of_finite _ _
  exact AlgebraicCurve.TwoChartIntegralModel.isFractionRing_chartAlg (R p) ℚ (FF Γ) ({(jAt Γ hj : FF Γ)} : Set (FF Γ))

def jA : ↥(AA p Γ hj) := ⟨(jAt Γ hj : FF Γ), TwoChartIntegralModel.subset_chartAlg (R p) (FF Γ) _ rfl⟩

@[scoped simp] theorem coe_jA : (jA p Γ hj : FF Γ) = (jAt Γ hj : FF Γ) := rfl

end ChartRing

section Pinned

variable (Γ : Subgroup SL(2, ℤ))

abbrev ΩQ : Type := @KaehlerDifferential ℚ (FF Γ) _ _ (instQ Γ)

abbrev DQ : FF Γ → ΩQ Γ := fun x => @KaehlerDifferential.D ℚ (FF Γ) _ _ (instQ Γ) x

theorem DQ_apply (x : FF Γ) : DQ Γ x = @KaehlerDifferential.D ℚ (FF Γ) _ _ (instQ Γ) x := rfl

end Pinned

section RankOne

variable {R C : Type*} [CommRing R] [CommRing C] [Algebra R C]

theorem exists_frame_of_isStandardSmoothOfRelativeDimension_one
    [Algebra.IsStandardSmoothOfRelativeDimension 1 R C] (Q : Ideal C) [hQ : Q.IsPrime] :
    ∃ t : C, ∀ b : C, ∃ u c : C, u ∉ Q ∧
      u • KaehlerDifferential.D R C b = c • KaehlerDifferential.D R C t := by
  classical
  haveI : Nontrivial C := nontrivial_of_ne (1 : C) 0 fun h10 =>
    hQ.ne_top ((Ideal.eq_top_iff_one Q).mpr (by rw [h10]; exact Q.zero_mem))
  haveI : Algebra.IsStandardSmooth R C := Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth 1
  have hrank : Module.rank C (Ω[C⁄R]) = 1 := by
    simpa using Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential (R := R) (S := C) 1
  set ι := Module.Free.ChooseBasisIndex C (Ω[C⁄R])
  let e := Module.Free.chooseBasis C (Ω[C⁄R])
  have hcard : Cardinal.mk ι = 1 := by
    rw [← Module.Free.rank_eq_card_chooseBasisIndex, hrank]
  obtain ⟨hsub, ⟨i₀⟩⟩ := Cardinal.eq_one_iff_unique.mp hcard
  letI : Unique ι := ⟨⟨i₀⟩, fun j => Subsingleton.elim _ _⟩

  have hrepr : ∀ ω : Ω[C⁄R], ω = e.coord i₀ ω • e i₀ := fun ω => by
    conv_lhs => rw [← e.sum_repr ω]
    rw [Fintype.sum_unique, Module.Basis.coord_apply]
    rfl

  have hspan : Ideal.span (Set.range fun b : C => e.coord i₀ (KaehlerDifferential.D R C b)) = ⊤ := by
    rw [Ideal.eq_top_iff_one]
    have h1 : e.coord i₀ (e i₀) = (1 : C) := by
      simp [Module.Basis.coord_apply, Module.Basis.repr_self]
    have hmem : e i₀ ∈ Submodule.span C (Set.range (KaehlerDifferential.D R C)) := by
      rw [KaehlerDifferential.span_range_derivation]; trivial
    have h2 := Submodule.mem_map_of_mem (f := e.coord i₀) hmem
    rw [Submodule.map_span, h1, ← Set.range_comp] at h2
    exact h2

  obtain ⟨t, ht⟩ : ∃ t : C, e.coord i₀ (KaehlerDifferential.D R C t) ∉ Q := by
    by_contra h
    push Not at h
    apply hQ.ne_top
    rw [eq_top_iff, ← hspan, Ideal.span_le]
    rintro _ ⟨b, rfl⟩
    exact h b
  refine ⟨t, fun b => ⟨e.coord i₀ (KaehlerDifferential.D R C t), e.coord i₀ (KaehlerDifferential.D R C b), ht, ?_⟩⟩
  conv_lhs => rw [hrepr (KaehlerDifferential.D R C b)]
  conv_rhs => rw [hrepr (KaehlerDifferential.D R C t)]
  rw [smul_smul, smul_smul, mul_comm]

end RankOne

section Transport

universe u

variable {R : Type u} [CommRing R] {F : Type u} [Field F] [Algebra R F]
  (A : Subalgebra R F) (𝔭 : Ideal ↥A) [h𝔭 : 𝔭.IsPrime]

def IsFracAt (x : F) : Prop := ∃ a s : ↥A, s ∉ 𝔭 ∧ x = (a : F) * ((s : F))⁻¹

omit h𝔭 in
theorem isFracAt_coe (a : ↥A) (h1 : (1 : ↥A) ∉ 𝔭) : IsFracAt A 𝔭 (a : F) :=
  ⟨a, 1, h1, by simp⟩

theorem transport_frame (M : Submonoid ↥A) (hM : M ≤ 𝔭.primeCompl)
    (C : Type u) [CommRing C] [Algebra ↥A C] [Algebra R C] [IsScalarTower R ↥A C] [IsLocalization M C]
    (hC : ∃ t : C, ∀ b : C, ∃ u c : C, u ∉ Ideal.map (algebraMap ↥A C) 𝔭 ∧
      u • KaehlerDifferential.D R C b = c • KaehlerDifferential.D R C t) :
    ∃ t : F, IsFracAt A 𝔭 t ∧ ∀ b : ↥A, ∃ c : F, IsFracAt A 𝔭 c ∧
      KaehlerDifferential.D R F (b : F) = c • KaehlerDifferential.D R F t := by

  have hunit : ∀ m : M, IsUnit ((A.val : ↥A →+* F) m) := fun m => by
    rw [isUnit_iff_ne_zero]
    intro h0
    have : (m : ↥A) = 0 := Subtype.ext (by simpa using h0)
    exact hM m.2 (by rw [this]; exact 𝔭.zero_mem)
  let g : C →+* F := IsLocalization.lift (M := M) hunit
  have hg_alg : ∀ a : ↥A, g (algebraMap ↥A C a) = (a : F) := fun a => IsLocalization.lift_eq hunit a
  have hg_mk' : ∀ (a : ↥A) (m : M), g (IsLocalization.mk' C a m) = (a : F) * ((m : ↥A) : F)⁻¹ := by
    intro a m
    have hm0 : ((m : ↥A) : F) ≠ 0 := (hunit m).ne_zero
    rw [eq_mul_inv_iff_mul_eq₀ hm0]
    have := congrArg g (IsLocalization.mk'_spec C a m)
    rwa [map_mul, hg_alg, hg_alg] at this

  have hform : ∀ x : C, IsFracAt A 𝔭 (g x) := by
    intro x
    obtain ⟨⟨a, m⟩, rfl⟩ := IsLocalization.mk'_surjective M x
    exact ⟨a, m, hM m.2, hg_mk' a m⟩
  have hout : ∀ u : C, u ∉ Ideal.map (algebraMap ↥A C) 𝔭 →
      ∃ a s : ↥A, a ∉ 𝔭 ∧ s ∉ 𝔭 ∧ g u = (a : F) * ((s : F))⁻¹ := by
    intro u hu
    obtain ⟨⟨a, m⟩, rfl⟩ := IsLocalization.mk'_surjective M u
    refine ⟨a, m, fun ha => hu ?_, hM m.2, hg_mk' a m⟩
    exact (IsLocalization.mk'_mem_map_algebraMap_iff M C 𝔭 a m).mpr ⟨1, M.one_mem, by simpa using ha⟩

  letI : Algebra C F := g.toAlgebra
  haveI : IsScalarTower R C F := IsScalarTower.of_algebraMap_eq fun r => by
    rw [RingHom.algebraMap_toAlgebra, IsScalarTower.algebraMap_apply R ↥A C, hg_alg,
      IsScalarTower.algebraMap_apply R ↥A F]
    rfl
  haveI : SMulCommClass R C F := ⟨fun r c x => by simp only [Algebra.smul_def]; ring⟩
  let Φ := KaehlerDifferential.map R R C F
  have hΦ : ∀ x : C, Φ (KaehlerDifferential.D R C x) = KaehlerDifferential.D R F (g x) := fun x =>
    KaehlerDifferential.map_D R R C F x
  have hΦsmul : ∀ (u : C) (ω : Ω[C⁄R]), Φ (u • ω) = g u • Φ ω := fun u ω => by
    rw [map_smul, ← IsScalarTower.algebraMap_smul F u (Φ ω)]
    rfl

  obtain ⟨t₀, ht₀⟩ := hC
  refine ⟨g t₀, hform t₀, fun b => ?_⟩
  obtain ⟨u, c, hu, huc⟩ := ht₀ (algebraMap ↥A C b)
  obtain ⟨a, s, ha, hs, hgu⟩ := hout u hu
  obtain ⟨a', s', hs', hgc⟩ := hform c
  have key := congrArg Φ huc
  rw [hΦsmul, hΦsmul, hΦ, hΦ, hg_alg] at key

  have hgu0 : g u ≠ 0 := by
    rw [hgu]
    exact mul_ne_zero (fun h => ha (by rw [show a = 0 from Subtype.ext (by simpa using h)]; exact 𝔭.zero_mem))
      (inv_ne_zero (fun h => hs (by rw [show s = 0 from Subtype.ext (by simpa using h)]; exact 𝔭.zero_mem)))
  refine ⟨(g u)⁻¹ * g c, ⟨a' * s, s' * a, ?_, ?_⟩, ?_⟩
  · exact fun h => (h𝔭.mem_or_mem h).elim hs' ha
  · rw [hgu, hgc]
    push_cast
    rw [mul_inv, mul_inv, inv_inv]
    ring
  · rw [mul_smul, ← key, smul_smul, inv_mul_cancel₀ hgu0, one_smul]

end Transport

section LocallySmooth

universe u

variable {R : Type u} [CommRing R] {F : Type u} [Field F] [Algebra R F]
  (A : Subalgebra R F) (𝔭 : Ideal ↥A) [h𝔭 : 𝔭.IsPrime]

theorem exists_frame_of_locally (s : ↥A) (hs : s ∉ 𝔭)
    (hloc : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1)
      (algebraMap R (Localization.Away s))) :
    ∃ t : F, IsFracAt A 𝔭 t ∧ ∀ b : ↥A, ∃ c : F, IsFracAt A 𝔭 c ∧
      KaehlerDifferential.D R F (b : F) = c • KaehlerDifferential.D R F t := by
  obtain ⟨S, hS, hP⟩ := hloc
  let As := Localization.Away s
  let 𝔭s : Ideal As := Ideal.map (algebraMap ↥A As) 𝔭
  haveI h𝔭s : 𝔭s.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers s) As 𝔭 h𝔭
    ((Ideal.disjoint_powers_iff_notMem s h𝔭.isRadical).mpr hs)
  obtain ⟨t, htS, ht⟩ : ∃ t ∈ S, t ∉ 𝔭s := by
    by_contra h
    push Not at h
    apply h𝔭s.ne_top
    rw [eq_top_iff, ← hS, Ideal.span_le]
    exact h
  let C := Localization.Away t
  have hPt := hP t htS
  rw [← IsScalarTower.algebraMap_eq R As C] at hPt
  haveI : Algebra.IsStandardSmoothOfRelativeDimension 1 R C :=
    (RingHom.isStandardSmoothOfRelativeDimension_algebraMap 1).mp hPt

  let N : Submonoid ↥A := IsLocalization.localizationLocalizationSubmodule (Submonoid.powers s) (Submonoid.powers t)
  haveI : IsLocalization N C := IsLocalization.localization_localization_isLocalization _ _ _
  have hN : N ≤ 𝔭.primeCompl := by
    intro x hx hx𝔭
    rw [IsLocalization.mem_localizationLocalizationSubmodule] at hx
    obtain ⟨⟨y, hy⟩, ⟨z, hz⟩, hxyz⟩ := hx
    have h1 : algebraMap ↥A As x ∈ 𝔭s := Ideal.mem_map_of_mem _ hx𝔭
    rw [hxyz] at h1
    rcases h𝔭s.mem_or_mem h1 with h | h
    · obtain ⟨n, rfl⟩ := hy
      exact ht (h𝔭s.mem_of_pow_mem n h)
    · obtain ⟨n, rfl⟩ := hz
      refine h𝔭s.ne_top (Ideal.eq_top_of_isUnit_mem _ h ?_)
      simp only [map_pow]
      exact (IsLocalization.Away.algebraMap_isUnit s).pow n

  haveI : (Ideal.map (algebraMap ↥A C) 𝔭).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint N C 𝔭 h𝔭 (Set.disjoint_left.mpr fun x hxN hx𝔭 => hN hxN hx𝔭)
  exact transport_frame A 𝔭 N hN C
    (exists_frame_of_isStandardSmoothOfRelativeDimension_one (R := R) (Ideal.map (algebraMap ↥A C) 𝔭))

end LocallySmooth

section BaseSwap

theorem D_eq_smul_D_of_tower {R K F : Type*} [CommRing R] [CommRing K] [CommRing F] [Algebra R K] [Algebra R F]
    [Algebra K F] [IsScalarTower R K F] {b t c : F}
    (h : KaehlerDifferential.D R F b = c • KaehlerDifferential.D R F t) :
    KaehlerDifferential.D K F b = c • KaehlerDifferential.D K F t := by
  have := congrArg (KaehlerDifferential.map R K F F) h
  simpa [KaehlerDifferential.map_D, map_smul] using this

end BaseSwap

section FrameGeom

variable (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
  (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))

omit [NeZero M] in

theorem exists_locally_isStandardSmoothOfRelativeDimension_away (𝔛 : XHDRModelAtP p M H hpM hj)
    (𝔭 : PrimeSpectrum ↥(AA p (ΓM M H) hj))
    (hx : (ιFin p (ΓM M H) hj).base 𝔭 ∈ 𝔛.smoothLocus) :
    ∃ s : ↥(AA p (ΓM M H) hj), s ∉ 𝔭.asIdeal ∧
      RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1)
        (algebraMap (R p) (Localization.Away s)) := by

  have hopen : IsOpen ((ιFin p (ΓM M H) hj).base ⁻¹' (𝔛.smoothLocus : Set (X p (ΓM M H) hj))) :=
    𝔛.smoothLocus.isOpen.preimage (ιFin p (ΓM M H) hj).base.hom.continuous
  obtain ⟨_, ⟨s, rfl⟩, hs𝔭, hsU⟩ :=
    (PrimeSpectrum.isTopologicalBasis_basic_opens (R := ↥(AA p (ΓM M H) hj))).exists_subset_of_mem_open hx hopen
  refine ⟨s, (PrimeSpectrum.mem_basicOpen _ _).mp hs𝔭, ?_⟩

  let f₁ : Spec (CommRingCat.of (Localization.Away s)) ⟶ Spec (CommRingCat.of ↥(AA p (ΓM M H) hj)) :=
    Spec.map (CommRingCat.ofHom (algebraMap ↥(AA p (ΓM M H) hj) (Localization.Away s)))
  have hrange : Set.range (f₁ ≫ ιFin p (ΓM M H) hj) ⊆ Set.range 𝔛.smoothLocus.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨y, rfl⟩
    have hy : f₁ y ∈ Set.range (PrimeSpectrum.comap (algebraMap ↥(AA p (ΓM M H) hj) (Localization.Away s))) :=
      ⟨y, rfl⟩
    rw [PrimeSpectrum.localization_away_comap_range (Localization.Away s) s] at hy
    rw [Scheme.Hom.comp_apply]
    exact hsU hy

  let l := IsOpenImmersion.lift 𝔛.smoothLocus.ι (f₁ ≫ ιFin p (ΓM M H) hj) hrange
  haveI : IsOpenImmersion (l ≫ 𝔛.smoothLocus.ι) := by
    rw [IsOpenImmersion.lift_fac]
    infer_instance
  haveI : IsOpenImmersion l := IsOpenImmersion.of_comp l 𝔛.smoothLocus.ι
  have h1 : SmoothOfRelativeDimension 1 (l ≫ (𝔛.smoothLocus.ι ≫ toBase p (ΓM M H) hj)) :=
    IsZariskiLocalAtSource.comp (P := @SmoothOfRelativeDimension 1) inferInstance l
  have h2 : l ≫ (𝔛.smoothLocus.ι ≫ toBase p (ΓM M H) hj) =
      Spec.map (CommRingCat.ofHom (algebraMap (R p) (Localization.Away s))) := by
    rw [← Category.assoc, IsOpenImmersion.lift_fac, Category.assoc]
    erw [TwoChartIntegralModel.ιFin_toBase]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  rw [h2] at h1
  have h3 := (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension 1)).mp h1
  simpa using h3

theorem frame (𝔛 : XHDRModelAtP p M H hpM hj) (𝔭 : PrimeSpectrum ↥(AA p (ΓM M H) hj))
    (hx : (ιFin p (ΓM M H) hj).base 𝔭 ∈ 𝔛.smoothLocus) :
    ∃ t : FF (ΓM M H),
      (∃ a s : ↥(AA p (ΓM M H) hj), s ∉ 𝔭.asIdeal ∧ t = (a : FF (ΓM M H)) * ((s : FF (ΓM M H)))⁻¹) ∧
      ∀ b : ↥(AA p (ΓM M H) hj), ∃ c : FF (ΓM M H),
        (∃ a s : ↥(AA p (ΓM M H) hj), s ∉ 𝔭.asIdeal ∧ c = (a : FF (ΓM M H)) * ((s : FF (ΓM M H)))⁻¹) ∧
        DQ (ΓM M H) (b : FF (ΓM M H)) = c • DQ (ΓM M H) t := by
  obtain ⟨s, hs, hloc⟩ := exists_locally_isStandardSmoothOfRelativeDimension_away p M H hpM hj 𝔛 𝔭 hx
  obtain ⟨t, ht, hall⟩ := exists_frame_of_locally (AA p (ΓM M H) hj) 𝔭.asIdeal s hs hloc

  have hT : @IsScalarTower (R p) ℚ (FF (ΓM M H)) _ (instQ (ΓM M H)).toSMul _ :=
    @IsScalarTower.of_algebraMap_eq (R p) ℚ (FF (ΓM M H)) _ _ _ _ (instQ (ΓM M H)) _ fun x =>
      (IsScalarTower.algebraMap_apply (R p) ℚ (FF (ΓM M H)) x).trans
        (RingHom.congr_fun (Subsingleton.elim _ _) _)
  refine ⟨t, ht, fun b => ?_⟩
  obtain ⟨c, hc, hD⟩ := hall b
  exact ⟨c, hc, @D_eq_smul_D_of_tower (R p) ℚ (FF (ΓM M H)) _ _ _ _ _ (instQ (ΓM M H)) hT _ _ _ hD⟩

end FrameGeom

section Level

theorem Gamma1_le_GammaH (M : ℕ) (H : Subgroup (ZMod M)ˣ) : CongruenceSubgroup.Gamma1 M ≤ CohCarrier.GammaH M H := by
  intro A hA
  rw [CongruenceSubgroup.Gamma1_mem] at hA
  obtain ⟨h00, h11, h10⟩ := hA
  have hA0 : A ∈ CongruenceSubgroup.Gamma0 M := CongruenceSubgroup.Gamma0_mem.mpr h10
  refine CohCarrier.mem_GammaH_iff.mpr ⟨hA0, ?_⟩
  have : CohCarrier.gamma0Units M ⟨A, hA0⟩ = 1 := by
    apply Units.ext
    rw [CohCarrier.val_gamma0Units, Units.val_one]
    exact h11
  rw [this]
  exact one_mem H

theorem finiteIndex_GammaH (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) : (CohCarrier.GammaH M H).FiniteIndex :=
  haveI : (CongruenceSubgroup.Gamma1 M).FiniteIndex := inferInstance
  Subgroup.finiteIndex_of_le (Gamma1_le_GammaH M H)

theorem T_mem_GammaH (M : ℕ) (H : Subgroup (ZMod M)ˣ) : ModularGroup.T ∈ CohCarrier.GammaH M H := by
  apply Gamma1_le_GammaH
  rw [CongruenceSubgroup.Gamma1_mem]
  refine ⟨?_, ?_, ?_⟩ <;> simp [ModularGroup.T]

end Level

section LocFrac

variable {K : Type*} [Field K] {A : Type*} [CommRing A] [Algebra A K]

def IsLocFrac (𝔭 : Ideal A) (x : K) : Prop := ∃ a s : A, s ∉ 𝔭 ∧ x = algebraMap A K a * (algebraMap A K s)⁻¹

end LocFrac

section Endgame

variable {k : Type*} [Field k] {K : Type*} [Field K] [Algebra k K]
  {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
  [Algebra A K] [IsFractionRing A K]

theorem endgame (𝔭 : Ideal A) [h𝔭 : 𝔭.IsPrime] (𝔓 : Ideal A) [h𝔓 : 𝔓.IsPrime]
    (hht : 𝔓.height = 1) (h𝔓𝔭 : 𝔓 ≤ 𝔭) (π : A) (hπ0 : π ≠ 0) (hπ𝔓 : π ∈ 𝔓)
    (hone : (Ideal.map (algebraMap A (Localization.AtPrime 𝔭)) (Ideal.span {π})).IsPrime)
    (η : Ω[K⁄k]) (t φ : K) (hη : η = φ • KaehlerDifferential.D k K t)
    (hDt : KaehlerDifferential.D k K t ≠ 0) (ht : IsLocFrac 𝔭 t)
    (hfr : ∀ b : A, ∃ c : K, IsLocFrac 𝔭 c ∧
      KaehlerDifferential.D k K (algebraMap A K b) = c • KaehlerDifferential.D k K t)
    (hφ : ∃ a b : A, b ∉ 𝔓 ∧ φ * algebraMap A K b = algebraMap A K a)
    (hgenV : ∀ V : ValuationSubring K, (∀ a : A, algebraMap A K a ∈ V) →
      (∀ s : A, s ∉ 𝔭 → (algebraMap A K s)⁻¹ ∈ V) → (algebraMap A K π)⁻¹ ∈ V →
      ∃ c ∈ V, ∃ t' ∈ V, η = c • KaehlerDifferential.D k K t') :
    ∃ s : A, s ∉ 𝔭 ∧ ∃ (n m : ℕ) (a b : Fin m → A),
      (algebraMap A K s ^ n) • η =
        ∑ i, algebraMap A K (a i) • KaehlerDifferential.D k K (algebraMap A K (b i)) := by
  have hinj : Function.Injective (algebraMap A K) := IsFractionRing.injective A K
  have hne0 : ∀ s : A, s ∉ 𝔭 → algebraMap A K s ≠ 0 := fun s hs h =>
    hs (by rw [(map_eq_zero_iff _ hinj).mp h]; exact 𝔭.zero_mem)
  have hπK0 : algebraMap A K π ≠ 0 := (map_ne_zero_iff _ hinj).mpr hπ0

  let S := Localization.AtPrime 𝔭
  have hunits : ∀ y : 𝔭.primeCompl, IsUnit (algebraMap A K y) := fun y => isUnit_iff_ne_zero.mpr (hne0 y y.2)
  letI : Algebra S K := (IsLocalization.lift (M := 𝔭.primeCompl) (S := S) hunits).toAlgebra
  have hSA : ∀ a : A, algebraMap S K (algebraMap A S a) = algebraMap A K a := fun a =>
    IsLocalization.lift_eq hunits a
  haveI : IsScalarTower A S K := IsScalarTower.of_algebraMap_eq fun a => (hSA a).symm
  haveI : IsFractionRing S K :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization 𝔭.primeCompl S K
  haveI : IsDomain S := IsLocalization.isDomain_localization (Ideal.primeCompl_le_nonZeroDivisors 𝔭)
  haveI : IsIntegrallyClosed S :=
    isIntegrallyClosed_of_isLocalization S 𝔭.primeCompl (Ideal.primeCompl_le_nonZeroDivisors 𝔭)
  haveI : IsNoetherianRing S := IsLocalization.isNoetherianRing 𝔭.primeCompl S inferInstance
  have hSinj : Function.Injective (algebraMap S K) := IsFractionRing.injective S K
  have hmk' : ∀ (a : A) (s : 𝔭.primeCompl),
      algebraMap S K (IsLocalization.mk' S a s) = algebraMap A K a * (algebraMap A K (s : A))⁻¹ := by
    intro a s
    rw [eq_mul_inv_iff_mul_eq₀ (hne0 s s.2)]
    have := congrArg (algebraMap S K) (IsLocalization.mk'_spec S a s)
    rwa [map_mul, hSA, hSA] at this

  have hmemS : ∀ x : K, x ∈ Set.range (algebraMap S K) ↔ IsLocFrac 𝔭 x := by
    intro x
    constructor
    · rintro ⟨y, rfl⟩
      obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective 𝔭.primeCompl y
      exact ⟨a, s, s.2, hmk' a s⟩
    · rintro ⟨a, s, hs, rfl⟩
      exact ⟨IsLocalization.mk' S a ⟨s, hs⟩, hmk' a ⟨s, hs⟩⟩

  have hfrS : ∀ y : S, ∃ e : S,
      KaehlerDifferential.D k K (algebraMap S K y) = algebraMap S K e • KaehlerDifferential.D k K t := by
    intro y
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective 𝔭.primeCompl y
    obtain ⟨ca, hca, hDa⟩ := hfr a
    obtain ⟨cs, hcs, hDs⟩ := hfr s
    obtain ⟨ya, hya⟩ := (hmemS ca).mpr hca
    obtain ⟨ys, hys⟩ := (hmemS cs).mpr hcs
    refine ⟨IsLocalization.mk' S 1 s * ya - IsLocalization.mk' S a s * IsLocalization.mk' S 1 s * ys, ?_⟩
    show KaehlerDifferential.D k K (algebraMap S K (IsLocalization.mk' S a s)) = _
    rw [hmk', exists_D_mul_inv_eq_smul hDa hDs]
    congr 1
    simp only [map_sub, map_mul, hmk', map_one, one_mul, hya, hys]

  let pS : Ideal S := Ideal.map (algebraMap A S) (Ideal.span {π})
  have hpS : pS.IsPrime := hone
  let 𝔓S : Ideal S := Ideal.map (algebraMap A S) 𝔓
  have hdisj : Disjoint (𝔭.primeCompl : Set A) (𝔓 : Set A) :=
    Set.disjoint_left.mpr fun a ha hb => ha (h𝔓𝔭 hb)
  have h𝔓S : 𝔓S.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint 𝔭.primeCompl S 𝔓 h𝔓 hdisj
  have hcomap𝔓 : 𝔓S.comap (algebraMap A S) = 𝔓 :=
    IsLocalization.comap_map_of_isPrime_disjoint 𝔭.primeCompl S h𝔓 hdisj
  have hpS_le : pS ≤ 𝔓S := Ideal.map_mono ((Ideal.span_singleton_le_iff_mem _).mpr hπ𝔓)
  have h𝔓min : 𝔓 ∈ (Ideal.span {π}).minimalPrimes :=
    (Ideal.height_eq_one_iff_mem_minimalPrimes_span_singleton_of_mem hπ0 𝔓 hπ𝔓).mp hht
  have hpS_eq : pS = 𝔓S := by
    apply le_antisymm hpS_le
    have h1 : Ideal.span {π} ≤ pS.comap (algebraMap A S) := Ideal.le_comap_map
    have h2 : pS.comap (algebraMap A S) ≤ 𝔓 := (Ideal.comap_mono hpS_le).trans hcomap𝔓.le
    have : (pS.comap (algebraMap A S)).IsPrime := Ideal.IsPrime.comap _
    have h3 : 𝔓 ≤ pS.comap (algebraMap A S) := h𝔓min.2 ⟨this, h1⟩ h2
    calc 𝔓S = Ideal.map (algebraMap A S) (pS.comap (algebraMap A S)) := by
          show Ideal.map (algebraMap A S) 𝔓 = _
          rw [le_antisymm h3 h2]
      _ ≤ pS := Ideal.map_comap_le

  have hπS0 : algebraMap A S π ≠ 0 := fun h => hπK0 (by rw [← hSA, h, map_zero])
  have key : ∀ Q : Ideal S, Q.IsPrime → Q.height = 1 →
      ∃ a s : S, s ∉ Q ∧ φ * algebraMap S K s = algebraMap S K a := by
    intro Q hQ hQ1
    haveI := hQ
    by_cases hπQ : algebraMap A S π ∈ Q
    ·
      have hQmin : Q ∈ pS.minimalPrimes := by
        have h : Q ∈ (Ideal.span {algebraMap A S π}).minimalPrimes :=
          (Ideal.height_eq_one_iff_mem_minimalPrimes_span_singleton_of_mem hπS0 Q hπQ).mp hQ1
        have hpS' : pS = Ideal.span {algebraMap A S π} := by
          simp only [pS, Ideal.map_span, Set.image_singleton]
        rwa [hpS']
      have hQeq : Q = pS := le_antisymm (hQmin.2 ⟨hpS, le_rfl⟩ hQmin.1.2) hQmin.1.2
      obtain ⟨a, b, hb, hab⟩ := hφ
      refine ⟨algebraMap A S a, algebraMap A S b, ?_, ?_⟩
      · rw [hQeq, hpS_eq]
        intro hb'
        exact hb (by rw [← hcomap𝔓]; exact Ideal.mem_comap.mpr hb')
      · rw [hSA, hSA]; exact hab
    ·
      obtain ⟨V, hVmem, hVS, -, -⟩ :=
        IsIntegrallyClosed.exists_valuationSubring_mem_iff_and_nonunits_iff_of_height_eq_one (K := K) Q hQ1
      have hAV : ∀ a : A, algebraMap A K a ∈ V := fun a => by rw [← hSA]; exact hVS _
      have hinvV : ∀ s : A, s ∉ 𝔭 → (algebraMap A K s)⁻¹ ∈ V := fun s hs => by
        rw [hVmem]
        refine ⟨1, algebraMap A S s, fun h => ?_, by rw [hSA, inv_mul_cancel₀ (hne0 s hs), map_one]⟩
        exact hQ.ne_top (Ideal.eq_top_of_isUnit_mem _ h (IsLocalization.map_units S (⟨s, hs⟩ : 𝔭.primeCompl)))
      have hπV : (algebraMap A K π)⁻¹ ∈ V := by
        rw [hVmem]
        exact ⟨1, algebraMap A S π, hπQ, by rw [hSA, inv_mul_cancel₀ hπK0, map_one]⟩
      obtain ⟨c, hcV, t', ht'V, hηc⟩ := hgenV V hAV hinvV hπV
      obtain ⟨c', s', hs'Q, ht's⟩ := (hVmem t').mp ht'V
      have hs'0 : algebraMap S K s' ≠ 0 := fun h => hs'Q (by
        rw [(map_eq_zero_iff _ hSinj).mp h]; exact Q.zero_mem)
      have ht'eq : t' = algebraMap S K c' * (algebraMap S K s')⁻¹ := by
        rw [← ht's, mul_assoc, mul_inv_cancel₀ hs'0, mul_one]
      obtain ⟨ec, hDc⟩ := hfrS c'
      obtain ⟨es, hDs⟩ := hfrS s'
      have hDt' := exists_D_mul_inv_eq_smul hDc hDs
      rw [← ht'eq] at hDt'
      have hφeq : φ = c * ((algebraMap S K s')⁻¹ * algebraMap S K ec -
          t' * (algebraMap S K s')⁻¹ * algebraMap S K es) := by
        apply smul_D_injective hDt
        rw [← hη, hηc, hDt', smul_smul]
      have hs'inv : (algebraMap S K s')⁻¹ ∈ V := by
        rw [hVmem]; exact ⟨1, s', hs'Q, by rw [inv_mul_cancel₀ hs'0, map_one]⟩
      have hφV : φ ∈ V := by
        rw [hφeq]
        exact mul_mem hcV (sub_mem (mul_mem hs'inv (hVS ec)) (mul_mem (mul_mem ht'V hs'inv) (hVS es)))
      exact (hVmem φ).mp hφV

  obtain ⟨aφ, sφ, hsφ, hφ'⟩ : IsLocFrac 𝔭 φ :=
    (hmemS φ).mp (IsIntegrallyClosed.mem_range_algebraMap_of_forall_height_eq_one φ key)

  obtain ⟨a₁, s₁, hs₁, rfl⟩ := ht
  have hφmul : φ * algebraMap A K sφ = algebraMap A K aφ := by
    rw [hφ', mul_assoc, inv_mul_cancel₀ (hne0 sφ hsφ), mul_one]
  have hfinal := clear_denominators hη rfl hφmul (hne0 s₁ hs₁) (hne0 sφ hsφ)
  refine ⟨sφ * s₁ ^ 2, ?_, 1, 2, ![aφ * s₁, -(aφ * a₁)], ![a₁, s₁], ?_⟩
  · intro hmem
    rcases h𝔭.mem_or_mem hmem with h | h
    · exact hsφ h
    · exact hs₁ (h𝔭.mem_of_pow_mem 2 h)
  · simp only [pow_one, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, map_mul, map_pow, map_neg]
    exact hfinal

end Endgame

end E2Body
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_exists_pow_smul_eq_sum_smul_D_chartAlgFin_of_mem_gauss_of_mem_smoothLocus.E2Body"

open E2Body in

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (hj : ModularCurve.jqModC ℚ ∈ ModularCurve.qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : ModularCurve.XHDRModelAtP p M H hpM hj)

    (W₀ : ValuationSubring ↥(ModularCurve.qExpFunctionFieldC ℚ (ModularCurve.XHDRLevel.ΓM M H)))
    (hW₀ : (∀ f₀ : ↥(ModularCurve.qExpFunctionFieldC ℚ (ModularCurve.XHDRLevel.ΓM M H)), f₀ ∈ W₀ ↔
        ∃ a a' : PowerSeries ↥(GaloisRep.ratLocalizedAt p), a'.map (GaloisRep.ratLocalizedAtResidue p) ≠ 0 ∧
        (f₀ : LaurentSeries ℚ) * HahnSeries.ofPowerSeries ℤ ℚ (a'.map (GaloisRep.ratLocalizedAt p).subtype) =
          HahnSeries.ofPowerSeries ℤ ℚ (a.map (GaloisRep.ratLocalizedAt p).subtype)))

    (η : (@KaehlerDifferential ℚ ↥(ModularCurve.qExpFunctionFieldC ℚ (ModularCurve.XHDRLevel.ΓM M H)) _ _ (ModularCurve.instAlgebraIntermediateFieldLaurent (ModularCurve.qExpFunctionFieldC ℚ (ModularCurve.XHDRLevel.ΓM M H)))))
    (g : ↥(ModularCurve.qExpFunctionFieldC ℚ (ModularCurve.XHDRLevel.ΓM M H))) (hg : g ∈ W₀)
    (hη : η = g • @KaehlerDifferential.D ℚ ↥(ModularCurve.qExpFunctionFieldC ℚ (ModularCurve.XHDRLevel.ΓM M H)) _ _ (ModularCurve.instAlgebraIntermediateFieldLaurent (ModularCurve.qExpFunctionFieldC ℚ (ModularCurve.XHDRLevel.ΓM M H)))
      (ModularCurve.XHDRLevel.jAt (ModularCurve.XHDRLevel.ΓM M H) hj))

    (hgen : ∀ O : ValuationSubring ↥(ModularCurve.qExpFunctionFieldC ℚ (ModularCurve.XHDRLevel.ΓM M H)),
      (∀ a : ℚ, @algebraMap ℚ ↥(ModularCurve.qExpFunctionFieldC ℚ (ModularCurve.XHDRLevel.ΓM M H)) _ _ (ModularCurve.instAlgebraIntermediateFieldLaurent (ModularCurve.qExpFunctionFieldC ℚ (ModularCurve.XHDRLevel.ΓM M H))) a ∈ O) →
      ∃ c ∈ O, ∃ t ∈ O, η = c • @KaehlerDifferential.D ℚ ↥(ModularCurve.qExpFunctionFieldC ℚ (ModularCurve.XHDRLevel.ΓM M H)) _ _ (ModularCurve.instAlgebraIntermediateFieldLaurent (ModularCurve.qExpFunctionFieldC ℚ (ModularCurve.XHDRLevel.ΓM M H))) t)

    (𝔭 : PrimeSpectrum ↥(ModularCurve.XHDRLevel.chartAlgFin p (ModularCurve.XHDRLevel.ΓM M H) hj))
    (h𝔭p : algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.XHDRLevel.chartAlgFin p (ModularCurve.XHDRLevel.ΓM M H) hj)
      ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)) ∈ 𝔭.asIdeal)
    (hx : (ModularCurve.XHDRLevel.ιFin p (ModularCurve.XHDRLevel.ΓM M H) hj).base 𝔭 ∈ 𝔛.smoothLocus)

    (hx0 : ∀ s : ↥(ModularCurve.XHDRLevel.chartAlgFin p (ModularCurve.XHDRLevel.ΓM M H) hj), s ∉ 𝔭.asIdeal →
      ((s : ↥(ModularCurve.qExpFunctionFieldC ℚ (ModularCurve.XHDRLevel.ΓM M H))))⁻¹ ∈ W₀)
    (hone : (Ideal.map (algebraMap ↥(ModularCurve.XHDRLevel.chartAlgFin p (ModularCurve.XHDRLevel.ΓM M H) hj)
        (Localization.AtPrime 𝔭.asIdeal))
      (Ideal.span {algebraMap ↥(GaloisRep.ratLocalizedAt p)
        ↥(ModularCurve.XHDRLevel.chartAlgFin p (ModularCurve.XHDRLevel.ΓM M H) hj) ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p))})).IsPrime) :
    ∃ s : ↥(ModularCurve.XHDRLevel.chartAlgFin p (ModularCurve.XHDRLevel.ΓM M H) hj), s ∉ 𝔭.asIdeal ∧
      ∃ (n k : ℕ) (a b : Fin k → ↥(ModularCurve.XHDRLevel.chartAlgFin p (ModularCurve.XHDRLevel.ΓM M H) hj)),
        ((s : ↥(ModularCurve.qExpFunctionFieldC ℚ (ModularCurve.XHDRLevel.ΓM M H))) ^ n) • η =
          ∑ i, ((a i : ↥(ModularCurve.qExpFunctionFieldC ℚ (ModularCurve.XHDRLevel.ΓM M H)))) •
            @KaehlerDifferential.D ℚ ↥(ModularCurve.qExpFunctionFieldC ℚ (ModularCurve.XHDRLevel.ΓM M H)) _ _ (ModularCurve.instAlgebraIntermediateFieldLaurent (ModularCurve.qExpFunctionFieldC ℚ (ModularCurve.XHDRLevel.ΓM M H)))
              (b i : ↥(ModularCurve.qExpFunctionFieldC ℚ (ModularCurve.XHDRLevel.ΓM M H))) := by

  have : (ΓM M H).FiniteIndex := finiteIndex_GammaH M H
  have hT : ModularGroup.T ∈ ΓM M H := T_mem_GammaH M H
  change ∃ s : ↥(AA p (ΓM M H) hj), s ∉ 𝔭.asIdeal ∧ ∃ (n k : ℕ) (a b : Fin k → ↥(AA p (ΓM M H) hj)),
    ((s : FF (ΓM M H)) ^ n) • η = ∑ i, ((a i : FF (ΓM M H))) • DQ (ΓM M H) (b i : FF (ΓM M H))

  set pA : ↥(AA p (ΓM M H) hj) := algebraMap (R p) ↥(AA p (ΓM M H) hj) ((p : ℕ) : R p) with hpAdef
  have hcoepA : (pA : FF (ΓM M H)) = ((p : ℕ) : FF (ΓM M H)) := by
    rw [hpAdef, Subalgebra.coe_algebraMap]
    simp
  have hp0F : ((p : ℕ) : FF (ΓM M H)) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hpA0 : pA ≠ 0 := fun h => hp0F (by rw [← hcoepA, h]; rfl)

  obtain ⟨hAW, 𝔓, h𝔓, hht, hmem, hp𝔓, hloc⟩ := centre p (ΓM M H) hT hj W₀ hW₀
  have h𝔓𝔭 : 𝔓 ≤ 𝔭.asIdeal := centre_le hAW hmem 𝔭 hx0
  obtain ⟨hjW, -⟩ := jAt_mem_gauss p (ΓM M H) hj W₀ hW₀

  have hlocW : ∀ x : FF (ΓM M H), (∃ a s : ↥(AA p (ΓM M H) hj), s ∉ 𝔭.asIdeal ∧ x = (a : FF (ΓM M H)) * ((s : FF (ΓM M H)))⁻¹) →
      x ∈ W₀ := by
    rintro x ⟨a, s, hs, rfl⟩
    exact mul_mem (hAW a) (hx0 s hs)

  obtain ⟨t, ht, hfr⟩ := frame p M H hpM hj 𝔛 𝔭 hx

  obtain ⟨cj, hcj, hDcj⟩ := hfr (jA p (ΓM M H) hj)
  rw [coe_jA] at hDcj
  set j : FF (ΓM M H) := (jAt (ΓM M H) hj : FF (ΓM M H)) with hjdef
  have hj0 : j ≠ 0 := (fact_jAt_ne_zero (ΓM M H) hj).out
  have hDj := hDcj
  have hηφ := @smul_D_eq_of_D_eq ℚ _ (FF (ΓM M H)) _ (instQ (ΓM M H)) η g j _ t hη hDj
  set φ : FF (ΓM M H) := g * cj with hφdef

  have hφW : φ ∈ W₀ := mul_mem hg (hlocW cj hcj)
  obtain ⟨aφ, bφ, hbφ, hφab⟩ := (hloc φ).mp hφW

  have hDt : DQ (ΓM M H) t ≠ 0 := by
    have hiQ : (DivisionRing.toRatAlgebra : Algebra ℚ (FF (ΓM M H))) = instQ (ΓM M H) := Subsingleton.elim _ _

    have htrQ : Transcendental ℚ j := fun halg =>
      transcendental_jAt p (ΓM M H) hj ((IsFractionRing.isAlgebraic_iff (R p) ℚ (FF (ΓM M H))).mpr halg)

    have := finiteDimensional_adjoin (ΓM M H) hT hj
    have : CharZero ↥(IntermediateField.adjoin ℚ ({j} : Set (FF (ΓM M H)))) :=
      charZero_of_injective_algebraMap (algebraMap ℚ _).injective
    have : Algebra.IsAlgebraic ↥(IntermediateField.adjoin ℚ ({j} : Set (FF (ΓM M H)))) (FF (ΓM M H)) :=
      Algebra.IsAlgebraic.of_finite _ _
    have hsepQ : Algebra.IsSeparable ↥(IntermediateField.adjoin ℚ ({j} : Set (FF (ΓM M H)))) (FF (ΓM M H)) :=
      inferInstance
    have hDjne := @KaehlerDifferential.D_ne_zero_of_transcendental ℚ _ (FF (ΓM M H)) _ (instQ (ΓM M H)) j
      (transcendental_congr_inst j htrQ hiQ) (isSeparable_adjoin_congr_inst j hsepQ hiQ)
    exact @D_ne_zero_of_D_eq_smul ℚ _ (FF (ΓM M H)) _ (instQ (ΓM M H)) j t cj hDjne hDcj

  have hpF : algebraMap (R p) (FF (ΓM M H)) ((p : ℕ) : R p) = ((p : ℕ) : FF (ΓM M H)) := map_natCast _ p
  have hpR0 : ((p : ℕ) : R p) ≠ 0 := fun h => hp0F (by rw [← hpF, h, map_zero])
  have hpirr : Irreducible ((p : ℕ) : R p) :=
    IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal _ hpR0 (maximalIdeal_R p)
  have hval : ∀ V : ValuationSubring (FF (ΓM M H)),
      (∀ a : ↥(AA p (ΓM M H) hj), algebraMap ↥(AA p (ΓM M H) hj) (FF (ΓM M H)) a ∈ V) →
      (∀ s : ↥(AA p (ΓM M H) hj), s ∉ 𝔭.asIdeal → (algebraMap ↥(AA p (ΓM M H) hj) (FF (ΓM M H)) s)⁻¹ ∈ V) →
      (algebraMap ↥(AA p (ΓM M H) hj) (FF (ΓM M H)) pA)⁻¹ ∈ V →
      ∃ c ∈ V, ∃ t' ∈ V, η = c • DQ (ΓM M H) t' := by
    intro V hAV _ hpinvV
    change ((pA : FF (ΓM M H)))⁻¹ ∈ V at hpinvV
    rw [hcoepA] at hpinvV
    have hRV : ∀ r : R p, algebraMap (R p) (FF (ΓM M H)) r ∈ V := fun r => by
      have := hAV (algebraMap (R p) ↥(AA p (ΓM M H) hj) r)
      change ((algebraMap (R p) ↥(AA p (ΓM M H) hj) r : ↥(AA p (ΓM M H) hj)) : FF (ΓM M H)) ∈ V at this
      rwa [Subalgebra.coe_algebraMap] at this
    have hQV : ∀ q : ℚ, @algebraMap ℚ (FF (ΓM M H)) _ _ (instQ (ΓM M H)) q ∈ V := by
      intro q
      have hrh : (@algebraMap ℚ (FF (ΓM M H)) _ _ (instQ (ΓM M H)) : ℚ →+* FF (ΓM M H)) =
          algebraMap ℚ (FF (ΓM M H)) := Subsingleton.elim _ _
      rw [hrh]
      obtain ⟨r, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := R p) q
      rw [map_div₀, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply, div_eq_mul_inv]
      have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
      obtain ⟨k, u, hu⟩ := IsDiscreteValuationRing.associated_pow_irreducible hs0 hpirr
      have hinv : (algebraMap (R p) (FF (ΓM M H)) s)⁻¹ =
          algebraMap (R p) (FF (ΓM M H)) (u : R p) * (((p : ℕ) : FF (ΓM M H))⁻¹) ^ k := by
        apply inv_eq_of_mul_eq_one_right
        rw [← mul_assoc, ← map_mul, hu, map_pow, hpF, ← mul_pow, mul_inv_cancel₀ hp0F, one_pow]
      rw [hinv]
      exact mul_mem (hRV r) (mul_mem (hRV _) (pow_mem hpinvV k))
    exact hgen V hQV
  exact @endgame ℚ _ (FF (ΓM M H)) _ (instQ (ΓM M H)) ↥(AA p (ΓM M H) hj) _ inferInstance
    (isNoetherianRing_A p (ΓM M H) hT hj) (isIntegrallyClosed_A p (ΓM M H) hj) _ (isFractionRing_A p (ΓM M H) hT hj)
    𝔭.asIdeal inferInstance 𝔓 h𝔓 hht h𝔓𝔭 pA hpA0 hp𝔓 hone η t φ hηφ hDt ht hfr ⟨aφ, bφ, hbφ, hφab⟩ hval

end
end S_ModularCurve_XHDRModelAtP_exists_pow_smul_eq_sum_smul_D_chartAlgFin_of_mem_gauss_of_mem_smoothLocus
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_exists_pow_smul_eq_sum_smul_D_chartAlgFin_of_mem_gauss_of_mem_smoothLocus (solution)
