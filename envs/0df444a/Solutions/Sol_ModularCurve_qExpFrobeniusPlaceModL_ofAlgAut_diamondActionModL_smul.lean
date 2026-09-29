-- Prove2me | solution 1 for ModularCurve.qExpFrobeniusPlaceModL_ofAlgAut_diamondActionModL_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/7e23f856-4c92-5eb7-bcd1-2853e838c074

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental_of_perfectField
import Theorems.Thm_ModularCurve_qExpFrobeniusInputsModL_and_finrankAlong_of_transcendental
import Theorems.Thm_ModularCurve_IsDiamondPullbackModL_unique
import Theorems.Thm_ModularCurve_finiteDimensional_and_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index
import Theorems.Thm_ModularCurve_coeff_jqModC_neg_one
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_qExpFrobeniusPlaceModL_ofAlgAut_diamondActionModL_smul
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff"
p2m_attr_erase "simp" "ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

noncomputable section

p2m_open "Polynomial IntermediateField HahnSeries ModularCurve P2MW.S_ModularCurve_qExpFrobeniusPlaceModL_ofAlgAut_diamondActionModL_smul.ModularCurve AlgebraicCurve"

namespace ModularCurve
p2m_export "ModularCurve" "diamondActionModL isDiamondPullbackModL_diamondActionModL IsDiamondPullbackModL Gamma1_le_GammaH intSeriesC intFormRatiosC qExpFunctionFieldC intFormRatiosC_subset div_mem_qExpFunctionFieldC qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd jq ofPowerSeries_coeff_of_neg coeffMap coeffMap_coeff coeffMap_coeffMap coeffMap_id algebraMap_laurentSeries_eq_single coeffMap_algebraMap qExpFrobeniusModL coe_qExpFrobeniusModL qExpFrobeniusModL_isIntegral qExpFrobeniusPlaceModL mem_qExpFrobeniusPlaceModL_iff qExpFrobeniusDivPushforwardModL qExpFrobeniusDivPushforwardModL_single coe_qExpFrobeniusDegZeroPushforwardModL qExpFrobeniusPushforwardModL qExpFrobeniusPushforwardModL_mk pow_char_eq_coeffMap_frobenius_qExpand jqModC coeff_jqModC_neg_one qExpFrobeniusInputsModL_and_finrankAlong_of_transcendental IsDiamondPullbackModL.unique finiteDimensional_and_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index jqModC_mem_intFormRatiosC"
namespace QExpFrobBij
p2m_open "ModularCurve"

section Sigma

variable (K : Type*) [Field K] (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ))
variable {ℓ : ℕ} [Fact ℓ.Prime] [CharP K ℓ] [PerfectRing K ℓ]

abbrev FF : Type _ := qExpFunctionFieldC K Γ

omit [Fact ℓ.Prime] [CharP K ℓ] [PerfectRing K ℓ] in

theorem coeffMap_intSeriesC (g : K →+* K) (p : PowerSeries ℤ) : coeffMap g (intSeriesC K p) = intSeriesC K p := by
  ext k
  rw [coeffMap_coeff]
  rcases lt_or_ge k 0 with hk | hk
  · rw [intSeriesC, ofPowerSeries_coeff_of_neg _ hk, map_zero]
  · lift k to ℕ using hk with k
    rw [intSeriesC, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map, eq_intCast, map_intCast]

omit [Fact ℓ.Prime] [CharP K ℓ] [PerfectRing K ℓ] in

theorem coeffMap_mem (g : K →+* K) {x : LaurentSeries K} (hx : x ∈ qExpFunctionFieldC K Γ) :
    coeffMap g x ∈ qExpFunctionFieldC K Γ := by
  have hx' : x ∈ (qExpFunctionFieldC K Γ).toSubfield := hx
  rw [qExpFunctionFieldC, adjoin_toSubfield] at hx'
  have key : (Subfield.closure (Set.range (algebraMap K (LaurentSeries K)) ∪ intFormRatiosC K Γ)).map
      (coeffMap g) ≤ (qExpFunctionFieldC K Γ).toSubfield := by
    rw [RingHom.map_field_closure, Subfield.closure_le]
    rintro _ ⟨y, hy, rfl⟩
    rcases hy with ⟨c, rfl⟩ | ⟨k, f, g', pf, pg, hf, hg, hg0, rfl⟩
    · rw [coeffMap_algebraMap]
      exact (qExpFunctionFieldC K Γ).algebraMap_mem _
    · change coeffMap g (intSeriesC K pf / intSeriesC K pg) ∈ qExpFunctionFieldC K Γ
      rw [map_div₀, coeffMap_intSeriesC, coeffMap_intSeriesC]
      exact div_mem_qExpFunctionFieldC f g' hf hg hg0
  exact key ⟨x, hx', rfl⟩

omit [Fact ℓ.Prime] [CharP K ℓ] [PerfectRing K ℓ] in

theorem coeffMap_qExpand' (g : K →+* K) (n : ℕ) [NeZero n] (x : LaurentSeries K) :
    coeffMap g (qExpand K n x) = qExpand K n (coeffMap g x) := by
  ext k
  rw [coeffMap_coeff]
  by_cases hk : (n : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := hk
    rw [qExpand_coeff_mul, qExpand_coeff_mul, coeffMap_coeff]
  · rw [qExpand_coeff_of_not_dvd n _ hk, qExpand_coeff_of_not_dvd n _ hk, map_zero]

variable (ℓ)

def sigmaRingHom : FF K Γ →+* FF K Γ where
  toFun x := ⟨coeffMap (frobenius K ℓ) x, coeffMap_mem K Γ _ x.2⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)

def sigmaInvRingHom : FF K Γ →+* FF K Γ where
  toFun x := ⟨coeffMap ((frobeniusEquiv K ℓ).symm : K →+* K) x, coeffMap_mem K Γ _ x.2⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)

def sigma : FF K Γ ≃+* FF K Γ :=
  { sigmaRingHom K Γ ℓ with
    invFun := sigmaInvRingHom K Γ ℓ
    left_inv := fun x => Subtype.ext <| by
      change coeffMap _ (coeffMap _ (x : LaurentSeries K)) = (x : LaurentSeries K)
      rw [coeffMap_coeffMap]
      convert coeffMap_id (x : LaurentSeries K)
      ext a; exact (frobeniusEquiv K ℓ).symm_apply_apply a
    right_inv := fun x => Subtype.ext <| by
      change coeffMap _ (coeffMap _ (x : LaurentSeries K)) = (x : LaurentSeries K)
      rw [coeffMap_coeffMap]
      convert coeffMap_id (x : LaurentSeries K)
      ext a; exact (frobeniusEquiv K ℓ).apply_symm_apply a }

@[scoped simp] theorem coe_sigma (x : FF K Γ) : (sigma K Γ ℓ x : LaurentSeries K) = coeffMap (frobenius K ℓ) x := rfl

theorem frobenius_sigma (x : FF K Γ) : qExpFrobeniusModL K Γ ℓ (sigma K Γ ℓ x) = x ^ ℓ := by
  apply Subtype.ext
  rw [coe_qExpFrobeniusModL, coe_sigma, ← coeffMap_qExpand']
  push_cast
  exact (pow_char_eq_coeffMap_frobenius_qExpand ℓ (x : LaurentSeries K)).symm

theorem frobenius_eq_pow (y : FF K Γ) : qExpFrobeniusModL K Γ ℓ y = ((sigma K Γ ℓ).symm y) ^ ℓ := by
  conv_lhs => rw [← (sigma K Γ ℓ).apply_symm_apply y]
  exact frobenius_sigma K Γ ℓ _

theorem sigma_algebraMap (a : K) : sigma K Γ ℓ (algebraMap K (FF K Γ) a) = algebraMap K (FF K Γ) (a ^ ℓ) := by
  apply Subtype.ext
  change coeffMap (frobenius K ℓ) (algebraMap K (LaurentSeries K) a) = algebraMap K (LaurentSeries K) (a ^ ℓ)
  rw [coeffMap_algebraMap, frobenius_def]

def sigmaSL : SemilinearAut K (FF K Γ) :=
  ⟨(sigma K Γ ℓ, frobeniusEquiv K ℓ), fun a => by
    change sigma K Γ ℓ (algebraMap K (FF K Γ) a) = algebraMap K (FF K Γ) (frobeniusEquiv K ℓ a)
    rw [sigma_algebraMap, frobeniusEquiv_apply, frobenius_def]⟩

theorem sigmaSL_inv_smul (x : FF K Γ) : (sigmaSL K Γ ℓ)⁻¹ • x = (sigma K Γ ℓ).symm x := rfl

theorem pow_mem_valuationSubring_iff {F : Type*} [Field F] (O : ValuationSubring F) {n : ℕ} (hn : n ≠ 0)
    (u : F) : u ^ n ∈ O ↔ u ∈ O := by
  rw [← O.valuation_le_one_iff, ← O.valuation_le_one_iff, map_pow]
  exact pow_le_one_iff hn

theorem frobeniusPlace_eq_smul (w : Place K (FF K Γ)) :
    qExpFrobeniusPlaceModL K Γ ℓ w = sigmaSL K Γ ℓ • w := by
  apply Place.ext
  ext x
  rw [mem_qExpFrobeniusPlaceModL_iff, SemilinearAut.smul_toValuationSubring,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, sigmaSL_inv_smul, frobenius_eq_pow]
  exact pow_mem_valuationSubring_iff _ (Fact.out : ℓ.Prime).ne_zero _

end Sigma

section Divisors

variable (K : Type*) [Field K] [IsAlgClosed K] (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ))
variable (ℓ : ℕ) [Fact ℓ.Prime] [CharP K ℓ]
variable [hC : IsCurveOver K (FF K Γ)]

scoped instance perfectRing_of_isAlgClosed : PerfectRing K ℓ :=
  haveI := IsAlgClosed.perfectField K
  PerfectField.toPerfectRing ℓ

theorem deg_eq_one (w : Place K (FF K Γ)) : w.deg = 1 := IsCurveOver.deg_eq_one_of_isAlgClosed w

theorem inertiaDegAlong_frobenius (w : Place K (FF K Γ)) :
    Place.inertiaDegAlong (qExpFrobeniusModL K Γ ℓ) (qExpFrobeniusModL_isIntegral K Γ ℓ) w = 1 := by
  letI := algebraAlong (qExpFrobeniusModL K Γ ℓ)
  haveI := isScalarTower_along (qExpFrobeniusModL K Γ ℓ)
  haveI := isIntegral_along (qExpFrobeniusModL K Γ ℓ) (qExpFrobeniusModL_isIntegral K Γ ℓ)
  have h := Place.deg_restrict_mul_inertiaDeg (F := FF K Γ) w
  rw [deg_eq_one, deg_eq_one, one_mul] at h
  exact h

theorem divPushforward_eq_smul (D : Divisor K (FF K Γ)) :
    qExpFrobeniusDivPushforwardModL K Γ ℓ D = sigmaSL K Γ ℓ • D := by
  induction D using Finsupp.induction with
  | zero => rw [map_zero, smul_zero]
  | single_add v n D _ _ ih =>
    rw [map_add, smul_add, ih, qExpFrobeniusDivPushforwardModL_single, inertiaDegAlong_frobenius,
      Nat.cast_one, mul_one, frobeniusPlace_eq_smul, SemilinearAut.smul_single]

end Divisors

theorem main (K : Type*) [Field K] [IsAlgClosed K] {ℓ : ℕ} [Fact ℓ.Prime] [CharP K ℓ]
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ))
    (hF : ∃ x : qExpFunctionFieldC K Γ, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set (qExpFunctionFieldC K Γ))) (qExpFunctionFieldC K Γ)) :
    Function.Bijective (qExpFrobeniusPushforwardModL K Γ ℓ) := by
  haveI := IsAlgClosed.perfectField K

  obtain ⟨⟨hP, hfin, hFI, hN⟩, -⟩ := qExpFrobeniusInputsModL_and_finrankAlong_of_transcendental K Γ hF
  obtain ⟨x, htr, hfd⟩ := hF
  haveI : IsCurveOver K (FF K Γ) := AlgebraicCurve.isCurveOver_of_transcendental_of_perfectField htr hfd
  haveI := hP

  have key : ∀ y : Pic0 K (FF K Γ), qExpFrobeniusPushforwardModL K Γ ℓ y = sigmaSL K Γ ℓ • y := by
    intro y
    obtain ⟨D, rfl⟩ := Pic0.mk_surjective y
    rw [qExpFrobeniusPushforwardModL_mk hfin hFI hN, SemilinearAut.pic0_smul_mk]
    congr 1
    apply Subtype.ext
    rw [coe_qExpFrobeniusDegZeroPushforwardModL, SemilinearAut.coe_degZeroSMulHom]
    exact divPushforward_eq_smul K Γ ℓ D
  have hfun : (qExpFrobeniusPushforwardModL K Γ ℓ : Pic0 K (FF K Γ) → Pic0 K (FF K Γ)) =
      fun y => sigmaSL K Γ ℓ • y := funext key
  rw [hfun]
  exact MulAction.bijective (sigmaSL K Γ ℓ)

section Comm

variable (K : Type) [Field K] [IsAlgClosed K] (p : ℕ) [Fact p.Prime] [CharP K p]
variable (N : ℕ) [NeZero N] (H' : Subgroup (ZMod N)ˣ)

def sigmaConj (D : FF K (CohCarrier.GammaH N H') ≃ₐ[K] FF K (CohCarrier.GammaH N H')) :
    FF K (CohCarrier.GammaH N H') ≃ₐ[K] FF K (CohCarrier.GammaH N H') :=
  { ((sigma K (CohCarrier.GammaH N H') p).symm.trans (D.toRingEquiv.trans (sigma K (CohCarrier.GammaH N H') p))) with
    commutes' := fun a => by
      show sigma K _ p (D ((sigma K _ p).symm (algebraMap K _ a))) = algebraMap K _ a
      have hsurj : Function.Surjective (frobenius K p) := (frobeniusEquiv K p).surjective
      obtain ⟨b, rfl⟩ := hsurj a
      have e1 : (sigma K (CohCarrier.GammaH N H') p).symm (algebraMap K _ (frobenius K p b)) = algebraMap K _ b := by
        apply (sigma K (CohCarrier.GammaH N H') p).injective
        rw [RingEquiv.apply_symm_apply, sigma_algebraMap, frobenius_def]
      rw [e1, AlgEquiv.commutes, sigma_algebraMap, frobenius_def] }

theorem sigmaConj_apply (D : FF K (CohCarrier.GammaH N H') ≃ₐ[K] FF K (CohCarrier.GammaH N H')) (x : FF K (CohCarrier.GammaH N H')) :
    sigmaConj K p N H' D x = sigma K _ p (D ((sigma K _ p).symm x)) := rfl

def sigmaConjHom : (FF K (CohCarrier.GammaH N H') ≃ₐ[K] FF K (CohCarrier.GammaH N H')) →*
    (FF K (CohCarrier.GammaH N H') ≃ₐ[K] FF K (CohCarrier.GammaH N H')) where
  toFun := sigmaConj K p N H'
  map_one' := by
    apply AlgEquiv.ext; intro x
    rw [sigmaConj_apply, AlgEquiv.one_apply, AlgEquiv.one_apply, RingEquiv.apply_symm_apply]
  map_mul' D E := by
    apply AlgEquiv.ext; intro x
    simp only [sigmaConj_apply, AlgEquiv.mul_apply, RingEquiv.symm_apply_apply]

theorem coe_sigma_symm_of_coe_eq_div (x : FF K (CohCarrier.GammaH N H')) (pf pg : PowerSeries ℤ)
    (hx : (x : LaurentSeries K) = intSeriesC K pf / intSeriesC K pg) :
    (((sigma K (CohCarrier.GammaH N H') p).symm x : FF K (CohCarrier.GammaH N H')) : LaurentSeries K) =
      intSeriesC K pf / intSeriesC K pg := by
  change coeffMap ((frobeniusEquiv K p).symm : K →+* K) (x : LaurentSeries K) = _
  rw [hx, map_div₀, coeffMap_intSeriesC, coeffMap_intSeriesC]

theorem coe_sigma_of_coe_eq_div (x : FF K (CohCarrier.GammaH N H')) (pf pg : PowerSeries ℤ)
    (hx : (x : LaurentSeries K) = intSeriesC K pf / intSeriesC K pg) :
    ((sigma K (CohCarrier.GammaH N H') p x : FF K (CohCarrier.GammaH N H')) : LaurentSeries K) =
      intSeriesC K pf / intSeriesC K pg := by
  rw [coe_sigma, hx, map_div₀, coeffMap_intSeriesC, coeffMap_intSeriesC]

theorem isDiamondPullbackModL_sigmaConj
    {ρ : CongruenceSubgroup.Gamma0 N →* (FF K (CohCarrier.GammaH N H') ≃ₐ[K] FF K (CohCarrier.GammaH N H'))}
    (hρ : IsDiamondPullbackModL K N H' ρ) :
    IsDiamondPullbackModL K N H' ((sigmaConjHom K p N H').comp ρ) := by
  intro γ k f g f₁ g₁ pf pg pf₁ pg₁ hf hg hf₁ hg₁ hfs hgs hpg x hx
  show ((sigmaConj K p N H' (ρ γ) x : FF K _) : LaurentSeries K) = _
  rw [sigmaConj_apply]
  have h1 := coe_sigma_symm_of_coe_eq_div K p N H' x pf₁ pg₁ hx
  have h2 := hρ γ k f g f₁ g₁ pf pg pf₁ pg₁ hf hg hf₁ hg₁ hfs hgs hpg _ h1
  exact coe_sigma_of_coe_eq_div K p N H' _ pf pg h2

theorem sigma_diamondActionModL (hN : (N : K) ≠ 0) (γ : CongruenceSubgroup.Gamma0 N) (x : FF K (CohCarrier.GammaH N H')) :
    sigma K _ p (diamondActionModL K N H' γ x) = diamondActionModL K N H' γ (sigma K _ p x) := by
  by_cases h : ∃ ρ : CongruenceSubgroup.Gamma0 N →* (FF K (CohCarrier.GammaH N H') ≃ₐ[K] FF K (CohCarrier.GammaH N H')),
      IsDiamondPullbackModL K N H' ρ
  · have hρ : IsDiamondPullbackModL K N H' (diamondActionModL K N H') := isDiamondPullbackModL_diamondActionModL h
    have hρ' := isDiamondPullbackModL_sigmaConj K p N H' hρ
    have e := IsDiamondPullbackModL.unique K N hN H' hρ' hρ
    have ex : sigmaConj K p N H' (diamondActionModL K N H' γ) = diamondActionModL K N H' γ := by
      have := congrArg (fun ρ => ρ γ) e
      exact this
    have := congrArg (fun D : FF K _ ≃ₐ[K] FF K _ => D (sigma K _ p x)) ex
    simp only [sigmaConj_apply, RingEquiv.symm_apply_apply] at this
    exact this
  · have : diamondActionModL K N H' = 1 := by rw [diamondActionModL, dif_neg h]
    rw [this, MonoidHom.one_apply, AlgEquiv.one_apply, AlgEquiv.one_apply]

theorem sigmaSL_mul_ofAlgAut (hN : (N : K) ≠ 0) (γ : CongruenceSubgroup.Gamma0 N) :
    sigmaSL K (CohCarrier.GammaH N H') p * SemilinearAut.ofAlgAut (diamondActionModL K N H' γ) =
      SemilinearAut.ofAlgAut (diamondActionModL K N H' γ) * sigmaSL K (CohCarrier.GammaH N H') p := by
  apply Subtype.ext
  apply Prod.ext
  · apply RingEquiv.ext
    intro x
    exact sigma_diamondActionModL K p N H' hN γ x
  · apply RingEquiv.ext
    intro a
    rfl

theorem exists_transcendental_finiteDimensional (hN : (N : K) ≠ 0) :
    ∃ x : FF K (CohCarrier.GammaH N H'), Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set (FF K (CohCarrier.GammaH N H')))) (FF K (CohCarrier.GammaH N H')) := by
  have hj : jqModC K ∈ qExpFunctionFieldC K (CohCarrier.GammaH N H') :=
    intFormRatiosC_subset K _ (jqModC_mem_intFormRatiosC K _)
  let x : FF K (CohCarrier.GammaH N H') := ⟨jqModC K, hj⟩
  haveI : (CongruenceSubgroup.Gamma1 N).FiniteIndex := (CongruenceSubgroup.Gamma1_is_congruence N).finiteIndex
  haveI : (CohCarrier.GammaH N H').FiniteIndex := Subgroup.finiteIndex_of_le (ModularCurve.Gamma1_le_GammaH N H')
  have hT : ModularGroup.T ∈ CohCarrier.GammaH N H' := ModularCurve.Gamma1_le_GammaH N H' (by
    rw [CongruenceSubgroup.Gamma1_mem]; simp [ModularGroup.T])
  obtain ⟨hfin, -⟩ := finiteDimensional_and_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index K
    (CohCarrier.GammaH N H') hT (CohCarrier.GammaH N H') le_rfl (fun γ hγ => Or.inl hγ) x rfl
  refine ⟨x, ?_, hfin⟩

  intro halg
  have hint : IsIntegral K x := halg.isIntegral
  have hdeg : (minpoly K x).degree = 1 := IsAlgClosed.degree_eq_one_of_irreducible K (minpoly.irreducible hint)
  have hx : x = algebraMap K _ (-(minpoly K x).coeff 0) := by
    have h0 := minpoly.aeval K x
    rw [Polynomial.eq_X_add_C_of_degree_eq_one hdeg] at h0
    rw [(minpoly.monic hint).leadingCoeff] at h0
    simp only [map_one, one_mul, map_add, map_mul, Polynomial.aeval_X, Polynomial.aeval_C] at h0
    rw [map_neg, eq_neg_iff_add_eq_zero]; exact h0
  have hcoe := congrArg (fun y : FF K (CohCarrier.GammaH N H') => (y : LaurentSeries K).coeff (-1)) hx
  beta_reduce at hcoe
  change (jqModC K).coeff (-1) = (algebraMap K (LaurentSeries K) _).coeff (-1) at hcoe
  rw [coeff_jqModC_neg_one, algebraMap_laurentSeries_eq_single, HahnSeries.coeff_single_of_ne (by norm_num)] at hcoe
  exact one_ne_zero hcoe

theorem qExpFrobeniusPushforwardModL_eq_sigmaSL_smul (hN : (N : K) ≠ 0) (y : Pic0 K (FF K (CohCarrier.GammaH N H'))) :
    qExpFrobeniusPushforwardModL K (CohCarrier.GammaH N H') p y = sigmaSL K (CohCarrier.GammaH N H') p • y := by
  haveI := IsAlgClosed.perfectField K
  have hF := exists_transcendental_finiteDimensional K N H' hN
  obtain ⟨⟨hP, hfin, hFI, hNf⟩, -⟩ := qExpFrobeniusInputsModL_and_finrankAlong_of_transcendental K (CohCarrier.GammaH N H') hF
  obtain ⟨x, htr, hfd⟩ := hF
  haveI : IsCurveOver K (FF K (CohCarrier.GammaH N H')) := AlgebraicCurve.isCurveOver_of_transcendental_of_perfectField htr hfd
  haveI := hP
  obtain ⟨D, rfl⟩ := Pic0.mk_surjective y
  rw [qExpFrobeniusPushforwardModL_mk hfin hFI hNf, SemilinearAut.pic0_smul_mk]
  congr 1
  apply Subtype.ext
  rw [coe_qExpFrobeniusDegZeroPushforwardModL, SemilinearAut.coe_degZeroSMulHom]
  exact divPushforward_eq_smul K (CohCarrier.GammaH N H') p D

theorem comm (hpN : ¬ p ∣ N) (γ : CongruenceSubgroup.Gamma0 N) (z : Pic0 K (FF K (CohCarrier.GammaH N H'))) :
    qExpFrobeniusPushforwardModL K (CohCarrier.GammaH N H') p (SemilinearAut.ofAlgAut (diamondActionModL K N H' γ) • z) =
      SemilinearAut.ofAlgAut (diamondActionModL K N H' γ) • qExpFrobeniusPushforwardModL K (CohCarrier.GammaH N H') p z := by
  have hN : (N : K) ≠ 0 := by
    intro h; exact hpN ((CharP.cast_eq_zero_iff K p N).mp h)
  rw [qExpFrobeniusPushforwardModL_eq_sigmaSL_smul K p N H' hN, qExpFrobeniusPushforwardModL_eq_sigmaSL_smul K p N H' hN,
    ← mul_smul, sigmaSL_mul_ofAlgAut K p N H' hN γ, mul_smul]

end Comm

end ModularCurve.QExpFrobBij
p2m_reactivate "P2MW.S_ModularCurve_qExpFrobeniusPlaceModL_ofAlgAut_diamondActionModL_smul.ModularCurve P2MW.S_ModularCurve_qExpFrobeniusPlaceModL_ofAlgAut_diamondActionModL_smul.ModularCurve.QExpFrobBij"
p2m_reactivate "P2MW.S_ModularCurve_qExpFrobeniusPlaceModL_ofAlgAut_diamondActionModL_smul.ModularCurve"

end
p2m_reactivate "P2MW.S_ModularCurve_qExpFrobeniusPlaceModL_ofAlgAut_diamondActionModL_smul.ModularCurve P2MW.S_ModularCurve_qExpFrobeniusPlaceModL_ofAlgAut_diamondActionModL_smul.ModularCurve.QExpFrobBij"

p2m_open "ModularCurve P2MW.S_ModularCurve_qExpFrobeniusPlaceModL_ofAlgAut_diamondActionModL_smul.ModularCurve AlgebraicCurve"

theorem solution
    (K : Type) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] [IsAlgClosed K]
    (N : ℕ) [NeZero N] (hpN : ¬ p ∣ N) (H' : Subgroup (ZMod N)ˣ) (γ : CongruenceSubgroup.Gamma0 N)
    (w : Place K ↥(qExpFunctionFieldC K (CohCarrier.GammaH N H'))) :
    qExpFrobeniusPlaceModL K (CohCarrier.GammaH N H') p
        (SemilinearAut.ofAlgAut (diamondActionModL K N H' γ) • w) =
      SemilinearAut.ofAlgAut (diamondActionModL K N H' γ) •
        qExpFrobeniusPlaceModL K (CohCarrier.GammaH N H') p w := by
  haveI := IsAlgClosed.perfectField K
  haveI : PerfectRing K p := PerfectField.toPerfectRing p
  have hN : (N : K) ≠ 0 := by
    intro h
    exact hpN ((CharP.cast_eq_zero_iff K p N).mp h)
  rw [ModularCurve.QExpFrobBij.frobeniusPlace_eq_smul K (CohCarrier.GammaH N H') (ℓ := p),
    ModularCurve.QExpFrobBij.frobeniusPlace_eq_smul K (CohCarrier.GammaH N H') (ℓ := p),
    ← mul_smul, ← mul_smul, ModularCurve.QExpFrobBij.sigmaSL_mul_ofAlgAut K p N H' hN γ]

#print axioms solution

end S_ModularCurve_qExpFrobeniusPlaceModL_ofAlgAut_diamondActionModL_smul
end P2MW
export P2MW.S_ModularCurve_qExpFrobeniusPlaceModL_ofAlgAut_diamondActionModL_smul (solution)
