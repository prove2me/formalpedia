-- Prove2me | solution 1 for ModularCurve.isRegularLocalRing_of_isLocalization_atPrime_chartAlgInf_laurentBaseChange_cuspInfty
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/f6268086-0fa7-5035-b6a7-8041deeee743

import Mathlib
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_IgusaScheme
import Definitions.Def_GaloisRep_Flat
import Theorems.Thm_IsIntegrallyClosed_isRegularLocalRing_of_isLocalization_atPrime_of_ringHom_powerSeries_of_forall_minimalPrimes_le
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_ringHom_powerSeries_chartAlgInf_coe_eq_and_algebraMap_eq_coeff_zero
import Theorems.Thm_ModularCurve_IgusaScheme_exists_mul_eq_natCast_mul_add_jInvChartInf_mul_of_coeff_zero_mem
import Theorems.Thm_ModularCurve_IgusaScheme_finiteType_chartAlgFin_and_chartAlgInf
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_finiteType_chartAlgFin_and_chartAlgInf
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isIntegrallyClosed_chartAlg
import Theorems.Thm_ModularCurve_transcendental_coeffEmb_jq
import Theorems.Thm_ModularCurve_finiteDimensional_adjoin_coeffEmb_jq_full
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Theorems.Thm_GaloisRep_isFractionRing_ratLocalizedAt
import Theorems.Thm_GaloisRep_isDiscreteValuationRing_ratLocalizedAt
import Theorems.Thm_GaloisRep_irreducible_natCast_ratLocalizedAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_isRegularLocalRing_of_isLocalization_atPrime_chartAlgInf_laurentBaseChange_cuspInfty
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.qExpandAlgHomC_apply ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk"
p2m_attr_erase "simp" "ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_cuspidalDivisor₀"
p2m_attr_erase "simp" "ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul"

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

noncomputable section

open scoped Classical
open Polynomial ModularCurve ModularCurve.IgusaScheme AlgebraicCurve

namespace CuspBC

universe u

theorem single_mul_jq :
    HahnSeries.single (1 : ℤ) (1 : ℚ) * jq = ((jNumQ : PowerSeries ℚ) : LaurentSeries ℚ) := by
  rw [jq, ← mul_assoc, HahnSeries.single_mul_single, one_mul,
    show (1 : ℤ) + -1 = 0 by norm_num, HahnSeries.single_zero_one, one_mul]

theorem jq_inv_eq : (jq⁻¹ : LaurentSeries ℚ) =
    HahnSeries.single (1 : ℤ) (1 : ℚ) * ((jNumQ⁻¹ : PowerSeries ℚ) : LaurentSeries ℚ) := by
  have hc : PowerSeries.constantCoeff jNumQ ≠ 0 := by rw [constantCoeff_jNumQ]; exact one_ne_zero
  have h0 : HahnSeries.single (1 : ℤ) (1 : ℚ) * jq ≠ 0 := by
    rw [single_mul_jq]; intro h
    have h1 : ((jNumQ : PowerSeries ℚ) : LaurentSeries ℚ).coeff 0 = (0 : LaurentSeries ℚ).coeff 0 := by
      rw [h]
    rw [show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, LaurentSeries.coeff_coe_powerSeries,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_jNumQ, HahnSeries.coeff_zero] at h1
    exact one_ne_zero h1
  have hinv : (HahnSeries.single (1 : ℤ) (1 : ℚ) * jq)⁻¹ = ((jNumQ⁻¹ : PowerSeries ℚ) : LaurentSeries ℚ) := by
    apply mul_left_cancel₀ h0
    rw [mul_inv_cancel₀ h0, single_mul_jq, ← map_mul, PowerSeries.mul_inv_cancel _ hc, map_one]
  have h𝔮0 : (HahnSeries.single (1 : ℤ) (1 : ℚ) : LaurentSeries ℚ) ≠ 0 :=
    HahnSeries.single_ne_zero one_ne_zero
  rw [← hinv, mul_inv, ← mul_assoc, mul_inv_cancel₀ h𝔮0, one_mul]

theorem jq_inv_coeff_of_le_zero {n : ℤ} (hn : n ≤ 0) : (jq⁻¹ : LaurentSeries ℚ).coeff n = 0 := by
  rw [jq_inv_eq, HahnSeries.coeff_single_mul, one_mul, HahnSeries.ofPowerSeries_apply]
  exact HahnSeries.embDomain_notin_range (by rintro ⟨m, hm⟩; simp at hm; omega)

theorem jq_inv_coeff_one : (jq⁻¹ : LaurentSeries ℚ).coeff 1 = 1 := by
  rw [jq_inv_eq, HahnSeries.coeff_single_mul, one_mul, show (1 : ℤ) - 1 = ((0 : ℕ) : ℤ) by norm_num,
    LaurentSeries.coeff_coe_powerSeries, PowerSeries.coeff_zero_eq_constantCoeff_apply,
    PowerSeries.constantCoeff_inv, constantCoeff_jNumQ, inv_one]

theorem coeff_zero_coe_powerSeries {R : Type*} [CommRing R] (F : PowerSeries R) :
    (F : LaurentSeries R).coeff 0 = PowerSeries.constantCoeff F := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, LaurentSeries.coeff_coe_powerSeries]

section ZpLevel

variable (M p : ℕ) [NeZero M] [hp : Fact p.Prime]

set_option quotPrecheck false in
set_option hygiene false in
local notation "F" => (↥(modularFunctionFieldFull M) : Type)
set_option quotPrecheck false in
set_option hygiene false in
local notation "Zp" => (↥(GaloisRep.ratLocalizedAt p) : Type)
set_option quotPrecheck false in
set_option hygiene false in
local notation "B0" => (↥(chartAlgInf M p) : Type)

scoped instance isDVR_Zp : IsDiscreteValuationRing Zp := GaloisRep.isDiscreteValuationRing_ratLocalizedAt p hp.out

scoped instance isFractionRing_Zp : IsFractionRing Zp ℚ := GaloisRep.isFractionRing_ratLocalizedAt p

theorem coe_algebraMap_full (r : Zp) :
    ((algebraMap Zp F r : F) : LaurentSeries ℚ) = HahnSeries.single 0 (r : ℚ) := by
  change ((algebraMap ℚ F (r : ℚ) : F) : LaurentSeries ℚ) = _
  rw [eq_ratCast (algebraMap ℚ _), SubfieldClass.coe_ratCast, ← eq_ratCast (algebraMap ℚ (LaurentSeries ℚ)),
    ModularCurve.algebraMap_apply_eq_single]

theorem igusa_algebraMap_eq (x : Zp) : algebraMap Zp F x =
    @algebraMap ℚ F _ _ (SubalgebraClass.toAlgebra (modularFunctionFieldFull M)) (algebraMap Zp ℚ x) := by
  apply Subtype.ext
  change ((algebraMap ℚ F (x : ℚ) : F) : LaurentSeries ℚ) = algebraMap ℚ (LaurentSeries ℚ) (x : ℚ)
  rw [eq_ratCast (algebraMap ℚ _), SubfieldClass.coe_ratCast, ← eq_ratCast (algebraMap ℚ (LaurentSeries ℚ))]

theorem igusa_tower : @IsScalarTower Zp ℚ F Algebra.toSMul
    (SubalgebraClass.toAlgebra (modularFunctionFieldFull M)).toSMul (igusaAlgebra M p).toSMul :=
  @IsScalarTower.of_algebraMap_eq Zp ℚ F _ _ _ _
    (SubalgebraClass.toAlgebra (modularFunctionFieldFull M)) (igusaAlgebra M p) (igusa_algebraMap_eq M p)

theorem exists_constChar :
    ∃ χ0 : B0 →+* Zp, ∀ b : B0, ((b : F) : LaurentSeries ℚ).coeff 0 = ((χ0 b : Zp) : ℚ) := by
  have hj : ∀ n : ℤ, n ≤ 0 → ((jFull M : F) : LaurentSeries ℚ)⁻¹.coeff n = 0 := by
    intro n hn; rw [coe_jFull]; exact jq_inv_coeff_of_le_zero hn
  obtain ⟨ι, χ, hι, hχ, -, -⟩ :=
    @TwoChartIntegralModel.exists_ringHom_powerSeries_chartAlgInf_coe_eq_and_algebraMap_eq_coeff_zero
      ℚ _ Zp _ _ _ _ _ (modularFunctionFieldFull M) (igusaAlgebra M p) (igusa_tower M p) (jFull M) _ hj
  refine ⟨χ, fun b => ?_⟩

  have h1 := hι b
  have h2 := hχ b
  have h3 : ((b : F) : LaurentSeries ℚ).coeff 0 = ((ι b : PowerSeries ℚ) : LaurentSeries ℚ).coeff 0 := by
    rw [h1]
  rw [h3, coeff_zero_coe_powerSeries, ← h2]
  rfl

theorem maximalIdeal_Zp : IsLocalRing.maximalIdeal Zp = Ideal.span {(p : Zp)} :=
  (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mp
    (GaloisRep.irreducible_natCast_ratLocalizedAt p hp.out)

theorem exists_mul_iff_not_isUnit (r : Zp) :
    (∃ c ∈ GaloisRep.ratLocalizedAt p, (r : ℚ) = (p : ℚ) * c) ↔ ¬ IsUnit r := by
  rw [show (¬ IsUnit r) ↔ r ∈ IsLocalRing.maximalIdeal Zp from Iff.rfl, maximalIdeal_Zp,
    Ideal.mem_span_singleton']
  constructor
  · rintro ⟨c, hc, hrc⟩
    exact ⟨⟨c, hc⟩, Subtype.ext (by simp [hrc, mul_comm])⟩
  · rintro ⟨c, hc⟩
    exact ⟨(c : ℚ), c.2, by rw [← hc]; simp [mul_comm]⟩

end ZpLevel

section Main

variable (M p : ℕ) [NeZero M] [hp : Fact p.Prime]
variable (L : Type) [Field L] [CharZero L]
variable (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]

set_option quotPrecheck false in
set_option hygiene false in
local notation "F" => (↥(modularFunctionFieldFull M) : Type)
set_option quotPrecheck false in
set_option hygiene false in
local notation "Zp" => (↥(GaloisRep.ratLocalizedAt p) : Type)
set_option quotPrecheck false in
set_option hygiene false in
local notation "B0" => (↥(chartAlgInf M p) : Type)
set_option quotPrecheck false in
set_option hygiene false in
local notation "Λ" => LaurentSeries L
set_option quotPrecheck false in
set_option hygiene false in
local notation "KL" => laurentBaseChange L (modularFunctionFieldFull M)

theorem natCast_den_isUnit (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (r : Zp) :
    IsUnit (((r : ℚ).den : A)) := by
  by_contra hnu
  have hmem : (((r : ℚ).den : A)) ∈ IsLocalRing.maximalIdeal A := hnu
  have hcop : (r : ℚ).den.Coprime p := r.2
  obtain ⟨x, y, hxy⟩ := Nat.isCoprime_iff_coprime.mpr hcop
  have h1 : (x : A) * ((r : ℚ).den : A) + (y : A) * (p : A) = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → A) hxy
  have hmem1 : (1 : A) ∈ IsLocalRing.maximalIdeal A := by
    rw [← h1]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hmem) (Ideal.mul_mem_left _ _ hAp)
  exact (IsLocalRing.maximalIdeal.isMaximal A).ne_top ((Ideal.eq_top_iff_one _).mpr hmem1)

theorem exists_algebraMap_eq (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (r : Zp) :
    ∃ a : A, algebraMap A L a = algebraMap ℚ L (r : ℚ) := by
  obtain ⟨w, hw⟩ := natCast_den_isUnit p A hAp r
  refine ⟨((r : ℚ).num : A) * ((w⁻¹ : Aˣ) : A), ?_⟩
  have hden0 : (((r : ℚ).den : L)) ≠ 0 := by exact_mod_cast (r : ℚ).den_ne_zero
  have hwL : algebraMap A L (w : A) = ((r : ℚ).den : L) := by rw [hw]; simp
  have hwinv : algebraMap A L ((w⁻¹ : Aˣ) : A) = (((r : ℚ).den : L))⁻¹ := by
    rw [← hwL]
    refine (eq_inv_of_mul_eq_one_left ?_)
    rw [← map_mul, Units.inv_mul, map_one]
  rw [map_mul, hwinv, eq_ratCast, Rat.cast_def]
  simp [div_eq_mul_inv]

theorem algebraMap_injective : Function.Injective (algebraMap A L) := IsFractionRing.injective A L

def phi0 : F →+* ↥KL where
  toFun f := ⟨coeffEmb L (f : LaurentSeries ℚ), coeffEmb_mem_laurentBaseChange L f.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' a b := Subtype.ext (by simp)

@[scoped simp] theorem coe_phi0 (f : F) : ((phi0 M L f : ↥KL) : Λ) = coeffEmb L (f : LaurentSeries ℚ) := rfl

theorem coeff_coe_phi0 (f : F) (k : ℤ) :
    ((phi0 M L f : ↥KL) : Λ).coeff k = algebraMap ℚ L ((f : LaurentSeries ℚ).coeff k) := rfl

variable [Algebra A ↥KL] [IsScalarTower A L ↥KL]

theorem coe_algebraMap_KL (a : A) : ((algebraMap A ↥KL a : ↥KL) : Λ) = HahnSeries.single 0 (algebraMap A L a) := by
  rw [IsScalarTower.algebraMap_apply A L ↥KL a]
  show algebraMap L Λ (algebraMap A L a) = _
  rw [algebraMap_laurentSeries_eq_single]

theorem phi0_algebraMap {r : Zp} {a : A} (ha : algebraMap A L a = algebraMap ℚ L (r : ℚ)) :
    phi0 M L (algebraMap Zp F r) = algebraMap A ↥KL a := by
  apply Subtype.ext
  rw [coe_phi0, coe_algebraMap_full, coe_algebraMap_KL, coeffEmb, coeffMap_single, ha]

variable (j : ↥KL) [Fact (j ≠ 0)]

set_option quotPrecheck false in
set_option hygiene false in
local notation "B" => (↥(TwoChartIntegralModel.chartAlgInf A ↥KL j) : Type)
set_option quotPrecheck false in
set_option hygiene false in
local notation "uB" => TwoChartIntegralModel.jInvChartInf A ↥KL j

theorem phi0_jFull (hj : ((j : ↥KL) : Λ) = coeffEmb L jq) : phi0 M L (jFull M) = j :=
  Subtype.ext (by rw [coe_phi0, coe_jFull, hj])

theorem phi0_mem_adjoin (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hj : ((j : ↥KL) : Λ) = coeffEmb L jq)
    {x : F} (hx : x ∈ Algebra.adjoin Zp ({(jFull M)⁻¹} : Set F)) :
    phi0 M L x ∈ Algebra.adjoin A ({j⁻¹} : Set ↥KL) := by
  induction hx using Algebra.adjoin_induction with
  | mem y hy =>
    rw [Set.mem_singleton_iff] at hy; subst hy
    rw [map_inv₀, phi0_jFull M L j hj]
    exact Algebra.subset_adjoin rfl
  | algebraMap r =>
    obtain ⟨a, ha⟩ := exists_algebraMap_eq p L A hAp r
    rw [phi0_algebraMap M p L A ha]
    exact Subalgebra.algebraMap_mem _ a
  | add x y _ _ hx hy => rw [map_add]; exact Subalgebra.add_mem _ hx hy
  | mul x y _ _ hx hy => rw [map_mul]; exact Subalgebra.mul_mem _ hx hy

theorem phi0_mem_chart (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hj : ((j : ↥KL) : Λ) = coeffEmb L jq)
    (b : B0) : phi0 M L (b : F) ∈ TwoChartIntegralModel.chartAlgInf A ↥KL j := by
  change IsIntegral _ _
  have hb : IsIntegral ↥(Algebra.adjoin Zp ({(jFull M)⁻¹} : Set F)) (b : F) := b.2
  let κ : ↥(Algebra.adjoin Zp ({(jFull M)⁻¹} : Set F)) →+* ↥(Algebra.adjoin A ({j⁻¹} : Set ↥KL)) :=
    ((phi0 M L).comp (Algebra.adjoin Zp ({(jFull M)⁻¹} : Set F)).val.toRingHom).codRestrict _
      (fun x => phi0_mem_adjoin M p L A j hAp hj x.2)
  exact hb.map_of_comp_eq κ (phi0 M L) (by ext x; rfl)

def phi (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hj : ((j : ↥KL) : Λ) = coeffEmb L jq) : B0 →+* B :=
  ((phi0 M L).comp (chartAlgInf M p).val.toRingHom).codRestrict _ (fun b => phi0_mem_chart M p L A j hAp hj b)

@[scoped simp] theorem coe_phi (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hj : ((j : ↥KL) : Λ) = coeffEmb L jq) (b : B0) : ((phi M p L A j hAp hj b : B) : ↥KL) = phi0 M L (b : F) := rfl

theorem coe_coe_phi (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hj : ((j : ↥KL) : Λ) = coeffEmb L jq) (b : B0) : (((phi M p L A j hAp hj b : B) : ↥KL) : Λ) = coeffEmb L ((b : F) : LaurentSeries ℚ) := rfl

theorem phi_jInv (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hj : ((j : ↥KL) : Λ) = coeffEmb L jq) : phi M p L A j hAp hj (jInvChartInf M p) = uB := by
  apply Subtype.ext
  rw [coe_phi, IgusaScheme.coe_jInvChartInf, map_inv₀, phi0_jFull M L j hj]
  rfl

theorem phi_injective (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hj : ((j : ↥KL) : Λ) = coeffEmb L jq) : Function.Injective (phi M p L A j hAp hj) := by
  intro x y hxy
  have h := congrArg (fun z : B => ((z : ↥KL) : Λ)) hxy
  simp only [coe_coe_phi] at h
  apply Subtype.ext
  apply Subtype.ext
  ext k
  have hk := congrArg (fun z : Λ => z.coeff k) h
  simpa [coeffEmb_coeff] using hk

def Bp : Subalgebra A ↥KL := Algebra.adjoin A (Set.range fun b : B0 => phi0 M L (b : F))

theorem phi0_mem_Bp (b : B0) : phi0 M L (b : F) ∈ Bp M p L A := Algebra.subset_adjoin ⟨b, rfl⟩

theorem Bp_le (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hj : ((j : ↥KL) : Λ) = coeffEmb L jq) : Bp M p L A ≤ TwoChartIntegralModel.chartAlgInf A ↥KL j := by
  refine Algebra.adjoin_le ?_
  rintro _ ⟨b, rfl⟩
  exact phi0_mem_chart M p L A j hAp hj b

def phip : B0 →+* ↥(Bp M p L A) :=
  ((phi0 M L).comp (chartAlgInf M p).val.toRingHom).codRestrict _ (fun b => phi0_mem_Bp M p L A b)

@[scoped simp] theorem coe_phip (b : B0) : ((phip M p L A b : ↥(Bp M p L A)) : ↥KL) = phi0 M L (b : F) := rfl

def incl (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hj : ((j : ↥KL) : Λ) = coeffEmb L jq) : ↥(Bp M p L A) →ₐ[A] B := Subalgebra.inclusion (Bp_le M p L A j hAp hj)

@[scoped simp] theorem coe_incl (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hj : ((j : ↥KL) : Λ) = coeffEmb L jq) (x : ↥(Bp M p L A)) : ((incl M p L A j hAp hj x : B) : ↥KL) = (x : ↥KL) := rfl

theorem incl_injective (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hj : ((j : ↥KL) : Λ) = coeffEmb L jq) : Function.Injective (incl M p L A j hAp hj) := Subalgebra.inclusion_injective _

theorem incl_phip (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hj : ((j : ↥KL) : Λ) = coeffEmb L jq) (b : B0) : incl M p L A j hAp hj (phip M p L A b) = phi M p L A j hAp hj b := rfl

theorem finiteType_Bp (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) : Algebra.FiniteType A ↥(Bp M p L A) := by
  obtain ⟨s, hs⟩ := (finiteType_chartAlgFin_and_chartAlgInf M p).2.out
  rw [← Subalgebra.fg_iff_finiteType]
  refine ⟨s.image (fun b : B0 => phi0 M L (b : F)), le_antisymm ?_ ?_⟩
  · refine Algebra.adjoin_le ?_
    intro y hy
    rw [Finset.coe_image] at hy
    obtain ⟨b, -, rfl⟩ := hy
    exact phi0_mem_Bp M p L A b
  · refine Algebra.adjoin_le ?_
    rintro _ ⟨b, rfl⟩
    have hb : b ∈ Algebra.adjoin Zp (s : Set B0) := by rw [hs]; trivial
    show phi0 M L (b : F) ∈ Algebra.adjoin A (↑(s.image (fun b : B0 => phi0 M L (b : F))) : Set ↥KL)
    induction hb using Algebra.adjoin_induction with
    | mem y hy => exact Algebra.subset_adjoin (by rw [Finset.coe_image]; exact ⟨y, hy, rfl⟩)
    | algebraMap r =>
      obtain ⟨a, ha⟩ := exists_algebraMap_eq p L A hAp r
      have : phi0 M L ((algebraMap Zp B0 r : B0) : F) = algebraMap A ↥KL a := by
        rw [show ((algebraMap Zp B0 r : B0) : F) = algebraMap Zp F r from rfl]
        exact phi0_algebraMap M p L A ha
      rw [this]; exact Subalgebra.algebraMap_mem _ a
    | add x y _ _ hx hy => rw [Subalgebra.coe_add, map_add]; exact Subalgebra.add_mem _ hx hy
    | mul x y _ _ hx hy => rw [Subalgebra.coe_mul, map_mul]; exact Subalgebra.mul_mem _ hx hy

theorem isNoetherianRing_Bp (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) : IsNoetherianRing ↥(Bp M p L A) := by
  haveI := finiteType_Bp M p L A hAp
  exact Algebra.FiniteType.isNoetherianRing A ↥(Bp M p L A)

theorem coe_mem_span_of_mem_Bp (y : ↥(Bp M p L A)) :
    (y : ↥KL) ∈ Submodule.span A (Set.range fun b : B0 => phi0 M L (b : F)) := by
  have hy : (y : ↥KL) ∈ Subalgebra.toSubmodule
      (Algebra.adjoin A (Set.range fun b : B0 => phi0 M L (b : F))) := y.2
  rw [Algebra.adjoin_eq_span] at hy
  refine Submodule.span_mono ?_ hy

  let g : B0 →* ↥KL := ((phi0 M L).comp (chartAlgInf M p).val.toRingHom).toMonoidHom
  have : (Set.range fun b : B0 => phi0 M L (b : F)) = (MonoidHom.mrange g : Set ↥KL) := by
    ext z; simp [g]
  rw [this, Submonoid.closure_eq]

variable (𝔫 : Ideal B) [𝔫.IsPrime]

def NCond : Prop :=
  ∀ b : B, b ∈ 𝔫 ↔ ∃ c ∈ IsLocalRing.maximalIdeal A, ((b : ↥KL) : Λ).coeff 0 = algebraMap A L c

variable {𝔫}

theorem algebraMap_mem_iff (h𝔫 : NCond M L A j 𝔫) (a : A) :
    algebraMap A B a ∈ 𝔫 ↔ a ∈ IsLocalRing.maximalIdeal A := by
  rw [h𝔫]
  have hcoe : (((algebraMap A B a : B) : ↥KL) : Λ).coeff 0 = algebraMap A L a := by
    rw [show ((algebraMap A B a : B) : ↥KL) = algebraMap A ↥KL a from rfl, coe_algebraMap_KL,
      HahnSeries.coeff_single_same]
  rw [hcoe]
  constructor
  · rintro ⟨c, hc, hac⟩
    rwa [algebraMap_injective L A hac]
  · intro ha; exact ⟨a, ha, rfl⟩

theorem algebraMap_ϖ_mem (h𝔫 : NCond M L A j 𝔫) {ϖ : A} (hϖ : Irreducible ϖ) : algebraMap A B ϖ ∈ 𝔫 :=
  (algebraMap_mem_iff M L A j h𝔫 ϖ).mpr hϖ.not_isUnit

theorem uB_mem (h𝔫 : NCond M L A j 𝔫) (hj : ((j : ↥KL) : Λ) = coeffEmb L jq) : uB ∈ 𝔫 := by
  rw [h𝔫]
  refine ⟨0, Ideal.zero_mem _, ?_⟩
  rw [TwoChartIntegralModel.coe_jInvChartInf, IntermediateField.coe_inv, hj, ← map_inv₀, coeffEmb_coeff,
    jq_inv_coeff_of_le_zero le_rfl, map_zero, map_zero]

theorem phi_mem_of (h𝔫 : NCond M L A j 𝔫) (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A)
    (hj : ((j : ↥KL) : Λ) = coeffEmb L jq) (b : B0)
    (hb : ∃ c ∈ GaloisRep.ratLocalizedAt p, ((b : F) : LaurentSeries ℚ).coeff 0 = (p : ℚ) * c) :
    phi M p L A j hAp hj b ∈ 𝔫 := by
  obtain ⟨c, hc, hbc⟩ := hb
  obtain ⟨a, ha⟩ := exists_algebraMap_eq p L A hAp ⟨c, hc⟩
  rw [h𝔫]
  refine ⟨(p : A) * a, Ideal.mul_mem_right _ _ hAp, ?_⟩
  rw [coe_coe_phi, coeffEmb_coeff, hbc, map_mul, map_mul, ha, map_natCast, map_natCast]

theorem phi_not_mem_of (h𝔫 : NCond M L A j 𝔫) (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A)
    (hj : ((j : ↥KL) : Λ) = coeffEmb L jq) (s : B0)
    (hs : ¬ ∃ c ∈ GaloisRep.ratLocalizedAt p, ((s : F) : LaurentSeries ℚ).coeff 0 = (p : ℚ) * c) :
    phi M p L A j hAp hj s ∉ 𝔫 := by
  obtain ⟨χ0, hχ0⟩ := exists_constChar M p
  intro hmem
  rw [h𝔫] at hmem
  obtain ⟨c, hc, hsc⟩ := hmem
  rw [coe_coe_phi, coeffEmb_coeff, hχ0 s] at hsc
  rw [hχ0 s, exists_mul_iff_not_isUnit, not_not] at hs
  obtain ⟨v, hv⟩ := hs
  obtain ⟨a, ha⟩ := exists_algebraMap_eq p L A hAp (χ0 s)
  obtain ⟨a', ha'⟩ := exists_algebraMap_eq p L A hAp ((v⁻¹ : (Zp)ˣ) : Zp)
  have hac : a = c := algebraMap_injective L A (by rw [ha, hsc])
  have h1 : algebraMap A L (a * a') = algebraMap A L 1 := by
    rw [map_mul, ha, ha', map_one, ← map_mul, ← Subring.coe_mul, ← hv, Units.mul_inv]; simp
  have hunit : IsUnit a := IsUnit.of_mul_eq_one a' (algebraMap_injective L A h1)
  exact hc (hac ▸ hunit)

def np (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hj : ((j : ↥KL) : Λ) = coeffEmb L jq) :
    Ideal ↥(Bp M p L A) :=
  𝔫.comap (incl M p L A j hAp hj)

scoped instance np_isPrime (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hj : ((j : ↥KL) : Λ) = coeffEmb L jq) :
    (np M p L A j (𝔫 := 𝔫) hAp hj).IsPrime := Ideal.IsPrime.comap _

theorem mem_np_iff (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hj : ((j : ↥KL) : Λ) = coeffEmb L jq)
    (x : ↥(Bp M p L A)) : x ∈ np M p L A j (𝔫 := 𝔫) hAp hj ↔ incl M p L A j hAp hj x ∈ 𝔫 := Iff.rfl

def N0 : Set B0 := {b | ∃ c ∈ GaloisRep.ratLocalizedAt p, ((b : F) : LaurentSeries ℚ).coeff 0 = (p : ℚ) * c}

theorem decomp (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (y : ↥(Bp M p L A)) :
    ∃ a : A, ∃ z ∈ Submodule.span A (phip M p L A '' N0 M p),
      y = algebraMap A ↥(Bp M p L A) a + z := by
  obtain ⟨χ0, hχ0⟩ := exists_constChar M p
  suffices h : ∀ w ∈ Submodule.span A (Set.range fun b : B0 => phi0 M L (b : F)),
      ∃ a : A, ∃ z ∈ Submodule.span A (phip M p L A '' N0 M p),
        w = ((algebraMap A ↥(Bp M p L A) a + z : ↥(Bp M p L A)) : ↥KL) by
    obtain ⟨a, z, hz, hw⟩ := h (y : ↥KL) (coe_mem_span_of_mem_Bp M p L A y)
    exact ⟨a, z, hz, Subtype.ext hw⟩
  intro w hw
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨b, rfl⟩ := hw
    set r : Zp := χ0 b with hr
    obtain ⟨a, ha⟩ := exists_algebraMap_eq p L A hAp r
    have hb' : b - algebraMap Zp B0 r ∈ N0 M p := by
      refine ⟨0, Subring.zero_mem _, ?_⟩
      rw [mul_zero, Subalgebra.coe_sub, AddSubgroupClass.coe_sub, HahnSeries.coeff_sub, hχ0 b,
        show ((algebraMap Zp B0 r : B0) : F) = algebraMap Zp F r from rfl, coe_algebraMap_full,
        HahnSeries.coeff_single_same, sub_self]
    refine ⟨a, phip M p L A (b - algebraMap Zp B0 r), Submodule.subset_span ⟨_, hb', rfl⟩, ?_⟩
    rw [Subalgebra.coe_add, Subalgebra.coe_algebraMap, coe_phip, Subalgebra.coe_sub, map_sub,
      show ((algebraMap Zp B0 r : B0) : F) = algebraMap Zp F r from rfl, phi0_algebraMap M p L A ha]
    ring
  | zero => exact ⟨0, 0, Submodule.zero_mem _, by simp⟩
  | add w w' _ _ hw hw' =>
    obtain ⟨a, z, hz, rfl⟩ := hw
    obtain ⟨a', z', hz', rfl⟩ := hw'
    refine ⟨a + a', z + z', Submodule.add_mem _ hz hz', ?_⟩
    rw [← Subalgebra.coe_add, map_add]; congr 1; ring
  | smul a w _ hw =>
    obtain ⟨a', z, hz, rfl⟩ := hw
    refine ⟨a * a', a • z, Submodule.smul_mem _ _ hz, ?_⟩
    rw [← Subalgebra.coe_smul, smul_add, map_mul, Algebra.smul_def, Algebra.smul_def]

theorem span_N0_le_np (h𝔫 : NCond M L A j 𝔫) (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A)
    (hj : ((j : ↥KL) : Λ) = coeffEmb L jq) :
    Submodule.span A (phip M p L A '' N0 M p) ≤ (np M p L A j (𝔫 := 𝔫) hAp hj).restrictScalars A := by
  rw [Submodule.span_le]
  rintro _ ⟨b, hb, rfl⟩
  change phip M p L A b ∈ np M p L A j hAp hj
  rw [mem_np_iff, incl_phip]
  exact phi_mem_of M p L A j h𝔫 hAp hj b hb

section SLevel

variable (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hj : ((j : ↥KL) : Λ) = coeffEmb L jq)

set_option quotPrecheck false in
set_option hygiene false in
local notation "S" => Localization.AtPrime (np M p L A j (𝔫 := 𝔫) hAp hj)
set_option quotPrecheck false in
set_option hygiene false in
local notation "aS" => algebraMap ↥(Bp M p L A) (Localization.AtPrime (np M p L A j (𝔫 := 𝔫) hAp hj))
set_option quotPrecheck false in
set_option hygiene false in
local notation "uS" => algebraMap ↥(Bp M p L A) (Localization.AtPrime (np M p L A j (𝔫 := 𝔫) hAp hj))
  (phip M p L A (jInvChartInf M p))

theorem isNoetherianRing_S : IsNoetherianRing S := by
  haveI := isNoetherianRing_Bp M p L A hAp
  exact IsLocalization.isNoetherianRing (np M p L A j (𝔫 := 𝔫) hAp hj).primeCompl _ inferInstance

theorem aS_injective : Function.Injective aS :=
  IsLocalization.injective S (np M p L A j (𝔫 := 𝔫) hAp hj).primeCompl_le_nonZeroDivisors

theorem natCast_mem_span (ϖ : A) (hϖ : Irreducible ϖ) :
    (p : S) ∈ Ideal.span {aS (algebraMap A _ ϖ)} := by
  have hmax : IsLocalRing.maximalIdeal A = Ideal.span {ϖ} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ
  have hp' : (p : A) ∈ Ideal.span {ϖ} := hmax ▸ hAp
  obtain ⟨e, he⟩ := Ideal.mem_span_singleton'.mp hp'
  rw [show (p : S) = aS (algebraMap A _ (p : A)) by simp, ← he, map_mul, map_mul]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)

theorem aS_mem_span_pair_of_mem_span (h𝔫 : NCond M L A j 𝔫) (ϖ : A) (hϖ : Irreducible ϖ)
    {z : ↥(Bp M p L A)} (hz : z ∈ Submodule.span A (phip M p L A '' N0 M p)) :
    aS z ∈ Ideal.span {aS (algebraMap A _ ϖ), uS} := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨b, hb, rfl⟩ := hz
    obtain ⟨s, c, d, hs, hrel⟩ := exists_mul_eq_natCast_mul_add_jInvChartInf_mul_of_coeff_zero_mem M p b hb
    have hsn : phip M p L A s ∉ np M p L A j (𝔫 := 𝔫) hAp hj := by
      rw [mem_np_iff, incl_phip]; exact phi_not_mem_of M p L A j h𝔫 hAp hj s hs
    have hunit : IsUnit (aS (phip M p L A s)) :=
      IsLocalization.map_units S (⟨phip M p L A s, hsn⟩ : (np M p L A j (𝔫 := 𝔫) hAp hj).primeCompl)
    have hrel' : aS (phip M p L A s) * aS (phip M p L A b) =
        (p : S) * aS (phip M p L A c) + uS * aS (phip M p L A d) := by
      rw [← map_mul, ← map_mul, hrel]; simp
    have : aS (phip M p L A b) = ↑(hunit.unit⁻¹) *
        ((p : S) * aS (phip M p L A c) + uS * aS (phip M p L A d)) := by
      rw [← hrel', ← mul_assoc, IsUnit.val_inv_mul, one_mul]
    rw [this]
    refine Ideal.mul_mem_left _ _ (Ideal.add_mem _ ?_ ?_)
    · exact Ideal.mul_mem_right _ _
        ((Ideal.span_mono (Set.singleton_subset_iff.mpr (by simp)) ) (natCast_mem_span M p L A j hAp hj ϖ hϖ))
    · exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))
  | zero => rw [map_zero]; exact Ideal.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Ideal.add_mem _ hx hy
  | smul a x _ hx => rw [Algebra.smul_def, map_mul]; exact Ideal.mul_mem_left _ _ hx

theorem maximalIdeal_eq (h𝔫 : NCond M L A j 𝔫) (ϖ : A) (hϖ : Irreducible ϖ) :
    IsLocalRing.maximalIdeal S = Ideal.span {aS (algebraMap A _ ϖ), uS} := by
  have hmax : IsLocalRing.maximalIdeal A = Ideal.span {ϖ} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (np M p L A j (𝔫 := 𝔫) hAp hj) S]
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    obtain ⟨a, z, hz, rfl⟩ := decomp M p L A hAp x
    have hz' : z ∈ np M p L A j (𝔫 := 𝔫) hAp hj := span_N0_le_np M p L A j h𝔫 hAp hj hz
    have ha : algebraMap A ↥(Bp M p L A) a ∈ np M p L A j (𝔫 := 𝔫) hAp hj := by
      have := Ideal.sub_mem _ hx hz'
      rwa [add_sub_cancel_right] at this
    rw [mem_np_iff, AlgHom.commutes, algebraMap_mem_iff M L A j h𝔫, hmax,
      Ideal.mem_span_singleton'] at ha
    obtain ⟨e, rfl⟩ := ha
    rw [Ideal.mem_comap, map_add, map_mul, map_mul]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
      (aS_mem_span_pair_of_mem_span M p L A j hAp hj h𝔫 ϖ hϖ hz)
  · rw [Ideal.span_le]
    rintro x (rfl | rfl)
    · refine Ideal.mem_map_of_mem _ ?_
      rw [mem_np_iff, AlgHom.commutes]
      exact algebraMap_ϖ_mem M L A j h𝔫 hϖ
    · refine Ideal.mem_map_of_mem _ ?_
      rw [mem_np_iff, incl_phip, phi_jInv]
      exact uB_mem M L A j h𝔫 hj

theorem prime_eq_span_u (h𝔫 : NCond M L A j 𝔫) (ϖ : A) (hϖ : Irreducible ϖ)
    (𝔭 : Ideal S) [𝔭.IsPrime] (hu : uS ∈ 𝔭) (hϖ𝔭 : aS (algebraMap A _ ϖ) ∉ 𝔭) :
    𝔭 = Ideal.span {uS} := by
  haveI := isNoetherianRing_S M p L A j (𝔫 := 𝔫) hAp hj
  have hmS := maximalIdeal_eq M p L A j hAp hj h𝔫 ϖ hϖ
  apply le_antisymm
  ·
    have hle : (𝔭 : Submodule S S) ≤ Ideal.span {uS} ⊔ Ideal.span {aS (algebraMap A _ ϖ)} • 𝔭 := by
      intro x hx
      have hxm : x ∈ IsLocalRing.maximalIdeal S := IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top ‹_›) hx
      rw [hmS, Ideal.mem_span_pair] at hxm
      obtain ⟨c, d, rfl⟩ := hxm
      have hc : c * aS (algebraMap A _ ϖ) ∈ 𝔭 := by
        have := Ideal.sub_mem _ hx (Ideal.mul_mem_left _ d hu)
        rwa [add_sub_cancel_right] at this
      have hc' : c ∈ 𝔭 := ((Ideal.IsPrime.mem_or_mem ‹_› hc).resolve_right hϖ𝔭)
      rw [add_comm]
      refine Submodule.add_mem_sup ?_ ?_
      · exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
      · rw [Ideal.smul_eq_mul, Ideal.mem_span_singleton_mul]
        exact ⟨c, hc', mul_comm _ _⟩
    refine Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian _) ?_ hle
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top, hmS]
    exact Ideal.span_mono (by simp)
  · rw [Ideal.span_le, Set.singleton_subset_iff]; exact hu

theorem exists_pow_mul (h𝔫 : NCond M L A j 𝔫) (ϖ : A) (hϖ : Irreducible ϖ) (x : S) (hx : x ≠ 0) :
    ∃ (n : ℕ) (x' : S), x' ∉ Ideal.span {uS} ∧ x = uS ^ n * x' := by
  haveI := isNoetherianRing_S M p L A j (𝔫 := 𝔫) hAp hj
  have hne : Ideal.span {uS} ≠ ⊤ := by
    intro h
    have : uS ∈ IsLocalRing.maximalIdeal S := by
      rw [maximalIdeal_eq M p L A j hAp hj h𝔫 ϖ hϖ]; exact Ideal.subset_span (by simp)
    exact IsLocalRing.maximalIdeal.isMaximal S |>.ne_top
      (top_le_iff.mp (h ▸ (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr this))))
  have hkrull := Ideal.iInf_pow_eq_bot_of_isLocalRing (Ideal.span {uS}) hne
  have hex : ∃ n : ℕ, x ∉ Ideal.span {uS} ^ n := by
    by_contra hall
    push Not at hall
    have : x ∈ (⨅ i : ℕ, Ideal.span {uS} ^ i) := Ideal.mem_iInf.mpr hall
    rw [hkrull] at this
    exact hx this
  let n := Nat.find hex
  have hn : x ∉ Ideal.span {uS} ^ n := Nat.find_spec hex
  have hn0 : n ≠ 0 := by
    intro h0; rw [h0, pow_zero, Ideal.one_eq_top] at hn; exact hn trivial
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hn0
  have hxm : x ∈ Ideal.span {uS} ^ m := by
    have := Nat.find_min hex (m := m) (by omega)
    simpa using this
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at hxm
  obtain ⟨x', rfl⟩ := hxm
  refine ⟨m, x', ?_, by ring⟩
  intro hx'
  apply hn
  rw [hm, Ideal.span_singleton_pow, Ideal.mem_span_singleton']
  obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.mp hx'
  exact ⟨y, by rw [pow_succ]; ring⟩

end SLevel

theorem exists_pow_mul_jqN_mem (d : ℕ) [NeZero d] (hd : d ∣ M) :
    ∃ n : ℕ, (jFull M : F)⁻¹ ^ n * ⟨qExpand ℚ d jq, jqd_mem_full M hd⟩ ∈ chartAlgInf M p := by
  obtain ⟨Φ⟩ := nonempty_modularPolynomialData d
  set x : F := ⟨qExpand ℚ d jq, jqd_mem_full M hd⟩ with hxdef

  have hint : x ∈ IgusaScheme.chartAlg M p ({jFull M, (jFull M)⁻¹} : Set F) := by
    rw [IgusaScheme.mem_chartAlg_iff]
    let θ : Polynomial ℤ →+* ↥(Algebra.adjoin Zp ({jFull M, (jFull M)⁻¹} : Set F)) :=
      (Polynomial.aeval (R := ℤ) (⟨jFull M, Algebra.subset_adjoin (by simp)⟩ :
        ↥(Algebra.adjoin Zp ({jFull M, (jFull M)⁻¹} : Set F)))).toRingHom
    refine ⟨Φ.Φ.map θ, Φ.monic.map θ, ?_⟩
    have hinj : Function.Injective ((modularFunctionFieldFull M).subtype) := Subtype.val_injective
    apply hinj
    rw [map_zero, Polynomial.eval₂_map, Polynomial.hom_eval₂]
    have hcomp : ((modularFunctionFieldFull M).subtype).comp
        ((algebraMap ↥(Algebra.adjoin Zp ({jFull M, (jFull M)⁻¹} : Set F)) F).comp θ) = evalAtJ := by
      refine Polynomial.ringHom_ext (fun a => by simp [θ]) ?_
      simp [θ, evalAtJ]
      rfl
    rw [hcomp]
    exact Φ.eval_eq_zero
  have h := IgusaScheme.exists_pow_mul_mem_chartAlg (N := M) (ℓ := p) (S := ({(jFull M)⁻¹} : Set F))
    (s := (jFull M)⁻¹) rfl (inv_ne_zero (jFull_ne_zero M)) (x := x) (by rwa [inv_inv])
  exact h

theorem exists_frac_B0 (f : F) : ∃ b t : B0, t ≠ 0 ∧ f * (t : F) = b := by
  have hf : (f : LaurentSeries ℚ) ∈ Subfield.closure (Set.range (algebraMap ℚ (LaurentSeries ℚ)) ∪ divisorExpansions M) :=
    f.2
  suffices h : ∀ w ∈ Subfield.closure (Set.range (algebraMap ℚ (LaurentSeries ℚ)) ∪ divisorExpansions M),
      ∃ b t : B0, t ≠ 0 ∧ w * ((t : F) : LaurentSeries ℚ) = ((b : F) : LaurentSeries ℚ) by
    obtain ⟨b, t, ht, h⟩ := h _ hf
    exact ⟨b, t, ht, Subtype.ext (by simpa using h)⟩
  intro w hw
  induction hw using Subfield.closure_induction with
  | mem y hy =>
    rcases hy with ⟨c, rfl⟩ | ⟨d, hd0, hd, rfl⟩
    · refine ⟨(c.num : B0), (c.den : B0), by exact_mod_cast c.den_ne_zero, ?_⟩
      have h1 : algebraMap ℚ (LaurentSeries ℚ) c * (c.den : LaurentSeries ℚ) = (c.num : LaurentSeries ℚ) := by
        rw [← map_natCast (algebraMap ℚ (LaurentSeries ℚ)), ← map_intCast (algebraMap ℚ (LaurentSeries ℚ)),
          ← map_mul, Rat.mul_den_eq_num]
      simpa using h1
    · haveI := hd0
      obtain ⟨n, hn⟩ := exists_pow_mul_jqN_mem M p d hd
      refine ⟨⟨_, hn⟩, jInvChartInf M p ^ n, pow_ne_zero _ (fun h => ?_), ?_⟩
      · have := congrArg (fun z : B0 => (z : F)) h
        simp only [IgusaScheme.coe_jInvChartInf, ZeroMemClass.coe_zero, inv_eq_zero] at this
        exact jFull_ne_zero M this
      · simp [mul_comm]
  | one => exact ⟨1, 1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨b, t, ht, h⟩ := hx
    obtain ⟨b', t', ht', h'⟩ := hy
    refine ⟨b * t' + b' * t, t * t', mul_ne_zero ht ht', ?_⟩
    simp only [Subalgebra.coe_add, Subalgebra.coe_mul]
    push_cast
    linear_combination ((t' : F) : LaurentSeries ℚ) * h + ((t : F) : LaurentSeries ℚ) * h'
  | neg x _ hx =>
    obtain ⟨b, t, ht, h⟩ := hx
    refine ⟨-b, t, ht, ?_⟩
    simp only [Subalgebra.coe_neg]; push_cast; linear_combination -h
  | inv x _ hx =>
    obtain ⟨b, t, ht, h⟩ := hx
    by_cases hb : b = 0
    · refine ⟨0, 1, one_ne_zero, ?_⟩
      have hx0 : x = 0 := by
        have ht0 : ((t : F) : LaurentSeries ℚ) ≠ 0 := by
          intro h0; apply ht; exact Subtype.ext (Subtype.ext (by simpa using h0))
        have : x * ((t : F) : LaurentSeries ℚ) = 0 := by rw [h, hb]; simp
        exact (mul_eq_zero.mp this).resolve_right ht0
      simp [hx0]
    · refine ⟨t, b, hb, ?_⟩
      have hb0 : ((b : F) : LaurentSeries ℚ) ≠ 0 := by
        intro h0; apply hb; exact Subtype.ext (Subtype.ext (by simpa using h0))
      have hx0 : x ≠ 0 := by rintro rfl; rw [zero_mul] at h; exact hb0 h.symm
      exact ((eq_inv_mul_iff_mul_eq₀ hx0).mpr h).symm
  | mul x y _ _ hx hy =>
    obtain ⟨b, t, ht, h⟩ := hx
    obtain ⟨b', t', ht', h'⟩ := hy
    refine ⟨b * b', t * t', mul_ne_zero ht ht', ?_⟩
    simp only [Subalgebra.coe_mul]; push_cast
    linear_combination y * ((t' : F) : LaurentSeries ℚ) * h + ((b : F) : LaurentSeries ℚ) * h'

theorem exists_frac_Bp (y : ↥KL) : ∃ x t : ↥(Bp M p L A), t ≠ 0 ∧ y * (t : ↥KL) = x := by
  have hy : (y : Λ) ∈ Subfield.closure (Set.range (algebraMap L Λ) ∪
      (⇑(coeffEmb L) '' ((modularFunctionFieldFull M : IntermediateField ℚ (LaurentSeries ℚ)) : Set (LaurentSeries ℚ)))) :=
    y.2
  suffices h : ∀ w ∈ Subfield.closure (Set.range (algebraMap L Λ) ∪
      (⇑(coeffEmb L) '' ((modularFunctionFieldFull M : IntermediateField ℚ (LaurentSeries ℚ)) : Set (LaurentSeries ℚ)))),
      ∃ x t : ↥(Bp M p L A), t ≠ 0 ∧ w * ((t : ↥KL) : Λ) = ((x : ↥KL) : Λ) by
    obtain ⟨x, t, ht, h⟩ := h _ hy
    exact ⟨x, t, ht, Subtype.ext (by simpa using h)⟩
  have hinjA : Function.Injective (algebraMap A ↥(Bp M p L A)) := by
    intro a b hab
    have := congrArg (fun z : ↥(Bp M p L A) => ((z : ↥KL) : Λ)) hab
    simp only [Subalgebra.coe_algebraMap, coe_algebraMap_KL] at this
    exact algebraMap_injective L A (HahnSeries.single_injective 0 this)
  intro w hw
  induction hw using Subfield.closure_induction with
  | mem z hz =>
    rcases hz with ⟨c, rfl⟩ | ⟨f, hf, rfl⟩
    · obtain ⟨a, a', ha', rfl⟩ := IsFractionRing.div_surjective (A := A) c
      have ha'0 : a' ≠ 0 := nonZeroDivisors.ne_zero ha'
      refine ⟨algebraMap A _ a, algebraMap A _ a', fun h => ha'0 (hinjA (by rw [h, map_zero])), ?_⟩
      have h0 : algebraMap A L a' ≠ 0 := fun h => ha'0 (algebraMap_injective L A (by rw [h, map_zero]))
      simp only [Subalgebra.coe_algebraMap, coe_algebraMap_KL, ← algebraMap_laurentSeries_eq_single]
      rw [← map_mul, div_mul_cancel₀ _ h0]
    · obtain ⟨b, t, ht, hbt⟩ := exists_frac_B0 M p ⟨f, hf⟩
      refine ⟨phip M p L A b, phip M p L A t, fun h => ht ?_, ?_⟩
      · have := congrArg (fun z : ↥(Bp M p L A) => ((z : ↥KL) : Λ)) h
        simp only [coe_phip, coe_phi0, ZeroMemClass.coe_zero] at this
        apply Subtype.ext; apply Subtype.ext
        ext k
        have hk := congrArg (fun z : Λ => z.coeff k) this
        simpa [coeffEmb_coeff] using hk
      · have := congrArg (fun z : F => coeffEmb L (z : LaurentSeries ℚ)) hbt
        simpa using this
  | one => exact ⟨1, 1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨b, t, ht, h⟩ := hx
    obtain ⟨b', t', ht', h'⟩ := hy
    refine ⟨b * t' + b' * t, t * t', mul_ne_zero ht ht', ?_⟩
    simp only [Subalgebra.coe_add, Subalgebra.coe_mul]
    push_cast
    linear_combination ((t' : ↥KL) : Λ) * h + ((t : ↥KL) : Λ) * h'
  | neg x _ hx =>
    obtain ⟨b, t, ht, h⟩ := hx
    refine ⟨-b, t, ht, ?_⟩
    simp only [Subalgebra.coe_neg]; push_cast; linear_combination -h
  | inv x _ hx =>
    obtain ⟨b, t, ht, h⟩ := hx
    by_cases hb : b = 0
    · refine ⟨0, 1, one_ne_zero, ?_⟩
      have hx0 : x = 0 := by
        have ht0 : ((t : ↥KL) : Λ) ≠ 0 := by
          intro h0; apply ht; exact Subtype.ext (Subtype.ext (by simpa using h0))
        have : x * ((t : ↥KL) : Λ) = 0 := by rw [h, hb]; simp
        exact (mul_eq_zero.mp this).resolve_right ht0
      simp [hx0]
    · refine ⟨t, b, hb, ?_⟩
      have hb0 : ((b : ↥KL) : Λ) ≠ 0 := by
        intro h0; apply hb; exact Subtype.ext (Subtype.ext (by simpa using h0))
      have hx0 : x ≠ 0 := by rintro rfl; rw [zero_mul] at h; exact hb0 h.symm
      exact ((eq_inv_mul_iff_mul_eq₀ hx0).mpr h).symm
  | mul x y _ _ hx hy =>
    obtain ⟨b, t, ht, h⟩ := hx
    obtain ⟨b', t', ht', h'⟩ := hy
    refine ⟨b * b', t * t', mul_ne_zero ht ht', ?_⟩
    simp only [Subalgebra.coe_mul]; push_cast
    linear_combination y * ((t' : ↥KL) : Λ) * h + ((b : ↥KL) : Λ) * h'

section NonCollision

variable (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hj : ((j : ↥KL) : Λ) = coeffEmb L jq)
  (h𝔫 : NCond M L A j 𝔫) (ϖ : A) (hϖ : Irreducible ϖ)

set_option quotPrecheck false in
set_option hygiene false in
local notation "S" => Localization.AtPrime (np M p L A j (𝔫 := 𝔫) hAp hj)
set_option quotPrecheck false in
set_option hygiene false in
local notation "aS" => algebraMap ↥(Bp M p L A) (Localization.AtPrime (np M p L A j (𝔫 := 𝔫) hAp hj))
set_option quotPrecheck false in
set_option hygiene false in
local notation "u'" => phip M p L A (jInvChartInf M p)

include h𝔫 hϖ in

theorem exists_factor (x : ↥(Bp M p L A)) (hx : x ≠ 0) :
    ∃ (n : ℕ) (x₁ t₁ : ↥(Bp M p L A)) (ht₁ : t₁ ∉ np M p L A j (𝔫 := 𝔫) hAp hj),
      IsLocalization.mk' S x₁ (⟨t₁, ht₁⟩ : (np M p L A j (𝔫 := 𝔫) hAp hj).primeCompl) ∉
        Ideal.span {aS u'} ∧ x * t₁ = u' ^ n * x₁ := by
  have hx' : aS x ≠ 0 := fun h => hx (aS_injective M p L A j (𝔫 := 𝔫) hAp hj (by rw [h, map_zero]))
  obtain ⟨n, x', hx'u, hxx'⟩ := exists_pow_mul M p L A j (𝔫 := 𝔫) hAp hj h𝔫 ϖ hϖ (aS x) hx'
  obtain ⟨⟨x₁, t₁⟩, rfl⟩ := IsLocalization.mk'_surjective (np M p L A j (𝔫 := 𝔫) hAp hj).primeCompl x'
  refine ⟨n, x₁, t₁, t₁.2, hx'u, aS_injective M p L A j (𝔫 := 𝔫) hAp hj ?_⟩
  rw [map_mul, map_mul, map_pow, hxx', mul_assoc, IsLocalization.mk'_spec]

include h𝔫 hϖ in

theorem not_mem_of_mk'_not_mem (P : Ideal B) [P.IsPrime] (hP : P ≤ 𝔫) (huP : uB ∈ P)
    (hϖP : algebraMap A B ϖ ∉ P) (x₁ t₁ : ↥(Bp M p L A)) (ht₁ : t₁ ∉ np M p L A j (𝔫 := 𝔫) hAp hj)
    (h : IsLocalization.mk' S x₁ (⟨t₁, ht₁⟩ : (np M p L A j (𝔫 := 𝔫) hAp hj).primeCompl) ∉ Ideal.span {aS u'}) :
    incl M p L A j hAp hj x₁ ∉ P := by
  set Pp : Ideal ↥(Bp M p L A) := P.comap (incl M p L A j hAp hj) with hPp
  have hPp_prime : Pp.IsPrime := Ideal.IsPrime.comap _
  have hPp_le : Pp ≤ np M p L A j (𝔫 := 𝔫) hAp hj := fun y hy => hP hy
  have hdisj : Disjoint ((np M p L A j (𝔫 := 𝔫) hAp hj).primeCompl : Set ↥(Bp M p L A)) (Pp : Set _) := by
    rw [Set.disjoint_left]; intro y hy hyP; exact hy (hPp_le hyP)
  haveI h𝔭 : (Pp.map aS).IsPrime := IsLocalization.isPrime_of_isPrime_disjoint _ S Pp hPp_prime hdisj
  have hu𝔭 : aS u' ∈ Pp.map aS := by
    refine Ideal.mem_map_of_mem _ ?_
    change incl M p L A j hAp hj u' ∈ P
    rw [incl_phip, phi_jInv]; exact huP
  have hϖ𝔭 : aS (algebraMap A _ ϖ) ∉ Pp.map aS := by
    rw [IsLocalization.algebraMap_mem_map_algebraMap_iff (np M p L A j (𝔫 := 𝔫) hAp hj).primeCompl]
    rintro ⟨m, hm, hmϖ⟩
    change incl M p L A j hAp hj (m * algebraMap A _ ϖ) ∈ P at hmϖ
    rw [map_mul, AlgHom.commutes] at hmϖ
    rcases (Ideal.IsPrime.mem_or_mem ‹_› hmϖ) with h1 | h1
    · exact hm (hPp_le h1)
    · exact hϖP h1
  have heq := prime_eq_span_u M p L A j hAp hj h𝔫 ϖ hϖ (Pp.map aS) hu𝔭 hϖ𝔭
  intro hx₁
  apply h
  rw [← heq, IsLocalization.mk'_mem_map_algebraMap_iff (np M p L A j (𝔫 := 𝔫) hAp hj).primeCompl]
  exact ⟨1, Submonoid.one_mem _, by rw [one_mul]; exact hx₁⟩

include hAp hj h𝔫 hϖ in

theorem not_mem_of_not_mem (P P' : Ideal B) [P.IsPrime] [P'.IsPrime] (hP : P ≤ 𝔫) (hP' : P' ≤ 𝔫)
    (huP : uB ∈ P) (huP' : uB ∈ P') (hϖP : algebraMap A B ϖ ∉ P) (hϖP' : algebraMap A B ϖ ∉ P')
    (b : B) (hb : b ∉ P') : b ∉ P := by
  have hb0 : (b : ↥KL) ≠ 0 := by
    intro h0; apply hb; rw [show b = 0 from Subtype.ext h0]; exact Ideal.zero_mem _
  obtain ⟨x, t, ht, hxt⟩ := exists_frac_Bp M p L A ((b : ↥KL)⁻¹)
  have hx0 : x ≠ 0 := by
    intro hx0
    rw [hx0, ZeroMemClass.coe_zero, mul_eq_zero, inv_eq_zero] at hxt
    rcases hxt with h | h
    · exact hb0 h
    · exact ht (Subtype.ext (by simpa using h))
  obtain ⟨a, x₁, tx, htx, hx₁, hfx⟩ := exists_factor M p L A j hAp hj h𝔫 ϖ hϖ x hx0
  obtain ⟨c, t₁, tt, htt, ht₁, hft⟩ := exists_factor M p L A j hAp hj h𝔫 ϖ hϖ t ht

  have hI := fun (y : ↥(Bp M p L A)) => (rfl : ((incl M p L A j hAp hj y : B) : ↥KL) = (y : ↥KL))
  have huK : ((uB : B) : ↥KL) = ((u' : ↥(Bp M p L A)) : ↥KL) := by
    rw [← coe_incl M p L A j hAp hj, incl_phip, phi_jInv]

  have key : ((uB : B) : ↥KL) ^ c * (t₁ : ↥KL) * (tx : ↥KL) =
      (b : ↥KL) * (((uB : B) : ↥KL) ^ a * (x₁ : ↥KL) * (tt : ↥KL)) := by
    have e1 : (x : ↥KL) * (tx : ↥KL) = ((u' : ↥(Bp M p L A)) : ↥KL) ^ a * (x₁ : ↥KL) := by
      have := congrArg (fun z : ↥(Bp M p L A) => (z : ↥KL)) hfx; simpa using this
    have e2 : (t : ↥KL) * (tt : ↥KL) = ((u' : ↥(Bp M p L A)) : ↥KL) ^ c * (t₁ : ↥KL) := by
      have := congrArg (fun z : ↥(Bp M p L A) => (z : ↥KL)) hft; simpa using this
    rw [huK]
    have e3 : (b : ↥KL)⁻¹ * (t : ↥KL) = (x : ↥KL) := hxt
    have e4 : (t : ↥KL) = (b : ↥KL) * (x : ↥KL) := by
      rw [← e3, ← mul_assoc, mul_inv_cancel₀ hb0, one_mul]
    calc ((u' : ↥(Bp M p L A)) : ↥KL) ^ c * (t₁ : ↥KL) * (tx : ↥KL)
        = (t : ↥KL) * (tt : ↥KL) * (tx : ↥KL) := by rw [e2]
      _ = (b : ↥KL) * ((x : ↥KL) * (tx : ↥KL)) * (tt : ↥KL) := by rw [e4]; ring
      _ = (b : ↥KL) * (((u' : ↥(Bp M p L A)) : ↥KL) ^ a * (x₁ : ↥KL) * (tt : ↥KL)) := by rw [e1]; ring
  rcases le_or_gt c a with hca | hac
  ·
    have key' : (b : ↥KL) * (((uB : B) : ↥KL) ^ (a - c) * (x₁ : ↥KL) * (tt : ↥KL)) =
        (t₁ : ↥KL) * (tx : ↥KL) := by
      have hu0 : ((uB : B) : ↥KL) ≠ 0 := by
        rw [TwoChartIntegralModel.coe_jInvChartInf]; exact inv_ne_zero (Fact.out)
      have hpow : ((uB : B) : ↥KL) ^ a = ((uB : B) : ↥KL) ^ c * ((uB : B) : ↥KL) ^ (a - c) := by
        rw [← pow_add, Nat.add_sub_cancel' hca]
      apply mul_left_cancel₀ (pow_ne_zero c hu0)
      rw [hpow] at key
      linear_combination key.symm
    have hB : b * (uB ^ (a - c) * incl M p L A j hAp hj x₁ * incl M p L A j hAp hj tt) =
        incl M p L A j hAp hj t₁ * incl M p L A j hAp hj tx := by
      apply Subtype.ext
      simpa using key'
    intro hbP
    have hmem : incl M p L A j hAp hj t₁ * incl M p L A j hAp hj tx ∈ P := by
      rw [← hB]; exact Ideal.mul_mem_right _ _ hbP
    rcases Ideal.IsPrime.mem_or_mem ‹_› hmem with h1 | h1
    · exact not_mem_of_mk'_not_mem M p L A j hAp hj h𝔫 ϖ hϖ P hP huP hϖP t₁ tt htt ht₁ h1
    · exact htx (hP h1)
  ·
    exfalso
    have key' : ((uB : B) : ↥KL) ^ (c - a) * (t₁ : ↥KL) * (tx : ↥KL) =
        (b : ↥KL) * ((x₁ : ↥KL) * (tt : ↥KL)) := by
      have hu0 : ((uB : B) : ↥KL) ≠ 0 := by
        rw [TwoChartIntegralModel.coe_jInvChartInf]; exact inv_ne_zero (Fact.out)
      have hpow : ((uB : B) : ↥KL) ^ c = ((uB : B) : ↥KL) ^ a * ((uB : B) : ↥KL) ^ (c - a) := by
        rw [← pow_add, Nat.add_sub_cancel' hac.le]
      apply mul_left_cancel₀ (pow_ne_zero a hu0)
      rw [hpow] at key
      linear_combination key
    have hB : uB ^ (c - a) * incl M p L A j hAp hj t₁ * incl M p L A j hAp hj tx =
        b * (incl M p L A j hAp hj x₁ * incl M p L A j hAp hj tt) := by
      apply Subtype.ext
      simpa using key'
    have hlhs : uB ^ (c - a) * incl M p L A j hAp hj t₁ * incl M p L A j hAp hj tx ∈ P' := by
      refine Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ ?_)
      obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.sub_ne_zero_of_lt hac)
      rw [hk, pow_succ]; exact Ideal.mul_mem_left _ _ huP'
    rw [hB] at hlhs
    rcases Ideal.IsPrime.mem_or_mem ‹_› hlhs with h1 | h1
    · exact hb h1
    · rcases Ideal.IsPrime.mem_or_mem ‹_› h1 with h2 | h2
      · exact not_mem_of_mk'_not_mem M p L A j hAp hj h𝔫 ϖ hϖ P' hP' huP' hϖP' x₁ tx htx hx₁ h2
      · exact htt (hP' h2)

include h𝔫 hϖ hAp hj in

theorem eq_of_le_of_mem_of_not_mem (P P' : Ideal B) [P.IsPrime] [P'.IsPrime] (hP : P ≤ 𝔫) (hP' : P' ≤ 𝔫)
    (huP : uB ∈ P) (huP' : uB ∈ P') (hϖP : algebraMap A B ϖ ∉ P) (hϖP' : algebraMap A B ϖ ∉ P') :
    P = P' := by
  apply le_antisymm
  · intro b hb; by_contra hb'
    exact not_mem_of_not_mem M p L A j hAp hj h𝔫 ϖ hϖ P P' hP hP' huP huP' hϖP hϖP' b hb' hb
  · intro b hb; by_contra hb'
    exact not_mem_of_not_mem M p L A j hAp hj h𝔫 ϖ hϖ P' P hP' hP huP' huP hϖP' hϖP b hb' hb

end NonCollision

theorem isMaximal_of_mem_of_mem (ϖ : A) (hϖ : Irreducible ϖ) (P : Ideal B) [P.IsPrime]
    (hϖP : algebraMap A B ϖ ∈ P) (huP : uB ∈ P) : P.IsMaximal := by
  let R₀ : Subalgebra A ↥KL := Algebra.adjoin A ({j⁻¹} : Set ↥KL)
  have hR₀ : R₀ ≤ TwoChartIntegralModel.chartAlgInf A ↥KL j := TwoChartIntegralModel.adjoin_le_chartAlg A ↥KL _
  letI : Algebra ↥R₀ B := (Subalgebra.inclusion hR₀).toRingHom.toAlgebra
  haveI : IsScalarTower ↥R₀ B ↥KL := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : Algebra.IsIntegral ↥R₀ B := ⟨fun b =>
    (isIntegral_algebraMap_iff (Subtype.val_injective : Function.Injective (algebraMap B ↥KL))).mp b.2⟩
  refine Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := ↥R₀) P ?_
  have hmax : IsLocalRing.maximalIdeal A = Ideal.span {ϖ} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ
  rw [Ideal.isMaximal_iff]
  refine ⟨fun h1 => (Ideal.IsPrime.ne_top ‹_›) ((Ideal.eq_top_iff_one _).mpr (by simpa using h1)), ?_⟩
  intro J x hIJ hxI hxJ

  have hx : (x : ↥KL) ∈ (Polynomial.aeval (R := A) (j⁻¹ : ↥KL)).range := by
    rw [← Algebra.adjoin_singleton_eq_range_aeval]; exact x.2
  obtain ⟨q, hq⟩ := hx
  let uR : ↥R₀ := ⟨j⁻¹, Algebra.subset_adjoin rfl⟩
  let r : ↥R₀ := ⟨Polynomial.aeval (R := A) (j⁻¹ : ↥KL) q.divX, by
    show _ ∈ Algebra.adjoin A ({j⁻¹} : Set ↥KL)
    rw [Algebra.adjoin_singleton_eq_range_aeval]; exact ⟨_, rfl⟩⟩
  have hxeq : x = uR * r + algebraMap A ↥R₀ (q.coeff 0) := by
    apply Subtype.ext
    change (x : ↥KL) = j⁻¹ * Polynomial.aeval (R := A) (j⁻¹ : ↥KL) q.divX + algebraMap A ↥KL (q.coeff 0)
    rw [← hq]
    change Polynomial.aeval (R := A) (j⁻¹ : ↥KL) q = _
    calc Polynomial.aeval (R := A) (j⁻¹ : ↥KL) q
        = Polynomial.aeval (R := A) (j⁻¹ : ↥KL) (X * q.divX + C (q.coeff 0)) := by
          rw [Polynomial.X_mul_divX_add]
      _ = _ := by rw [map_add, map_mul, Polynomial.aeval_X, Polynomial.aeval_C]
  have huR : uR ∈ P.comap (algebraMap ↥R₀ B) := by
    change algebraMap ↥R₀ B uR ∈ P
    first | exact huP | (convert huP using 1 <;> rfl)
  have hϖR : algebraMap A ↥R₀ ϖ ∈ P.comap (algebraMap ↥R₀ B) := by
    change algebraMap ↥R₀ B (algebraMap A ↥R₀ ϖ) ∈ P
    first | exact hϖP | (convert hϖP using 1 <;> first | rfl | exact (IsScalarTower.algebraMap_apply A ↥R₀ B ϖ).symm)
  by_cases hcunit : IsUnit (q.coeff 0)
  · obtain ⟨w, hw⟩ := hcunit
    have h1 : (1 : ↥R₀) = algebraMap A ↥R₀ ((w⁻¹ : Aˣ) : A) * (x - uR * r) := by
      rw [hxeq, add_sub_cancel_left, ← map_mul, ← hw, Units.inv_mul, map_one]
    rw [h1]
    exact Ideal.mul_mem_left _ _ (Ideal.sub_mem _ hxJ (hIJ (Ideal.mul_mem_right _ _ huR)))
  · exfalso
    apply hxI
    have hcm : q.coeff 0 ∈ Ideal.span {ϖ} := hmax ▸ (show q.coeff 0 ∈ IsLocalRing.maximalIdeal A from hcunit)
    obtain ⟨e, he⟩ := Ideal.mem_span_singleton'.mp hcm
    rw [hxeq, ← he, map_mul]
    exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ huR) (Ideal.mul_mem_left _ _ hϖR)

theorem ϖ_not_mem_of_mem_minimalPrimes (ϖ : A) (hϖ : Irreducible ϖ)
    (𝔮 : Ideal B) [𝔮.IsPrime] (h𝔮𝔫 : 𝔮 ≤ 𝔫) (hu𝔮 : uB ∈ 𝔮) (hϖ𝔮 : algebraMap A B ϖ ∉ 𝔮)
    (P : Ideal B) (hP : P ∈ (Ideal.span {uB}).minimalPrimes) (hP𝔫 : P ≤ 𝔫) :
    algebraMap A B ϖ ∉ P := by
  intro hϖP
  haveI : P.IsPrime := hP.1.1
  have huP : uB ∈ P := hP.1.2 (Ideal.subset_span rfl)
  have hPmax := isMaximal_of_mem_of_mem M L A j ϖ hϖ P hϖP huP
  have hP𝔫eq : P = 𝔫 := hPmax.eq_of_le (Ideal.IsPrime.ne_top ‹_›) hP𝔫

  have h𝔫le𝔮 : 𝔫 ≤ 𝔮 := by
    have := hP.2 ⟨‹𝔮.IsPrime›, (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hu𝔮))⟩ (hP𝔫eq ▸ h𝔮𝔫)
    rwa [hP𝔫eq] at this
  exact hϖ𝔮 (h𝔫le𝔮 (hP𝔫eq ▸ hϖP))

theorem main (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hj : ((j : ↥KL) : Λ) = coeffEmb L jq)
    (h𝔫 : NCond M L A j 𝔫) (ϖ : A) (hϖ : Irreducible ϖ)
    (Bm : Type) [CommRing Bm] [Algebra B Bm] [IsLocalization.AtPrime Bm 𝔫] :
    IsRegularLocalRing Bm ∧ ringKrullDim Bm = 2 ∧
      𝔫.map (algebraMap B Bm) = Ideal.span {algebraMap B Bm (algebraMap A B ϖ), algebraMap B Bm uB} := by

  have hj' : ∀ n : ℤ, n ≤ 0 → ((j : ↥KL) : Λ)⁻¹.coeff n = 0 := by
    intro n hn; rw [hj, ← map_inv₀, coeffEmb_coeff, jq_inv_coeff_of_le_zero hn, map_zero]
  obtain ⟨ι, χ, hιcoe, hχ, hιC, hιu⟩ :=
    TwoChartIntegralModel.exists_ringHom_powerSeries_chartAlgInf_coe_eq_and_algebraMap_eq_coeff_zero L A
      (laurentBaseChange L (modularFunctionFieldFull M)) j hj'

  haveI : IsIntegrallyClosed B := TwoChartIntegralModel.isIntegrallyClosed_chartAlg A ↥KL _
  haveI : IsNoetherianRing B := by
    have hjeq : j = ⟨coeffEmb L jq, coeffEmb_mem_laurentBaseChange L (jq_mem_full M)⟩ := Subtype.ext hj
    have htL : Transcendental L j := hjeq ▸ transcendental_coeffEmb_jq L M
    have htA : Transcendental A j := htL.restrictScalars (IsFractionRing.injective A L)
    haveI hFD : FiniteDimensional ↥(IntermediateField.adjoin L ({j} : Set ↥KL)) ↥KL := by
      rw [hjeq]; exact finiteDimensional_adjoin_coeffEmb_jq_full L M
    have hsep : Algebra.IsSeparable ↥(IntermediateField.adjoin L ({j} : Set ↥KL)) ↥KL := inferInstance
    haveI := (TwoChartIntegralModel.finiteType_chartAlgFin_and_chartAlgInf A L ↥KL j htA hFD hsep).2
    exact Algebra.FiniteType.isNoetherianRing A B

  have hcoeff : ∀ b : B, ((b : ↥KL) : Λ).coeff 0 = algebraMap A L (χ b) := fun b => by
    rw [← hιcoe b, coeff_zero_coe_powerSeries, hχ]
  have h𝔫' : ∀ b : B, b ∈ 𝔫 ↔ χ b ∈ IsLocalRing.maximalIdeal A := fun b => by
    rw [h𝔫 b, hcoeff]
    exact ⟨fun ⟨c, hc, h⟩ => (algebraMap_injective L A h) ▸ hc, fun h => ⟨_, h, rfl⟩⟩
  have hu : ∃ w : PowerSeries L, IsUnit w ∧ ι uB = PowerSeries.X * w := by
    refine ⟨_, ?_, hιu⟩
    rw [PowerSeries.isUnit_iff_constantCoeff, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      PowerSeries.coeff_mk, hj, ← map_inv₀, coeffEmb_coeff, show ((0 : ℕ) : ℤ) + 1 = 1 by norm_num,
      jq_inv_coeff_one, map_one]
    exact isUnit_one

  haveI : (RingHom.ker χ).IsPrime := RingHom.ker_isPrime χ
  have hχA : ∀ a : A, χ (algebraMap A B a) = a := fun a => algebraMap_injective L A (by
    rw [hχ, hιC, PowerSeries.constantCoeff_C])
  have h𝔮𝔫 : RingHom.ker χ ≤ 𝔫 := fun b hb => by
    rw [h𝔫']; rw [RingHom.mem_ker] at hb; rw [hb]; exact Ideal.zero_mem _
  have hu𝔮 : uB ∈ RingHom.ker χ := by
    rw [RingHom.mem_ker]; apply algebraMap_injective L A
    rw [hχ, hιu, map_zero]; simp
  have hϖ𝔮 : algebraMap A B ϖ ∉ RingHom.ker χ := by
    rw [RingHom.mem_ker, hχA]; exact hϖ.ne_zero

  have hmin : ∀ P ∈ (Ideal.span {uB}).minimalPrimes, P ≤ 𝔫 → P = RingHom.ker χ := by
    intro P hP hP𝔫
    haveI : P.IsPrime := hP.1.1
    have huP : uB ∈ P := hP.1.2 (Ideal.subset_span rfl)
    have hϖP := ϖ_not_mem_of_mem_minimalPrimes M L A j ϖ hϖ (RingHom.ker χ) h𝔮𝔫 hu𝔮 hϖ𝔮 P hP hP𝔫
    exact eq_of_le_of_mem_of_not_mem M p L A j hAp hj h𝔫 ϖ hϖ P (RingHom.ker χ) hP𝔫 h𝔮𝔫 huP hu𝔮 hϖP hϖ𝔮
  exact IsIntegrallyClosed.isRegularLocalRing_of_isLocalization_atPrime_of_ringHom_powerSeries_of_forall_minimalPrimes_le
    ι χ hχ hιC uB hu 𝔫 h𝔫' hmin ϖ hϖ Bm

end Main

end CuspBC
p2m_reactivate "P2MW.S_ModularCurve_isRegularLocalRing_of_isLocalization_atPrime_chartAlgInf_laurentBaseChange_cuspInfty.CuspBC"

open CuspBC in
theorem solution
    (M p : ℕ) [NeZero M] [Fact p.Prime]
    (L : Type) [Field L] [CharZero L]
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.modularFunctionFieldFull M))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (𝔫 : Ideal ↥(TwoChartIntegralModel.chartAlgInf A (↥K) j)) [𝔫.IsPrime]
    (h𝔫 : ∀ b : ↥(TwoChartIntegralModel.chartAlgInf A (↥K) j), b ∈ 𝔫 ↔
      ∃ c ∈ IsLocalRing.maximalIdeal A, ((b : ↥K) : LaurentSeries L).coeff 0 = algebraMap A L c)
    (ϖ : A) (hϖ : Irreducible ϖ)
    (Bm : Type) [CommRing Bm] [Algebra ↥(TwoChartIntegralModel.chartAlgInf A (↥K) j) Bm]
    [IsLocalization.AtPrime Bm 𝔫] :
    IsRegularLocalRing Bm ∧ ringKrullDim Bm = 2 ∧
      𝔫.map (algebraMap ↥(TwoChartIntegralModel.chartAlgInf A (↥K) j) Bm) =
        Ideal.span {algebraMap ↥(TwoChartIntegralModel.chartAlgInf A (↥K) j) Bm
            (algebraMap A ↥(TwoChartIntegralModel.chartAlgInf A (↥K) j) ϖ),
          algebraMap ↥(TwoChartIntegralModel.chartAlgInf A (↥K) j) Bm
            (TwoChartIntegralModel.jInvChartInf A (↥K) j)} := by
  subst hK
  exact CuspBC.main M p L A j hAp hj h𝔫 ϖ hϖ Bm

end
end S_ModularCurve_isRegularLocalRing_of_isLocalization_atPrime_chartAlgInf_laurentBaseChange_cuspInfty
end P2MW
export P2MW.S_ModularCurve_isRegularLocalRing_of_isLocalization_atPrime_chartAlgInf_laurentBaseChange_cuspInfty (solution)
