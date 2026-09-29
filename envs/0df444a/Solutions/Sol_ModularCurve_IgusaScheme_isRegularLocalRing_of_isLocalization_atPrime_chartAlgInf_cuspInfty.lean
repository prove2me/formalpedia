-- Prove2me | solution 1 for ModularCurve.IgusaScheme.isRegularLocalRing_of_isLocalization_atPrime_chartAlgInf_cuspInfty
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/aa9d1f69-ab39-5360-a996-7ac9af09bcaf

import Mathlib
import Definitions.Def_ModularCurve_IgusaScheme
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_AtkinLehnerPartial
import Theorems.Thm_ModularCurve_IgusaScheme_finiteType_chartAlgFin_and_chartAlgInf
import Theorems.Thm_GaloisRep_isDiscreteValuationRing_ratLocalizedAt
import Theorems.Thm_ModularCurve_IgusaScheme_exists_mul_eq_natCast_mul_add_jInvChartInf_mul_of_coeff_zero_mem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_IgusaScheme_isRegularLocalRing_of_isLocalization_atPrime_chartAlgInf_cuspInfty
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "ModularCurve.qExpandAlgHomC_apply ModularCurve.jqNModC_one AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero"
p2m_attr_erase "simp" "ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd"
p2m_attr_erase "simp" "AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord"

set_option linter.unusedSectionVars false
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

noncomputable section

open scoped Classical
open Polynomial ModularCurve ModularCurve.IgusaScheme WithZero

namespace CuspInftyRegular

local notation "Λ" => LaurentSeries ℚ

def 𝒪 : Subring Λ := (Valued.v : Valuation Λ ℤᵐ⁰).integer

theorem mem_𝒪_iff (f : Λ) : f ∈ 𝒪 ↔ ∀ n : ℤ, n < 0 → f.coeff n = 0 := by
  rw [𝒪, Valuation.mem_integer_iff]
  have h := LaurentSeries.valuation_le_iff_coeff_lt_eq_zero (K := ℚ) (D := 0) (f := f)
  simpa using h

theorem exists_powerSeries_of_mem_𝒪 {f : Λ} (hf : f ∈ 𝒪) : ∃ F : PowerSeries ℚ, (F : Λ) = f :=
  (LaurentSeries.val_le_one_iff_eq_coe (K := ℚ) f).mp hf

theorem coeff_zero_coe_powerSeries (F : PowerSeries ℚ) :
    (F : Λ).coeff 0 = PowerSeries.constantCoeff F := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, LaurentSeries.coeff_coe_powerSeries]

def ρ : ↥𝒪 →+* ℚ where
  toFun f := (f : Λ).coeff 0
  map_one' := by simp
  map_mul' f g := by
    obtain ⟨F, hF⟩ := exists_powerSeries_of_mem_𝒪 f.2
    obtain ⟨G, hG⟩ := exists_powerSeries_of_mem_𝒪 g.2
    change ((f : Λ) * (g : Λ)).coeff 0 = (f : Λ).coeff 0 * (g : Λ).coeff 0
    rw [← hF, ← hG, ← map_mul]
    change ((F * G : PowerSeries ℚ) : Λ).coeff 0 = (F : Λ).coeff 0 * (G : Λ).coeff 0
    rw [coeff_zero_coe_powerSeries, coeff_zero_coe_powerSeries, coeff_zero_coe_powerSeries, map_mul]
  map_zero' := by simp
  map_add' f g := by simp

theorem single_mul_jq : HahnSeries.single (1 : ℤ) (1 : ℚ) * jq = ((jNumQ : PowerSeries ℚ) : Λ) := by
  rw [jq, ← mul_assoc, HahnSeries.single_mul_single, one_mul,
    show (1 : ℤ) + -1 = 0 by norm_num, HahnSeries.single_zero_one, one_mul]

theorem jq_inv_eq : (jq⁻¹ : Λ) = HahnSeries.single (1 : ℤ) (1 : ℚ) * ((jNumQ⁻¹ : PowerSeries ℚ) : Λ) := by
  have hc : PowerSeries.constantCoeff jNumQ ≠ 0 := by rw [constantCoeff_jNumQ]; exact one_ne_zero
  have h0 : HahnSeries.single (1 : ℤ) (1 : ℚ) * jq ≠ 0 := by
    rw [single_mul_jq]; intro h
    have h1 : ((jNumQ : PowerSeries ℚ) : Λ).coeff 0 = (0 : Λ).coeff 0 := by rw [h]
    rw [coeff_zero_coe_powerSeries, constantCoeff_jNumQ, HahnSeries.coeff_zero] at h1
    exact one_ne_zero h1
  have hinv : (HahnSeries.single (1 : ℤ) (1 : ℚ) * jq)⁻¹ = ((jNumQ⁻¹ : PowerSeries ℚ) : Λ) := by
    apply mul_left_cancel₀ h0
    rw [mul_inv_cancel₀ h0, single_mul_jq, ← map_mul, PowerSeries.mul_inv_cancel _ hc, map_one]
  have h𝔮0 : (HahnSeries.single (1 : ℤ) (1 : ℚ) : Λ) ≠ 0 := HahnSeries.single_ne_zero one_ne_zero
  rw [← hinv, mul_inv, ← mul_assoc, mul_inv_cancel₀ h𝔮0, one_mul]

theorem jq_inv_coeff_zero : (jq⁻¹ : Λ).coeff 0 = 0 := by
  rw [jq_inv_eq, HahnSeries.coeff_single_mul, one_mul, show (0 : ℤ) - 1 = -1 by norm_num,
    HahnSeries.ofPowerSeries_apply]
  exact HahnSeries.embDomain_notin_range (by rintro ⟨m, hm⟩; simp at hm)

theorem jq_inv_mem_𝒪 : (jq⁻¹ : Λ) ∈ 𝒪 := by
  rw [jq_inv_eq, mem_𝒪_iff]
  intro n hn
  rw [HahnSeries.coeff_single_mul, one_mul]
  have hmem : ((jNumQ⁻¹ : PowerSeries ℚ) : Λ) ∈ 𝒪 :=
    (LaurentSeries.val_le_one_iff_eq_coe (K := ℚ) _).mpr ⟨_, rfl⟩
  exact (mem_𝒪_iff _).mp hmem _ (by omega)

section Chart

variable (M p : ℕ) [NeZero M] [hp : Fact p.Prime]

set_option quotPrecheck false in
local notation "F" => (↥(modularFunctionFieldFull M) : Type)
set_option quotPrecheck false in
local notation "Zp" => (↥(GaloisRep.ratLocalizedAt p) : Type)
set_option quotPrecheck false in
local notation "B" => (↥(chartAlgInf M p) : Type)

theorem coe_mem_𝒪 (b : B) : ((b : F) : Λ) ∈ 𝒪 := by
  have hb : IsIntegral ↥(Algebra.adjoin Zp ({(jFull M)⁻¹} : Set F)) (b : F) := (mem_chartAlg_iff M p).mp b.2
  obtain ⟨Q, hQm, hQ⟩ := hb

  set ι : F →+* Λ := algebraMap F Λ with hι
  have hA : ∀ z ∈ Algebra.adjoin Zp ({(jFull M)⁻¹} : Set F), ι z ∈ 𝒪 := by
    intro z hz
    induction hz using Algebra.adjoin_induction with
    | mem x hx =>
      rw [Set.mem_singleton_iff] at hx; subst hx
      rw [map_inv₀]; exact jq_inv_mem_𝒪
    | algebraMap r =>
      change ((algebraMap ℚ F (r : ℚ) : F) : Λ) ∈ 𝒪
      rw [show ((algebraMap ℚ F (r : ℚ) : F) : Λ) = algebraMap ℚ Λ (r : ℚ) by
        rw [eq_ratCast (algebraMap ℚ F), SubfieldClass.coe_ratCast, ← eq_ratCast (algebraMap ℚ Λ)],
        ModularCurve.algebraMap_apply_eq_single, mem_𝒪_iff]
      intro n hn
      rw [HahnSeries.coeff_single_of_ne hn.ne]
    | add x y _ _ hx hy => rw [map_add]; exact Subring.add_mem _ hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact Subring.mul_mem _ hx hy
  set κ : ↥(Algebra.adjoin Zp ({(jFull M)⁻¹} : Set F)) →+* ↥𝒪 :=
    { toFun := fun z => ⟨ι z, hA z z.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp)
      map_zero' := Subtype.ext (by simp)
      map_add' := fun a b => Subtype.ext (by simp) } with hκ
  have hroot : eval₂ (algebraMap ↥𝒪 Λ) ((b : F) : Λ) (Q.map κ) = 0 := by
    rw [eval₂_map]
    have hcomp : (algebraMap ↥𝒪 Λ).comp κ = ι.comp (algebraMap _ F) := RingHom.ext fun z => rfl
    rw [hcomp, show ((b : F) : Λ) = ι b from rfl, ← Polynomial.hom_eval₂, hQ, map_zero]
  exact (Valuation.integer.integers (Valued.v : Valuation Λ ℤᵐ⁰)).mem_of_integral ⟨Q.map κ, hQm.map κ, hroot⟩

def evalInfty : B →+* ℚ :=
  ρ.comp
    { toFun := fun b => ⟨((b : F) : Λ), coe_mem_𝒪 M p b⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp)
      map_zero' := Subtype.ext (by simp)
      map_add' := fun a b => Subtype.ext (by simp) }

theorem evalInfty_apply (b : B) : evalInfty M p b = ((b : F) : Λ).coeff 0 := rfl

def 𝔮 : Ideal B := RingHom.ker (evalInfty M p)

scoped instance 𝔮_isPrime : (𝔮 M p).IsPrime := RingHom.ker_isPrime _

theorem mem_𝔮_iff (b : B) : b ∈ 𝔮 M p ↔ ((b : F) : Λ).coeff 0 = 0 := by
  rw [𝔮, RingHom.mem_ker, evalInfty_apply]

theorem jInvChartInf_mem_𝔮 : jInvChartInf M p ∈ 𝔮 M p := by
  rw [mem_𝔮_iff, coe_jInvChartInf, IntermediateField.coe_inv]
  exact jq_inv_coeff_zero

theorem jInvChartInf_ne_zero : jInvChartInf M p ≠ 0 := by
  intro h
  have h1 : ((jInvChartInf M p : B) : F) = ((0 : B) : F) := by rw [h]
  rw [coe_jInvChartInf, ZeroMemClass.coe_zero] at h1
  exact inv_ne_zero (jFull_ne_zero M) h1

theorem coe_natCast_coeff_zero : ((((p : B) : F) : Λ)).coeff 0 = p := by
  rw [SubringClass.coe_natCast, SubringClass.coe_natCast, ← map_natCast (algebraMap ℚ Λ) p,
    ModularCurve.algebraMap_apply_eq_single, HahnSeries.coeff_single_same]

end Chart

section Main

variable (M p : ℕ) [NeZero M] [hp : Fact p.Prime]

set_option quotPrecheck false in
local notation "F" => (↥(modularFunctionFieldFull M) : Type)
set_option quotPrecheck false in
local notation "Zp" => (↥(GaloisRep.ratLocalizedAt p) : Type)
set_option quotPrecheck false in
local notation "B" => (↥(chartAlgInf M p) : Type)

scoped instance : IsDiscreteValuationRing Zp := GaloisRep.isDiscreteValuationRing_ratLocalizedAt p hp.out

scoped instance isNoetherianRing_chartAlgInf : IsNoetherianRing B :=
  @Algebra.FiniteType.isNoetherianRing Zp B _ _ _ (finiteType_chartAlgFin_and_chartAlgInf M p).2 inferInstance

theorem main (𝔪 : Ideal B) [𝔪.IsPrime]
    (h𝔪 : ∀ b : B, b ∈ 𝔪 ↔ ∃ c ∈ GaloisRep.ratLocalizedAt p, ((b : F) : Λ).coeff 0 = (p : ℚ) * c)
    (Bm : Type) [CommRing Bm] [Algebra B Bm] [IsLocalization.AtPrime Bm 𝔪] :
    IsRegularLocalRing Bm ∧ ringKrullDim Bm = 2 ∧
      𝔪.map (algebraMap B Bm) = Ideal.span {algebraMap B Bm (p : B), algebraMap B Bm (jInvChartInf M p)} := by
  haveI : IsLocalRing Bm := IsLocalization.AtPrime.isLocalRing Bm 𝔪
  haveI : IsNoetherianRing Bm := IsLocalization.isNoetherianRing 𝔪.primeCompl Bm inferInstance
  have hmax : IsLocalRing.maximalIdeal Bm = 𝔪.map (algebraMap B Bm) :=
    (IsLocalization.AtPrime.map_eq_maximalIdeal 𝔪 Bm).symm

  have hp𝔪 : (p : B) ∈ 𝔪 := (h𝔪 _).mpr ⟨1, Subring.one_mem _, by rw [coe_natCast_coeff_zero, mul_one]⟩
  have hu𝔪 : jInvChartInf M p ∈ 𝔪 := (h𝔪 _).mpr ⟨0, Subring.zero_mem _, by
    rw [mul_zero, coe_jInvChartInf, IntermediateField.coe_inv]; exact jq_inv_coeff_zero⟩
  have hgen : 𝔪.map (algebraMap B Bm)
      = Ideal.span {algebraMap B Bm (p : B), algebraMap B Bm (jInvChartInf M p)} := by
    apply le_antisymm
    · rw [Ideal.map_le_iff_le_comap]
      intro b hb
      obtain ⟨s, c, d, hs, hrel⟩ :=
        exists_mul_eq_natCast_mul_add_jInvChartInf_mul_of_coeff_zero_mem M p b ((h𝔪 b).mp hb)
      have hs' : s ∈ 𝔪.primeCompl := fun h => hs ((h𝔪 s).mp h)
      have hunit : IsUnit (algebraMap B Bm s) := IsLocalization.map_units Bm ⟨s, hs'⟩
      rw [Ideal.mem_comap]
      have hb' : algebraMap B Bm b = ↑(hunit.unit⁻¹) * (algebraMap B Bm (p : B) * algebraMap B Bm c
          + algebraMap B Bm (jInvChartInf M p) * algebraMap B Bm d) := by
        rw [← map_mul, ← map_mul, ← map_add, ← hrel, map_mul, ← mul_assoc, IsUnit.val_inv_mul, one_mul]
      rw [hb']
      refine Ideal.mul_mem_left _ _ (Ideal.add_mem _ (Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp)))
        (Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))))
    · rw [Ideal.span_le]
      rintro x (rfl | rfl)
      · exact Ideal.mem_map_of_mem _ hp𝔪
      · exact Ideal.mem_map_of_mem _ hu𝔪

  have hspan : (IsLocalRing.maximalIdeal Bm).spanFinrank ≤ 2 := by
    rw [hmax, hgen]
    refine (Submodule.spanFinrank_span_le_ncard_of_finite (Set.toFinite _)).trans ?_
    exact (Set.ncard_insert_le _ _).trans (by rw [Set.ncard_singleton])

  have h𝔮le : 𝔮 M p ≤ 𝔪 := fun b hb => (h𝔪 b).mpr ⟨0, Subring.zero_mem _, by
    rw [mul_zero]; exact (mem_𝔮_iff M p b).mp hb⟩
  have h𝔮ne_bot : 𝔮 M p ≠ ⊥ := fun h => jInvChartInf_ne_zero M p (by
    have := jInvChartInf_mem_𝔮 M p; rw [h] at this; exact (Submodule.mem_bot _).mp this)
  have h𝔮ne_𝔪 : 𝔮 M p ≠ 𝔪 := fun h => by
    have hp𝔮 : (p : B) ∈ 𝔮 M p := h ▸ hp𝔪
    rw [mem_𝔮_iff, coe_natCast_coeff_zero] at hp𝔮
    exact hp.out.ne_zero (by exact_mod_cast hp𝔮)
  have hdisj : ∀ I : Ideal B, I ≤ 𝔪 → Disjoint (𝔪.primeCompl : Set B) (I : Set B) := by
    intro I hI
    rw [Set.disjoint_left]
    intro x hx hxI
    exact hx (hI hxI)

  let P : ∀ I : Ideal B, I.IsPrime → I ≤ 𝔪 → PrimeSpectrum Bm := fun I hI hle =>
    ⟨I.map (algebraMap B Bm), IsLocalization.isPrime_of_isPrime_disjoint 𝔪.primeCompl Bm I hI (hdisj I hle)⟩
  have hunder : ∀ (I : Ideal B) (hI : I.IsPrime) (hle : I ≤ 𝔪),
      Ideal.comap (algebraMap B Bm) (P I hI hle).asIdeal = I := fun I hI hle =>
    IsLocalization.under_map_of_isPrime_disjoint 𝔪.primeCompl Bm hI (hdisj I hle)
  have hlt : ∀ (I J : Ideal B) (hI : I.IsPrime) (hJ : J.IsPrime) (hIle : I ≤ 𝔪) (hJle : J ≤ 𝔪),
      I ≤ J → I ≠ J → P I hI hIle < P J hJ hJle := by
    intro I J hI hJ hIle hJle hIJ hne
    refine lt_of_le_of_ne ?_ ?_
    · change I.map (algebraMap B Bm) ≤ J.map (algebraMap B Bm)
      exact Ideal.map_mono hIJ
    · intro h
      apply hne
      rw [← hunder I hI hIle, ← hunder J hJ hJle, h]
  haveI : (⊥ : Ideal B).IsPrime := Ideal.isPrime_bot
  set P0 := P ⊥ inferInstance bot_le with hP0
  set P1 := P (𝔮 M p) inferInstance h𝔮le with hP1
  set P2 := P 𝔪 inferInstance le_rfl with hP2
  have h01 : P0 < P1 := hlt ⊥ (𝔮 M p) inferInstance inferInstance bot_le h𝔮le bot_le (Ne.symm h𝔮ne_bot)
  have h12 : P1 < P2 := hlt (𝔮 M p) 𝔪 inferInstance inferInstance h𝔮le le_rfl h𝔮le h𝔮ne_𝔪
  have hdim : (2 : WithBot ℕ∞) ≤ ringKrullDim Bm := by
    let s : LTSeries (PrimeSpectrum Bm) :=
      ((RelSeries.singleton _ P0).snoc P1 h01).snoc P2 (by rw [RelSeries.last_snoc]; exact h12)
    have hs : s.length = 2 := rfl
    have := Order.LTSeries.length_le_krullDim s
    rw [hs] at this
    exact this

  have hreg : IsRegularLocalRing Bm := by
    refine IsRegularLocalRing.of_spanFinrank_maximalIdeal_le Bm (le_trans ?_ hdim)
    exact_mod_cast hspan
  refine ⟨hreg, le_antisymm ?_ hdim, hgen⟩
  refine (ringKrullDim_le_spanFinrank_maximalIdeal Bm).trans ?_
  exact_mod_cast hspan

end Main

end CuspInftyRegular
p2m_reactivate "P2MW.S_ModularCurve_IgusaScheme_isRegularLocalRing_of_isLocalization_atPrime_chartAlgInf_cuspInfty.CuspInftyRegular"

theorem solution
    (M p : ℕ) [NeZero M] [Fact p.Prime]
    (𝔪 : Ideal ↥(chartAlgInf M p)) [𝔪.IsPrime]
    (h𝔪 : ∀ b : ↥(chartAlgInf M p), b ∈ 𝔪 ↔
      ∃ c ∈ GaloisRep.ratLocalizedAt p,
        ((b : ↥(modularFunctionFieldFull M)) : LaurentSeries ℚ).coeff 0 = (p : ℚ) * c)
    (Bm : Type) [CommRing Bm] [Algebra ↥(chartAlgInf M p) Bm] [IsLocalization.AtPrime Bm 𝔪] :
    IsRegularLocalRing Bm ∧ ringKrullDim Bm = 2 ∧
      𝔪.map (algebraMap ↥(chartAlgInf M p) Bm) =
        Ideal.span {algebraMap ↥(chartAlgInf M p) Bm (p : ↥(chartAlgInf M p)),
          algebraMap ↥(chartAlgInf M p) Bm (jInvChartInf M p)} :=
  CuspInftyRegular.main M p 𝔪 h𝔪 Bm

end
end S_ModularCurve_IgusaScheme_isRegularLocalRing_of_isLocalization_atPrime_chartAlgInf_cuspInfty
end P2MW
export P2MW.S_ModularCurve_IgusaScheme_isRegularLocalRing_of_isLocalization_atPrime_chartAlgInf_cuspInfty (solution)
