-- Prove2me | solution 1 for ModularCurve.exists_uniform_window_smul_mem_integers_of_qCoeff_criterion
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/1ad4f3e1-1ec2-58f3-ae9d-d1f3b6f4a20b

import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_ModularCurve_FinitePlaceLift
import Definitions.Def_ModularCurve_JZeroHeightForm
import Theorems.Thm_ModularCurve_exists_finiteDimensional_forall_coeff_mem
import Theorems.Thm_ModularCurve_exists_smul_forall_coeff_mem_and_exists_not_mem_nonunits
import Theorems.Thm_ValuationSubring_exists_algEquiv_smul_eq_of_liesOverPrime
import Theorems.Thm_ValuationSubring_exists_uniform_pow_mul_mem_of_liesOverPrime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_uniform_window_smul_mem_integers_of_qCoeff_criterion
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois"
p2m_attr_erase "simp" "ModularCurve.PlaceSpecialization.mk.injEq ModularCurve.PlaceSpecialization.mk.sizeOf_spec ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero"
p2m_attr_erase "simp" "ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_cuspidalDivisor₀ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul"

set_option autoImplicit false
set_option Elab.async false

open AlgebraicCurve ModularCurve

namespace WindowDev

open IsLocalRing Polynomial

local notation "𝕂" => AlgebraicClosure ℚ

theorem inv_mem_of_isUnit_coe {K : Type*} [Field K] {A : ValuationSubring K} {x : A}
    (hx : IsUnit x) : ((x : K))⁻¹ ∈ A := by
  obtain ⟨u, hu⟩ := hx
  have h : ((x : A) : K) * (((u⁻¹ : Aˣ) : A) : K) = 1 := by
    have h0 : (u : A) * ((u⁻¹ : Aˣ) : A) = 1 := u.mul_inv
    rw [hu] at h0
    exact_mod_cast congrArg (fun z : A => (z : K)) h0
  rw [inv_eq_of_mul_eq_one_right h]
  exact Subtype.mem _

theorem inv_natCast_mem_of_not_dvd {A : ValuationSubring 𝕂} {p : ℕ} (hp : p.Prime)
    (hA : (p : 𝕂) ∈ A.nonunits) {m : ℕ} (hm : ¬ p ∣ m) : ((m : 𝕂))⁻¹ ∈ A := by
  obtain ⟨a, b, hab⟩ :=
    Nat.isCoprime_iff_coprime.mpr ((Nat.Prime.coprime_iff_not_dvd hp).mpr hm)
  have habK : (a : 𝕂) * p + b * m = 1 := by
    have h := congrArg (fun z : ℤ => (z : 𝕂)) hab
    push_cast at h
    exact h
  let P : A := ⟨(p : 𝕂), natCast_mem A p⟩
  let M : A := ⟨(m : 𝕂), natCast_mem A m⟩
  have hP : P ∈ maximalIdeal A := ValuationSubring.coe_mem_nonunits_iff.mp hA
  have hMu : IsUnit M := by
    by_contra hMu
    have hMm : M ∈ maximalIdeal A := (mem_maximalIdeal M).mpr (mem_nonunits_iff.mpr hMu)
    have hsum : (⟨(a : 𝕂), intCast_mem A a⟩ : A) * P + (⟨(b : 𝕂), intCast_mem A b⟩ : A) * M ∈
        maximalIdeal A :=
      Ideal.add_mem _ (Ideal.mul_mem_left _ _ hP) (Ideal.mul_mem_left _ _ hMm)
    have h1 : (⟨(a : 𝕂), intCast_mem A a⟩ : A) * P + (⟨(b : 𝕂), intCast_mem A b⟩ : A) * M = 1 := by
      apply Subtype.ext
      push_cast
      exact habK
    rw [h1] at hsum
    exact (maximalIdeal.isMaximal A).ne_top ((Ideal.eq_top_iff_one _).mpr hsum)
  exact inv_mem_of_isUnit_coe hMu

theorem aeval_int_mem (A : ValuationSubring 𝕂) {c : 𝕂} (hc : c ∈ A) (q : ℤ[X]) :
    aeval c q ∈ A := by
  refine Polynomial.induction_on' q ?_ ?_
  · intro f g hf hg
    rw [map_add]
    exact add_mem hf hg
  · intro n a
    rw [aeval_monomial, eq_intCast]
    exact mul_mem (intCast_mem A a) (pow_mem hc n)

theorem exists_intCast_mul_inv_mem {A : ValuationSubring 𝕂} {c : 𝕂} (hc : c ∈ A) (hc0 : c ≠ 0) :
    ∃ b : ℤ, b ≠ 0 ∧ (b : 𝕂) * c⁻¹ ∈ A := by
  have halg : IsAlgebraic ℤ c :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ 𝕂).mpr ((AlgebraicClosure.isAlgebraic ℚ).isAlgebraic c)
  obtain ⟨f, hf0, hfc⟩ := halg
  obtain ⟨g, hfg, hXg⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd f hf0 0
  have hg0 : g.coeff 0 ≠ 0 := by
    intro h
    apply hXg
    rw [map_zero, sub_zero]
    exact X_dvd_iff.mpr h
  have hgc : aeval c g = 0 := by
    have h := hfc
    rw [hfg, map_mul, map_pow, map_sub, aeval_X, aeval_C, map_zero, sub_zero] at h
    exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero _ hc0)
  have key : (g.coeff 0 : 𝕂) * c⁻¹ = -(aeval c g.divX) := by
    have h := congrArg (aeval c) (X_mul_divX_add g)
    rw [map_add, map_mul, aeval_X, aeval_C, hgc, eq_intCast] at h

    field_simp
    linear_combination h
  exact ⟨g.coeff 0, hg0, key ▸ neg_mem (aeval_int_mem A hc g.divX)⟩

theorem exists_window {A : ValuationSubring 𝕂} {p : ℕ} (hp : p.Prime)
    (hA : (p : 𝕂) ∈ A.nonunits) {c : 𝕂} (hc0 : c ≠ 0) :
    ∃ B : ℕ, (p : 𝕂) ^ B * c ∈ A ∧ (p : 𝕂) ^ B * c⁻¹ ∈ A := by

  have step : ∀ {x : 𝕂}, x ∈ A → x ≠ 0 → ∃ B : ℕ, (p : 𝕂) ^ B * x⁻¹ ∈ A := by
    intro x hx hx0
    obtain ⟨b, hb0, hb⟩ := exists_intCast_mul_inv_mem hx hx0
    have hbn0 : b.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hb0
    obtain ⟨B, m, hm, hbm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hbn0 p hp.ne_one
    obtain ⟨u, hu⟩ := Int.dvd_natAbs.mpr (dvd_refl b)

    have hnat : (b.natAbs : 𝕂) * x⁻¹ ∈ A := by
      have : (b.natAbs : 𝕂) * x⁻¹ = (u : 𝕂) * ((b : 𝕂) * x⁻¹) := by
        rw [← Int.cast_natCast, hu]; push_cast; ring
      rw [this]
      exact mul_mem (intCast_mem A u) hb
    have hm0 : (m : 𝕂) ≠ 0 := by
      intro h
      rw [Nat.cast_eq_zero] at h
      rw [h, mul_zero] at hbm
      exact hbn0 hbm
    refine ⟨B, ?_⟩
    have : (p : 𝕂) ^ B * x⁻¹ = ((m : 𝕂))⁻¹ * ((b.natAbs : 𝕂) * x⁻¹) := by
      rw [hbm]; push_cast; field_simp
    rw [this]
    exact mul_mem (inv_natCast_mem_of_not_dvd hp hA hm) hnat
  have hpA : (p : 𝕂) ∈ A := natCast_mem A p
  rcases A.mem_or_inv_mem c with hc | hc
  · obtain ⟨B, hB⟩ := step hc hc0
    exact ⟨B, mul_mem (pow_mem hpA B) hc, hB⟩
  · obtain ⟨B, hB⟩ := step hc (inv_ne_zero hc0)
    rw [inv_inv] at hB
    exact ⟨B, hB, mul_mem (pow_mem hpA B) hc⟩

theorem window_mono {A : ValuationSubring 𝕂} {p : ℕ} {c : 𝕂} {B B' : ℕ} (h : B ≤ B')
    (hB : (p : 𝕂) ^ B * c ∈ A) : (p : 𝕂) ^ B' * c ∈ A := by
  rw [← Nat.sub_add_cancel h, pow_add, mul_assoc]
  exact mul_mem (pow_mem (natCast_mem A p) _) hB

theorem mem_of_isIntegral_int (A : ValuationSubring 𝕂) {y : 𝕂} (hy : IsIntegral ℤ y) : y ∈ A := by
  obtain ⟨f, hfm, hf⟩ := hy
  have hA : IsIntegral A y := by
    refine ⟨f.map (algebraMap ℤ A), hfm.map _, ?_⟩
    rw [eval₂_map, RingHom.ext_int ((algebraMap A 𝕂).comp (algebraMap ℤ A)) (algebraMap ℤ 𝕂)]
    exact hf
  obtain ⟨z, hz⟩ := (IsIntegrallyClosed.isIntegral_iff (R := A) (K := 𝕂)).mp hA
  rw [← hz]
  exact z.2

theorem exists_intCast_mul_inv_eq_aeval {y : 𝕂} (hy0 : y ≠ 0) :
    ∃ b : ℤ, b ≠ 0 ∧ ∃ r : ℤ[X], (b : 𝕂) * y⁻¹ = aeval y r := by
  have halg : IsAlgebraic ℤ y :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ 𝕂).mpr ((AlgebraicClosure.isAlgebraic ℚ).isAlgebraic y)
  obtain ⟨f, hf0, hfc⟩ := halg
  obtain ⟨g, hfg, hXg⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd f hf0 0
  have hg0 : g.coeff 0 ≠ 0 := by
    intro h
    apply hXg
    rw [map_zero, sub_zero]
    exact X_dvd_iff.mpr h
  have hgc : aeval y g = 0 := by
    have h := hfc
    rw [hfg, map_mul, map_pow, map_sub, aeval_X, aeval_C, map_zero, sub_zero] at h
    exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero _ hy0)
  refine ⟨g.coeff 0, hg0, -g.divX, ?_⟩
  have h := congrArg (aeval y) (X_mul_divX_add g)
  rw [map_add, map_mul, aeval_X, aeval_C, hgc, eq_intCast] at h
  rw [map_neg]
  field_simp
  linear_combination h

theorem exists_pow_mul_intCast_inv_mem {p : ℕ} (hp : p.Prime) {n : ℤ} (hn : n ≠ 0) :
    ∃ i : ℕ, ∀ A : ValuationSubring 𝕂, (p : 𝕂) ∈ A.nonunits → (p : 𝕂) ^ i * ((n : 𝕂))⁻¹ ∈ A := by
  have hn0 : n.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hn
  obtain ⟨i, m, hm, hnm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn0 p hp.ne_one
  obtain ⟨u, hu⟩ := Int.dvd_natAbs.mpr (dvd_refl n)
  refine ⟨i, fun A hA => ?_⟩
  have hm0 : (m : 𝕂) ≠ 0 := by
    intro h
    rw [Nat.cast_eq_zero] at h
    rw [h, mul_zero] at hnm
    exact hn0 hnm
  have hnK : (n : 𝕂) ≠ 0 := Int.cast_ne_zero.mpr hn
  have hcast : (n : 𝕂) * (u : 𝕂) = (p : 𝕂) ^ i * (m : 𝕂) := by
    have h1 : ((n.natAbs : ℤ) : 𝕂) = (n : 𝕂) * (u : 𝕂) := by rw [hu, Int.cast_mul]
    rw [Int.cast_natCast, hnm, Nat.cast_mul, Nat.cast_pow] at h1
    exact h1.symm
  have : (p : 𝕂) ^ i * ((n : 𝕂))⁻¹ = (u : 𝕂) * ((m : 𝕂))⁻¹ := by
    rw [← div_eq_mul_inv, ← div_eq_mul_inv, div_eq_div_iff hnK hm0]
    linear_combination -hcast
  rw [this]
  exact mul_mem (intCast_mem A u) (inv_natCast_mem_of_not_dvd hp hA hm)

theorem exists_uniform_window {p : ℕ} (hp : p.Prime) {x : 𝕂} (hx : x ≠ 0) :
    ∃ B : ℕ, ∀ A : ValuationSubring 𝕂, (p : 𝕂) ∈ A.nonunits →
      (p : 𝕂) ^ B * x ∈ A ∧ (p : 𝕂) ^ B * x⁻¹ ∈ A := by
  have halg : IsAlgebraic ℤ x :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ 𝕂).mpr ((AlgebraicClosure.isAlgebraic ℚ).isAlgebraic x)
  obtain ⟨d, hd0, hdx⟩ := halg.exists_integral_multiple
  rw [Algebra.smul_def, eq_intCast] at hdx
  set y : 𝕂 := (d : 𝕂) * x with hy
  have hdK : (d : 𝕂) ≠ 0 := Int.cast_ne_zero.mpr hd0
  have hy0 : y ≠ 0 := mul_ne_zero hdK hx
  obtain ⟨b, hb0, r, hbr⟩ := exists_intCast_mul_inv_eq_aeval hy0
  obtain ⟨i, hi⟩ := exists_pow_mul_intCast_inv_mem hp hd0
  obtain ⟨j, hj⟩ := exists_pow_mul_intCast_inv_mem hp hb0
  refine ⟨i + j, fun A hA => ?_⟩
  have hyA : y ∈ A := mem_of_isIntegral_int A hdx
  have hbyA : (b : 𝕂) * y⁻¹ ∈ A := by rw [hbr]; exact aeval_int_mem A hyA r
  have hpA : (p : 𝕂) ∈ A := natCast_mem A p
  have hbK : (b : 𝕂) ≠ 0 := Int.cast_ne_zero.mpr hb0
  have hdd : ((d : 𝕂))⁻¹ * (d : 𝕂) = 1 := inv_mul_cancel₀ hdK
  have hbb : ((b : 𝕂))⁻¹ * (b : 𝕂) = 1 := inv_mul_cancel₀ hbK
  have hxinv : x⁻¹ = (d : 𝕂) * y⁻¹ := by
    rw [hy, mul_inv, ← mul_assoc, mul_inv_cancel₀ hdK, one_mul]
  constructor
  · have : (p : 𝕂) ^ (i + j) * x = (p : 𝕂) ^ j * (((p : 𝕂) ^ i * ((d : 𝕂))⁻¹) * y) := by
      rw [hy]
      linear_combination (-((p : 𝕂) ^ (i + j) * x)) * hdd
    rw [this]
    exact mul_mem (pow_mem hpA j) (mul_mem (hi A hA) hyA)
  · have : (p : 𝕂) ^ (i + j) * x⁻¹
        = (p : 𝕂) ^ i * ((d : 𝕂) * (((p : 𝕂) ^ j * ((b : 𝕂))⁻¹) * ((b : 𝕂) * y⁻¹))) := by
      rw [hxinv]
      linear_combination (-((p : 𝕂) ^ (i + j) * (d : 𝕂) * y⁻¹)) * hbb
    rw [this]
    exact mul_mem (pow_mem hpA i) (mul_mem (intCast_mem A d) (mul_mem (hj A hA) hbyA))

end WindowDev

namespace WindowDev

open IsLocalRing Polynomial
open scoped Pointwise

local notation "𝕂" => AlgebraicClosure ℚ

theorem inv_mem_of_not_mem_nonunits {K : Type*} [Field K] (A : ValuationSubring K) {y : K}
    (hy : y ∉ A.nonunits) : y⁻¹ ∈ A := by
  by_contra h
  exact hy (A.inv_mem_nonunits_iff.mpr (Or.inr h) |> fun h' => by simpa using h')

theorem one_not_mem_nonunits {K : Type*} [Field K] (A : ValuationSubring K) :
    (1 : K) ∉ A.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff, map_one]
  exact lt_irrefl 1

theorem algebraMap_laurentSeries_eq_single' (L : Type*) [Field L] (c : L) :
    algebraMap L (LaurentSeries L) c = HahnSeries.single 0 c := by
  have h1 : algebraMap L (PowerSeries L) c = PowerSeries.C c := by
    simp
  rw [HahnSeries.algebraMap_apply', h1, HahnSeries.ofPowerSeries_C]
  rfl

theorem mem_iff_smul_mem_smul (g : 𝕂 ≃ₐ[ℚ] 𝕂) (A : ValuationSubring 𝕂) (x : 𝕂) :
    x ∈ A ↔ g • x ∈ g • A := by
  rw [ValuationSubring.mem_smul_pointwise_iff_exists]
  constructor
  · exact fun h => ⟨x, h, rfl⟩
  · rintro ⟨s, hs, hsx⟩
    have : s = x := smul_left_cancel g hsx
    exact this ▸ hs

theorem abstract_face
    (F : IntermediateField 𝕂 (LaurentSeries 𝕂)) (V : Submodule 𝕂 F)
    {r : ℕ} (s : Fin r → F) (hsV : ∀ l, s l ∈ V) (hs0 : ∀ l, s l ≠ 0)
    {p : ℕ} (hp : p.Prime)
    (hQ1a : ∀ f : F, ∃ K : IntermediateField ℚ 𝕂, FiniteDimensional ℚ K ∧
      ∀ k : ℤ, (f : LaurentSeries 𝕂).coeff k ∈ K)
    (hQ1b : ∀ f : F, f ∈ V → f ≠ 0 → ∀ A : ValuationSubring 𝕂, (p : 𝕂) ∈ A.nonunits →
      ∃ c : 𝕂, c ≠ 0 ∧ (∀ k : ℤ, ((c • f : F) : LaurentSeries 𝕂).coeff k ∈ A) ∧
        ∃ k : ℤ, ((c • f : F) : LaurentSeries 𝕂).coeff k ∉ A.nonunits)
    (hT : ∀ A A₀ : ValuationSubring 𝕂, (p : 𝕂) ∈ A.nonunits → (p : 𝕂) ∈ A₀.nonunits →
      ∃ g : 𝕂 ≃ₐ[ℚ] 𝕂, g • A = A₀)
    (hW : ∀ x : 𝕂, x ≠ 0 → ∃ B : ℕ, ∀ A : ValuationSubring 𝕂, (p : 𝕂) ∈ A.nonunits →
      (p : 𝕂) ^ B * x ∈ A ∧ (p : 𝕂) ^ B * x⁻¹ ∈ A) :
    ∃ B : ℕ, ∀ A : ValuationSubring 𝕂, (p : 𝕂) ∈ A.nonunits →
    ∀ (Fbar : Type) [Field Fbar] (O : ValuationSubring F) (res : O →+* Fbar),
      (∀ f : F, f ∈ V → (∀ k : ℤ, (f : LaurentSeries 𝕂).coeff k ∈ A) →
        (∃ k : ℤ, (f : LaurentSeries 𝕂).coeff k ∉ A.nonunits) → ∃ h : f ∈ O, res ⟨f, h⟩ ≠ 0) →
    ∀ l : Fin r, ∃ c : 𝕂, c ≠ 0 ∧ (p : 𝕂) ^ B * c ∈ A ∧ (p : 𝕂) ^ B * c⁻¹ ∈ A ∧
      ∃ h : c • s l ∈ O, res ⟨c • s l, h⟩ ≠ 0 := by
  classical

  have hcoeff : ∀ (c : 𝕂) (f : F) (k : ℤ),
      ((c • f : F) : LaurentSeries 𝕂).coeff k = c * (f : LaurentSeries 𝕂).coeff k := by
    intro c f k
    rw [IntermediateField.coe_smul, Algebra.smul_def, algebraMap_laurentSeries_eq_single',
      HahnSeries.coeff_single_zero_mul]

  suffices hone : ∀ l : Fin r, ∃ B : ℕ, ∀ A : ValuationSubring 𝕂, (p : 𝕂) ∈ A.nonunits →
      ∀ (Fbar : Type) [Field Fbar] (O : ValuationSubring F) (res : O →+* Fbar),
        (∀ f : F, f ∈ V → (∀ k : ℤ, (f : LaurentSeries 𝕂).coeff k ∈ A) →
          (∃ k : ℤ, (f : LaurentSeries 𝕂).coeff k ∉ A.nonunits) → ∃ h : f ∈ O, res ⟨f, h⟩ ≠ 0) →
        ∃ c : 𝕂, c ≠ 0 ∧ (p : 𝕂) ^ B * c ∈ A ∧ (p : 𝕂) ^ B * c⁻¹ ∈ A ∧
          ∃ h : c • s l ∈ O, res ⟨c • s l, h⟩ ≠ 0 by
    choose Bf hBf using hone
    refine ⟨Finset.univ.sup Bf, fun A hA Fbar _ O res hcrit l => ?_⟩
    obtain ⟨c, hc0, h1, h2, h, hres⟩ := hBf l A hA Fbar O res hcrit
    have hle : Bf l ≤ Finset.univ.sup Bf := Finset.le_sup (Finset.mem_univ l)
    exact ⟨c, hc0, window_mono hle h1, window_mono hle h2, h, hres⟩
  intro l
  set f : F := s l with hf
  obtain ⟨K, hKfd, haK⟩ := hQ1a f
  haveI := hKfd
  set a : ℤ → 𝕂 := fun k => (f : LaurentSeries 𝕂).coeff k with ha
  by_cases hex : ∃ A₀ : ValuationSubring 𝕂, (p : 𝕂) ∈ A₀.nonunits
  swap
  · exact ⟨0, fun A hA => (hex ⟨A, hA⟩).elim⟩
  obtain ⟨A₀, hA₀⟩ := hex

  have hg : ∀ A : {A : ValuationSubring 𝕂 // (p : 𝕂) ∈ A.nonunits}, ∃ g : 𝕂 ≃ₐ[ℚ] 𝕂,
      g • A.1 = A₀ := fun A => hT A.1 A₀ A.2 hA₀
  choose g hgA using hg
  let cls : {A : ValuationSubring 𝕂 // (p : 𝕂) ∈ A.nonunits} → (K →ₐ[ℚ] 𝕂) :=
    fun A => (g A).toAlgHom.comp K.val
  have htransport : ∀ A A' : {A : ValuationSubring 𝕂 // (p : 𝕂) ∈ A.nonunits},
      cls A = cls A' → ∀ x : 𝕂, x ∈ K → (x ∈ A.1 ↔ x ∈ A'.1) := by
    intro A A' hAA' x hx
    have h1 : x ∈ A.1 ↔ cls A ⟨x, hx⟩ ∈ A₀ := by
      rw [mem_iff_smul_mem_smul (g A) A.1 x, hgA A]; rfl
    have h2 : x ∈ A'.1 ↔ cls A' ⟨x, hx⟩ ∈ A₀ := by
      rw [mem_iff_smul_mem_smul (g A') A'.1 x, hgA A']; rfl
    rw [h1, h2, hAA']

  let good : (K →ₐ[ℚ] 𝕂) → ℤ → Prop := fun φ k₀ => a k₀ ≠ 0 ∧
    ∃ A : {A : ValuationSubring 𝕂 // (p : 𝕂) ∈ A.nonunits}, cls A = φ ∧ ∀ k, a k * (a k₀)⁻¹ ∈ A.1
  let rep : (K →ₐ[ℚ] 𝕂) → ℤ := fun φ => if h : ∃ k₀, good φ k₀ then h.choose else 0
  have hrep : ∀ φ, (∃ k₀, good φ k₀) → good φ (rep φ) := by
    intro φ h
    simp only [rep, dif_pos h]
    exact h.choose_spec
  let Bof : (K →ₐ[ℚ] 𝕂) → ℕ := fun φ => if h : a (rep φ) ≠ 0 then (hW (a (rep φ)) h).choose else 0
  have hBof : ∀ φ (h : a (rep φ) ≠ 0), ∀ A : ValuationSubring 𝕂, (p : 𝕂) ∈ A.nonunits →
      (p : 𝕂) ^ Bof φ * a (rep φ) ∈ A ∧ (p : 𝕂) ^ Bof φ * (a (rep φ))⁻¹ ∈ A := by
    intro φ h
    simp only [Bof, dif_pos h]
    exact (hW (a (rep φ)) h).choose_spec
  refine ⟨Finset.univ.sup Bof, fun A hA Fbar _ O res hcrit => ?_⟩

  obtain ⟨c', hc'0, hint, k₁, hk₁⟩ := hQ1b f (hsV l) (hs0 l) A hA
  have hint' : ∀ k, c' * a k ∈ A := fun k => by rw [← hcoeff]; exact hint k
  have hk₁' : c' * a k₁ ∉ A.nonunits := by rw [← hcoeff]; exact hk₁
  have hak₁ : a k₁ ≠ 0 := by
    intro h0
    apply hk₁'
    rw [h0, mul_zero, ValuationSubring.mem_nonunits_iff, map_zero]
    exact zero_lt_one
  let Acl : {A : ValuationSubring 𝕂 // (p : 𝕂) ∈ A.nonunits} := ⟨A, hA⟩
  have hgoodA : ∃ k₀, good (cls Acl) k₀ := by
    refine ⟨k₁, hak₁, Acl, rfl, fun k => ?_⟩
    have : a k * (a k₁)⁻¹ = (c' * a k) * (c' * a k₁)⁻¹ := by
      field_simp
    rw [this]
    exact mul_mem (hint' k) (inv_mem_of_not_mem_nonunits A hk₁')
  obtain ⟨hak₀, Astar, hcls, hmem⟩ := hrep (cls Acl) hgoodA
  set k₀ := rep (cls Acl) with hk₀

  have hmemA : ∀ k, a k * (a k₀)⁻¹ ∈ A := by
    intro k
    have hxK : a k * (a k₀)⁻¹ ∈ K := mul_mem (haK k) (inv_mem (haK k₀))
    exact (htransport Astar Acl hcls _ hxK).mp (hmem k)

  refine ⟨(a k₀)⁻¹, inv_ne_zero hak₀, ?_, ?_, ?_⟩
  · have hle : Bof (cls Acl) ≤ Finset.univ.sup Bof := Finset.le_sup (Finset.mem_univ _)
    exact window_mono hle (hBof (cls Acl) hak₀ A hA).2
  · have hle : Bof (cls Acl) ≤ Finset.univ.sup Bof := Finset.le_sup (Finset.mem_univ _)
    rw [inv_inv]
    exact window_mono hle (hBof (cls Acl) hak₀ A hA).1
  · apply hcrit ((a k₀)⁻¹ • f) (V.smul_mem _ (hsV l))
    · intro k
      rw [hcoeff, mul_comm]
      exact hmemA k
    · refine ⟨k₀, ?_⟩
      rw [hcoeff, inv_mul_cancel₀ hak₀]
      exact one_not_mem_nonunits A

end WindowDev

open scoped Pointwise in

theorem solution
    (N : ℕ) [NeZero N] {r : ℕ} (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s)
    (p : ℕ) (hp : p.Prime) :
    ∃ B : ℕ, ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
    ∀ (Fbar : Type) [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
      (C : ComponentChart A (modularFunctionFieldBar N) Fbar),
      (∀ f : modularFunctionFieldBar N, f ∈ riemannRochSpace (embDivisor N) →
        (∀ k : ℤ, (f : LaurentSeries (AlgebraicClosure ℚ)).coeff k ∈ A) →
        (∃ k : ℤ, (f : LaurentSeries (AlgebraicClosure ℚ)).coeff k ∉ A.nonunits) →
        ∃ h : f ∈ C.integers, C.residue ⟨f, h⟩ ≠ 0) →
    ∀ l : Fin r, ∃ c : AlgebraicClosure ℚ, c ≠ 0 ∧ (p : AlgebraicClosure ℚ) ^ B * c ∈ A ∧
      (p : AlgebraicClosure ℚ) ^ B * c⁻¹ ∈ A ∧
      ∃ h : c • s l ∈ C.integers, C.residue ⟨c • s l, h⟩ ≠ 0 := by
  obtain ⟨B, hB⟩ := WindowDev.abstract_face (modularFunctionFieldBar N)
    (riemannRochSpace (embDivisor N)) s
    (fun l => hs.2 ▸ Submodule.subset_span (Set.mem_range_self l))
    (fun l => hs.1.ne_zero l) hp
    (fun f => ModularCurve.exists_finiteDimensional_forall_coeff_mem N f)
    (fun f hf hf0 A hA =>
      ModularCurve.exists_smul_forall_coeff_mem_and_exists_not_mem_nonunits N (embDegree N) f hf hf0
        A hp hA)
    (fun A A₀ hA hA₀ => ValuationSubring.exists_algEquiv_smul_eq_of_liesOverPrime hp A A₀ hA hA₀)
    (fun x hx => ValuationSubring.exists_uniform_pow_mul_mem_of_liesOverPrime hp hx)
  refine ⟨B, fun A hA Fbar _ _ C hcrit l => ?_⟩
  exact hB A hA Fbar C.integers C.residue hcrit l

end S_ModularCurve_exists_uniform_window_smul_mem_integers_of_qCoeff_criterion
end P2MW
export P2MW.S_ModularCurve_exists_uniform_window_smul_mem_integers_of_qCoeff_criterion (solution)
