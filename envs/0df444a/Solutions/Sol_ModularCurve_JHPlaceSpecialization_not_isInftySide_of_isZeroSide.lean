-- Prove2me | solution 1 for ModularCurve.JHPlaceSpecialization.not_isInftySide_of_isZeroSide
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/0debba63-c925-5aa1-ac52-f18904b97871

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Theorems.Thm_ModularCurve_coeff_jqModC_neg_one
import Theorems.Thm_AlgebraicCurve_Place_deg_eq_one_iff_surjective_algebraMap_residueField
import Theorems.Thm_ModularCurve_place_deg_eq_one_laurentBaseChange_qExpFunctionFieldC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JHPlaceSpecialization_not_isInftySide_of_isZeroSide
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ"

set_option autoImplicit false
set_option quotPrecheck false

open AlgebraicCurve IsLocalRing ModularCurve
open scoped MatrixGroups

noncomputable section

namespace E4AV_CuspSides

section hasValue
variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem hasValue_pow {W : Place K F} {g : F} {a : K} (h : W.HasValue g a) (n : ℕ) :
    W.HasValue (g ^ n) (a ^ n) := by
  induction n with
  | zero => simpa using W.hasValue_one
  | succ n ih => rw [pow_succ, pow_succ]; exact ih.mul h

theorem ord_sub_algebraMap_pos_of_hasValue (W : Place K F) (g : F) (c : K) (h : W.HasValue g c)
    (hne : g - algebraMap K F c ≠ 0) : 0 < W.ord (g - algebraMap K F c) := by
  have hm : g - algebraMap K F c ∈ W.toValuationSubring := sub_mem h.mem (W.algebraMap_mem' c)
  have hres : IsLocalRing.residue W.toValuationSubring ⟨_, hm⟩ = 0 := by
    have hsplit : (⟨_, hm⟩ : W.toValuationSubring) = ⟨g, h.mem⟩ - algebraMap K W.toValuationSubring c :=
      Subtype.ext rfl
    rw [hsplit, map_sub, h.residue_eq, Place.residue_algebraMap, sub_self]
  have hnn := W.ord_nonneg_of_mem hm
  rcases hnn.lt_or_eq with hlt | heq
  · exact hlt
  · exfalso
    obtain ⟨hm', hu⟩ := W.exists_isUnit_of_ord_eq_zero hne heq.symm
    have := (IsLocalRing.residue_ne_zero_iff_isUnit _).mpr hu
    exact this hres

end hasValue

section valring
variable {A : ValuationSubring (AlgebraicClosure ℚ)}

theorem inv_mem_nonunits_of_not_mem {e : AlgebraicClosure ℚ} (he : e ∉ A) : e⁻¹ ∈ A.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff]
  have h1 : ¬ A.valuation e ≤ 1 := fun h => he ((A.valuation_le_one_iff e).mp h)
  push Not at h1
  rw [map_inv₀]
  exact inv_lt_one_of_one_lt₀ h1

theorem pow_succ_mem_nonunits {x : AlgebraicClosure ℚ} (hx : x ∈ A.nonunits) (m : ℕ) : x ^ (m + 1) ∈ A.nonunits := by
  induction m with
  | zero => simpa using hx
  | succ m ih => rw [pow_succ]; exact mul_mem ih hx

theorem residue_eq_zero_of_mem_nonunits (τ : ↥A) (h : ((τ : ↥A) : AlgebraicClosure ℚ) ∈ A.nonunits) :
    IsLocalRing.residue ↥A τ = 0 := by
  by_contra hne
  have hu : IsUnit τ := (IsLocalRing.residue_ne_zero_iff_isUnit τ).mp hne
  have h1 : A.valuation (τ : AlgebraicClosure ℚ) = 1 := (A.valuation_eq_one_iff τ).mp hu
  have h2 := (ValuationSubring.mem_nonunits_iff A).mp h
  rw [h1] at h2
  exact lt_irrefl _ h2

end valring

section level
variable (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)

local notation "𝕂" => AlgebraicClosure ℚ
local notation "FM" => ↥(xHFunctionFieldBar M H)

scoped instance gammaH_finiteIndex : (CohCarrier.GammaH M H).FiniteIndex :=
  Subgroup.finiteIndex_of_le (Gamma1_le_GammaH M H)

theorem surjective_algebraMap_residueField (W : Place 𝕂 FM) :
    Function.Surjective (algebraMap 𝕂 W.ResidueField) := by
  rw [← Place.deg_eq_one_iff_surjective_algebraMap_residueField]
  exact place_deg_eq_one_laurentBaseChange_qExpFunctionFieldC 𝕂 (CohCarrier.GammaH M H)
    (translation_mem_GammaH M H) (xHFunctionField M H) rfl W

theorem coe_algebraMap_coeff (e : 𝕂) {n : ℤ} (hn : n ≠ 0) :
    ((algebraMap 𝕂 FM e : FM) : LaurentSeries 𝕂).coeff n = 0 := by
  have h1 : ((algebraMap 𝕂 FM e : FM) : LaurentSeries 𝕂) = algebraMap 𝕂 (LaurentSeries 𝕂) e :=
    (xHFunctionFieldBar M H).val.commutes e
  rw [h1, HahnSeries.algebraMap_apply', show algebraMap 𝕂 (PowerSeries 𝕂) e = PowerSeries.C e from rfl,
    HahnSeries.ofPowerSeries_C, HahnSeries.C_apply, HahnSeries.coeff_single_of_ne hn]

theorem ne_algebraMap_of_coe_eq_jqModC (x : FM) (hx : ((x : FM) : LaurentSeries 𝕂) = jqModC 𝕂) (e : 𝕂) :
    x ≠ algebraMap 𝕂 FM e := by
  intro h
  have h1 := congrArg (fun y : LaurentSeries 𝕂 => y.coeff (-1 : ℤ)) (hx.symm.trans (congrArg Subtype.val h))
  simp only [coeff_jqModC_neg_one] at h1
  rw [coe_algebraMap_coeff M H e (by norm_num)] at h1
  exact one_ne_zero h1

theorem ne_algebraMap_of_coe_eq_qExpand_jqModC (p : ℕ) [NeZero p] (x : FM)
    (hx : ((x : FM) : LaurentSeries 𝕂) = qExpand 𝕂 p (jqModC 𝕂)) (e : 𝕂) :
    x ≠ algebraMap 𝕂 FM e := by
  intro h
  have h1 := congrArg (fun y : LaurentSeries 𝕂 => y.coeff ((p : ℤ) * (-1 : ℤ))) (hx.symm.trans (congrArg Subtype.val h))
  simp only [qExpand_coeff_mul, coeff_jqModC_neg_one] at h1
  have hp : ((p : ℤ) * (-1 : ℤ)) ≠ 0 := by
    have := NeZero.ne p
    simp [this]
  rw [coe_algebraMap_coeff M H e hp] at h1
  exact one_ne_zero h1

end level

section engine
variable (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (A : ValuationSubring (AlgebraicClosure ℚ))

local notation "𝕂" => AlgebraicClosure ℚ
local notation "FM" => ↥(xHFunctionFieldBar M H)

theorem not_isInftySide_of_isZeroSide (W : Place 𝕂 FM)
    (hW : JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A) W) :
    ¬ JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A) W := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  rintro ⟨hc, x₁, x₁', hx₁, hx₁', τ₁, hτ₁, hv₁⟩
  obtain ⟨hc', x, x', hx, hx', τ₀, hτ₀, hv₀⟩ := hW

  have ex : x₁ = x := Subtype.ext (hx₁.trans hx.symm)
  have ex' : x₁' = x' := Subtype.ext (hx₁'.trans hx'.symm)
  subst ex ex'
  have hq2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  obtain ⟨m, hm⟩ : ∃ m : ℕ, p = m + 1 + 1 := ⟨p - 2, by omega⟩
  suffices hnu : (((τ₁ * τ₀ : ↥A)) : 𝕂) ∈ A.nonunits by
    have h0 := residue_eq_zero_of_mem_nonunits (τ₁ * τ₀) hnu
    rw [map_mul, hτ₁, hτ₀, mul_one] at h0
    exact one_ne_zero h0
  have hval0 : ∀ {g : FM} {τ : ↥A}, IsLocalRing.residue ↥A τ = 1 → W.HasValue g (τ : 𝕂) → g ≠ 0 := by
    intro g τ hτ hg h0
    rw [h0] at hg
    have h00 : W.HasValue (0 : FM) 0 := by simpa using W.hasValue_algebraMap 0
    have : (τ : 𝕂) = 0 := hg.unique h00
    have hτ0 : τ = 0 := Subtype.ext this
    rw [hτ0, map_zero] at hτ
    exact zero_ne_one hτ
  have hx0 : x₁ ≠ 0 := by
    intro h0
    apply hval0 hτ₁ hv₁
    rw [h0, zero_pow (by omega), div_zero]
  have hx'0 : x₁' ≠ 0 := by
    intro h0
    apply hval0 hτ₀ hv₀
    rw [h0, zero_pow (by omega), div_zero]
  set u : FM := x₁ * x₁' with hu
  have hu0 : u ≠ 0 := mul_ne_zero hx0 hx'0
  have hprod : x₁' / x₁ ^ p * (x₁ / x₁' ^ p) = u * (u ^ p)⁻¹ := by
    rw [hu, mul_pow, mul_inv, div_eq_mul_inv, div_eq_mul_inv]
    ring
  have hv : W.HasValue (u * (u ^ p)⁻¹) ((τ₁ : 𝕂) * τ₀) := hprod ▸ hv₁.mul hv₀
  have hτne : ((τ₁ : 𝕂) * τ₀) ≠ 0 := by
    intro h0
    have : τ₁ * τ₀ = 0 := Subtype.ext (by push_cast; exact h0)
    have h1 : IsLocalRing.residue ↥A (τ₁ * τ₀) = 1 := by rw [map_mul, hτ₁, hτ₀, mul_one]
    rw [this, map_zero] at h1
    exact zero_ne_one h1
  have hordu : W.ord u = 0 := by
    have h1 := hv.ord_eq_zero hτne
    rw [W.ord_mul hu0 (inv_ne_zero (pow_ne_zero _ hu0)), Place.ord_inv, ← zpow_natCast, Place.ord_zpow] at h1
    have : (1 - (p : ℤ)) * W.ord u = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · omega
    · exact h
  have hordx : W.ord x₁ ≤ 0 := by have h := hc x₁ hx₁ 0; simpa using h
  have hordx' : W.ord x₁' ≤ 0 := by have h := hc' x₁' hx₁' 0; simpa using h
  rw [hu, W.ord_mul hx0 hx'0] at hordu
  have hx_ord : W.ord x₁ = 0 := by omega
  have hx'_ord : W.ord x₁' = 0 := by omega
  have hsurj := surjective_algebraMap_residueField M H W
  obtain ⟨hxm, hxu⟩ := W.exists_isUnit_of_ord_eq_zero hx0 hx_ord
  obtain ⟨e, he, he0⟩ := W.exists_hasValue_of_surjective hsurj hxm
  have he0 := he0 hxu
  obtain ⟨hxm', hxu'⟩ := W.exists_isUnit_of_ord_eq_zero hx'0 hx'_ord
  obtain ⟨e', he', he'0⟩ := W.exists_hasValue_of_surjective hsurj hxm'
  have he'0 := he'0 hxu'
  have heA : e ∉ A := by
    intro heA
    have h1 := hc x₁ hx₁ ⟨e, heA⟩
    have hne : x₁ - algebraMap 𝕂 FM e ≠ 0 :=
      fun h0 => ne_algebraMap_of_coe_eq_jqModC M H x₁ hx₁ e (sub_eq_zero.mp h0)
    have h2 := ord_sub_algebraMap_pos_of_hasValue W x₁ e he hne
    change W.ord (x₁ - algebraMap 𝕂 FM e) ≤ 0 at h1
    omega
  have he'A : e' ∉ A := by
    intro he'A
    have h1 := hc' x₁' hx₁' ⟨e', he'A⟩
    have hne : x₁' - algebraMap 𝕂 FM e' ≠ 0 :=
      fun h0 => ne_algebraMap_of_coe_eq_qExpand_jqModC M H p x₁' hx₁' e' (sub_eq_zero.mp h0)
    have h2 := ord_sub_algebraMap_pos_of_hasValue W x₁' e' he' hne
    change W.ord (x₁' - algebraMap 𝕂 FM e') ≤ 0 at h1
    omega
  set y : 𝕂 := e * e' with hy
  have hy0 : y ≠ 0 := mul_ne_zero he0 he'0
  have hyu : W.HasValue u y := he.mul he'
  have hval : W.HasValue (u * (u ^ p)⁻¹) (y * (y ^ p)⁻¹) :=
    hyu.mul ((hasValue_pow hyu p).inv (pow_ne_zero _ hy0))
  have hτy : ((τ₁ : 𝕂) * τ₀) = y * (y ^ p)⁻¹ := hv.unique hval
  have hid : y * (y ^ p)⁻¹ = (y⁻¹) ^ (m + 1) := by
    rw [hm, pow_succ, mul_inv, mul_comm ((y ^ (m + 1))⁻¹), ← mul_assoc, mul_inv_cancel₀ hy0, one_mul, inv_pow]
  have hyn : y⁻¹ ∈ A.nonunits := by
    rw [hy, mul_inv]
    exact mul_mem (inv_mem_nonunits_of_not_mem heA) (inv_mem_nonunits_of_not_mem he'A)
  show ((τ₁ : 𝕂) * τ₀) ∈ A.nonunits
  rw [hτy, hid]
  exact pow_succ_mem_nonunits hyn m

end engine

end E4AV_CuspSides
p2m_reactivate "P2MW.S_ModularCurve_JHPlaceSpecialization_not_isInftySide_of_isZeroSide.E4AV_CuspSides"

end
p2m_reactivate "P2MW.S_ModularCurve_JHPlaceSpecialization_not_isInftySide_of_isZeroSide.E4AV_CuspSides"

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))
    (hW : JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A) W) :
    ¬ JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A) W := by
  exact E4AV_CuspSides.not_isInftySide_of_isZeroSide p M H A W hW

end S_ModularCurve_JHPlaceSpecialization_not_isInftySide_of_isZeroSide
end P2MW
export P2MW.S_ModularCurve_JHPlaceSpecialization_not_isInftySide_of_isZeroSide (solution)
