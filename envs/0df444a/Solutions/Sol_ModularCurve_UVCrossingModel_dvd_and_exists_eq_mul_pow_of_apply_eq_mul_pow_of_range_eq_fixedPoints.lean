-- Prove2me | solution 1 for ModularCurve.UVCrossingModel.dvd_and_exists_eq_mul_pow_of_apply_eq_mul_pow_of_range_eq_fixedPoints
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/45ff19ed-9506-5b39-b19a-dd8efb89e3ba

import Mathlib
import Definitions.Def_ModularCurve_UVCrossingModel
import Theorems.Thm_ModularCurve_UVCrossingModel_isIntegrallyClosed_of_uniformizer_pow_of_isAdicComplete
import Theorems.Thm_ModularCurve_UVCrossingModel_exists_unit_eigen_of_tangent
import Theorems.Thm_ModularCurve_UVCrossingModel_exists_sub_const_mem_maximalIdeal
import Theorems.Thm_ModularCurve_UVCrossingModel_const_mem_nonZeroDivisors
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_UVCrossingModel_dvd_and_exists_eq_mul_pow_of_apply_eq_mul_pow_of_range_eq_fixedPoints

set_option autoImplicit false
set_option maxHeartbeats 0

open IsLocalRing ModularCurve ModularCurve.UVCrossingModel

namespace PsiGerm

theorem const_eq_algebraMap {W : Type*} [CommRing W] (p : W) (w : W) :
    const p w = algebraMap W (UVCrossingModel W p) w := rfl

theorem engine
    {W : Type*} [CommRing W] [IsLocalRing W]
    (p : W) [IsLocalRing (UVCrossingModel W p)] [IsDomain (UVCrossingModel W p)] (hpu : ¬ IsUnit p)
    (p' : W)
    (n : ℕ) (hn : 1 ≤ n) (ζ' : W) (hζ'n : ζ' ^ n = 1) (hζ'prim : ∀ j : ℕ, 0 < j → j < n → IsUnit (ζ' ^ j - 1))
    (θ : UVCrossingModel W p ≃ₐ[W] UVCrossingModel W p)
    (X : UVCrossingModel W p) (hX : X ≠ 0) (γ₁ : (UVCrossingModel W p)ˣ)
    (hθX : θ ((γ₁ : UVCrossingModel W p) * X) = algebraMap W _ ζ' * ((γ₁ : UVCrossingModel W p) * X))
    (ψ : UVCrossingModel W p' →+* UVCrossingModel W p) (hψinj : Function.Injective ψ)
    (X' : UVCrossingModel W p') (γ' : (UVCrossingModel W p)ˣ) (hψX : ψ X' = ((γ' : UVCrossingModel W p) * X) ^ n)
    (hψrange : ∀ z : UVCrossingModel W p, z ∈ Set.range ψ ↔ θ z = z)
    (z : UVCrossingModel W p') (e : ℕ) (w : (UVCrossingModel W p)ˣ) (hz : ψ z = (w : UVCrossingModel W p) * X ^ e) :
    n ∣ e ∧ ∃ w' : (UVCrossingModel W p')ˣ, z = (w' : UVCrossingModel W p') * X' ^ (e / n) := by
  classical

  have hθconst : ∀ c : W, θ (algebraMap W _ c) = algebraMap W _ c := fun c => θ.commutes c
  have hθmax : ∀ x : UVCrossingModel W p, x ∈ maximalIdeal _ → θ x ∈ maximalIdeal _ := by
    intro x hx
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hx ⊢
    intro hu; apply hx
    have := hu.map θ.symm
    simpa using this
  have hθmod : ∀ x : UVCrossingModel W p, θ x - x ∈ maximalIdeal _ := by
    intro x
    obtain ⟨c, hc⟩ := exists_sub_const_mem_maximalIdeal hpu x
    rw [const_eq_algebraMap] at hc
    have h1 : θ x - x = θ (x - algebraMap W _ c) - (x - algebraMap W _ c) := by
      rw [map_sub, hθconst]; abel
    rw [h1]
    exact Ideal.sub_mem _ (hθmax _ hc) hc

  have hX₁ne : (γ₁ : UVCrossingModel W p) * X ≠ 0 := mul_ne_zero (Units.ne_zero γ₁) hX
  have hθX₁pow : ∀ k : ℕ, θ (((γ₁ : UVCrossingModel W p) * X) ^ k) = algebraMap W _ (ζ' ^ k) * ((γ₁ : UVCrossingModel W p) * X) ^ k := by
    intro k
    rw [map_pow, hθX, mul_pow, ← map_pow]

  have hfix : θ (ψ z) = ψ z := (hψrange _).mp ⟨z, rfl⟩

  let w₂ : (UVCrossingModel W p)ˣ := w * (γ₁⁻¹) ^ e
  have hw₂ : ((w₂ : (UVCrossingModel W p)ˣ) : UVCrossingModel W p) = (w : UVCrossingModel W p) * (↑γ₁⁻¹ : UVCrossingModel W p) ^ e := by
    simp [w₂]
  have hXe : (w : UVCrossingModel W p) * X ^ e = (w₂ : UVCrossingModel W p) * ((γ₁ : UVCrossingModel W p) * X) ^ e := by
    rw [hw₂, mul_pow, mul_assoc, ← mul_assoc (((↑γ₁⁻¹ : UVCrossingModel W p)) ^ e), ← mul_pow, Units.inv_mul, one_pow, one_mul]
  have hkey : θ (w₂ : UVCrossingModel W p) * algebraMap W _ (ζ' ^ e) = (w₂ : UVCrossingModel W p) := by
    have h1 : θ ((w₂ : UVCrossingModel W p) * ((γ₁ : UVCrossingModel W p) * X) ^ e) = (w₂ : UVCrossingModel W p) * ((γ₁ : UVCrossingModel W p) * X) ^ e := by
      rw [← hXe, ← hz]; exact hfix
    rw [map_mul, hθX₁pow, ← mul_assoc] at h1
    exact mul_right_cancel₀ (pow_ne_zero e hX₁ne) h1

  have hnu : ¬ IsUnit (ζ' ^ e - 1) := by
    intro hu
    have h1 : (w₂ : UVCrossingModel W p) * (algebraMap W _ (ζ' ^ e) - 1) =
        -(θ (w₂ : UVCrossingModel W p) - (w₂ : UVCrossingModel W p)) * algebraMap W _ (ζ' ^ e) := by
      linear_combination hkey
    have h2 : (w₂ : UVCrossingModel W p) * (algebraMap W _ (ζ' ^ e) - 1) ∈ maximalIdeal (UVCrossingModel W p) := by
      rw [h1]; exact Ideal.mul_mem_right _ _ (neg_mem (hθmod _))
    have h3 : IsUnit ((w₂ : UVCrossingModel W p) * (algebraMap W _ (ζ' ^ e) - 1)) := by
      refine (Units.isUnit w₂).mul ?_
      rw [← map_one (algebraMap W (UVCrossingModel W p)), ← map_sub]
      exact hu.map _
    exact (IsLocalRing.mem_maximalIdeal _).mp h2 h3

  have hdvd : n ∣ e := by
    by_contra hnd
    have hr : 0 < e % n := Nat.pos_of_ne_zero (fun h0 => hnd (Nat.dvd_of_mod_eq_zero h0))
    have hrn : e % n < n := Nat.mod_lt e (by omega)
    apply hnu
    have : ζ' ^ e = ζ' ^ (e % n) := by
      conv_lhs => rw [← Nat.div_add_mod e n, pow_add, pow_mul, hζ'n, one_pow, one_mul]
    rw [this]; exact hζ'prim _ hr hrn
  refine ⟨hdvd, ?_⟩
  obtain ⟨k, hk⟩ := hdvd
  have hkn : e / n = k := by rw [hk, Nat.mul_div_cancel_left k (by omega)]

  have hψXk : ψ (X' ^ k) = (γ' : UVCrossingModel W p) ^ e * X ^ e := by
    rw [map_pow, hψX, ← pow_mul, ← hk, mul_pow]
  have hψXk_ne : ψ (X' ^ k) ≠ 0 := by
    rw [hψXk]; exact mul_ne_zero (pow_ne_zero _ (Units.ne_zero γ')) (pow_ne_zero _ hX)

  let u : (UVCrossingModel W p)ˣ := w * (γ'⁻¹) ^ e
  have huval : ((u : (UVCrossingModel W p)ˣ) : UVCrossingModel W p) = (w : UVCrossingModel W p) * (↑γ'⁻¹ : UVCrossingModel W p) ^ e := by
    simp [u]
  have hzu : ψ z = (u : UVCrossingModel W p) * ψ (X' ^ k) := by
    rw [hz, hψXk, huval, mul_assoc, ← mul_assoc ((↑γ'⁻¹ : UVCrossingModel W p) ^ e), ← mul_pow, Units.inv_mul, one_pow, one_mul]

  have hfixk : θ (ψ (X' ^ k)) = ψ (X' ^ k) := (hψrange _).mp ⟨_, rfl⟩
  have hufix : θ (u : UVCrossingModel W p) = (u : UVCrossingModel W p) := by
    have h1 : θ ((u : UVCrossingModel W p) * ψ (X' ^ k)) = (u : UVCrossingModel W p) * ψ (X' ^ k) := by rw [← hzu]; exact hfix
    rw [map_mul, hfixk] at h1
    exact mul_right_cancel₀ hψXk_ne h1
  have huinvfix : θ (↑u⁻¹ : UVCrossingModel W p) = (↑u⁻¹ : UVCrossingModel W p) := by
    have h1 : θ (↑u⁻¹ : UVCrossingModel W p) * (u : UVCrossingModel W p) = 1 := by
      rw [← hufix, ← map_mul, Units.inv_mul, map_one]
    calc θ (↑u⁻¹ : UVCrossingModel W p) = θ (↑u⁻¹ : UVCrossingModel W p) * ((u : UVCrossingModel W p) * (↑u⁻¹ : UVCrossingModel W p)) := by
          rw [Units.mul_inv, mul_one]
      _ = (θ (↑u⁻¹ : UVCrossingModel W p) * (u : UVCrossingModel W p)) * (↑u⁻¹ : UVCrossingModel W p) := by ring
      _ = (↑u⁻¹ : UVCrossingModel W p) := by rw [h1, one_mul]
  obtain ⟨u', hu'⟩ := (hψrange _).mpr hufix
  obtain ⟨u'', hu''⟩ := (hψrange _).mpr huinvfix
  have hu'unit : IsUnit u' := by
    refine isUnit_iff_exists_inv.mpr ⟨u'', hψinj ?_⟩
    rw [map_mul, hu', hu'', map_one, Units.mul_inv]
  refine ⟨hu'unit.unit, hψinj ?_⟩
  rw [hkn, map_mul, IsUnit.unit_spec, hu', ← hzu]

end PsiGerm

open PsiGerm in
theorem solution
    {W : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]
    (π : W) (hπ : maximalIdeal W = Ideal.span {π}) (m : ℕ) (hm : 1 ≤ m)
    [IsLocalRing (UVCrossingModel W (π ^ m))]
    [IsAdicComplete (maximalIdeal (UVCrossingModel W (π ^ m))) (UVCrossingModel W (π ^ m))]
    (n : ℕ) (hn : 1 ≤ n) (hnu : IsUnit ((n : ℕ) : W)) (ζ ζ' : W) (hζ : ζ * ζ' = 1) (hζn : ζ ^ n = 1)
    (hζprim : ∀ j : ℕ, 0 < j → j < n → IsUnit (ζ ^ j - 1))
    (θ : UVCrossingModel W (π ^ m) ≃ₐ[W] UVCrossingModel W (π ^ m)) (hord : ∀ z, θ^[n] z = z)
    (htanU : θ (U (π ^ m)) - const (π ^ m) ζ * U (π ^ m) ∈ maximalIdeal (UVCrossingModel W (π ^ m)) ^ 2)
    (htanV : θ (V (π ^ m)) - const (π ^ m) ζ' * V (π ^ m) ∈ maximalIdeal (UVCrossingModel W (π ^ m)) ^ 2)
    (ψ : UVCrossingModel W (π ^ (m * n)) →+* UVCrossingModel W (π ^ m)) (hψinj : Function.Injective ψ)
    (hψc : ∀ w : W, ψ (const (π ^ (m * n)) w) = const (π ^ m) w)
    (γ γ' : (UVCrossingModel W (π ^ m))ˣ)
    (hψU : ψ (U (π ^ (m * n))) = ((γ : UVCrossingModel W (π ^ m)) * U (π ^ m)) ^ n)
    (hψV : ψ (V (π ^ (m * n))) = ((γ' : UVCrossingModel W (π ^ m)) * V (π ^ m)) ^ n)
    (hψrange : ∀ z : UVCrossingModel W (π ^ m), z ∈ Set.range ψ ↔ θ z = z) :
    (∀ (z : UVCrossingModel W (π ^ (m * n))) (e : ℕ) (w : (UVCrossingModel W (π ^ m))ˣ),
      ψ z = (w : UVCrossingModel W (π ^ m)) * V (π ^ m) ^ e →
        n ∣ e ∧ ∃ w' : (UVCrossingModel W (π ^ (m * n)))ˣ, z = (w' : UVCrossingModel W (π ^ (m * n))) * V (π ^ (m * n)) ^ (e / n)) ∧
    (∀ (z : UVCrossingModel W (π ^ (m * n))) (e : ℕ) (w : (UVCrossingModel W (π ^ m))ˣ),
      ψ z = (w : UVCrossingModel W (π ^ m)) * U (π ^ m) ^ e →
        n ∣ e ∧ ∃ w' : (UVCrossingModel W (π ^ (m * n)))ˣ, z = (w' : UVCrossingModel W (π ^ (m * n))) * U (π ^ (m * n)) ^ (e / n)) := by
  classical
  have hπirr : Irreducible π := (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mpr hπ
  obtain ⟨hdom, -, -⟩ := ModularCurve.UVCrossingModel.isIntegrallyClosed_of_uniformizer_pow_of_isAdicComplete π hπirr m hm
  haveI := hdom
  have hπmem : π ∈ maximalIdeal W := by rw [hπ]; exact Ideal.mem_span_singleton_self π
  have hπne : π ≠ 0 := by
    intro h0
    apply IsDiscreteValuationRing.not_a_field' (R := W)
    rw [hπ, h0, Ideal.span_singleton_eq_bot]
  have hπmu : ¬ IsUnit (π ^ m) := fun hu =>
    (IsLocalRing.mem_maximalIdeal _).mp hπmem (isUnit_pow_iff (by omega) |>.mp hu)
  have hπmnz : π ^ m ∈ nonZeroDivisors W := mem_nonZeroDivisors_of_ne_zero (pow_ne_zero m hπne)
  have hnil : ∃ j : ℕ, maximalIdeal W ^ j ≤ Ideal.span {π ^ m} := ⟨m, by rw [hπ, Ideal.span_singleton_pow]⟩
  obtain ⟨γ₁, -, hγU, hγV⟩ := ModularCurve.UVCrossingModel.exists_unit_eigen_of_tangent (π ^ m) hπmu hπmnz hnil n hnu ζ ζ' hζ hζn θ hord htanU htanV

  have hUV : U (π ^ m) * V (π ^ m) = const (π ^ m) (π ^ m) := by
    change UVCrossingModel.mk (π ^ m) (MvPowerSeries.X 0) * UVCrossingModel.mk (π ^ m) (MvPowerSeries.X 1) =
      UVCrossingModel.mk (π ^ m) (MvPowerSeries.C (π ^ m))
    rw [← map_mul]
    exact (Ideal.Quotient.eq).mpr (Ideal.subset_span (by simp))
  have hc0 : const (π ^ m) (π ^ m) ≠ 0 := nonZeroDivisors.ne_zero (const_mem_nonZeroDivisors hπmnz)
  have hU0 : U (π ^ m) ≠ 0 := fun h => hc0 (by rw [← hUV, h, zero_mul])
  have hV0 : V (π ^ m) ≠ 0 := fun h => hc0 (by rw [← hUV, h, mul_zero])

  have hζu : IsUnit ζ := isUnit_iff_exists_inv.mpr ⟨ζ', hζ⟩
  have hζ'u : IsUnit ζ' := isUnit_iff_exists_inv.mpr ⟨ζ, by rw [mul_comm]; exact hζ⟩
  have hζ'n : ζ' ^ n = 1 := by
    have : (ζ * ζ') ^ n = 1 := by rw [hζ, one_pow]
    rwa [mul_pow, hζn, one_mul] at this
  have hζ'prim : ∀ j : ℕ, 0 < j → j < n → IsUnit (ζ' ^ j - 1) := by
    intro j hj hjn
    have e1 : ζ' ^ j - 1 = -(ζ' ^ j) * (ζ ^ j - 1) := by
      have : ζ ^ j * ζ' ^ j = 1 := by rw [← mul_pow, hζ, one_pow]
      linear_combination this
    rw [e1]
    exact ((hζ'u.pow j).neg).mul (hζprim j hj hjn)
  refine ⟨fun z e w hz => ?_, fun z e w hz => ?_⟩
  · exact engine (π ^ m) hπmu (π ^ (m * n)) n hn ζ' hζ'n hζ'prim θ (V (π ^ m)) hV0 γ₁⁻¹
      (by rw [← const_eq_algebraMap]; exact hγV) ψ hψinj (V (π ^ (m * n))) γ' hψV hψrange z e w hz
  · exact engine (π ^ m) hπmu (π ^ (m * n)) n hn ζ hζn hζprim θ (U (π ^ m)) hU0 γ₁
      (by rw [← const_eq_algebraMap]; exact hγU) ψ hψinj (U (π ^ (m * n))) γ hψU hψrange z e w hz

end S_ModularCurve_UVCrossingModel_dvd_and_exists_eq_mul_pow_of_apply_eq_mul_pow_of_range_eq_fixedPoints
end P2MW
export P2MW.S_ModularCurve_UVCrossingModel_dvd_and_exists_eq_mul_pow_of_apply_eq_mul_pow_of_range_eq_fixedPoints (solution)
