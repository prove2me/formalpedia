-- Prove2me | solution 1 for IsLocalRing.exists_branchReadings_of_ringEquiv_adicCompletion_uvCrossingModel_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/d4be26d7-0b50-5272-b48c-4258c74aa390

import Mathlib
import Definitions.Def_ModularCurve_UVCrossingModel
import Theorems.Thm_ModularCurve_UVCrossingModel_mem_iff_ringEquiv_adicCompletion_mem_span_or_swap_of_ne
import Theorems.Thm_ModularCurve_UVCrossingModel_exists_ringEquiv_quotient_span_V_powerSeries
import Theorems.Thm_ModularCurve_UVCrossingModel_exists_ringEquiv_quotient_span_U_quotient_span_V
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsLocalRing_exists_branchReadings_of_ringEquiv_adicCompletion_uvCrossingModel_pow

set_option autoImplicit false

open IsLocalRing ModularCurve ModularCurve.UVCrossingModel PowerSeries

namespace BranchDict

section Readings

variable {W : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
variable (π : W) (hπ : maximalIdeal W = Ideal.span {π}) (E : ℕ) (hE : 1 ≤ E)

include hπ hE in
theorem span_pow_le : Ideal.span {π ^ E} ≤ maximalIdeal W := by
  rw [hπ, Ideal.span_singleton_le_span_singleton]
  exact dvd_pow_self π (by omega)

noncomputable def red : W ⧸ Ideal.span {π ^ E} →+* ResidueField W :=
  Ideal.Quotient.factor (span_pow_le π hπ E hE)

theorem red_mk (w : W) : red π hπ E hE (Ideal.Quotient.mk _ w) = residue W w := rfl

theorem red_surjective : Function.Surjective (red π hπ E hE) := by
  intro x
  obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact ⟨Ideal.Quotient.mk _ w, rfl⟩

include hπ in
theorem red_pi : red π hπ E hE (Ideal.Quotient.mk _ π) = 0 := by
  rw [red_mk, residue_eq_zero_iff, hπ]
  exact Ideal.mem_span_singleton_self π

structure Reading where
  ρ : UVCrossingModel W (π ^ E) →+* PowerSeries (ResidueField W)
  Z : UVCrossingModel W (π ^ E)
  Z' : UVCrossingModel W (π ^ E)
  surj : Function.Surjective ρ
  ρZ : ρ Z = X
  ker_iff : ∀ m, ρ m = 0 ↔ m ∈ Ideal.span {const (π ^ E) π, Z'}

include hπ hE in

theorem exists_readingV : ∃ R : Reading π E, R.Z = U (π ^ E) ∧ R.Z' = V (π ^ E) ∧
    (∀ w : W, R.ρ (const (π ^ E) w) = C (residue W w)) := by
  obtain ⟨e, heU, heV, heC⟩ := ModularCurve.UVCrossingModel.exists_ringEquiv_quotient_span_V_powerSeries (W := W) (π ^ E)
  let ρ : UVCrossingModel W (π ^ E) →+* PowerSeries (ResidueField W) :=
    (PowerSeries.map (red π hπ E hE)).comp (e.toRingHom.comp (Ideal.Quotient.mk (Ideal.span {V (π ^ E)})))
  have hρ : ∀ m, ρ m = PowerSeries.map (red π hπ E hE) (e (Ideal.Quotient.mk _ m)) := fun m => rfl
  have hρC : ∀ w : W, ρ (const (π ^ E) w) = C (residue W w) := by
    intro w; rw [hρ, heC, map_C]; rfl
  refine ⟨⟨ρ, U (π ^ E), V (π ^ E), ?surj, ?ρZ, ?ker⟩, rfl, rfl, hρC⟩
  · intro s
    obtain ⟨s', rfl⟩ := PowerSeries.map_surjective (red π hπ E hE) (red_surjective π hπ E hE) s
    obtain ⟨m', hm'⟩ := e.surjective s'
    obtain ⟨m, rfl⟩ := Ideal.Quotient.mk_surjective m'
    exact ⟨m, by rw [hρ, hm']⟩
  · rw [hρ, heU, map_X]
  · intro m
    constructor
    · intro h0
      rw [hρ] at h0

      set s := e (Ideal.Quotient.mk (Ideal.span {V (π ^ E)}) m) with hs
      have hcoef : ∀ n, ∃ w : W, coeff n s = Ideal.Quotient.mk _ (π * w) := by
        intro n
        have hn := congrArg (coeff n) h0
        rw [coeff_map, map_zero] at hn
        obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (coeff n s)
        rw [← ha, red_mk, residue_eq_zero_iff, hπ, Ideal.mem_span_singleton'] at hn
        obtain ⟨w, hw⟩ := hn
        exact ⟨w, by rw [← ha, ← hw, mul_comm]⟩
      choose w hw using hcoef
      have hs' : s = PowerSeries.C (Ideal.Quotient.mk _ π) * PowerSeries.mk (fun n => Ideal.Quotient.mk _ (w n)) := by
        ext n
        rw [hw, PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, ← map_mul]

      obtain ⟨m₁', hm₁'⟩ := e.surjective (PowerSeries.mk (fun n => Ideal.Quotient.mk _ (w n)))
      obtain ⟨m₁, rfl⟩ := Ideal.Quotient.mk_surjective m₁'
      have hmk : Ideal.Quotient.mk (Ideal.span {V (π ^ E)}) m =
          Ideal.Quotient.mk (Ideal.span {V (π ^ E)}) (const (π ^ E) π * m₁) := by
        apply e.injective
        rw [← hs, hs', map_mul, map_mul, heC, hm₁']
      rw [Ideal.Quotient.eq, Ideal.mem_span_singleton'] at hmk
      obtain ⟨b, hb⟩ := hmk
      rw [Ideal.mem_span_pair]
      exact ⟨m₁, b, by linear_combination hb⟩
    · intro hm
      rw [Ideal.mem_span_pair] at hm
      obtain ⟨a, b, rfl⟩ := hm
      rw [map_add, map_mul, map_mul, hρC, hρ (V (π ^ E)), heV, map_zero, mul_zero, add_zero]
      have : residue W π = 0 := by rw [residue_eq_zero_iff, hπ]; exact Ideal.mem_span_singleton_self π
      rw [this, map_zero, mul_zero]

include hπ hE in

theorem exists_readingU : ∃ R : Reading π E, R.Z = V (π ^ E) ∧ R.Z' = U (π ^ E) ∧
    (∀ w : W, R.ρ (const (π ^ E) w) = C (residue W w)) := by
  obtain ⟨RV, hZ, hZ', hC⟩ := exists_readingV π hπ E hE
  obtain ⟨eUV, heUV⟩ := ModularCurve.UVCrossingModel.exists_ringEquiv_quotient_span_U_quotient_span_V (W := W) (π ^ E)

  let σ : UVCrossingModel W (π ^ E) ≃+* UVCrossingModel W (π ^ E) := crossingSwap (π ^ E)
  have σU : σ (U (π ^ E)) = V (π ^ E) := by
    change crossingSwap (π ^ E) (mk (π ^ E) (MvPowerSeries.X 0)) = mk (π ^ E) (MvPowerSeries.X 1)
    rw [crossingSwap_mk, uvSwapEquiv_X_zero]
  have σV : σ (V (π ^ E)) = U (π ^ E) := by
    change crossingSwap (π ^ E) (mk (π ^ E) (MvPowerSeries.X 1)) = mk (π ^ E) (MvPowerSeries.X 0)
    rw [crossingSwap_mk, uvSwapEquiv_X_one]
  have σC : ∀ w : W, σ (const (π ^ E) w) = const (π ^ E) w := by
    intro w
    change crossingSwap (π ^ E) (mk (π ^ E) (MvPowerSeries.C w)) = mk (π ^ E) (MvPowerSeries.C w)
    rw [crossingSwap_mk, uvSwapEquiv_C]
  refine ⟨⟨RV.ρ.comp σ.toRingHom, V (π ^ E), U (π ^ E), ?_, ?_, ?_⟩, rfl, rfl, ?_⟩
  · exact RV.surj.comp σ.surjective
  · change RV.ρ (σ (V (π ^ E))) = X
    rw [σV, ← hZ]; exact RV.ρZ
  · intro m
    change RV.ρ (σ m) = 0 ↔ _
    rw [RV.ker_iff, hZ']

    constructor
    · intro h
      rw [Ideal.mem_span_pair] at h ⊢
      obtain ⟨a, b, hab⟩ := h
      refine ⟨σ.symm a, σ.symm b, ?_⟩
      apply σ.injective
      rw [map_add, map_mul, map_mul, σ.apply_symm_apply, σ.apply_symm_apply, σC, σU, hab]
    · intro h
      rw [Ideal.mem_span_pair] at h ⊢
      obtain ⟨a, b, rfl⟩ := h
      exact ⟨σ a, σ b, by rw [map_add, map_mul, map_mul, σC, σU]⟩
  · intro w
    change RV.ρ (σ (const (π ^ E) w)) = _
    rw [σC, hC]

end Readings

end BranchDict

namespace BranchDict

section Package

variable {W : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
variable (π : W) (E : ℕ)

theorem constantCoeff_eq_zero_of_not_isUnit (R : Reading π E) (m : UVCrossingModel W (π ^ E))
    (hm : ¬ IsUnit m) : constantCoeff (R.ρ m) = 0 := by
  haveI : Nontrivial (UVCrossingModel W (π ^ E)) := R.ρ.domain_nontrivial
  haveI : IsLocalRing (UVCrossingModel W (π ^ E)) :=
    IsLocalRing.of_surjective' (mk (π ^ E)) (mk_surjective (π ^ E))
  let χ : UVCrossingModel W (π ^ E) →+* ResidueField W := (constantCoeff).comp R.ρ
  have hχ : Function.Surjective χ := by
    intro a
    obtain ⟨m, hm⟩ := R.surj (C a)
    exact ⟨m, by simp [χ, hm]⟩
  have hmax : (RingHom.ker χ).IsMaximal := RingHom.ker_isMaximal_of_surjective χ hχ
  have hker : RingHom.ker χ = maximalIdeal _ := IsLocalRing.eq_maximalIdeal hmax
  have hmem : m ∈ maximalIdeal (UVCrossingModel W (π ^ E)) := (mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hm)
  rw [← hker, RingHom.mem_ker] at hmem
  exact hmem

theorem reading_package (R : Reading π E)
    {O : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    (ι : AdicCompletion (maximalIdeal O) O ≃+* UVCrossingModel W (π ^ E))
    (P : Ideal O) (hP : ∀ f : O, f ∈ P ↔
      ι (algebraMap O (AdicCompletion (maximalIdeal O) O) f) ∈ Ideal.span {const (π ^ E) π, R.Z'})
    (c : O) (γ : (UVCrossingModel W (π ^ E))ˣ)
    (hc : ι (algebraMap O (AdicCompletion (maximalIdeal O) O) c) = (γ : UVCrossingModel W (π ^ E)) * R.Z) :
    ∃ φ : O →+* PowerSeries (ResidueField W),
      (∀ f : O, φ f = 0 ↔ f ∈ P) ∧
      (∀ f : O, f ∈ maximalIdeal O → constantCoeff (φ f) = 0) ∧
      (∃ u : PowerSeries (ResidueField W), IsUnit u ∧ φ c = u * X) ∧
      (∀ (f : O) (n : ℕ), φ f ≠ 0 → (φ f).order = n →
        ∃ γ' : UVCrossingModel W (π ^ E), IsUnit γ' ∧
          ι (algebraMap O (AdicCompletion (maximalIdeal O) O) f) - γ' * R.Z ^ n ∈
            Ideal.span {const (π ^ E) π, R.Z'}) := by
  classical
  let ιh : O →+* UVCrossingModel W (π ^ E) := ι.toRingHom.comp (algebraMap O (AdicCompletion (maximalIdeal O) O))
  have hιh : ∀ f, ιh f = ι (algebraMap O (AdicCompletion (maximalIdeal O) O) f) := fun f => rfl
  let φ : O →+* PowerSeries (ResidueField W) := R.ρ.comp ιh
  have hφ : ∀ f, φ f = R.ρ (ι (algebraMap O (AdicCompletion (maximalIdeal O) O) f)) := fun f => rfl
  refine ⟨φ, ?_, ?_, ?_, ?_⟩
  · intro f
    rw [hφ, R.ker_iff, hP]
  · intro f hf
    rw [hφ]
    apply constantCoeff_eq_zero_of_not_isUnit

    intro hu
    have hu' := (hu.map ι.symm)
    rw [ι.symm_apply_apply] at hu'
    have hu'' := hu'.map (AdicCompletion.evalₐ (maximalIdeal O) 1)
    rw [AlgHom.commutes, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem.mpr (by rwa [pow_one]),
      isUnit_zero_iff] at hu''
    haveI : Nontrivial (O ⧸ maximalIdeal O ^ 1) :=
      Ideal.Quotient.nontrivial_iff.mpr (by rw [pow_one]; exact (maximalIdeal.isMaximal O).ne_top)
    exact zero_ne_one hu''
  · refine ⟨R.ρ γ, (γ.isUnit).map R.ρ, ?_⟩
    rw [hφ, hc, map_mul, R.ρZ]
  · intro f n hf hn
    set s := φ f with hs
    have hsn : s.order.toNat = n := by rw [hn]; rfl
    have hdec : X ^ n * divXPowOrder s = s := by rw [← hsn]; exact X_pow_order_mul_divXPowOrder
    have hd0 : constantCoeff (divXPowOrder s) ≠ 0 := fun h => hf (constantCoeff_divXPowOrder_eq_zero_iff.mp h)
    obtain ⟨γ₀, hγ₀⟩ := R.surj (divXPowOrder s)
    have hγ₀u : IsUnit γ₀ := by
      by_contra hnu
      exact hd0 (hγ₀ ▸ constantCoeff_eq_zero_of_not_isUnit π E R γ₀ hnu)
    refine ⟨γ₀, hγ₀u, ?_⟩
    rw [← R.ker_iff, map_sub, map_mul, map_pow, R.ρZ, hγ₀, ← hφ, ← hs, sub_eq_zero, mul_comm]
    exact hdec.symm

end Package

end BranchDict

open BranchDict in
theorem solution
    {W : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]
    (π : W) (hπ : maximalIdeal W = Ideal.span {π}) (E : ℕ) (hE : 1 ≤ E)
    {O : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    (ι : AdicCompletion (maximalIdeal O) O ≃+* UVCrossingModel W (π ^ E))
    (t : O) (ht : ι (algebraMap O (AdicCompletion (maximalIdeal O) O) t) = const (π ^ E) π)
    (cx cy : O) (γU γV : (UVCrossingModel W (π ^ E))ˣ)
    (hcx : ι (algebraMap O (AdicCompletion (maximalIdeal O) O) cx) = (γU : UVCrossingModel W (π ^ E)) * U (π ^ E))
    (hcy : ι (algebraMap O (AdicCompletion (maximalIdeal O) O) cy) = (γV : UVCrossingModel W (π ^ E)) * V (π ^ E))
    (PV PU : Ideal O) [PV.IsPrime] [PU.IsPrime]
    (htV : t ∈ PV) (hcyV : cy ∈ PV) (hcxV : cx ∉ PV)
    (htU : t ∈ PU) (hcxU : cx ∈ PU) (hcyU : cy ∉ PU) :
    (∀ f : O, f ∈ PV ↔
      ι (algebraMap O (AdicCompletion (maximalIdeal O) O) f) ∈ Ideal.span {const (π ^ E) π, V (π ^ E)}) ∧
    (∀ f : O, f ∈ PU ↔
      ι (algebraMap O (AdicCompletion (maximalIdeal O) O) f) ∈ Ideal.span {const (π ^ E) π, U (π ^ E)}) ∧
    (∃ φV : O →+* PowerSeries (ResidueField W),
      (∀ f : O, φV f = 0 ↔ f ∈ PV) ∧
      (∀ f : O, f ∈ maximalIdeal O → PowerSeries.constantCoeff (φV f) = 0) ∧
      (∃ u : PowerSeries (ResidueField W), IsUnit u ∧ φV cx = u * PowerSeries.X) ∧
      (∀ (f : O) (n : ℕ), φV f ≠ 0 → (φV f).order = n →
        ∃ γ : UVCrossingModel W (π ^ E), IsUnit γ ∧
          ι (algebraMap O (AdicCompletion (maximalIdeal O) O) f) - γ * U (π ^ E) ^ n ∈
            Ideal.span {const (π ^ E) π, V (π ^ E)})) ∧
    (∃ φU : O →+* PowerSeries (ResidueField W),
      (∀ f : O, φU f = 0 ↔ f ∈ PU) ∧
      (∀ f : O, f ∈ maximalIdeal O → PowerSeries.constantCoeff (φU f) = 0) ∧
      (∃ u : PowerSeries (ResidueField W), IsUnit u ∧ φU cy = u * PowerSeries.X) ∧
      (∀ (f : O) (n : ℕ), φU f ≠ 0 → (φU f).order = n →
        ∃ γ : UVCrossingModel W (π ^ E), IsUnit γ ∧
          ι (algebraMap O (AdicCompletion (maximalIdeal O) O) f) - γ * V (π ^ E) ^ n ∈
            Ideal.span {const (π ^ E) π, U (π ^ E)})) := by
  classical
  obtain ⟨RV, hVZ, hVZ', hVC⟩ := exists_readingV π hπ E hE
  obtain ⟨RU, hUZ, hUZ', hUC⟩ := exists_readingU π hπ E hE

  have hcxm : cx ∈ maximalIdeal O := (mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr fun hu =>
    (Ideal.IsPrime.ne_top ‹PU.IsPrime›) (Ideal.eq_top_of_isUnit_mem _ hcxU hu))
  have hcym : cy ∈ maximalIdeal O := (mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr fun hu =>
    (Ideal.IsPrime.ne_top ‹PV.IsPrime›) (Ideal.eq_top_of_isUnit_mem _ hcyV hu))
  have hne : PV ≠ PU := fun h => hcxV (h ▸ hcxU)
  have hV1 : PV ≠ maximalIdeal O := fun h => hcxV (h ▸ hcxm)
  have hU1 : PU ≠ maximalIdeal O := fun h => hcyU (h ▸ hcym)

  have D1 : (∀ f : O, f ∈ PV ↔
      ι (algebraMap O (AdicCompletion (maximalIdeal O) O) f) ∈ Ideal.span {const (π ^ E) π, V (π ^ E)}) ∧
    (∀ f : O, f ∈ PU ↔
      ι (algebraMap O (AdicCompletion (maximalIdeal O) O) f) ∈ Ideal.span {const (π ^ E) π, U (π ^ E)}) := by
    rcases ModularCurve.UVCrossingModel.mem_iff_ringEquiv_adicCompletion_mem_span_or_swap_of_ne π hπ E hE ι t ht
        PV PU hne htV htU hV1 hU1 with h | h
    ·
      exfalso
      have h1 := (h.1 cy).mp hcyV
      rw [hcy, ← hUZ', ← RU.ker_iff, map_mul, ← hUZ, RU.ρZ] at h1
      have h2 : IsUnit (RU.ρ (γV : UVCrossingModel W (π ^ E))) := (γV.isUnit).map RU.ρ
      exact (mul_ne_zero h2.ne_zero X_ne_zero) h1
    · exact h
  refine ⟨D1.1, D1.2, ?_, ?_⟩
  · have := reading_package π E RV ι PV (by rw [hVZ']; exact D1.1) cx γU (by rw [hVZ]; exact hcx)
    rw [hVZ, hVZ'] at this
    exact this
  · have := reading_package π E RU ι PU (by rw [hUZ']; exact D1.2) cy γV (by rw [hUZ]; exact hcy)
    rw [hUZ, hUZ'] at this
    exact this

end S_IsLocalRing_exists_branchReadings_of_ringEquiv_adicCompletion_uvCrossingModel_pow
end P2MW
export P2MW.S_IsLocalRing_exists_branchReadings_of_ringEquiv_adicCompletion_uvCrossingModel_pow (solution)
