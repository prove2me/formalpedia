-- Prove2me | solution 1 for IsRegularLocalRing.exists_algEquiv_mvPowerSeries_quotient_span_C_sub_of_maximalIdeal_eq_span_pair
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/ea242989-49e3-5fa7-b933-da3492ae0cbe

import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.MvPowerSeries.Basic
import Theorems.Thm_MvPowerSeries_exists_algHom_apply_X_eq
import Theorems.Thm_MvPowerSeries_algHom_surjective_of_apply_X_eq
import Theorems.Thm_IsRegularLocalRing_mvPowerSeries_fin
import Theorems.Thm_MvPowerSeries_ringKrullDim_fin_eq_of_isDiscreteValuationRing
import Theorems.Thm_IsRegularLocalRing_quotient_span_singleton_of_notMem_sq_of_forall_minimalPrimes_notMem
import Theorems.Thm_IsLocalRing_ringKrullDim_quotient_span_singleton_add_one_of_forall_minimalPrimes_notMem
import Theorems.Thm_IsRegularLocalRing_isDomain
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsRegularLocalRing_exists_algEquiv_mvPowerSeries_quotient_span_C_sub_of_maximalIdeal_eq_span_pair
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType"

set_option autoImplicit false

open IsLocalRing MvPowerSeries

theorem solution
    (W₀ : Type) [CommRing W₀] [IsDomain W₀] [IsDiscreteValuationRing W₀]
    (π : W₀) (hπ : maximalIdeal W₀ = Ideal.span {π})
    (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Algebra W₀ R]
    [IsAdicComplete (maximalIdeal R) R] [IsRegularLocalRing R]
    (hdim : ringKrullDim R = 2)
    (hres : ∀ r : R, ∃ w : W₀, r - algebraMap W₀ R w ∈ maximalIdeal R)
    (hπR : algebraMap W₀ R π ∈ maximalIdeal R)
    (x₀ x₁ : R) (hmax : maximalIdeal R = Ideal.span {x₀, x₁}) :
    ∃ (h : MvPowerSeries (Fin 2) W₀) (_ : MvPowerSeries.constantCoeff h = 0)
      (e : R ≃ₐ[W₀] (MvPowerSeries (Fin 2) W₀ ⧸ Ideal.span {MvPowerSeries.C π - h})),
      e x₀ = Ideal.Quotient.mk _ (MvPowerSeries.X 0) ∧ e x₁ = Ideal.Quotient.mk _ (MvPowerSeries.X 1) := by
  classical

  have hπunit : ¬ IsUnit π := fun hu => by
    have htop : maximalIdeal W₀ = ⊤ := by rw [hπ]; exact Ideal.span_singleton_eq_top.mpr hu
    exact (maximalIdeal.isMaximal W₀).ne_top htop
  have hπ0 : π ≠ 0 := by
    intro h0
    apply IsDiscreteValuationRing.not_a_field W₀
    rw [hπ, h0, Ideal.span_singleton_eq_bot]

  have hrange : Set.range (![x₀, x₁] : Fin 2 → R) = {x₀, x₁} :=
    Matrix.range_cons_cons_empty x₀ x₁ ![]
  have ha : ∀ i, (![x₀, x₁] : Fin 2 → R) i ∈ maximalIdeal R := by
    intro i
    rw [hmax, ← hrange]
    exact Ideal.subset_span ⟨i, rfl⟩

  obtain ⟨φ, hφ⟩ := MvPowerSeries.exists_algHom_apply_X_eq (𝒪 := W₀) (maximalIdeal R)
    (![x₀, x₁] : Fin 2 → R) ha
  have hφ0 : φ (X 0) = x₀ := hφ 0
  have hφ1 : φ (X 1) = x₁ := hφ 1

  have hφs : Function.Surjective φ := by
    refine MvPowerSeries.algHom_surjective_of_apply_X_eq φ (![x₀, x₁] : Fin 2 → R) hφ ha ?_
    intro q
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
    obtain ⟨w, hw⟩ := hres r
    refine ⟨w, ?_⟩
    simp only [Function.comp_apply]
    rw [Ideal.Quotient.eq, hrange, ← hmax, ← Ideal.neg_mem_iff, neg_sub]
    exact hw

  have hπmem : algebraMap W₀ R π ∈ Ideal.span {x₀, x₁} := by rw [← hmax]; exact hπR
  obtain ⟨c₀, c₁, hc⟩ := Ideal.mem_span_pair.mp hπmem
  obtain ⟨g₀, hg₀⟩ := hφs c₀
  obtain ⟨g₁, hg₁⟩ := hφs c₁
  obtain ⟨h, hh⟩ : ∃ h : MvPowerSeries (Fin 2) W₀, h = g₀ * X 0 + g₁ * X 1 := ⟨_, rfl⟩
  have hh0 : constantCoeff h = 0 := by
    simp only [hh, map_add, map_mul, constantCoeff_X, mul_zero, add_zero]
  have hφC : φ (C π) = algebraMap W₀ R π := by
    rw [MvPowerSeries.c_eq_algebraMap]; exact φ.commutes π
  have hφh : φ (C π - h) = 0 := by
    simp only [map_sub, hφC, hh, map_add, map_mul, hφ0, hφ1, hg₀, hg₁]
    rw [hc, sub_self]
  have hcc : constantCoeff (C π - h) = π := by
    rw [map_sub, constantCoeff_C, hh0, sub_zero]

  have hJφ : ∀ q ∈ Ideal.span {C π - h}, φ q = 0 := by
    intro q hq
    obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.mp hq
    rw [map_mul, hφh, mul_zero]
  let ψ : (MvPowerSeries (Fin 2) W₀ ⧸ Ideal.span {C π - h}) →ₐ[W₀] R :=
    Ideal.Quotient.liftₐ (Ideal.span {C π - h}) φ hJφ
  have hψmk : ∀ q, ψ (Ideal.Quotient.mk (Ideal.span {C π - h}) q) = φ q := fun q => rfl
  have hψs : Function.Surjective ψ := by
    intro r
    obtain ⟨q, rfl⟩ := hφs r
    exact ⟨Ideal.Quotient.mk _ q, hψmk q⟩

  haveI : IsDomain (MvPowerSeries (Fin 2) W₀) := NoZeroDivisors.to_isDomain _
  haveI : IsRegularLocalRing (MvPowerSeries (Fin 2) W₀) := IsRegularLocalRing.mvPowerSeries_fin W₀ 2
  have hdimA : ringKrullDim (MvPowerSeries (Fin 2) W₀) = ((2 + 1 : ℕ) : WithBot ℕ∞) :=
    MvPowerSeries.ringKrullDim_fin_eq_of_isDiscreteValuationRing W₀ 2
  have hmaxA : ∀ q : MvPowerSeries (Fin 2) W₀,
      q ∈ maximalIdeal (MvPowerSeries (Fin 2) W₀) ↔ constantCoeff q ∈ maximalIdeal W₀ := by
    intro q
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff,
      IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  have hxmem : C π - h ∈ maximalIdeal (MvPowerSeries (Fin 2) W₀) := by
    rw [hmaxA, hcc, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact hπunit
  have hxunit : ¬ IsUnit (C π - h) :=
    mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp hxmem)
  have hxsq : C π - h ∉ maximalIdeal (MvPowerSeries (Fin 2) W₀) ^ 2 := by
    intro hmem
    have hle : maximalIdeal (MvPowerSeries (Fin 2) W₀) ≤
        (maximalIdeal W₀).comap (constantCoeff : MvPowerSeries (Fin 2) W₀ →+* W₀) := by
      intro q hq
      rw [Ideal.mem_comap]
      exact (hmaxA q).mp hq
    have h2 : constantCoeff (C π - h) ∈ (maximalIdeal W₀) ^ 2 :=
      Ideal.le_comap_pow _ 2 (Ideal.pow_right_mono hle 2 hmem)
    rw [hcc, hπ, Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at h2
    obtain ⟨u, hu⟩ := h2
    apply hπunit
    have h1 : π * (u * π) = π * 1 := by
      rw [mul_one, mul_comm π (u * π), mul_assoc, ← pow_two, hu]
    have h1' : u * π = 1 := mul_left_cancel₀ hπ0 h1
    exact IsUnit.of_mul_eq_one u (by rw [mul_comm]; exact h1')
  have hxmin : ∀ p ∈ minimalPrimes (MvPowerSeries (Fin 2) W₀), C π - h ∉ p := by
    intro p hp
    have hpbot : p = ⊥ :=
      le_bot_iff.mp (hp.2 ⟨Ideal.isPrime_bot, le_rfl⟩ bot_le)
    rw [hpbot, Ideal.mem_bot]
    intro h0
    apply hπ0
    rw [← hcc, h0, map_zero]
  haveI : Nontrivial (MvPowerSeries (Fin 2) W₀ ⧸ Ideal.span {C π - h}) :=
    Ideal.Quotient.nontrivial_iff.mpr (Ideal.span_singleton_ne_top hxunit)
  haveI : IsLocalRing (MvPowerSeries (Fin 2) W₀ ⧸ Ideal.span {C π - h}) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk (Ideal.span {C π - h})) Ideal.Quotient.mk_surjective
  have hBreg : IsRegularLocalRing (MvPowerSeries (Fin 2) W₀ ⧸ Ideal.span {C π - h}) :=
    (IsRegularLocalRing.quotient_span_singleton_of_notMem_sq_of_forall_minimalPrimes_notMem
      (MvPowerSeries (Fin 2) W₀) hxmem hxsq hxmin).1
  have hBdim : ringKrullDim (MvPowerSeries (Fin 2) W₀ ⧸ Ideal.span {C π - h}) + 1 =
      ringKrullDim (MvPowerSeries (Fin 2) W₀) :=
    IsLocalRing.ringKrullDim_quotient_span_singleton_add_one_of_forall_minimalPrimes_notMem hxmem hxmin
  haveI : IsDomain (MvPowerSeries (Fin 2) W₀ ⧸ Ideal.span {C π - h}) :=
    IsRegularLocalRing.isDomain _

  have hψi : Function.Injective ψ := by
    refine (injective_iff_map_eq_zero ψ).mpr fun b hb => ?_
    by_contra hb0
    have hsucc := ringKrullDim_succ_le_of_surjective (ψ : _ →+* R) hψs
      (mem_nonZeroDivisors_of_ne_zero hb0) hb
    rw [hdim] at hsucc
    rw [hdimA] at hBdim
    have h3 : (2 : WithBot ℕ∞) + 1 + 1 ≤ ((2 + 1 : ℕ) : WithBot ℕ∞) := by
      rw [← hBdim]
      gcongr
    exact absurd h3 (by decide)

  let e' : (MvPowerSeries (Fin 2) W₀ ⧸ Ideal.span {C π - h}) ≃ₐ[W₀] R :=
    AlgEquiv.ofBijective ψ ⟨hψi, hψs⟩
  refine ⟨h, hh0, e'.symm, ?_, ?_⟩
  · rw [AlgEquiv.symm_apply_eq]
    show x₀ = ψ (Ideal.Quotient.mk (Ideal.span {C π - h}) (X 0))
    rw [hψmk, hφ0]
  · rw [AlgEquiv.symm_apply_eq]
    show x₁ = ψ (Ideal.Quotient.mk (Ideal.span {C π - h}) (X 1))
    rw [hψmk, hφ1]

end S_IsRegularLocalRing_exists_algEquiv_mvPowerSeries_quotient_span_C_sub_of_maximalIdeal_eq_span_pair
end P2MW
export P2MW.S_IsRegularLocalRing_exists_algEquiv_mvPowerSeries_quotient_span_C_sub_of_maximalIdeal_eq_span_pair (solution)
