-- Prove2me | solution 1 for ModularCurve.UVCrossingModel.exists_algHom_range_eq_fixedPoints_apply_U_apply_V_of_tangent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/cfce0e6e-49a1-5699-aa4f-0128eb95ccaa

import Mathlib
import Definitions.Def_ModularCurve_UVCrossingModel
import Theorems.Thm_ModularCurve_UVCrossingModel_exists_unit_eigen_of_tangent
import Theorems.Thm_ModularCurve_UVCrossingModel_exists_algEquiv_apply_U_eq_mul
import Theorems.Thm_ModularCurve_UVCrossingModel_exists_powMap_range_eq_fixedPoints
import Theorems.Thm_MvPowerSeries_algHom_ext_of_apply_X_mem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_UVCrossingModel_exists_algHom_range_eq_fixedPoints_apply_U_apply_V_of_tangent

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000

open ModularCurve ModularCurve.UVCrossingModel MvPowerSeries
namespace Ws30C3c
namespace FixSig

variable {Ô : Type*} [CommRing Ô]

theorem const_eq_algebraMap (π w : Ô) : const π w = algebraMap Ô (UVCrossingModel Ô π) w := by
  show Ideal.Quotient.mk (uvCrossingIdeal Ô π) (C w) = Ideal.Quotient.mk (uvCrossingIdeal Ô π) (algebraMap Ô _ w)
  rw [MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]

theorem rescale_X_eq (c : Fin 2 → Ô) (i : Fin 2) : rescale c (X i) = C (c i) * X i := by
  classical
  refine MvPowerSeries.ext fun n => ?_
  rw [coeff_rescale, coeff_C_mul, coeff_X]
  split_ifs with h
  · subst h
    simp only [Finsupp.prod_single_index, pow_zero, pow_one, mul_one]
  · rw [mul_zero, mul_zero]

theorem not_isUnit_mk_X (π : Ô) (hπu : ¬ IsUnit π) (i : Fin 2) : ¬ IsUnit (mk π (X i)) := by
  classical
  intro hu

  have hker : ∀ a ∈ uvCrossingIdeal Ô π, (Ideal.Quotient.mk (Ideal.span {π})).comp constantCoeff a = 0 := by
    intro a ha
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    have hP : constantCoeff (X 0 * X 1 - C π : MvPowerSeries (Fin 2) Ô) = -π := by
      rw [map_sub, map_mul, constantCoeff_X, zero_mul, constantCoeff_C, zero_sub]
    rw [RingHom.comp_apply, map_mul, hP, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mul_mem_left _ _ (Submodule.neg_mem _ (Ideal.mem_span_singleton_self π))
  let χ : UVCrossingModel Ô π →+* Ô ⧸ Ideal.span {π} :=
    Ideal.Quotient.lift (uvCrossingIdeal Ô π) ((Ideal.Quotient.mk (Ideal.span {π})).comp constantCoeff) hker
  have hχ : χ (mk π (X i)) = 0 := by
    show Ideal.Quotient.lift (uvCrossingIdeal Ô π) _ hker (Ideal.Quotient.mk _ (X i)) = 0
    rw [Ideal.Quotient.lift_mk, RingHom.comp_apply, constantCoeff_X, map_zero]
  have h0 : IsUnit (0 : Ô ⧸ Ideal.span {π}) := hχ ▸ hu.map χ
  rw [isUnit_zero_iff, Ideal.Quotient.zero_eq_one_iff, Ideal.span_singleton_eq_top] at h0
  exact hπu h0

section Complete

variable [IsLocalRing Ô] [IsAdicComplete (IsLocalRing.maximalIdeal Ô) Ô] (π : Ô) (hπu : ¬ IsUnit π)
  (hnil : ∃ k : ℕ, IsLocalRing.maximalIdeal Ô ^ k ≤ Ideal.span {π})

omit [IsAdicComplete (IsLocalRing.maximalIdeal Ô) Ô] in
include hπu in
theorem span_le_maximalIdeal : Ideal.span {π} ≤ IsLocalRing.maximalIdeal Ô := by
  rw [Ideal.span_le, Set.singleton_subset_iff]
  exact (IsLocalRing.mem_maximalIdeal π).mpr hπu

include hπu in

theorem sep : ∀ x : Ô, (∀ n : ℕ, π ^ n ∣ x) → x = 0 := by
  intro x hx
  refine IsHausdorff.haus (inferInstance : IsHausdorff (IsLocalRing.maximalIdeal Ô) Ô) x fun n => ?_
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
  obtain ⟨c, hc⟩ := hx n
  rw [hc]
  exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow ((IsLocalRing.mem_maximalIdeal π).mpr hπu) n)

include hπu hnil in

theorem precomplete : IsPrecomplete (Ideal.span {π}) Ô := by
  obtain ⟨k, hk⟩ := hnil
  have hk1 : 1 ≤ k := by
    by_contra h
    have : k = 0 := by omega
    rw [this, pow_zero, Ideal.one_eq_top, top_le_iff, Ideal.span_singleton_eq_top] at hk
    exact hπu hk
  have hle : ∀ m : ℕ, (Ideal.span {π} ^ m • ⊤ : Submodule Ô Ô) ≤ (IsLocalRing.maximalIdeal Ô ^ m • ⊤ : Submodule Ô Ô) :=
    fun m => Submodule.smul_mono_left (Ideal.pow_right_mono (span_le_maximalIdeal π hπu) m)
  have hle' : ∀ n : ℕ, (IsLocalRing.maximalIdeal Ô ^ (k * n) • ⊤ : Submodule Ô Ô) ≤ (Ideal.span {π} ^ n • ⊤ : Submodule Ô Ô) := by
    intro n
    apply Submodule.smul_mono_left
    rw [pow_mul]
    exact Ideal.pow_right_mono hk n
  refine ⟨fun {f} hf => ?_⟩

  have hg : ∀ {m n : ℕ}, m ≤ n → f (k * m) ≡ f (k * n) [SMOD (IsLocalRing.maximalIdeal Ô ^ m • ⊤ : Submodule Ô Ô)] := by
    intro m n hmn
    have h1 : f (k * m) ≡ f (k * n) [SMOD (Ideal.span {π} ^ (k * m) • ⊤ : Submodule Ô Ô)] :=
      hf (Nat.mul_le_mul_left k hmn)
    refine (h1.mono (hle _)).mono (Submodule.smul_mono_left (Ideal.pow_le_pow_right ?_))
    exact Nat.le_mul_of_pos_left m (by omega)
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (inferInstance : IsPrecomplete (IsLocalRing.maximalIdeal Ô) Ô) hg
  refine ⟨L, fun n => ?_⟩

  have h1 : f n ≡ f (k * (k * n)) [SMOD (Ideal.span {π} ^ n • ⊤ : Submodule Ô Ô)] := by
    apply hf
    calc n ≤ k * n := Nat.le_mul_of_pos_left n (by omega)
      _ ≤ k * (k * n) := Nat.le_mul_of_pos_left _ (by omega)
  have h2 : f (k * (k * n)) ≡ L [SMOD (Ideal.span {π} ^ n • ⊤ : Submodule Ô Ô)] := (hL (k * n)).mono (hle' n)
  exact h1.trans h2

end Complete

end Ws30C3c.FixSig

open Ws30C3c.FixSig

theorem solution
    {Ô : Type*} [CommRing Ô] [IsLocalRing Ô] [IsAdicComplete (IsLocalRing.maximalIdeal Ô) Ô]
    (π : Ô) (hπu : ¬IsUnit π) (hπ : π ∈ nonZeroDivisors Ô)
    (hnil : ∃ k : ℕ, IsLocalRing.maximalIdeal Ô ^ k ≤ Ideal.span {π})
    [IsLocalRing (UVCrossingModel Ô π)]
    [IsAdicComplete (IsLocalRing.maximalIdeal (UVCrossingModel Ô π)) (UVCrossingModel Ô π)]
    (e : ℕ) (he : IsUnit ((e : ℕ) : Ô)) (ζ ζ' : Ô) (hζ : ζ * ζ' = 1) (hζe : ζ ^ e = 1)
    (hreg : ∀ m : ℕ, 0 < m → m < e → ζ ^ m - 1 ∈ nonZeroDivisors Ô)
    (σ : UVCrossingModel Ô π ≃ₐ[Ô] UVCrossingModel Ô π) (hord : ∀ z, σ^[e] z = z)
    (htanU : σ (U π) - const π ζ * U π ∈ IsLocalRing.maximalIdeal (UVCrossingModel Ô π) ^ 2)
    (htanV : σ (V π) - const π ζ' * V π ∈ IsLocalRing.maximalIdeal (UVCrossingModel Ô π) ^ 2) :
    ∃ (ι : UVCrossingModel Ô (π ^ e) →ₐ[Ô] UVCrossingModel Ô π) (γ : (UVCrossingModel Ô π)ˣ),
      Function.Injective ι ∧ (∀ z : UVCrossingModel Ô π, σ z = z ↔ z ∈ Set.range ι) ∧
      (γ : UVCrossingModel Ô π) - 1 ∈ IsLocalRing.maximalIdeal (UVCrossingModel Ô π) ∧
      ι (U (π ^ e)) = ((γ : UVCrossingModel Ô π) * U π) ^ e ∧
      ι (V (π ^ e)) = ((↑γ⁻¹ : UVCrossingModel Ô π) * V π) ^ e := by
  classical

  haveI : IsPrecomplete (Ideal.span {π}) Ô := precomplete π hπu hnil
  have hsep := sep π hπu
  have he0 : e ≠ 0 := by
    rintro rfl
    simp only [Nat.cast_zero, isUnit_zero_iff] at he
    exact zero_ne_one he

  obtain ⟨γ, hγ1, hγU, hγV⟩ := ModularCurve.UVCrossingModel.exists_unit_eigen_of_tangent π hπu hπ hnil e he ζ ζ' hζ hζe σ
    hord htanU htanV
  obtain ⟨τ, hτU, hτV⟩ := ModularCurve.UVCrossingModel.exists_algEquiv_apply_U_eq_mul π hπu γ
  obtain ⟨θ, δ, hθ, hinj, hδ, hfix⟩ :=
    ModularCurve.UVCrossingModel.exists_powMap_range_eq_fixedPoints π hsep e he0 ζ ζ' hζe hζ hreg

  set R := UVCrossingModel Ô π
  let σ' : R →ₐ[Ô] R := (τ.symm : R →ₐ[Ô] R).comp ((σ : R →ₐ[Ô] R).comp (τ : R →ₐ[Ô] R))
  have hσ' : ∀ z, σ' z = τ.symm (σ (τ z)) := fun z => rfl
  have hconst : ∀ w : Ô, const π w = algebraMap Ô R w := const_eq_algebraMap π
  have hσ'U : σ' (U π) = const π ζ * U π := by
    rw [hσ', hτU, hγU, map_mul, hconst, AlgEquiv.commutes, ← hτU, AlgEquiv.symm_apply_apply]
  have hσ'V : σ' (V π) = const π ζ' * V π := by
    rw [hσ', hτV, hγV, map_mul, hconst, AlgEquiv.commutes, ← hτV, AlgEquiv.symm_apply_apply]
  have hδX : ∀ i : Fin 2, δ (mk π (X i)) = const π (![ζ, ζ'] i) * mk π (X i) := by
    intro i
    rw [hδ, rescale_X_eq, map_mul]
    rfl

  have hXmem : ∀ i : Fin 2, mk π (X i) ∈ IsLocalRing.maximalIdeal R :=
    fun i => (IsLocalRing.mem_maximalIdeal _).mpr (not_isUnit_mk_X π hπu i)
  let φ : MvPowerSeries (Fin 2) Ô →ₐ[Ô] R := σ'.comp (Ideal.Quotient.mkₐ Ô (uvCrossingIdeal Ô π))
  let ψ : MvPowerSeries (Fin 2) Ô →ₐ[Ô] R := (δ : R →ₐ[Ô] R).comp (Ideal.Quotient.mkₐ Ô (uvCrossingIdeal Ô π))
  have hφX : ∀ i : Fin 2, φ (X i) = const π (![ζ, ζ'] i) * mk π (X i) := by
    intro i
    fin_cases i
    · exact hσ'U
    · exact hσ'V
  have hψX : ∀ i : Fin 2, ψ (X i) = const π (![ζ, ζ'] i) * mk π (X i) := fun i => hδX i
  have hφψ : φ = ψ := by
    refine MvPowerSeries.algHom_ext_of_apply_X_mem (IsLocalRing.maximalIdeal R) φ ψ (fun i => ?_) (fun i => ?_)
    · rw [hφX]; exact Ideal.mul_mem_left _ _ (hXmem i)
    · rw [hφX, hψX]
  have hagree : ∀ w : R, τ.symm (σ (τ w)) = δ w := by
    intro w
    obtain ⟨F, rfl⟩ := mk_surjective π w
    have := congrArg (fun χ => χ F) hφψ
    exact this

  have hθX : ∀ i : Fin 2, θ (mk (π ^ e) (X i)) = mk π (X i) ^ e := by
    intro i
    rw [hθ, MvPowerSeries.expand_X, map_pow]

  refine ⟨(τ : R →ₐ[Ô] R).comp θ, γ, τ.injective.comp hinj, fun z => ?_, hγ1, ?_, ?_⟩
  · constructor
    · intro hz
      have h1 : δ (τ.symm z) = τ.symm z := by rw [← hagree, AlgEquiv.apply_symm_apply, hz]
      obtain ⟨y, hy⟩ := (hfix _).mp h1
      exact ⟨y, by show τ (θ y) = z; rw [hy, AlgEquiv.apply_symm_apply]⟩
    · rintro ⟨y, rfl⟩
      have h1 : δ (θ y) = θ y := (hfix _).mpr ⟨y, rfl⟩
      have h2 := hagree (θ y)
      rw [h1] at h2
      have h3 := congrArg τ h2
      rw [AlgEquiv.apply_symm_apply] at h3
      exact h3
  · show τ (θ (U (π ^ e))) = _
    rw [show U (π ^ e) = mk (π ^ e) (X 0) from rfl, hθX, map_pow, show mk π (X 0) = U π from rfl, hτU]
  · show τ (θ (V (π ^ e))) = _
    rw [show V (π ^ e) = mk (π ^ e) (X 1) from rfl, hθX, map_pow, show mk π (X 1) = V π from rfl, hτV]

end S_ModularCurve_UVCrossingModel_exists_algHom_range_eq_fixedPoints_apply_U_apply_V_of_tangent
end P2MW
export P2MW.S_ModularCurve_UVCrossingModel_exists_algHom_range_eq_fixedPoints_apply_U_apply_V_of_tangent (solution)
