-- Prove2me | solution 1 for MvPowerSeries.exists_ringEquiv_quotient_quotient_span_C_of_maximalIdeal_eq_span
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/8c37a207-83f6-5c09-b5ce-4d30a694936d

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvPowerSeries_exists_ringEquiv_quotient_quotient_span_C_of_maximalIdeal_eq_span

set_option autoImplicit false

universe u v

open MvPowerSeries

theorem solution
    {W : Type u} [CommRing W] [IsLocalRing W] (π : W) (hπ : IsLocalRing.maximalIdeal W = Ideal.span {π})
    {σ : Type v} (g : MvPowerSeries σ W) :
    ∃ e : ((MvPowerSeries σ W ⧸ Ideal.span {g}) ⧸
          Ideal.span {Ideal.Quotient.mk (Ideal.span {g}) (C π)}) ≃+*
        (MvPowerSeries σ (IsLocalRing.ResidueField W) ⧸ Ideal.span {MvPowerSeries.map (IsLocalRing.residue W) g}),
      ∀ p : MvPowerSeries σ W,
        e (Ideal.Quotient.mk _ (Ideal.Quotient.mk (Ideal.span {g}) p)) =
          Ideal.Quotient.mk _ (MvPowerSeries.map (IsLocalRing.residue W) p) := by
  classical

  set φ : MvPowerSeries σ W →+* MvPowerSeries σ (IsLocalRing.ResidueField W) :=
    MvPowerSeries.map (IsLocalRing.residue W) with hφ
  have hφsurj : Function.Surjective φ := by
    intro q
    refine ⟨fun n => Function.surjInv Ideal.Quotient.mk_surjective (MvPowerSeries.coeff n q), ?_⟩
    ext n
    rw [hφ, MvPowerSeries.coeff_map]
    exact Function.surjInv_eq Ideal.Quotient.mk_surjective _
  have hkerφ : ∀ p : MvPowerSeries σ W, φ p = 0 → ∃ h : MvPowerSeries σ W, p = C π * h := by
    intro p hp
    have hc : ∀ n : σ →₀ ℕ, ∃ h : W, MvPowerSeries.coeff n p = π * h := by
      intro n
      have h0 : IsLocalRing.residue W (MvPowerSeries.coeff n p) = 0 := by
        rw [← MvPowerSeries.coeff_map, ← hφ, hp, MvPowerSeries.coeff_zero]
      rw [IsLocalRing.residue_eq_zero_iff, hπ, Ideal.mem_span_singleton'] at h0
      obtain ⟨a, ha⟩ := h0
      exact ⟨a, by rw [← ha, mul_comm]⟩
    choose h hh using hc
    refine ⟨h, ?_⟩
    ext n
    rw [MvPowerSeries.coeff_C_mul, hh]
    rfl
  have hφC : φ (C π) = 0 := by
    rw [hφ, MvPowerSeries.map_C, (IsLocalRing.residue_eq_zero_iff π).mpr (by rw [hπ]; exact Ideal.mem_span_singleton_self π),
      map_zero]

  let J : Ideal (MvPowerSeries σ W) := Ideal.span {g}
  let K : Ideal (MvPowerSeries σ W ⧸ J) := Ideal.span {Ideal.Quotient.mk J (C π)}
  let Ibar : Ideal (MvPowerSeries σ (IsLocalRing.ResidueField W)) := Ideal.span {φ g}
  let ψ : MvPowerSeries σ W →+* MvPowerSeries σ (IsLocalRing.ResidueField W) ⧸ Ibar := (Ideal.Quotient.mk Ibar).comp φ
  have hψ : ∀ p, ψ p = Ideal.Quotient.mk Ibar (φ p) := fun p => rfl
  have hψsurj : Function.Surjective ψ := Ideal.Quotient.mk_surjective.comp hφsurj
  have hψJ : ∀ a ∈ J, ψ a = 0 := by
    intro a ha
    obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [hψ, map_mul, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
  let ψ₁ : MvPowerSeries σ W ⧸ J →+* MvPowerSeries σ (IsLocalRing.ResidueField W) ⧸ Ibar := Ideal.Quotient.lift J ψ hψJ
  have hψ₁ : ∀ p, ψ₁ (Ideal.Quotient.mk J p) = ψ p := fun p => Ideal.Quotient.lift_mk J ψ hψJ
  have hψ₁K : ∀ a ∈ K, ψ₁ a = 0 := by
    intro a ha
    obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [map_mul, hψ₁, hψ, hφC, map_zero, mul_zero]
  let ψ₂ : (MvPowerSeries σ W ⧸ J) ⧸ K →+* MvPowerSeries σ (IsLocalRing.ResidueField W) ⧸ Ibar :=
    Ideal.Quotient.lift K ψ₁ hψ₁K
  have hψ₂ : ∀ p, ψ₂ (Ideal.Quotient.mk K (Ideal.Quotient.mk J p)) = ψ p := fun p => by
    show Ideal.Quotient.lift K ψ₁ hψ₁K (Ideal.Quotient.mk K (Ideal.Quotient.mk J p)) = ψ p
    rw [Ideal.Quotient.lift_mk, hψ₁]
  have hψ₂surj : Function.Surjective ψ₂ := by
    intro t
    obtain ⟨p, rfl⟩ := hψsurj t
    exact ⟨Ideal.Quotient.mk K (Ideal.Quotient.mk J p), hψ₂ p⟩
  have hψ₂inj : Function.Injective ψ₂ := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨x₁, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x₁
    rw [hψ₂, hψ, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton'] at hx
    obtain ⟨a, ha⟩ := hx
    obtain ⟨q, rfl⟩ := hφsurj a
    obtain ⟨h, hh⟩ := hkerφ (p - q * g) (by rw [map_sub, map_mul, ← ha, sub_self])
    rw [Ideal.Quotient.eq_zero_iff_mem]
    have hp : Ideal.Quotient.mk J p = Ideal.Quotient.mk J (C π) * Ideal.Quotient.mk J h := by
      rw [← map_mul, Ideal.Quotient.eq]
      exact Ideal.mem_span_singleton'.mpr ⟨q, by linear_combination (-1 : MvPowerSeries σ W) * hh⟩
    rw [hp]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  refine ⟨RingEquiv.ofBijective ψ₂ ⟨hψ₂inj, hψ₂surj⟩, fun p => ?_⟩
  rw [RingEquiv.ofBijective_apply, hψ₂, hψ]

end S_MvPowerSeries_exists_ringEquiv_quotient_quotient_span_C_of_maximalIdeal_eq_span
end P2MW
export P2MW.S_MvPowerSeries_exists_ringEquiv_quotient_quotient_span_C_of_maximalIdeal_eq_span (solution)
