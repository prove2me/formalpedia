-- Prove2me | solution 1 for ModularCurve.UVCrossingModel.exists_unit_eigen_of_tangent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/cb75677e-6316-5716-aa5b-649d5e364517

import Mathlib
import Definitions.Def_ModularCurve_UVCrossingModel
import Theorems.Thm_ModularCurve_UVCrossingModel_exists_ringEquiv_quotient_span_U_powerSeries
import Theorems.Thm_ModularCurve_UVCrossingModel_const_mem_nonZeroDivisors
import Theorems.Thm_ModularCurve_UVCrossingModel_U_mem_nonZeroDivisors
import Theorems.Thm_ModularCurve_UVCrossingModel_U_mul_V
import Theorems.Thm_HenselianLocalRing_of_isAdicComplete_maximalIdeal
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_UVCrossingModel_exists_unit_eigen_of_tangent

set_option autoImplicit false
set_option maxHeartbeats 3200000

open ModularCurve ModularCurve.UVCrossingModel IsLocalRing

noncomputable section

namespace LinGamma

section NZD

variable {A : Type*} [CommRing A]

theorem X_mul_eq_zero {g : PowerSeries A} (h : PowerSeries.X * g = 0) : g = 0 := by
  ext n
  have := congrArg (PowerSeries.coeff (n + 1)) h
  rwa [PowerSeries.coeff_succ_X_mul, map_zero] at this

theorem X_pow_mul_eq_zero (k : ℕ) {g : PowerSeries A} (h : PowerSeries.X ^ k * g = 0) : g = 0 := by
  induction k generalizing g with
  | zero => simpa using h
  | succ k ih =>
    rw [pow_succ', mul_assoc] at h
    exact ih (X_mul_eq_zero h)

theorem mem_nonZeroDivisors_of_coeff (f : PowerSeries A) (h0 : IsNilpotent (PowerSeries.constantCoeff f))
    (h1 : IsUnit (PowerSeries.coeff 1 f)) : f ∈ nonZeroDivisors (PowerSeries A) := by
  obtain ⟨k, hk⟩ := h0
  set a := PowerSeries.constantCoeff f with ha
  set w : PowerSeries A := PowerSeries.mk fun n => PowerSeries.coeff (n + 1) f with hw
  have hf : f = PowerSeries.X * w + PowerSeries.C a := PowerSeries.eq_X_mul_shift_add_const f
  have hwu : IsUnit w := by
    rw [PowerSeries.isUnit_iff_constantCoeff, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, hw,
      PowerSeries.coeff_mk]
    exact h1
  have key : ∀ g : PowerSeries A, g * f = 0 → g = 0 := by
    intro g hg
    have e1 : (PowerSeries.X * w) * g = -PowerSeries.C a * g := by
      have e : PowerSeries.X * w = f - PowerSeries.C a := by rw [hf]; ring
      rw [e, sub_mul, mul_comm f g, hg, zero_sub, neg_mul]
    have step : ∀ j : ℕ, (PowerSeries.X * w) ^ j * g = (-PowerSeries.C a) ^ j * g := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
        calc (PowerSeries.X * w) ^ (j + 1) * g = (PowerSeries.X * w) ^ j * ((PowerSeries.X * w) * g) := by ring
          _ = (PowerSeries.X * w) ^ j * (-PowerSeries.C a * g) := by rw [e1]
          _ = -PowerSeries.C a * ((PowerSeries.X * w) ^ j * g) := by ring
          _ = -PowerSeries.C a * ((-PowerSeries.C a) ^ j * g) := by rw [ih]
          _ = (-PowerSeries.C a) ^ (j + 1) * g := by ring
    have h2 : (PowerSeries.X * w) ^ k * g = 0 := by
      rw [step k, neg_pow, ← map_pow, hk, map_zero, mul_zero, zero_mul]
    rw [mul_pow, mul_comm (PowerSeries.X ^ k), mul_assoc] at h2

    have h3 : PowerSeries.X ^ k * g = 0 := (hwu.pow k).mul_right_eq_zero.mp h2
    exact X_pow_mul_eq_zero k h3
  exact mem_nonZeroDivisors_iff.mpr ⟨fun g hg => key g (by rw [mul_comm]; exact hg), key⟩

end NZD

section Branch

variable {Ô : Type*} [CommRing Ô] [IsLocalRing Ô] {π : Ô}

theorem nontrivial_quot (hπu : ¬IsUnit π) : Nontrivial (Ô ⧸ Ideal.span {π}) :=
  ⟨⟨0, 1, fun h => hπu (by
    have h1 : (Ideal.Quotient.mk (Ideal.span {π})) 1 = 0 := by rw [map_one]; exact h.symm
    rw [Ideal.Quotient.eq_zero_iff_mem] at h1
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp h1
    exact IsUnit.of_mul_eq_one a (by rw [mul_comm]; exact ha))⟩⟩

theorem isUnit_of_sub_one_mem [IsLocalRing (UVCrossingModel Ô π)] {a : UVCrossingModel Ô π}
    (h : a - 1 ∈ maximalIdeal (UVCrossingModel Ô π)) : IsUnit a := by
  by_contra hu
  have ha : a ∈ maximalIdeal _ := (mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hu)
  have h1 : (1 : UVCrossingModel Ô π) ∈ maximalIdeal _ := by
    have e : (1 : UVCrossingModel Ô π) = a - (a - 1) := by ring
    rw [e]; exact Ideal.sub_mem _ ha h
  exact (maximalIdeal.isMaximal _).ne_top (Ideal.eq_top_of_isUnit_mem _ h1 isUnit_one)

theorem mul_sub_one_mem [IsLocalRing (UVCrossingModel Ô π)] {a b : UVCrossingModel Ô π}
    (ha : a - 1 ∈ maximalIdeal (UVCrossingModel Ô π)) (hb : b - 1 ∈ maximalIdeal (UVCrossingModel Ô π)) :
    a * b - 1 ∈ maximalIdeal (UVCrossingModel Ô π) := by
  have e : a * b - 1 = (a - 1) * b + (b - 1) := by ring
  rw [e]; exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ ha) hb

theorem prod_sub_one_mem [IsLocalRing (UVCrossingModel Ô π)] (s : Finset ℕ) (f : ℕ → UVCrossingModel Ô π)
    (h : ∀ i ∈ s, f i - 1 ∈ maximalIdeal (UVCrossingModel Ô π)) :
    (∏ i ∈ s, f i) - 1 ∈ maximalIdeal (UVCrossingModel Ô π) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s has ih =>
    rw [Finset.prod_insert has]
    exact mul_sub_one_mem (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

variable (π) in

theorem branch_facts (hπu : ¬IsUnit π) (hnil : ∃ k : ℕ, maximalIdeal Ô ^ k ≤ Ideal.span {π})
    [IsLocalRing (UVCrossingModel Ô π)] :
    ∃ (ρ : UVCrossingModel Ô π →+* PowerSeries (Ô ⧸ Ideal.span {π})),
      ρ (V π) = PowerSeries.X ∧ ρ (U π) = 0 ∧
      (∀ w, ρ (const π w) = PowerSeries.C (Ideal.Quotient.mk (Ideal.span {π}) w)) ∧
      Ideal.Quotient.mk (Ideal.span {π}) π = 0 ∧
      (∀ s, ρ s = 0 → s ∈ Ideal.span {U π}) ∧
      (∀ r ∈ maximalIdeal (UVCrossingModel Ô π), IsNilpotent (PowerSeries.constantCoeff (ρ r))) ∧
      (∀ r ∈ maximalIdeal (UVCrossingModel Ô π) ^ 2,
        PowerSeries.constantCoeff (ρ r) ∈ nilradical (Ô ⧸ Ideal.span {π}) ∧
          PowerSeries.coeff 1 (ρ r) ∈ nilradical (Ô ⧸ Ideal.span {π})) := by
  classical
  obtain ⟨ε, hV, hU, hC⟩ := exists_ringEquiv_quotient_span_U_powerSeries π
  haveI hnt : Nontrivial (Ô ⧸ Ideal.span {π}) := nontrivial_quot hπu
  let ρ : UVCrossingModel Ô π →+* PowerSeries (Ô ⧸ Ideal.span {π}) :=
    ε.toRingHom.comp (Ideal.Quotient.mk (Ideal.span {U π}))
  have ρsurj : Function.Surjective ρ := ε.surjective.comp Ideal.Quotient.mk_surjective

  have hnilA : ∀ a : Ô ⧸ Ideal.span {π}, ¬IsUnit a → IsNilpotent a := by
    intro a ha
    obtain ⟨k, hk⟩ := hnil
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
    have hx : x ∈ maximalIdeal Ô := by
      rw [mem_maximalIdeal, mem_nonunits_iff]
      exact fun hu => ha (hu.map _)
    refine ⟨k, ?_⟩
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact hk (Ideal.pow_mem_pow hx k)

  have hcc : ∀ r ∈ maximalIdeal (UVCrossingModel Ô π), ¬IsUnit (PowerSeries.constantCoeff (ρ r)) := by
    intro r hr hu
    let τ : UVCrossingModel Ô π →+* (Ô ⧸ Ideal.span {π}) := PowerSeries.constantCoeff.comp ρ
    have hτ : Function.Surjective τ := by
      intro a
      obtain ⟨z, hz⟩ := ρsurj (PowerSeries.C a)
      exact ⟨z, by show PowerSeries.constantCoeff (ρ z) = a; rw [hz, PowerSeries.constantCoeff_C]⟩
    obtain ⟨t, ht⟩ := hτ ((hu.unit⁻¹ : (Ô ⧸ Ideal.span {π})ˣ) : Ô ⧸ Ideal.span {π})
    have h1 : τ (1 - r * t) = 0 := by
      rw [map_sub, map_one, map_mul, ht]
      show 1 - PowerSeries.constantCoeff (ρ r) * ↑hu.unit⁻¹ = 0
      rw [IsUnit.mul_val_inv, sub_self]
    have h2 : IsUnit (1 - r * t) := by
      by_contra hnu
      have hm : r * t ∈ maximalIdeal _ := Ideal.mul_mem_right _ _ hr
      have h3 : (1 : UVCrossingModel Ô π) ∈ maximalIdeal _ := by
        have e : (1 : UVCrossingModel Ô π) = (1 - r * t) + r * t := by ring
        rw [e]; exact Ideal.add_mem _ ((mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hnu)) hm
      exact (maximalIdeal.isMaximal _).ne_top (Ideal.eq_top_of_isUnit_mem _ h3 isUnit_one)
    exact not_isUnit_zero (h1 ▸ h2.map τ)
  refine ⟨ρ, hV, hU, hC, ?_, ?_, ?_, ?_⟩
  · exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self π)
  · intro s hs
    have h1 : ε (Ideal.Quotient.mk (Ideal.span {U π}) s) = 0 := hs
    rw [ε.map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem] at h1
    exact h1
  · intro r hr
    exact hnilA _ (hcc r hr)
  · intro r hr
    rw [pow_two] at hr
    refine Submodule.mul_induction_on hr ?_ ?_
    · intro a ha b hb
      have ha' : PowerSeries.constantCoeff (ρ a) ∈ nilradical _ := mem_nilradical.mpr (hnilA _ (hcc a ha))
      have hb' : PowerSeries.constantCoeff (ρ b) ∈ nilradical _ := mem_nilradical.mpr (hnilA _ (hcc b hb))
      rw [map_mul]
      constructor
      · rw [map_mul]; exact Ideal.mul_mem_left _ _ hb'
      · rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_succ, Finset.Nat.antidiagonal_zero, Finset.sum_singleton]
        refine Ideal.add_mem _ ?_ ?_
        · rw [PowerSeries.coeff_zero_eq_constantCoeff]; exact Ideal.mul_mem_right _ _ ha'
        · rw [PowerSeries.coeff_zero_eq_constantCoeff]; exact Ideal.mul_mem_left _ _ hb'
    · intro a b ha hb
      rw [map_add, map_add, map_add]
      exact ⟨Ideal.add_mem _ ha.1 hb.1, Ideal.add_mem _ ha.2 hb.2⟩

theorem mem_span_U (hπu : ¬IsUnit π) (hnil : ∃ k : ℕ, maximalIdeal Ô ^ k ≤ Ideal.span {π})
    [IsLocalRing (UVCrossingModel Ô π)] {ζ' : Ô} (hζ' : IsUnit ζ') (s s' : UVCrossingModel Ô π)
    (hss' : s * s' = const π π) (hs' : s' - const π ζ' * V π ∈ maximalIdeal (UVCrossingModel Ô π) ^ 2) :
    s ∈ Ideal.span {U π} := by
  haveI : Nontrivial (Ô ⧸ Ideal.span {π}) := nontrivial_quot hπu
  obtain ⟨ρ, ρV, ρU, ρC, κπ, hker, hm1, hm2⟩ := branch_facts π hπu hnil
  apply hker

  have hf : ρ s' ∈ nonZeroDivisors (PowerSeries (Ô ⧸ Ideal.span {π})) := by
    have e : ρ s' = PowerSeries.C (Ideal.Quotient.mk (Ideal.span {π}) ζ') * PowerSeries.X
        + ρ (s' - const π ζ' * V π) := by
      rw [map_sub, map_mul, ρC, ρV]; ring
    obtain ⟨h0, h1⟩ := hm2 _ hs'
    refine mem_nonZeroDivisors_of_coeff _ ?_ ?_
    · rw [e, map_add, map_mul, PowerSeries.constantCoeff_X, mul_zero, zero_add]
      exact mem_nilradical.mp h0
    · rw [e, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_one_X, mul_one]
      exact IsNilpotent.isUnit_add_left_of_commute (mem_nilradical.mp h1) (hζ'.map _) (Commute.all _ _)
  have h0 : ρ s * ρ s' = 0 := by rw [← map_mul, hss', ρC, κπ, map_zero]
  exact (mem_nonZeroDivisors_iff.mp hf).2 _ h0

theorem V_not_mem_sq (hπu : ¬IsUnit π) (hnil : ∃ k : ℕ, maximalIdeal Ô ^ k ≤ Ideal.span {π})
    [IsLocalRing (UVCrossingModel Ô π)] : V π ∉ maximalIdeal (UVCrossingModel Ô π) ^ 2 := by
  haveI : Nontrivial (Ô ⧸ Ideal.span {π}) := nontrivial_quot hπu
  obtain ⟨ρ, ρV, ρU, ρC, κπ, hker, hm1, hm2⟩ := branch_facts π hπu hnil
  intro h
  have h1 := (hm2 _ h).2
  rw [ρV, PowerSeries.coeff_one_X] at h1
  obtain ⟨k, hk⟩ := mem_nilradical.mp h1
  rw [one_pow] at hk
  exact one_ne_zero hk

end Branch

section Main

variable {Ô : Type*} [CommRing Ô] [IsLocalRing Ô] {π : Ô}

theorem const_eq_algebraMap (w : Ô) : const π w = algebraMap Ô (UVCrossingModel Ô π) w := by
  show Ideal.Quotient.mk (uvCrossingIdeal Ô π) (MvPowerSeries.C w) = _
  rw [MvPowerSeries.c_eq_algebraMap, Ideal.Quotient.mk_algebraMap]

theorem crossingSwap_U : crossingSwap π (U π) = V π := by
  show UVCrossingModel.mk π (uvSwapEquiv (MvPowerSeries.X 0)) = UVCrossingModel.mk π (MvPowerSeries.X 1)
  rw [uvSwapEquiv_X_zero]

theorem crossingSwap_V : crossingSwap π (V π) = U π := by
  show UVCrossingModel.mk π (uvSwapEquiv (MvPowerSeries.X 1)) = UVCrossingModel.mk π (MvPowerSeries.X 0)
  rw [uvSwapEquiv_X_one]

theorem crossingSwap_const (w : Ô) : crossingSwap π (const π w) = const π w := by
  show UVCrossingModel.mk π (uvSwapEquiv (MvPowerSeries.C w)) = UVCrossingModel.mk π (MvPowerSeries.C w)
  rw [uvSwapEquiv_C]

theorem map_mem_maximalIdeal [IsLocalRing (UVCrossingModel Ô π)]
    (f : UVCrossingModel Ô π ≃+* UVCrossingModel Ô π) {r : UVCrossingModel Ô π}
    (hr : r ∈ maximalIdeal (UVCrossingModel Ô π)) : f r ∈ maximalIdeal (UVCrossingModel Ô π) := by
  rw [mem_maximalIdeal, mem_nonunits_iff] at hr ⊢
  intro hu
  exact hr (by simpa using hu.map f.symm)

theorem map_mem_maximalIdeal_sq [IsLocalRing (UVCrossingModel Ô π)]
    (f : UVCrossingModel Ô π ≃+* UVCrossingModel Ô π) {r : UVCrossingModel Ô π}
    (hr : r ∈ maximalIdeal (UVCrossingModel Ô π) ^ 2) : f r ∈ maximalIdeal (UVCrossingModel Ô π) ^ 2 := by
  rw [pow_two] at hr ⊢
  refine Submodule.mul_induction_on hr ?_ ?_
  · intro a ha b hb
    rw [map_mul]
    exact Ideal.mul_mem_mul (map_mem_maximalIdeal f ha) (map_mem_maximalIdeal f hb)
  · intro a b ha hb
    rw [map_add]
    exact Ideal.add_mem _ ha hb

theorem iterate_map_mul (σ : UVCrossingModel Ô π ≃ₐ[Ô] UVCrossingModel Ô π) (i : ℕ) (x y : UVCrossingModel Ô π) :
    σ^[i] (x * y) = σ^[i] x * σ^[i] y := by
  induction i with
  | zero => rfl
  | succ i ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', Function.iterate_succ_apply', ih, map_mul]

theorem iterate_map_const (σ : UVCrossingModel Ô π ≃ₐ[Ô] UVCrossingModel Ô π) (i : ℕ) (w : Ô) :
    σ^[i] (const π w) = const π w := by
  induction i with
  | zero => rfl
  | succ i ih => rw [Function.iterate_succ_apply', ih, const_eq_algebraMap, AlgEquiv.commutes]

theorem iterate_sub_one_mem [IsLocalRing (UVCrossingModel Ô π)] (σ : UVCrossingModel Ô π ≃ₐ[Ô] UVCrossingModel Ô π)
    (i : ℕ) {c : UVCrossingModel Ô π} (hc : c - 1 ∈ maximalIdeal (UVCrossingModel Ô π)) :
    σ^[i] c - 1 ∈ maximalIdeal (UVCrossingModel Ô π) := by
  induction i with
  | zero => exact hc
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    have e : σ (σ^[i] c) - 1 = σ (σ^[i] c - 1) := by rw [map_sub, map_one]
    rw [e]
    exact map_mem_maximalIdeal σ.toRingEquiv ih

theorem main (hπu : ¬IsUnit π) (hπ : π ∈ nonZeroDivisors Ô)
    (hnil : ∃ k : ℕ, maximalIdeal Ô ^ k ≤ Ideal.span {π})
    [IsLocalRing (UVCrossingModel Ô π)]
    [IsAdicComplete (maximalIdeal (UVCrossingModel Ô π)) (UVCrossingModel Ô π)]
    (e : ℕ) (he : IsUnit ((e : ℕ) : Ô)) (ζ ζ' : Ô) (hζ : ζ * ζ' = 1) (hζe : ζ ^ e = 1)
    (σ : UVCrossingModel Ô π ≃ₐ[Ô] UVCrossingModel Ô π) (hord : ∀ z, σ^[e] z = z)
    (htanU : σ (U π) - const π ζ * U π ∈ maximalIdeal (UVCrossingModel Ô π) ^ 2)
    (htanV : σ (V π) - const π ζ' * V π ∈ maximalIdeal (UVCrossingModel Ô π) ^ 2) :
    ∃ γ : (UVCrossingModel Ô π)ˣ, (γ : UVCrossingModel Ô π) - 1 ∈ maximalIdeal (UVCrossingModel Ô π) ∧
      σ ((γ : UVCrossingModel Ô π) * U π) = const π ζ * ((γ : UVCrossingModel Ô π) * U π) ∧
      σ ((↑γ⁻¹ : UVCrossingModel Ô π) * V π) = const π ζ' * ((↑γ⁻¹ : UVCrossingModel Ô π) * V π) := by
  classical

  have hζu : IsUnit ζ := IsUnit.of_mul_eq_one ζ' hζ
  have hζ'u : IsUnit ζ' := IsUnit.of_mul_eq_one ζ (by rw [mul_comm]; exact hζ)
  have hconst : ∀ w, σ (const π w) = const π w := fun w => by
    rw [const_eq_algebraMap, AlgEquiv.commutes]
  have hcζ : const π ζ * const π ζ' = 1 := by
    rw [const_eq_algebraMap, const_eq_algebraMap, ← map_mul, hζ, map_one]
  have hUV : U π * V π = const π π := U_mul_V π
  have hπR : const π π ∈ nonZeroDivisors (UVCrossingModel Ô π) := const_mem_nonZeroDivisors hπ
  have hUR : U π ∈ nonZeroDivisors (UVCrossingModel Ô π) := U_mem_nonZeroDivisors hπ
  have he0 : 0 < e := by
    rcases Nat.eq_zero_or_pos e with h | h
    · exfalso; subst h
      rw [Nat.cast_zero, isUnit_zero_iff] at he
      exact zero_ne_one he
    · exact h

  obtain ⟨α, hα⟩ : ∃ α, α * U π = σ (U π) :=
    Ideal.mem_span_singleton'.mp (mem_span_U hπu hnil hζ'u (σ (U π)) (σ (V π))
      (by rw [← map_mul, hUV, hconst]) htanV)

  obtain ⟨β', hβ'⟩ : ∃ β', β' * U π = crossingSwap π (σ (V π)) := by
    refine Ideal.mem_span_singleton'.mp (mem_span_U hπu hnil hζu (crossingSwap π (σ (V π)))
      (crossingSwap π (σ (U π))) ?_ ?_)
    · rw [← map_mul, ← map_mul, mul_comm, hUV, hconst, crossingSwap_const]
    · have e1 : crossingSwap π (σ (U π)) - const π ζ * V π = crossingSwap π (σ (U π) - const π ζ * U π) := by
        rw [map_sub, map_mul, crossingSwap_const, crossingSwap_U]
      rw [e1]
      exact map_mem_maximalIdeal_sq (crossingSwap π) htanU
  obtain ⟨β, hβ⟩ : ∃ β, β * V π = σ (V π) := by
    refine ⟨(crossingSwap π).symm β', ?_⟩
    have h1 := congrArg (crossingSwap π).symm hβ'
    rw [map_mul, RingEquiv.symm_apply_apply] at h1
    have h2 : (crossingSwap π).symm (U π) = V π := by
      rw [RingEquiv.symm_apply_eq]; exact crossingSwap_V.symm
    rw [h2] at h1
    exact h1

  have hαβ : α * β = 1 := by
    have h0 : σ (U π) * σ (V π) = const π π := by rw [← map_mul, hUV, hconst]
    rw [← hα, ← hβ] at h0
    have h1 : (α * β - 1) * const π π = 0 := by
      rw [sub_mul, one_mul, ← hUV, sub_eq_zero]
      calc α * β * (U π * V π) = (α * U π) * (β * V π) := by ring
        _ = U π * V π := by rw [h0, hUV]
    exact sub_eq_zero.mp ((mem_nonZeroDivisors_iff.mp hπR).2 _ h1)
  have hαu : IsUnit α := IsUnit.of_mul_eq_one β hαβ

  have hαζ : α - const π ζ ∈ maximalIdeal (UVCrossingModel Ô π) := by
    by_contra hne
    have hu : IsUnit (α - const π ζ) := by
      rwa [mem_maximalIdeal, mem_nonunits_iff, not_not] at hne
    have h1 : (α - const π ζ) * U π ∈ maximalIdeal (UVCrossingModel Ô π) ^ 2 := by
      rw [sub_mul, hα]; exact htanU
    have h2 : U π ∈ maximalIdeal (UVCrossingModel Ô π) ^ 2 := by
      have h3 := Ideal.mul_mem_left _ (↑(hu.unit⁻¹) : UVCrossingModel Ô π) h1
      rwa [← mul_assoc, IsUnit.val_inv_mul, one_mul] at h3
    have h3 : V π ∈ maximalIdeal (UVCrossingModel Ô π) ^ 2 := by
      rw [← crossingSwap_U]; exact map_mem_maximalIdeal_sq (crossingSwap π) h2
    exact V_not_mem_sq hπu hnil h3

  have hiter : ∀ k : ℕ, σ^[k] (U π) = (∏ i ∈ Finset.range k, σ^[i] α) * U π := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Function.iterate_succ_apply', ih, map_mul, ← hα, map_prod, Finset.prod_range_succ' (fun i => σ^[i] α)]
      simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
      ring
  have hN : (∏ i ∈ Finset.range e, σ^[i] α) = 1 := by
    have h1 := hord (U π)
    rw [hiter] at h1
    have h2 : ((∏ i ∈ Finset.range e, σ^[i] α) - 1) * U π = 0 := by rw [sub_mul, one_mul, h1, sub_self]
    exact sub_eq_zero.mp ((mem_nonZeroDivisors_iff.mp hUR).2 _ h2)

  haveI : HenselianLocalRing (UVCrossingModel Ô π) := HenselianLocalRing.of_isAdicComplete_maximalIdeal _
  set αi : UVCrossingModel Ô π := ↑(hαu.unit⁻¹) with hαi
  have hααi : α * αi = 1 := hαu.mul_val_inv
  set c := const π ζ * αi with hc
  have hcα : c * α = const π ζ := by rw [hc, mul_assoc, mul_comm αi, hααi, mul_one]
  have hc1 : c - 1 ∈ maximalIdeal (UVCrossingModel Ô π) := by
    have e1 : c - 1 = -(αi * (α - const π ζ)) := by
      rw [mul_sub, mul_comm αi α, hααi, hc]; ring
    rw [e1]; exact (Ideal.neg_mem_iff _).mpr (Ideal.mul_mem_left _ _ hαζ)
  set P : ℕ → UVCrossingModel Ô π := fun k => ∏ i ∈ Finset.range k, σ^[i] c with hP
  have hP1 : ∀ k, P k - 1 ∈ maximalIdeal (UVCrossingModel Ô π) := fun k =>
    prod_sub_one_mem _ _ fun i _ => iterate_sub_one_mem σ i hc1
  have hσP : ∀ k, σ (P k) * c = P (k + 1) := by
    intro k
    simp only [hP]
    rw [map_prod, Finset.prod_range_succ' (fun i => σ^[i] c)]
    simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
  have hPe : P e = 1 := by
    have h1 : P e * ∏ i ∈ Finset.range e, σ^[i] α = ∏ i ∈ Finset.range e, σ^[i] (const π ζ) := by
      simp only [hP]
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun i _ => by rw [← iterate_map_mul, hcα]
    rw [hN, mul_one] at h1
    rw [h1]
    simp only [iterate_map_const]
    rw [Finset.prod_const, Finset.card_range, const_eq_algebraMap, ← map_pow, hζe, map_one]
  set Q := ∏ k ∈ Finset.range e, P k with hQ
  have hQ1 : Q - 1 ∈ maximalIdeal (UVCrossingModel Ô π) := prod_sub_one_mem _ _ fun k _ => hP1 k
  have hQu : IsUnit Q := isUnit_of_sub_one_mem hQ1
  have hσQ : σ Q * c ^ e = Q := by
    have hce : c ^ e = ∏ _k ∈ Finset.range e, c := by rw [Finset.prod_const, Finset.card_range]
    simp only [hQ]
    rw [map_prod, hce, ← Finset.prod_mul_distrib]
    simp only [hσP]
    have h1 := Finset.prod_range_succ P e
    have h2 := Finset.prod_range_succ' P e
    rw [hPe, mul_one] at h1
    have hP0 : P 0 = 1 := by simp [hP]
    rw [hP0, mul_one] at h2
    rw [← h2, h1]
  have heR : IsUnit ((e : ℕ) : UVCrossingModel Ô π) := by
    have h := he.map (algebraMap Ô (UVCrossingModel Ô π)); rwa [map_natCast] at h
  set q : UVCrossingModel Ô π := ↑(hQu.unit⁻¹) with hq
  have hQq : Q * q = 1 := hQu.mul_val_inv
  have hq1 : q - 1 ∈ maximalIdeal (UVCrossingModel Ô π) := by
    have e1 : q - 1 = -(q * (Q - 1)) := by rw [mul_sub, mul_comm q Q, hQq]; ring
    rw [e1]; exact (Ideal.neg_mem_iff _).mpr (Ideal.mul_mem_left _ _ hQ1)

  obtain ⟨γ, hγ, hγ1⟩ := HenselianLocalRing.is_henselian (Polynomial.X ^ e - Polynomial.C q)
    (Polynomial.monic_X_pow_sub_C q he0.ne') 1
    (by
      rw [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C, one_pow]
      have e1 : (1 : UVCrossingModel Ô π) - q = -(q - 1) := by ring
      rw [e1]; exact (Ideal.neg_mem_iff _).mpr hq1)
    (by
      rw [Polynomial.derivative_sub, Polynomial.derivative_X_pow, Polynomial.derivative_C, sub_zero,
        Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, one_pow, mul_one]
      exact heR)
  have hγe : γ ^ e = q := by
    have h := hγ
    rw [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
      sub_eq_zero] at h
    exact h
  have hγu : IsUnit γ := isUnit_of_sub_one_mem hγ1

  have hσq : σ q = c ^ e * q := by
    have h1 : σ Q * σ q = 1 := by rw [← map_mul, hQq, map_one]
    have hσQu : IsUnit (σ Q) := IsUnit.of_mul_eq_one _ h1
    apply hσQu.mul_left_cancel
    rw [h1]
    calc (1 : UVCrossingModel Ô π) = Q * q := hQq.symm
      _ = σ Q * c ^ e * q := by rw [hσQ]
      _ = σ Q * (c ^ e * q) := by ring
  have hroot1 : (Polynomial.X ^ e - Polynomial.C (c ^ e * q)).IsRoot (σ γ) := by
    rw [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
      ← map_pow, hγe, hσq, sub_self]
  have hroot2 : (Polynomial.X ^ e - Polynomial.C (c ^ e * q)).IsRoot (c * γ) := by
    rw [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C, mul_pow,
      hγe, sub_self]
  have hdiff : c * γ - σ γ ∈ maximalIdeal (UVCrossingModel Ô π) := by
    have e1 : c * γ - σ γ = (c * γ - 1) - (σ γ - 1) := by ring
    rw [e1]
    refine Ideal.sub_mem _ (mul_sub_one_mem hc1 hγ1) ?_
    have e2 : σ γ - 1 = σ (γ - 1) := by rw [map_sub, map_one]
    rw [e2]; exact map_mem_maximalIdeal σ.toRingEquiv hγ1
  have hder : IsUnit ((Polynomial.X ^ e - Polynomial.C (c ^ e * q)).derivative.eval (σ γ)) := by
    rw [Polynomial.derivative_sub, Polynomial.derivative_X_pow, Polynomial.derivative_C, sub_zero,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    exact heR.mul ((hγu.map σ).pow _)
  have hnu : ¬IsUnit (σ γ - c * γ) := by
    have hm : σ γ - c * γ ∈ maximalIdeal (UVCrossingModel Ô π) := by
      rw [← neg_sub]; exact (Ideal.neg_mem_iff _).mpr hdiff
    exact mem_nonunits_iff.mp ((mem_maximalIdeal _).mp hm)
  have hσγ : σ γ = c * γ := IsLocalRing.eq_of_eval_eq_zero_of_not_isUnit_sub hroot1 hroot2 hnu hder

  set γi : UVCrossingModel Ô π := ↑(hγu.unit⁻¹) with hγi
  have hγγi : γ * γi = 1 := hγu.mul_val_inv
  refine ⟨hγu.unit, by rw [IsUnit.unit_spec]; exact hγ1, ?_, ?_⟩
  · rw [IsUnit.unit_spec, map_mul, hσγ, ← hα]
    calc c * γ * (α * U π) = (c * α) * (γ * U π) := by ring
      _ = const π ζ * (γ * U π) := by rw [hcα]
  · show σ (γi * V π) = const π ζ' * (γi * V π)
    have hσγi : σ γi * (c * γ) = 1 := by rw [← hσγ, ← map_mul, mul_comm, hγγi, map_one]
    have hcγu : IsUnit (c * γ) := IsUnit.of_mul_eq_one _ (by rw [mul_comm]; exact hσγi)
    have hβαi : β = αi := by
      calc β = (αi * α) * β := by rw [mul_comm αi, hααi, one_mul]
        _ = αi * (α * β) := by ring
        _ = αi := by rw [hαβ, mul_one]
    apply hcγu.mul_left_cancel
    rw [map_mul, ← hβ]
    calc c * γ * (σ γi * (β * V π)) = (σ γi * (c * γ)) * β * V π := by ring
      _ = αi * V π := by rw [hσγi, one_mul, hβαi]
      _ = (const π ζ * const π ζ') * (γ * γi) * (αi * V π) := by rw [hcζ, hγγi, one_mul, one_mul]
      _ = c * γ * (const π ζ' * (γi * V π)) := by rw [hc]; ring

end Main

end LinGamma

end

theorem solution
    {Ô : Type*} [CommRing Ô] [IsLocalRing Ô] (π : Ô) (hπu : ¬IsUnit π) (hπ : π ∈ nonZeroDivisors Ô)
    (hnil : ∃ k : ℕ, IsLocalRing.maximalIdeal Ô ^ k ≤ Ideal.span {π})
    [IsLocalRing (UVCrossingModel Ô π)]
    [IsAdicComplete (IsLocalRing.maximalIdeal (UVCrossingModel Ô π)) (UVCrossingModel Ô π)]
    (e : ℕ) (he : IsUnit ((e : ℕ) : Ô)) (ζ ζ' : Ô) (hζ : ζ * ζ' = 1) (hζe : ζ ^ e = 1)
    (σ : UVCrossingModel Ô π ≃ₐ[Ô] UVCrossingModel Ô π) (hord : ∀ z, σ^[e] z = z)
    (htanU : σ (U π) - const π ζ * U π ∈ IsLocalRing.maximalIdeal (UVCrossingModel Ô π) ^ 2)
    (htanV : σ (V π) - const π ζ' * V π ∈ IsLocalRing.maximalIdeal (UVCrossingModel Ô π) ^ 2) :
    ∃ γ : (UVCrossingModel Ô π)ˣ, (γ : UVCrossingModel Ô π) - 1 ∈ IsLocalRing.maximalIdeal (UVCrossingModel Ô π) ∧
      σ ((γ : UVCrossingModel Ô π) * U π) = const π ζ * ((γ : UVCrossingModel Ô π) * U π) ∧
      σ ((↑γ⁻¹ : UVCrossingModel Ô π) * V π) = const π ζ' * ((↑γ⁻¹ : UVCrossingModel Ô π) * V π) :=
  LinGamma.main hπu hπ hnil e he ζ ζ' hζ hζe σ hord htanU htanV

end S_ModularCurve_UVCrossingModel_exists_unit_eigen_of_tangent
end P2MW
export P2MW.S_ModularCurve_UVCrossingModel_exists_unit_eigen_of_tangent (solution)
