-- Prove2me | solution 1 for IsLocalRing.HasseForm.isUnit_sum_map_mul_pow_of_forall_isUnit_sum_mul_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/ef88519f-7179-589d-a301-3065e1774682

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsLocalRing_HasseForm_isUnit_sum_map_mul_pow_of_forall_isUnit_sum_mul_pow

set_option autoImplicit false

p2m_open "IsLocalRing P2MW.S_IsLocalRing_HasseForm_isUnit_sum_map_mul_pow_of_forall_isUnit_sum_mul_pow.IsLocalRing"

namespace IsLocalRing
p2m_export "IsLocalRing" "ResidueField maximalIdeal residue_eq_zero_iff mem_maximalIdeal residue_ne_zero_iff_isUnit residue"
namespace HasseForm
p2m_open "IsLocalRing"

theorem intCast_pow_sub_intCast_mem (q : ℕ) [Fact q.Prime] {W : Type*} [CommRing W] [IsLocalRing W]
    (hq : (q : W) ∈ maximalIdeal W) (n : ℤ) : (n : W) ^ q - (n : W) ∈ maximalIdeal W := by
  have h : ((n ^ q - n : ℤ) : ZMod q) = 0 := by
    rw [Int.cast_sub, Int.cast_pow, ZMod.pow_card, sub_self]
  obtain ⟨k, hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mp h
  have : (n : W) ^ q - (n : W) = ((n ^ q - n : ℤ) : W) := by push_cast; ring
  rw [this, hk, Int.cast_mul, Int.cast_natCast]
  exact Ideal.mul_mem_right _ _ hq

end IsLocalRing.HasseForm

open IsLocalRing.HasseForm in
theorem solution
    (q : ℕ) [Fact q.Prime]
    {W₁ W₂ : Type*} [CommRing W₁] [IsLocalRing W₁] [CommRing W₂] [IsLocalRing W₂]
    (hq₁ : (q : W₁) ∈ maximalIdeal W₁)
    (ρ : W₁ →+* W₂) (hρ : ∀ x ∈ maximalIdeal W₁, ρ x ∈ maximalIdeal W₂)
    (e₀ : ℕ) (c : ℕ → W₁)
    (hunit : ∀ a b : W₁, (a ∉ maximalIdeal W₁ ∨ b ∉ maximalIdeal W₁) →
      a ^ q * b - a * b ^ q ∈ maximalIdeal W₁ →
        IsUnit (∑ i ∈ Finset.range (e₀ + 1), c i * a ^ i * b ^ (e₀ - i))) :
    ∀ a b : W₂, (a ∉ maximalIdeal W₂ ∨ b ∉ maximalIdeal W₂) →
      a ^ q * b - a * b ^ q ∈ maximalIdeal W₂ →
        IsUnit (∑ i ∈ Finset.range (e₀ + 1), ρ (c i) * a ^ i * b ^ (e₀ - i)) := by
  classical
  have hqp : q.Prime := Fact.out
  have hq₂ : (q : W₂) ∈ maximalIdeal W₂ := by simpa using hρ _ hq₁
  haveI : CharP (ResidueField W₂) q := by
    rw [CharP.charP_iff_prime_eq_zero hqp, ← map_natCast (residue W₂), residue_eq_zero_iff]; exact hq₂

  have hρunit : ∀ x : W₁, IsUnit x → residue W₂ (ρ x) ≠ 0 := fun x hx =>
    (residue_ne_zero_iff_isUnit _).mpr (hx.map ρ)
  intro a b hab hdir
  rw [← residue_ne_zero_iff_isUnit, map_sum]
  simp only [map_mul, map_pow]
  set r := residue W₂ with hr
  have hdir' : r a ^ q * r b = r a * r b ^ q := by
    rw [← sub_eq_zero, ← map_pow, ← map_pow, ← map_mul, ← map_mul, ← map_sub, hr, residue_eq_zero_iff]; exact hdir
  rcases hab with ha | hb
  ·
    have ha0 : r a ≠ 0 := by rw [hr, Ne, residue_eq_zero_iff]; exact ha
    set lam := r b / r a with hlam
    have hb' : r b = lam * r a := by rw [hlam, div_mul_cancel₀ _ ha0]
    have hlamq : lam ^ q = lam := by
      rw [hlam, div_pow, div_eq_div_iff (pow_ne_zero _ ha0) ha0]

      linear_combination (-1 : ResidueField W₂) * hdir'
    obtain ⟨n, hn⟩ := (mem_bot_iff_intCast q (ResidueField W₂)).mp
      ((Subfield.mem_bot_iff_pow_eq_self (ResidueField W₂) q).mpr hlamq)

    have hF := hunit 1 (n : W₁) (Or.inl (by rw [mem_maximalIdeal, mem_nonunits_iff, not_not]; exact isUnit_one))
      (by
        rw [one_pow, one_mul, one_mul]
        have := (maximalIdeal W₁).neg_mem (intCast_pow_sub_intCast_mem q hq₁ n)
        rwa [neg_sub] at this)
    have key : ∑ i ∈ Finset.range (e₀ + 1), r (ρ (c i)) * r a ^ i * r b ^ (e₀ - i) =
        r a ^ e₀ * r (ρ (∑ i ∈ Finset.range (e₀ + 1), c i * 1 ^ i * (n : W₁) ^ (e₀ - i))) := by
      rw [map_sum, map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hi' : i ≤ e₀ := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      simp only [map_mul, map_pow, map_intCast, one_pow, mul_one, hb', mul_pow]
      rw [← hn]
      have : r a ^ i * (r a) ^ (e₀ - i) = r a ^ e₀ := by rw [← pow_add, Nat.add_sub_cancel' hi']
      calc r (ρ (c i)) * r a ^ i * ((n : ResidueField W₂) ^ (e₀ - i) * r a ^ (e₀ - i))
          = (r a ^ i * r a ^ (e₀ - i)) * (r (ρ (c i)) * (n : ResidueField W₂) ^ (e₀ - i)) := by ring
        _ = r a ^ e₀ * (r (ρ (c i)) * (n : ResidueField W₂) ^ (e₀ - i)) := by rw [this]
    rw [key]
    exact mul_ne_zero (pow_ne_zero _ ha0) (hρunit _ hF)
  ·
    have hb0 : r b ≠ 0 := by rw [hr, Ne, residue_eq_zero_iff]; exact hb
    set mu := r a / r b with hmu
    have ha' : r a = mu * r b := by rw [hmu, div_mul_cancel₀ _ hb0]
    have hmuq : mu ^ q = mu := by
      rw [hmu, div_pow, div_eq_div_iff (pow_ne_zero _ hb0) hb0]
      linear_combination hdir'
    obtain ⟨m, hm⟩ := (mem_bot_iff_intCast q (ResidueField W₂)).mp
      ((Subfield.mem_bot_iff_pow_eq_self (ResidueField W₂) q).mpr hmuq)
    have hF := hunit (m : W₁) 1 (Or.inr (by rw [mem_maximalIdeal, mem_nonunits_iff, not_not]; exact isUnit_one))
      (by rw [one_pow, mul_one, mul_one]; exact intCast_pow_sub_intCast_mem q hq₁ m)
    have key : ∑ i ∈ Finset.range (e₀ + 1), r (ρ (c i)) * r a ^ i * r b ^ (e₀ - i) =
        r b ^ e₀ * r (ρ (∑ i ∈ Finset.range (e₀ + 1), c i * (m : W₁) ^ i * 1 ^ (e₀ - i))) := by
      rw [map_sum, map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hi' : i ≤ e₀ := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      simp only [map_mul, map_pow, map_intCast, one_pow, mul_one, ha', mul_pow]
      rw [← hm]
      have : r b ^ i * (r b) ^ (e₀ - i) = r b ^ e₀ := by rw [← pow_add, Nat.add_sub_cancel' hi']
      calc r (ρ (c i)) * ((m : ResidueField W₂) ^ i * r b ^ i) * r b ^ (e₀ - i)
          = (r b ^ i * r b ^ (e₀ - i)) * (r (ρ (c i)) * (m : ResidueField W₂) ^ i) := by ring
        _ = r b ^ e₀ * (r (ρ (c i)) * (m : ResidueField W₂) ^ i) := by rw [this]
    rw [key]
    exact mul_ne_zero (pow_ne_zero _ hb0) (hρunit _ hF)

end S_IsLocalRing_HasseForm_isUnit_sum_map_mul_pow_of_forall_isUnit_sum_mul_pow
end P2MW
export P2MW.S_IsLocalRing_HasseForm_isUnit_sum_map_mul_pow_of_forall_isUnit_sum_mul_pow (solution)
