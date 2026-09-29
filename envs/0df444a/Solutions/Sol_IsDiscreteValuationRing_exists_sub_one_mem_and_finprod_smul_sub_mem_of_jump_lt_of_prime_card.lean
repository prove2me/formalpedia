-- Prove2me | solution 1 for IsDiscreteValuationRing.exists_sub_one_mem_and_finprod_smul_sub_mem_of_jump_lt_of_prime_card
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/7075a972-0f12-50db-a28d-9323c25d8ba8

import Mathlib
import Definitions.Def_Mathlib_RingTheory_Valuation_UpperRamificationGroup
import Definitions.Def_Mathlib_RingTheory_Invariant_FixedSubringLocal
import Theorems.Thm_prod_one_add_smul_eq_one_add_finsum_add_finprod_add_finsum_smul_of_prime_card
import Theorems.Thm_IsDiscreteValuationRing_finsum_smul_mem_maximalIdeal_pow_of_lowerRamificationGroup_eq_top_of_eq_bot
import Theorems.Thm_IsDiscreteValuationRing_exists_finsum_smul_eq_of_mem_maximalIdeal_pow_of_lowerRamificationGroup_eq_top_of_eq_bot
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsDiscreteValuationRing_exists_sub_one_mem_and_finprod_smul_sub_mem_of_jump_lt_of_prime_card

set_option autoImplicit false

namespace Ws45
namespace S2

open IsLocalRing
open scoped Pointwise

variable {B : Type*} [CommRing B] [IsLocalRing B] {G : Type*} [Group G] [MulSemiringAction G B]

theorem prod_mem_pow {ι : Type*} (I : Ideal B) (s : Finset ι) (f : ι → B) (hf : ∀ i ∈ s, f i ∈ I) :
    ∏ i ∈ s, f i ∈ I ^ s.card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha, pow_succ']
    exact Ideal.mul_mem_mul (hf a (Finset.mem_insert_self a s)) (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

theorem smul_mem_maximalIdeal_pow {k : ℕ} (σ : G) {x : B} (hx : x ∈ maximalIdeal B ^ k) : σ • x ∈ maximalIdeal B ^ k := by
  rw [← pointwise_smul_maximalIdeal_pow (R := B) σ k]
  exact Ideal.smul_mem_pointwise_smul σ x _ hx

end Ws45.S2

theorem solution
    {B : Type*} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    {G : Type*} [Group G] [Finite G] [MulSemiringAction G B] [FaithfulSMul G B]
    [(IsLocalRing.maximalIdeal B).LiesOver (IsLocalRing.maximalIdeal (FixedPoints.subring B G))]
    [Algebra.IsSeparable
      (FixedPoints.subring B G ⧸ IsLocalRing.maximalIdeal (FixedPoints.subring B G))
      (B ⧸ IsLocalRing.maximalIdeal B)]
    (hℓ : (Nat.card G).Prime)
    (t : ℕ) (ht : IsLocalRing.lowerRamificationGroup B G t = ⊤)
    (ht' : IsLocalRing.lowerRamificationGroup B G (t + 1) = ⊥)
    (n : ℕ) (hn : t < n) (a : FixedPoints.subring B G)
    (ha : (a : B) - 1 ∈ IsLocalRing.maximalIdeal B ^ (Nat.card G * n)) :
    ∃ b : B, b - 1 ∈ IsLocalRing.maximalIdeal B ^ (t + Nat.card G * (n - t)) ∧
      (∏ᶠ σ : G, σ • b) - a ∈ IsLocalRing.maximalIdeal B ^ (Nat.card G * (n + 1)) := by
  classical
  haveI := Fintype.ofFinite G
  set ℓ := Nat.card G with hℓdef
  have hℓ2 : 2 ≤ ℓ := hℓ.two_le
  have htn : t ≤ n := hn.le
  set ψ := t + ℓ * (n - t) with hψ

  have hmul : 2 * (n - t) ≤ ℓ * (n - t) := Nat.mul_le_mul_right _ hℓ2
  have hψn : n + 1 ≤ ψ := by omega
  have hr : (ψ + (t + 1) * (ℓ - 1)) / ℓ = n := by
    have : ψ + (t + 1) * (ℓ - 1) = ℓ * n + (ℓ - 1) := by
      rw [hψ]
      zify [htn, (by omega : 1 ≤ ℓ)]
      ring
    rw [this, Nat.add_comm, Nat.add_mul_div_left _ _ (by omega : 0 < ℓ), Nat.div_eq_of_lt (by omega : ℓ - 1 < ℓ), zero_add]
  have hr2 : n + 1 ≤ (2 * ψ + (t + 1) * (ℓ - 1)) / ℓ := by
    rw [Nat.le_div_iff_mul_le (by omega : 0 < ℓ)]
    have hnt : 1 ≤ ℓ * (n - t) + t := by nlinarith
    have : 2 * ψ + (t + 1) * (ℓ - 1) = ℓ * (n + 1) + (ℓ * (n - t) + t - 1) := by
      rw [hψ]
      zify [htn, (by omega : 1 ≤ ℓ), hnt]
      ring
    rw [this, mul_comm]
    exact Nat.le_add_right _ _

  have hcG : ∀ σ : G, σ • ((a : B) - 1) = (a : B) - 1 := fun σ => by
    rw [smul_sub, smul_one, a.2 σ]
  have hc : (a : B) - 1 ∈ IsLocalRing.maximalIdeal B ^ (ℓ * ((ψ + (t + 1) * (ℓ - 1)) / ℓ)) := by
    rw [hr]; exact ha
  obtain ⟨y, hy, hyTr⟩ :=
    IsDiscreteValuationRing.exists_finsum_smul_eq_of_mem_maximalIdeal_pow_of_lowerRamificationGroup_eq_top_of_eq_bot
      t ht ht' ψ ((a : B) - 1) hcG hc

  obtain ⟨δ, hδ, hexp⟩ := prod_one_add_smul_eq_one_add_finsum_add_finprod_add_finsum_smul_of_prime_card (B := B) (G := G) hℓ y
  refine ⟨1 + y, by rw [add_sub_cancel_left]; exact hy, ?_⟩

  have hb : ∏ᶠ σ : G, σ • (1 + y) = ∏ᶠ σ : G, (1 + σ • y) :=
    finprod_congr fun σ => by rw [smul_add, smul_one]
  have hkey : (∏ᶠ σ : G, σ • (1 + y)) - a = ∏ᶠ σ : G, σ • y + ∑ᶠ σ : G, σ • δ := by
    rw [hb, hexp, hyTr]; ring
  rw [hkey]
  refine Ideal.add_mem _ ?_ ?_
  ·
    rw [finprod_eq_prod_of_fintype]
    have h1 := Ws45.S2.prod_mem_pow (IsLocalRing.maximalIdeal B ^ ψ) (Finset.univ : Finset G) (fun σ => σ • y)
      fun σ _ => Ws45.S2.smul_mem_maximalIdeal_pow σ hy
    have hcardu : (Finset.univ : Finset G).card = ℓ := by rw [Finset.card_univ, hℓdef, Nat.card_eq_fintype_card]
    rw [← pow_mul, hcardu] at h1
    exact Ideal.pow_le_pow_right (by nlinarith) h1
  ·
    have hδ2 : δ ∈ IsLocalRing.maximalIdeal B ^ (2 * ψ) := by
      refine (Ideal.span_le.2 ?_) hδ
      rintro x ⟨σ₁, σ₂, -, rfl⟩
      rw [two_mul, pow_add]
      exact Ideal.mul_mem_mul (Ws45.S2.smul_mem_maximalIdeal_pow σ₁ hy) (Ws45.S2.smul_mem_maximalIdeal_pow σ₂ hy)
    have h2 := IsDiscreteValuationRing.finsum_smul_mem_maximalIdeal_pow_of_lowerRamificationGroup_eq_top_of_eq_bot
      t ht ht' (2 * ψ) δ hδ2
    exact Ideal.pow_le_pow_right (Nat.mul_le_mul_left _ hr2) h2

end S_IsDiscreteValuationRing_exists_sub_one_mem_and_finprod_smul_sub_mem_of_jump_lt_of_prime_card
end P2MW
export P2MW.S_IsDiscreteValuationRing_exists_sub_one_mem_and_finprod_smul_sub_mem_of_jump_lt_of_prime_card (solution)
