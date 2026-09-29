-- Prove2me | solution 1 for IsDiscreteValuationRing.finprod_smul_sub_one_mem_maximalIdeal_pow_of_sub_one_mem_pow_herbrand_of_prime_card
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/73d11bd9-96db-5d52-84d4-49e2f957de44

import Mathlib
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_Mathlib_RingTheory_Valuation_UpperRamificationGroup
import Definitions.Def_Mathlib_RingTheory_Invariant_FixedSubringLocal

import Theorems.Thm_prod_one_add_smul_eq_one_add_finsum_add_finprod_add_finsum_smul_of_prime_card
import Theorems.Thm_IsDiscreteValuationRing_finsum_smul_mem_maximalIdeal_pow_of_lowerRamificationGroup_eq_top_of_eq_bot
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsDiscreteValuationRing_finprod_smul_sub_one_mem_maximalIdeal_pow_of_sub_one_mem_pow_herbrand_of_prime_card

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxSynthPendingDepth 3
open IsDedekindDomain NumberField
open scoped NumberField.PlaceDecomp

namespace IsDiscreteValuationRing
p2m_export "IsDiscreteValuationRing" "maximalIdeal finsum_smul_mem_maximalIdeal_pow_of_lowerRamificationGroup_eq_top_of_eq_bot"
namespace XCNormDvrSol
p2m_open "IsDiscreteValuationRing"

open IsLocalRing

theorem prod_mem_pow_mul_card {B ι : Type*} [CommRing B] (I : Ideal B) (k : ℕ) (s : Finset ι) (f : ι → B)
    (h : ∀ i ∈ s, f i ∈ I ^ k) : ∏ i ∈ s, f i ∈ I ^ (k * s.card) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha, Nat.mul_succ, add_comm, pow_add]
    exact Ideal.mul_mem_mul (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem herbrand_arith {ℓ t n : ℕ} (hℓ : 2 ≤ ℓ) :
    n ≤ ((if n ≤ t then n else t + ℓ * (n - t)) + (t + 1) * (ℓ - 1)) / ℓ ∧
      n ≤ (if n ≤ t then n else t + ℓ * (n - t)) := by
  obtain ⟨k, rfl⟩ : ∃ k, ℓ = k + 1 := ⟨ℓ - 1, by omega⟩
  have hk : 1 ≤ k := by omega
  simp only [Nat.add_sub_cancel]
  split_ifs with hnt
  · refine ⟨(Nat.le_div_iff_mul_le (by omega)).mpr ?_, le_rfl⟩
    have : n * k ≤ (t + 1) * k := Nat.mul_le_mul_right k (by omega)
    nlinarith
  · push Not at hnt
    refine ⟨(Nat.le_div_iff_mul_le (by omega)).mpr ?_, ?_⟩
    · have h1 : t + (k + 1) * (n - t) + (t + 1) * k = n * (k + 1) + k := by
        have : n - t + t = n := Nat.sub_add_cancel hnt.le
        nlinarith [this]
      omega
    · nlinarith [Nat.sub_add_cancel hnt.le]

theorem herbrand_arith_succ {ℓ t n : ℕ} (hℓ : 2 ≤ ℓ) :
    n + 1 ≤ ((if n ≤ t then n else t + ℓ * (n - t)) + 1 + (t + 1) * (ℓ - 1)) / ℓ := by
  obtain ⟨k, rfl⟩ : ∃ k, ℓ = k + 1 := ⟨ℓ - 1, by omega⟩
  have hk : 1 ≤ k := by omega
  simp only [Nat.add_sub_cancel]
  refine (Nat.le_div_iff_mul_le (by omega)).mpr ?_
  split_ifs with hnt
  · have : (n + 1) * k ≤ (t + 1) * k := Nat.mul_le_mul_right k (by omega)
    nlinarith
  · push Not at hnt
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hnt
    rw [show t + d + 1 - t = d + 1 by omega]
    nlinarith

end IsDiscreteValuationRing.XCNormDvrSol

open IsDiscreteValuationRing.XCNormDvrSol IsLocalRing in
theorem solution
    {B : Type*} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    {G : Type*} [Group G] [Finite G] [MulSemiringAction G B] [FaithfulSMul G B]
    [(IsLocalRing.maximalIdeal B).LiesOver (IsLocalRing.maximalIdeal (FixedPoints.subring B G))]
    [Algebra.IsSeparable
      (FixedPoints.subring B G ⧸ IsLocalRing.maximalIdeal (FixedPoints.subring B G))
      (B ⧸ IsLocalRing.maximalIdeal B)]
    (hℓ : (Nat.card G).Prime) (t : ℕ)
    (ht : IsLocalRing.lowerRamificationGroup B G t = ⊤) (ht' : IsLocalRing.lowerRamificationGroup B G (t + 1) = ⊥)
    (n : ℕ) (b : B) :
    (b - 1 ∈ IsLocalRing.maximalIdeal B ^ (if n ≤ t then n else t + Nat.card G * (n - t)) →
        (∏ᶠ σ : G, σ • b) - 1 ∈ IsLocalRing.maximalIdeal B ^ (Nat.card G * n)) ∧
    (b - 1 ∈ IsLocalRing.maximalIdeal B ^ ((if n ≤ t then n else t + Nat.card G * (n - t)) + 1) →
        (∏ᶠ σ : G, σ • b) - 1 ∈ IsLocalRing.maximalIdeal B ^ (Nat.card G * (n + 1))) := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  have hℓ2 : 2 ≤ Nat.card G := hℓ.two_le
  have hℓcard : Fintype.card G = Nat.card G := (Nat.card_eq_fintype_card).symm

  have core : ∀ (m k : ℕ) (γ : B), γ ∈ maximalIdeal B ^ m →
      k ≤ (m + (t + 1) * (Nat.card G - 1)) / Nat.card G → k ≤ m →
      (∏ᶠ σ : G, (1 + σ • γ)) - 1 ∈ maximalIdeal B ^ (Nat.card G * k) := by
    intro m k γ hγ hk1 hk2
    obtain ⟨δ, hδ, hexp⟩ := prod_one_add_smul_eq_one_add_finsum_add_finprod_add_finsum_smul_of_prime_card hℓ γ
    rw [hexp, show (1 : B) + ∑ᶠ σ : G, σ • γ + ∏ᶠ σ : G, σ • γ + ∑ᶠ σ : G, σ • δ - 1 =
      ∑ᶠ σ : G, σ • γ + ∏ᶠ σ : G, σ • γ + ∑ᶠ σ : G, σ • δ by ring]

    have hσγ : ∀ σ : G, σ • γ ∈ maximalIdeal B ^ m := fun σ => by
      have h := (Ideal.smul_mem_pointwise_smul_iff (a := σ)).mpr hγ
      rwa [IsLocalRing.pointwise_smul_maximalIdeal_pow] at h

    have hδm : δ ∈ maximalIdeal B ^ (2 * m) := by
      refine (Ideal.span_le.mpr ?_) hδ
      rintro x ⟨σ₁, σ₂, -, rfl⟩
      rw [two_mul, pow_add]
      exact Ideal.mul_mem_mul (hσγ σ₁) (hσγ σ₂)
    refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_
    ·
      exact Ideal.pow_le_pow_right (Nat.mul_le_mul_left _ hk1)
        (IsDiscreteValuationRing.finsum_smul_mem_maximalIdeal_pow_of_lowerRamificationGroup_eq_top_of_eq_bot t ht ht' m γ hγ)
    ·
      rw [finprod_eq_prod_of_fintype]
      have h := prod_mem_pow_mul_card (maximalIdeal B) m Finset.univ (fun σ : G => σ • γ) fun σ _ => hσγ σ
      rw [Finset.card_univ, hℓcard] at h
      exact Ideal.pow_le_pow_right (by rw [mul_comm]; exact Nat.mul_le_mul_right _ hk2) h
    ·
      refine Ideal.pow_le_pow_right (Nat.mul_le_mul_left _ (hk1.trans ?_))
        (IsDiscreteValuationRing.finsum_smul_mem_maximalIdeal_pow_of_lowerRamificationGroup_eq_top_of_eq_bot t ht ht' (2 * m) δ hδm)
      exact Nat.div_le_div_right (by omega)
  have hb1 : (∏ᶠ σ : G, σ • b) = ∏ᶠ σ : G, (1 + σ • (b - 1)) :=
    finprod_congr fun σ => by conv_lhs => rw [show b = 1 + (b - 1) by ring]; rw [smul_add, smul_one]
  constructor
  · intro hb
    obtain ⟨h1, h2⟩ := herbrand_arith (ℓ := Nat.card G) (t := t) (n := n) hℓ2
    rw [hb1]
    exact core _ n (b - 1) hb h1 h2
  · intro hb
    have h1 := herbrand_arith_succ (ℓ := Nat.card G) (t := t) (n := n) hℓ2
    have h2 : n + 1 ≤ (if n ≤ t then n else t + Nat.card G * (n - t)) + 1 := by
      have := (herbrand_arith (ℓ := Nat.card G) (t := t) (n := n) hℓ2).2; omega
    rw [hb1]
    exact core _ (n + 1) (b - 1) hb h1 h2

end S_IsDiscreteValuationRing_finprod_smul_sub_one_mem_maximalIdeal_pow_of_sub_one_mem_pow_herbrand_of_prime_card
end P2MW
export P2MW.S_IsDiscreteValuationRing_finprod_smul_sub_one_mem_maximalIdeal_pow_of_sub_one_mem_pow_herbrand_of_prime_card (solution)
