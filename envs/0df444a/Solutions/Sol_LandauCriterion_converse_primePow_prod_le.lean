-- Prove2me | solution 1 for LandauCriterion.converse_primePow_prod_le
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-03T17:55:03.790187+00:00
-- url     : https://prove2.me/submissions/69dc3bb5-12a4-4d0d-9f55-c21a8a468df1

import Mathlib
import Definitions.Def_LandauExplore_landauLocal
import Definitions.Def_LandauFunction_landau

open Finset LandauExplore LandauFunction

theorem solution {n : ℕ} {t : Finset ℕ}
    (hf : ∃ f : ℕ → ℕ, (∀ q ∈ t, (f q).Prime ∧ ∃ k : ℕ, 1 ≤ k ∧ q = (f q) ^ k) ∧ Set.InjOn f t)
    (hsum : ∑ q ∈ t, q ≤ n) : ∏ q ∈ t, q ≤ landauLocal n := by
  rcases hf with ⟨f, hf, hf_inj⟩

  -- Each q ∈ t is ≥ 2
  have h_ge_2 : ∀ q ∈ t, 2 ≤ q := by
    intro q hq
    have h := hf q hq
    rcases h.2 with ⟨k, hk, hq_eq⟩
    have hp : (f q).Prime := h.1
    have h2 : 2 ≤ f q := Nat.Prime.two_le hp
    have h1 : 1 ≤ f q := Nat.le_of_lt (Nat.lt_of_lt_of_le (by norm_num) h2)
    have h_le_pow : f q ≤ (f q) ^ k := by
      calc
        f q = (f q) ^ 1 := by rw [Nat.pow_one]
        _ ≤ (f q) ^ k := pow_le_pow_right' h1 hk
    rw [hq_eq]
    exact le_trans h2 h_le_pow

  -- Pairwise coprime
  have h_pairwise : Set.Pairwise t (Nat.Coprime.onFun id) := by
    intro q₁ hq₁ q₂ hq₂ hne
    have h1 := hf q₁ hq₁
    have h2 := hf q₂ hq₂
    rcases h1.2 with ⟨k₁, hk₁, hq₁_eq⟩
    rcases h2.2 with ⟨k₂, hk₂, hq₂_eq⟩
    have hp1 : (f q₁).Prime := h1.1
    have hp2 : (f q₂).Prime := h2.1
    have hfne : f q₁ ≠ f q₂ := fun h => hne (hf_inj hq₁ hq₂ h)
    rw [hq₁_eq, hq₂_eq]
    exact Nat.coprime_pow_primes k₁ k₂ hp1 hp2 hfne

  -- lcm of elements of t equals their product
  have h_lcm_eq_prod : t.lcm id = t.prod id :=
    Finset.lcm_eq_prod h_pairwise

  -- Multiset sum ≤ n
  have h_m_sum : t.val.sum ≤ n := by
    have h_sum_eq : t.sum id = t.val.sum := by
      show (t.1.map (fun q => q)).sum = t.1.sum
      rw [Multiset.map_id']
    rw [← h_sum_eq]
    exact hsum

  -- All elements ≥ 2 in Multiset
  have h_m_ge_2 : ∀ a ∈ t.val, 2 ≤ a := h_ge_2

  -- Construct permutation with cycleType = t.val
  have h_sigma : ∃ σ : Equiv.Perm (Fin n), σ.cycleType = t.val := by
    apply (Equiv.Perm.exists_with_cycleType_iff (Fin n)).mpr
    constructor
    · rw [Fintype.card_fin]
      exact h_m_sum
    · exact h_m_ge_2

  rcases h_sigma with ⟨σ, hσ_cycle⟩

  -- orderOf σ = t.val.lcm
  have h_order_eq_lcm : orderOf σ = t.val.lcm := by
    rw [← hσ_cycle]
    exact (Equiv.Perm.lcm_cycleType σ).symm

  -- t.val.lcm = t.lcm id
  have h_val_lcm : t.val.lcm = t.lcm id := by
    show t.1.lcm = t.lcm id
    rw [Finset.lcm_def]
    rw [Multiset.map_id]

  -- ∏ q ∈ t, q = t.val.lcm
  have h_prod_eq_lcm : ∏ q ∈ t, q = t.val.lcm := by
    rw [h_val_lcm, h_lcm_eq_prod]
    show (t.1.map (fun q => q)).prod = (t.1.map id).prod
    rw [Multiset.map_id', Multiset.map_id]

  -- t.val.lcm ≤ landauLocal n
  have h_le : t.val.lcm ≤ landauLocal n := by
    rw [← h_order_eq_lcm]
    apply Finset.le_sup
    exact Finset.mem_univ σ

  exact h_prod_eq_lcm ▸ h_le
