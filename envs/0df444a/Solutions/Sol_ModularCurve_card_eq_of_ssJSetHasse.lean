-- Prove2me | solution 1 for ModularCurve.card_eq_of_ssJSetHasse
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/73414c03-9e25-500e-ad45-d863ced56485

import Mathlib
import Definitions.Def_WeierstrassCurve_HasseInvariant
import Definitions.Def_ModularCurve_JWidth
import Theorems.Thm_ModularCurve_sum_inv_jWidth_of_ssJSetHasse
import Theorems.Thm_ModularCurve_zero_mem_ssJSetHasse_iff
import Theorems.Thm_ModularCurve_ofNat1728_mem_ssJSetHasse_iff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_card_eq_of_ssJSetHasse

set_option autoImplicit false

open Polynomial

namespace ModularCurve
p2m_export "ModularCurve" "ssJSetHasse jWidth sum_inv_jWidth_of_ssJSetHasse zero_mem_ssJSetHasse_iff ofNat1728_mem_ssJSetHasse_iff"
p2m_open "ModularCurve"

open Finset

theorem two_ne_zero_of_charP_of_ne_two' (K : Type*) [Field K] {q : ℕ} [hp : Fact q.Prime]
    [CharP K q] (hq2 : q ≠ 2) : (2 : K) ≠ 0 := by
  have : ((2 : ℕ) : K) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff K q]
    intro h
    exact hq2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp h)
  simpa using this

theorem three_ne_zero_of_charP_of_five_le' (K : Type*) [Field K] {q : ℕ} [hp : Fact q.Prime]
    [CharP K q] (hq : 5 ≤ q) : (3 : K) ≠ 0 := by
  have : ((3 : ℕ) : K) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff K q]
    intro h
    have := (Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_three).mp h
    omega
  simpa using this

theorem inv_cast_jWidth_eq' {K : Type*} [Field K] [DecidableEq K] (h1728 : (1728 : K) ≠ 0) (j : K) :
    ((jWidth j : ℚ))⁻¹
      = 1 - (if j = 0 then (2 / 3 : ℚ) else 0) - (if j = 1728 then (1 / 2 : ℚ) else 0) := by
  unfold jWidth
  by_cases h0 : j = 0
  · subst h0
    simp only [if_true, if_neg (Ne.symm h1728)]
    norm_num
  · by_cases h1 : j = 1728
    · subst h1
      simp only [if_neg h1728, if_true]
      norm_num
    · simp only [if_neg h0, if_neg h1]
      norm_num

theorem card_eq_of_ssJSetHasse' (q : ℕ) [hp : Fact q.Prime] (hq : 5 ≤ q)
    (K : Type*) [Field K] [IsAlgClosed K] [CharP K q] [DecidableEq K]
    (S : Finset K) (hS : ∀ j, j ∈ S ↔ j ∈ ssJSetHasse q K) :
    S.card = q / 12 + (if q % 3 = 2 then 1 else 0) + (if q % 4 = 3 then 1 else 0) := by
  have hq2 : q ≠ 2 := by omega
  have hodd : q % 2 = 1 := Nat.odd_iff.mp (hp.out.odd_of_ne_two hq2)
  have h3q : q % 3 ≠ 0 := fun h => by
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp.out).mp (Nat.dvd_of_mod_eq_zero h)
    omega
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_charP_of_ne_two' K hq2
  have h3 : (3 : K) ≠ 0 := three_ne_zero_of_charP_of_five_le' K hq
  have h1728 : (1728 : K) ≠ 0 := by
    rw [show (1728 : K) = 2 ^ 6 * 3 ^ 3 by norm_num]
    exact mul_ne_zero (pow_ne_zero _ h2) (pow_ne_zero _ h3)
  have hmass := sum_inv_jWidth_of_ssJSetHasse q hq K S hS
  rw [Finset.sum_congr rfl (fun j _ => inv_cast_jWidth_eq' h1728 j), Finset.sum_sub_distrib,
    Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one, Finset.sum_ite_eq',
    Finset.sum_ite_eq'] at hmass
  have h0 : (0 : K) ∈ S ↔ q % 3 = 2 := (hS 0).trans (zero_mem_ssJSetHasse_iff q hq K)
  have h1 : (1728 : K) ∈ S ↔ q % 4 = 3 := (hS 1728).trans (ofNat1728_mem_ssJSetHasse_iff q hq K)
  simp only [h0, h1] at hmass

  split_ifs at hmass ⊢ with ha hb hb
  · have e : ((12 * S.card + 1 : ℕ) : ℚ) = ((q + 14 : ℕ) : ℚ) := by push_cast; linarith
    have := (Nat.cast_inj (R := ℚ)).mp e
    omega
  · have e : ((12 * S.card + 1 : ℕ) : ℚ) = ((q + 8 : ℕ) : ℚ) := by push_cast; linarith
    have := (Nat.cast_inj (R := ℚ)).mp e
    omega
  · have e : ((12 * S.card + 1 : ℕ) : ℚ) = ((q + 6 : ℕ) : ℚ) := by push_cast; linarith
    have := (Nat.cast_inj (R := ℚ)).mp e
    omega
  · have e : ((12 * S.card + 1 : ℕ) : ℚ) = ((q : ℕ) : ℚ) := by push_cast; linarith
    have := (Nat.cast_inj (R := ℚ)).mp e
    omega

end ModularCurve

p2m_open "ModularCurve P2MW.S_ModularCurve_card_eq_of_ssJSetHasse.ModularCurve"

theorem solution (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q)
    (K : Type*) [Field K] [IsAlgClosed K] [CharP K q] [DecidableEq K]
    (S : Finset K) (hS : ∀ j, j ∈ S ↔ j ∈ ssJSetHasse q K) :
    S.card = q / 12 + (if q % 3 = 2 then 1 else 0) + (if q % 4 = 3 then 1 else 0) :=
  ModularCurve.card_eq_of_ssJSetHasse' q hq K S hS

end S_ModularCurve_card_eq_of_ssJSetHasse
end P2MW
export P2MW.S_ModularCurve_card_eq_of_ssJSetHasse (solution)
