-- Prove2me | solution 1 for GlobalTheory.CMVal.ValEx.eq_one_of_cong
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:21:42.687494+00:00
-- url     : https://prove2.me/submissions/4da74089-f15a-405e-a4e8-a66868386868

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsUnitaryCharOfOpenSubgroupAndHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_WithZeroEqOfLeExpIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousOfVal
import Theorems.Thm_GlobalTheory_CMVal_ValEx_val_nat_le
import Theorems.Thm_GlobalTheory_CMVal_ValEx_val_int_le
import Theorems.Thm_GlobalTheory_CMVal_ValEx_val_binom
import Theorems.Thm_GlobalTheory_CMVal_ValEx_exp_one_sq
import Theorems.Thm_GlobalTheory_CMVal_ValEx_exp_one_le
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub



set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open scoped WithZero
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.ValEx
variable {K : Type} [Field K] (v : Valuation K ℤᵐ⁰)
namespace GlobalTheory.CMVal.ValEx
theorem _root_.solution {l : ℕ} (hl : l.Prime) (h2 : l ≠ 2) (hv : v (l : K) = WithZero.exp (-1 : ℤ)) {z : Kˣ}
    (hz : IsOfFinOrder z) (h1 : z ∈ cong v 1) : z = 1 := by
  by_contra hne
  obtain ⟨p, hp, k, hk⟩ := Nat.exists_prime_and_dvd (n := orderOf z) (fun h => hne (orderOf_eq_one_iff.1 h))
  have hpos := hz.orderOf_pos
  have hk0 : k ≠ 0 := by rintro rfl; omega
  have hη : z ^ k ≠ 1 := pow_ne_one_of_lt_orderOf hk0 (by
    rw [hk]; have := hp.two_le; nlinarith [Nat.pos_of_ne_zero hk0])
  have hηp : (z ^ k) ^ p = 1 := by rw [← pow_mul, mul_comm, ← hk, pow_orderOf_eq_one]
  have hc := (cong v 1).pow_mem h1 k
  generalize z ^ k = y at hη hηp hc
  obtain ⟨t, ht⟩ : ∃ t : K, (y : K) = 1 + t := ⟨y - 1, by ring⟩
  have ht0 : t ≠ 0 := by rintro rfl; exact hη (Units.ext (by simpa using ht))
  have ht1 : v t ≤ WithZero.exp (-1 : ℤ) := by simpa [ht] using hc.2
  have hp1 : (1 + t) ^ p = 1 := by rw [← ht, ← Units.val_pow_eq_pow_val, hηp, Units.val_one]
  have hvp : v (p : K) ≤ WithZero.exp (-1 : ℤ) := by
    have := val_binom v (ht1.trans exp_one_le) p
    rw [hp1, sub_self, zero_sub, v.map_neg, map_mul] at this
    exact (le_of_mul_le_mul_right this (zero_lt_iff.2 (by simpa using ht0))).trans ht1
  have hpl : p = l := by
    by_contra hpl
    obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hp hl).2 hpl)
    have e : (1 : K) = (a : K) * p + (b : K) * l := by exact_mod_cast congrArg (Int.cast : ℤ → K) hab.symm
    have : v (1 : K) ≤ WithZero.exp (-1 : ℤ) := by
      rw [e]
      refine v.map_add_le ?_ ?_ <;> rw [map_mul]
      · exact (mul_le_mul' (val_int_le v a) hvp).trans (by rw [one_mul])
      · exact (mul_le_mul' (val_int_le v b) hv.le).trans (by rw [one_mul])
    rw [map_one, ← WithZero.exp_zero, WithZero.exp_le_exp] at this
    omega
  subst hpl
  obtain ⟨m, hm⟩ := hp.odd_of_ne_two h2
  have hs : ∑ i ∈ Finset.range p, (1 + t) ^ i = 0 := by
    have := geom_sum_mul (1 + t) p
    rw [hp1, sub_self, add_sub_cancel_left] at this
    exact (mul_eq_zero.1 this).resolve_right ht0
  have hsum : ∑ i ∈ Finset.range p, i = p * m := by
    have := Finset.sum_range_id_mul_two p
    have e : p - 1 = 2 * m := by omega
    rw [e] at this; nlinarith
  have hsum' : ∑ i ∈ Finset.range p, (i : K) = p * m := by
    have := congrArg (Nat.cast : ℕ → K) hsum
    rwa [Nat.cast_sum, Nat.cast_mul] at this
  have e : (p : K) = -(∑ i ∈ Finset.range p, ((1 + t) ^ i - 1 - i * t)) - (m : K) * (p * t) := by
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, hs, ← Finset.sum_mul, hsum']; simp; ring
  have : v (p : K) ≤ WithZero.exp (-2 : ℤ) := by
    rw [e, ← exp_one_sq]
    refine v.map_sub_le ?_ ?_
    · rw [v.map_neg]
      exact v.map_sum_le fun i _ => (val_binom v (ht1.trans exp_one_le) i).trans (mul_le_mul' ht1 ht1)
    · rw [map_mul, map_mul]
      exact (mul_le_mul' (val_nat_le v m) (mul_le_mul' hv.le ht1)).trans (by rw [one_mul])
  rw [hv, WithZero.exp_le_exp] at this
  omega
end GlobalTheory.CMVal.ValEx
