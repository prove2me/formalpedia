-- Prove2me | solution 1 for GlobalTheory.CMVal.OrderUnits.root_of_unity_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:37:06.147801+00:00
-- url     : https://prove2.me/submissions/63811745-0b33-43d6-8421-ee7a8250f16d

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmRingClassOrderUnitsEqMaxRealSubfieldUnits
import Theorems.Thm_GlobalTheory_CMVal_OrderUnits_geom_first_order
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
open NumberField IsDedekindDomain GlobalTheory.CMVal
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.OrderUnits
namespace GlobalTheory.CMVal.OrderUnits
theorem _root_.solution {R : Type} [CommRing R] [IsDomain R] {P : Ideal R} (hP : P ≠ ⊤) {l : ℕ} (hl : l.Prime) (hl2 : l ≠ 2)
    (hlP : (l : R) ∈ P) (hlP2 : (l : R) ∉ P ^ 2) {ζ : R} (hζ : IsOfFinOrder ζ) (h1 : ζ - 1 ∈ P) : ζ = 1 := by
  by_contra hne
  have hn : orderOf ζ ≠ 1 := fun h => hne (orderOf_eq_one_iff.1 h)
  obtain ⟨p, hp, m, hm⟩ := Nat.exists_prime_and_dvd hn
  have hpos := hζ.orderOf_pos
  have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; simp [hm] at hpos)
  have hη1 : ζ ^ m ≠ 1 := pow_ne_one_of_lt_orderOf hm0.ne' (by rw [hm]; nlinarith [hp.two_le])
  have hηp : (ζ ^ m) ^ p = 1 := by rw [← pow_mul, mul_comm, ← hm, pow_orderOf_eq_one]
  have ht : ζ ^ m - 1 ∈ P := by
    obtain ⟨s, hs⟩ := sub_one_dvd_pow_sub_one ζ m
    rw [hs]; exact P.mul_mem_right _ h1
  have hsum : ∑ i ∈ Finset.range p, (ζ ^ m) ^ i = 0 := by
    have := mul_geom_sum (ζ ^ m) p
    rw [hηp, sub_self] at this
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hη1)
  obtain ⟨r, hr⟩ := geom_first_order (ζ ^ m - 1) p
  rw [add_sub_cancel, hsum] at hr
  set t := ζ ^ m - 1
  have hpe : (p : R) = -((p.choose 2 : ℕ) * t) - t ^ 2 * r := by linear_combination -hr
  have hpP : (p : R) ∈ P := by
    rw [hpe]
    exact sub_mem (neg_mem (P.mul_mem_left _ ht)) (P.mul_mem_right _ (P.pow_mem_of_mem ht 2 two_pos))
  have hpl : p = l := by
    by_contra h
    have hc : IsCoprime (p : R) (l : R) := Nat.Coprime.cast ((Nat.coprime_primes hp hl).2 h)
    obtain ⟨a, b, hab⟩ := hc
    exact hP ((Ideal.eq_top_iff_one P).2 (hab ▸ add_mem (P.mul_mem_left _ hpP) (P.mul_mem_left _ hlP)))
  subst hpl
  obtain ⟨k, hk⟩ := hp.dvd_choose_self two_ne_zero (lt_of_le_of_ne hp.two_le (Ne.symm hl2))
  apply hlP2
  rw [hpe, hk]
  refine sub_mem (neg_mem ?_) (Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow ht 2))
  rw [sq]
  push_cast
  exact Ideal.mul_mem_mul (P.mul_mem_right _ hlP) ht
end GlobalTheory.CMVal.OrderUnits
