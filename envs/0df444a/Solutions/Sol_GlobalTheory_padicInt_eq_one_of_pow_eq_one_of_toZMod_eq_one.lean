-- Prove2me | solution 1 for GlobalTheory.padicInt_eq_one_of_pow_eq_one_of_toZMod_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:27:19.613037+00:00
-- url     : https://prove2.me/submissions/426e9f05-6178-4e44-b894-7ce492e8887b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsCosetRepresentativesOfFiniteSubgroupPadicI

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {l : ℕ} [hl : Fact l.Prime] (h2 : l ≠ 2)
    (δ : ℤ_[l]) {n : ℕ} (hn : n ≠ 0) (hδ : δ ^ n = 1) (h1 : PadicInt.toZMod δ = 1) : δ = 1 := by
  have key : ∀ p : ℕ, p.Prime → ∀ ε : ℤ_[l], ε ^ p = 1 → PadicInt.toZMod ε = 1 → ε = 1 := by
    intro p hp ε hε he1
    by_contra hne
    have hsum : ∑ i ∈ Finset.range p, ε ^ i = 0 := by
      have := geom_sum_mul ε p
      rw [hε, sub_self] at this
      exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr hne)
    have hp0 : (p : ZMod l) = 0 := by
      have := congrArg PadicInt.toZMod hsum
      simpa [map_sum, map_pow, he1] using this
    have hpl : l = p := (Nat.prime_dvd_prime_iff_eq hl.out hp).mp ((ZMod.natCast_eq_zero_iff _ _).mp hp0)
    subst hpl
    have hmem : ∀ z : ℤ_[l], (l : ℤ_[l]) ∣ z ↔ PadicInt.toZMod z = 0 := by
      intro z
      rw [← RingHom.mem_ker, PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p,
        Ideal.mem_span_singleton]
    have h := emultiplicity_geom_sum₂_eq_one (p := l) (x := ε) (y := 1) PadicInt.prime_p
      (hl.out.odd_of_ne_two h2) ((hmem _).mpr (by simp [he1])) (by rw [hmem, he1]; exact one_ne_zero)
    simp [hsum] at h
  induction n using Nat.recOnMul generalizing δ with
  | zero => exact absurd rfl hn
  | one => simpa using hδ
  | prime p hp => exact key p hp δ hδ h1
  | mul a b iha ihb =>
    have ha : a ≠ 0 := left_ne_zero_of_mul hn
    have hb : b ≠ 0 := right_ne_zero_of_mul hn
    refine iha δ ha (ihb (δ ^ a) hb (by rw [← pow_mul, hδ]) (by rw [map_pow, h1, one_pow])) h1
end GlobalTheory
