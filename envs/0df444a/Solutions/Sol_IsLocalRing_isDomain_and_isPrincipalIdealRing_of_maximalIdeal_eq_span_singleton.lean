-- Prove2me | solution 1 for IsLocalRing.isDomain_and_isPrincipalIdealRing_of_maximalIdeal_eq_span_singleton
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/918105f4-6910-519a-8a03-23589779808e

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsLocalRing_isDomain_and_isPrincipalIdealRing_of_maximalIdeal_eq_span_singleton
set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace HartogsAbs

open IsLocalRing

variable {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

theorem isDomain_of_maximalIdeal_eq_span_of_forall_pow_ne_zero (τ : R)
    (hmax : maximalIdeal R = Ideal.span {τ}) (hτ : ∀ n : ℕ, τ ^ n ≠ 0) : IsDomain R := by
  classical
  have key : ∀ x : R, x ≠ 0 → ∃ (n : ℕ) (u : Rˣ), x = τ ^ n * u := by
    intro x hx
    have hinf : (⨅ n : ℕ, (maximalIdeal R) ^ n) = ⊥ :=
      Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal R).ne_top
    have hex : ∃ n : ℕ, x ∉ (maximalIdeal R) ^ n := by
      by_contra h
      push Not at h
      have : x ∈ (⨅ n : ℕ, (maximalIdeal R) ^ n) := Ideal.mem_iInf.mpr h
      rw [hinf, Ideal.mem_bot] at this
      exact hx this
    let n := Nat.find hex
    have hn : x ∉ (maximalIdeal R) ^ n := Nat.find_spec hex
    have hn0 : n ≠ 0 := by
      intro h0
      apply hn
      rw [show (n : ℕ) = 0 from h0, pow_zero, Ideal.one_eq_top]
      exact Submodule.mem_top
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hn0
    have hxm : x ∈ (maximalIdeal R) ^ m := by
      have := Nat.find_min hex (show m < n by omega)
      simpa using this
    rw [hmax, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hxm
    obtain ⟨u, rfl⟩ := hxm
    have hu : IsUnit u := by
      by_contra hu
      have hu' : u ∈ maximalIdeal R := (mem_maximalIdeal u).mpr hu
      rw [hmax, Ideal.mem_span_singleton] at hu'
      obtain ⟨v, rfl⟩ := hu'
      apply hn
      rw [hm, hmax, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
      exact ⟨v, by rw [pow_succ]; ring⟩
    exact ⟨m, hu.unit, by simp⟩
  haveI : NoZeroDivisors R := ⟨by
    intro a b hab
    by_contra h
    push Not at h
    obtain ⟨n, u, rfl⟩ := key a h.1
    obtain ⟨m, v, rfl⟩ := key b h.2
    apply hτ (n + m)
    have e : τ ^ n * ↑u * (τ ^ m * ↑v) = τ ^ (n + m) * ↑(u * v) := by rw [pow_add, Units.val_mul]; ring
    rw [e] at hab
    exact (Units.mul_left_eq_zero (u * v)).mp hab⟩
  exact NoZeroDivisors.to_isDomain R

theorem isPrincipalIdealRing_of_maximalIdeal_eq_span_of_forall_pow_ne_zero (τ : R)
    (hmax : maximalIdeal R = Ideal.span {τ}) (hτ : ∀ n : ℕ, τ ^ n ≠ 0) : IsPrincipalIdealRing R := by
  haveI := isDomain_of_maximalIdeal_eq_span_of_forall_pow_ne_zero τ hmax hτ
  have htfae := tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain R
  exact (htfae.out 0 4).mpr (show (IsLocalRing.maximalIdeal R).IsPrincipal from ⟨⟨τ, hmax⟩⟩)

end HartogsAbs

theorem solution
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R] (τ : R)
    (hmax : IsLocalRing.maximalIdeal R = Ideal.span {τ}) (hτ : ∀ n : ℕ, τ ^ n ≠ 0) :
    IsDomain R ∧ IsPrincipalIdealRing R :=
  ⟨HartogsAbs.isDomain_of_maximalIdeal_eq_span_of_forall_pow_ne_zero τ hmax hτ,
   HartogsAbs.isPrincipalIdealRing_of_maximalIdeal_eq_span_of_forall_pow_ne_zero τ hmax hτ⟩

end S_IsLocalRing_isDomain_and_isPrincipalIdealRing_of_maximalIdeal_eq_span_singleton
end P2MW
export P2MW.S_IsLocalRing_isDomain_and_isPrincipalIdealRing_of_maximalIdeal_eq_span_singleton (solution)
