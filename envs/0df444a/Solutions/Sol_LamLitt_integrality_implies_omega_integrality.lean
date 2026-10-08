-- Prove2me | solution 1 for LamLitt.integrality_implies_omega_integrality
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T14:37:29.792147+00:00
-- url     : https://prove2.me/submissions/af58cbeb-259b-4522-ab25-d142c9a1bf18

import Definitions.Def_LamLitt_Defs
import Mathlib

set_option autoImplicit false

open PowerSeries

namespace LamLittAux1cf

open LamLitt in
theorem den_coprime_of_mem (N : ℕ) (x : ℚ) (hx : x ∈ ℤAdjoinInvNat N) :
    ∀ p : ℕ, p.Prime → N < p → Nat.Coprime x.den p := by
  unfold ℤAdjoinInvNat at hx
  induction hx using Algebra.adjoin_induction with
  | mem y hy =>
    rw [Set.mem_singleton_iff] at hy
    subst hy
    intro p hp hNp
    rcases Nat.eq_zero_or_pos N with h0 | hpos
    · subst h0; simp
    · rw [one_div, Rat.inv_natCast_den, if_neg (Nat.pos_iff_ne_zero.mp hpos)]
      exact Nat.Coprime.symm
        ((Nat.Prime.coprime_iff_not_dvd hp).2 (Nat.not_dvd_of_pos_of_lt hpos hNp))
  | algebraMap r =>
    intro p hp hNp
    simp
  | add a b _ _ ha hb =>
    intro p hp hNp
    exact Nat.Coprime.coprime_dvd_left (Rat.add_den_dvd a b)
      (Nat.Coprime.mul (ha p hp hNp) (hb p hp hNp))
  | mul a b _ _ ha hb =>
    intro p hp hNp
    exact Nat.Coprime.coprime_dvd_left (Rat.mul_den_dvd a b)
      (Nat.Coprime.mul (ha p hp hNp) (hb p hp hNp))

end LamLittAux1cf

open LamLitt PowerSeries in
theorem solution
    (f : PowerSeries ℚ) (N : ℕ) (hN : IsCoeffIntegralAdjointInvNat f N) :
    ∃ ω : Nat.Primes → ℤ, omegaSuperlinear ω ∧ omegaIntegral ω (PowerSeries.coeff · f) := by
  refine ⟨fun p => if N < (p : ℕ) then ((p : ℕ) : ℤ) ^ 2 else -1, ?_, ?_⟩
  · unfold omegaSuperlinear
    have hlim : Filter.Tendsto (fun p : Nat.Primes => (((p : ℕ) : ℝ)))
        (Filter.comap (fun p : Nat.Primes ↦ (p : ℕ)) Filter.atTop) Filter.atTop :=
      tendsto_natCast_atTop_atTop.comp Filter.tendsto_comap
    refine hlim.congr' ?_
    have hev : ∀ᶠ p : Nat.Primes in
        Filter.comap (fun p : Nat.Primes ↦ (p : ℕ)) Filter.atTop, N < (p : ℕ) := by
      rw [Filter.eventually_comap]
      filter_upwards [Filter.eventually_gt_atTop N] with n hn p hp
      rw [hp]; exact hn
    filter_upwards [hev] with p hp
    rw [if_pos hp]
    have hp0 : ((p : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast p.prop.ne_zero
    push_cast
    field_simp
  · intro p j hj
    by_cases h : N < (p : ℕ)
    · exact LamLittAux1cf.den_coprime_of_mem N _ (hN j) p p.prop h
    · simp only [if_neg h] at hj
      omega
