-- Prove2me | solution 1 for HighEntropyLimit.lindblad_antinormal_monomial
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T05:42:46.400233+00:00
-- url     : https://prove2.me/submissions/5d2735a5-865c-4766-b449-ebc67dbff790

import Mathlib
import Definitions.Def_HighEntropyLimit_lindblad

open HighEntropyLimit

namespace HELind

variable {A : Type*} [Ring A] [Algebra ℂ A] (a adag : A)

lemma comm1 (hccr : a * adag - adag * a = 1) (n : ℕ) :
    a * (a ^ n * adag - adag * a ^ n) = (n : ℂ) • a ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : a ^ (n + 1) * adag - adag * a ^ (n + 1) =
        a * (a ^ n * adag - adag * a ^ n) + (a * adag - adag * a) * a ^ n := by
      rw [pow_succ']; noncomm_ring
    rw [e, hccr, one_mul, mul_add, ih, mul_smul_comm, ← pow_succ']
    push_cast
    rw [add_smul, one_smul]

lemma comm2 (hccr : a * adag - adag * a = 1) (m : ℕ) :
    (a * adag ^ m - adag ^ m * a) * adag = (m : ℂ) • adag ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    have e : a * adag ^ (m + 1) - adag ^ (m + 1) * a =
        (a * adag ^ m - adag ^ m * a) * adag + adag ^ m * (a * adag - adag * a) := by
      rw [pow_succ]; noncomm_ring
    rw [e, hccr, mul_one, add_mul, ih, smul_mul_assoc, ← pow_succ]
    push_cast
    rw [add_smul, one_smul]

end HELind

open HELind in
theorem solution {A : Type*} [Ring A] [Algebra ℂ A] (a adag : A)
    (hccr : a * adag - adag * a = 1) (hbar γ : ℝ) (n m : ℕ) :
    lindbladHeisenberg hbar 0 [(γ, adag, a)] (a ^ n * adag ^ m) =
      ((γ / 2 * (n + m) : ℝ) : ℂ) • (a ^ n * adag ^ m) := by
  set X := a ^ n * adag ^ m with hX
  have E1 : a * X * adag - a * adag * X = (n : ℂ) • X := by
    have : a * X * adag - a * adag * X = a * (a ^ n * adag - adag * a ^ n) * adag ^ m := by
      have h1 : adag ^ m * adag = adag * adag ^ m := (Commute.self_pow adag m).eq.symm
      calc a * X * adag - a * adag * X = a * a ^ n * (adag ^ m * adag) - a * adag * a ^ n * adag ^ m := by
            rw [hX]; noncomm_ring
        _ = a * a ^ n * (adag * adag ^ m) - a * adag * a ^ n * adag ^ m := by rw [h1]
        _ = _ := by noncomm_ring
    rw [this, comm1 a adag hccr n, smul_mul_assoc]
  have E2 : a * X * adag - X * (a * adag) = (m : ℂ) • X := by
    have : a * X * adag - X * (a * adag) = a ^ n * ((a * adag ^ m - adag ^ m * a) * adag) := by
      have h1 : a * a ^ n = a ^ n * a := (Commute.self_pow a n).eq
      calc a * X * adag - X * (a * adag) = (a * a ^ n) * adag ^ m * adag - a ^ n * adag ^ m * a * adag := by
            rw [hX]; noncomm_ring
        _ = (a ^ n * a) * adag ^ m * adag - a ^ n * adag ^ m * a * adag := by rw [h1]
        _ = _ := by noncomm_ring
    rw [this, comm2 a adag hccr m, mul_smul_comm]
  have key : a * X * adag - (1 / 2 : ℂ) • (a * adag * X + X * (a * adag)) =
      (1 / 2 : ℂ) • (a * X * adag - a * adag * X) + (1 / 2 : ℂ) • (a * X * adag - X * (a * adag)) := by
    module
  unfold lindbladHeisenberg
  simp only [zero_mul, mul_zero, sub_self, smul_zero, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, add_zero, zero_add]
  rw [key, E1, E2, smul_smul, smul_smul, ← add_smul, smul_smul]
  congr 1
  push_cast
  ring
