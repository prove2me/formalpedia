-- Prove2me | solution 1 for MasulloRH.three_adic_angular_prime_atom_reconstruction_and_energy
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-21T19:41:22.513419+00:00
-- url     : https://prove2.me/submissions/6d329d75-258d-480d-95c8-7bc384b1bda9

import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

open scoped BigOperators Classical

theorem solution (n : ℕ) (c m : ℂ) :
    let q := 3 ^ (n + 1)
    let h : ℕ := 2 * 3 ^ n
    let ρ := fun x : (ZMod q)ˣ =>
      ∑ χ : DirichletCharacter ℂ q,
        χ ((x : ZMod q)⁻¹) * (c * χ 2 - if χ = 1 then m else 0)
    (∀ x : (ZMod q)ˣ, ρ x = (if (x : ZMod q) = 2 then (h : ℂ) * c else 0) - m) ∧
    (∑ x : (ZMod q)ˣ, Complex.normSq (ρ x)) / (h : ℝ) =
      ((h : ℝ) - 1) * Complex.normSq c + Complex.normSq (c - m) := by
  classical
  dsimp only
  let q := 3 ^ (n + 1)
  let h : ℕ := 2 * 3 ^ n
  have : NeZero q := ⟨by dsimp [q]; positivity⟩
  have hcard : q.totient = h := by
    simpa [q, h, Nat.mul_comm] using Nat.totient_prime_pow_succ (p := 3) (by decide) n
  let a : (ZMod q)ˣ := ZMod.unitOfCoprime 2 ((show Nat.Coprime 2 3 by decide).pow_right _)
  have ha : (a : ZMod q) = 2 := by simp [a]
  let ρ := fun x : (ZMod q)ˣ =>
    ∑ χ : DirichletCharacter ℂ q,
      χ ((x : ZMod q)⁻¹) * (c * χ 2 - if χ = 1 then m else 0)
  have hr (x : (ZMod q)ˣ) :
      ρ x = (if (x : ZMod q) = 2 then (h : ℂ) * c else 0) - m := by
    dsimp [ρ]
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib]
    conv_lhs =>
      enter [1, 2, χ]
      rw [mul_left_comm]
    rw [← Finset.mul_sum, DirichletCharacter.sum_char_inv_mul_char_eq ℂ x.isUnit, hcard]
    simp [mul_ite, mul_comm c]
  refine ⟨hr, ?_⟩
  change (∑ x : (ZMod q)ˣ, Complex.normSq (ρ x)) / (h : ℝ) = _
  have ht (x : (ZMod q)ˣ) : Complex.normSq (ρ x) =
      (if x = a then Complex.normSq ((h : ℂ) * c - m) - Complex.normSq m else 0) +
        Complex.normSq m := by
    rw [hr x]
    by_cases hx : x = a
    · simp [hx, ha]
    · have hx' : (x : ZMod q) ≠ 2 := fun e => hx (Units.ext (e.trans ha.symm))
      simp [hx, hx', Complex.normSq_neg]
  simp_rw [ht]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, ZMod.card_units_eq_totient, hcard]
  have hne : (h : ℝ) ≠ 0 := by dsimp [h]; positivity
  apply (div_eq_iff hne).2
  simp only [Complex.normSq_sub, Complex.normSq_mul, Complex.normSq_natCast,
    mul_assoc, Complex.mul_re, Complex.natCast_im, Complex.natCast_re,
    zero_mul, sub_zero]
  dsimp [h]
  push_cast
  ring
