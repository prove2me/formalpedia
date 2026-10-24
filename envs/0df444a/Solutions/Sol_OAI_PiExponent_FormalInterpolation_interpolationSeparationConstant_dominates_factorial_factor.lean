-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.interpolationSeparationConstant_dominates_factorial_factor
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-24T04:23:04.726888+00:00
-- url     : https://prove2.me/submissions/aec37b12-9dfa-415c-aa89-2be3bd4e8ee9

import Definitions.Def_OAI_PiExponent_LogarithmicNormalBases
import Definitions.Def_OAI_PiExponent_LogarithmicInterpolationNumerics

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.FormalInterpolation

theorem solution (m k : Nat) (hk : k ≤ m + 1) (sigma : Rat)
    (hsigma : 0 < (sigma : Real)) :
    2 * (k.factorial : Real) *
        (((m : Real) + 2) / (sigma : Real)) ^ k ≤
      interpolationSeparationConstant m sigma := by
  let b : Real := (m : Real) + 2
  let a : Real := b / (sigma : Real)
  have hm : 1 ≤ m + 2 := by omega
  have hkb : k ≤ m + 2 := by omega
  have hb : 1 ≤ b := by
    dsimp [b]
    exact_mod_cast hm
  have ha : 0 < a := by
    dsimp [a]
    exact div_pos (by dsimp [b]; positivity) hsigma
  have fact_bound : ∀ n d : Nat, n ≤ d → n.factorial ≤ d ^ n := by
    intro n
    induction n with
    | zero =>
        intro d _
        simp [Nat.factorial]
    | succ n ih =>
        intro d hnd
        have hprev : n ≤ d := Nat.le_trans (Nat.le_succ n) hnd
        rw [Nat.factorial_succ]
        calc
          (n + 1) * n.factorial ≤ d * d ^ n := Nat.mul_le_mul hnd (ih d hprev)
          _ = d ^ (n + 1) := by rw [pow_succ]; exact Nat.mul_comm d (d ^ n)
  have hfactNat : k.factorial ≤ (m + 2) ^ k := fact_bound k (m + 2) hkb
  have hfact : (k.factorial : Real) ≤ b ^ k := by
    dsimp [b]
    exact_mod_cast hfactNat
  have hbpow : b ^ k ≤ b ^ (m + 2) := by
    gcongr
    all_goals first
    | exact hb
    | exact_mod_cast hkb
    | positivity
  have habase : a ≤ 1 + a := by linarith
  have haone : 1 ≤ 1 + a := by linarith
  have hapowBase : a ^ k ≤ (1 + a) ^ k := by
    gcongr
    all_goals first
    | exact habase
    | positivity
  have hapow : (1 + a) ^ k ≤ (1 + a) ^ (m + 2) := by
    gcongr
    all_goals first
    | exact haone
    | exact_mod_cast hkb
    | positivity
  have hapow' : a ^ k ≤ (1 + a) ^ (m + 2) := le_trans hapowBase hapow
  have hfirst :
      2 * (k.factorial : Real) * a ^ k ≤ 2 * b ^ k * a ^ k := by
    have hcoef : 2 * (k.factorial : Real) ≤ 2 * b ^ k := by nlinarith [hfact]
    exact mul_le_mul_of_nonneg_right hcoef (by positivity)
  have hsecond :
      2 * b ^ k * a ^ k ≤ 2 * b ^ (m + 2) * (1 + a) ^ (m + 2) := by
    have hcoef : 2 * b ^ k ≤ 2 * b ^ (m + 2) := by nlinarith [hbpow]
    calc
      2 * b ^ k * a ^ k ≤ 2 * b ^ (m + 2) * a ^ k :=
        mul_le_mul_of_nonneg_right hcoef (by positivity)
      _ ≤ 2 * b ^ (m + 2) * (1 + a) ^ (m + 2) := by
        exact mul_le_mul_of_nonneg_left hapow' (by positivity)
  change 2 * (k.factorial : Real) * a ^ k ≤
    2 * b ^ (m + 2) * (1 + a) ^ (m + 2)
  simpa [a, b, interpolationSeparationConstant] using le_trans hfirst hsecond
