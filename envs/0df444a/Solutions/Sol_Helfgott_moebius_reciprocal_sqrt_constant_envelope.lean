-- Prove2me | solution 1 for Helfgott.moebius_reciprocal_sqrt_constant_envelope
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T05:59:10.266045+00:00
-- url     : https://prove2.me/submissions/bd0f8653-ba46-4915-8a20-2623e4f26359

import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.Tactic
import Theorems.Thm_Helfgott_moebius_reciprocal_sqrt_two_finite

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2200000
open Finset Nat Real ArithmeticFunction
open scoped BigOperators Classical
namespace Helfgott
lemma constantEnv_relaxed_sqrt (t beta : ℝ)
    (ht : 1 ≤ t) (hb0 : 0 ≤ beta) (hb1 : beta ≤ 1/2)
    (hsquare : (∑ n∈Icc 1 ⌊t⌋₊, ((moebius n : ℤ) : ℝ)/(n : ℝ))^2*t ≤ 2) :
    |∑ n∈Icc 1 ⌊t⌋₊, ((moebius n : ℤ) : ℝ)/(n : ℝ)| ≤ (2/t)^beta := by
  have ht0 : 0 < t := by linarith
  by_cases ht2 : 2 ≤ t
  · have hbase0 : 0 ≤ 2/t := by positivity
    have hbase1 : 2/t ≤ 1 := (div_le_one ht0).mpr ht2
    have hs : (∑ n∈Icc 1 ⌊t⌋₊, ((moebius n : ℤ) : ℝ)/(n : ℝ))^2 ≤ 2/t :=
      (le_div_iff₀ ht0).mpr hsquare
    have hroot : |∑ n∈Icc 1 ⌊t⌋₊, ((moebius n : ℤ) : ℝ)/(n : ℝ)| ≤ Real.sqrt (2/t) := by
      apply (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).mp
      simpa only [sq_abs,Real.sq_sqrt hbase0] using hs
    have hp := Real.rpow_le_rpow_of_exponent_ge (by positivity : 0 < 2/t) hbase1 hb1
    exact hroot.trans (by simpa only [Real.sqrt_eq_rpow] using hp)
  · have hfloor : ⌊t⌋₊=1 := (Nat.floor_eq_iff ht0.le).mpr (by constructor <;> norm_num <;> linarith)
    have hbase : 1 ≤ 2/t := (le_div_iff₀ ht0).mpr (by linarith)
    simpa [hfloor] using Real.one_le_rpow hbase hb0


theorem moebius_reciprocal_sqrt_constant_envelope_complete
    (hdecay : ∀ v : ℝ, 11815 ≤ v →
      |∑ r∈Icc 1 ⌊v⌋₊, ((moebius r : ℤ) : ℝ)/(r : ℝ)| ≤ (3/100)/Real.log v)
    (beta : ℝ) (hb0 : 0 ≤ beta) (hb1 : beta ≤ 1/2) :
    ∀ v : ℝ, 1 ≤ v →
      |∑ r∈Icc 1 ⌊v⌋₊, ((moebius r : ℤ) : ℝ)/(r : ℝ)| ≤
        (2/v)^beta+(3/100)/Real.log (1200001 : ℝ) := by
  intro v hv
  have hlog : 0 < Real.log (1200001 : ℝ) := Real.log_pos (by norm_num)
  by_cases hsmall : v < 1200001
  · have hi := constantEnv_relaxed_sqrt v beta hv hb0 hb1
      (moebius_reciprocal_sqrt_two_finite v hv hsmall)
    exact hi.trans (le_add_of_nonneg_right (by positivity))
  · have hlarge : (1200001 : ℝ) ≤ v := le_of_not_gt hsmall
    have hi := hdecay v (by linarith)
    have hc : (3/100 : ℝ)/Real.log v ≤ (3/100)/Real.log (1200001 : ℝ) :=
      div_le_div_of_nonneg_left (by norm_num) hlog
        (Real.log_le_log (by norm_num) hlarge)
    exact (hi.trans hc).trans (le_add_of_nonneg_left (by positivity))
end Helfgott
end

open Helfgott Finset Nat Real ArithmeticFunction
open scoped BigOperators Classical
theorem solution 
    (hdecay : ∀ v : ℝ, 11815 ≤ v →
      |∑ r∈Icc 1 ⌊v⌋₊, ((moebius r : ℤ) : ℝ)/(r : ℝ)| ≤ (3/100)/Real.log v)
    (beta : ℝ) (hb0 : 0 ≤ beta) (hb1 : beta ≤ 1/2) :
    ∀ v : ℝ, 1 ≤ v →
      |∑ r∈Icc 1 ⌊v⌋₊, ((moebius r : ℤ) : ℝ)/(r : ℝ)| ≤
        (2/v)^beta+(3/100)/Real.log (1200001 : ℝ) := Helfgott.moebius_reciprocal_sqrt_constant_envelope_complete hdecay beta hb0 hb1
#print axioms solution
