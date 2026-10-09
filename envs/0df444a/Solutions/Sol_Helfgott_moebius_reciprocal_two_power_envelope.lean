-- Prove2me | solution 1 for Helfgott.moebius_reciprocal_two_power_envelope
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T04:42:59.758621+00:00
-- url     : https://prove2.me/submissions/51884033-d848-48fc-a2d8-1ba33a6664f0

import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.Tactic

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
open Finset Nat Real ArithmeticFunction
open scoped BigOperators Classical
namespace Helfgott

lemma reciprocal_log_power_comparison (T X t c delta : ℝ)
    (hT : 1 < T) (ht : T ≤ t) (htX : t ≤ X) (hc : 0 ≤ c)
    (hd : 1/Real.log T ≤ delta) :
    c/Real.log t ≤ (c/Real.log X)*(X/t)^delta := by
  have ht0 : 0 < t := by linarith
  have hX0 : 0 < X := by linarith
  have hlogT : 0 < Real.log T := Real.log_pos hT
  have hlogt : 0 < Real.log t := Real.log_pos (by linarith)
  have hlogX : 0 < Real.log X := Real.log_pos (by linarith)
  have hlogTt : Real.log T ≤ Real.log t := Real.log_le_log (by linarith) ht
  have hlogtX : Real.log t ≤ Real.log X := Real.log_le_log ht0 htX
  have hd0 : 0 ≤ delta := le_trans (by positivity) hd
  have hdlog : 1 ≤ delta*Real.log t := by
    have hi := (div_le_iff₀ hlogT).mp hd
    have hm := mul_le_mul_of_nonneg_left hlogTt hd0
    nlinarith
  have hp : 1+delta*(Real.log X-Real.log t) ≤ (X/t)^delta := by
    rw [Real.rpow_def_of_pos (div_pos hX0 ht0),Real.log_div hX0.ne' ht0.ne']
    simpa only [mul_comm,add_comm] using Real.add_one_le_exp (delta*(Real.log X-Real.log t))
  have hr : Real.log X ≤ Real.log t*(X/t)^delta := by
    have hm := mul_le_mul_of_nonneg_left hp hlogt.le
    have hdif : 0 ≤ Real.log X-Real.log t := sub_nonneg.mpr hlogtX
    have hh := mul_le_mul_of_nonneg_right hdlog hdif
    nlinarith
  apply (div_le_iff₀ hlogt).mpr
  have hm := mul_le_mul_of_nonneg_left hr (div_nonneg hc hlogX.le)
  have he : (c/Real.log X)*Real.log X=c := div_mul_cancel₀ c hlogX.ne'
  nlinarith

lemma moebius_reciprocal_relaxed_sqrt_envelope (t beta : ℝ)
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

theorem moebius_reciprocal_two_power_envelope_complete
    (T X beta delta : ℝ) (hT : 11815 ≤ T) (hX : T ≤ X)
    (hb0 : 0 ≤ beta) (hb1 : beta ≤ 1/2) (hd : 1/Real.log T ≤ delta)
    (hsqrt : ∀ t : ℝ, 1 ≤ t → t < T →
      (∑ n∈Icc 1 ⌊t⌋₊, ((moebius n : ℤ) : ℝ)/(n : ℝ))^2*t ≤ 2)
    (hdecay : ∀ t : ℝ, 11815 ≤ t →
      |∑ n∈Icc 1 ⌊t⌋₊, ((moebius n : ℤ) : ℝ)/(n : ℝ)| ≤ (3/100)/Real.log t) :
    ∀ t : ℝ, 1 ≤ t → t ≤ X →
      |∑ n∈Icc 1 ⌊t⌋₊, ((moebius n : ℤ) : ℝ)/(n : ℝ)| ≤
        (2/t)^beta + ((3/100)/Real.log X)*(X/t)^delta := by
  intro t ht htX
  have hXp : 1 < X := by linarith
  have hlogX : 0 < Real.log X := Real.log_pos hXp
  by_cases hlo : t < T
  · have hi := moebius_reciprocal_relaxed_sqrt_envelope t beta ht hb0 hb1 (hsqrt t ht hlo)
    exact hi.trans (le_add_of_nonneg_right (by positivity))
  · have hTt : T ≤ t := le_of_not_gt hlo
    have hi := (hdecay t (hT.trans hTt)).trans
      (reciprocal_log_power_comparison T X t (3/100) delta (by linarith) hTt htX (by norm_num) hd)
    exact hi.trans (le_add_of_nonneg_left (by positivity))

end Helfgott
end

open Helfgott Finset Nat Real ArithmeticFunction
open scoped BigOperators Classical
theorem solution 
    (T X beta delta : ℝ) (hT : 11815 ≤ T) (hX : T ≤ X)
    (hb0 : 0 ≤ beta) (hb1 : beta ≤ 1/2) (hd : 1/Real.log T ≤ delta)
    (hsqrt : ∀ t : ℝ, 1 ≤ t → t < T →
      (∑ n∈Icc 1 ⌊t⌋₊, ((moebius n : ℤ) : ℝ)/(n : ℝ))^2*t ≤ 2)
    (hdecay : ∀ t : ℝ, 11815 ≤ t →
      |∑ n∈Icc 1 ⌊t⌋₊, ((moebius n : ℤ) : ℝ)/(n : ℝ)| ≤ (3/100)/Real.log t) :
    ∀ t : ℝ, 1 ≤ t → t ≤ X →
      |∑ n∈Icc 1 ⌊t⌋₊, ((moebius n : ℤ) : ℝ)/(n : ℝ)| ≤
        (2/t)^beta + ((3/100)/Real.log X)*(X/t)^delta := Helfgott.moebius_reciprocal_two_power_envelope_complete T X beta delta hT hX hb0 hb1 hd hsqrt hdecay
#print axioms solution
