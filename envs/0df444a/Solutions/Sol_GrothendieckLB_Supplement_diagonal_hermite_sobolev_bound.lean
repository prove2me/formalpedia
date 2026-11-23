-- Prove2me | solution 1 for GrothendieckLB.Supplement.diagonal_hermite_sobolev_bound
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T19:27:18.832637+00:00
-- url     : https://prove2.me/submissions/6da94181-ad7a-45a9-aebd-57bc97f4dacd

import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib

set_option maxHeartbeats 2000000

namespace HermiteBoundaryEstimate
open Finset
set_option maxHeartbeats 600000

private theorem reciprocal (n : ℕ) :
    (∑ j ∈ range n, (1:ℝ)/((j:ℝ)+1)^2) ≤ 2 := by
  have h (k : ℕ) : (∑ j ∈ range k, (1:ℝ)/((j:ℝ)+2)^2) ≤ 1-1/((k:ℝ)+1) := by
    induction k with
    | zero => norm_num
    | succ k ih =>
      rw [sum_range_succ,Nat.cast_succ]
      have hp : 0 < (k:ℝ)+1 := by positivity
      have hq : 0 < (k:ℝ)+2 := by positivity
      have ht : (1:ℝ)/((k:ℝ)+2)^2 ≤ 1/((k:ℝ)+1)-1/((k:ℝ)+2) := by
        field_simp [hp.ne',hq.ne'] <;> nlinarith
      rw [show (k:ℝ)+1+1=k+2 by ring]
      linarith only [ih,ht]
  cases n with
  | zero => norm_num
  | succ n =>
    rw [sum_range_succ']
    simp only [Nat.cast_zero,zero_add,one_pow,div_one,Nat.cast_succ]
    simp only [add_assoc,show (1:ℝ)+1=2 by norm_num]
    linarith only [h n,show (0:ℝ)≤1/((n:ℝ)+1) by positivity]

end HermiteBoundaryEstimate

open HermiteBoundaryEstimate in
theorem solution (d : ℕ → ℂ) (z : ℂ) (hz : ‖z‖≤1) (u v : ℝ)
    (hu : ‖d 0‖^2≤u) (hv : ∀ n : ℕ, (∑ k ∈ Finset.range n, ((k:ℝ)+1)^2*‖d (k+1)‖^2)≤v) :
    Summable (fun n : ℕ => z^n*d n) ∧ ‖∑' n : ℕ, z^n*d n‖^2≤(3/2:ℝ)*(u+4*v) := by
  have hv0 : 0≤v := by simpa using hv 0
  have hu0 := (sq_nonneg ‖d 0‖).trans hu
  have hbound (n : ℕ) : (∑ k ∈ Finset.range n, ‖d (k+1)‖)≤Real.sqrt (2*v) := by
    have hc := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (Finset.range n)
      (r:=fun k : ℕ => ‖d (k+1)‖) (f:=fun k : ℕ => ((k:ℝ)+1)^2*‖d (k+1)‖^2)
      (g:=fun k : ℕ => 1/((k:ℝ)+1)^2) (fun k _ => by positivity) (fun k _ => by positivity)
      (fun k _ => by
        have h : (k:ℝ)+1≠0 := by positivity
        apply le_of_eq
        field_simp [h])
    apply Real.le_sqrt_of_sq_le
    rw [mul_comm 2 v]
    exact hc.trans (mul_le_mul (hv n) (reciprocal n) (Finset.sum_nonneg fun k _ => by positivity) hv0)
  have ha := summable_of_sum_range_le (fun k : ℕ => norm_nonneg (d (k+1))) hbound
  have ht := Real.tsum_le_of_sum_range_le (fun k : ℕ => norm_nonneg (d (k+1))) hbound
  have hd (n : ℕ) : ‖z^n*d n‖≤‖d n‖ := by
    rw [norm_mul,norm_pow]
    exact mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hz)
  have htail : Summable fun n : ℕ => z^(n+1)*d (n+1) := ha.of_norm_bounded (fun n => hd (n+1))
  have hs : Summable fun n : ℕ => z^n*d n := (summable_nat_add_iff 1).mp htail
  refine ⟨hs,?_⟩
  have hnorm : ‖∑' n : ℕ, z^n*d n‖≤Real.sqrt u+Real.sqrt (2*v) := by
    rw [tsum_eq_zero_add' (f:=fun n : ℕ => z^n*d n) htail,pow_zero,one_mul]
    exact (norm_add_le _ _).trans (add_le_add (Real.le_sqrt_of_sq_le hu)
      ((tsum_of_norm_bounded ha.hasSum (fun n => hd (n+1))).trans ht))
  have ht2 := Real.sq_sqrt (show 0≤2*v by positivity)
  have hu2 := Real.sq_sqrt hu0
  have hm := sq_nonneg (Real.sqrt u-2*Real.sqrt (2*v))
  have hw := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  nlinarith only [hw,ht2,hu2,hm]

