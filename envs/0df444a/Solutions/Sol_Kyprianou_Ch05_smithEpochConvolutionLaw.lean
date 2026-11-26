-- Prove2me | solution 1 for Kyprianou.Ch05.smithEpochConvolutionLaw
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T17:05:59.439784+00:00
-- url     : https://prove2.me/submissions/7bcad9a2-7583-4e27-8578-45d5fcaa3924

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_SmithRenewal_Elementary_RenewalProcess
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal BigOperators
set_option autoImplicit false
open Kyprianou.Ch05 SmithRenewal.Elementary

/-- The nth renewal epoch of a Smith renewal process has the nth convolution power of its common spacing law. -/
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : Nat → Omega → Real) (F : Measure Real)
    (hX : IsRenewalProcess P X)
    (hLaw : ∀ n, Measure.map (X n) P = F) (n : Nat) :
    Measure.map (S X n) P = renewalConvolutionPower F n := by
  have hm (i : Nat) : Measurable (S X i) := by
    unfold S
    exact Finset.measurable_sum _ fun j _ => hX.measurable j
  induction n with
  | zero =>
    have h0 : S X 0 = fun _ => (0 : Real) := by
      funext w
      simp [S]
    rw [h0]
    simp [renewalConvolutionPower]
  | succ n ih =>
    have hS : S X (n+1) = fun w => S X n w + X n w := by
      funext w
      simp [S, Finset.sum_range_succ]
    have hi := hX.indep.indepFun_finsetSum_of_notMem hX.measurable
      (Finset.notMem_range_self (n := n))
    have he : (∑ j ∈ Finset.range n, X j) = S X n := by
      funext w
      simp [S]
    rw [he] at hi
    rw [hS]
    change Measure.map (S X n + X n) P = (renewalConvolutionPower F n).conv F
    rw [← ih, ← hLaw n]
    first
    | exact hi.map_add_eq_map_conv_map (hm n) (hX.measurable n)
    | exact hi.map_add_eq_map_conv_map
    | exact hi.map_add_eq_map_conv_map' (hm n) (hX.measurable n)
