-- Prove2me | solution 1 for Kyprianou.Ch05.renewalEpochPairLawV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T19:00:56.807117+00:00
-- url     : https://prove2.me/submissions/4c627445-87d1-4450-9991-b5e9d58e4595

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_RenewalEpochProcess
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

open Set Kyprianou.Ch05
open Classical in
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Z : ℕ → Omega → ℝ) (F : Measure ℝ)
    (hRenewal : IsRenewalEpochProcess P Z F) (n : ℕ) :
    P.map (fun w => (renewalEpoch Z n w,Z n w)) =
      (renewalConvolutionPower F n).prod F := by
  have hm (i : ℕ) : Measurable (renewalEpoch Z i) := by
    unfold renewalEpoch
    exact Finset.measurable_sum _ fun j _ => hRenewal.1 j
  have hi (i : ℕ) : IndepFun (renewalEpoch Z i) (Z i) P := by
    apply indepFun_iff_measure_inter_preimage_eq_mul.mpr
    intro A B hA hB
    rw [← Measure.map_apply (hRenewal.1 i) hB,hRenewal.2.1 i]
    exact hRenewal.2.2.2.2 i A B hA hB
  have hl (i : ℕ) : P.map (renewalEpoch Z i) = renewalConvolutionPower F i := by
    induction i with
    | zero =>
      have h0 : renewalEpoch Z 0 = fun _ => (0 : ℝ) := by funext w; simp [renewalEpoch]
      rw [h0]
      simp [renewalConvolutionPower]
    | succ i ih =>
      have hS : renewalEpoch Z (i+1) = renewalEpoch Z i + Z i := by
        funext w
        simp [renewalEpoch,Finset.sum_range_succ]
      rw [hS]
      change P.map (renewalEpoch Z i + Z i) = (renewalConvolutionPower F i).conv F
      rw [← ih,← hRenewal.2.1 i]
      exact (hi i).map_add_eq_map_conv_map (hm i) (hRenewal.1 i)
  rw [← hl n,← hRenewal.2.1 n]
  exact (hi n).map_prod_eq_prod_map_map (hm n).aemeasurable (hRenewal.1 n).aemeasurable
