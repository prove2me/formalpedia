-- Prove2me | solution 1 for Kyprianou.Ch01.exponentialAscendingLadderRenewal
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T01:02:04.942295+00:00
-- url     : https://prove2.me/submissions/baa058b5-77fa-4a8e-8e66-caad9be7d32d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Distributions.Exponential
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Definitions.Def_QueueingFundamentals_MG1_transforms
import Theorems.Thm_Kyprianou_Ch01_expAscendingRenewalZeroAtom
import Theorems.Thm_Kyprianou_Ch01_expAscendingRenewalPositiveSeries
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

theorem solution
    (beta : ℝ) (hbeta : 0 < beta) :
    let mu : Measure ℝ :=
      (volume.restrict (Set.Ioi (0 : ℝ))).withDensity
        (fun x : ℝ => ENNReal.ofReal
          (beta * Real.exp (-beta * x)))
    ∀ x : ℝ, 0 ≤ x →
      (∑' n : ℕ,
        ((QueueingFundamentals.MG1.convPow mu n)
          (Set.Icc (0 : ℝ) x)).toReal) = 1 + beta * x := by
  intro mu x hx
  let f : ℕ → ℝ := fun n =>
    ((QueueingFundamentals.MG1.convPow mu n)
      (Set.Icc (0 : ℝ) x)).toReal
  have hplus : Summable (fun n => f (n + 1)) ∧
      (∑' n, f (n + 1)) = beta * x := by
    simpa only [f, mu] using
      (Kyprianou.Ch01.expAscendingRenewalPositiveSeries beta hbeta x hx)
  have hzero : f 0 = 1 :=
    Kyprianou.Ch01.expAscendingRenewalZeroAtom mu x hx
  have hsum : Summable f :=
    (summable_nat_add_iff (f := f) 1).mp hplus.1
  change (∑' n, f n) = 1 + beta * x
  calc
    (∑' n, f n) = f 0 + ∑' n, f (n + 1) := hsum.tsum_eq_zero_add
    _ = 1 + beta * x := by rw [hzero, hplus.2]
