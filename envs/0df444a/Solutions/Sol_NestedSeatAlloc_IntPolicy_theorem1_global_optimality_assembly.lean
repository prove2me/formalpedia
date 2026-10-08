-- Prove2me | solution 1 for NestedSeatAlloc.IntPolicy.theorem1_global_optimality_assembly
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-06T21:16:13.868331+00:00
-- url     : https://prove2.me/submissions/cdf06a95-588d-4d26-ad73-7efd0bd78a13

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open NestedSeatAlloc.IntPolicy

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (f p : ℕ → ℝ) (hM : IsSeatModel P X f)
    (hp : IsProtectionPolicy p) (h20 : SubdiffCondition P X f p)
    (hbase : ∀ q, IsProtectionPolicy q → ∀ s, 0 ≤ s →
      expRevenue P X f q 1 s ≤ expRevenue P X f p 1 s)
    (hstep : ∀ k s, 1 ≤ k → 0 ≤ s →
      InSubdiff (expRevenue P X f p k) (p k) (f (k + 1)) →
      (∀ q, IsProtectionPolicy q → expRevenue P X f q k s ≤ expRevenue P X f p k s) →
      ∀ q, IsProtectionPolicy q → expRevenue P X f q (k + 1) s ≤ expRevenue P X f p (k + 1) s) :
    IsOptimal P X f p := by
  intro q hq k hk s hs
  revert q hq hk s hs
  induction k with
  | zero =>
      intro q hq hk s hs
      exact (Nat.not_succ_le_zero 0 hk).elim
  | succ k ih =>
      by_cases hk0 : k = 0
      · subst k
        intro q hq hk s hs
        exact hbase q hq s hs
      · have hkpos : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
        intro q hq hk s hs
        exact hstep k s hkpos hs (h20 k hkpos)
          (fun q' hq' => ih q' hq' hkpos s hs) q hq
