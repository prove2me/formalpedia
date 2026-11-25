-- Prove2me | solution 1 for Kyprianou.Ch04.geometricMixtureOfProbabilityMeasures
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T20:10:21.041705+00:00
-- url     : https://prove2.me/submissions/af9bfdc8-8521-49d0-82c3-c564c9251a79

import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.MeasureTheory.Measure.MeasureSpace
open MeasureTheory
open scoped ENNReal
set_option autoImplicit false
/-- A geometric mixture of probability laws is again a probability law. -/
theorem solution
    {α : Type*} [MeasurableSpace α]
    (rho : ENNReal) (hRho : rho < 1)
    (nu : ℕ → Measure α) (hNu : ∀ n, IsProbabilityMeasure (nu n)) :
    IsProbabilityMeasure
      (Measure.sum (fun n : ℕ => ((1 - rho) * rho ^ n) • nu n)) := by
  rw [isProbabilityMeasure_iff, Measure.sum_apply _ MeasurableSet.univ]
  have hTerms (n : ℕ) :
      (((1 - rho) * rho ^ n) • nu n) Set.univ = (1 - rho) * rho ^ n := by
    rw [Measure.smul_apply]
    rw [isProbabilityMeasure_iff.mp (hNu n)]
    simp
  simp_rw [hTerms]
  rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
  have hpos : 0 < (1 : ENNReal) - rho := (tsub_pos_iff_lt).2 hRho
  have hfin : (1 : ENNReal) - rho ≠ ⊤ := by
    exact ne_of_lt (lt_of_le_of_lt (tsub_le_self) ENNReal.one_lt_top)
  exact ENNReal.mul_inv_cancel (ne_of_gt hpos) hfin
