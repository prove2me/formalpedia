-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.weightedSimplex_measurable
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T15:05:08.355557+00:00
-- url     : https://prove2.me/submissions/7e491c56-7d43-4b0a-8ee1-dcae378a25e1

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open Filter Topology
open scoped BigOperators

theorem solution
    {m : Nat} (w : Fin m → Real) (A : Real) :
    MeasurableSet
      {x : Fin m → Real | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin m, w i * x i ≤ A} := by
  have hcoords :
      MeasurableSet {x : Fin m → Real | ∀ i, 0 ≤ x i} := by
    have h :
        MeasurableSet
          (⋂ i : Fin m, {x : Fin m → Real | 0 ≤ x i}) :=
      MeasurableSet.iInter (fun i =>
        measurableSet_le measurable_const (continuous_apply i).measurable)
    convert h using 1
    ext x
    simp
  have hsum :
      MeasurableSet {x : Fin m → Real | ∑ i : Fin m, w i * x i ≤ A} := by
    have hc : Continuous (fun x : Fin m → Real => ∑ i : Fin m, w i * x i) := by
      apply continuous_finset_sum
      intro i hi
      exact continuous_const.mul (continuous_apply i)
    exact measurableSet_le hc.measurable measurable_const
  convert MeasurableSet.inter hcoords hsum using 1 <;> ext x <;> simp