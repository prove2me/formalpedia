-- Prove2me | solution 1 for OAI.PiExponent.Collision.sum_weight_ge_of_low_count_le
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-08T08:39:13.577618+00:00
-- url     : https://prove2.me/submissions/78ad72fd-0fdd-44e6-93c7-f0e607baa6fa

import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.RingTheory.PowerSeries.Log
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic
import Mathlib.Topology.Instances.Matrix

section


namespace OAI

open scoped BigOperators

namespace PiExponent.Collision





















theorem cutoff_mul_high_count_le_sum {ι : Type*}
    (rows : Finset ι) (weight : ι → ℝ) (cutoff : ℝ)
    (hnonneg : ∀ i ∈ rows, 0 ≤ weight i) :
    cutoff * ((rows.filter fun i => ¬ weight i ≤ cutoff).card : ℝ) ≤
      ∑ i ∈ rows, weight i := by
  classical
  calc
    _ = ∑ i ∈ rows.filter (fun i => ¬ weight i ≤ cutoff), cutoff := by
      simp [mul_comm]
    _ ≤ ∑ i ∈ rows.filter (fun i => ¬ weight i ≤ cutoff), weight i := by
      apply Finset.sum_le_sum
      intro i hi
      exact le_of_lt (lt_of_not_ge (Finset.mem_filter.mp hi).2)
    _ ≤ ∑ i ∈ rows, weight i := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ rows)
      intro i hi _
      exact hnonneg i hi



end PiExponent.Collision

end OAI

end

open scoped BigOperators
theorem solution {ι : Type*}
    (rows : Finset ι) (weight : ι → ℝ) {cutoff η : ℝ}
    (hcutoff : 0 ≤ cutoff) (hnonneg : ∀ i ∈ rows, 0 ≤ weight i)
    (hlow : ((rows.filter fun i => weight i ≤ cutoff).card : ℝ) ≤
      η * rows.card) :
    cutoff * (1 - η) * rows.card ≤ ∑ i ∈ rows, weight i := open OAI OAI.PiExponent OAI.PiExponent.Collision in by
  classical
  have hcard : ((rows.filter fun i => weight i ≤ cutoff).card : ℝ) +
      ((rows.filter fun i => ¬ weight i ≤ cutoff).card : ℝ) = rows.card := by
    exact_mod_cast (Finset.card_filter_add_card_filter_not (s := rows)
      (fun i => weight i ≤ cutoff))
  have hhigh : (1 - η) * rows.card ≤
      ((rows.filter fun i => ¬ weight i ≤ cutoff).card : ℝ) := by nlinarith
  calc
    _ = cutoff * ((1 - η) * rows.card) := by ring
    _ ≤ cutoff * ((rows.filter fun i => ¬ weight i ≤ cutoff).card : ℝ) :=
      mul_le_mul_of_nonneg_left hhigh hcutoff
    _ ≤ ∑ i ∈ rows, weight i := cutoff_mul_high_count_le_sum rows weight cutoff hnonneg

#print axioms solution
