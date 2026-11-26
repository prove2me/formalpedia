-- Prove2me | solution 1 for Kyprianou.Ch04.finiteFamilyCovarianceExpansion
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T23:25:59.868063+00:00
-- url     : https://prove2.me/submissions/82ba076f-21ae-4a71-9792-47d0cc196dc1

import Mathlib.MeasureTheory.Integral.Bochner.Basic
open MeasureTheory
open scoped BigOperators
set_option autoImplicit false
universe u v

/-- Expand the second moment of a finite family using every covariance. -/
theorem solution
    {Ω : Type u} {ι : Type v} [MeasurableSpace Ω] [DecidableEq ι]
    (P : Measure Ω) (s : Finset ι) (Z : ι → Ω → ℝ)
    (hprod : ∀ i ∈ s, ∀ j ∈ s,
      Integrable (fun ω => Z i ω * Z j ω) P) :
    (∫ ω, (∑ i ∈ s, Z i ω)^2 ∂P) =
      ∑ i ∈ s, ∑ j ∈ s, ∫ ω, Z i ω * Z j ω ∂P := by
  have hrow (i : ι) (hi : i ∈ s) :
      Integrable (fun ω => ∑ j ∈ s, Z i ω * Z j ω) P :=
    integrable_finsetSum s (fun j hj => hprod i hi j hj)
  calc
    (∫ ω, (∑ i ∈ s, Z i ω)^2 ∂P) =
        ∫ ω, ∑ i ∈ s, ∑ j ∈ s, Z i ω * Z j ω ∂P := by
      apply integral_congr_ae
      filter_upwards [] with ω
      rw [pow_two, Finset.sum_mul]
      simp only [Finset.mul_sum]
    _ = ∑ i ∈ s, ∫ ω, ∑ j ∈ s, Z i ω * Z j ω ∂P :=
      integral_finsetSum s hrow
    _ = _ := Finset.sum_congr rfl (fun i hi =>
      integral_finsetSum s (fun j hj => hprod i hi j hj))
