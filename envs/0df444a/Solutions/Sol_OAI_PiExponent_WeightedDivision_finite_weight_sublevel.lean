-- Prove2me | solution 1 for OAI.PiExponent.WeightedDivision.finite_weight_sublevel
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-20T08:16:47.186751+00:00
-- url     : https://prove2.me/submissions/9d3f36d4-999f-4579-b022-d9b83019916b

import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Algebra.BigOperators.Ring.Finset
import Theorems.Thm_OAI_PiExponent_WeightedDivision_exists_uniform_coordinate_bound
import Theorems.Thm_OAI_PiExponent_WeightedDivision_coordinate_box_finite

open scoped BigOperators

theorem solution
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (d : ι → ℝ) (hd : ∀ i, 0 < d i) (B : ℝ) :
    {u : ι →₀ ℕ | (∑ i, d i * (u i : ℝ)) ≤ B}.Finite := by
  obtain ⟨N, hN⟩ := OAI.PiExponent.WeightedDivision.exists_uniform_coordinate_bound d hd B
  have hbox : {u : ι →₀ ℕ | ∀ i, u i ≤ N}.Finite :=
    OAI.PiExponent.WeightedDivision.coordinate_box_finite (ι := ι) N
  apply hbox.subset
  intro u hu
  exact hN u hu