-- Prove2me | solution 1 for Kyprianou.Ch04.exercise45ClosedWindowPositiveTimeV2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T17:22:29.184813+00:00
-- url     : https://prove2.me/submissions/3a24af8e-4f7a-4c9d-a17e-502688f3d83e

import Mathlib
import Definitions.Def_Kyprianou_Ch04_Exercise4_5CertificationV3
open MeasureTheory ProbabilityTheory Filter Set Topology LevyStochCalc.Poisson
open scoped NNReal ENNReal Classical Topology
set_option autoImplicit false
theorem solution
    (μ : Measure (ℝ × ℝ)) (hzero : μ ({0} ×ˢ (Set.univ : Set ℝ)) = 0)
    (T : NNReal) :
    μ.restrict (Icc (0 : ℝ) (T : ℝ) ×ˢ Set.univ) =
      μ.restrict (Ioc (0 : ℝ) (T : ℝ) ×ˢ Set.univ) := by
  apply Measure.restrict_congr_set
  have h : ∀ᵐ z : ℝ × ℝ ∂μ, z ∉ ({0} ×ˢ (Set.univ : Set ℝ)) :=
    (compl_mem_ae_iff.mpr hzero)
  filter_upwards [h] with z hz
  have hn : z.1 ≠ 0 := fun he => hz ⟨he,Set.mem_univ _⟩
  change (z.1 ∈ Icc (0 : ℝ) (T : ℝ) ∧ z.2 ∈ Set.univ) = (z.1 ∈ Ioc (0 : ℝ) (T : ℝ) ∧ z.2 ∈ Set.univ)
  apply propext
  change (0 ≤ z.1 ∧ z.1 ≤ (T : ℝ)) ∧ z.2 ∈ Set.univ ↔ (0 < z.1 ∧ z.1 ≤ (T : ℝ)) ∧ z.2 ∈ Set.univ
  constructor
  · rintro ⟨⟨h0,hT⟩,hu⟩
    exact ⟨⟨lt_of_le_of_ne h0 (Ne.symm hn),hT⟩,hu⟩
  · rintro ⟨⟨h0,hT⟩,hu⟩
    exact ⟨⟨h0.le,hT⟩,hu⟩
