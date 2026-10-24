-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.standardSimplex_explicitBounds_volume_succ_slice
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T15:14:33.429778+00:00
-- url     : https://prove2.me/submissions/24593a25-1f98-4d5e-9fb9-e1c48a9895e2

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_measurable_box_fubini_real
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_standardSimplex_measurable_subset_box
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_standardSimplex_fiber_integral

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open Filter Topology
open scoped BigOperators

theorem solution (m : Nat) (A : Real) (hA : 0 ≤ A) :
    (MeasureTheory.volume {x : Fin (m + 1) → Real | (∀ i, 0 ≤ x i) ∧
      ∑ i : Fin (m + 1), x i ≤ A}).toReal =
      ∫ t in Set.Icc (0 : Real) A,
        (MeasureTheory.volume {x : Fin m → Real | (∀ i, 0 ≤ x i) ∧
          ∑ i : Fin m, x i ≤ A - t}).toReal := by
  let s : Set (Fin (m + 1) → Real) :=
    {x | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin (m + 1), x i ≤ A}
  have hs := OAI.PiExponent.DeterminantContradiction.standardSimplex_measurable_subset_box
    m A hA
  have h := OAI.PiExponent.DeterminantContradiction.measurable_box_fubini_real
    m A hA s hs.1 hs.2
  rw [OAI.PiExponent.DeterminantContradiction.standardSimplex_fiber_integral] at h
  simpa [s] using h