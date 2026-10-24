-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.simplex_volume_succ_product_reindex
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T12:34:10.547844+00:00
-- url     : https://prove2.me/submissions/d0299ea2-6201-412e-bc96-2a73c2b1d15d

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_coordinate_reindex_isometry
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplex_volume_of_coordinate_isometry
open scoped BigOperators
open MeasureTheory

theorem solution (m : Nat) (T : Real) :
    MeasureTheory.volume {x : Fin (m + 1) → Real |
      (∀ i, 0 ≤ x i) ∧ (∑ i, x i) < T} =
      MeasureTheory.volume {p : (Fin m → Real) × Real |
        (∀ i, 0 ≤ p.1 i) ∧ 0 ≤ p.2 ∧ (∑ i, p.1 i) + p.2 < T} := by
  obtain ⟨e, hfirst, hlast⟩ :=
    OAI.PiExponent.DeterminantContradiction.coordinate_reindex_isometry m
  exact OAI.PiExponent.DeterminantContradiction.simplex_volume_of_coordinate_isometry
    m T e hfirst hlast