-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.weightedSimplex_region_volume_toReal
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T06:49:21.557311+00:00
-- url     : https://prove2.me/submissions/255813fb-692a-4076-9a5f-ec87e626ecad

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_standardSimplex_sublevel_volume_toReal
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weightedSimplex_diagonal_change_toReal
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open Filter Topology
open scoped BigOperators

theorem solution {m : Nat} (w : Fin m → Real) (A : Real)
    (hw : ∀ i, 0 < w i) (hA : 0 < A) :
    (MeasureTheory.volume {x : Fin m → Real | (∀ i : Fin m, 0 ≤ x i) ∧
      ∑ i : Fin m, w i * x i ≤ A}).toReal =
      A ^ m / ((m.factorial : Real) * ∏ i : Fin m, w i) := by
  rw [OAI.PiExponent.DeterminantContradiction.weightedSimplex_diagonal_change_toReal
    w A hw hA,
    OAI.PiExponent.DeterminantContradiction.standardSimplex_sublevel_volume_toReal
      A hA]
  have hfact : (m.factorial : Real) ≠ 0 := by positivity
  have hprod : (∏ i : Fin m, w i) ≠ 0 :=
    ne_of_gt (Finset.prod_pos fun i hi => hw i)
  field_simp [hfact, hprod]
  <;> ring