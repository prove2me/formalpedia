-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.weightedSimplex_volume_eq_standardSimplex_div_prod
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T14:57:40.288849+00:00
-- url     : https://prove2.me/submissions/5f7a03c6-890e-4604-b9cc-06127e92f973

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_diagonal_scaling_volume_toReal
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_diagonalScaling_image_weighted_eq_standardSimplex
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weightedSimplex_measurable
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open Filter Topology
open scoped BigOperators

theorem solution {m : Nat} (w : Fin m → Real) (A : Real)
    (hw : ∀ i, 0 < w i) (hA : 0 ≤ A) :
    (MeasureTheory.volume
      {x : Fin m → Real | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin m, w i * x i ≤ A}).toReal =
      ((MeasureTheory.volume
        {y : Fin m → Real | (∀ i, 0 ≤ y i) ∧ ∑ i : Fin m, y i ≤ A}).toReal) /
        ∏ i : Fin m, w i := by
  have hset :
      (fun x : Fin m → Real => fun i => w i * x i) ''
          {x : Fin m → Real | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin m, w i * x i ≤ A} =
        {y : Fin m → Real | (∀ i, 0 ≤ y i) ∧ ∑ i : Fin m, y i ≤ A} :=
    OAI.PiExponent.DeterminantContradiction.diagonalScaling_image_weighted_eq_standardSimplex
      w A hw hA
  have hscale :
      (MeasureTheory.volume
        ((fun x : Fin m → Real => fun i => w i * x i) ''
          {x : Fin m → Real | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin m, w i * x i ≤ A})).toReal =
        (∏ i : Fin m, w i) *
          (MeasureTheory.volume
            {x : Fin m → Real | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin m, w i * x i ≤ A}).toReal :=
    OAI.PiExponent.DeterminantContradiction.diagonal_scaling_volume_toReal
      w hw
      {x : Fin m → Real | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin m, w i * x i ≤ A}
      (OAI.PiExponent.DeterminantContradiction.weightedSimplex_measurable w A)
  rw [← hset, hscale]
  have hp : 0 < ∏ i : Fin m, w i := Finset.prod_pos fun i _ => hw i
  field_simp [ne_of_gt hp]
  <;> ring