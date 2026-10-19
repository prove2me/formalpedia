-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.weighted_simplex_region_scale
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-17T03:17:47.188794+00:00
-- url     : https://prove2.me/submissions/119aa2cf-794a-4b55-ab2a-52179900ec2c

import Definitions.Def_OAI_NumberTheory_PiExponent_WeightedSimplexRegion
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weighted_simplex_region_map
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_diagonal_map_volume

open scoped BigOperators Topology
open OAI.PiExponent.DeterminantContradiction

theorem solution
    (m : ℕ) (w : Fin m → ℝ) (T : ℝ) (hw : ∀ i, 0 < w i) :
    ENNReal.toReal (MeasureTheory.volume (weightedSimplexRegion w T)) =
      (∏ i : Fin m, w i)⁻¹ * ENNReal.toReal (MeasureTheory.volume
        {x : Fin m → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin m, x i ≤ T}) := by
  let D : (Fin m → ℝ) → (Fin m → ℝ) := fun x i => w i * x i
  have himage :
      D '' weightedSimplexRegion w T =
        {x : Fin m → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin m, x i ≤ T} :=
    OAI.PiExponent.DeterminantContradiction.weighted_simplex_region_map
      m w T hw
  have hscale :
      ENNReal.toReal (MeasureTheory.volume (D '' weightedSimplexRegion w T)) =
        (∏ i : Fin m, w i) *
          ENNReal.toReal (MeasureTheory.volume (weightedSimplexRegion w T)) :=
    OAI.PiExponent.DeterminantContradiction.diagonal_map_volume
      m w T hw
  rw [himage] at hscale
  have hp : 0 < ∏ i : Fin m, w i := Finset.prod_pos fun i hi => hw i
  calc
    ENNReal.toReal (MeasureTheory.volume (weightedSimplexRegion w T)) =
        (∏ i : Fin m, w i)⁻¹ *
          ((∏ i : Fin m, w i) *
            ENNReal.toReal (MeasureTheory.volume (weightedSimplexRegion w T))) := by
              field_simp
    _ = (∏ i : Fin m, w i)⁻¹ *
          ENNReal.toReal (MeasureTheory.volume
            {x : Fin m → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin m, x i ≤ T}) := by
              rw [← hscale]