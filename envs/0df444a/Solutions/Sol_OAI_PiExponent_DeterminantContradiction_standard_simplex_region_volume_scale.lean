-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.standard_simplex_region_volume_scale
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-17T03:19:01.223424+00:00
-- url     : https://prove2.me/submissions/bc09276b-0838-441d-8d49-23443c40b28c

import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplex_region_eq_smul_image
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_volume_smul_image_fin_real

open scoped BigOperators Topology

theorem solution
    (m : ℕ) (T : ℝ) (hT : 0 ≤ T) :
    ENNReal.toReal (MeasureTheory.volume
      {x : Fin m → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin m, x i ≤ T}) =
      T ^ m * ENNReal.toReal (MeasureTheory.volume
        {x : Fin m → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin m, x i ≤ (1 : ℝ)}) := by
  rw [OAI.PiExponent.DeterminantContradiction.simplex_region_eq_smul_image m T hT]
  exact OAI.PiExponent.DeterminantContradiction.volume_smul_image_fin_real m T hT
    {x : Fin m → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin m, x i ≤ (1 : ℝ)}