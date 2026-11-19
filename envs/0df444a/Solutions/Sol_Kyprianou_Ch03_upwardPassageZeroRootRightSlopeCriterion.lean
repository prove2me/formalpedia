-- Prove2me | solution 1 for Kyprianou.Ch03.upwardPassageZeroRootRightSlopeCriterion
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T17:11:39.898974+00:00
-- url     : https://prove2.me/submissions/b6a15f66-1e1e-4ffd-9754-b4a2287191c6

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_Kyprianou_Ch03_firstPassageZero_maximalRootExistence
import Theorems.Thm_Kyprianou_Ch03_rootSlope_zeroImpliesRightSlope
import Theorems.Thm_Kyprianou_Ch03_rootSlope_rightSlopeImpliesZero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch03

theorem solution
{Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hNotDecreasing : ¬ (∀ᵐ omega : Omega ∂P,
      Antitone (fun t : NNReal => L.X t omega))) :
    ∃ phi : ℝ,
      0 ≤ phi ∧ L.ψ phi = 0 ∧
      (∀ theta : ℝ, 0 ≤ theta → L.ψ theta = 0 → theta ≤ phi) ∧
      (phi = 0 ↔
        ∀ a : ℝ, a < 0 →
          ∃ delta : ℝ, 0 < delta ∧
            ∀ theta : ℝ, 0 < theta → theta < delta →
              a < L.ψ theta / theta) := by
  obtain ⟨phi, hpos, hzero, hmax⟩ :=
    Kyprianou.Ch03.firstPassageZero_maximalRootExistence P F L hNotDecreasing
  refine ⟨phi, hpos, hzero, hmax, Iff.intro ?_ ?_⟩
  · exact Kyprianou.Ch03.rootSlope_zeroImpliesRightSlope
      P F L hNotDecreasing phi ⟨hpos, hzero, hmax⟩
  · exact Kyprianou.Ch03.rootSlope_rightSlopeImpliesZero
      P F L hNotDecreasing phi ⟨hpos, hzero, hmax⟩
