-- Prove2me | solution 1 for Kyprianou.Ch03.rootSlope_zeroImpliesRightSlope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T17:42:46.282067+00:00
-- url     : https://prove2.me/submissions/c57bc90d-2d5d-4bf0-ac72-72b982c3dffb

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_Kyprianou_Ch03_firstPassageZero_consequence3
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
    ∀ (phi : ℝ), (0 ≤ phi ∧ L.ψ phi = 0 ∧ (∀ theta : ℝ, 0 ≤ theta → L.ψ theta = 0 → theta ≤ phi)) →
      phi = 0 → (∀ a : ℝ, a < 0 →
          ∃ delta : ℝ, 0 < delta ∧
            ∀ theta : ℝ, 0 < theta → theta < delta →
              a < L.ψ theta / theta) := by
  intro phi hRoot hPhi a ha
  have hPsi : ∀ theta : ℝ, 0 ≤ theta → 0 ≤ L.ψ theta :=
    (Kyprianou.Ch03.firstPassageZero_consequence3
      P F L hNotDecreasing phi hRoot).mp hPhi
  refine ⟨1, by norm_num, ?_⟩
  refine fun theta htheta _ => ?_
  exact lt_of_lt_of_le ha
    (div_nonneg (hPsi theta (le_of_lt htheta)) (le_of_lt htheta))

