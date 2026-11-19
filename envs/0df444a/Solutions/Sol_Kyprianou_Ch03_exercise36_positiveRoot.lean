-- Prove2me | solution 1 for Kyprianou.Ch03.exercise36_positiveRoot
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T15:56:20.767437+00:00
-- url     : https://prove2.me/submissions/3f130058-79d5-4584-81e0-5784c7f1bbce

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_LevyExtrema_SBA_runSup
import Theorems.Thm_Kyprianou_Ch03_firstPassageTransform_maximalRootExistence
import Theorems.Thm_Kyprianou_Ch03_exponentRegularity_zeroAtOrigin
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch03

theorem solution
{Omega OmegaE : Type}
    [MeasurableSpace Omega] [MeasurableSpace OmegaE]
    (P : Measure Omega) (Q : Measure OmegaE)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hNotDecreasing : ¬ (∀ᵐ omega : Omega ∂P,
      Antitone (fun t : NNReal => L.X t omega)))
    (q : ℝ) (hq : 0 < q)
    (e : OmegaE → NNReal)
    (hExponential : ∀ t : NNReal,
      (Q {eta : OmegaE | t < e eta}).toReal =
        Real.exp (-q * (t : ℝ))) :
    ∃ phi : ℝ, 0 < phi ∧ L.ψ phi = q := by
  obtain ⟨phi, hnonneg, hroot, hmax⟩ :=
    Kyprianou.Ch03.firstPassageTransform_maximalRootExistence
      P F L hNotDecreasing q (le_of_lt hq)
  refine ⟨phi, ?_, hroot⟩
  rcases eq_or_lt_of_le hnonneg with hzero | hpos
  · exfalso
    have hzeroPsi : L.ψ phi = 0 := by
      rw [← hzero]
      exact Kyprianou.Ch03.exponentRegularity_zeroAtOrigin P F L
    rw [hroot] at hzeroPsi
    exact (ne_of_gt hq) hzeroPsi
  · exact hpos

