-- Prove2me | solution 1 for Kyprianou.Ch03.exercise36_expTailFormula
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T17:37:18.896112+00:00
-- url     : https://prove2.me/submissions/bc3d12ef-5d35-46a4-8e0b-4bec8bd216b8

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_LevyExtrema_SBA_runSup
import Theorems.Thm_Kyprianou_Ch03_exercise36_expTailFormula_positive
import Theorems.Thm_Kyprianou_Ch03_exercise36_expTailFormula_atZero
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
    ∀ (phi : ℝ), (0 < phi ∧ L.ψ phi = q) →
    (∀ x : ℝ, 0 ≤ x →
        ((P.prod Q) {pair : Omega × OmegaE |
          x < LevyExtrema.SBA.runSup
            (fun s => L.X s pair.1) (e pair.2)}).toReal =
        Real.exp (-phi * x)) := by
  intro phi hphi x hx
  rcases eq_or_lt_of_le hx with hzero | hpos
  · subst x
    simpa using
      (Kyprianou.Ch03.exercise36_expTailFormula_atZero
        P Q F L hNotDecreasing q hq e hExponential phi hphi)
  · exact Kyprianou.Ch03.exercise36_expTailFormula_positive
      P Q F L hNotDecreasing q hq e hExponential phi hphi x hpos

