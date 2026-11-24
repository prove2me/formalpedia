-- Prove2me | solution 1 for Kyprianou.Ch03.exercise36_multiplicativeExpTail
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T17:12:09.934203+00:00
-- url     : https://prove2.me/submissions/eb99edc0-a89d-4c73-b87a-cc26a01e833d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_LevyExtrema_SBA_runSup
import Theorems.Thm_Kyprianou_Ch03_exercise36_expTailFormula
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
    (∀ x y : ℝ, 0 < x → 0 < y →
        let tail (z : ℝ) :=
          ((P.prod Q) {pair : Omega × OmegaE |
             z < LevyExtrema.SBA.runSup
               (fun s => L.X s pair.1) (e pair.2)}).toReal
        tail (x + y) = tail x * tail y) := by
  refine fun phi hphi x y hx hy => ?_
  dsimp
  have htail :=
    Kyprianou.Ch03.exercise36_expTailFormula
      P Q F L hNotDecreasing q hq e hExponential phi hphi
  rw [htail (x + y) (by linarith), htail x (le_of_lt hx),
    htail y (le_of_lt hy)]
  rw [mul_add, Real.exp_add]

