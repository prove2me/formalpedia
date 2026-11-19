-- Prove2me | solution 1 for Kyprianou.Ch03.exercise36SupremumAtIndependentExponentialTime
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T15:55:54.004902+00:00
-- url     : https://prove2.me/submissions/d6f831f2-6cdd-45b1-b07a-a22661b255f8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_LevyExtrema_SBA_runSup
import Theorems.Thm_Kyprianou_Ch03_exercise36_positiveRoot
import Theorems.Thm_Kyprianou_Ch03_exercise36_multiplicativeExpTail
import Theorems.Thm_Kyprianou_Ch03_exercise36_expTailFormula
import Theorems.Thm_Kyprianou_Ch03_exercise36_positiveExpMoments
import Theorems.Thm_Kyprianou_Ch03_exercise36_zeroRootEverPassage
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
    ∃ phi : ℝ, 0 < phi ∧ L.ψ phi = q ∧
      (∀ x y : ℝ, 0 < x → 0 < y →
        let tail (z : ℝ) :=
          ((P.prod Q) {pair : Omega × OmegaE |
             z < LevyExtrema.SBA.runSup
               (fun s => L.X s pair.1) (e pair.2)}).toReal
        tail (x + y) = tail x * tail y) ∧
      (∀ x : ℝ, 0 ≤ x →
        ((P.prod Q) {pair : Omega × OmegaE |
          x < LevyExtrema.SBA.runSup
            (fun s => L.X s pair.1) (e pair.2)}).toReal =
        Real.exp (-phi * x)) ∧
      (∀ beta : ℝ, 0 ≤ beta →
        ∀ t : NNReal, Integrable
          (fun omega => Real.exp (beta * L.X t omega)) P) ∧
      (∃ phi0 : ℝ, 0 ≤ phi0 ∧ L.ψ phi0 = 0 ∧
        (∀ theta : ℝ, 0 ≤ theta →
          L.ψ theta = 0 → theta ≤ phi0) ∧
        ∀ x : ℝ, 0 ≤ x →
          (P {omega : Omega |
            ∃ t : NNReal, x < L.X t omega}).toReal =
          Real.exp (-phi0 * x)) := by
  obtain ⟨phi, hpos, hroot⟩ :=
    Kyprianou.Ch03.exercise36_positiveRoot P Q F L hNotDecreasing q hq e hExponential
  refine ⟨phi, hpos, hroot, ?_, ?_, ?_, ?_⟩
  · exact Kyprianou.Ch03.exercise36_multiplicativeExpTail
      P Q F L hNotDecreasing q hq e hExponential phi ⟨hpos, hroot⟩
  · exact Kyprianou.Ch03.exercise36_expTailFormula
      P Q F L hNotDecreasing q hq e hExponential phi ⟨hpos, hroot⟩
  · exact Kyprianou.Ch03.exercise36_positiveExpMoments P Q F L hNotDecreasing q hq e hExponential
  · exact Kyprianou.Ch03.exercise36_zeroRootEverPassage P Q F L hNotDecreasing q hq e hExponential

