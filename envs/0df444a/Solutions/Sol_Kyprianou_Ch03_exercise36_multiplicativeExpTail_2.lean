-- Prove2me | solution 2 for Kyprianou.Ch03.exercise36_multiplicativeExpTail
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T16:01:08.574813+00:00
-- url     : https://prove2.me/submissions/e5690e47-8af7-4c28-a3f8-607337efb982
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_LevyExtrema_SBA_runSup
import Theorems.Thm_Kyprianou_Ch03_exercise36_expTailFormula_positive
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

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
  intro phi hphi x y hx hy
  have hf := Kyprianou.Ch03.exercise36_expTailFormula_positive P Q F L hNotDecreasing
    q hq e hExponential phi hphi
  dsimp
  rw [hf (x+y) (add_pos hx hy), hf x hx, hf y hy, ← Real.exp_add]
  congr 1
  ring
