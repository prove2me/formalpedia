-- Prove2me | solution 1 for Kyprianou.Ch03.levy_natFiltr_rightGerm_le_completed
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-24T04:07:34.710798+00:00
-- url     : https://prove2.me/submissions/3ceaf09a-0ad6-46f2-b7a3-4221b8253a6a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
import Definitions.Def_DurrettProbability_Brownian
import Theorems.Thm_Kyprianou_Ch03_levy_rightGerm_le_natFiltr_join_shiftedGerm
import Theorems.Thm_Kyprianou_Ch03_levy_shiftedGerm_le_nullCompletion

open MeasureTheory ProbabilityTheory DurrettProbability
open scoped NNReal

set_option autoImplicit false

/-!
Right-germ inclusion for Lévy natural filtrations.

Reduction (shift + Blumenthal):
1. Structural: `⨅_{s>t} G_s ≤ G_t ⊔ germ(Y)` for `Y_u = X_{t+u}-X_t`.
2. Probabilistic: `germ(Y) ≤ Null` by Blumenthal for the shifted Lévy process.
3. Join: `G_t ⊔ germ(Y) ≤ G_t ⊔ Null`.
-/

open Kyprianou.Ch03 in
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal -> Omega -> Real)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (t : NNReal) :
    (⨅ s : NNReal, ⨅ (_ : t < s), PerfCorrMSQ.natFiltr X s) ≤
      PerfCorrMSQ.natFiltr X t ⊔
        MeasurableSpace.generateFrom
          {A : Set Omega |
            exists N : Set Omega,
              MeasurableSet N ∧ P N = 0 ∧ A ⊆ N} := by
  have hStruct := levy_rightGerm_le_natFiltr_join_shiftedGerm (Omega := Omega) X t
  have hNull := levy_shiftedGerm_le_nullCompletion P X hX t
  exact hStruct.trans (sup_le_sup_left hNull _)
