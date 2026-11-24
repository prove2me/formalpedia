-- Prove2me | solution 1 for Kyprianou.Ch01.sequenceDirectBranchingCountMeasurable
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-24T02:51:48.904437+00:00
-- url     : https://prove2.me/submissions/370cf22f-3696-4edc-a7f2-14039388e8c3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Theorems.Thm_Kyprianou_Ch01_sequenceDirectBranchingZMeasurable

open MeasureTheory ProbabilityTheory Kyprianou.Ch01
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (z : ℕ) (s : ℝ≥0) :
    Measurable
      (fun seq : (ℕ → ℝ) × (ℕ → ℝ) =>
        (compoundPoissonToBranching
          (integerCompoundPoisson z
            (fun n (σ : (ℕ → ℝ) × (ℕ → ℝ)) => σ.1 n)
            (fun n (σ : (ℕ → ℝ) × (ℕ → ℝ)) => σ.2 n))
          s seq).toNat) := by
  have hZ := sequenceDirectBranchingZMeasurable z s
  have hto : Measurable (Int.toNat : ℤ → ℕ) := measurable_of_countable _
  exact hto.comp hZ
