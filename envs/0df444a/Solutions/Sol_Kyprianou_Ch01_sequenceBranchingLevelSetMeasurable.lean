-- Prove2me | solution 1 for Kyprianou.Ch01.sequenceBranchingLevelSetMeasurable
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-24T02:31:27.975223+00:00
-- url     : https://prove2.me/submissions/c9d8c9c4-12db-4a31-b5a3-d9d80ad7e185
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Theorems.Thm_Kyprianou_Ch01_sequenceBranchingCountMeasurable

open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (z : ℕ) (s : ℝ≥0) (m : ℕ) :
    MeasurableSet
      {seq : (ℕ → ℝ) × (ℕ → ℝ) |
        (compoundPoissonToBranching
          (integerCompoundPoisson z
            (fun n (_ : Unit) => seq.1 n)
            (fun n (_ : Unit) => seq.2 n))
          s ()).toNat = m} := by
  have hcount := sequenceBranchingCountMeasurable z s
  change MeasurableSet
    ((fun seq : (ℕ → ℝ) × (ℕ → ℝ) =>
        (compoundPoissonToBranching
          (integerCompoundPoisson z
            (fun n (_ : Unit) => seq.1 n)
            (fun n (_ : Unit) => seq.2 n))
          s ()).toNat) ⁻¹' {m})
  exact hcount (measurableSet_singleton m)
