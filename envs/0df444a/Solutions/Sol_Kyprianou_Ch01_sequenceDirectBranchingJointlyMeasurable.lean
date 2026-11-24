-- Prove2me | solution 1 for Kyprianou.Ch01.sequenceDirectBranchingJointlyMeasurable
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-24T05:30:40.091799+00:00
-- url     : https://prove2.me/submissions/b68b2aa8-b709-4fbe-a987-05272ab88b3c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Theorems.Thm_Kyprianou_Ch01_sequenceIntegerWalkJointlyMeasurable
import Theorems.Thm_Kyprianou_Ch01_lampertiImageOfMeasurableWalk

open MeasureTheory ProbabilityTheory Kyprianou.Ch01
open scoped NNReal ENNReal
set_option autoImplicit false
set_option maxHeartbeats 4000000

private noncomputable abbrev seqLatticeWalk (z : ℕ) :
    ℝ≥0 → ((ℕ → ℝ) × (ℕ → ℝ)) → ℤ :=
  integerCompoundPoisson z
    (fun n (σ : (ℕ → ℝ) × (ℕ → ℝ)) => σ.1 n)
    (fun n (σ : (ℕ → ℝ) × (ℕ → ℝ)) => σ.2 n)

theorem solution
    (z : ℕ) :
    Measurable
      (fun p : ((ℕ → ℝ) × (ℕ → ℝ)) × ℝ≥0 =>
        compoundPoissonToBranching
          (integerCompoundPoisson z
            (fun n (σ : (ℕ → ℝ) × (ℕ → ℝ)) => σ.1 n)
            (fun n (σ : (ℕ → ℝ) × (ℕ → ℝ)) => σ.2 n))
          p.2 p.1) := by
  have hwalk : Measurable (fun p : ((ℕ → ℝ) × (ℕ → ℝ)) × ℝ≥0 =>
      seqLatticeWalk z p.2 p.1) := by
    simpa [seqLatticeWalk] using sequenceIntegerWalkJointlyMeasurable z
  simpa [seqLatticeWalk] using
    lampertiImageOfMeasurableWalk (seqLatticeWalk z) hwalk
