-- Prove2me | solution 1 for Kyprianou.Ch01.sequenceDirectBranchingZMeasurable
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-24T05:28:30.199804+00:00
-- url     : https://prove2.me/submissions/1671472e-b54a-4f1d-911e-9a94a60f437a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Theorems.Thm_Kyprianou_Ch01_sequenceDirectBranchingJointlyMeasurable

open MeasureTheory ProbabilityTheory Kyprianou.Ch01
open scoped NNReal ENNReal
set_option autoImplicit false
set_option maxHeartbeats 4000000

theorem solution
    (z : ℕ) (s : ℝ≥0) :
    Measurable
      (fun seq : (ℕ → ℝ) × (ℕ → ℝ) =>
        compoundPoissonToBranching
          (integerCompoundPoisson z
            (fun n (σ : (ℕ → ℝ) × (ℕ → ℝ)) => σ.1 n)
            (fun n (σ : (ℕ → ℝ) × (ℕ → ℝ)) => σ.2 n))
          s seq) := by
  have hJ := sequenceDirectBranchingJointlyMeasurable z
  have hpair :
      Measurable (fun seq : (ℕ → ℝ) × (ℕ → ℝ) => (seq, s)) :=
    measurable_id.prodMk measurable_const
  change Measurable
    ((fun p : ((ℕ → ℝ) × (ℕ → ℝ)) × ℝ≥0 =>
        compoundPoissonToBranching
          (integerCompoundPoisson z
            (fun n (σ : (ℕ → ℝ) × (ℕ → ℝ)) => σ.1 n)
            (fun n (σ : (ℕ → ℝ) × (ℕ → ℝ)) => σ.2 n))
          p.2 p.1) ∘ fun seq => (seq, s))
  exact hJ.comp hpair
