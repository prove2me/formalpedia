-- Prove2me | solution 1 for Kyprianou.Ch01.sequenceIntegerWalkJointlyMeasurable
-- status  : ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-24T09:58:55.550373+00:00
-- url     : https://prove2.me/submissions/c96fccc3-10a3-477c-ac94-dd7e61b5bdc3

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Theorems.Thm_Kyprianou_Ch01_compoundPoissonOfMeasurableSequences

open MeasureTheory ProbabilityTheory Kyprianou.Ch01
open scoped NNReal ENNReal
set_option autoImplicit false
set_option maxHeartbeats 2000000

theorem solution
    (z : ℕ) :
    Measurable
      (fun p : ((ℕ → ℝ) × (ℕ → ℝ)) × ℝ≥0 =>
        integerCompoundPoisson z
          (fun n (seq : (ℕ → ℝ) × (ℕ → ℝ)) => seq.1 n)
          (fun n (seq : (ℕ → ℝ) × (ℕ → ℝ)) => seq.2 n)
          p.2 p.1) := by
  have hArr : ∀ n, Measurable (fun seq : (ℕ → ℝ) × (ℕ → ℝ) => seq.1 n) := by
    intro n
    exact (measurable_pi_apply n).comp measurable_fst
  have hMk : ∀ n, Measurable (fun seq : (ℕ → ℝ) × (ℕ → ℝ) => seq.2 n) := by
    intro n
    exact (measurable_pi_apply n).comp measurable_snd
  have hξ :=
    compoundPoissonOfMeasurableSequences
      (fun n (seq : (ℕ → ℝ) × (ℕ → ℝ)) => seq.1 n)
      (fun n (seq : (ℕ → ℝ) × (ℕ → ℝ)) => seq.2 n) hArr hMk
  have hsum :
      Measurable
        (fun p : ((ℕ → ℝ) × (ℕ → ℝ)) × ℝ≥0 =>
          (z : ℝ) +
            ProbabilityTheory.compoundPoisson 0
              (fun n (seq : (ℕ → ℝ) × (ℕ → ℝ)) => seq.1 n)
              (fun n (seq : (ℕ → ℝ) × (ℕ → ℝ)) => seq.2 n)
              (p.2 : ℝ) p.1) :=
    measurable_const.add hξ
  simpa [integerCompoundPoisson] using hsum.floor
