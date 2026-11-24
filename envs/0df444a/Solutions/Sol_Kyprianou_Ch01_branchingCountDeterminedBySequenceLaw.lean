-- Prove2me | solution 1 for Kyprianou.Ch01.branchingCountDeterminedBySequenceLaw
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-24T01:56:13.03626+00:00
-- url     : https://prove2.me/submissions/0cf6ec24-59ae-4dab-ad78-225e4ad82aa2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Theorems.Thm_Kyprianou_Ch01_branchingCountFactorsThroughSequences
import Theorems.Thm_Kyprianou_Ch01_sequenceBranchingLevelSetMeasurable

open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (rate : ℝ≥0)
    (arrival marks : ℕ → Ω → ℝ)
    (jumpLaw : Measure ℝ) [IsProbabilityMeasure jumpLaw]
    (hNoExplosion : ∀ y : ℕ, ∀ᵐ ω ∂Q,
      ∀ t : ℝ≥0, ∃ s : ℝ≥0,
        (t : ℝ≥0∞) <
          reciprocalOccupation (integerCompoundPoisson y arrival marks) s ω)
    (hTailDriver : IsCompoundPoissonDriver
      (fun n w => arrival (n + 1) w)
      (fun n w => marks (n + 1) w) rate jumpLaw Q)
    (ν : Measure ((ℕ → ℝ) × (ℕ → ℝ)))
    (hOrig : HasLaw (fun w => (fun n => arrival n w, fun n => marks n w)) ν Q)
    (hShift : HasLaw
      (fun w => (fun n => arrival (n + 1) w, fun n => marks (n + 1) w)) ν Q)
    (z : ℕ) (s : ℝ≥0) (m : ℕ) :
    Q {ω | (compoundPoissonToBranching
        (integerCompoundPoisson z
          (fun n w => arrival (n + 1) w)
          (fun n w => marks (n + 1) w)) s ω).toNat = m} =
      Q {ω | (compoundPoissonToBranching
        (integerCompoundPoisson z arrival marks) s ω).toNat = m} := by
  have hfac :=
    branchingCountFactorsThroughSequences Q rate arrival marks jumpLaw hNoExplosion hTailDriver
      ν hOrig hShift z s m
  have hm : MeasurableSet
      {seq : (ℕ → ℝ) × (ℕ → ℝ) |
        (branchingCountOfSequences z s seq).toNat = m} := by
    simpa [branchingCountOfSequences] using
      sequenceBranchingLevelSetMeasurable z s m
  have hshift_set :
      {ω | (compoundPoissonToBranching
          (integerCompoundPoisson z
            (fun n w => arrival (n + 1) w)
            (fun n w => marks (n + 1) w)) s ω).toNat = m} =
        {ω | (branchingCountOfSequences z s
            (fun n => arrival (n + 1) ω, fun n => marks (n + 1) ω)).toNat = m} := by
    ext ω
    simp [hfac.1 ω]
  have horig_set :
      {ω | (compoundPoissonToBranching
          (integerCompoundPoisson z arrival marks) s ω).toNat = m} =
        {ω | (branchingCountOfSequences z s
            (fun n => arrival n ω, fun n => marks n ω)).toNat = m} := by
    ext ω
    simp [hfac.2 ω]
  rw [hshift_set, horig_set, hShift.measure_eq hm, hOrig.measure_eq hm]
