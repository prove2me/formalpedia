-- Prove2me | solution 1 for Kyprianou.Ch01.lampertiBranchingToCompoundPoissonPathLawWithoutMoment
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T12:49:28.843662+00:00
-- url     : https://prove2.me/submissions/162ca945-20f9-49f8-9458-af853961ee26
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ForwardLampertiPaths
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Theorems.Thm_Kyprianou_Ch01_lampertiForwardFiniteDimensionalLawWithoutMoment
import Theorems.Thm_Kyprianou_Ch01_lampertiForwardPathMapsMeasurableWithoutMoment
import Theorems.Thm_Kyprianou_Ch01_pathMeasureEqOfFiniteDimensionalLawsV2
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (Y : ℝ≥0 → Ω → ℕ)
    (P : ℕ → Measure Ω) (law : PopulationLaws)
    (Q : Measure Ω') [IsProbabilityMeasure Q]
    (rate : ℝ≥0) (hRate : 0 < rate)
    (offspring : PMF ℕ) (hNoNullJumps : offspring 1 = 0)
    (hBranching : HasBranchingProperty law)
    (hMarkov : IsPopulationMarkovPath Y P law)
    (hSemigroup : IsPopulationMarkovSemigroup law)
    (hGenerator : IsBranchingRateGenerator law rate offspring)
    (hInitial : ∀ y : ℕ, P y {ω | Y 0 ω = y} = 1)
    (hMeas : ∀ t : ℝ≥0, Measurable (Y t))
    (hCadlag : ∀ y : ℕ, ∀ᵐ ω ∂P y,
      IsCadlag (fun t : ℝ≥0 => Y t ω))
    (arrival marks : ℕ → Ω' → ℝ)
    (jumpLaw : Measure ℝ) [IsProbabilityMeasure jumpLaw]
    (hDriver : IsCompoundPoissonDriver
      arrival marks rate jumpLaw Q)
    (hSupport : jumpLaw
      {x : ℝ | ∃ k : ℕ, x = (k : ℝ) - 1} = 1)
    (hJumpMass : ∀ k : ℕ,
      jumpLaw ({((k : ℝ) - 1)} : Set ℝ) = offspring k) :
    ∀ y : ℕ,
      (P y).map
        (fun ω => fun t : ℝ≥0 => (branchingToPoisson Y t ω : ℤ)) =
      Q.map
        (fun ω => fun t : ℝ≥0 =>
          stoppedIntegerCompoundPoisson y arrival marks t ω) := by
  intro y
  let F : Ω → (ℝ≥0 → ℤ) :=
    fun ω t => (branchingToPoisson Y t ω : ℤ)
  let G : Ω' → (ℝ≥0 → ℤ) :=
    fun ω t => stoppedIntegerCompoundPoisson y arrival marks t ω
  letI : IsProbabilityMeasure (P y) := hMarkov.1 y
  have hMaps :=
    Kyprianou.Ch01.lampertiForwardPathMapsMeasurableWithoutMoment
      Y P law Q rate hRate offspring hNoNullJumps
      hBranching hMarkov hSemigroup hGenerator hInitial
      hMeas hCadlag arrival marks jumpLaw hDriver hSupport hJumpMass y
  have hJoint : ∀ n : ℕ, ∀ times : Fin n → ℝ≥0,
      (P y).map (fun ω => fun i : Fin n => F ω (times i)) =
      Q.map (fun ω => fun i : Fin n => G ω (times i)) := by
    intro n times
    simpa [F, G] using
      Kyprianou.Ch01.lampertiForwardFiniteDimensionalLawWithoutMoment
        Y P law Q rate hRate offspring hNoNullJumps
      hBranching hMarkov hSemigroup hGenerator hInitial
      hMeas hCadlag arrival marks jumpLaw hDriver hSupport hJumpMass y n times
  simpa [F, G] using
    Kyprianou.Ch01.pathMeasureEqOfFiniteDimensionalLawsV2
      (P y) Q F G hMaps.1 hMaps.2 hJoint
