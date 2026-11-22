-- Prove2me | solution 1 for Kyprianou.Ch01.lampertiForwardCylinderMarkov
-- status  : ACCEPTED   (prove)
-- author  : @coqelz
-- created : 2026-11-22T16:30:26.327778+00:00
-- url     : https://prove2.me/submissions/4ac2d0f0-8b48-4126-8596-b02c346c943d

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ForwardLampertiPaths
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Theorems.Thm_Kyprianou_Ch01_lampertiForwardMeasurableAndInitial
import Theorems.Thm_Kyprianou_Ch01_lampertiForwardCylinderMarkovProperty
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (Y : ℝ≥0 → Ω → ℕ)
    (P : ℕ → Measure Ω) (law : PopulationLaws)
    (rate : ℝ≥0) (hRate : 0 < rate)
    (offspring : PMF ℕ) (hNoNullJumps : offspring 1 = 0)
    (hBranching : HasBranchingProperty law)
    (hMarkov : IsPopulationMarkovPath Y P law)
    (hSemigroup : IsPopulationMarkovSemigroup law)
    (hGenerator : IsBranchingRateGenerator law rate offspring)
    (hInitial : ∀ y : ℕ, P y {ω | Y 0 ω = y} = 1)
    (hMeas : ∀ t : ℝ≥0, Measurable (Y t))
    (hCadlag : ∀ y : ℕ, ∀ᵐ ω ∂P y,
      IsCadlag (fun t : ℝ≥0 => Y t ω)) :
    ∀ y : ℕ,
      (∀ t : ℝ≥0, AEMeasurable (fun ω => branchingToPoisson Y t ω) (P y)) ∧
      P y {ω | branchingToPoisson Y 0 ω = y} = 1 ∧
      ∀ (m : ℕ) (u : Fin m → ℝ≥0) (v : Fin m → ℕ) (s t : ℝ≥0) (k : ℕ),
        (∀ i, u i ≤ s) →
        P y ({ω | ∀ i, branchingToPoisson Y (u i) ω = v i} ∩
            {ω | branchingToPoisson Y (s + t) ω = k}) =
          ∑' z : ℕ, P y ({ω | ∀ i, branchingToPoisson Y (u i) ω = v i} ∩
            {ω | branchingToPoisson Y s ω = z}) *
            P z {ω | branchingToPoisson Y t ω = k} := by
  intro y
  have hA := lampertiForwardMeasurableAndInitial
    Y P law rate hRate offspring hNoNullJumps hBranching hMarkov hSemigroup hGenerator hInitial hMeas hCadlag y
  have hB := lampertiForwardCylinderMarkovProperty
    Y P law rate hRate offspring hNoNullJumps hBranching hMarkov hSemigroup hGenerator hInitial hMeas hCadlag y
  exact ⟨hA.1, hA.2, fun m u v s t k hu => hB m u v s t k hu⟩
