-- Prove2me | solution 1 for Kyprianou.Ch01.integerCompoundPoissonSingleMarkedSourceInterval
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T15:15:59.370823+00:00
-- url     : https://prove2.me/submissions/15e3fb7c-af8c-453a-b465-a0bb54eccef8

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Definitions.Def_LeanLevy_Processes_PiecewisePath
import Theorems.Thm_Kyprianou_Ch01_sourceJumpCountMonotoneAndLtIffPublic
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type*}
    (y j : ℕ) (arrival marks : ℕ → Ω → ℝ) (ω : Ω)
    (hMono : StrictMono (fun n => ProbabilityTheory.arrival arrival n ω))
    (hTop : Tendsto (fun n => ProbabilityTheory.arrival arrival n ω) atTop atTop)
    (hMark : marks 0 ω = (j : ℝ) - 1)
    (hy : 0 < y) :
    ∀ u : ℝ≥0,
      ProbabilityTheory.arrival arrival 0 ω ≤ (u : ℝ) →
      (u : ℝ) < ProbabilityTheory.arrival arrival 1 ω →
      integerCompoundPoisson y arrival marks u ω =
        ((y + j - 1 : ℕ) : ℤ) := by
  intro u hu0 hu1
  let T : ℕ → ℝ := fun n => ProbabilityTheory.arrival arrival n ω
  have hc := (Kyprianou.Ch01.sourceJumpCountMonotoneAndLtIffPublic
    T hMono hTop).1
  have hc0 : 0 < ProbabilityTheory.jumpCount T (u : ℝ) :=
    (hc 0 (u : ℝ)).2 hu0
  have hc1 : ¬ 1 < ProbabilityTheory.jumpCount T (u : ℝ) := by
    intro h
    exact (not_le_of_gt hu1) ((hc 1 (u : ℝ)).1 h)
  have hcEq : ProbabilityTheory.jumpCount T (u : ℝ) = 1 := by omega
  have hCP :
      ProbabilityTheory.compoundPoisson 0 arrival marks (u : ℝ) ω =
        marks 0 ω := by
    simp [ProbabilityTheory.compoundPoisson,
      ProbabilityTheory.piecewisePath, T, hcEq]
  have hNat : 1 ≤ y + j := by omega
  have hReal :
      (y : ℝ) + ((j : ℝ) - 1) =
        (((y + j - 1 : ℕ) : ℤ) : ℝ) := by
    push_cast [Nat.cast_sub hNat]
    ring
  simp [integerCompoundPoisson, hCP, hMark, hReal]
