-- Prove2me | solution 1 for Kyprianou.Ch01.branchingCumulantFiniteHorizonRegular
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T10:40:29.295668+00:00
-- url     : https://prove2.me/submissions/04252e8d-e9d0-4ecc-96b0-39271f863d06

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Theorems.Thm_Kyprianou_Ch01_branchingOneAncestorGeneratorFromRates
import Theorems.Thm_Kyprianou_Ch01_branchingU_timeContinuous
import Theorems.Thm_Kyprianou_Ch01_branchingU_evolution_derivative
import Theorems.Thm_Kyprianou_Ch01_branchingU_positive
open Kyprianou.Ch01 MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (rate : ℝ≥0) (hrate : 0 < rate) (offspring : PMF ℕ)
    (hNoZeroJumps : offspring 1 = 0)
    (K : PopulationLaws)
    (hBranch : HasBranchingProperty K)
    (hSemi : IsPopulationMarkovSemigroup K)
    (hInit : ∀ y : ℕ, K y 0 = PMF.pure y)
    (hGen : IsBranchingRateGenerator K rate offspring)
    (hPos : ∀ t : ℝ≥0, ∀ q : ℝ, 0 < q →
       0 < branchingLaplace K 1 t q)
    (hBelow : ∀ t : ℝ≥0, ∀ q : ℝ, 0 < q →
       branchingLaplace K 1 t q < 1)
    (T : ℝ≥0) (q : ℝ) (hq : 0 < q) :
    let f : ℝ → ℝ := fun s => branchingU K (Real.toNNReal s) q
    ContinuousOn f (Set.Icc 0 (T : ℝ)) ∧
    (∀ s ∈ Set.Icc 0 (T : ℝ), 0 < f s) ∧
    (∀ s ∈ Set.Ico 0 (T : ℝ),
      HasDerivWithinAt f
        (branchingMechanism (rate : ℝ) offspring (f s))
        (Set.Ici s) s) := by
  dsimp
  have hGR : ∀ z : ℝ, 0 < z →
      HasDerivWithinAt
        (fun s : ℝ => branchingLaplace K 1 (Real.toNNReal s) z)
        (-(branchingMechanism (rate : ℝ) offspring z) * Real.exp (-z))
        (Set.Ici 0) 0 :=
    Kyprianou.Ch01.branchingOneAncestorGeneratorFromRates
      K rate offspring hrate hNoZeroJumps (hInit 1) hGen
  have hRP : 0 < (rate : ℝ) := by exact_mod_cast hrate
  have hLap (t : ℝ≥0) (z : ℝ) (hz : 0 < z) :
      0 < branchingLaplace K 1 t z ∧
        branchingLaplace K 1 t z < 1 :=
    ⟨hPos t z hz, hBelow t z hz⟩
  have hc := Kyprianou.Ch01.branchingU_timeContinuous
    K (rate : ℝ) offspring hBranch hSemi hInit hLap hGR q hq
  have hd := Kyprianou.Ch01.branchingU_evolution_derivative
    K (rate : ℝ) offspring hRP hBranch hSemi hInit hLap hGR q hq
  refine ⟨hc.mono (by intro x hx; exact hx.1), ?_, ?_⟩
  · intro s hs
    exact Kyprianou.Ch01.branchingU_positive
      K hLap (Real.toNNReal s) q hq
  · intro s hs
    have hs0 : 0 ≤ s := hs.1
    have hsEq : ((Real.toNNReal s : ℝ≥0) : ℝ) = s :=
      Real.coe_toNNReal s hs0
    have hder := hd (Real.toNNReal s)
    rw [hsEq] at hder
    exact hder.mono (by intro u hu; exact le_trans hs0 hu)
