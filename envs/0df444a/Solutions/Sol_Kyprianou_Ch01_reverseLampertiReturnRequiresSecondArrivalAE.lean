-- Prove2me | solution 1 for Kyprianou.Ch01.reverseLampertiReturnRequiresSecondArrivalAE
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T18:10:53.148557+00:00
-- url     : https://prove2.me/submissions/ebf8e45e-bc95-4393-b22b-cf896b70e256

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Theorems.Thm_Kyprianou_Ch01_compoundPoissonFirstMarkOffspringSupportAE
import Theorems.Thm_Kyprianou_Ch01_compoundPoissonFirstMarkNonzeroAEFromNoUnitOffspring
import Theorems.Thm_Kyprianou_Ch01_reverseLampertiSingleMarkedJumpWindowAE
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (rate : ℝ≥0) (hrate : 0 < rate)
    (offspring : PMF ℕ) (hNoZeroJumps : offspring 1 = 0)
    (arrival marks : ℕ → Ω → ℝ)
    (jumpLaw : Measure ℝ) [IsProbabilityMeasure jumpLaw]
    (hdriver : IsCompoundPoissonDriver arrival marks rate jumpLaw Q)
    (hSupport : jumpLaw
      {x : ℝ | ∃ k : ℕ, x = (k : ℝ) - 1} = 1)
    (hJumpMass : ∀ k : ℕ,
      jumpLaw ({((k : ℝ) - 1)} : Set ℝ) = offspring k)
    (hNoExplosion : ∀ y : ℕ, ∀ᵐ ω ∂Q,
      ∀ t : ℝ≥0, ∃ s : ℝ≥0,
        (t : ℝ≥0∞) <
          reciprocalOccupation (integerCompoundPoisson y arrival marks) s ω)
    (hBefore : ∀ (z : ℕ) (u : ℝ≥0) (ω : Ω),
      (u : ℝ) < ProbabilityTheory.arrival arrival 0 ω →
        integerCompoundPoisson z arrival marks u ω = (z : ℤ)) :
    ∀ (y : ℕ) (t : ℝ≥0), 0 < y →
      ∀ᵐ ω ∂Q,
        (compoundPoissonToBranching
          (integerCompoundPoisson y arrival marks) t ω).toNat = y →
        (y : ℝ) * (t : ℝ) <
          ProbabilityTheory.arrival arrival 0 ω ∨
        ∃ j : ℕ, marks 0 ω = (j : ℝ) - 1 ∧
          ProbabilityTheory.arrival arrival 0 ω ≤ (y : ℝ) * (t : ℝ) ∧
          ProbabilityTheory.arrival arrival 1 ω ≤
            ProbabilityTheory.arrival arrival 0 ω +
              (((y + j : ℕ) : ℝ)) * (t : ℝ) := by
  intro y t hy
  have hSupportAE :=
    Kyprianou.Ch01.compoundPoissonFirstMarkOffspringSupportAE
      Q rate hrate arrival marks jumpLaw hdriver hSupport
  have hNotZeroAE :=
    Kyprianou.Ch01.compoundPoissonFirstMarkNonzeroAEFromNoUnitOffspring
      Q rate hrate offspring hNoZeroJumps arrival marks jumpLaw
      hdriver hJumpMass
  have hWindowAE :=
    Kyprianou.Ch01.reverseLampertiSingleMarkedJumpWindowAE
      Q rate hrate arrival marks jumpLaw hdriver y t hy
  filter_upwards [hSupportAE, hNotZeroAE, hWindowAE]
    with ω hSupportMark hNotZero hWindow
  intro hReturn
  by_cases hNoArrival :
      (y : ℝ) * (t : ℝ) < ProbabilityTheory.arrival arrival 0 ω
  · exact Or.inl hNoArrival
  · right
    obtain ⟨j, hMark⟩ := hSupportMark
    refine ⟨j, hMark, le_of_not_gt hNoArrival, ?_⟩
    by_contra hNoSecond
    have hState := hWindow j hMark (le_of_not_gt hNoArrival) hNoSecond
    have hEqual : y + j - 1 = y := hState.symm.trans hReturn
    have hj : j = 1 := by omega
    subst j
    have hZero : marks 0 ω = 0 := by simpa using hMark
    exact hNotZero hZero
