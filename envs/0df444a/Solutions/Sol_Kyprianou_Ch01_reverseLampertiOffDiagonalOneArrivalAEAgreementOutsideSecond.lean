-- Prove2me | solution 1 for Kyprianou.Ch01.reverseLampertiOffDiagonalOneArrivalAEAgreementOutsideSecond
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T14:17:11.477797+00:00
-- url     : https://prove2.me/submissions/d32e6295-49cf-4f44-a409-bc6b8fef2fe7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Theorems.Thm_Kyprianou_Ch01_compoundPoissonFirstArrivalPositiveFromSurvivalAE
import Theorems.Thm_Kyprianou_Ch01_reverseLampertiNoFirstArrivalWindowAE
import Theorems.Thm_Kyprianou_Ch01_reverseLampertiSingleMarkedJumpWindowAE
import Theorems.Thm_Kyprianou_Ch01_compoundPoissonFirstMarkOffspringSupportAE
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
    (K : PopulationLaws)
    (hRealisation : ∀ (y : ℕ) (t : ℝ≥0) (k : ℕ),
      K y t k =
        Q {ω | (compoundPoissonToBranching
          (integerCompoundPoisson y arrival marks) t ω).toNat = k}) :
    ∀ (y k : ℕ), k ≠ y → ∀ (t : ℝ), 0 ≤ t →
      ∀ᵐ ω ∂Q,
        (¬ (∃ j : ℕ,
          marks 0 ω = (j : ℝ) - 1 ∧
          ProbabilityTheory.arrival arrival 0 ω ≤
            (y : ℝ) * (Real.toNNReal t : ℝ) ∧
          ProbabilityTheory.arrival arrival 1 ω ≤
            ProbabilityTheory.arrival arrival 0 ω +
              ((y + j : ℕ) : ℝ) * (Real.toNNReal t : ℝ))) →
          ((compoundPoissonToBranching
            (integerCompoundPoisson y arrival marks)
            (Real.toNNReal t) ω).toNat = k ↔
            y ≤ k + 1 ∧
            marks 0 ω = ((k + 1 - y : ℕ) : ℝ) - 1 ∧
            ProbabilityTheory.arrival arrival 0 ω ≤
              (y : ℝ) * (Real.toNNReal t : ℝ)) := by
  intro y k hyk t ht
  have hPos := Kyprianou.Ch01.compoundPoissonFirstArrivalPositiveFromSurvivalAE
    Q rate hrate arrival marks jumpLaw hdriver
  have hMark :=
    Kyprianou.Ch01.compoundPoissonFirstMarkOffspringSupportAE
      Q rate hrate arrival marks jumpLaw hdriver hSupport
  have hNoFirst :=
    Kyprianou.Ch01.reverseLampertiNoFirstArrivalWindowAE
      Q rate hrate arrival marks jumpLaw hdriver y (Real.toNNReal t)
  by_cases hy0 : y = 0
  · subst y
    filter_upwards [hPos, hNoFirst] with ω hp hn hExc
    have hBefore :
        ((0 : ℕ) : ℝ) * (Real.toNNReal t : ℝ) <
          ProbabilityTheory.arrival arrival 0 ω := by
      simpa using hp
    have hY := hn hBefore
    constructor
    · intro hk
      have hEq : 0 = k := by simpa only [hY] using hk
      exact (hyk hEq.symm).elim
    · rintro ⟨_, _, hArr⟩
      have hBad : ProbabilityTheory.arrival arrival 0 ω ≤ 0 := by
        simpa using hArr
      exact (not_le.mpr hp hBad).elim
  · have hy : 0 < y := Nat.pos_of_ne_zero hy0
    have hOne :=
      Kyprianou.Ch01.reverseLampertiSingleMarkedJumpWindowAE
        Q rate hrate arrival marks jumpLaw hdriver
        y (Real.toNNReal t) hy
    filter_upwards [hMark, hNoFirst, hOne] with ω hm hn ho hExc
    by_cases hArr :
        ProbabilityTheory.arrival arrival 0 ω ≤
          (y : ℝ) * (Real.toNNReal t : ℝ)
    · rcases hm with ⟨j, hj⟩
      have hSecond : ¬ (ProbabilityTheory.arrival arrival 1 ω ≤
          ProbabilityTheory.arrival arrival 0 ω +
            ((y + j : ℕ) : ℝ) * (Real.toNNReal t : ℝ)) := by
        intro hS
        exact hExc ⟨j, hj, hArr, hS⟩
      have hY := ho j hj hArr hSecond
      constructor
      · intro hk
        have hEq : y + j - 1 = k := by simpa only [hY] using hk
        have hIdx : k + 1 - y = j := by omega
        refine ⟨by omega, ?_, hArr⟩
        simpa only [hIdx] using hj
      · rintro ⟨hIdx, hMarkEq, _⟩
        have hCast : (j : ℝ) = ((k + 1 - y : ℕ) : ℝ) := by
          linarith [hj, hMarkEq]
        have hJ : j = k + 1 - y := by exact_mod_cast hCast
        have hEq : y + j - 1 = k := by omega
        simpa only [hY, hEq]
    · have hBefore :
          (y : ℝ) * (Real.toNNReal t : ℝ) <
            ProbabilityTheory.arrival arrival 0 ω := lt_of_not_ge hArr
      have hY := hn hBefore
      constructor
      · intro hk
        have hEq : y = k := by simpa only [hY] using hk
        exact (hyk hEq.symm).elim
      · rintro ⟨_, _, hAt⟩
        exact (hArr hAt).elim
