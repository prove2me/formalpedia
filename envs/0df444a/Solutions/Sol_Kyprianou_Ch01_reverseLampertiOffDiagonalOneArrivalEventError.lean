-- Prove2me | solution 1 for Kyprianou.Ch01.reverseLampertiOffDiagonalOneArrivalEventError
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T13:13:56.760805+00:00
-- url     : https://prove2.me/submissions/a0de9f6b-f118-44bf-a10d-7a7fb953c19f

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Theorems.Thm_Kyprianou_Ch01_reverseLampertiOffDiagonalOneArrivalAEAgreementOutsideSecond
import Theorems.Thm_Kyprianou_Ch01_probabilityAbsDifferenceLeExceptionOfAEAgreement
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
      |((K y (Real.toNNReal t)) k).toReal -
        (if y ≤ k + 1 then (Q {ω | marks 0 ω = ((k + 1 - y : ℕ) : ℝ) - 1 ∧
          ProbabilityTheory.arrival arrival 0 ω ≤
            (y : ℝ) * (Real.toNNReal t : ℝ)}).toReal else 0)| ≤
        (Q {ω | ∃ j : ℕ,
          marks 0 ω = (j : ℝ) - 1 ∧
          ProbabilityTheory.arrival arrival 0 ω ≤
            (y : ℝ) * (Real.toNNReal t : ℝ) ∧
          ProbabilityTheory.arrival arrival 1 ω ≤
            ProbabilityTheory.arrival arrival 0 ω +
              ((y + j : ℕ) : ℝ) * (Real.toNNReal t : ℝ)}).toReal := by
  intro y k hyk t ht
  let A : Set Ω := {ω |
    (compoundPoissonToBranching
      (integerCompoundPoisson y arrival marks)
      (Real.toNNReal t) ω).toNat = k}
  let B : Set Ω := {ω |
    y ≤ k + 1 ∧
    marks 0 ω = ((k + 1 - y : ℕ) : ℝ) - 1 ∧
    ProbabilityTheory.arrival arrival 0 ω ≤
      (y : ℝ) * (Real.toNNReal t : ℝ)}
  let E : Set Ω := {ω | ∃ j : ℕ,
    marks 0 ω = (j : ℝ) - 1 ∧
    ProbabilityTheory.arrival arrival 0 ω ≤
      (y : ℝ) * (Real.toNNReal t : ℝ) ∧
    ProbabilityTheory.arrival arrival 1 ω ≤
      ProbabilityTheory.arrival arrival 0 ω +
        ((y + j : ℕ) : ℝ) * (Real.toNNReal t : ℝ)}
  have hPath :=
    Kyprianou.Ch01.reverseLampertiOffDiagonalOneArrivalAEAgreementOutsideSecond
      Q rate hrate offspring hNoZeroJumps arrival marks jumpLaw
      hdriver hSupport hJumpMass hNoExplosion
      K hRealisation y k hyk t ht
  have hAgree : ∀ᵐ ω ∂Q,
      ω ∉ E → (ω ∈ A ↔ ω ∈ B) := by
    filter_upwards [hPath] with ω hω
    simpa only [A, B, E, Set.mem_setOf_eq] using hω
  have hBound :=
    Kyprianou.Ch01.probabilityAbsDifferenceLeExceptionOfAEAgreement
      Q A B E hAgree
  have hB :
      (Q B).toReal =
        (if y ≤ k + 1 then
          (Q {ω | marks 0 ω = ((k + 1 - y : ℕ) : ℝ) - 1 ∧
            ProbabilityTheory.arrival arrival 0 ω ≤
              (y : ℝ) * (Real.toNNReal t : ℝ)}).toReal
          else 0) := by
    by_cases hidx : y ≤ k + 1
    · simp [B, hidx, and_assoc]
    · simp [B, hidx]
  rw [hB] at hBound
  rw [hRealisation y (Real.toNNReal t) k]
  simpa only [A, E] using hBound
