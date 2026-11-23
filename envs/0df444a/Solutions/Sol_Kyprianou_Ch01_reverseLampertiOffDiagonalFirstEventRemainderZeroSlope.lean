-- Prove2me | solution 1 for Kyprianou.Ch01.reverseLampertiOffDiagonalFirstEventRemainderZeroSlope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T12:46:32.837822+00:00
-- url     : https://prove2.me/submissions/f994e48e-46e8-4f8c-a5bc-721eb009ac37

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Theorems.Thm_Kyprianou_Ch01_reverseLampertiOffDiagonalMultipleArrivalErrorBound
import Theorems.Thm_Kyprianou_Ch01_absLinearSmallFactorHasZeroRightDeriv
import Theorems.Thm_Kyprianou_Ch01_pmfMarkedSecondEventFactorTendsZero
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
    ∀ (y k : ℕ), k ≠ y →
      HasDerivWithinAt
        (fun t : ℝ =>
          ((K y (Real.toNNReal t)) k).toReal -
            (if y ≤ k + 1 then (offspring (k + 1 - y)).toReal else 0) *
              (1 - Real.exp (-(((rate : ℝ) * (y : ℝ)) *
                (Real.toNNReal t : ℝ)))))
        0 (Set.Ici 0) 0 := by
  intro y k hyk
  let a : ℝ := (rate : ℝ) * (y : ℝ)
  let D : ℝ → ℝ := fun t =>
    ((K y (Real.toNNReal t)) k).toReal -
      (if y ≤ k + 1 then (offspring (k + 1 - y)).toReal else 0) *
        (1 - Real.exp (-(a * (Real.toNNReal t : ℝ))))
  let H : ℝ → ℝ := fun t => ∑' j : ℕ, (offspring j).toReal *
    (1 - Real.exp (-((rate : ℝ) * (((y + j : ℕ) : ℝ)) * t)))
  have hSmall : Tendsto H
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    simpa only [H] using
      (Kyprianou.Ch01.pmfMarkedSecondEventFactorTendsZero
        offspring rate y)
  have hBound (t : ℝ) (ht : 0 ≤ t) :
      |D t| ≤ a * t * H t := by
    simpa only [D, a, H] using
      (Kyprianou.Ch01.reverseLampertiOffDiagonalMultipleArrivalErrorBound
        Q rate hrate offspring hNoZeroJumps arrival marks
        jumpLaw hdriver hSupport hJumpMass hNoExplosion
        K hRealisation y k hyk t ht)
  have hDeriv :=
    Kyprianou.Ch01.absLinearSmallFactorHasZeroRightDeriv
      D H a hSmall hBound
  simpa only [D, a] using hDeriv
