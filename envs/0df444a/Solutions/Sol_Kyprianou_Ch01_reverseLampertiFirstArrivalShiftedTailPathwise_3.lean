-- Prove2me | solution 3 for Kyprianou.Ch01.reverseLampertiFirstArrivalShiftedTailPathwise
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T18:20:14.915953+00:00
-- url     : https://prove2.me/submissions/2fe71564-da85-46c3-8f00-e1ec25a5aa64
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Theorems.Thm_Kyprianou_Ch01_compoundPoissonDriverArrivalStrictMonoDivergesPublic
import Theorems.Thm_Kyprianou_Ch01_compoundPoissonFirstArrivalPositiveFromSurvivalAE
import Theorems.Thm_Kyprianou_Ch01_compoundPoissonFirstMarkOffspringSupportAE
import Theorems.Thm_Kyprianou_Ch01_reverseIntegerCompoundPoissonConstantBeforeFirstArrival
import Theorems.Thm_Kyprianou_Ch01_integerCompoundPoissonShiftAfterFirstMark
import Theorems.Thm_Kyprianou_Ch01_reverseLampertiConstantPrefixPhysicalRestart
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal BigOperators Interval
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
          (integerCompoundPoisson y arrival marks) t ω).toNat = k})
    (y : ℕ) (hy : 0 < y) (t : ℝ≥0) (ht : 0 < t) (k : ℕ) :
    ∀ᵐ ω ∂Q, ¬ ((y : ℝ) * (t : ℝ) <
          ProbabilityTheory.arrival arrival 0 ω) →
      (compoundPoissonToBranching
            (integerCompoundPoisson y arrival marks) t ω).toNat =
      (compoundPoissonToBranching
            (integerCompoundPoisson
              ((y - 1) +
                (Int.floor (marks 0 ω + 1)).toNat)
              (fun n w => arrival (n + 1) w)
              (fun n w => marks (n + 1) w))
            (Real.toNNReal
              ((t : ℝ) -
                ProbabilityTheory.arrival arrival 0 ω / (y : ℝ)))
            ω).toNat := by
  obtain ⟨hMonoAE, hTopAE⟩ :=
    Kyprianou.Ch01.compoundPoissonDriverArrivalStrictMonoDivergesPublic
      Q rate hrate arrival marks jumpLaw hdriver
  have hPosAE : ∀ᵐ w ∂Q,
      0 < ProbabilityTheory.arrival arrival 0 w :=
    Kyprianou.Ch01.compoundPoissonFirstArrivalPositiveFromSurvivalAE
      Q rate hrate arrival marks jumpLaw hdriver
  have hMarkAE : ∀ᵐ w ∂Q, ∃ j : ℕ,
      marks 0 w = (j : ℝ) - 1 :=
    Kyprianou.Ch01.compoundPoissonFirstMarkOffspringSupportAE
      Q rate hrate arrival marks jumpLaw hdriver hSupport
  filter_upwards [hMonoAE, hTopAE, hPosAE, hMarkAE, hNoExplosion y]
    with w hMono hTop hPos hMark hNonExpl
  intro hFirst
  obtain ⟨j, hj⟩ := hMark
  let X : ℝ≥0 → Ω → ℤ :=
    integerCompoundPoisson y arrival marks
  let Y : ℝ≥0 → Ω → ℤ :=
    integerCompoundPoisson ((y - 1) + j)
      (fun n z => arrival (n + 1) z)
      (fun n z => marks (n + 1) z)
  have hPrefix (u : ℝ≥0)
      (hu : (u : ℝ) < ProbabilityTheory.arrival arrival 0 w) :
      X u w = (y : ℤ) :=
    Kyprianou.Ch01.reverseIntegerCompoundPoissonConstantBeforeFirstArrival
      y arrival marks u w hu
  have hSuffix (u : ℝ≥0)
      (hu : ProbabilityTheory.arrival arrival 0 w ≤ (u : ℝ)) :
      X u w =
        Y (Real.toNNReal ((u : ℝ) -
          ProbabilityTheory.arrival arrival 0 w)) w :=
    Kyprianou.Ch01.integerCompoundPoissonShiftAfterFirstMark
      y j arrival marks w hy hMono hTop hj u hu
  have hNonExplX : ∀ t : ℝ≥0, ∃ s : ℝ≥0,
      (t : ℝ≥0∞) < reciprocalOccupation X s w := hNonExpl
  have hClock :=
    Kyprianou.Ch01.reverseLampertiConstantPrefixPhysicalRestart
      X Y w y hy (ProbabilityTheory.arrival arrival 0 w)
      hPos hPrefix hSuffix hNonExplX t (le_of_not_gt hFirst)
  have hMarkNat : (Int.floor (marks 0 w + 1)).toNat = j := by
    have hm : marks 0 w + 1 = (j : ℝ) := by
      rw [hj]
      ring
    rw [hm]
    norm_num
  simpa only [X, Y, hMarkNat] using hClock
