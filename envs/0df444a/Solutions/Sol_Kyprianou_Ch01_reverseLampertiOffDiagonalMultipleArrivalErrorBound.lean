-- Prove2me | solution 1 for Kyprianou.Ch01.reverseLampertiOffDiagonalMultipleArrivalErrorBound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T13:01:54.231786+00:00
-- url     : https://prove2.me/submissions/4a043ba6-c8ba-45b4-8900-11b5bef910e4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Theorems.Thm_Kyprianou_Ch01_reverseLampertiOffDiagonalOneArrivalEventError
import Theorems.Thm_Kyprianou_Ch01_compoundPoissonFirstMarkedOffDiagonalEventMass
import Theorems.Thm_Kyprianou_Ch01_compoundPoissonMarkedFirstTwoClockUpperBound
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
        (if y ≤ k + 1 then (offspring (k + 1 - y)).toReal else 0) *
          (1 - Real.exp (-(((rate : ℝ) * (y : ℝ)) *
            (Real.toNNReal t : ℝ))))| ≤
        ((rate : ℝ) * (y : ℝ)) * t *
          (∑' j : ℕ, (offspring j).toReal *
            (1 - Real.exp (-((rate : ℝ) * (((y + j : ℕ) : ℝ)) * t)))) := by
  intro y k hyk t ht
  have hEvent :=
    Kyprianou.Ch01.reverseLampertiOffDiagonalOneArrivalEventError
      Q rate hrate offspring hNoZeroJumps arrival marks jumpLaw
      hdriver hSupport hJumpMass hNoExplosion
      K hRealisation y k hyk t ht
  have hFirst :=
    Kyprianou.Ch01.compoundPoissonFirstMarkedOffDiagonalEventMass
      Q rate hrate offspring arrival marks jumpLaw
      hdriver hJumpMass y k t ht
  rw [hFirst] at hEvent
  have hTwo :=
    Kyprianou.Ch01.compoundPoissonMarkedFirstTwoClockUpperBound
      Q rate hrate offspring arrival marks jumpLaw
      hdriver hJumpMass y (Real.toNNReal t)
  rw [Real.coe_toNNReal t ht] at hTwo hEvent ⊢
  exact le_trans hEvent hTwo
