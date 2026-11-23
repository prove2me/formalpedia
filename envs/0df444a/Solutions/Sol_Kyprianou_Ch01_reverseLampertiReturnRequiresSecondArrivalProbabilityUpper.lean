-- Prove2me | solution 1 for Kyprianou.Ch01.reverseLampertiReturnRequiresSecondArrivalProbabilityUpper
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T17:32:45.496135+00:00
-- url     : https://prove2.me/submissions/5777e1cd-44df-430c-aca4-35735e9733a0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Theorems.Thm_Kyprianou_Ch01_reverseLampertiReturnRequiresSecondArrivalAE
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
          (integerCompoundPoisson y arrival marks) t ω).toNat = k})
    (hBefore : ∀ (z : ℕ) (u : ℝ≥0) (ω : Ω),
      (u : ℝ) < ProbabilityTheory.arrival arrival 0 ω →
        integerCompoundPoisson z arrival marks u ω = (z : ℤ)) :
    ∀ y : ℕ, 0 < y → ∀ t : ℝ, 0 ≤ t →
      (Q {ω | (compoundPoissonToBranching
          (integerCompoundPoisson y arrival marks)
          (Real.toNNReal t) ω).toNat = y}).toReal ≤ (Q {ω | (y : ℝ) * (Real.toNNReal t : ℝ) <
        ProbabilityTheory.arrival arrival 0 ω}).toReal + (Q {ω | ∃ k : ℕ,
          marks 0 ω = (k : ℝ) - 1 ∧
          ProbabilityTheory.arrival arrival 0 ω ≤
            (y : ℝ) * (Real.toNNReal t : ℝ) ∧
          ProbabilityTheory.arrival arrival 1 ω ≤
            ProbabilityTheory.arrival arrival 0 ω +
              (((y + k : ℕ) : ℝ)) * (Real.toNNReal t : ℝ)}).toReal := by
  intro y hy t ht
  let τ : ℝ≥0 := Real.toNNReal t
  let A : Set Ω := {ω | (y : ℝ) * (τ : ℝ) <
    ProbabilityTheory.arrival arrival 0 ω}
  let B : Set Ω := {ω | (compoundPoissonToBranching
    (integerCompoundPoisson y arrival marks) τ ω).toNat = y}
  let C : Set Ω := {ω | ∃ j : ℕ,
    marks 0 ω = (j : ℝ) - 1 ∧
    ProbabilityTheory.arrival arrival 0 ω ≤ (y : ℝ) * (τ : ℝ) ∧
    ProbabilityTheory.arrival arrival 1 ω ≤
      ProbabilityTheory.arrival arrival 0 ω +
        (((y + j : ℕ) : ℝ)) * (τ : ℝ)}
  have hReturn :=
    Kyprianou.Ch01.reverseLampertiReturnRequiresSecondArrivalAE
      Q rate hrate offspring hNoZeroJumps arrival marks jumpLaw
      hdriver hSupport hJumpMass hNoExplosion hBefore y τ hy
  have hSub : Q B ≤ Q (A ∪ C) := by
    apply measure_mono_ae
    filter_upwards [hReturn] with ω hω
    intro hB
    exact hω hB
  have hBound : (Q B).toReal ≤ (Q A).toReal + (Q C).toReal :=
    (ENNReal.toReal_mono (measure_ne_top _ _) hSub).trans
      (measureReal_union_le A C)
  simpa only [A, B, C, τ] using hBound
