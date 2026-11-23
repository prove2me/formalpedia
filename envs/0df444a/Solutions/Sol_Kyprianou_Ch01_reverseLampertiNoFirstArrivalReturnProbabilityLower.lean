-- Prove2me | solution 1 for Kyprianou.Ch01.reverseLampertiNoFirstArrivalReturnProbabilityLower
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T17:23:39.05848+00:00
-- url     : https://prove2.me/submissions/c27c0481-194a-4ea2-9d2a-5d720dd1101c

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Theorems.Thm_Kyprianou_Ch01_reverseLampertiNoFirstArrivalWindowAE
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
      (Q {ω | (y : ℝ) * (Real.toNNReal t : ℝ) <
        ProbabilityTheory.arrival arrival 0 ω}).toReal ≤ (Q {ω | (compoundPoissonToBranching
          (integerCompoundPoisson y arrival marks)
          (Real.toNNReal t) ω).toNat = y}).toReal := by
  intro y hy t ht
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono_ae
  filter_upwards [Kyprianou.Ch01.reverseLampertiNoFirstArrivalWindowAE
      Q rate hrate arrival marks jumpLaw hdriver
      y (Real.toNNReal t)] with ω hω
  exact hω
