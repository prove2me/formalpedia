-- Prove2me | solution 1 for Kyprianou.Ch01.stoppedCompoundPoissonCountablePathSkeletonAEMeasurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T15:37:43.946621+00:00
-- url     : https://prove2.me/submissions/ba390808-b61e-4262-bdce-8902d880f294

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ForwardLampertiPaths
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Theorems.Thm_Kyprianou_Ch01_stoppedCompoundPoissonMarkov

open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Countable skeleton of stopped compound Poisson paths is a.e. measurable. -/
theorem solution
    {Ω' : Type*} [MeasurableSpace Ω']
    (Q : Measure Ω') [IsProbabilityMeasure Q]
    (rate : ℝ≥0) (hRate : 0 < rate)
    (offspring : PMF ℕ) (hNoNullJumps : offspring 1 = 0)
    (arrival marks : ℕ → Ω' → ℝ)
    (jumpLaw : Measure ℝ) [IsProbabilityMeasure jumpLaw]
    (hDriver : IsCompoundPoissonDriver
      arrival marks rate jumpLaw Q)
    (hSupport : jumpLaw
      {x : ℝ | ∃ k : ℕ, x = (k : ℝ) - 1} = 1)
    (hJumpMass : ∀ k : ℕ,
      jumpLaw ({((k : ℝ) - 1)} : Set ℝ) = offspring k) :
    ∀ (y : ℕ) (times : ℕ → ℝ≥0),
      AEMeasurable (fun ω : Ω' => fun n : ℕ =>
        stoppedIntegerCompoundPoisson y arrival marks (times n) ω) Q := by
  classical
  obtain ⟨lawC, hS, hZ, hGen, hPaths⟩ :=
    Kyprianou.Ch01.stoppedCompoundPoissonMarkov
      Q rate hRate offspring hNoNullJumps arrival marks
      jumpLaw hDriver hSupport hJumpMass
  intro y times
  have hPos : ∀ t : ℝ≥0, ∀ᵐ ω ∂Q,
      0 ≤ stoppedIntegerCompoundPoisson y arrival marks t ω :=
    (hPaths y).1
  have hNat : ∀ t : ℝ≥0, AEMeasurable
      (fun ω => (stoppedIntegerCompoundPoisson y arrival marks t ω).toNat) Q :=
    (hPaths y).2.1
  apply (aemeasurable_pi_iff).2
  intro n
  have hCast : AEMeasurable
      (fun ω : Ω' =>
        ((stoppedIntegerCompoundPoisson y arrival marks (times n) ω).toNat : ℤ)) Q :=
    (measurable_of_countable (fun j : ℕ => (j : ℤ))).comp_aemeasurable
      (hNat (times n))
  apply AEMeasurable.congr hCast
  filter_upwards [hPos (times n)] with ω hω
  omega
