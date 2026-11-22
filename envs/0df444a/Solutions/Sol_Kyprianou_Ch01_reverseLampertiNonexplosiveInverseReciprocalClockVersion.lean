-- Prove2me | solution 1 for Kyprianou.Ch01.reverseLampertiNonexplosiveInverseReciprocalClockVersion
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T23:09:44.712598+00:00
-- url     : https://prove2.me/submissions/83d5d11d-7439-4faf-9b3e-6778fbd5fcea

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Theorems.Thm_Kyprianou_Ch01_reverseLampertiNonexplosiveJointIntegerProcessVersion
import Theorems.Thm_Kyprianou_Ch01_measurableReciprocalOccupationFromJointIntegerProcess
import Theorems.Thm_Kyprianou_Ch01_measurableInverseReciprocalOccupationFromSections
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (rate : ℝ≥0) (hrate : 0 < rate)
    (arrival marks : ℕ → Ω → ℝ)
    (jumpLaw : Measure ℝ) [IsProbabilityMeasure jumpLaw]
    (hdriver : IsCompoundPoissonDriver arrival marks rate jumpLaw Q)
    (hNoExplosion : ∀ y : ℕ, ∀ᵐ ω ∂Q,
      ∀ t : ℝ≥0, ∃ s : ℝ≥0,
        (t : ℝ≥0∞) <
          reciprocalOccupation (integerCompoundPoisson y arrival marks) s ω) :
    ∀ y : ℕ, ∃ U : ℝ≥0 → Ω → WithTop ℝ≥0,
      (∀ t : ℝ≥0, Measurable (U t)) ∧
      ∀ᵐ ω ∂Q, ∀ t : ℝ≥0,
        U t ω = inverseReciprocalOccupation
          (integerCompoundPoisson y arrival marks) t ω := by
  intro y
  obtain ⟨W, hWJoint, hWAE⟩ :=
    Kyprianou.Ch01.reverseLampertiNonexplosiveJointIntegerProcessVersion
      Q rate hrate arrival marks jumpLaw hdriver y
  have hSections : ∀ s : ℝ≥0,
      Measurable (fun ω : Ω => reciprocalOccupation W s ω) := by
    intro s
    exact Kyprianou.Ch01.measurableReciprocalOccupationFromJointIntegerProcess
      W hWJoint s
  refine ⟨inverseReciprocalOccupation W, ?_, ?_⟩
  · intro t
    exact Kyprianou.Ch01.measurableInverseReciprocalOccupationFromSections
      W hSections t
  · filter_upwards [hWAE] with ω hω
    intro t
    have hOcc (s : ℝ≥0) :
        reciprocalOccupation W s ω =
        reciprocalOccupation (integerCompoundPoisson y arrival marks) s ω := by
      unfold reciprocalOccupation
      apply lintegral_congr
      intro r
      rw [hω (Real.toNNReal r)]
    have hCross :
        (∃ s : ℝ≥0, (t : ℝ≥0∞) < reciprocalOccupation W s ω) ↔
        (∃ s : ℝ≥0, (t : ℝ≥0∞) <
          reciprocalOccupation (integerCompoundPoisson y arrival marks) s ω) := by
      simp_rw [hOcc]
    have hSet :
        {s : ℝ≥0 | (t : ℝ≥0∞) < reciprocalOccupation W s ω} =
        {s : ℝ≥0 | (t : ℝ≥0∞) <
          reciprocalOccupation (integerCompoundPoisson y arrival marks) s ω} := by
      ext s
      simpa only [Set.mem_setOf_eq, hOcc s]
    unfold inverseReciprocalOccupation
    rw [hSet]
    by_cases hIf : ∃ s : ℝ≥0, (t : ℝ≥0∞) < reciprocalOccupation W s ω
    · rw [if_pos hIf, if_pos (hCross.mp hIf)]
    · rw [if_neg hIf, if_neg (fun h => hIf (hCross.mpr h))]
