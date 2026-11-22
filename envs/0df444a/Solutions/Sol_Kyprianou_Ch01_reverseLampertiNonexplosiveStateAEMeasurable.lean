-- Prove2me | solution 1 for Kyprianou.Ch01.reverseLampertiNonexplosiveStateAEMeasurable
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T21:01:21.528672+00:00
-- url     : https://prove2.me/submissions/88a676ef-2e00-4cbe-b2fb-419d9a1f06f6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Theorems.Thm_Kyprianou_Ch01_measurableWithTopIntegerRandomTimeEvaluation
import Theorems.Thm_Kyprianou_Ch01_reverseLampertiNonexplosiveJointClockVersion
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false
/-- A jointly measurable integer-process version and globally measurable
inverse clock supply a.e.-measurable exact reverse Lamperti states. -/
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
          reciprocalOccupation (integerCompoundPoisson y arrival marks) s ω) :
    (∀ (y : ℕ) (t : ℝ≥0),
      AEMeasurable
        (fun ω : Ω => (compoundPoissonToBranching
          (integerCompoundPoisson y arrival marks) t ω).toNat) Q) := by
  intro y t
  obtain ⟨W, T, hJoint, hT, hEq⟩ :=
    Kyprianou.Ch01.reverseLampertiNonexplosiveJointClockVersion
      Q rate hrate offspring hNoZeroJumps
      arrival marks jumpLaw hdriver hSupport hJumpMass hNoExplosion y
  have hEval : Measurable (fun ω : Ω =>
      (if T t ω = ⊤ then (0 : ℤ)
       else W ((T t ω).untopD 0) ω).toNat) :=
    Kyprianou.Ch01.measurableWithTopIntegerRandomTimeEvaluation
      W hJoint (T t) (hT t)
  apply hEval.aemeasurable.congr
  filter_upwards [hEq] with ω hω
  exact (hω t).symm
