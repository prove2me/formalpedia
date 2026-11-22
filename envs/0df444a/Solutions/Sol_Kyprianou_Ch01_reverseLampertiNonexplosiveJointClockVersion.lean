-- Prove2me | solution 1 for Kyprianou.Ch01.reverseLampertiNonexplosiveJointClockVersion
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T21:45:14.666837+00:00
-- url     : https://prove2.me/submissions/b5a9603d-ed83-42a6-a4f8-58d01ffcab00

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Theorems.Thm_Kyprianou_Ch01_reverseLampertiNonexplosiveJointIntegerProcessVersion
import Theorems.Thm_Kyprianou_Ch01_reverseLampertiNonexplosiveStoppedInverseClockMeasurableVersion
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

/-- One common conull event combines the jointly measurable lattice process
with its stopped inverse reciprocal-occupation clock. -/
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
    ∀ y : ℕ,
      ∃ (W : ℝ≥0 → Ω → ℤ)
        (T : ℝ≥0 → Ω → WithTop ℝ≥0),
        Measurable (fun z : ℝ≥0 × Ω => W z.1 z.2) ∧
        (∀ t : ℝ≥0, Measurable (T t)) ∧
        (∀ᵐ ω ∂Q, ∀ t : ℝ≥0,
          (compoundPoissonToBranching
            (integerCompoundPoisson y arrival marks) t ω).toNat =
          (if T t ω = ⊤ then (0 : ℤ)
           else W ((T t ω).untopD 0) ω).toNat) := by
  intro y
  obtain ⟨W, hJoint, hW⟩ :=
    Kyprianou.Ch01.reverseLampertiNonexplosiveJointIntegerProcessVersion
      Q rate hrate arrival marks jumpLaw hdriver y
  obtain ⟨T, hT, hClock⟩ :=
    Kyprianou.Ch01.reverseLampertiNonexplosiveStoppedInverseClockMeasurableVersion
      Q rate hrate arrival marks jumpLaw hdriver hNoExplosion y
  refine ⟨W, T, hJoint, hT, ?_⟩
  filter_upwards [hW, hClock] with ω hWω hClockω
  intro t
  cases hmin : min
      (inverseReciprocalOccupation
        (integerCompoundPoisson y arrival marks) t ω)
      (firstNegativePassage
        (integerCompoundPoisson y arrival marks) ω) with
  | top =>
      simp [compoundPoissonToBranching, hmin, hClockω t]
  | coe s =>
      have hsrc : compoundPoissonToBranching
          (integerCompoundPoisson y arrival marks) t ω =
          integerCompoundPoisson y arrival marks s ω := by
        simp [compoundPoissonToBranching, hmin]
      have ht : T t ω = (↑s : WithTop ℝ≥0) := by
        rw [hClockω t, hmin]
      rw [hsrc, ht]
      have hnot : (↑s : WithTop ℝ≥0) ≠ ⊤ := WithTop.coe_ne_top
      rw [if_neg hnot, WithTop.untopD_coe, hWω s]
