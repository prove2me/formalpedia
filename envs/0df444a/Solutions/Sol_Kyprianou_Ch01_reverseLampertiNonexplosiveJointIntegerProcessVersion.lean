-- Prove2me | solution 1 for Kyprianou.Ch01.reverseLampertiNonexplosiveJointIntegerProcessVersion
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T21:50:27.313622+00:00
-- url     : https://prove2.me/submissions/6e62f77e-5058-46a2-bfbc-a4b852863472

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Theorems.Thm_Kyprianou_Ch01_integerCompoundPoissonFixedTimeMeasurable
import Theorems.Thm_Kyprianou_Ch01_integerCompoundPoissonRightContinuousAE
import Theorems.Thm_Kyprianou_Ch01_measurableConullIntegerRightContinuousGate
import Theorems.Thm_Kyprianou_Ch01_integerRightContinuousGatedJointVersion
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The Proved compound-Poisson regularity results supply the two
common-event helpers required for a jointly measurable integer version. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (rate : ℝ≥0) (hrate : 0 < rate)
    (arrival marks : ℕ → Ω → ℝ)
    (jumpLaw : Measure ℝ) [IsProbabilityMeasure jumpLaw]
    (hdriver : IsCompoundPoissonDriver arrival marks rate jumpLaw Q) :
    ∀ y : ℕ, ∃ W : ℝ≥0 → Ω → ℤ,
      Measurable (fun z : ℝ≥0 × Ω => W z.1 z.2) ∧
      ∀ᵐ ω ∂Q, ∀ s : ℝ≥0,
        W s ω = integerCompoundPoisson y arrival marks s ω := by
  intro y
  let F : ℝ≥0 → Ω → ℤ := integerCompoundPoisson y arrival marks
  have hF : ∀ t : ℝ≥0, Measurable (F t) := by
    intro t
    exact Kyprianou.Ch01.integerCompoundPoissonFixedTimeMeasurable
      y arrival marks hdriver.measurable_interarrival
      hdriver.measurable_mark t
  have hRight : ∀ᵐ ω ∂Q, ∀ t : ℝ≥0,
      ContinuousWithinAt (fun s : ℝ≥0 => F s ω) (Set.Ici t) t :=
    Kyprianou.Ch01.integerCompoundPoissonRightContinuousAE
      Q rate hrate arrival marks jumpLaw hdriver y
  obtain ⟨G, hG, hGae, hGrc⟩ :=
    Kyprianou.Ch01.measurableConullIntegerRightContinuousGate
      Q F hRight
  obtain ⟨W, hJoint, hSame⟩ :=
    Kyprianou.Ch01.integerRightContinuousGatedJointVersion F hF G hG hGrc
  refine ⟨W, hJoint, ?_⟩
  filter_upwards [hGae] with ω hω
  exact hSame ω hω
