-- Prove2me | solution 1 for Kyprianou.Ch01.reverseLampertiNonexplosiveFirstNegativePassageVersion
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T22:05:53.787502+00:00
-- url     : https://prove2.me/submissions/86762da6-0a09-41a7-b3cb-1bc06ac59265

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Definitions.Def_Kyprianou_Ch01_ForwardLampertiPaths
import Theorems.Thm_Kyprianou_Ch01_integerCompoundPoissonFixedTimeMeasurable
import Theorems.Thm_Kyprianou_Ch01_integerCompoundPoissonRightContinuousAE
import Theorems.Thm_Kyprianou_Ch01_reverseCompoundPoissonIntegerStartsAtInitialStateAE
import Theorems.Thm_Kyprianou_Ch01_firstNegativePassageEqShiftedFirstNonpositive
import Theorems.Thm_Kyprianou_Ch01_firstNonpositiveLatticeEqRationalOfRightContinuous
import Theorems.Thm_Kyprianou_Ch01_rationalFirstNonpositiveLatticeClockMeasurable
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

/-- A strict negative lattice first passage has a globally measurable
rational-grid representative on the driver right-continuity event. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (rate : ℝ≥0) (hrate : 0 < rate)
    (arrival marks : ℕ → Ω → ℝ)
    (jumpLaw : Measure ℝ) [IsProbabilityMeasure jumpLaw]
    (hdriver : IsCompoundPoissonDriver arrival marks rate jumpLaw Q) :
    ∀ y : ℕ, ∃ V : Ω → WithTop ℝ≥0,
      Measurable V ∧
      ∀ᵐ ω ∂Q, V ω =
        firstNegativePassage (integerCompoundPoisson y arrival marks) ω := by
  intro y
  let X : ℝ≥0 → Ω → ℤ := integerCompoundPoisson y arrival marks
  let R : ℝ≥0 → Ω → ℤ := fun s ω => X s ω + 1
  have hMeasX : ∀ t : ℝ≥0, Measurable (X t) := by
    intro t
    exact Kyprianou.Ch01.integerCompoundPoissonFixedTimeMeasurable
      y arrival marks hdriver.measurable_interarrival
      hdriver.measurable_mark t
  have hMeasR : ∀ t : ℝ≥0, Measurable (R t) := by
    intro t
    exact (hMeasX t).add measurable_const
  let V : Ω → WithTop ℝ≥0 := fun ω =>
    ⨅ q : ℚ,
      if R (Real.toNNReal (q : ℝ)) ω ≤ 0 then
        ((Real.toNNReal (q : ℝ) : ℝ≥0) : WithTop ℝ≥0)
      else ⊤
  have hV : Measurable V :=
    Kyprianou.Ch01.rationalFirstNonpositiveLatticeClockMeasurable
      R hMeasR
  have hRC : ∀ᵐ ω ∂Q, ∀ t : ℝ≥0,
      ContinuousWithinAt (fun s : ℝ≥0 => X s ω) (Set.Ici t) t :=
    Kyprianou.Ch01.integerCompoundPoissonRightContinuousAE
      Q rate hrate arrival marks jumpLaw hdriver y
  have hStart : ∀ᵐ ω ∂Q, 0 ≤ X 0 ω := by
    filter_upwards [
      Kyprianou.Ch01.reverseCompoundPoissonIntegerStartsAtInitialStateAE
        Q rate hrate arrival marks jumpLaw hdriver y] with ω hω
    change 0 ≤ integerCompoundPoisson y arrival marks 0 ω
    rw [hω]
    exact Int.natCast_nonneg y
  refine ⟨V, hV, ?_⟩
  filter_upwards [hRC, hStart] with ω hω hstart
  have hRCshift : ∀ t : ℝ≥0,
      ContinuousWithinAt (fun s : ℝ≥0 => R s ω) (Set.Ici t) t := by
    intro t
    exact (hω t).add continuousWithinAt_const
  have hClock :=
    Kyprianou.Ch01.firstNonpositiveLatticeEqRationalOfRightContinuous
      R ω hRCshift
  have hPass :=
    Kyprianou.Ch01.firstNegativePassageEqShiftedFirstNonpositive
      X ω hstart
  calc
    V ω = firstNonpositiveLattice R ω := by
      exact hClock.symm
    _ = firstNegativePassage X ω := by
      simpa only [R] using hPass.symm
