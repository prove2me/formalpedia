-- Prove2me | solution 1 for Kyprianou.Ch01.stoppedIntegerCompoundPoissonPathAEMeasurableFromDriver
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T17:02:32.966811+00:00
-- url     : https://prove2.me/submissions/f91621ec-aed0-4ca6-ad4d-252591c7d0bc

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ForwardLampertiPaths
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Theorems.Thm_Kyprianou_Ch01_integerCompoundPoissonPathMeasurable
import Theorems.Thm_Kyprianou_Ch01_firstNonpositiveLatticeAEMeasurableFromDriver

open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The stopped compound Poisson path is a.e. measurable once the exact
first nonpositive lattice time is known to be a.e. measurable. -/
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
    ∀ y : ℕ, AEMeasurable
      (fun ω : Ω' => fun t : ℝ≥0 =>
        stoppedIntegerCompoundPoisson y arrival marks t ω) Q := by
  classical
  intro y
  let X : ℝ≥0 → Ω' → ℤ := integerCompoundPoisson y arrival marks
  have hXm : Measurable (fun ω : Ω' => fun t : ℝ≥0 => X t ω) := by
    exact Kyprianou.Ch01.integerCompoundPoissonPathMeasurable
      y arrival marks hDriver.measurable_interarrival hDriver.measurable_mark
  have hHit : AEMeasurable
      (fun ω : Ω' => firstNonpositiveLattice X ω) Q := by
    exact Kyprianou.Ch01.firstNonpositiveLatticeAEMeasurableFromDriver
      Q rate hRate arrival marks jumpLaw hDriver y
  let T : Ω' → WithTop ℝ≥0 :=
    hHit.mk (fun ω : Ω' => firstNonpositiveLattice X ω)
  have hTm : Measurable T := hHit.measurable_mk
  have hTeq : (fun ω : Ω' => firstNonpositiveLattice X ω) =ᵐ[Q] T :=
    hHit.ae_eq_mk
  have hStopped : Measurable (fun ω : Ω' => fun t : ℝ≥0 =>
      if T ω ≤ (t : WithTop ℝ≥0) then (0 : ℤ) else X t ω) := by
    apply measurable_pi_iff.2
    intro t
    exact Measurable.ite (measurableSet_le hTm measurable_const)
      measurable_const ((measurable_pi_iff.1 hXm) t)
  apply AEMeasurable.congr hStopped.aemeasurable
  filter_upwards [hTeq] with ω hω
  funext t
  change (if T ω ≤ (t : WithTop ℝ≥0) then (0 : ℤ) else X t ω) =
      (if firstNonpositiveLattice X ω ≤ (t : WithTop ℝ≥0)
        then (0 : ℤ) else X t ω)
  rw [hω]
