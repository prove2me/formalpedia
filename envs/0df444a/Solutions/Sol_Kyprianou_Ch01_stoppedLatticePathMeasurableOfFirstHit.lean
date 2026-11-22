-- Prove2me | solution 1 for Kyprianou.Ch01.stoppedLatticePathMeasurableOfFirstHit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T16:58:13.143628+00:00
-- url     : https://prove2.me/submissions/aeb852e8-1037-40c0-b475-f7f7107fe766

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ForwardLampertiPaths
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Stopping a globally measurable lattice-valued random path at a measurable
first nonpositive time preserves product-space measurability. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → ℤ)
    (hPath : Measurable (fun ω : Ω => fun t : ℝ≥0 => X t ω))
    (hHit : Measurable (fun ω : Ω => firstNonpositiveLattice X ω)) :
    Measurable (fun ω : Ω => fun t : ℝ≥0 =>
      if firstNonpositiveLattice X ω ≤ (t : WithTop ℝ≥0)
      then (0 : ℤ) else X t ω) := by
  classical
  apply measurable_pi_iff.2
  intro t
  have hEvent : MeasurableSet
      {ω : Ω | firstNonpositiveLattice X ω ≤ (t : WithTop ℝ≥0)} :=
    measurableSet_le hHit measurable_const
  have hSection : Measurable (fun ω : Ω => X t ω) :=
    (measurable_pi_iff.1 hPath) t
  exact Measurable.ite hEvent measurable_const hSection
