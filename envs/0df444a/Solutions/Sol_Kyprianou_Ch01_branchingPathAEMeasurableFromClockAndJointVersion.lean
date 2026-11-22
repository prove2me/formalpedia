-- Prove2me | solution 1 for Kyprianou.Ch01.branchingPathAEMeasurableFromClockAndJointVersion
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T19:46:39.06002+00:00
-- url     : https://prove2.me/submissions/901bf164-de8b-4ce9-9022-a1c2d0ebdca8

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_ForwardLampertiPaths
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Construct a genuinely measurable full-path representative from the
sectionwise measurable inverse clock and the joint population version. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (Y : ℝ≥0 → Ω → ℕ) (P : Measure Ω)
    (C : ℝ≥0 → Ω → WithTop ℝ≥0)
    (hCMeas : ∀ t : ℝ≥0, Measurable (C t))
    (hCEq : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      C t ω = inverseBranchingOccupation Y t ω)
    (Z : ℝ≥0 → Ω → ℝ)
    (hJoint : Measurable (fun z : ℝ≥0 × Ω => Z z.1 z.2))
    (hSame : ∀ᵐ ω ∂P, ∀ s : ℝ≥0,
      Z s ω = (Y s ω : ℝ)) :
    AEMeasurable
      (fun ω : Ω => fun t : ℝ≥0 =>
        (branchingToPoisson Y t ω : ℤ)) P := by
  classical
  let H : Ω → (ℝ≥0 → ℤ) := fun ω t =>
    if C t ω = ⊤ then 0 else
      Int.floor (Z ((C t ω).untopD 0) ω)
  have hH : Measurable H := by
    apply measurable_pi_iff.2
    intro t
    have hClock : Measurable (fun ω : Ω => (C t ω).untopD 0) :=
      (hCMeas t).untopD 0
    have hValue : Measurable
        (fun ω : Ω => Z ((C t ω).untopD 0) ω) :=
      hJoint.comp (hClock.prodMk measurable_id)
    exact Measurable.ite
      (show MeasurableSet {ω : Ω | C t ω = ⊤} from
        (measurableSet_singleton (⊤ : WithTop ℝ≥0)).preimage (hCMeas t))
      measurable_const (Int.measurable_floor.comp hValue)
  apply AEMeasurable.congr hH.aemeasurable
  filter_upwards [hCEq, hSame] with ω hclock hpop
  funext t
  change H ω t = (branchingToPoisson Y t ω : ℤ)
  cases hI : inverseBranchingOccupation Y t ω with
  | top =>
      simp [H, hclock t, hI, branchingToPoisson]
  | coe s =>
      have hz : Z s ω = (Y s ω : ℝ) := hpop s
      have hc : C t ω = (↑s : WithTop ℝ≥0) := by
        rw [hclock t, hI]
      have hTarget : branchingToPoisson Y t ω = Y s ω := by
        simp [branchingToPoisson, hI]
      rw [hTarget]
      dsimp [H]
      rw [hc]
      have hnot : (↑s : WithTop ℝ≥0) ≠ ⊤ := WithTop.coe_ne_top
      rw [if_neg hnot, WithTop.untopD_coe, hz]
      exact Int.floor_natCast (Y s ω)
