-- Prove2me | solution 1 for GlobalTheory.HypChartPf.restrict_periodic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:53:01.178952+00:00
-- url     : https://prove2.me/submissions/f5669b01-95c7-41b9-be74-e642183e09cd

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushLoc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushQ
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HyperboloidChartMeasureFormula

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Matrix
open scoped ENNReal
open GlobalTheory GlobalTheory.HypChartPf
open PI.RhsWLim PI.RhsWLim.W
namespace GlobalTheory.HypChartPf
theorem _root_.solution (A : Set ℝ) (hA : MeasurableSet A) (hp : ∀ x, x + 2 * Real.pi ∈ A ↔ x ∈ A) :
    volume.restrict (Set.Ioc (0 : ℝ) (2 * Real.pi)) A = volume.restrict (Set.Ioc (-Real.pi) Real.pi) A := by
  have hpos : (0 : ℝ) < 2 * Real.pi := by positivity
  have h1 := isAddFundamentalDomain_Ioc hpos 0 (volume : Measure ℝ)
  have h2 := isAddFundamentalDomain_Ioc hpos (-Real.pi) (volume : Measure ℝ)
  rw [zero_add] at h1
  rw [show -Real.pi + 2 * Real.pi = Real.pi by ring] at h2
  have key : ∀ n : ℤ, ∀ x, n • (2 * Real.pi) + x ∈ A ↔ x ∈ A := by
    intro n
    induction n using Int.induction_on with
    | zero => intro x; simp
    | succ m ih =>
      intro x
      rw [← ih x, ← hp ((m : ℤ) • (2 * Real.pi) + x)]
      rw [show ((m : ℤ) + 1) • (2 * Real.pi) + x = (m : ℤ) • (2 * Real.pi) + x + 2 * Real.pi by
        rw [add_smul, one_smul]; abel]
    | pred m ih =>
      intro x
      have h := hp ((-(m : ℤ) - 1) • (2 * Real.pi) + x)
      rw [show (-(m : ℤ) - 1) • (2 * Real.pi) + x + 2 * Real.pi = (-(m : ℤ)) • (2 * Real.pi) + x by
        rw [sub_smul, one_smul]; abel, ih x] at h
      exact h.symm
  rw [Measure.restrict_apply hA, Measure.restrict_apply hA]
  refine h1.measure_set_eq h2 hA ?_
  rintro ⟨g, hg⟩
  obtain ⟨n, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hg
  ext x
  exact key n x
end GlobalTheory.HypChartPf
