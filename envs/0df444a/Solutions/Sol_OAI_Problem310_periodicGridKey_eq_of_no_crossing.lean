-- Prove2me | solution 1 for OAI.Problem310.periodicGridKey_eq_of_no_crossing
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T07:17:42.63099+00:00
-- url     : https://prove2.me/submissions/100ddde4-7120-4199-8611-916c5f2ad63c

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/DyadicAvoidance/GridGeometry.lean:L59-L81
-- (upload_full_project.md Phase 4): solution for node OAI.Problem310.periodicGridKey_eq_of_no_crossing. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_DyadicAvoidance
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_PeriodicBasic
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_GridSeparation
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_FiniteTableModel
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_OrderedRouting
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_RoutingPath
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_CenterRouteExposure
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_ExceptionalCenters
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_CenterFailureBound
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_FirstDefault
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_ConcreteLabelMeasures
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_CenterFirstDefault
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_RandomSetDensity
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_RoutedSetDensity
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_RoutedExposure
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_FirstDefaultSelection
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_FiniteLocalPredicate
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_WindowData
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_WindowTableModel
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_StableRoutingBridge
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_WindowExceptionalTransfer
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_TrialAddresses
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_WindowTrialAddresses
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_ConcreteWindowAtom
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_PeriodicEnvelope
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_GlobalFromPeriodic
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_GridGeometry

-- ---- from OAI.MeasureTheory.DyadicAvoidance.GridGeometry ----
namespace OAI

noncomputable section
namespace Problem310

/-- The periodic label is the residue of the label on the real-line grid. -/
theorem periodicGridKey_eq_emod (q : ℕ) (hq : 0 < q) (x : ℝ) :
    periodicGridKey q x = ⌊(q : ℝ) * x⌋ % (q : ℤ) := by
  unfold periodicGridKey Int.fract
  rw [mul_sub]
  have hc : (q : ℝ) * (⌊x⌋ : ℝ) = (((q : ℤ) * ⌊x⌋ : ℤ) : ℝ) := by
    push_cast
    rfl
  rw [hc, Int.floor_sub_intCast, Int.emod_def]
  have hf := Int.natCast_mul_floor_div_cancel (R := ℝ) (Nat.ne_of_gt hq) x
  rw [hf]

/-- Absence of a real-line grid boundary between ordered points preserves keys.
The interval is open at its left end, so a center on a boundary is allowed. -/
theorem periodicGridKey_eq_of_no_crossing (q : ℕ) (hq : 0 < q) {x y : ℝ}
    (hxy : x ≤ y) (hcross : ∀ k : ℤ, (k : ℝ) / q ∉ Set.Ioc x y) :
    periodicGridKey q x = periodicGridKey q y := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  have hmono : ⌊(q : ℝ) * x⌋ ≤ ⌊(q : ℝ) * y⌋ :=
    Int.floor_mono (mul_le_mul_of_nonneg_left hxy hqpos.le)
  have hfloors : ⌊(q : ℝ) * x⌋ = ⌊(q : ℝ) * y⌋ := by
    by_contra hne
    have hlt : ⌊(q : ℝ) * x⌋ + 1 ≤ ⌊(q : ℝ) * y⌋ := by omega
    apply hcross (⌊(q : ℝ) * x⌋ + 1)
    constructor
    · apply (lt_div_iff₀ hqpos).mpr
      have h := Int.lt_floor_add_one ((q : ℝ) * x)
      push_cast
      nlinarith
    · apply (div_le_iff₀ hqpos).mpr
      have hcast : ((⌊(q : ℝ) * x⌋ + 1 : ℤ) : ℝ) ≤
          (⌊(q : ℝ) * y⌋ : ℝ) := by exact_mod_cast hlt
      have h := Int.floor_le ((q : ℝ) * y)
      nlinarith
  rw [periodicGridKey_eq_emod q hq, periodicGridKey_eq_emod q hq, hfloors]

end Problem310

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem310


theorem solution : type_of% @_root_.OAI.Problem310.periodicGridKey_eq_of_no_crossing := @_root_.OAI.Problem310.periodicGridKey_eq_of_no_crossing
