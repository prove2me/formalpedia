-- Prove2me | solution 1 for OAI.Problem310Support.periodic_nat_interval_volume_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T07:02:51.59999+00:00
-- url     : https://prove2.me/submissions/ae389734-c0b8-40fd-9d52-d231b12d0355

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/DyadicAvoidance/PeriodicMeasure.lean:L39-L58
-- (upload_full_project.md Phase 4): solution for node OAI.Problem310Support.periodic_nat_interval_volume_le. The node keeps its source
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
import Theorems.Thm_OAI_Problem310Support_periodic_unit_volume_nat

-- ---- from OAI.MeasureTheory.DyadicAvoidance.PeriodicMeasure ----
namespace OAI

noncomputable section

open Set MeasureTheory

namespace Problem310Support

/-- A period-one set occupies at most `n` times its unit-cell volume in `n` cells.
No measurability assumption is needed for this upper bound. -/
theorem periodic_nat_interval_volume_le {H : Set ℝ}
    (hH : ∀ x : ℝ, x + 1 ∈ H ↔ x ∈ H) (n : ℕ) :
    volume (H ∩ Icc (0 : ℝ) (n : ℝ)) ≤
      (n : ENNReal) * volume (H ∩ Icc (0 : ℝ) 1) := by
  induction n with
  | zero =>
    simp only [Nat.cast_zero, Icc_self, zero_mul, nonpos_iff_eq_zero]
    exact measure_mono_null inter_subset_right (measure_singleton 0)
  | succ n ih =>
    have hsplit : H ∩ Icc (0 : ℝ) ((n : ℝ) + 1) =
        (H ∩ Icc (0 : ℝ) (n : ℝ)) ∪
          (H ∩ Icc (n : ℝ) ((n : ℝ) + 1)) := by
      rw [← inter_union_distrib_left,
        Icc_union_Icc_eq_Icc (by positivity : (0 : ℝ) ≤ n) (by linarith)]
    simp only [Nat.cast_add, Nat.cast_one]
    rw [hsplit, add_mul, one_mul]
    exact (measure_union_le _ _).trans
      (add_le_add ih (le_of_eq (periodic_unit_volume_nat hH n)))

end Problem310Support

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem310Support
open Set MeasureTheory


theorem solution : type_of% @_root_.OAI.Problem310Support.periodic_nat_interval_volume_le := @_root_.OAI.Problem310Support.periodic_nat_interval_volume_le
