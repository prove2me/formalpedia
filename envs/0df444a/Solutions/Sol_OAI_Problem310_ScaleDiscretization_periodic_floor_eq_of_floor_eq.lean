-- Prove2me | solution 1 for OAI.Problem310.ScaleDiscretization.periodic_floor_eq_of_floor_eq
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T06:15:18.40758+00:00
-- url     : https://prove2.me/submissions/5849c62f-573a-41b3-b767-cbb015faab56

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/DyadicAvoidance/MonotoneRepresentatives.lean:L165-L182
-- (upload_full_project.md Phase 4): solution for node OAI.Problem310.ScaleDiscretization.periodic_floor_eq_of_floor_eq. The node keeps its source
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

-- ---- from OAI.MeasureTheory.DyadicAvoidance.MonotoneRepresentatives ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe u_α u_ι

noncomputable section

open scoped BigOperators

namespace Problem310.ScaleDiscretization

/-- Passing from a real-line dyadic cell to its periodic key loses no information. -/
lemma periodic_floor_eq_of_floor_eq (q : ℕ) {y z : ℝ}
    (h : ⌊(2 : ℝ) ^ q * y⌋ = ⌊(2 : ℝ) ^ q * z⌋) :
    ⌊(2 : ℝ) ^ q * Int.fract y⌋ = ⌊(2 : ℝ) ^ q * Int.fract z⌋ := by
  have hcancel (w : ℝ) : ⌊(2 : ℝ) ^ q * w⌋ / (2 : ℤ) ^ q = ⌊w⌋ := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using
      Int.natCast_mul_floor_div_cancel (n := 2 ^ q) (by positivity) w
  have hfloor : ⌊y⌋ = ⌊z⌋ := by
    rw [← hcancel y, ← hcancel z, h]
  have hkey (w : ℝ) : ⌊(2 : ℝ) ^ q * Int.fract w⌋ =
      ⌊(2 : ℝ) ^ q * w⌋ - (2 : ℤ) ^ q * ⌊w⌋ := by
    rw [Int.fract]
    have heq : (2 : ℝ) ^ q * (w - (⌊w⌋ : ℝ)) =
        (2 : ℝ) ^ q * w - (((2 : ℤ) ^ q * ⌊w⌋ : ℤ) : ℝ) := by
      push_cast
      ring
    rw [heq, Int.floor_sub_intCast]
  rw [hkey, hkey, h, hfloor]

end Problem310.ScaleDiscretization

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem310 OAI.Problem310.ScaleDiscretization
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.Problem310.ScaleDiscretization.periodic_floor_eq_of_floor_eq := @_root_.OAI.Problem310.ScaleDiscretization.periodic_floor_eq_of_floor_eq
