-- Prove2me | solution 1 for OAI.RuledApproximation.integer_fixed_point_of_bounded_drift
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T07:36:42.520307+00:00
-- url     : https://prove2.me/submissions/6c3f6b43-18f8-4380-b01a-d0c7abf8bbb8

-- Generated from openai/math@1581d4c lean/OAI/Geometry/RuledCovering/Lattice.lean:L26-L48
-- (upload_full_project.md Phase 4): solution for node OAI.RuledApproximation.integer_fixed_point_of_bounded_drift. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_RuledCovering
import Definitions.Def_OAI_Geometry_RuledCovering_Projection
import Definitions.Def_OAI_Geometry_RuledCovering_Frames
import Definitions.Def_OAI_Geometry_RuledCovering_OuterApproximation
import Definitions.Def_OAI_Geometry_RuledCovering_Lattice

-- ---- from OAI.Geometry.RuledCovering.Lattice ----
namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

/-- An integer version of the monotone fixed-point argument. The bounded drift
with slope strictly less than one supplies both end barriers. -/
lemma integer_fixed_point_of_bounded_drift (F : ℤ → ℤ) (hF : Monotone F)
    (q B : ℝ) (hq : q < 1) (hB : ∀ i : ℤ, |(F i : ℝ) - q * i| ≤ B) :
    ∃ i : ℤ, F i = i := by
  have hq' : 0 < 1 - q := sub_pos.mpr hq
  obtain ⟨lo, hlo⟩ := exists_int_le (-B / (1 - q))
  obtain ⟨hi, hhi⟩ := exists_int_ge (B / (1 - q))
  have hbound : ∀ i : ℤ, F i ≤ i → lo ≤ i := by
    intro i hi
    have hb := (abs_le.mp (hB i)).1
    have hi' : (F i : ℝ) ≤ i := by exact_mod_cast hi
    have hreal : -B / (1 - q) ≤ (i : ℝ) := by
      apply (div_le_iff₀ hq').2
      nlinarith
    exact_mod_cast hlo.trans hreal
  have hhi' : F hi ≤ hi := by
    have hb := (abs_le.mp (hB hi)).2
    have ht := (div_le_iff₀ hq').1 hhi
    have : (F hi : ℝ) ≤ hi := by nlinarith
    exact_mod_cast this
  obtain ⟨i, hi, hmin⟩ := Int.exists_least_of_bdd ⟨lo, hbound⟩ ⟨hi, hhi'⟩
  exact ⟨i, le_antisymm hi (hmin (F i) (hF hi))⟩

end RuledApproximation

end

end OAI

-- ---- platform node ----
open OAI OAI.RuledApproximation
open Set MeasureTheory Filter Metric
open scoped Topology ContDiff


theorem solution : type_of% @_root_.OAI.RuledApproximation.integer_fixed_point_of_bounded_drift := @_root_.OAI.RuledApproximation.integer_fixed_point_of_bounded_drift
