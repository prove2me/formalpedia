-- Prove2me | solution 1 for OAI.ForestSpace.exists_raw_test
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T04:48:00.782654+00:00
-- url     : https://prove2.me/submissions/eb572a62-3663-4447-af77-0177156890cd

-- Generated from openai/math@1581d4c lean/OAI/Analysis/ForestSpace/Polar.lean:L36-L50
-- (upload_full_project.md Phase 4): solution for node OAI.ForestSpace.exists_raw_test. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ForestSpace
import Definitions.Def_OAI_Analysis_ForestSpace_Moduli
import Definitions.Def_OAI_Analysis_ForestSpace_Segments
import Definitions.Def_OAI_Analysis_ForestSpace_FiniteGeometry
import Definitions.Def_OAI_Analysis_ForestSpace_Paired
import Definitions.Def_OAI_Analysis_ForestSpace_Norm
import Definitions.Def_OAI_Analysis_ForestSpace_Completion
import Definitions.Def_OAI_Analysis_ForestSpace_Polar
import Theorems.Thm_OAI_ForestSpace_norm_rawRestriction

-- ---- from OAI.Analysis.ForestSpace.Polar ----
namespace OAI

open scoped BigOperators
open Finset

namespace ForestSpace

noncomputable section
attribute [local instance] Classical.propDecidable

section PolarTests
variable {V : Type} [PartialOrder V]

/-- Norming tests can always be chosen finitely supported, with a positive
rather than absolute pairing. -/
 theorem exists_raw_test (x : FullDual V) {r : ℝ} (hr : r < ‖x‖) :
    ∃ u : TestVector V, ‖u‖ ≤ 1 ∧ r < x (u : J V) := by
  have hr' : r < ‖rawRestriction x‖ := by simpa only [norm_rawRestriction] using hr
  obtain ⟨u,hu,hr⟩ := (rawRestriction x).exists_lt_apply_of_lt_opNorm hr'
  rw [Real.norm_eq_abs] at hr
  by_cases hpos : 0 ≤ rawRestriction x u
  · refine ⟨u,hu.le, ?_⟩
    rw [abs_of_nonneg hpos] at hr
    exact hr
  · refine ⟨-u, by simpa only [norm_neg] using hu.le, ?_⟩
    have ha : rawRestriction x (-u) = -rawRestriction x u := map_neg _ _
    rw [abs_of_neg (lt_of_not_ge hpos), ← ha] at hr
    exact hr

end PolarTests

section CoordinateCompletion
variable {W : Type} [PartialOrder W]
variable {V : Type} [PartialOrder V]

end CoordinateCompletion

end

end ForestSpace

end OAI

-- ---- platform node ----
open OAI OAI.ForestSpace
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable


theorem solution : type_of% @_root_.OAI.ForestSpace.exists_raw_test := @_root_.OAI.ForestSpace.exists_raw_test
