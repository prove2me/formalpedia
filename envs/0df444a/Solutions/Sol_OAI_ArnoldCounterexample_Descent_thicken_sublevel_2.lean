-- Prove2me | solution 2 for OAI.ArnoldCounterexample.Descent.thicken_sublevel
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T10:05:36.860472+00:00
-- url     : https://prove2.me/submissions/a616420b-000a-41e0-a206-bc80bc3007ae

-- Generated from openai/math@1581d4c lean/OAI/Geometry/Arnold/Descent.lean:L146-L166
-- (upload_full_project.md Phase 4): solution for node OAI.ArnoldCounterexample.Descent.thicken_sublevel. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ArnoldCounterexample
import Definitions.Def_OAI_Geometry_Arnold_Involution
import Definitions.Def_OAI_Geometry_Arnold_Projective
import Definitions.Def_OAI_Geometry_Arnold_Rotation
import Definitions.Def_OAI_Geometry_Arnold_Tangent
import Definitions.Def_OAI_Geometry_Arnold_Haar
import Definitions.Def_OAI_Geometry_Arnold_Differentiation
import Definitions.Def_OAI_Geometry_Arnold_Orbit
import Definitions.Def_OAI_Geometry_Arnold_Symplectic
import Definitions.Def_OAI_Geometry_Arnold_Coordinates
import Definitions.Def_OAI_Geometry_Arnold_Extension

-- ---- from OAI.Geometry.Arnold.Descent ----
namespace OAI

universe uE uX

noncomputable section
open scoped BigOperators ContDiff
open MeasureTheory Set Filter
open scoped Matrix.Norms.Operator
open scoped Topology

open Set
open scoped ContDiff

namespace ArnoldCounterexample.Descent

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]

end ArnoldCounterexample.Descent

open Set Function

namespace ArnoldCounterexample.Descent

variable {X : Type uX} [TopologicalSpace X] [CompactSpace X]

/-- Strict sublevel containment on the zero set of a continuous coordinate
persists on a slightly larger closed sublevel. -/
theorem thicken_sublevel {f g : X → ℝ} {ℓ : X → ℂ}
    (hf : Continuous f) (hg : Continuous g) (hℓ : Continuous ℓ)
    (c a : ℝ) (h : ∀ x, f x ≤ c → ℓ x = 0 → g x < a) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x, f x ≤ c + ε → ℓ x = 0 → g x < a := by
  let K : Set X := {x | ℓ x = 0 ∧ a ≤ g x}
  have hK : IsCompact K := ((isClosed_eq hℓ continuous_const).inter
    (isClosed_le continuous_const hg)).isCompact
  by_cases hne : K.Nonempty
  · obtain ⟨z, hz, hmin⟩ := hK.exists_isMinOn hne hf.continuousOn
    have hcz : c < f z := by
      by_contra hc
      exact (not_lt_of_ge hz.2) (h z (le_of_not_gt hc) hz.1)
    refine ⟨(f z - c) / 2, by linarith, fun x hx hzero ↦ ?_⟩
    by_contra hxa
    have hbound : f z ≤ f x := hmin (show x ∈ K from ⟨hzero, le_of_not_gt hxa⟩)
    linarith
  · refine ⟨1, zero_lt_one, fun x _ hzero ↦ ?_⟩
    by_contra hxa
    exact hne ⟨x, hzero, le_of_not_gt hxa⟩

end ArnoldCounterexample.Descent

end

end OAI

-- ---- platform node ----
open OAI OAI.ArnoldCounterexample OAI.ArnoldCounterexample.Descent
open scoped BigOperators ContDiff
open MeasureTheory Set Filter
open scoped Matrix.Norms.Operator
open scoped Topology
open Set
open scoped ContDiff
open Set Function


theorem solution.{uX} : type_of% @_root_.OAI.ArnoldCounterexample.Descent.thicken_sublevel.{uX} := @_root_.OAI.ArnoldCounterexample.Descent.thicken_sublevel.{uX}
