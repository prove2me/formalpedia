-- Prove2me | solution 2 for OAI.C0Absorption.lipschitz_convex_subtype_of_local
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T22:46:29.572581+00:00
-- url     : https://prove2.me/submissions/90fef6d1-b593-4b54-b803-42e1dcdd666b

-- Generated from openai/math@1581d4c lean/OAI/Analysis/C0Absorption/Localization.lean:L75-L97
-- (upload_full_project.md Phase 4): solution for node OAI.C0Absorption.lipschitz_convex_subtype_of_local. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_C0Absorption
import Definitions.Def_OAI_Analysis_C0Absorption_Molecules
import Definitions.Def_OAI_Analysis_C0Absorption_Norm
import Definitions.Def_OAI_Analysis_C0Absorption_Completion
import Definitions.Def_OAI_Analysis_C0Absorption_Signs
import Definitions.Def_OAI_Analysis_C0Absorption_Lists
import Definitions.Def_OAI_Analysis_C0Absorption_Pairings
import Definitions.Def_OAI_Analysis_C0Absorption_Localization

-- ---- from OAI.Analysis.C0Absorption.Localization ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace C0Absorption

open scoped BigOperators NNReal ENNReal
noncomputable section
open Finset

open Set Filter Topology

theorem lipschitz_convex_subtype_of_local {E Y : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [PseudoMetricSpace Y]
    {B : Set E} (hB : Convex ℝ B) {f : B → Y} {K : ℝ≥0}
    (hf : Continuous f)
    (hloc : ∀ x, ∀ᶠ y in nhds x, dist (f x) (f y) ≤ K * dist x y) :
    LipschitzWith K f := by
  classical
  apply LipschitzWith.of_dist_le_mul
  intro x y
  let F : E → Y := fun z => if h : z ∈ B then f ⟨z, h⟩ else f x
  have hF (z : B) : F z = f z := by simp [F]
  have hc : ContinuousOn F B := by
    rw [continuousOn_iff_continuous_domRestrict]
    convert hf using 1
    exact funext hF
  have hl : ∀ z ∈ B, ∀ᶠ w in nhdsWithin z B,
      dist (F z) (F w) ≤ K * dist z w := by
    intro z hz
    rw [nhdsWithin_eq_map_subtype_coe hz]
    change ∀ᶠ w : B in nhds ⟨z, hz⟩, dist (F z) (F w) ≤ K * dist z (w : E)
    simpa only [show F z = f ⟨z, hz⟩ from hF ⟨z, hz⟩, hF, Subtype.dist_eq] using hloc ⟨z, hz⟩
  have hh := (lipschitzOn_convex_of_local hB hc hl).dist_le_mul x x.property y y.property
  simpa only [hF, Subtype.dist_eq] using hh

noncomputable section

end

end
end C0Absorption

end OAI

-- ---- platform node ----
open OAI OAI.C0Absorption
open scoped BigOperators NNReal ENNReal
open Finset
open Set Filter Topology


theorem solution : type_of% @_root_.OAI.C0Absorption.lipschitz_convex_subtype_of_local := @_root_.OAI.C0Absorption.lipschitz_convex_subtype_of_local
