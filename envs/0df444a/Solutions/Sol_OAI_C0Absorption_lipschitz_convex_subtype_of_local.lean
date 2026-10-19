-- Prove2me | solution 1 for OAI.C0Absorption.lipschitz_convex_subtype_of_local
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T22:21:28.050471+00:00
-- url     : https://prove2.me/submissions/be9b6109-730e-4586-85b4-448368cad6b9

import Mathlib
import Definitions.Def_C0Absorption
import Definitions.Def_OAI_Analysis_C0Absorption_Molecules
import Definitions.Def_OAI_Analysis_C0Absorption_Norm
import Definitions.Def_OAI_Analysis_C0Absorption_Completion
import Definitions.Def_OAI_Analysis_C0Absorption_Signs
import Definitions.Def_OAI_Analysis_C0Absorption_Lists
import Definitions.Def_OAI_Analysis_C0Absorption_Pairings
import Definitions.Def_OAI_Analysis_C0Absorption_Localization

open OAI OAI.C0Absorption
open scoped BigOperators NNReal ENNReal
open Finset
open Set Filter Topology


theorem solution {E Y : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [PseudoMetricSpace Y]
    {B : Set E} (hB : Convex ℝ B) {f : B → Y} {K : ℝ≥0}
    (hf : Continuous f)
    (hloc : ∀ x, ∀ᶠ y in nhds x, dist (f x) (f y) ≤ K * dist x y) :
    LipschitzWith K f := by
  classical
  by_cases hne : IsEmpty B
  · exact LipschitzWith.of_dist_le_mul (fun x _ => (hne.false x).elim)
  rw [not_isEmpty_iff] at hne
  obtain ⟨b⟩ := hne
  let F : E → Y := fun x => if h : x ∈ B then f ⟨x, h⟩ else f b
  have hres : B.restrict F = f := by
    funext x; simp [F, Set.restrict, x.2]
  have hFc : ContinuousOn F B := by
    rw [continuousOn_iff_continuous_restrict]; change Continuous (B.restrict F); rw [hres]; exact hf
  have hFl : ∀ x ∈ B, ∀ᶠ y in nhdsWithin x B, dist (F x) (F y) ≤ K * dist x y := by
    intro x hx
    rw [← map_nhds_subtype_val ⟨x, hx⟩, Filter.eventually_map]
    filter_upwards [hloc ⟨x, hx⟩] with y hy
    simpa [F, hx, y.2, Subtype.dist_eq] using hy
  have : LipschitzWith K (B.restrict F) := (lipschitzOn_convex_of_local hB hFc hFl).to_restrict
  rwa [hres] at this

