-- Prove2me | solution 2 for OAI.PlanarBoundary.boundary_degree
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T22:29:33.118056+00:00
-- url     : https://prove2.me/submissions/e78a5120-b920-4f15-acaf-f8fe04cb2a5f

-- Generated from openai/math@1581d4c lean/OAI/Probability/CriticalZ3/Matching.lean:L130-L154
-- (upload_full_project.md Phase 4): solution for node OAI.PlanarBoundary.boundary_degree. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_CriticalZ3
import Definitions.Def_OAI_Probability_CriticalZ3_Basic
import Definitions.Def_OAI_Probability_CriticalZ3_ProductCylinder
import Definitions.Def_OAI_Probability_CriticalZ3_Symmetry
import Definitions.Def_OAI_Probability_CriticalZ3_QuarterFaces
import Definitions.Def_OAI_Probability_CriticalZ3_Resampling
import Definitions.Def_OAI_Probability_CriticalZ3_HyperedgeComparison
import Definitions.Def_OAI_Probability_CriticalZ3_LatticeGraph
import Definitions.Def_OAI_Probability_CriticalZ3_BoxGeometry
import Definitions.Def_OAI_Probability_CriticalZ3_LatticePaths
import Definitions.Def_OAI_Probability_CriticalZ3_EntryLayers
import Definitions.Def_OAI_Probability_CriticalZ3_SeedTrials
import Definitions.Def_OAI_Probability_CriticalZ3_Conditioning
import Definitions.Def_OAI_Probability_CriticalZ3_ConditionalQuality
import Definitions.Def_OAI_Probability_CriticalZ3_TrialCounts
import Definitions.Def_OAI_Probability_CriticalZ3_ShellProbability
import Definitions.Def_OAI_Probability_CriticalZ3_SeedQuality
import Definitions.Def_OAI_Probability_CriticalZ3_Scales
import Definitions.Def_OAI_Probability_CriticalZ3_Relay
import Definitions.Def_OAI_Probability_CriticalZ3_RelayProbability
import Definitions.Def_OAI_Probability_CriticalZ3_FiniteTrails
import Definitions.Def_OAI_Probability_CriticalZ3_PlanarBoundary
import Definitions.Def_OAI_Probability_CriticalZ3_Matching

-- ---- from OAI.Probability.CriticalZ3.Matching ----
namespace OAI

universe uAlpha uE uV

-- [generator] trimmed: open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical Filter Topology Function
open _root_.MeasureTheory ProbabilityTheory Classical Filter Topology Function

open scoped ENNReal BigOperators Matrix

/-! Exact greedy constants used in the shell trials and contour estimate. -/
namespace GreedyPacking
open Classical

variable {α : Type uAlpha}

end GreedyPacking

namespace FiniteMatching
open Classical
variable {E : Type uE} {V : Type uV} [Fintype E]

/- Choosing either endpoint of each edge of a matching gives distinct vertices. -/
end FiniteMatching

namespace PlanarBoundary
open Classical

/-- Boundary edges incident to a fixed primal vertex have at most four possibilities. -/
theorem boundary_degree (X : Finset Point) (v : Point) :
    Fintype.card {e : Boundary X // primalInside e = v ∨ primalOutside e = v} ≤ 4 := by
  let f : {e : Boundary X // primalInside e = v ∨ primalOutside e = v} → Direction :=
    fun e => e.val.val.2
  have hinj : Function.Injective f := by
    intro e g he
    have hd : e.val.val.2 = g.val.val.2 := he
    have hc : e.val.val.1 = g.val.val.1 := by
      by_cases hv : v ∈ X
      · have hve : primalInside e.val = v := e.property.resolve_right
          (by intro h; apply e.val.property.2; change primalOutside e.val ∈ X; rwa [h])
        have hvg : primalInside g.val = v := g.property.resolve_right
          (by intro h; apply g.val.property.2; change primalOutside g.val ∈ X; rwa [h])
        exact hve.trans hvg.symm
      · have hve : primalOutside e.val = v := e.property.resolve_left
          (fun h => hv (h ▸ e.val.property.1))
        have hvg : primalOutside g.val = v := g.property.resolve_left
          (fun h => hv (h ▸ g.val.property.1))
        have hh := hve.trans hvg.symm
        change e.val.val.1+outward e.val.val.2 = g.val.val.1+outward g.val.val.2 at hh
        rw [hd] at hh
        exact add_right_cancel hh
    exact Subtype.ext (Subtype.ext (Prod.ext hc hd))
  exact (Fintype.card_le_of_injective f hinj).trans_eq (Fintype.card_fin 4)

end PlanarBoundary

end OAI

-- ---- platform node ----
open OAI OAI.PlanarBoundary
open _root_.MeasureTheory ProbabilityTheory Classical Filter Topology Function
open scoped ENNReal BigOperators Matrix
open Classical


theorem solution : type_of% @_root_.OAI.PlanarBoundary.boundary_degree := @_root_.OAI.PlanarBoundary.boundary_degree
