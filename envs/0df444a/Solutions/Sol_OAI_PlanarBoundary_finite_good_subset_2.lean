-- Prove2me | solution 2 for OAI.PlanarBoundary.finite_good_subset
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T22:34:39.157669+00:00
-- url     : https://prove2.me/submissions/e664202c-e1d7-48a6-85d2-5a4a76b64c8a

-- Generated from openai/math@1581d4c lean/OAI/Probability/CriticalZ3/Peierls.lean:L111-L129
-- (upload_full_project.md Phase 4): solution for node OAI.PlanarBoundary.finite_good_subset. The node keeps its source
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
import Definitions.Def_OAI_Probability_CriticalZ3_Peierls
import Theorems.Thm_OAI_PlanarBoundary_exists_boundary_code

-- ---- from OAI.Probability.CriticalZ3.Peierls ----
namespace OAI

universe uOmega

-- [generator] trimmed: open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical Filter Topology Function
open _root_.MeasureTheory ProbabilityTheory Classical Filter Topology Function

open scoped ENNReal BigOperators Matrix

open Filter Topology

namespace PlanarBoundary
-- [generator] trimmed: open Classical _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open Classical _root_.MeasureTheory ProbabilityTheory
variable {Ω : Type uOmega} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

omit [MeasurableSpace Ω] in
/-- The main contour inclusion, without conditioning on a random boundary. -/
theorem finite_good_subset (Good : Ω → Set Point) (Bad : Point → Set Ω)
    (houtside : ∀ ω, (Good ω).Finite → ∀ x ∈ Good ω, ∀ d : Direction,
      x+outward d ∉ Good ω → ω ∈ Bad (x+outward d)) :
    {ω | (Good ω).Finite ∧ (0,0) ∈ Good ω} ⊆
      ⋃ n, ⋃ c : {c : Code n // Valid c}, candidate Bad c := by
  intro ω hω
  let X := hω.1.toFinset
  have hX : (0,0) ∈ X := by simpa only [X,Set.Finite.mem_toFinset] using hω.2
  obtain ⟨n,_,c,e,hinj,he⟩ := exists_boundary_code X hX
  refine Set.mem_iUnion.mpr ⟨n,Set.mem_iUnion.mpr ⟨⟨c,X,e,hinj,he⟩,?_⟩⟩
  intro i
  right
  change ω ∈ Bad ((traceSide c i).1+outward (traceSide c i).2)
  rw [he]
  apply houtside ω hω.1
  · simpa only [X,Set.Finite.mem_toFinset] using (e i).property.1
  · simpa only [X,Set.Finite.mem_toFinset] using (e i).property.2

end PlanarBoundary

end OAI

-- ---- platform node ----
open OAI OAI.PlanarBoundary
open _root_.MeasureTheory ProbabilityTheory Classical Filter Topology Function
open scoped ENNReal BigOperators Matrix
open Filter Topology
open Classical _root_.MeasureTheory ProbabilityTheory


theorem solution.{uOmega} : type_of% @_root_.OAI.PlanarBoundary.finite_good_subset.{uOmega} := @_root_.OAI.PlanarBoundary.finite_good_subset.{uOmega}
