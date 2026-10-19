-- Prove2me | solution 2 for OAI.CriticalZ3.Coarse.Exploration.visited_advance_mono
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T22:52:13.005803+00:00
-- url     : https://prove2.me/submissions/90c07c4b-4163-4ae4-9770-045b92d467ba

-- Generated from openai/math@1581d4c lean/OAI/Probability/CriticalZ3/ExplorationInvariant.lean:L231-L246
-- (upload_full_project.md Phase 4): solution for node OAI.CriticalZ3.Coarse.Exploration.visited_advance_mono. The node keeps its source
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
import Definitions.Def_OAI_Probability_CriticalZ3_Coarse
import Definitions.Def_OAI_Probability_CriticalZ3_AdaptiveReveals
import Definitions.Def_OAI_Probability_CriticalZ3_Exploration
import Definitions.Def_OAI_Probability_CriticalZ3_ExplorationInvariant

-- ---- from OAI.Probability.CriticalZ3.Exploration ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

-- [generator] trimmed: open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical Filter Topology Function
open _root_.MeasureTheory ProbabilityTheory Classical Filter Topology Function

open scoped ENNReal BigOperators Matrix

namespace CriticalZ3
-- [generator] trimmed: open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical InfiniteConditioning
open _root_.MeasureTheory ProbabilityTheory Classical InfiniteConditioning
namespace Coarse

namespace Packet
variable {r : ℕ}
end Packet

namespace Exploration
variable {m : Model} {r : ℕ}
end Exploration
end Coarse
end CriticalZ3

namespace CriticalZ3
-- [generator] trimmed: open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical InfiniteConditioning
open _root_.MeasureTheory ProbabilityTheory Classical InfiniteConditioning
namespace Coarse

namespace Exploration
variable {m : Model} {r : ℕ}

theorem queue_visited (s : Exploration m r) {t : Packet r} (ht : t ∈ s.queue) :
    t.vertex ∈ s.visited :=
  Finset.mem_union_right _ (List.mem_toFinset.mpr (List.mem_map.mpr ⟨t,ht,rfl⟩))

theorem processed_visited (s : Exploration m r) : s.processed ⊆ s.visited := Finset.subset_union_left

theorem advance_empty (s : Exploration m r) (q : Set.Icc (0:ℝ) 1) (δ : ℝ)
    (ω : m.Config) (h : s.queue = []) : s.advance q δ ω = s := by
  cases s with
  | mk history processed queue good bad =>
    cases history
    simp_all only [advance,after,reveal,History.observe,Finset.union_empty,Exploration.mk.injEq,History.mk.injEq,true_and,and_true]
    funext e
    exact ite_eq_right (Finset.notMem_empty e)

end Exploration
end Coarse
end CriticalZ3

end OAI

-- ---- from OAI.Probability.CriticalZ3.ExplorationInvariant ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

-- [generator] trimmed: open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical Filter Topology Function
open _root_.MeasureTheory ProbabilityTheory Classical Filter Topology Function

open scoped ENNReal BigOperators Matrix

namespace CriticalZ3
-- [generator] trimmed: open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical InfiniteConditioning
open _root_.MeasureTheory ProbabilityTheory Classical InfiniteConditioning
namespace Coarse.Exploration
variable {m : Model} {r : ℕ}

end Coarse.Exploration
end CriticalZ3

namespace CriticalZ3
-- [generator] trimmed: open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical InfiniteConditioning
open _root_.MeasureTheory ProbabilityTheory Classical InfiniteConditioning
namespace Coarse.Exploration
variable {m : Model} {r : ℕ}

theorem advance_processed (s : Exploration m r) (q : Set.Icc (0:ℝ) 1) (δ : ℝ) (ω : m.Config)
    {t : Packet r} {ts : List (Packet r)} (hq : s.queue = t::ts) :
    (s.advance q δ ω).processed = insert t.vertex s.processed := by simp only [advance,hq]

theorem advance_queue (s : Exploration m r) (q : Set.Icc (0:ℝ) 1) (δ : ℝ) (ω : m.Config)
    {t : Packet r} {ts : List (Packet r)} (hq : s.queue = t::ts) :
    (s.advance q δ ω).queue = ts ++ if s.Accept q δ t ω then s.candidates t else [] := by
  simp only [advance,hq]

theorem mem_advance_queue (s : Exploration m r) (q : Set.Icc (0:ℝ) 1) (δ : ℝ) (ω : m.Config)
    {t u : Packet r} {ts : List (Packet r)} (hq : s.queue = t::ts) :
    u ∈ (s.advance q δ ω).queue ↔ u ∈ ts ∨ (s.Accept q δ t ω ∧ u ∈ s.candidates t) := by
  rw [s.advance_queue q δ ω hq,List.mem_append]
  by_cases h : s.Accept q δ t ω <;> simp [h]

theorem processed_advance_mono (s : Exploration m r) (q : Set.Icc (0:ℝ) 1) (δ : ℝ) (ω : m.Config) :
    s.processed ⊆ (s.advance q δ ω).processed := by
  cases hq : s.queue
  · rw [advance_empty s q δ ω hq]
  · rw [s.advance_processed q δ ω hq]; exact Finset.subset_insert _ _

theorem visited_advance_mono (s : Exploration m r) (q : Set.Icc (0:ℝ) 1) (δ : ℝ) (ω : m.Config) :
    s.visited ⊆ (s.advance q δ ω).visited := by
  cases hq : s.queue with
  | nil => rw [advance_empty s q δ ω hq]
  | cons t ts =>
    intro v hv
    rcases Finset.mem_union.mp hv with hv|hv
    · exact (s.advance q δ ω).processed_visited (s.processed_advance_mono q δ ω hv)
    · obtain ⟨u,hu,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hv)
      rw [hq,List.mem_cons] at hu
      rcases hu with rfl|hu
      · apply (s.advance q δ ω).processed_visited
        rw [s.advance_processed q δ ω hq]
        exact Finset.mem_insert_self _ _
      · apply (s.advance q δ ω).queue_visited
        exact (s.mem_advance_queue q δ ω hq).mpr (Or.inl hu)

end Coarse.Exploration
end CriticalZ3

end OAI

-- ---- platform node ----
open OAI OAI.CriticalZ3 OAI.CriticalZ3.Coarse OAI.CriticalZ3.Coarse.Exploration
open _root_.MeasureTheory ProbabilityTheory Classical Filter Topology Function
open scoped ENNReal BigOperators Matrix
open _root_.MeasureTheory ProbabilityTheory Classical InfiniteConditioning


theorem solution : type_of% @_root_.OAI.CriticalZ3.Coarse.Exploration.visited_advance_mono := @_root_.OAI.CriticalZ3.Coarse.Exploration.visited_advance_mono
