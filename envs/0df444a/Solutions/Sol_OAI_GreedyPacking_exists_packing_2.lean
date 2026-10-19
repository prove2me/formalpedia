-- Prove2me | solution 2 for OAI.GreedyPacking.exists_packing
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T22:27:27.372672+00:00
-- url     : https://prove2.me/submissions/d2bf2902-34d2-44d1-895c-5246e2bde3d1

-- Generated from openai/math@1581d4c lean/OAI/Probability/CriticalZ3/Matching.lean:L17-L49
-- (upload_full_project.md Phase 4): solution for node OAI.GreedyPacking.exists_packing. The node keeps its source
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

/-- Greedily deleting at most M conflicts loses at most M elements per choice. -/
theorem exists_packing (t : Finset α) (R : α → α → Prop)
    (hrefl : ∀ a ∈ t, R a a) (hsym : ∀ a ∈ t, ∀ b ∈ t, R a b → R b a)
    (M : ℕ) (hM : ∀ a ∈ t, (t.filter (R a)).card ≤ M) :
    ∃ s : Finset α, s ⊆ t ∧ (s : Set α).Pairwise (fun a b => ¬R a b) ∧ t.card ≤ M*s.card := by
  classical
  induction t using Finset.strongInduction with
  | H t ih =>
    by_cases ht : t = ∅
    · subst t
      exact ⟨∅,by simp,by simp,by simp⟩
    obtain ⟨a,ha⟩ := Finset.nonempty_iff_ne_empty.mpr ht
    let u := t.filter (fun b => ¬R a b)
    have hu : u ⊆ t := Finset.filter_subset _ _
    have hau : a ∉ u := by simp [u,hrefl a ha]
    have hut : u ⊂ t := Finset.ssubset_iff_subset_ne.mpr ⟨hu,by intro h; exact hau (h.symm ▸ ha)⟩
    obtain ⟨s,hs,hpair,hcard⟩ := ih u hut
      (fun b hb => hrefl b (hu hb))
      (fun b hb c hc h => hsym b (hu hb) c (hu hc) h)
      (fun b hb => le_trans (Finset.card_le_card (Finset.filter_subset_filter _ hu)) (hM b (hu hb)))
    refine ⟨insert a s,Finset.insert_subset ha (hs.trans hu),?_,?_⟩
    · simp only [Finset.coe_insert]
      rw [Set.pairwise_insert]
      refine ⟨hpair,?_⟩
      intro b hb _
      exact ⟨(Finset.mem_filter.mp (hs hb)).2,
        fun h => (Finset.mem_filter.mp (hs hb)).2 (hsym b (hu (hs hb)) a ha h)⟩
    · have has : a ∉ s := fun h => hau (hs h)
      rw [Finset.card_insert_of_notMem has]
      have he : (t.filter (R a)).card+u.card = t.card := by
        exact Finset.card_filter_add_card_filter_not (s := t) (R a)
      have hm := hM a ha
      nlinarith

end GreedyPacking

namespace FiniteMatching
open Classical
variable {E : Type uE} {V : Type uV} [Fintype E]

/- Choosing either endpoint of each edge of a matching gives distinct vertices. -/
end FiniteMatching

namespace PlanarBoundary
open Classical

end PlanarBoundary

end OAI

-- ---- platform node ----
open OAI OAI.GreedyPacking
open _root_.MeasureTheory ProbabilityTheory Classical Filter Topology Function
open scoped ENNReal BigOperators Matrix
open Classical


theorem solution.{uAlpha} : type_of% @_root_.OAI.GreedyPacking.exists_packing.{uAlpha} := @_root_.OAI.GreedyPacking.exists_packing.{uAlpha}
