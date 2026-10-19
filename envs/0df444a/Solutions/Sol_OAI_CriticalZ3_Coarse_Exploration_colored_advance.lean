-- Prove2me | solution 1 for OAI.CriticalZ3.Coarse.Exploration.colored_advance
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T21:13:08.75316+00:00
-- url     : https://prove2.me/submissions/8a6f0ba2-84a9-4020-a51f-4bd7497e1ad5

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

open OAI OAI.CriticalZ3 OAI.CriticalZ3.Coarse OAI.CriticalZ3.Coarse.Exploration
open _root_.MeasureTheory ProbabilityTheory Classical Filter Topology Function
open scoped ENNReal BigOperators Matrix
open _root_.MeasureTheory ProbabilityTheory Classical InfiniteConditioning
variable {m : Model} {r : ℕ}


theorem solution {q : Set.Icc (0:ℝ) 1} {δ : ℝ} {s : Exploration m r}
    (hs : s.Valid q δ) (hc : s.Colored) (ω : m.Config) : (s.advance q δ ω).Colored := by
  rcases hq : s.queue with _ | ⟨t, ts⟩
  · constructor
    · simp only [Exploration.advance, hq]; exact hc.partition
    · simp only [Exploration.advance, hq]; exact hc.disjoint
  · have ht : t.vertex ∉ s.processed := hs.unprocessed t (by rw [hq]; exact List.mem_cons_self)
    rw [hc.partition, Finset.mem_union, not_or] at ht
    constructor
    · simp only [Exploration.advance, hq]
      rw [hc.partition]
      split_ifs
      · rw [Finset.insert_union]
      · rw [Finset.union_insert]
    · simp only [Exploration.advance, hq]
      split_ifs
      · exact Finset.disjoint_insert_left.mpr ⟨ht.2, hc.disjoint⟩
      · exact Finset.disjoint_insert_right.mpr ⟨ht.1, hc.disjoint⟩

