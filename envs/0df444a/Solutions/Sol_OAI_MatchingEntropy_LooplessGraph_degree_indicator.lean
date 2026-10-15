-- Prove2me | solution 1 for OAI.MatchingEntropy.LooplessGraph.degree_indicator
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T01:47:27.775894+00:00
-- url     : https://prove2.me/submissions/0bd24747-d2ff-4f45-bf5b-811c8d15c413

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/PerfectMatching/OddCuts.lean:L56-L69
-- (upload_full_project.md Phase 4): solution for node OAI.MatchingEntropy.LooplessGraph.degree_indicator. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_MatchingEntropy
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Model
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Basic
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Duality
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Calculus
import Definitions.Def_OAI_Combinatorics_PerfectMatching_SecondVariation
import Definitions.Def_OAI_Combinatorics_PerfectMatching_OddCuts

-- ---- from OAI.Combinatorics.PerfectMatching.OddCuts ----
namespace OAI

/-!
Degree and odd-cut constraints for the perfect matching polytope.
-/

noncomputable section

open scoped BigOperators Topology
open Filter

namespace MatchingEntropy

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

namespace LooplessGraph

omit [Fintype V] in
theorem degree_indicator (G : LooplessGraph V E) (M : G.Matching) (v : V) :
    G.degree (G.indicator M) v = 1 := by
  obtain ⟨e, ⟨he, hev⟩, huniq⟩ := M.property v
  rw [degree, Finset.sum_eq_single e]
  · simp [hev, indicator, he]
  · intro e' _ hne
    by_cases hv : G.Incident v e'
    · have hh : e' ∉ M.val := by
        intro hm
        exact hne (huniq e' ⟨hm, hv⟩)
      simp [hv, indicator, hh]
    · simp [hv]
  · simp

end LooplessGraph

end MatchingEntropy

end

end OAI

-- ---- platform node ----
open OAI OAI.MatchingEntropy OAI.MatchingEntropy.LooplessGraph
open scoped BigOperators Topology
open Filter
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

omit [Fintype V] in
theorem solution (G : LooplessGraph V E) (M : G.Matching) (v : V) :
    G.degree (G.indicator M) v = 1 := by
  first
    | exact OAI.MatchingEntropy.LooplessGraph.degree_indicator G M v
    | exact OAI.MatchingEntropy.LooplessGraph.degree_indicator
    | (apply OAI.MatchingEntropy.LooplessGraph.degree_indicator <;> assumption)
    | (intros; apply OAI.MatchingEntropy.LooplessGraph.degree_indicator <;> assumption)
