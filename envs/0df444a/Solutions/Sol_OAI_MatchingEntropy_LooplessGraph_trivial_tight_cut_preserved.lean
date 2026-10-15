-- Prove2me | solution 1 for OAI.MatchingEntropy.LooplessGraph.trivial_tight_cut_preserved
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T02:02:11.883464+00:00
-- url     : https://prove2.me/submissions/a39634e0-9b24-423f-a853-d0df792b1e13

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/PerfectMatching/Polytope.lean:L307-L326
-- (upload_full_project.md Phase 4): solution for node OAI.MatchingEntropy.LooplessGraph.trivial_tight_cut_preserved. The node keeps its source
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
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Coupling
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Contraction
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Polytope

-- ---- from OAI.Combinatorics.PerfectMatching.Contraction ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-!
Contraction of tight odd cuts and gluing of perfect matchings and their laws.
-/

noncomputable section

open scoped BigOperators Topology
open Filter

namespace MatchingEntropy

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

namespace LooplessGraph

theorem odd_compl_of_even {W : Type*} [Fintype W] [DecidableEq W]
    (hn : Even (Fintype.card W)) {T : Finset W} (hT : Odd T.card) : Odd Tᶜ.card := by
  rcases hn with ⟨k,hk⟩
  rcases hT with ⟨l,hl⟩
  have hle := Finset.card_le_univ T
  rw [Finset.card_compl]
  refine ⟨k-l-1, ?_⟩
  omega

end LooplessGraph

end MatchingEntropy

end

end OAI

-- ---- from OAI.Combinatorics.PerfectMatching.Polytope ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-!
Tutte's criterion and Edmonds' perfect matching polytope theorem for multigraphs.
-/

noncomputable section

open scoped BigOperators Topology
open Filter

namespace MatchingEntropy

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

namespace LooplessGraph

omit [DecidableEq E] in
/-- Without a nontrivial tight odd cut, only degrees constrain a supported direction. -/
theorem trivial_tight_cut_preserved (G : LooplessGraph V E) {x : E → ℝ}
    (heven : Even (Fintype.card V))
    (hnt : ¬∃ S : Finset V, Odd S.card ∧ 3≤S.card ∧ 3≤Sᶜ.card ∧ G.cutMass x S=1)
    (u : E → ℝ) (hdeg : ∀ v, G.degree u v=0) :
    ∀ S, Odd S.card → G.cutMass x S=1 → G.cutMass u S=0 := by
  intro S hS ht
  have hc := odd_compl_of_even heven hS
  have hsmall : S.card=1 ∨ Sᶜ.card=1 := by
    have hn : ¬ (3≤S.card ∧ 3≤Sᶜ.card) := fun h => hnt ⟨S,hS,h.1,h.2,ht⟩
    rcases hS with ⟨k,hk⟩
    rcases hc with ⟨l,hl⟩
    omega
  rcases hsmall with hs | hs
  · obtain ⟨v,rfl⟩ := Finset.card_eq_one.mp hs
    simpa using hdeg v
  · obtain ⟨v,hv⟩ := Finset.card_eq_one.mp hs
    have hh : G.cutMass u Sᶜ=0 := by rw [hv,cutMass_singleton,hdeg]
    simpa only [cutMass,cut_compl] using hh

end LooplessGraph

end MatchingEntropy

end

end OAI

-- ---- platform node ----
open OAI OAI.MatchingEntropy OAI.MatchingEntropy.LooplessGraph
open scoped BigOperators Topology
open Filter
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

omit [DecidableEq E] in
theorem solution (G : LooplessGraph V E) {x : E → ℝ}
    (heven : Even (Fintype.card V))
    (hnt : ¬∃ S : Finset V, Odd S.card ∧ 3≤S.card ∧ 3≤Sᶜ.card ∧ G.cutMass x S=1)
    (u : E → ℝ) (hdeg : ∀ v, G.degree u v=0) :
    ∀ S, Odd S.card → G.cutMass x S=1 → G.cutMass u S=0 := by
  first
    | exact OAI.MatchingEntropy.LooplessGraph.trivial_tight_cut_preserved G heven hnt u hdeg
    | exact OAI.MatchingEntropy.LooplessGraph.trivial_tight_cut_preserved
    | (apply OAI.MatchingEntropy.LooplessGraph.trivial_tight_cut_preserved <;> assumption)
    | (intros; apply OAI.MatchingEntropy.LooplessGraph.trivial_tight_cut_preserved <;> assumption)
