-- Prove2me | solution 1 for OAI.MatchingEntropy.LooplessGraph.constraint_eventually_line
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T01:59:59.59713+00:00
-- url     : https://prove2.me/submissions/2c7c8584-743e-4bcf-870a-1168844c163e

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/PerfectMatching/Polytope.lean:L255-L293
-- (upload_full_project.md Phase 4): solution for node OAI.MatchingEntropy.LooplessGraph.constraint_eventually_line. The node keeps its source
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

omit [Fintype V] [DecidableEq E] in
theorem continuous_cutMass (G : LooplessGraph V E) (S : Finset V) :
    Continuous (fun x : E → ℝ => G.cutMass x S) := by
  unfold cutMass
  fun_prop

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
/-- Local two-sided perturbations for the degree and odd-cut constraint system. -/
theorem constraint_eventually_line (G : LooplessGraph V E) {x : E → ℝ}
    (hx : x ∈ G.constraintPolytope) (u : E → ℝ)
    (hzero : ∀ e, x e=0 → u e=0) (hdeg : ∀ v, G.degree u v=0)
    (hcut : ∀ S, Odd S.card → G.cutMass x S=1 → G.cutMass u S=0) :
    ∀ᶠ t : ℝ in 𝓝 0, x+t • u ∈ G.constraintPolytope := by
  have hn : ∀ᶠ t : ℝ in 𝓝 0, ∀ e, 0≤(x+t • u) e := by
    apply Filter.eventually_all.mpr
    intro e
    by_cases he : x e=0
    · exact Filter.Eventually.of_forall (by intro t; simp [he,hzero e he])
    · have hp : 0<x e := lt_of_le_of_ne (hx.1 e) (Ne.symm he)
      have hc : Continuous (fun t : ℝ => (x+t • u) e) := by fun_prop
      have hh : ∀ᶠ t : ℝ in 𝓝 0, 0<(x+t • u) e := (isOpen_lt continuous_const hc).mem_nhds
        (by simpa using hp : 0<(x+(0:ℝ) • u) e)
      exact hh.mono fun t ht => ht.le
  have hodd : ∀ᶠ t : ℝ in 𝓝 0, ∀ S : Finset V, Odd S.card → 1≤G.cutMass (x+t • u) S := by
    apply Filter.eventually_all.mpr
    intro S
    by_cases hS : Odd S.card
    · by_cases ht : G.cutMass x S=1
      · exact Filter.Eventually.of_forall (by
          intro t _
          have he := G.cutMass_linear x u 1 t S
          simp only [one_smul, one_mul, hcut S hS ht, mul_zero, add_zero, ht] at he
          exact he.ge)
      · have hp : 1<G.cutMass x S := lt_of_le_of_ne (hx.2.2 S hS) (Ne.symm ht)
        have hc : Continuous (fun t : ℝ => G.cutMass (x+t • u) S) :=
          (G.continuous_cutMass S).comp (by fun_prop)
        have hh : ∀ᶠ t : ℝ in 𝓝 0, 1<G.cutMass (x+t • u) S := (isOpen_lt continuous_const hc).mem_nhds
          (by simpa using hp : 1<G.cutMass (x+(0:ℝ) • u) S)
        exact hh.mono fun t ht _ => ht.le
    · exact Filter.Eventually.of_forall fun _ h => (hS h).elim
  filter_upwards [hn,hodd] with t hn hodd
  refine ⟨hn,?_,hodd⟩
  intro v
  have he := G.degree_linear x u 1 t v
  simpa only [one_smul, one_mul, hdeg, mul_zero, add_zero, hx.2.1] using he

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
    (hx : x ∈ G.constraintPolytope) (u : E → ℝ)
    (hzero : ∀ e, x e=0 → u e=0) (hdeg : ∀ v, G.degree u v=0)
    (hcut : ∀ S, Odd S.card → G.cutMass x S=1 → G.cutMass u S=0) :
    ∀ᶠ t : ℝ in 𝓝 0, x+t • u ∈ G.constraintPolytope := by
  first
    | exact OAI.MatchingEntropy.LooplessGraph.constraint_eventually_line G hx u hzero hdeg hcut
    | exact OAI.MatchingEntropy.LooplessGraph.constraint_eventually_line
    | (apply OAI.MatchingEntropy.LooplessGraph.constraint_eventually_line <;> assumption)
    | (intros; apply OAI.MatchingEntropy.LooplessGraph.constraint_eventually_line <;> assumption)
