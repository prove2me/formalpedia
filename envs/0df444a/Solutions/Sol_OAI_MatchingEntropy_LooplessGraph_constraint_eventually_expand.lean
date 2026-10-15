-- Prove2me | solution 1 for OAI.MatchingEntropy.LooplessGraph.constraint_eventually_expand
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T02:09:51.554621+00:00
-- url     : https://prove2.me/submissions/b9581993-5802-4ccd-bd05-6ad55e38a4c0

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/PerfectMatching/Face.lean:L262-L300
-- (upload_full_project.md Phase 4): solution for node OAI.MatchingEntropy.LooplessGraph.constraint_eventually_expand. The node keeps its source
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
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Face

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

omit [Fintype V] [DecidableEq E] in
 theorem degree_sub (G : LooplessGraph V E) (x y : E → ℝ) (v : V) :
    G.degree (x-y) v = G.degree x v-G.degree y v := by
  have h := G.degree_linear x y 1 (-1) v
  simpa [sub_eq_add_neg] using h

omit [Fintype V] [DecidableEq E] in
 theorem cutMass_sub (G : LooplessGraph V E) (x y : E → ℝ) (S : Finset V) :
    G.cutMass (x-y) S = G.cutMass x S-G.cutMass y S := by
  have h := G.cutMass_linear x y 1 (-1) S
  simpa [sub_eq_add_neg] using h

end LooplessGraph

end MatchingEntropy

end

end OAI

-- ---- from OAI.Combinatorics.PerfectMatching.Face ----
namespace OAI

/-!
Active face spaces, their codimension bounds, and local radial extension.
-/

noncomputable section

open scoped BigOperators Topology
open Filter

namespace MatchingEntropy

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

namespace LooplessGraph

omit [Fintype V] [DecidableEq E] in
 theorem degree_add_smul (G : LooplessGraph V E) (x u : E → ℝ) (t : ℝ) (v : V) :
    G.degree (x+t • u) v=G.degree x v+t*G.degree u v := by
  simpa using G.degree_linear x u 1 t v

omit [Fintype V] [DecidableEq E] in
 theorem cutMass_add_smul (G : LooplessGraph V E) (x u : E → ℝ) (t : ℝ) (S : Finset V) :
    G.cutMass (x+t • u) S=G.cutMass x S+t*G.cutMass u S := by
  simpa using G.cutMass_linear x u 1 t S

omit [DecidableEq E] in
/-- Radial extension for this actual matching polytope. This is needed to prove
lower semicontinuity of the maximum entropy without assuming its regularity. -/
theorem constraint_eventually_expand (G : LooplessGraph V E) {x : E → ℝ}
    (hx : x ∈ G.constraintPolytope) {t : ℝ} (ht : 0<t) :
    ∀ᶠ y in 𝓝[G.constraintPolytope] x, x+t⁻¹ • (y-x) ∈ G.constraintPolytope := by
  have hn : ∀ᶠ y in 𝓝[G.constraintPolytope] x, ∀ e, 0≤(x+t⁻¹ • (y-x)) e := by
    apply Filter.eventually_all.mpr
    intro e
    by_cases he : x e=0
    · filter_upwards [eventually_mem_nhdsWithin] with y hy
      simpa [he] using mul_nonneg (inv_nonneg.mpr ht.le) (hy.1 e)
    · have hp : 0<x e := lt_of_le_of_ne (hx.1 e) (Ne.symm he)
      have hc : Continuous (fun y : E → ℝ => (x+t⁻¹ • (y-x)) e) := by fun_prop
      have hh : ∀ᶠ y : E → ℝ in 𝓝 x, 0<(x+t⁻¹ • (y-x)) e :=
        (isOpen_lt continuous_const hc).mem_nhds (by simpa using hp)
      exact (hh.filter_mono nhdsWithin_le_nhds).mono fun y hy => hy.le
  have hodd : ∀ᶠ y in 𝓝[G.constraintPolytope] x,
      ∀ S : Finset V, Odd S.card → 1≤G.cutMass (x+t⁻¹ • (y-x)) S := by
    apply Filter.eventually_all.mpr
    intro S
    by_cases hS : Odd S.card
    · by_cases hs : G.cutMass x S=1
      · filter_upwards [eventually_mem_nhdsWithin] with y hy _
        rw [cutMass_add_smul,cutMass_sub,hs]
        have hh := mul_nonneg (inv_nonneg.mpr ht.le) (sub_nonneg.mpr (hy.2.2 S hS))
        linarith
      · have hp : 1<G.cutMass x S := lt_of_le_of_ne (hx.2.2 S hS) (Ne.symm hs)
        have hc : Continuous (fun y : E → ℝ => G.cutMass (x+t⁻¹ • (y-x)) S) :=
          (G.continuous_cutMass S).comp (by fun_prop)
        have hh : ∀ᶠ y : E → ℝ in 𝓝 x, 1<G.cutMass (x+t⁻¹ • (y-x)) S :=
          (isOpen_lt continuous_const hc).mem_nhds (by simpa using hp)
        exact (hh.filter_mono nhdsWithin_le_nhds).mono fun y hy _ => hy.le
    · exact Filter.Eventually.of_forall fun _ h => (hS h).elim
  filter_upwards [hn,hodd,eventually_mem_nhdsWithin] with y hn hodd hy
  refine ⟨hn,?_,hodd⟩
  intro v
  rw [degree_add_smul,degree_sub,hx.2.1,hy.2.1]
  ring

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
    (hx : x ∈ G.constraintPolytope) {t : ℝ} (ht : 0<t) :
    ∀ᶠ y in 𝓝[G.constraintPolytope] x, x+t⁻¹ • (y-x) ∈ G.constraintPolytope := by
  first
    | exact OAI.MatchingEntropy.LooplessGraph.constraint_eventually_expand G hx ht
    | exact OAI.MatchingEntropy.LooplessGraph.constraint_eventually_expand
    | (apply OAI.MatchingEntropy.LooplessGraph.constraint_eventually_expand <;> assumption)
    | (intros; apply OAI.MatchingEntropy.LooplessGraph.constraint_eventually_expand <;> assumption)
