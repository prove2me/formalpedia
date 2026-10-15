-- Prove2me | solution 1 for OAI.MatchingEntropy.LooplessGraph.supportSimple_has_perfectMatching
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T01:57:49.269161+00:00
-- url     : https://prove2.me/submissions/6fb1f24a-d03b-4545-8245-8c43ebcb5e7d

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/PerfectMatching/Polytope.lean:L140-L194
-- (upload_full_project.md Phase 4): solution for node OAI.MatchingEntropy.LooplessGraph.supportSimple_has_perfectMatching. The node keeps its source
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
import Theorems.Thm_OAI_MatchingEntropy_LooplessGraph_odd_family_bound

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

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
 theorem supportSimple_edge (G : LooplessGraph V E) {x : E → ℝ} {e : E} (he : 0 < x e) :
    (G.supportSimple x).Adj (G.left e) (G.right e) := ⟨e,he,Or.inl ⟨rfl,rfl⟩⟩

omit [DecidableEq E] in
theorem supportSimple_has_perfectMatching (G : LooplessGraph V E) {x : E → ℝ}
    (hx : x ∈ G.constraintPolytope) :
    ∃ M : (G.supportSimple x).Subgraph, M.IsPerfectMatching := by
  classical
  apply SimpleGraph.tutte.mpr
  intro U
  let H := (⊤ : (G.supportSimple x).Subgraph).deleteVerts U
  let C := H.coe.oddComponents
  let : Fintype C := Fintype.ofFinite C
  let T : C → Finset V := fun c => (Subtype.val '' c.val.supp).toFinset
  have hnot : ∀ v : H.verts, v.val ∉ U := by
    intro v
    have hv := v.property
    simpa [H] using hv
  have hT : ∀ c : C, ∀ v : V, v ∈ T c ↔ ∃ w : H.verts, w ∈ c.val.supp ∧ w.val=v := by
    intro c v
    simp [T]
  have hodd : ∀ c : C, Odd (T c).card := by
    intro c
    have hc := c.property
    change Odd c.val.supp.ncard at hc
    change Odd ((Subtype.val '' c.val.supp).toFinset.card)
    rw [← Set.ncard_eq_toFinset_card', Set.ncard_image_of_injective _ Subtype.val_injective]
    exact hc
  have hdisj : ∀ c v, v ∈ T c → v ∉ U.toFinset := by
    intro c v hv
    obtain ⟨w,_,rfl⟩ := (hT c v).mp hv
    simpa using hnot w
  have huniq : ∀ a b v, v ∈ T a → v ∈ T b → a=b := by
    intro a b v ha hb
    obtain ⟨wa,hwa,rfl⟩ := (hT a v).mp ha
    obtain ⟨wb,hwb,he⟩ := (hT b wa.val).mp hb
    have hw : wb=wa := Subtype.ext he
    subst wb
    exact Subtype.ext (SimpleGraph.ConnectedComponent.eq_of_common_vertex hwa hwb)
  have hclosed : ∀ e, 0<x e → G.left e ∉ U.toFinset → G.right e ∉ U.toFinset →
      ∀ c, G.left e ∈ T c ↔ G.right e ∈ T c := by
    intro e he hl hr c
    have hl' : G.left e ∈ H.verts := by simpa [H] using hl
    have hr' : G.right e ∈ H.verts := by simpa [H] using hr
    have ha : H.Adj (G.left e) (G.right e) := by
      simpa [H, SimpleGraph.Subgraph.deleteVerts_adj] using
        And.intro hl (And.intro hr (G.supportSimple_edge he))
    change G.left e ∈ (Subtype.val '' c.val.supp).toFinset ↔
      G.right e ∈ (Subtype.val '' c.val.supp).toFinset
    simp only [Set.mem_toFinset]
    exact ⟨fun h => SimpleGraph.ConnectedComponent.mem_coe_supp_of_adj h hr' ha,
      fun h => SimpleGraph.ConnectedComponent.mem_coe_supp_of_adj h hl' ha.symm⟩
  have hb := G.odd_family_bound hx U.toFinset T hodd hdisj huniq hclosed
  change ¬ U.ncard < H.coe.oddComponents.ncard
  have hcard : Fintype.card C = H.coe.oddComponents.ncard := by
    simp [C, ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
  rw [hcard] at hb
  exact not_lt_of_ge (by simpa only [← Set.ncard_eq_toFinset_card'] using hb)

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
    (hx : x ∈ G.constraintPolytope) :
    ∃ M : (G.supportSimple x).Subgraph, M.IsPerfectMatching := by
  first
    | exact OAI.MatchingEntropy.LooplessGraph.supportSimple_has_perfectMatching G hx
    | exact OAI.MatchingEntropy.LooplessGraph.supportSimple_has_perfectMatching
    | (apply OAI.MatchingEntropy.LooplessGraph.supportSimple_has_perfectMatching <;> assumption)
    | (intros; apply OAI.MatchingEntropy.LooplessGraph.supportSimple_has_perfectMatching <;> assumption)
