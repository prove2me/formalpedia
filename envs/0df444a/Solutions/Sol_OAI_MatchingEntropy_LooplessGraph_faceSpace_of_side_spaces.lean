-- Prove2me | solution 1 for OAI.MatchingEntropy.LooplessGraph.faceSpace_of_side_spaces
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T02:06:29.606308+00:00
-- url     : https://prove2.me/submissions/1f8963e6-e237-4922-84db-69a0aaddf73c

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/PerfectMatching/Face.lean:L149-L178
-- (upload_full_project.md Phase 4): solution for node OAI.MatchingEntropy.LooplessGraph.faceSpace_of_side_spaces. The node keeps its source
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
import Theorems.Thm_OAI_MatchingEntropy_LooplessGraph_constraint_eventually_line
import Theorems.Thm_OAI_MatchingEntropy_LooplessGraph_constraint_subset_polytope_aux
import Theorems.Thm_OAI_MatchingEntropy_LooplessGraph_couple_laws
import Theorems.Thm_OAI_MatchingEntropy_LooplessGraph_degree_indicator
import Theorems.Thm_OAI_MatchingEntropy_LooplessGraph_mem_polytope_iff
import Theorems.Thm_OAI_MatchingEntropy_LooplessGraph_restriction_mem_constraints

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

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem incidence_sum (G : LooplessGraph V E) (e : E) (S : Finset V) :
    (∑ v ∈ S, if G.Incident v e then (1:ℕ) else 0) =
      (if G.left e ∈ S then 1 else 0) + (if G.right e ∈ S then 1 else 0) := by
  have hv : ∀ v, (if G.Incident v e then (1:ℕ) else 0) =
      (if v = G.left e then 1 else 0) + (if v = G.right e then 1 else 0) := by
    intro v
    by_cases hl : v = G.left e <;> by_cases hr : v = G.right e
    · exact ((G.loopless e) (hl.symm.trans hr)).elim
    · simp [Incident, hl, G.loopless e, Ne.symm (G.loopless e)]
    · simp [Incident, hr, G.loopless e, Ne.symm (G.loopless e)]
    · simp [Incident, Ne.symm hl, Ne.symm hr, hl, hr]
  simp_rw [hv, Finset.sum_add_distrib]
  simp

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem matching_incidence_count (G : LooplessGraph V E) (M : G.Matching)
    (S : Finset V) :
    (∑ e ∈ M.val, ((if G.left e ∈ S then (1:ℕ) else 0) +
      (if G.right e ∈ S then 1 else 0))) = S.card := by
  have hsum : ∀ v, (∑ e ∈ M.val, if G.Incident v e then (1:ℕ) else 0) = 1 := by
    intro v
    obtain ⟨e, ⟨he, hev⟩, hu⟩ := M.property v
    rw [Finset.sum_eq_single e]
    · simp [hev]
    · intro e' he' hh
      have hv : ¬G.Incident v e' := fun hv => hh (hu e' ⟨he', hv⟩)
      simp [hv]
    · simp [he]
  calc
    _ = ∑ e ∈ M.val, ∑ v ∈ S, if G.Incident v e then (1:ℕ) else 0 := by
      simp_rw [incidence_sum]
    _ = ∑ v ∈ S, ∑ e ∈ M.val, if G.Incident v e then (1:ℕ) else 0 := Finset.sum_comm
    _ = S.card := by simp_rw [hsum]; simp

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem matching_crosses_odd (G : LooplessGraph V E) (M : G.Matching)
    (S : Finset V) (hS : Odd S.card) : ∃ e ∈ M.val, G.Crosses S e := by
  by_contra h
  push Not at h
  have heq : ∀ e ∈ M.val, ((if G.left e ∈ S then (1:ℕ) else 0) +
      (if G.right e ∈ S then 1 else 0)) = 2*(if G.left e ∈ S then 1 else 0) := by
    intro e he
    have hc := h e he
    simp only [Crosses] at hc
    by_cases hl : G.left e ∈ S <;> by_cases hr : G.right e ∈ S <;>
      simp_all
  have hh := G.matching_incidence_count M S
  have heqsum := Finset.sum_congr rfl heq
  rw [heqsum, ← Finset.mul_sum] at hh
  obtain ⟨k, hk⟩ := hS
  omega

omit [Fintype V] [DecidableEq E] in
theorem convex_constraintPolytope (G : LooplessGraph V E) :
    Convex ℝ G.constraintPolytope := by
  intro x hx y hy a b ha hb hab
  refine ⟨fun e => add_nonneg (mul_nonneg ha (hx.1 e)) (mul_nonneg hb (hy.1 e)), ?_, ?_⟩
  · intro v
    rw [degree_linear, hx.2.1, hy.2.1, mul_one, mul_one, hab]
  · intro S hS
    rw [cutMass_linear]
    calc
      1 = a*1+b*1 := by linarith
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left (hx.2.2 S hS) ha)
        (mul_le_mul_of_nonneg_left (hy.2.2 S hS) hb)

omit [Fintype V] in
theorem indicator_mem_constraintPolytope (G : LooplessGraph V E) (M : G.Matching) :
    G.indicator M ∈ G.constraintPolytope := by
  refine ⟨?_, G.degree_indicator M, ?_⟩
  · intro e; simp [indicator]; split <;> norm_num
  · intro S hS
    obtain ⟨e, he, hc⟩ := G.matching_crosses_odd M S hS
    have h := Finset.single_le_sum (f := G.indicator M)
      (s := G.cut S) (a := e) (by intro e' _; simp [indicator]; split <;> norm_num)
      ((G.mem_cut S e).mpr hc)
    simpa only [cutMass, indicator, he, ite_true] using h

omit [Fintype V] in
theorem polytope_subset_constraintPolytope (G : LooplessGraph V E) :
    G.polytope ⊆ G.constraintPolytope := by
  apply convexHull_min
  · rintro x ⟨M, rfl⟩
    exact G.indicator_mem_constraintPolytope M
  · exact G.convex_constraintPolytope

end LooplessGraph

end MatchingEntropy

end

end OAI

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

/-- Edmonds' perfect matching polytope equality, with parallel edges retained. -/
theorem polytope_eq_constraints (G : LooplessGraph V E) (heven : Even (Fintype.card V)) :
    G.polytope = G.constraintPolytope := by
  exact Set.Subset.antisymm G.polytope_subset_constraintPolytope
    (constraint_subset_polytope_aux (Fintype.card V) G rfl heven)

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

omit [DecidableEq E] in
 theorem faceSpace_eventually_line (G : LooplessGraph V E) {x : E → ℝ}
    (hx : x ∈ G.constraintPolytope) {u : {e // 0<x e} → ℝ} (hu : u ∈ G.faceSpace x) :
    ∀ᶠ t : ℝ in 𝓝 0, x+t • positiveExtension x u ∈ G.constraintPolytope := by
  exact G.constraint_eventually_line hx _ (fun e he => positiveExtension_zero x u he)
    (congrFun hu.1) hu.2

omit [Fintype V] [DecidableEq E] in
 theorem faceSpace_of_eventually_line (G : LooplessGraph V E) {x : E → ℝ}
    (hx : x ∈ G.constraintPolytope) {u : {e // 0<x e} → ℝ}
    (hu : ∀ᶠ t : ℝ in 𝓝 0, x+t • positiveExtension x u ∈ G.constraintPolytope) :
    u ∈ G.faceSpace x := by
  have hu' : ∀ᶠ t : ℝ in 𝓝 0, x+(-t) • positiveExtension x u ∈ G.constraintPolytope := by
    have hc : Tendsto (fun t : ℝ => -t) (𝓝 0) (𝓝 0) := by simpa using continuous_neg.tendsto (0:ℝ)
    exact hc.eventually hu
  have hh : ∀ᶠ t : ℝ in 𝓝[>] 0,
      (x+t • positiveExtension x u ∈ G.constraintPolytope ∧
        x+(-t) • positiveExtension x u ∈ G.constraintPolytope) ∧ 0<t :=
    ((hu.and hu').filter_mono nhdsWithin_le_nhds).and eventually_mem_nhdsWithin
  obtain ⟨a,⟨ha,hna⟩,ha0⟩ := hh.exists
  refine ⟨?_,?_⟩
  · ext v
    have he := G.degree_linear x (positiveExtension x u) 1 a v
    simp only [one_smul,one_mul,hx.2.1,ha.2.1] at he
    change G.degree (positiveExtension x u) v=0
    nlinarith
  · intro S hS ht
    have he := G.cutMass_linear x (positiveExtension x u) 1 a S
    have he' := G.cutMass_linear x (positiveExtension x u) 1 (-a) S
    simp only [one_smul,one_mul,ht] at he he'
    have hp := ha.2.2 S hS
    have hn := hna.2.2 S hS
    change G.cutMass (positiveExtension x u) S=0
    nlinarith

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
 theorem sideMarginal_line (G : LooplessGraph V E) (x : E → ℝ) (S : Finset V)
    (u : {e // 0<x e} → ℝ) (t : ℝ) :
    G.sideMarginal (x+t • positiveExtension x u) S = G.sideMarginal x S +
      t • positiveExtension (G.sideMarginal x S) (G.sideRestriction x S u) := by
  rfl

/-- Pullbacks of both contraction face spaces preserve every original active cut,
including cuts crossing the chosen tight cut. This is the substantive coupling step. -/
theorem faceSpace_of_side_spaces (G : LooplessGraph V E) {x : E → ℝ}
    (heven : Even (Fintype.card V)) (hx : x ∈ G.constraintPolytope)
    (S : Finset V) (hS : Odd S.card) (ht : G.cutMass x S=1)
    {u : {e // 0<x e} → ℝ}
    (h1 : G.sideRestriction x S u ∈ (G.onSide S).faceSpace (G.sideMarginal x S))
    (h2 : G.sideRestriction x Sᶜ u ∈ (G.onSide Sᶜ).faceSpace (G.sideMarginal x Sᶜ)) :
    u ∈ G.faceSpace x := by
  have hc := odd_compl_of_even heven hS
  have htc : G.cutMass x Sᶜ=1 := by simpa only [cutMass,cut_compl] using ht
  have hx1 := G.restriction_mem_constraints hx S hS ht
  have hx2 := G.restriction_mem_constraints hx Sᶜ hc htc
  have hv1 : Even (Fintype.card (Option {v // v ∈ S})) := by
    simpa only [Fintype.card_option,Fintype.card_coe] using hS.add_odd odd_one
  have hv2 : Even (Fintype.card (Option {v // v ∈ Sᶜ})) := by
    simpa only [Fintype.card_option,Fintype.card_coe] using hc.add_odd odd_one
  apply G.faceSpace_of_eventually_line hx
  filter_upwards [(G.onSide S).faceSpace_eventually_line hx1 h1,
    (G.onSide Sᶜ).faceSpace_eventually_line hx2 h2] with t ht1 ht2
  rw [← G.sideMarginal_line x S u t] at ht1
  rw [← G.sideMarginal_line x Sᶜ u t] at ht2
  have hp1 : G.sideMarginal (x+t • positiveExtension x u) S ∈ (G.onSide S).polytope := by
    rwa [(G.onSide S).polytope_eq_constraints hv1]
  have hp2 : G.sideMarginal (x+t • positiveExtension x u) Sᶜ ∈ (G.onSide Sᶜ).polytope := by
    rwa [(G.onSide Sᶜ).polytope_eq_constraints hv2]
  obtain ⟨p,hp,hpx⟩ := ((G.onSide S).mem_polytope_iff _).mp hp1
  obtain ⟨q,hq,hqx⟩ := ((G.onSide Sᶜ).mem_polytope_iff _).mp hp2
  have hp := (G.mem_polytope_iff _).mpr (G.couple_laws S _ hp hq (congrFun hpx) (congrFun hqx))
  exact G.polytope_subset_constraintPolytope hp

end LooplessGraph

end MatchingEntropy

end

end OAI

-- ---- platform node ----
open OAI OAI.MatchingEntropy OAI.MatchingEntropy.LooplessGraph
open scoped BigOperators Topology
open Filter
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

theorem solution (G : LooplessGraph V E) {x : E → ℝ}
    (heven : Even (Fintype.card V)) (hx : x ∈ G.constraintPolytope)
    (S : Finset V) (hS : Odd S.card) (ht : G.cutMass x S=1)
    {u : {e // 0<x e} → ℝ}
    (h1 : G.sideRestriction x S u ∈ (G.onSide S).faceSpace (G.sideMarginal x S))
    (h2 : G.sideRestriction x Sᶜ u ∈ (G.onSide Sᶜ).faceSpace (G.sideMarginal x Sᶜ)) :
    u ∈ G.faceSpace x := by
  first
    | exact OAI.MatchingEntropy.LooplessGraph.faceSpace_of_side_spaces G heven hx S hS ht h1 h2
    | exact OAI.MatchingEntropy.LooplessGraph.faceSpace_of_side_spaces
    | (apply OAI.MatchingEntropy.LooplessGraph.faceSpace_of_side_spaces <;> assumption)
    | (intros; apply OAI.MatchingEntropy.LooplessGraph.faceSpace_of_side_spaces <;> assumption)
