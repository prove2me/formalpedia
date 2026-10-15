-- Prove2me | solution 1 for OAI.MatchingEntropy.LooplessGraph.constraint_subset_polytope_aux
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T02:03:38.201444+00:00
-- url     : https://prove2.me/submissions/17a9855c-6012-43f8-bc28-f9d1c5936ad6

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/PerfectMatching/Polytope.lean:L347-L384
-- (upload_full_project.md Phase 4): solution for node OAI.MatchingEntropy.LooplessGraph.constraint_subset_polytope_aux. The node keeps its source
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
import Theorems.Thm_OAI_MatchingEntropy_LooplessGraph_constraint_eventually_line
import Theorems.Thm_OAI_MatchingEntropy_LooplessGraph_couple_laws
import Theorems.Thm_OAI_MatchingEntropy_LooplessGraph_degree_indicator
import Theorems.Thm_OAI_MatchingEntropy_LooplessGraph_mem_polytope_iff
import Theorems.Thm_OAI_MatchingEntropy_LooplessGraph_restriction_mem_constraints
import Theorems.Thm_OAI_MatchingEntropy_LooplessGraph_supportSimple_has_perfectMatching
import Theorems.Thm_OAI_MatchingEntropy_LooplessGraph_trivial_tight_cut_preserved
import Theorems.Thm_OAI_MatchingEntropy_extreme_point_direction_zero

-- ---- from OAI.Combinatorics.PerfectMatching.Simplex ----
namespace OAI

/-!
Probability vectors on finite types, with their convexity and compactness properties.
The function-space simplex is the range of the weights of `Convexity.StdSimplex`.
-/

noncomputable section

open scoped BigOperators

namespace MatchingEntropy

theorem isCompact_probabilitySimplex (Index : Type*) [Fintype Index] :
    IsCompact (probabilitySimplex Index) := by
  exact isCompact_stdSimplex ℝ Index

end MatchingEntropy

end

end OAI

-- ---- from OAI.Combinatorics.PerfectMatching.Basic ----
namespace OAI

/-!
Finite loopless multigraphs, perfect matching indicators, and their convex hull.
The edge type distinguishes parallel edges. Feasible laws are probability vectors
on perfect matchings with a prescribed mean.
-/

noncomputable section

open scoped BigOperators Topology
open Filter

namespace MatchingEntropy

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

namespace LooplessGraph

omit [Fintype V] [DecidableEq V] in
theorem continuous_mean (G : LooplessGraph V E) : Continuous G.mean := by
  unfold mean
  fun_prop

omit [Fintype V] [DecidableEq V] in
theorem compact_polytope (G : LooplessGraph V E) : IsCompact G.polytope := by
  have heq : G.polytope = G.mean '' probabilitySimplex G.Matching := by
    ext y
    rw [G.mem_polytope_iff]
    rfl
  rw [heq]
  exact (isCompact_probabilitySimplex G.Matching).image G.continuous_mean

end LooplessGraph

end MatchingEntropy

end

end OAI

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

omit [Fintype V] [DecidableEq E] in
theorem constraint_coordinate_le_one (G : LooplessGraph V E) {x : E → ℝ}
    (hx : x ∈ G.constraintPolytope) (e : E) : x e ≤ 1 := by
  have h := Finset.single_le_sum (f := fun e' => if G.Incident (G.left e) e' then x e' else 0)
    (s := Finset.univ) (a := e) (by
      intro e' _; split; exact hx.1 e'; rfl) (Finset.mem_univ e)
  have he : G.Incident (G.left e) e := Or.inl rfl
  change (if G.Incident (G.left e) e then x e else 0) ≤ G.degree x (G.left e) at h
  simpa only [he, ite_true, hx.2.1] using h

omit [Fintype V] [DecidableEq E] in
theorem continuous_degree (G : LooplessGraph V E) (v : V) :
    Continuous (fun x : E → ℝ => G.degree x v) := by
  unfold degree
  apply continuous_finsetSum
  intro e _
  split <;> fun_prop

omit [Fintype V] [DecidableEq E] in
theorem continuous_cutMass (G : LooplessGraph V E) (S : Finset V) :
    Continuous (fun x : E → ℝ => G.cutMass x S) := by
  unfold cutMass
  fun_prop

omit [Fintype V] [DecidableEq E] in
theorem isClosed_constraintPolytope (G : LooplessGraph V E) :
    IsClosed G.constraintPolytope := by
  simp only [constraintPolytope, Set.ofPred_and, Set.ofPred_forall]
  exact (isClosed_iInter fun e => isClosed_le continuous_const (continuous_apply e)).inter
    ((isClosed_iInter fun v => isClosed_eq (G.continuous_degree v) continuous_const).inter
      (isClosed_iInter fun S => isClosed_iInter fun _ =>
        isClosed_le continuous_const (G.continuous_cutMass S)))

omit [Fintype V] [DecidableEq E] in
theorem isCompact_constraintPolytope (G : LooplessGraph V E) :
    IsCompact G.constraintPolytope := by
  apply (isCompact_Icc : IsCompact (Set.Icc (0 : E → ℝ) 1)).of_isClosed_subset
    G.isClosed_constraintPolytope
  intro x hx
  exact ⟨hx.1, fun e => G.constraint_coordinate_le_one hx e⟩

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

theorem exists_supported_matching (G : LooplessGraph V E) {x : E → ℝ}
    (hx : x ∈ G.constraintPolytope) :
    ∃ M : G.Matching, ∀ e ∈ M.val, 0 < x e := by
  classical
  obtain ⟨M,hM⟩ := G.supportSimple_has_perfectMatching hx
  have he : ∀ q ∈ M.edgeSet, ∃ e, 0<x e ∧ s(G.left e,G.right e)=q := by
    intro q
    induction q using Sym2.inductionOn with
    | hf v w =>
      intro hq
      obtain ⟨e,he,hor⟩ := (SimpleGraph.Subgraph.mem_edgeSet.mp hq).adj_sub
      refine ⟨e,he,Sym2.eq_iff.mpr hor⟩
  let f : M.edgeSet → E := fun q => (he q.val q.property).choose
  have hf : ∀ q, 0<x (f q) ∧ s(G.left (f q),G.right (f q))=q.val :=
    fun q => (he q.val q.property).choose_spec
  let F : Finset E := Finset.univ.image f
  have hF : G.IsPerfectMatching F := by
    intro v
    obtain ⟨w,hw,hu⟩ := SimpleGraph.Subgraph.isPerfectMatching_iff.mp hM v
    let q : M.edgeSet := ⟨s(v,w),SimpleGraph.Subgraph.mem_edgeSet.mpr hw⟩
    refine ⟨f q,⟨Finset.mem_image.mpr ⟨q,Finset.mem_univ _,rfl⟩,?_⟩,?_⟩
    · rcases Sym2.eq_iff.mp (hf q).2 with h | h
      · exact Or.inl h.1
      · exact Or.inr h.2
    · intro e he'
      obtain ⟨q',_,rfl⟩ := Finset.mem_image.mp he'.1
      have hq : q'=q := by
        apply Subtype.ext
        rcases he'.2 with hl | hr
        · have hval : q'.val=s(v,G.right (f q')) := by rw [← (hf q').2, hl]
          have hAdj : M.Adj v (G.right (f q')) :=
            SimpleGraph.Subgraph.mem_edgeSet.mp (hval ▸ q'.property)
          rw [hval, hu _ hAdj]
        · have hval : q'.val=s(v,G.left (f q')) := by
            rw [← (hf q').2, hr, Sym2.eq_swap]
          have hAdj : M.Adj v (G.left (f q')) :=
            SimpleGraph.Subgraph.mem_edgeSet.mp (hval ▸ q'.property)
          rw [hval, hu _ hAdj]
      exact congrArg f hq
  refine ⟨⟨F,hF⟩,?_⟩
  intro e he'
  obtain ⟨q,_,rfl⟩ := Finset.mem_image.mp he'
  exact (hf q).1

omit [Fintype V] [DecidableEq E] in
 theorem degree_sub (G : LooplessGraph V E) (x y : E → ℝ) (v : V) :
    G.degree (x-y) v = G.degree x v-G.degree y v := by
  have h := G.degree_linear x y 1 (-1) v
  simpa [sub_eq_add_neg] using h

 theorem extreme_no_tight_integral (G : LooplessGraph V E) {x : E → ℝ}
    (heven : Even (Fintype.card V)) (hx : x ∈ Set.extremePoints ℝ G.constraintPolytope)
    (hnt : ¬∃ S : Finset V, Odd S.card ∧ 3≤S.card ∧ 3≤Sᶜ.card ∧ G.cutMass x S=1) :
    ∃ M : G.Matching, G.indicator M=x := by
  have hxQ := (mem_extremePoints.mp hx).1
  obtain ⟨M,hM⟩ := G.exists_supported_matching hxQ
  have hd : ∀ v, G.degree (G.indicator M-x) v=0 := by
    intro v
    rw [degree_sub,degree_indicator,hxQ.2.1,sub_self]
  have hz : ∀ e, x e=0 → (G.indicator M-x) e=0 := by
    intro e he
    have hn : e ∉ M.val := fun h => (hM e h).ne' he
    simp [indicator,hn,he]
  have hu := G.constraint_eventually_line hxQ (G.indicator M-x) hz hd
    (G.trivial_tight_cut_preserved heven hnt _ hd)
  have he := extreme_point_direction_zero G.constraintPolytope hx _ hu
  exact ⟨M,sub_eq_zero.mp he⟩

/-- Induction over even orders, using only proved cut coupling and Mathlib Tutte. -/
theorem constraint_subset_polytope_aux (n : ℕ) :
    ∀ {W F : Type*} [Fintype W] [Fintype F] [DecidableEq W] [DecidableEq F]
      (G : LooplessGraph W F), Fintype.card W=n → Even n →
      G.constraintPolytope ⊆ G.polytope := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro W F _ _ _ _ G hcard heven
    have heven' : Even (Fintype.card W) := hcard ▸ heven
    have hex : Set.extremePoints ℝ G.constraintPolytope ⊆ G.polytope := by
      intro x hx
      have hxQ := (mem_extremePoints.mp hx).1
      by_cases hcut : ∃ S : Finset W, Odd S.card ∧ 3≤S.card ∧ 3≤Sᶜ.card ∧ G.cutMass x S=1
      · obtain ⟨S,hS,hlo,hhi,ht⟩ := hcut
        have hc := odd_compl_of_even heven' hS
        have hlt1 : Fintype.card (Option {v // v ∈ S}) < n := by
          simp only [Fintype.card_option,Fintype.card_coe]
          have hco := Finset.card_compl S
          omega
        have hlt2 : Fintype.card (Option {v // v ∈ Sᶜ}) < n := by
          simp only [Fintype.card_option,Fintype.card_coe]
          have hco := Finset.card_compl S
          have hle := Finset.card_le_univ S
          omega
        have hv1 : Even (Fintype.card (Option {v // v ∈ S})) := by
          simpa only [Fintype.card_option,Fintype.card_coe] using hS.add_odd odd_one
        have hv2 : Even (Fintype.card (Option {v // v ∈ Sᶜ})) := by
          simpa only [Fintype.card_option,Fintype.card_coe] using hc.add_odd odd_one
        have hx1 := ih _ hlt1 (G.onSide S) rfl hv1 (G.restriction_mem_constraints hxQ S hS ht)
        have htc : G.cutMass x Sᶜ=1 := by simpa only [cutMass,cut_compl] using ht
        have hx2 := ih _ hlt2 (G.onSide Sᶜ) rfl hv2 (G.restriction_mem_constraints hxQ Sᶜ hc htc)
        obtain ⟨p,hp,hpx⟩ := ((G.onSide S).mem_polytope_iff _).mp hx1
        obtain ⟨q,hq,hqx⟩ := ((G.onSide Sᶜ).mem_polytope_iff _).mp hx2
        exact (G.mem_polytope_iff x).mpr (G.couple_laws S x hp hq (congrFun hpx) (congrFun hqx))
      · obtain ⟨M,rfl⟩ := G.extreme_no_tight_integral heven' hx hcut
        exact subset_convexHull ℝ _ (Set.mem_range_self M)
    rw [← closure_convexHull_extremePoints G.isCompact_constraintPolytope G.convex_constraintPolytope]
    exact closure_minimal (convexHull_min hex (convex_convexHull ℝ _)) G.compact_polytope.isClosed

end LooplessGraph

end MatchingEntropy

end

end OAI

-- ---- platform node ----
open OAI OAI.MatchingEntropy OAI.MatchingEntropy.LooplessGraph
open scoped BigOperators Topology
open Filter
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

theorem solution (n : ℕ) :
    ∀ {W F : Type*} [Fintype W] [Fintype F] [DecidableEq W] [DecidableEq F]
      (G : LooplessGraph W F), Fintype.card W=n → Even n →
      G.constraintPolytope ⊆ G.polytope := by
  first
    | exact OAI.MatchingEntropy.LooplessGraph.constraint_subset_polytope_aux n
    | exact OAI.MatchingEntropy.LooplessGraph.constraint_subset_polytope_aux
    | (apply OAI.MatchingEntropy.LooplessGraph.constraint_subset_polytope_aux <;> assumption)
    | (intros; apply OAI.MatchingEntropy.LooplessGraph.constraint_subset_polytope_aux <;> assumption)
