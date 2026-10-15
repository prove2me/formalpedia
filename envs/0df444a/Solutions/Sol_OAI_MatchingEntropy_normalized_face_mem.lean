-- Prove2me | solution 1 for OAI.MatchingEntropy.normalized_face_mem
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T02:26:03.051947+00:00
-- url     : https://prove2.me/submissions/1e1f05f0-52a8-4d9f-b828-352e64a13640

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/PerfectMatching/MatchingCovariance.lean:L59-L98
-- (upload_full_project.md Phase 4): solution for node OAI.MatchingEntropy.normalized_face_mem. The node keeps its source
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
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Covariance
import Definitions.Def_OAI_Combinatorics_PerfectMatching_MatchingCovariance
import Theorems.Thm_OAI_MatchingEntropy_LooplessGraph_constraint_eventually_line
import Theorems.Thm_OAI_MatchingEntropy_LooplessGraph_constraint_subset_polytope_aux
import Theorems.Thm_OAI_MatchingEntropy_LooplessGraph_degree_indicator
import Theorems.Thm_OAI_MatchingEntropy_LooplessGraph_mem_polytope_iff
import Theorems.Thm_OAI_MatchingEntropy_midpoint_law_support

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

end LooplessGraph

end MatchingEntropy

end

end OAI

-- ---- from OAI.Combinatorics.PerfectMatching.MatchingCovariance ----
namespace OAI

/-!
Normalized matching covariance: face rank, exact trace, and second variation.
-/

noncomputable section

open scoped BigOperators Topology
open Filter

namespace MatchingEntropy

open Matrix

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

omit [Fintype V] [DecidableEq V] in
theorem matchingNormalized_average (G : LooplessGraph V E) {x y : E → ℝ}
    {q : G.Matching → ℝ} (hq : q ∈ G.feasibleLaws y) (e : {e // 0 < x e}) :
    (∑ M, q M*matchingNormalized G x M e)=(y e.val-x e.val)/Real.sqrt (x e.val) := by
  simp only [matchingNormalized,normalizedCentered,← mul_div_assoc,mul_sub,
    ← Finset.sum_div,Finset.sum_sub_distrib,← Finset.sum_mul,hq.1.2,one_mul]
  rw [show (∑ M, q M*G.indicator M e.val)=y e.val from congrFun hq.2 e.val]

/-- Every active-face direction belongs to the optimizer's normalized covariance
span. No face support or dimension assertion is being supplied as a hypothesis. -/
theorem normalized_face_mem (G : LooplessGraph V E) {x : E → ℝ}
    (heven : Even (Fintype.card V)) {p : G.Matching → ℝ}
    (hp : p ∈ G.feasibleLaws x) (hopt : entropy p=maxMatchingEntropy G x)
    {u : {e // 0 < x e} → ℝ} (hu : u ∈ G.faceSpace x) :
    (fun e => u e/Real.sqrt (x e.val)) ∈ weightedDirectionSpace p (matchingNormalized G x) := by
  have hx : x ∈ G.polytope := (G.mem_polytope_iff x).mpr ⟨p,hp⟩
  have hev := G.faceSpace_eventually_line (G.polytope_subset_constraintPolytope hx) hu
  have hneg : ∀ᶠ t : ℝ in 𝓝 0, x+(-t) • LooplessGraph.positiveExtension x u ∈ G.constraintPolytope := by
    have hc : Tendsto (fun t : ℝ => -t) (𝓝 0) (𝓝 0) := by simpa using continuous_neg.tendsto (0:ℝ)
    exact hc.eventually hev
  have hh : ∀ᶠ t : ℝ in 𝓝[>] 0,
      (x+t • LooplessGraph.positiveExtension x u ∈ G.constraintPolytope ∧
      x+(-t) • LooplessGraph.positiveExtension x u ∈ G.constraintPolytope) ∧ 0 < t :=
    ((hev.and hneg).filter_mono nhdsWithin_le_nhds).and eventually_mem_nhdsWithin
  obtain ⟨a,⟨ha,hna⟩,ha0⟩ := hh.exists
  rw [← G.polytope_eq_constraints heven] at ha hna
  obtain ⟨q,hq⟩ := (G.mem_polytope_iff _).mp ha
  obtain ⟨r,hr⟩ := (G.mem_polytope_iff _).mp hna
  have hsupp := midpoint_law_support G hp hopt hq hr
  have hsum : (∑ M, q M • matchingNormalized G x M) ∈
      weightedDirectionSpace p (matchingNormalized G x) := by
    apply Submodule.sum_mem
    intro M _
    by_cases hM : 0 < p M
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨M,hM⟩,rfl⟩)
    · have hq0 : q M=0 := le_antisymm (le_of_not_gt fun hqM => hM (hsupp M hqM)) (hq.1.1 M)
      simp only [hq0,zero_smul]
      exact Submodule.zero_mem _
  have hin := Submodule.smul_mem _ a⁻¹ hsum
  have he : a⁻¹ • (∑ M, q M • matchingNormalized G x M) =
      (fun e => u e/Real.sqrt (x e.val)) := by
    ext e
    simp only [Pi.smul_apply,Finset.sum_apply,smul_eq_mul]
    rw [matchingNormalized_average G hq]
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,LooplessGraph.positiveExtension_pos]
    field_simp
    ring
  rwa [he] at hin

end MatchingEntropy

end

end OAI

-- ---- platform node ----
open OAI OAI.MatchingEntropy
open scoped BigOperators Topology
open Filter
open Matrix
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

theorem solution (G : LooplessGraph V E) {x : E → ℝ}
    (heven : Even (Fintype.card V)) {p : G.Matching → ℝ}
    (hp : p ∈ G.feasibleLaws x) (hopt : entropy p=maxMatchingEntropy G x)
    {u : {e // 0 < x e} → ℝ} (hu : u ∈ G.faceSpace x) :
    (fun e => u e/Real.sqrt (x e.val)) ∈ weightedDirectionSpace p (matchingNormalized G x) := by
  first
    | exact OAI.MatchingEntropy.normalized_face_mem G heven hp hopt hu
    | exact OAI.MatchingEntropy.normalized_face_mem
    | (apply OAI.MatchingEntropy.normalized_face_mem <;> assumption)
    | (intros; apply OAI.MatchingEntropy.normalized_face_mem <;> assumption)
