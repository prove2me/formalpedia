-- Prove2me | solution 1 for OAI.MatchingEntropy.matching_covariance_rank
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T02:28:19.180198+00:00
-- url     : https://prove2.me/submissions/6d482bdd-ede1-44eb-a2c4-5dfe2e461faa

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/PerfectMatching/MatchingCovariance.lean:L106-L132
-- (upload_full_project.md Phase 4): solution for node OAI.MatchingEntropy.matching_covariance_rank. The node keeps its source
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
import Theorems.Thm_OAI_MatchingEntropy_LooplessGraph_degree_indicator
import Theorems.Thm_OAI_MatchingEntropy_LooplessGraph_faceCodimension_strong_aux
import Theorems.Thm_OAI_MatchingEntropy_LooplessGraph_mem_polytope_iff
import Theorems.Thm_OAI_MatchingEntropy_LooplessGraph_trivial_tight_cut_preserved
import Theorems.Thm_OAI_MatchingEntropy_normalized_face_mem

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

-- ---- from OAI.Combinatorics.PerfectMatching.Polyhedron ----
namespace OAI

/-!
Finite polyhedra, local perturbations, and quotient dimension bounds.
-/

noncomputable section

open scoped BigOperators Topology
open Filter

namespace MatchingEntropy

section PolyhedralPrelude
variable {I J : Type*} [Fintype I] [Fintype J]

section LinearHelper
open Module
variable {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
  [Module ℝ A] [Module ℝ B] [Module ℝ C]
  [FiniteDimensional ℝ A] [FiniteDimensional ℝ B] [FiniteDimensional ℝ C]

theorem quotient_finrank_le_of_ker_le (U : Submodule ℝ A) (f : A →ₗ[ℝ] B)
    (h : f.ker ≤ U) : finrank ℝ (A ⧸ U) ≤ finrank ℝ B := by
  have h1 := U.finrank_quotient_add_finrank
  have h2 := f.finrank_range_add_finrank_ker
  have h3 := Submodule.finrank_mono h
  have h4 : finrank ℝ f.range ≤ finrank ℝ B := Submodule.finrank_le _
  omega

end LinearHelper
end PolyhedralPrelude

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
 theorem faceCodimension_no_tight (G : LooplessGraph V E) {x : E → ℝ}
    (heven : Even (Fintype.card V))
    (hnt : ¬∃ S : Finset V, Odd S.card ∧ 3≤S.card ∧ 3≤Sᶜ.card ∧ G.cutMass x S=1) :
    G.faceCodimension x ≤ Fintype.card V := by
  classical
  let F := G.degreeLinear.comp (positiveExtension x)
  have hk : F.ker ≤ G.faceSpace x := by
    intro u hu
    have hd : G.degreeLinear (positiveExtension x u)=0 := hu
    refine ⟨hd,?_⟩
    exact G.trivial_tight_cut_preserved heven hnt _ (congrFun hd)
  simpa [faceCodimension] using quotient_finrank_le_of_ker_le (G.faceSpace x) F hk

/-- The precise coarse face-codimension estimate used by the entropy argument. -/
theorem faceCodimension_bound (G : LooplessGraph V E) {x : E → ℝ}
    (heven : Even (Fintype.card V)) (hx : x ∈ G.polytope) :
    G.faceCodimension x ≤ 2*Fintype.card V := by
  by_cases hn : 4≤Fintype.card V
  · have hb := faceCodimension_strong_aux (Fintype.card V) G rfl heven hn x
      (G.polytope_subset_constraintPolytope hx)
    omega
  · have hnt : ¬ ∃ S : Finset V, Odd S.card ∧ 3≤S.card ∧ 3≤Sᶜ.card ∧ G.cutMass x S=1 := by
      rintro ⟨S,_,hlo,hhi,_⟩
      have hh := Finset.card_compl_add_card S
      omega
    have hb := G.faceCodimension_no_tight heven hnt
    omega

end LooplessGraph

end MatchingEntropy

end

end OAI

-- ---- from OAI.Combinatorics.PerfectMatching.Covariance ----
namespace OAI

/-!
Positive semidefinite covariance matrices, rank, trace, and a spectral inequality.
-/

noncomputable section

open scoped BigOperators Topology
open Filter

namespace MatchingEntropy

open Matrix

variable {A I : Type*} [Fintype A] [Fintype I] [DecidableEq A] [DecidableEq I]

omit [Fintype A] [Fintype I] [DecidableEq A] [DecidableEq I] in
theorem weightedColumns_span {p : A → ℝ} (hp : ∀ a, 0 ≤ p a) (b : A → I → ℝ) :
    Submodule.span ℝ (Set.range (weightedColumns p b).col) = weightedDirectionSpace p b := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨a,rfl⟩
    by_cases ha : 0 < p a
    · have hb : b a ∈ weightedDirectionSpace p b := Submodule.subset_span ⟨⟨a,ha⟩,rfl⟩
      exact Submodule.smul_mem _ (Real.sqrt (p a)) hb
    · have hz := le_antisymm (le_of_not_gt ha) (hp a)
      have he : (weightedColumns p b).col a = 0 := by
        ext i
        simp [weightedColumns, Matrix.col, hz]
      rw [he]
      exact (weightedDirectionSpace p b).zero_mem
  · apply Submodule.span_le.mpr
    rintro _ ⟨a,rfl⟩
    have hb : (weightedColumns p b).col a.val ∈
        Submodule.span ℝ (Set.range (weightedColumns p b).col) := Submodule.subset_span ⟨a.val,rfl⟩
    have hs : Real.sqrt (p a.val) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 a.property)
    have hh := Submodule.smul_mem _ (Real.sqrt (p a.val))⁻¹ hb
    have he : (Real.sqrt (p a.val))⁻¹ • (weightedColumns p b).col a.val = b a.val := by
      ext i
      change (Real.sqrt (p a.val))⁻¹ * (Real.sqrt (p a.val) * b a.val i) = _
      rw [← mul_assoc, inv_mul_cancel₀ hs, one_mul]
    rw [he] at hh
    exact hh

omit [DecidableEq A] [DecidableEq I] in
theorem covariance_rank {p : A → ℝ} (hp : ∀ a, 0 ≤ p a) (b : A → I → ℝ) :
    (covariance p b).rank = Module.finrank ℝ (weightedDirectionSpace p b) := by
  rw [covariance, rank_self_mul_transpose, rank_eq_finrank_span_cols, weightedColumns_span hp]

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

/-- Face codimension gives a lower bound for the rank of the genuine covariance. -/
theorem matching_covariance_rank (G : LooplessGraph V E) {x : E → ℝ}
    (heven : Even (Fintype.card V)) {p : G.Matching → ℝ}
    (hp : p ∈ G.feasibleLaws x) (hopt : entropy p=maxMatchingEntropy G x) :
    Fintype.card {e // 0 < x e} ≤ 2*Fintype.card V+
      (covariance p (matchingNormalized G x)).rank := by
  let W := weightedDirectionSpace p (matchingNormalized G x)
  let L : G.faceSpace x →ₗ[ℝ] W :=
    ((normalizeLinear x).comp (G.faceSpace x).subtype).codRestrict W
      (fun u => normalized_face_mem G heven hp hopt u.property)
  have hi : Function.Injective L := by
    intro u v huv
    apply Subtype.ext
    funext e
    have hh := congrFun (congrArg Subtype.val huv) e
    change u.val e/Real.sqrt (x e.val)=v.val e/Real.sqrt (x e.val) at hh
    exact (div_left_inj' (ne_of_gt (Real.sqrt_pos.mpr e.property))).mp hh
  have hdim := LinearMap.finrank_le_finrank_of_injective hi
  have hq := (G.faceSpace x).finrank_quotient_add_finrank
  have hc := G.faceCodimension_bound heven ((G.mem_polytope_iff x).mpr ⟨p,hp⟩)
  rw [covariance_rank hp.1.1]
  have hq' : G.faceCodimension x+Module.finrank ℝ (G.faceSpace x)=Fintype.card {e // 0 < x e} := by
    simpa only [LooplessGraph.faceCodimension,Module.finrank_pi,Module.finrank_self,Finset.sum_const,
      Finset.card_univ,smul_eq_mul,mul_one] using hq
  change Module.finrank ℝ (G.faceSpace x) ≤ Module.finrank ℝ W at hdim
  dsimp only [W] at hdim
  omega

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
    (hp : p ∈ G.feasibleLaws x) (hopt : entropy p=maxMatchingEntropy G x) :
    Fintype.card {e // 0 < x e} ≤ 2*Fintype.card V+
      (covariance p (matchingNormalized G x)).rank := by
  first
    | exact OAI.MatchingEntropy.matching_covariance_rank G heven hp hopt
    | exact OAI.MatchingEntropy.matching_covariance_rank
    | (apply OAI.MatchingEntropy.matching_covariance_rank <;> assumption)
    | (intros; apply OAI.MatchingEntropy.matching_covariance_rank <;> assumption)
