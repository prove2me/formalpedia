-- Prove2me | solution 1 for OAI.MatchingEntropy.matching_covariance_trace
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T02:29:48.91986+00:00
-- url     : https://prove2.me/submissions/6817697c-8de1-485e-95da-4a11994aa471

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/PerfectMatching/MatchingCovariance.lean:L186-L201
-- (upload_full_project.md Phase 4): solution for node OAI.MatchingEntropy.matching_covariance_trace. The node keeps its source
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
import Theorems.Thm_OAI_MatchingEntropy_LooplessGraph_mem_polytope_iff

-- ---- from OAI.Combinatorics.PerfectMatching.Entropy ----
namespace OAI

/-!
Finite Shannon entropy and attainment of its supremum over feasible matching laws.
-/

noncomputable section

open scoped BigOperators Topology
open Filter

namespace MatchingEntropy

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

namespace LooplessGraph

omit [Fintype V] [DecidableEq V] in
theorem coordinate_mem_Icc (G : LooplessGraph V E) {y : E → ℝ}
    (hy : y ∈ G.polytope) (e : E) : y e ∈ Set.Icc (0 : ℝ) 1 := by
  obtain ⟨p, hp, rfl⟩ := (G.mem_polytope_iff y).mp hy
  constructor
  · exact Finset.sum_nonneg (fun M _ ↦ mul_nonneg (hp.1 M) (G.indicator_nonneg M e))
  · calc
      ∑ M, p M * G.indicator M e ≤ ∑ M, p M * 1 :=
        Finset.sum_le_sum (fun M _ ↦ mul_le_mul_of_nonneg_left (G.indicator_le_one M e) (hp.1 M))
      _ = 1 := by simpa using hp.2

omit [Fintype E] [DecidableEq E] in
/-- Counting the two distinct endpoints; parallel identities are never collapsed. -/
theorem incident_vertex_sum (G : LooplessGraph V E) (e : E) :
    (∑ v, if G.Incident v e then (1 : ℕ) else 0) = 2 := by
  classical
  have he (v : V) : (if G.Incident v e then (1 : ℕ) else 0) =
      (if G.left e = v then 1 else 0) + (if G.right e = v then 1 else 0) := by
    by_cases hl : G.left e = v <;> by_cases hr : G.right e = v
    · exact False.elim (G.loopless e (hl.trans hr.symm))
    · simp [Incident, hl, hr]
    · simp [Incident, hl, hr]
    · simp [Incident, hl, hr]
  simp_rw [he, Finset.sum_add_distrib]
  simp

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem matching_incident_sum (G : LooplessGraph V E) (M : G.Matching) (v : V) :
    (∑ e ∈ M.val, if G.Incident v e then (1 : ℕ) else 0) = 1 := by
  classical
  obtain ⟨e, ⟨he, hv⟩, hu⟩ := M.property v
  rw [Finset.sum_eq_single e]
  · simp [hv]
  · intro e' he' hne
    have hn : ¬ G.Incident v e' := fun hv' ↦ hne (hu e' ⟨he', hv'⟩)
    simp [hn]
  · simp [he]

omit [Fintype E] [DecidableEq E] in
theorem matching_card_twice (G : LooplessGraph V E) (M : G.Matching) :
    2 * M.val.card = Fintype.card V := by
  classical
  calc
    2 * M.val.card = ∑ e ∈ M.val, ∑ v, if G.Incident v e then (1 : ℕ) else 0 := by
      simp_rw [G.incident_vertex_sum]
      simp [Nat.mul_comm]
    _ = ∑ v, ∑ e ∈ M.val, if G.Incident v e then (1 : ℕ) else 0 := Finset.sum_comm
    _ = Fintype.card V := by
      simp_rw [G.matching_incident_sum]
      simp

omit [Fintype E] [DecidableEq E] in
theorem matching_card (G : LooplessGraph V E) {m : ℕ}
    (hV : Fintype.card V = 2 * m) (M : G.Matching) : M.val.card = m := by
  have h := G.matching_card_twice M
  omega

theorem indicator_sum (G : LooplessGraph V E) {m : ℕ}
    (hV : Fintype.card V = 2 * m) (M : G.Matching) :
    ∑ e, G.indicator M e = (m : ℝ) := by
  simp [indicator, G.matching_card hV M]

/-- All feasible marginal vectors have mass m, as in the entropy proof. -/
theorem marginal_sum (G : LooplessGraph V E) {m : ℕ}
    (hV : Fintype.card V = 2 * m) {y : E → ℝ} (hy : y ∈ G.polytope) :
    ∑ e, y e = (m : ℝ) := by
  obtain ⟨p, hp, rfl⟩ := (G.mem_polytope_iff y).mp hy
  simp_rw [mean]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, G.indicator_sum hV]
  rw [← Finset.sum_mul, hp.2, one_mul]

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

omit [Fintype I] [DecidableEq A] [DecidableEq I] in
theorem covariance_entry {p : A → ℝ} (hp : ∀ a, 0 ≤ p a) (b : A → I → ℝ) (i j : I) :
    covariance p b i j = ∑ a, p a*b a i*b a j := by
  unfold covariance
  rw [Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro a _
  simp only [weightedColumns, Matrix.transpose_apply]
  calc
    _ = (Real.sqrt (p a))^2 * b a i * b a j := by ring
    _ = _ := by rw [Real.sq_sqrt (hp a)]

omit [Fintype I] [DecidableEq A] [DecidableEq I] in
theorem normalizedCentered_variance {p : A → ℝ} (hp : ∑ a, p a = 1)
    (v : A → I → ℝ) (hv : ∀ a i, (v a i)^2=v a i) (x : I → ℝ)
    (hx : ∀ i, ∑ a, p a*v a i = x i) (hxp : ∀ i, 0 < x i) (i : I) :
    ∑ a, p a*(normalizedCentered v x a i)^2 = 1-x i := by
  have heq : ∀ a, p a*(normalizedCentered v x a i)^2 =
      (p a*v a i-2*x i*(p a*v a i)+(x i)^2*p a)/x i := by
    intro a
    rw [normalizedCentered, div_pow, Real.sq_sqrt (hxp i).le, ← mul_div_assoc]
    congr 1
    calc
      _ = p a*(v a i)^2-2*x i*(p a*v a i)+(x i)^2*p a := by ring
      _ = _ := by rw [hv]
  simp_rw [heq]
  rw [← Finset.sum_div]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    hx, hp, mul_one]
  field_simp [ne_of_gt (hxp i)]
  ring

omit [DecidableEq A] [DecidableEq I] in
theorem normalized_covariance_trace {p : A → ℝ} (hp : p ∈ probabilitySimplex A)
    (v : A → I → ℝ) (hv : ∀ a i, (v a i)^2=v a i) (x : I → ℝ)
    (hx : ∀ i, ∑ a, p a*v a i = x i) (hxp : ∀ i, 0 < x i) :
    (covariance p (normalizedCentered v x)).trace = Fintype.card I - ∑ i, x i := by
  unfold Matrix.trace Matrix.diag
  simp_rw [covariance_entry hp.1]
  have heq : ∀ i, (∑ a, p a*normalizedCentered v x a i*normalizedCentered v x a i) = 1-x i := by
    intro i
    simpa only [pow_two, mul_assoc] using
      normalizedCentered_variance hp.2 v hv x hx hxp i
  simp_rw [heq]
  simp

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

omit [DecidableEq E] in
theorem sum_positive_support (x f : E → ℝ) (hf : ∀ e, ¬ 0 < x e → f e=0) :
    (∑ e, f e) = ∑ e : {e // 0 < x e}, f e.val := by
  classical
  have hz : (∑ e : {e // ¬ 0 < x e}, f e.val)=0 :=
    Finset.sum_eq_zero fun e _ => hf e.val e.property
  have hh := Fintype.sum_subtype_add_sum_subtype (fun e => 0 < x e) f
  rw [hz,add_zero] at hh
  exact hh.symm

/-- The normalized covariance has the exact trace s-m. -/
theorem matching_covariance_trace (G : LooplessGraph V E) {x : E → ℝ}
    {p : G.Matching → ℝ} (hp : p ∈ G.feasibleLaws x) {m : ℕ}
    (hV : Fintype.card V=2*m) :
    (covariance p (matchingNormalized G x)).trace = Fintype.card {e // 0 < x e}-(m:ℝ) := by
  have hx : x ∈ G.polytope := (G.mem_polytope_iff x).mpr ⟨p,hp⟩
  have hsum : (∑ e : {e // 0 < x e}, x e.val)=(m:ℝ) := by
    rw [← G.marginal_sum hV hx]
    exact (sum_positive_support x x (fun e he => le_antisymm (le_of_not_gt he) (G.coordinate_mem_Icc hx e).1)).symm
  unfold matchingNormalized
  rw [normalized_covariance_trace hp.1 _ ?_ _ ?_ (fun e => e.property),hsum]
  · intro M e
    simp only [LooplessGraph.indicator]
    split <;> norm_num
  · intro e
    exact congrFun hp.2 e.val

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
    {p : G.Matching → ℝ} (hp : p ∈ G.feasibleLaws x) {m : ℕ}
    (hV : Fintype.card V=2*m) :
    (covariance p (matchingNormalized G x)).trace = Fintype.card {e // 0 < x e}-(m:ℝ) := by
  first
    | exact OAI.MatchingEntropy.matching_covariance_trace G hp hV
    | exact OAI.MatchingEntropy.matching_covariance_trace
    | (apply OAI.MatchingEntropy.matching_covariance_trace <;> assumption)
    | (intros; apply OAI.MatchingEntropy.matching_covariance_trace <;> assumption)
