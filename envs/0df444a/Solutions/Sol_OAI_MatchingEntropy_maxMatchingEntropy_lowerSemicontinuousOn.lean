-- Prove2me | solution 1 for OAI.MatchingEntropy.maxMatchingEntropy_lowerSemicontinuousOn
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T02:17:53.831988+00:00
-- url     : https://prove2.me/submissions/43d73065-5d40-4484-8b0d-0b4b485b77ab

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/PerfectMatching/Continuity.lean:L37-L60
-- (upload_full_project.md Phase 4): solution for node OAI.MatchingEntropy.maxMatchingEntropy_lowerSemicontinuousOn. The node keeps its source
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
import Theorems.Thm_OAI_MatchingEntropy_LooplessGraph_constraint_eventually_expand
import Theorems.Thm_OAI_MatchingEntropy_LooplessGraph_constraint_subset_polytope_aux
import Theorems.Thm_OAI_MatchingEntropy_LooplessGraph_degree_indicator
import Theorems.Thm_OAI_MatchingEntropy_LooplessGraph_mem_polytope_iff

-- ---- from OAI.Combinatorics.PerfectMatching.Simplex ----
namespace OAI

/-!
Probability vectors on finite types, with their convexity and compactness properties.
The function-space simplex is the range of the weights of `Convexity.StdSimplex`.
-/

noncomputable section

open scoped BigOperators

namespace MatchingEntropy

theorem convex_probabilitySimplex (Index : Type*) [Fintype Index] :
    Convex ℝ (probabilitySimplex Index) := by
  intro leftWeights leftMem rightWeights rightMem leftScale rightScale
    leftNonneg rightNonneg total
  constructor
  · intro index
    exact add_nonneg (mul_nonneg leftNonneg (leftMem.1 index))
      (mul_nonneg rightNonneg (rightMem.1 index))
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum, leftMem.2, rightMem.2, mul_one, total]

theorem probabilitySimplex_le_one {Index : Type*} [Fintype Index] {weights : Index → ℝ}
    (mem : weights ∈ probabilitySimplex Index) (index : Index) : weights index ≤ 1 := by
  rw [← mem.2]
  exact Finset.single_le_sum (fun other _ ↦ mem.1 other) (Finset.mem_univ index)

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
theorem compact_feasibleLaws (G : LooplessGraph V E) (y : E → ℝ) :
    IsCompact (G.feasibleLaws y) := by
  exact (isCompact_probabilitySimplex G.Matching).inter_right
    (isClosed_eq G.continuous_mean continuous_const)

end LooplessGraph

end MatchingEntropy

end

end OAI

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

theorem continuous_entropy {ι : Type*} [Fintype ι] :
    Continuous (entropy : (ι → ℝ) → ℝ) := by
  unfold entropy
  fun_prop

theorem entropy_nonneg {ι : Type*} [Fintype ι] {p : ι → ℝ}
    (hp : p ∈ probabilitySimplex ι) : 0 ≤ entropy p := by
  apply Finset.sum_nonneg
  intro i _
  exact Real.negMulLog_nonneg (hp.1 i)
    (probabilitySimplex_le_one hp i)

namespace LooplessGraph

end LooplessGraph

omit [Fintype V] [DecidableEq V] in
/-- The supremum in the definition of H is a genuine attained maximum. -/
theorem maxMatchingEntropy_attained (G : LooplessGraph V E) {y : E → ℝ}
    (hy : y ∈ G.polytope) :
    ∃ p ∈ G.feasibleLaws y, entropy p = maxMatchingEntropy G y := by
  have hc := (G.compact_feasibleLaws y).image continuous_entropy
  have hn := ((G.mem_polytope_iff y).mp hy).image entropy
  obtain ⟨p, hp, hpe⟩ := hc.sSup_mem hn
  exact ⟨p, hp, hpe⟩

omit [Fintype V] [DecidableEq V] in
theorem maxMatchingEntropy_nonneg (G : LooplessGraph V E) {y : E → ℝ}
    (hy : y ∈ G.polytope) : 0 ≤ maxMatchingEntropy G y := by
  obtain ⟨p, hp, he⟩ := maxMatchingEntropy_attained G hy
  rw [← he]
  exact entropy_nonneg hp.1

omit [Fintype V] [DecidableEq V] in
theorem entropy_le_maxMatchingEntropy (G : LooplessGraph V E) {y : E → ℝ}
    {p : G.Matching → ℝ} (hp : p ∈ G.feasibleLaws y) :
    entropy p ≤ maxMatchingEntropy G y := by
  apply le_csSup
  · exact ((G.compact_feasibleLaws y).image continuous_entropy).bddAbove
  · exact ⟨p, hp, rfl⟩

end MatchingEntropy

end

end OAI

-- ---- from OAI.Combinatorics.PerfectMatching.Optimizer ----
namespace OAI

/-!
Support and first-order identities for entropy-maximizing matching laws.
-/

noncomputable section

open scoped BigOperators Topology
open Filter

namespace MatchingEntropy

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

/-- Concavity of actual finite-law Shannon entropy. -/
theorem entropy_mix_ge {ι : Type*} [Fintype ι] {p q : ι → ℝ}
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (1-t) * entropy p + t * entropy q ≤
      entropy (fun i => (1-t)*p i + t*q i) := by
  unfold entropy
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  simpa only [smul_eq_mul] using Real.concaveOn_negMulLog.2
    (hp i) (hq i) (sub_nonneg.mpr ht.2) ht.1 (by ring : 1-t+t=1)

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

 theorem polytope_eventually_expand (G : LooplessGraph V E) {x : E → ℝ}
    (heven : Even (Fintype.card V)) (hx : x ∈ G.polytope) {t : ℝ} (ht : 0<t) :
    ∀ᶠ y in 𝓝[G.polytope] x, x+t⁻¹ • (y-x) ∈ G.polytope := by
  rw [G.polytope_eq_constraints heven] at hx ⊢
  exact G.constraint_eventually_expand hx ht

end LooplessGraph

end MatchingEntropy

end

end OAI

-- ---- from OAI.Combinatorics.PerfectMatching.Continuity ----
namespace OAI

/-!
Boundary lower semicontinuity of maximum entropy and attainment of the entropy defect.
-/

noncomputable section

open scoped BigOperators Topology
open Filter

namespace MatchingEntropy

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

omit [Fintype V] [DecidableEq V] in
/-- Concavity of H follows from mixing genuine optimizing probability laws. -/
theorem maxMatchingEntropy_mix_ge (G : LooplessGraph V E) {x y : E → ℝ}
    (hx : x ∈ G.polytope) (hy : y ∈ G.polytope) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (1-t)*maxMatchingEntropy G x+t*maxMatchingEntropy G y ≤
      maxMatchingEntropy G ((1-t) • x+t • y) := by
  obtain ⟨p,hp,hpe⟩ := maxMatchingEntropy_attained G hx
  obtain ⟨q,hq,hqe⟩ := maxMatchingEntropy_attained G hy
  rw [← hpe,← hqe]
  apply (entropy_mix_ge hp.1.1 hq.1.1 ht).trans
  apply entropy_le_maxMatchingEntropy
  refine ⟨convex_probabilitySimplex _ hp.1 hq.1 (sub_nonneg.mpr ht.2) ht.1 (by ring),?_⟩
  change G.meanLinear ((1-t) • p+t • q) = _
  rw [map_add,map_smul,map_smul]
  change (1-t) • G.mean p+t • G.mean q = _
  rw [hp.2,hq.2]

/-- Boundary lower semicontinuity, using the finite matching-polytope constraints.
A fixed small mixing coefficient suffices for each prescribed entropy tolerance. -/
theorem maxMatchingEntropy_lowerSemicontinuousOn (G : LooplessGraph V E)
    (heven : Even (Fintype.card V)) :
    LowerSemicontinuousOn (maxMatchingEntropy G) G.polytope := by
  intro x hx r hr
  have hn := maxMatchingEntropy_nonneg G hx
  have hden : 0 < maxMatchingEntropy G x+1 := by linarith
  have ha : 0 < min (1:ℝ) ((maxMatchingEntropy G x-r)/(maxMatchingEntropy G x+1)) :=
    lt_min (by norm_num) (div_pos (sub_pos.mpr hr) hden)
  obtain ⟨t,ht0,htt⟩ := exists_between ha
  have ht1 : t<1 := htt.trans_le (min_le_left _ _)
  have htb : t*(maxMatchingEntropy G x+1) < maxMatchingEntropy G x-r :=
    (lt_div_iff₀ hden).mp (htt.trans_le (min_le_right _ _))
  filter_upwards [G.polytope_eventually_expand heven hx ht0] with y hy
  have hh := maxMatchingEntropy_mix_ge G hx hy ⟨ht0.le,ht1.le⟩
  have he : (1-t) • x+t • (x+t⁻¹ • (y-x))=y := by
    ext e
    simp only [Pi.add_apply,Pi.smul_apply,Pi.sub_apply,smul_eq_mul]
    field_simp
    ring
  rw [he] at hh
  have hz := mul_nonneg ht0.le (maxMatchingEntropy_nonneg G hy)
  nlinarith

end MatchingEntropy

end

end OAI

-- ---- platform node ----
open OAI OAI.MatchingEntropy
open scoped BigOperators Topology
open Filter
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

theorem solution (G : LooplessGraph V E)
    (heven : Even (Fintype.card V)) :
    LowerSemicontinuousOn (maxMatchingEntropy G) G.polytope := by
  first
    | exact OAI.MatchingEntropy.maxMatchingEntropy_lowerSemicontinuousOn G heven
    | exact OAI.MatchingEntropy.maxMatchingEntropy_lowerSemicontinuousOn
    | (apply OAI.MatchingEntropy.maxMatchingEntropy_lowerSemicontinuousOn <;> assumption)
    | (intros; apply OAI.MatchingEntropy.maxMatchingEntropy_lowerSemicontinuousOn <;> assumption)
