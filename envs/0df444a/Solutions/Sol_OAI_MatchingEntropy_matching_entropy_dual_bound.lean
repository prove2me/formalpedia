-- Prove2me | solution 1 for OAI.MatchingEntropy.matching_entropy_dual_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T01:41:28.466806+00:00
-- url     : https://prove2.me/submissions/64d4a4fa-ade1-482a-bec7-0ec309caa242

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/PerfectMatching/Duality.lean:L101-L130
-- (upload_full_project.md Phase 4): solution for node OAI.MatchingEntropy.matching_entropy_dual_bound. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_MatchingEntropy
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Model
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Basic
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Duality
import Theorems.Thm_OAI_MatchingEntropy_LooplessGraph_mem_polytope_iff
import Theorems.Thm_OAI_MatchingEntropy_entropy_partition_bound
import Theorems.Thm_OAI_MatchingEntropy_matching_optimizer_face_support
import Theorems.Thm_OAI_MatchingEntropy_matching_optimizer_log_annihilates

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
theorem mean_mem_polytope (G : LooplessGraph V E) {p : G.Matching → ℝ}
    (hp : p ∈ probabilitySimplex G.Matching) : G.mean p ∈ G.polytope := by
  have h := (convex_convexHull ℝ (Set.range G.indicator)).sum_mem
    (fun M _ ↦ hp.1 M) hp.2 (fun M _ ↦ subset_convexHull ℝ _ (Set.mem_range_self M))
  have he : G.mean p = ∑ M, p M • G.indicator M := by
    ext e
    simp [mean]
  rw [he]
  exact h

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

end MatchingEntropy

end

end OAI

-- ---- from OAI.Combinatorics.PerfectMatching.Duality ----
namespace OAI

/-!
Finite exponential tilts, partition functions, and entropy duality on a face.
-/

noncomputable section

open scoped BigOperators Topology
open Filter

namespace MatchingEntropy

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

omit [Fintype V] [DecidableEq V] in
theorem sum_mean_assoc (G : LooplessGraph V E) (p : G.Matching → ℝ) (u : E → ℝ) :
    (∑ M, p M * (∑ e, u e * G.indicator M e)) = ∑ e, u e * G.mean p e := by
  simp only [LooplessGraph.mean, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  apply Finset.sum_congr rfl
  intro M _
  ring

omit [Fintype V] [DecidableEq V] in
theorem linearScore_expectation (G : LooplessGraph V E) (p : G.Matching → ℝ)
    (u : E → ℝ) (c : ℝ) :
    (∑ M, p M * linearScore G u c M) =
      (∑ e, u e * G.mean p e) - c * ∑ M, p M := by
  simp only [linearScore, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
  rw [sum_mean_assoc]
  ring

omit [Fintype V] [DecidableEq V] in
/-- A genuine upper bound on the actual maximum entropy at every mean in the
optimizer's face. This is proved from Gibbs' inequality, not assumed as a
replacement definition of H. -/
theorem matching_entropy_dual_bound (G : LooplessGraph V E) {y : E → ℝ}
    {p : G.Matching → ℝ} (hp : p ∈ G.feasibleLaws y)
    (hopt : entropy p = maxMatchingEntropy G y)
    {r : G.Matching → ℝ} (hr : r ∈ probabilitySimplex G.Matching)
    (hrsupport : ∀ M, p M = 0 → r M = 0)
    (u : E → ℝ) (c t : ℝ) :
    maxMatchingEntropy G (G.mean r) ≤
      Real.log (partition p (linearScore G u c) t) - ∑ M, r M * Real.log (p M) -
        t * ∑ M, r M * linearScore G u c M := by
  obtain ⟨q, hq, heq⟩ := maxMatchingEntropy_attained G (G.mean_mem_polytope hr)
  have hsuppq := matching_optimizer_face_support G hp hopt hq.1 hr hq.2 hrsupport
  have hmean : G.mean (q-r) = 0 := by
    change G.meanLinear (q-r) = 0
    rw [map_sub]
    change G.mean q-G.mean r = 0
    rw [hq.2, sub_self]
  have hsum : ∑ M, (q-r) M = 0 := by
    simp only [Pi.sub_apply, Finset.sum_sub_distrib, hq.1.2, hr.2, sub_self]
  have hlog := matching_optimizer_log_annihilates G hp hopt (q-r) hsum hmean
    (fun M hM => by simp [hsuppq M hM, hrsupport M hM])
  simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib, sub_eq_zero] at hlog
  have hscore : (∑ M, q M*linearScore G u c M) = ∑ M, r M*linearScore G u c M := by
    rw [linearScore_expectation, linearScore_expectation, hq.2, hq.1.2, hr.2]
  rw [← heq]
  simpa only [hlog, hscore] using entropy_partition_bound hp.1 hq.1 hsuppq
    (linearScore G u c) t

end MatchingEntropy

end

end OAI

-- ---- platform node ----
open OAI OAI.MatchingEntropy
open scoped BigOperators Topology
open Filter
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

omit [Fintype V] [DecidableEq V] in
theorem solution (G : LooplessGraph V E) {y : E → ℝ}
    {p : G.Matching → ℝ} (hp : p ∈ G.feasibleLaws y)
    (hopt : entropy p = maxMatchingEntropy G y)
    {r : G.Matching → ℝ} (hr : r ∈ probabilitySimplex G.Matching)
    (hrsupport : ∀ M, p M = 0 → r M = 0)
    (u : E → ℝ) (c t : ℝ) :
    maxMatchingEntropy G (G.mean r) ≤
      Real.log (partition p (linearScore G u c) t) - ∑ M, r M * Real.log (p M) -
        t * ∑ M, r M * linearScore G u c M := by
  first
    | exact OAI.MatchingEntropy.matching_entropy_dual_bound G hp hopt hr hrsupport u c t
    | exact OAI.MatchingEntropy.matching_entropy_dual_bound
    | (apply OAI.MatchingEntropy.matching_entropy_dual_bound <;> assumption)
    | (intros; apply OAI.MatchingEntropy.matching_entropy_dual_bound <;> assumption)
