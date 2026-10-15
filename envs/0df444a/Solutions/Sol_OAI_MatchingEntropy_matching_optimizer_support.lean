-- Prove2me | solution 1 for OAI.MatchingEntropy.matching_optimizer_support
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T01:33:09.855993+00:00
-- url     : https://prove2.me/submissions/1cfec223-e500-4bc9-ad00-5a5df0e452d0

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/PerfectMatching/Optimizer.lean:L79-L96
-- (upload_full_project.md Phase 4): solution for node OAI.MatchingEntropy.matching_optimizer_support. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_MatchingEntropy
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Model
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Basic
import Theorems.Thm_OAI_MatchingEntropy_entropy_maximizer_support

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

namespace LooplessGraph

end LooplessGraph

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

omit [Fintype V] [DecidableEq V] in
/-- The preceding support conclusion for the concrete matching-law optimizer. -/
theorem matching_optimizer_support (G : LooplessGraph V E) {y : E → ℝ}
    {p q : G.Matching → ℝ} (hp : p ∈ G.feasibleLaws y)
    (hq : q ∈ G.feasibleLaws y) (hopt : entropy p = maxMatchingEntropy G y)
    {M : G.Matching} (hM : 0 < q M) : 0 < p M := by
  apply entropy_maximizer_support hp.1.1 hq.1.1 _ hM
  intro t ht
  apply le_trans (entropy_le_maxMatchingEntropy (G := G) (y := y) ?_) (le_of_eq hopt.symm)
  constructor
  · exact convex_probabilitySimplex _ hp.1 hq.1
      (sub_nonneg.mpr ht.2) ht.1 (by ring)
  · calc
      G.mean (fun i => (1-t)*p i+t*q i) =
          (1-t) • G.mean p + t • G.mean q := by
        exact (G.meanLinear).map_add ((1-t) • p) (t • q) |>.trans (by
          rw [LinearMap.map_smul, LinearMap.map_smul]; rfl)
      _ = y := by rw [hp.2, hq.2]; ext e; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring

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
    {p q : G.Matching → ℝ} (hp : p ∈ G.feasibleLaws y)
    (hq : q ∈ G.feasibleLaws y) (hopt : entropy p = maxMatchingEntropy G y)
    {M : G.Matching} (hM : 0 < q M) : 0 < p M := by
  first
    | exact OAI.MatchingEntropy.matching_optimizer_support G hp hq hopt hM
    | exact OAI.MatchingEntropy.matching_optimizer_support
    | (apply OAI.MatchingEntropy.matching_optimizer_support <;> assumption)
    | (intros; apply OAI.MatchingEntropy.matching_optimizer_support <;> assumption)
