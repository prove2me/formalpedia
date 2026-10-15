-- Prove2me | solution 1 for OAI.MatchingEntropy.matching_optimizer_log_annihilates
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T01:36:06.186727+00:00
-- url     : https://prove2.me/submissions/ee6d7bf3-d513-48df-b790-aaa17a0fc6a7

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/PerfectMatching/Optimizer.lean:L153-L185
-- (upload_full_project.md Phase 4): solution for node OAI.MatchingEntropy.matching_optimizer_log_annihilates. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_MatchingEntropy
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Model
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Basic
import Theorems.Thm_OAI_MatchingEntropy_entropy_line_hasDerivAt

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
/-- The log probabilities of the actual optimizer annihilate every feasible
mass/mean-preserving linear variation. No exponential representation assumed. -/
theorem matching_optimizer_log_annihilates (G : LooplessGraph V E) {y : E → ℝ}
    {p : G.Matching → ℝ} (hp : p ∈ G.feasibleLaws y)
    (hopt : entropy p = maxMatchingEntropy G y) (v : G.Matching → ℝ)
    (hvsum : ∑ M, v M = 0) (hvmean : G.mean v = 0)
    (hsupp : ∀ M, p M = 0 → v M = 0) :
    ∑ M, v M * Real.log (p M) = 0 := by
  have hev : ∀ᶠ t : ℝ in 𝓝 0, ∀ M, 0 ≤ p M+t*v M := by
    apply Filter.eventually_all.mpr
    intro M
    by_cases hM : p M = 0
    · exact Filter.Eventually.of_forall (fun t => by simp [hM, hsupp M hM])
    · have hpos : 0 < p M := lt_of_le_of_ne (hp.1.1 M) (Ne.symm hM)
      have hc : Continuous (fun t : ℝ => p M+t*v M) := by fun_prop
      have hh : {t : ℝ | 0 < p M+t*v M} ∈ 𝓝 0 :=
        (isOpen_lt continuous_const hc).mem_nhds (by simpa using hpos)
      exact Filter.Eventually.mono hh (fun t ht => ht.le)
  have hlocal : IsLocalMax (fun t : ℝ => entropy (fun M => p M+t*v M)) 0 := by
    filter_upwards [hev] with t ht
    have hmean : G.mean (fun M => p M+t*v M) = y := by
      change G.meanLinear (p+t • v) = y
      rw [map_add, map_smul]
      change G.mean p + t • G.mean v = y
      rw [hp.2, hvmean, smul_zero, add_zero]
    have hsum : ∑ M, (p M+t*v M) = 1 := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, hp.1.2, hvsum, mul_zero, add_zero]
    have hle := entropy_le_maxMatchingEntropy (G := G) ⟨⟨ht, hsum⟩, hmean⟩
    simpa only [zero_mul, add_zero, ← hopt] using hle
  have hh := hlocal.deriv_eq_zero
  rw [(entropy_line_hasDerivAt p v hsupp).deriv, hvsum] at hh
  linarith

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
    (hopt : entropy p = maxMatchingEntropy G y) (v : G.Matching → ℝ)
    (hvsum : ∑ M, v M = 0) (hvmean : G.mean v = 0)
    (hsupp : ∀ M, p M = 0 → v M = 0) :
    ∑ M, v M * Real.log (p M) = 0 := by
  first
    | exact OAI.MatchingEntropy.matching_optimizer_log_annihilates G hp hopt v hvsum hvmean hsupp
    | exact OAI.MatchingEntropy.matching_optimizer_log_annihilates
    | (apply OAI.MatchingEntropy.matching_optimizer_log_annihilates <;> assumption)
    | (intros; apply OAI.MatchingEntropy.matching_optimizer_log_annihilates <;> assumption)
