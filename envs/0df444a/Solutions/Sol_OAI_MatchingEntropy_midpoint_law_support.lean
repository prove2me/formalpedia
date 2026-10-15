-- Prove2me | solution 1 for OAI.MatchingEntropy.midpoint_law_support
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T02:24:19.463135+00:00
-- url     : https://prove2.me/submissions/ebbbd24a-dcdd-4348-80a7-24a45b617f5a

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/PerfectMatching/MatchingCovariance.lean:L34-L57
-- (upload_full_project.md Phase 4): solution for node OAI.MatchingEntropy.midpoint_law_support. The node keeps its source
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
import Theorems.Thm_OAI_MatchingEntropy_matching_optimizer_support

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
/-- A feasible two-sided direction has a positive-side law supported on the
entropy optimizer at its midpoint. -/
theorem midpoint_law_support (G : LooplessGraph V E) {x v : E → ℝ} {a : ℝ}
    {p q r : G.Matching → ℝ} (hp : p ∈ G.feasibleLaws x)
    (hopt : entropy p=maxMatchingEntropy G x)
    (hq : q ∈ G.feasibleLaws (x+a • v))
    (hr : r ∈ G.feasibleLaws (x+(-a) • v)) :
    ∀ M, 0 < q M → 0 < p M := by
  let w : G.Matching → ℝ := (1/2:ℝ) • q+(1/2:ℝ) • r
  have hw : w ∈ G.feasibleLaws x := by
    refine ⟨convex_probabilitySimplex _ hq.1 hr.1 (by norm_num) (by norm_num) (by norm_num),?_⟩
    change G.meanLinear ((1/2:ℝ) • q+(1/2:ℝ) • r) = _
    rw [map_add,map_smul,map_smul]
    change (1/2:ℝ) • G.mean q+(1/2:ℝ) • G.mean r = _
    rw [hq.2,hr.2]
    ext e
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul]
    ring
  intro M hM
  apply matching_optimizer_support G hp hw hopt
  change 0 < (1/2:ℝ)*q M+(1/2:ℝ)*r M
  have hh := hr.1.1 M
  linarith

end MatchingEntropy

end

end OAI

-- ---- platform node ----
open OAI OAI.MatchingEntropy
open scoped BigOperators Topology
open Filter
open Matrix
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

omit [Fintype V] [DecidableEq V] in
theorem solution (G : LooplessGraph V E) {x v : E → ℝ} {a : ℝ}
    {p q r : G.Matching → ℝ} (hp : p ∈ G.feasibleLaws x)
    (hopt : entropy p=maxMatchingEntropy G x)
    (hq : q ∈ G.feasibleLaws (x+a • v))
    (hr : r ∈ G.feasibleLaws (x+(-a) • v)) :
    ∀ M, 0 < q M → 0 < p M := by
  first
    | exact OAI.MatchingEntropy.midpoint_law_support G hp hopt hq hr
    | exact OAI.MatchingEntropy.midpoint_law_support
    | (apply OAI.MatchingEntropy.midpoint_law_support <;> assumption)
    | (intros; apply OAI.MatchingEntropy.midpoint_law_support <;> assumption)
