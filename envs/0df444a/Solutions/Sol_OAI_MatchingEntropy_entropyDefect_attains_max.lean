-- Prove2me | solution 1 for OAI.MatchingEntropy.entropyDefect_attains_max
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T02:19:15.84869+00:00
-- url     : https://prove2.me/submissions/b12b204d-8843-46a5-9750-a1bfd5bb9f55

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/PerfectMatching/Continuity.lean:L62-L77
-- (upload_full_project.md Phase 4): solution for node OAI.MatchingEntropy.entropyDefect_attains_max. The node keeps its source
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
import Theorems.Thm_OAI_MatchingEntropy_LooplessGraph_mem_polytope_iff
import Theorems.Thm_OAI_MatchingEntropy_maxMatchingEntropy_lowerSemicontinuousOn

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

/-- The actual entropy defect attains a maximum on the closed matching polytope. -/
theorem entropyDefect_attains_max (G : LooplessGraph V E)
    (heven : Even (Fintype.card V)) (hPM : Nonempty G.Matching) (m : ℝ) :
    ∃ x ∈ G.polytope, ∀ y ∈ G.polytope, entropyDefect G m y ≤ entropyDefect G m x := by
  have hc : Continuous (fun y : E → ℝ => entropyBarrier m (entropy y)) := by
    have hb : Continuous (entropyBarrier m) := by unfold entropyBarrier; fun_prop
    exact hb.comp continuous_entropy
  have hs : UpperSemicontinuousOn (entropyDefect G m) G.polytope := by
    change UpperSemicontinuousOn (fun y => entropyBarrier m (entropy y)-maxMatchingEntropy G y) G.polytope
    simpa only [sub_eq_add_neg, Pi.neg_apply] using
      hc.continuousOn.upperSemicontinuousOn.add
        (maxMatchingEntropy_lowerSemicontinuousOn G heven).neg
  have hn : G.polytope.Nonempty := by
    obtain ⟨M⟩ := hPM
    exact ⟨G.indicator M,subset_convexHull ℝ _ (Set.mem_range_self M)⟩
  exact UpperSemicontinuousOn.exists_isMaxOn hn G.compact_polytope hs

end MatchingEntropy

end

end OAI

-- ---- platform node ----
open OAI OAI.MatchingEntropy
open scoped BigOperators Topology
open Filter
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

theorem solution (G : LooplessGraph V E)
    (heven : Even (Fintype.card V)) (hPM : Nonempty G.Matching) (m : ℝ) :
    ∃ x ∈ G.polytope, ∀ y ∈ G.polytope, entropyDefect G m y ≤ entropyDefect G m x := by
  first
    | exact OAI.MatchingEntropy.entropyDefect_attains_max G heven hPM m
    | exact OAI.MatchingEntropy.entropyDefect_attains_max
    | (apply OAI.MatchingEntropy.entropyDefect_attains_max <;> assumption)
    | (intros; apply OAI.MatchingEntropy.entropyDefect_attains_max <;> assumption)
