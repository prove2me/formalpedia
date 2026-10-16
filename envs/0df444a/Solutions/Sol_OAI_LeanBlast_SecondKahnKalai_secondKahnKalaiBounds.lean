-- Prove2me | solution 1 for OAI.LeanBlast.SecondKahnKalai.secondKahnKalaiBounds
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T03:16:11.261254+00:00
-- url     : https://prove2.me/submissions/0cd3dbd1-7195-448d-ae17-122a62fe11a3

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/GraphThreshold/Main.lean:L25-L65
-- (upload_full_project.md Phase 4): solution for the platform mission target OAI.LeanBlast.SecondKahnKalai.secondKahnKalaiBounds.
-- The source declaration is kept inside its namespace next to the proof-only helpers it needs;
-- `theorem solution` restates the platform stub (Theorems.Thm_OAI_LeanBlast_SecondKahnKalai_secondKahnKalaiBounds) verbatim and is proved by it.
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Action.Pointwise.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.List.Pairwise
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Order.Monotone
import Definitions.Def_SecondKahnKalai
import Definitions.Def_OAI_Combinatorics_GraphThreshold_GraphEncoding
import Definitions.Def_OAI_Combinatorics_GraphThreshold_GraphProbability
import Definitions.Def_OAI_Combinatorics_GraphThreshold_EmbeddingExtension
import Definitions.Def_OAI_Combinatorics_GraphThreshold_GraphSupport
import Definitions.Def_OAI_Combinatorics_GraphThreshold_Basic
import Definitions.Def_OAI_Combinatorics_GraphThreshold_FiniteProbability
import Definitions.Def_OAI_Combinatorics_GraphThreshold_CopyOrbits
import Definitions.Def_OAI_Combinatorics_GraphThreshold_GraphExpectedCopies
import Definitions.Def_OAI_Combinatorics_GraphThreshold_GraphCopies
import Definitions.Def_OAI_Combinatorics_GraphThreshold_ProbabilityTree
import Definitions.Def_OAI_Combinatorics_GraphThreshold_LocalFailureNumerics
import Definitions.Def_OAI_Combinatorics_GraphThreshold_Predecessor
import Definitions.Def_OAI_Combinatorics_GraphThreshold_GraphHierarchy
import Definitions.Def_OAI_Combinatorics_GraphThreshold_BernoulliCoupling
import Definitions.Def_OAI_Combinatorics_GraphThreshold_AdaptiveTrials
import Definitions.Def_OAI_Combinatorics_GraphThreshold_ProbabilityTreeFacts
import Definitions.Def_OAI_Combinatorics_GraphThreshold_ProbabilityTreeTrim
import Definitions.Def_OAI_Combinatorics_GraphThreshold_CapacityIteration
import Definitions.Def_OAI_Combinatorics_GraphThreshold_Resampling
import Definitions.Def_OAI_Combinatorics_GraphThreshold_ResamplingEvents
import Definitions.Def_OAI_Combinatorics_GraphThreshold_TreeReductionData
import Definitions.Def_OAI_Combinatorics_GraphThreshold_TreeReduction
import Definitions.Def_OAI_Combinatorics_GraphThreshold_OutsideChangeOfMeasure
import Definitions.Def_OAI_Combinatorics_GraphThreshold_TreePotential
import Definitions.Def_OAI_Combinatorics_GraphThreshold_TreeCovering
import Theorems.Thm_OAI_LeanBlast_SecondKahnKalai_ProbabilityTree_CoverState_exists_advance_of_good
import Theorems.Thm_OAI_LeanBlast_SecondKahnKalai_bernoulliExpectation_mono_parameter
import Theorems.Thm_OAI_LeanBlast_SecondKahnKalai_bernoulliExpectation_nodePotential_le
import Theorems.Thm_OAI_LeanBlast_SecondKahnKalai_capacity_failure_sum_lt_one_quarter
import Theorems.Thm_OAI_LeanBlast_SecondKahnKalai_choose_le_exp_div_pow
import Theorems.Thm_OAI_LeanBlast_SecondKahnKalai_copy_incidence_identity
import Theorems.Thm_OAI_LeanBlast_SecondKahnKalai_exists_spread_orbit_tree_of_predecessors
import Theorems.Thm_OAI_LeanBlast_SecondKahnKalai_expectationThreshold_pos
import Theorems.Thm_OAI_LeanBlast_SecondKahnKalai_expectation_intersection_eq_sum
import Theorems.Thm_OAI_LeanBlast_SecondKahnKalai_expectedCopies_formula
import Theorems.Thm_OAI_LeanBlast_SecondKahnKalai_intersection_card_ge_le_subsets
import Theorems.Thm_OAI_LeanBlast_SecondKahnKalai_isContained_iff_exists_smul_subset
import Theorems.Thm_OAI_LeanBlast_SecondKahnKalai_localFailureMass_add_successfulTargetMass
import Theorems.Thm_OAI_LeanBlast_SecondKahnKalai_local_failure_bound
import Theorems.Thm_OAI_LeanBlast_SecondKahnKalai_normalized_count_score_bound
import Theorems.Thm_OAI_LeanBlast_SecondKahnKalai_one_lt_nodePotential_of_bad
import Theorems.Thm_OAI_LeanBlast_SecondKahnKalai_outside_change_of_measure_moment
import Theorems.Thm_OAI_LeanBlast_SecondKahnKalai_predecessor_conditional_ratio_le
import Theorems.Thm_OAI_LeanBlast_SecondKahnKalai_treePotential_dependsOnlyOn
import Theorems.Thm_OAI_LeanBlast_SecondKahnKalai_tree_covering_of_progress

-- ---- from OAI.Combinatorics.GraphThreshold.GraphEncoding ----
namespace OAI

noncomputable section

open scoped Pointwise

namespace LeanBlast.SecondKahnKalai

variable {n : ℕ}

theorem edgeCount_eq_card_edgeFinset {V : Type*} [Fintype V] (G : SimpleGraph V)
    [Fintype G.edgeSet] :
    edgeCount G = G.edgeFinset.card := by
  classical
  rw [edgeCount, Nat.card_eq_fintype_card, SimpleGraph.edgeFinset_card]

end LeanBlast.SecondKahnKalai

end

end OAI

-- ---- from OAI.Combinatorics.GraphThreshold.GraphProbability ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

namespace LeanBlast.SecondKahnKalai

section BernoulliEndpoints

variable {X : Type*} [Fintype X] [DecidableEq X]

end BernoulliEndpoints

theorem copyCount_iso_target {V W U : Type*} [Fintype V]
    (G : SimpleGraph V) {H : SimpleGraph W} {F : SimpleGraph U}
    (e : H ≃g F) : G.copyCount H = G.copyCount F := by
  classical
  unfold SimpleGraph.copyCount
  congr 1
  apply Finset.filter_congr
  intro J _
  constructor
  · rintro ⟨g⟩
    exact ⟨g.comp e.symm⟩
  · rintro ⟨g⟩
    exact ⟨g.comp e⟩

theorem expectedCopies_iso {V W : Type*} (n : ℕ) (p : ℝ)
    {H : SimpleGraph V} {F : SimpleGraph W} (e : H ≃g F) :
    expectedCopies n p H = expectedCopies n p F := by
  unfold expectedCopies bernoulliExpectation
  simp_rw [copyCount_iso_target _ e]

theorem isContained_top_of_card_le {V : Type*} [Fintype V] (n : ℕ)
    (H : SimpleGraph V) (hcard : Fintype.card V ≤ n) :
    H.IsContained (⊤ : SimpleGraph (Fin n)) := by
  obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le
    (show Fintype.card V ≤ Fintype.card (Fin n) by simpa using hcard)
  refine ⟨{ toHom := ⟨f, ?_⟩, injective' := f.injective }⟩
  intro a b hab
  exact f.injective.ne hab.ne

theorem expectedCopies_one_ge_one {V : Type*} [Fintype V] (n : ℕ)
    (H : SimpleGraph V) (hcard : Fintype.card V ≤ n) :
    1 ≤ expectedCopies n 1 H := by
  have hp : 0 < (⊤ : SimpleGraph (Fin n)).copyCount H :=
    SimpleGraph.copyCount_pos.mpr (isContained_top_of_card_le n H hcard)
  simpa only [expectedCopies, bernoulliExpectation_one, graphOfEdges_univ,
    Nat.one_le_cast] using Nat.succ_le_of_lt hp

end LeanBlast.SecondKahnKalai

end

end OAI

-- ---- from OAI.Combinatorics.GraphThreshold.Thresholds ----
namespace OAI

/-!
# Continuity and attainment of the graph thresholds

Every probability is a literal finite sum of Bernoulli products.  The
admissible parameter sets are closed subsets of `[0,1]`; endpoint feasibility
therefore makes their infima admissible.  No minimizer is postulated.
-/

noncomputable section

open scoped BigOperators

namespace LeanBlast.SecondKahnKalai

theorem continuous_bernoulliWeight {X : Type*} [Fintype X] [DecidableEq X]
    (W : Finset X) : Continuous (fun p : ℝ => bernoulliWeight p W) := by
  unfold bernoulliWeight
  apply continuous_finsetProd
  intro x _
  split_ifs <;> fun_prop

theorem continuous_bernoulliExpectation {X : Type*} [Fintype X] [DecidableEq X]
    (f : Finset X → ℝ) : Continuous (fun p : ℝ => bernoulliExpectation p f) := by
  unfold bernoulliExpectation
  apply continuous_finsetSum
  intro W _
  exact (continuous_bernoulliWeight W).mul continuous_const

theorem continuous_expectedCopies {V : Type*} (n : ℕ) (H : SimpleGraph V) :
    Continuous (fun p : ℝ => expectedCopies n p H) := by
  classical
  exact continuous_bernoulliExpectation _

theorem isClosed_expectationFeasible {V : Type*} (n : ℕ) (H : SimpleGraph V) :
    IsClosed {p : ℝ | p ∈ Set.Icc 0 1 ∧
      ∀ F : H.Subgraph, (1 / 2 : ℝ) ≤ expectedCopies n p F.coe} := by
  have hc : IsClosed (⋂ F : H.Subgraph,
      {p : ℝ | (1 / 2 : ℝ) ≤ expectedCopies n p F.coe}) :=
    isClosed_iInter (fun F : H.Subgraph =>
      isClosed_le continuous_const (continuous_expectedCopies n F.coe))
  convert (isClosed_Icc : IsClosed (Set.Icc (0 : ℝ) 1)).inter hc using 1
  ext p
  simp

/-- All subgraph constraints hold at the expectation infimum.  Arbitrary
intersections of closed constraints suffice, so no enumeration is assumed. -/
theorem expectationThreshold_attained_of_one {V : Type*} (n : ℕ) (H : SimpleGraph V)
    (hone : ∀ F : H.Subgraph, (1 / 2 : ℝ) ≤ expectedCopies n 1 F.coe) :
    expectationThreshold n H ∈ Set.Icc 0 1 ∧
      ∀ F : H.Subgraph, (1 / 2 : ℝ) ≤
        expectedCopies n (expectationThreshold n H) F.coe := by
  have hb : BddBelow {p : ℝ | p ∈ Set.Icc 0 1 ∧
      ∀ F : H.Subgraph, (1 / 2 : ℝ) ≤ expectedCopies n p F.coe} := by
    refine ⟨0, ?_⟩
    intro p hp
    exact hp.1.1
  have hn : Set.Nonempty {p : ℝ | p ∈ Set.Icc 0 1 ∧
      ∀ F : H.Subgraph, (1 / 2 : ℝ) ≤ expectedCopies n p F.coe} :=
    ⟨1, ⟨by norm_num, hone⟩⟩
  exact (isClosed_expectationFeasible n H).csInf_mem hn hb

/-- Any admissible parameter gives an upper bound on the actual critical
threshold. -/
theorem criticalThreshold_le_of_probability {V : Type*} (n : ℕ) (H : SimpleGraph V)
    {p : ℝ} (hp : p ∈ Set.Icc 0 1)
    (hprob : (1 / 2 : ℝ) ≤ containmentProbability n p H) :
    criticalThreshold n H ≤ p := by
  unfold criticalThreshold
  apply csInf_le
  · refine ⟨0, ?_⟩
    intro q hq
    exact hq.1.1
  · exact ⟨hp, hprob⟩

theorem expectationFeasible_one {V : Type*} [Fintype V]
    (n : ℕ) (H : SimpleGraph V) (hcard : Fintype.card V ≤ n)
    (F : H.Subgraph) : (1 / 2 : ℝ) ≤ expectedCopies n 1 F.coe := by
  classical
  have hFcard : Fintype.card F.verts ≤ n :=
    (Fintype.card_le_of_injective (fun v : F.verts => (v : V)) Subtype.val_injective).trans hcard
  exact (by norm_num : (1 / 2 : ℝ) ≤ 1).trans (expectedCopies_one_ge_one n F.coe hFcard)

/-- Every actual subgraph expectation constraint holds at `p_E`. -/
theorem expectationThreshold_attained {V : Type*} [Fintype V]
    (n : ℕ) (H : SimpleGraph V) (hcard : Fintype.card V ≤ n) :
    expectationThreshold n H ∈ Set.Icc 0 1 ∧
      ∀ F : H.Subgraph, (1 / 2 : ℝ) ≤
        expectedCopies n (expectationThreshold n H) F.coe :=
  expectationThreshold_attained_of_one n H (expectationFeasible_one n H hcard)

end LeanBlast.SecondKahnKalai

end

end OAI

-- ---- from OAI.Combinatorics.GraphThreshold.ThresholdBounds ----
namespace OAI

/-!
# Explicit constants in the threshold conclusion

The tree argument first gives a logarithm of an edge capacity.  These elementary
bounds turn that quantity into the two constants stated for graphs.
-/

noncomputable section

namespace LeanBlast.SecondKahnKalai

theorem logTwo_eq_logb (x : ℝ) : logTwo x = Real.logb 2 x := rfl

theorem logTwo_nonneg {x : ℝ} (hx : 1 ≤ x) : 0 ≤ logTwo x := by
  unfold logTwo
  exact div_nonneg (Real.log_nonneg hx) (Real.log_pos (by norm_num)).le

theorem logTwo_mono {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    logTwo x ≤ logTwo y := by
  unfold logTwo
  exact div_le_div_of_nonneg_right (Real.log_le_log hx hxy)
    (Real.log_pos (by norm_num)).le

theorem edgeCount_le_sq {V : Type*} [Fintype V]
    (n : ℕ) (H : SimpleGraph V) (hcard : Fintype.card V ≤ n) :
    edgeCount H ≤ n ^ 2 := by
  classical
  rw [edgeCount_eq_card_edgeFinset]
  calc
    H.edgeFinset.card ≤ (Fintype.card V).choose 2 :=
      SimpleGraph.card_edgeFinset_le_card_choose_two
    _ ≤ (Fintype.card V) ^ 2 := Nat.choose_le_pow _ _
    _ ≤ n ^ 2 := Nat.pow_le_pow_left hcard 2

theorem one_add_logTwo_le_three_logTwo (n h : ℕ)
    (hn : 2 ≤ n) (hh : 1 ≤ h) (hhn : h ≤ n ^ 2) :
    1 + logTwo (h : ℝ) ≤ 3 * logTwo (n : ℝ) := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hh' : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hhn' : (h : ℝ) ≤ (n : ℝ) ^ 2 := by exact_mod_cast hhn
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogn : Real.log 2 ≤ Real.log (n : ℝ) :=
    Real.log_le_log (by norm_num) hn'
  have hone : 1 ≤ logTwo (n : ℝ) := by
    unfold logTwo
    exact (le_div_iff₀ hlog2).mpr (by simpa using hlogn)
  have hlogh : Real.log (h : ℝ) ≤ 2 * Real.log (n : ℝ) := by
    calc
      Real.log (h : ℝ) ≤ Real.log ((n : ℝ) ^ 2) :=
        Real.log_le_log (by linarith) hhn'
      _ = 2 * Real.log (n : ℝ) := by rw [Real.log_pow]; norm_num
  have htwo : logTwo (h : ℝ) ≤ 2 * logTwo (n : ℝ) := by
    unfold logTwo
    simpa only [mul_div_assoc] using
      div_le_div_of_nonneg_right hlogh hlog2.le
  linarith

theorem graph_one_add_logTwo_le_three_logTwo {V : Type*} [Fintype V]
    (n : ℕ) (H : SimpleGraph V) (hn : 2 ≤ n)
    (hcard : Fintype.card V ≤ n) (hedge : 1 ≤ edgeCount H) :
    1 + logTwo (edgeCount H : ℝ) ≤ 3 * logTwo (n : ℝ) :=
  one_add_logTwo_le_three_logTwo n (edgeCount H) hn hedge
    (edgeCount_le_sq n H hcard)

theorem graphThresholdParameter_mem_unitInterval (q : ℝ) (h : ℕ)
    (hq : 0 ≤ q) (hh : 1 ≤ h) :
    min 1 (2048 * Real.exp 50 * q * (1 + logTwo (h : ℝ))) ∈ Set.Icc 0 1 := by
  have hlog : 0 ≤ logTwo (h : ℝ) := logTwo_nonneg (by exact_mod_cast hh)
  constructor
  · exact le_min (by norm_num) (mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) (Real.exp_pos 50).le) hq) (by linarith))
  · exact min_le_left _ _

theorem treeSamplingParameter_mem_unitInterval (q : ℝ) (m : ℕ)
    (hq : 0 ≤ q) (hm : 0 < m) :
    min 1 (16 * Real.exp 50 * (128 * q) *
      (1 + Real.logb 2 (m : ℝ))) ∈ Set.Icc 0 1 := by
  have hfactor : 16 * Real.exp 50 * (128 * q) = 2048 * Real.exp 50 * q := by ring
  rw [hfactor, ← logTwo_eq_logb]
  exact graphThresholdParameter_mem_unitInterval q m hq hm

theorem treeSamplingParameter_le_graphParameter (q : ℝ) (m h : ℕ)
    (hq : 0 ≤ q) (hm : 0 < m) (hmh : m ≤ h) :
    min 1 (16 * Real.exp 50 * (128 * q) * (1 + Real.logb 2 (m : ℝ))) ≤
      min 1 (2048 * Real.exp 50 * q * (1 + logTwo (h : ℝ))) := by
  apply min_le_min_left
  have hlog : logTwo (m : ℝ) ≤ logTwo (h : ℝ) :=
    logTwo_mono (by exact_mod_cast hm) (by exact_mod_cast hmh)
  calc
    16 * Real.exp 50 * (128 * q) * (1 + Real.logb 2 (m : ℝ)) =
        2048 * Real.exp 50 * q * (1 + logTwo (m : ℝ)) := by
      rw [logTwo_eq_logb]
      ring
    _ ≤ 2048 * Real.exp 50 * q * (1 + logTwo (h : ℝ)) :=
      mul_le_mul_of_nonneg_left (by linarith)
        (mul_nonneg (mul_nonneg (by norm_num) (Real.exp_pos 50).le) hq)

theorem graphThresholdParameter_le_vertexBound {V : Type*} [Fintype V]
    (n : ℕ) (H : SimpleGraph V) (q : ℝ) (hn : 2 ≤ n)
    (hcard : Fintype.card V ≤ n) (hedge : 1 ≤ edgeCount H) (hq : 0 ≤ q) :
    min 1 (2048 * Real.exp 50 * q * (1 + logTwo (edgeCount H : ℝ))) ≤
      6144 * Real.exp 50 * q * logTwo (n : ℝ) := by
  calc
    min 1 (2048 * Real.exp 50 * q * (1 + logTwo (edgeCount H : ℝ))) ≤
        2048 * Real.exp 50 * q * (1 + logTwo (edgeCount H : ℝ)) := min_le_right _ _
    _ ≤ 2048 * Real.exp 50 * q * (3 * logTwo (n : ℝ)) := by
      exact mul_le_mul_of_nonneg_left
        (graph_one_add_logTwo_le_three_logTwo n H hn hcard hedge)
        (mul_nonneg (mul_nonneg (by norm_num) (Real.exp_pos 50).le) hq)
    _ = 6144 * Real.exp 50 * q * logTwo (n : ℝ) := by ring

end LeanBlast.SecondKahnKalai

end

end OAI

-- ---- from OAI.Combinatorics.GraphThreshold.GraphContainment ----
namespace OAI

noncomputable section

open scoped Pointwise

namespace LeanBlast.SecondKahnKalai

variable {n : ℕ} {V : Type*}

theorem card_mappedGraphEdges [Fintype V] (f : V ↪ Fin n) (H : SimpleGraph V) :
    (graphEdges (H.map f)).card = edgeCount H := by
  classical
  rw [card_graphEdges, edgeCount_eq_card_edgeFinset, edgeCount_eq_card_edgeFinset]
  exact SimpleGraph.card_edgeFinset_map f H

theorem copyCount_pos_iff_exists_smul_subset (f : V ↪ Fin n) (H : SimpleGraph V)
    (W : Finset (Edge n)) :
    0 < (graphOfEdges W).copyCount H ↔
      ∃ σ : Equiv.Perm (Fin n), σ • graphEdges (H.map f) ⊆ W :=
  SimpleGraph.copyCount_pos.trans (isContained_iff_exists_smul_subset f H W)

end LeanBlast.SecondKahnKalai

end

end OAI

-- ---- from OAI.Combinatorics.GraphThreshold.GraphSupport ----
namespace OAI

noncomputable section

open scoped Pointwise

namespace LeanBlast.SecondKahnKalai

variable {n : ℕ}

theorem edgeCount_edgeSupportGraph (S : Finset (Edge n)) :
    edgeCount (edgeSupportGraph S) = S.card := by
  classical
  have h := card_mappedGraphEdges
    (Function.Embedding.subtype (fun v => v ∈ (graphOfEdges S).support))
    (edgeSupportGraph S)
  simpa only [edgeSupportGraph_map, graphEdges_graphOfEdges] using h.symm

theorem exists_subgraph_iso_edgeSupportGraph {V : Type*} (f : V ↪ Fin n)
    (H : SimpleGraph V) (S : Finset (Edge n))
    (hS : S ⊆ graphEdges (H.map f)) :
    ∃ F : H.Subgraph, Nonempty (edgeSupportGraph S ≃g F.coe) :=
  SimpleGraph.isContained_iff_exists_iso_subgraph.mp
    ⟨edgeSupportGraph_copy_of_subset f H S hS⟩

end LeanBlast.SecondKahnKalai

end

end OAI

-- ---- from OAI.Combinatorics.GraphThreshold.FiniteProbability ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

namespace LeanBlast.SecondKahnKalai

namespace FiniteLaw

variable {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]

theorem expectation_nonneg (μ : FiniteLaw Ω) {f : Ω → ℝ} (hf : ∀ ω, 0 ≤ f ω) :
    0 ≤ μ.expectation f :=
  Finset.sum_nonneg fun ω _ => mul_nonneg (μ.nonneg ω) (hf ω)

theorem expectation_mono (μ : FiniteLaw Ω) {f g : Ω → ℝ} (hfg : ∀ ω, f ω ≤ g ω) :
    μ.expectation f ≤ μ.expectation g :=
  Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (hfg ω) (μ.nonneg ω)

theorem prob_eq_expectation (μ : FiniteLaw Ω) (P : Ω → Prop) :
    μ.prob P = μ.expectation (fun ω => if P ω then 1 else 0) := by
  classical
  simp [prob, expectation, mul_ite]

theorem prob_mono (μ : FiniteLaw Ω) {P Q : Ω → Prop} (hPQ : ∀ ω, P ω → Q ω) :
    μ.prob P ≤ μ.prob Q := by
  classical
  apply Finset.sum_le_sum
  intro ω _
  by_cases hp : P ω
  · simp [hp, hPQ ω hp]
  · by_cases hq : Q ω <;> simp [hp, hq, μ.nonneg ω]

theorem prob_compl (μ : FiniteLaw Ω) (P : Ω → Prop) :
    μ.prob (fun ω => ¬ P ω) = 1 - μ.prob P := by
  classical
  have h : μ.prob P + μ.prob (fun ω => ¬ P ω) = 1 := by
    rw [prob, prob, ← Finset.sum_add_distrib, ← μ.total]
    apply Finset.sum_congr rfl
    intro ω _
    by_cases hp : P ω <;> simp [hp]
  linarith

theorem prob_le_expectation (μ : FiniteLaw Ω) (P : Ω → Prop) (f : Ω → ℝ)
    (hf : ∀ ω, 0 ≤ f ω) (hP : ∀ ω, P ω → 1 ≤ f ω) : μ.prob P ≤ μ.expectation f := by
  classical
  rw [prob_eq_expectation]
  apply μ.expectation_mono
  intro ω
  by_cases hp : P ω
  · simpa [hp] using hP ω hp
  · simpa [hp] using hf ω

end FiniteLaw

variable {X : Type*} [Fintype X] [DecidableEq X]

theorem bernoulliProbability_eq_expectation (p : ℝ) (P : Finset X → Prop) :
    bernoulliProbability p P = bernoulliExpectation p (fun W => if P W then 1 else 0) := by
  classical
  simp [bernoulliProbability, bernoulliExpectation, mul_ite]

end LeanBlast.SecondKahnKalai

end

end OAI

-- ---- from OAI.Combinatorics.GraphThreshold.CopyOrbits ----
namespace OAI

/-!
# Distinct subset copies under a finite group action

Copies are distinct orbit elements, not group elements or labeled embeddings.
All counting and probability statements therefore retain the stabilizer
multiplicities correctly, including for the empty subset.
-/

noncomputable section

open scoped BigOperators Pointwise

namespace LeanBlast.SecondKahnKalai

universe u v

variable (G : Type u) [Group G] [Fintype G]
variable {X : Type v} [DecidableEq X] [MulAction G X]

theorem card_eq_of_mem_copyOrbit {F J : Finset X} (hJ : J ∈ copyOrbit G F) :
    J.card = F.card := by
  obtain ⟨g, rfl⟩ := (mem_copyOrbit_iff G).mp hJ
  exact Finset.card_smul_finset _ _

/-- There are no more internal copies than subsets of the correct size. -/
theorem internalCopyCount_le_choose (I F : Finset X) :
    internalCopyCount G I F ≤ Nat.choose I.card F.card := by
  rw [← Finset.card_powersetCard F.card I]
  apply Finset.card_le_card
  intro J hJ
  obtain ⟨hcopy, hsub⟩ := Finset.mem_filter.mp hJ
  exact Finset.mem_powersetCard.mpr ⟨hsub, card_eq_of_mem_copyOrbit G hcopy⟩

/-- The exact permutation-symmetry incidence identity, including the empty set. -/
theorem containmentProb_eq_internalCopyCount (I F : Finset X) :
    containmentProb G I F = (internalCopyCount G I F : ℝ) / orbitCount G F := by
  rw [containmentProb_eq_count]
  have hI : (orbitCount G I : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr (orbitCount_pos G I))
  have hF : (orbitCount G F : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr (orbitCount_pos G F))
  have hcount : (orbitCount G F : ℝ) * containingCopyCount G I F =
      (orbitCount G I : ℝ) * internalCopyCount G I F := by
    exact_mod_cast copy_incidence_identity G I F
  apply (div_eq_div_iff hI hF).mpr
  nlinarith [hcount]

end LeanBlast.SecondKahnKalai

end

end OAI

-- ---- from OAI.Combinatorics.GraphThreshold.GraphCopies ----
namespace OAI

noncomputable section

open scoped Pointwise

namespace LeanBlast.SecondKahnKalai

variable {n : ℕ}

theorem orbitCount_eq_copyCount (S : Finset (Edge n)) :
    orbitCount (Equiv.Perm (Fin n)) S =
      (⊤ : SimpleGraph (Fin n)).copyCount (edgeSupportGraph S) := by
  classical
  calc
    orbitCount (Equiv.Perm (Fin n)) S =
        Fintype.card (OrbitCopy (Equiv.Perm (Fin n)) S) := (card_OrbitCopy _ _).symm
    _ = Fintype.card {K : (⊤ : SimpleGraph (Fin n)).Subgraph //
        Nonempty (edgeSupportGraph S ≃g K.coe)} := Fintype.card_congr (orbitSubgraphEquiv S)
    _ = _ := by
      rw [SimpleGraph.copyCount, Fintype.card_subtype]
      apply congrArg Finset.card
      ext K
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]

theorem expectedCopies_edgeSupportGraph (p : ℝ) (S : Finset (Edge n)) :
    expectedCopies n p (edgeSupportGraph S) =
      (orbitCount (Equiv.Perm (Fin n)) S : ℝ) * p ^ S.card := by
  rw [expectedCopies_formula, edgeCount_edgeSupportGraph, orbitCount_eq_copyCount]

/-- The internal orbit constraint follows from an actual subgraph constraint
of the public expectation threshold, with no multiplicity factor. -/
theorem orbit_expectation_constraint {V : Type*} (f : V ↪ Fin n)
    (H : SimpleGraph V) (q : ℝ)
    (hq : ∀ F : H.Subgraph, (1 / 2 : ℝ) ≤ expectedCopies n q F.coe)
    (S : Finset (Edge n)) (hS : S ⊆ graphEdges (H.map f)) :
    (1 / 2 : ℝ) ≤ (orbitCount (Equiv.Perm (Fin n)) S : ℝ) * q ^ S.card := by
  obtain ⟨F, ⟨e⟩⟩ := exists_subgraph_iso_edgeSupportGraph f H S hS
  rw [← expectedCopies_edgeSupportGraph, expectedCopies_iso n q e]
  exact hq F

theorem copyCount_pos_iff_orbit_subset {V : Type*} (f : V ↪ Fin n)
    (H : SimpleGraph V) (W : Finset (Edge n)) :
    0 < (graphOfEdges W).copyCount H ↔
      ∃ E ∈ copyOrbit (Equiv.Perm (Fin n)) (graphEdges (H.map f)), E ⊆ W := by
  rw [copyCount_pos_iff_exists_smul_subset f H W]
  constructor
  · rintro ⟨σ, hσ⟩
    exact ⟨_, (mem_copyOrbit_iff _).mpr ⟨σ, rfl⟩, hσ⟩
  · rintro ⟨E, hE, hEW⟩
    obtain ⟨σ, rfl⟩ := (mem_copyOrbit_iff _).mp hE
    exact ⟨σ, hEW⟩

theorem exists_graphRepresentationWithConstraints {V : Type*} [Fintype V]
    (n : ℕ) (H : SimpleGraph V) (hcard : Fintype.card V ≤ n) (q : ℝ)
    (hq : ∀ F : H.Subgraph, (1 / 2 : ℝ) ≤ expectedCopies n q F.coe) :
    ∃ E : Finset (Edge n), E.card = edgeCount H ∧
      (∀ W : Finset (Edge n),
        (0 < (graphOfEdges W).copyCount H ↔
          ∃ T ∈ copyOrbit (Equiv.Perm (Fin n)) E, T ⊆ W)) ∧
      (∀ S : Finset (Edge n), S ⊆ E →
        (1 / 2 : ℝ) ≤ (orbitCount (Equiv.Perm (Fin n)) S : ℝ) * q ^ S.card) := by
  obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le
    (show Fintype.card V ≤ Fintype.card (Fin n) by simpa using hcard)
  exact ⟨graphEdges (H.map f), card_mappedGraphEdges f H,
    copyCount_pos_iff_orbit_subset f H, orbit_expectation_constraint f H q hq⟩

end LeanBlast.SecondKahnKalai

end

end OAI

-- ---- from OAI.Combinatorics.GraphThreshold.LocalFailureNumerics ----
namespace OAI

noncomputable section

open Finset

namespace LeanBlast.SecondKahnKalai

theorem two_lt_exp_one : (2 : ℝ) < Real.exp 1 := Real.exp_one_gt_two

theorem exp_one_lt_three : Real.exp 1 < (3 : ℝ) := Real.exp_one_lt_three

/-- The strict numerical estimate used to rule out large maximizing
predecessors in the graph hierarchy. -/
theorem predecessor_power_lt_one {r : ℕ} (hr : 1 ≤ r) :
    2 * (17 * Real.exp 1 / 128) ^ r < 1 := by
  have hbase0 : 0 ≤ 17 * Real.exp 1 / 128 := by positivity
  have hbase : 17 * Real.exp 1 / 128 < (1 / 2 : ℝ) := by
    nlinarith [exp_one_lt_three]
  have hp : (17 * Real.exp 1 / 128) ^ r ≤ 17 * Real.exp 1 / 128 :=
    pow_le_of_le_one hbase0 (by linarith) (by omega)
  linarith

theorem exp_neg_fifty_lt_one : Real.exp (-50) < 1 := by
  exact Real.exp_lt_one_iff.mpr (by norm_num)

theorem one_add_le_exp_one_of_le_exp_neg_fifty {q : ℝ}
    (hq : q ≤ Real.exp (-50)) : 1 + q ≤ Real.exp 1 := by
  linarith [exp_neg_fifty_lt_one, two_lt_exp_one]

theorem one_add_pow_le_exp_nat {q : ℝ} (hq0 : 0 ≤ q)
    (hq : q ≤ Real.exp (-50)) (m : ℕ) :
    (1 + q) ^ m ≤ Real.exp (m : ℝ) := by
  calc
    (1 + q) ^ m ≤ Real.exp 1 ^ m :=
      pow_le_pow_left₀ (by positivity) (one_add_le_exp_one_of_le_exp_neg_fifty hq) m
    _ = Real.exp (m : ℝ) := by rw [← Real.exp_nat_mul]; simp

end LeanBlast.SecondKahnKalai

end

end OAI

-- ---- from OAI.Combinatorics.GraphThreshold.Predecessor ----
namespace OAI

/-!
# Maximizing predecessors

The predecessor is chosen by maximization over the actual finite powerset,
including its empty member.  The graph application uses distinct group-orbit
copies and the actual containment probability, not labeled embeddings.
-/

noncomputable section

open scoped BigOperators

namespace LeanBlast.SecondKahnKalai

theorem two_choose_div_le_predecessor_power (h r : ℕ) (hr : 0 < r)
    (hhr : h ≤ 17 * r) :
    2 * (h.choose r : ℝ) / (128 : ℝ) ^ r ≤
      2 * (17 * Real.exp 1 / 128) ^ r := by
  have hr0 : 0 < (r : ℝ) := by exact_mod_cast hr
  have hhr' : (h : ℝ) ≤ 17 * (r : ℝ) := by exact_mod_cast hhr
  have hbase : Real.exp 1 * (h : ℝ) / (r : ℝ) ≤ 17 * Real.exp 1 := by
    apply (div_le_iff₀ hr0).mpr
    calc
      Real.exp 1 * (h : ℝ) ≤ Real.exp 1 * (17 * (r : ℝ)) :=
        mul_le_mul_of_nonneg_left hhr' (Real.exp_pos 1).le
      _ = _ := by ring
  have hchoose : (h.choose r : ℝ) ≤ (17 * Real.exp 1) ^ r :=
    (choose_le_exp_div_pow h r hr).trans (pow_le_pow_left₀ (by positivity) hbase r)
  calc
    2 * (h.choose r : ℝ) / (128 : ℝ) ^ r ≤
        2 * (17 * Real.exp 1) ^ r / (128 : ℝ) ^ r :=
      div_le_div_of_nonneg_right (by nlinarith) (by positivity)
    _ = _ := by rw [div_pow]; ring

theorem two_choose_div_lt_one (h r : ℕ) (hr : 0 < r) (hhr : h ≤ 17 * r) :
    2 * (h.choose r : ℝ) / (128 : ℝ) ^ r < 1 :=
  (two_choose_div_le_predecessor_power h r hr hhr).trans_lt
    (predecessor_power_lt_one hr)

section FiniteMaximum

variable {X : Type*}

theorem maximizingSubset_subset (I : Finset X) (score : Finset X → ℝ) :
    maximizingSubset I score ⊆ I :=
  Finset.mem_powerset.mp (exists_powerset_max I score).choose_spec.1

theorem le_maximizingSubset (I : Finset X) (score : Finset X → ℝ)
    {U : Finset X} (hU : U ⊆ I) : score U ≤ score (maximizingSubset I score) :=
  (exists_powerset_max I score).choose_spec.2 U (Finset.mem_powerset.mpr hU)

end FiniteMaximum

section OrbitPredecessor

variable (G : Type*) [Group G] [Fintype G]
variable {X : Type*} [DecidableEq X] [MulAction G X]

theorem maximizingPredecessor_subset (I : Finset X) (σ : ℝ) :
    maximizingPredecessor G I σ ⊆ I :=
  maximizingSubset_subset I _

theorem predecessorScore_le_max (I : Finset X) (σ : ℝ)
    {S : Finset X} (hS : S ⊆ I) :
    predecessorScore G I σ S ≤ predecessorScore G I σ (maximizingPredecessor G I σ) :=
  le_maximizingSubset I _ hS

theorem one_le_predecessorScore_max (I : Finset X) (σ : ℝ) :
    1 ≤ predecessorScore G I σ (maximizingPredecessor G I σ) := by
  simpa using predecessorScore_le_max G I σ (Finset.empty_subset I)

theorem predecessorScore_le_two_choose {I S : Finset X} {q : ℝ}
    (hq : 0 < q)
    (hE : (1 / 2 : ℝ) ≤ (orbitCount G S : ℝ) * q ^ S.card) :
    predecessorScore G I (128 * q) S ≤
      2 * (I.card.choose S.card : ℝ) / (128 : ℝ) ^ S.card := by
  rw [predecessorScore, containmentProb_eq_internalCopyCount]
  exact normalized_count_score_bound hq (orbitCount_pos G S)
    (internalCopyCount_le_choose G I S) hE

/-- The maximizing predecessor is less than one seventeenth of the current set.
The only probabilistic input is the actual expectation constraint for its
nonempty edge subsets. -/
theorem maximizingPredecessor_small (I : Finset X) (hI : I.Nonempty)
    {q : ℝ} (hq : 0 < q)
    (hE : ∀ S : Finset X, S ⊆ I → S.Nonempty →
      (1 / 2 : ℝ) ≤ (orbitCount G S : ℝ) * q ^ S.card) :
    17 * (maximizingPredecessor G I (128 * q)).card < I.card := by
  by_contra hsmall
  have hcardI : 0 < I.card := Finset.card_pos.mpr hI
  have hlarge : I.card ≤ 17 * (maximizingPredecessor G I (128 * q)).card := by omega
  have hcardS : 0 < (maximizingPredecessor G I (128 * q)).card := by omega
  have hbound := predecessorScore_le_two_choose G (I := I) hq
    (hE _ (maximizingPredecessor_subset G I _) (Finset.card_pos.mp hcardS))
  have hlt := hbound.trans_lt (two_choose_div_lt_one I.card _ hcardS hlarge)
  have hge := one_le_predecessorScore_max G I (128 * q)
  linarith

end OrbitPredecessor

end LeanBlast.SecondKahnKalai

end

end OAI

-- ---- from OAI.Combinatorics.GraphThreshold.GraphHierarchy ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-! The finite hierarchy and the actual tree of extensions used in the graph
application. Histories are represented by the probability tree's dependent
paths; equal set labels do not identify distinct histories. -/

noncomputable section

open Finset

namespace LeanBlast.SecondKahnKalai

namespace SetHierarchy

variable {X : Type*} [DecidableEq X]
variable {R : Finset X → Finset X → Prop} {H : Finset X}

end SetHierarchy

section OrbitTrees

variable (G : Type*) [Group G] [Fintype G]
variable {X : Type} [DecidableEq X] [MulAction G X]

theorem exists_spread_orbit_tree (H : Finset X) (q : ℝ) (hq : 0 < q)
    (hH : H.Nonempty)
    (hE : ∀ U : Finset X, U ⊆ H → U.Nonempty →
      (1 / 2 : ℝ) ≤ (orbitCount G U : ℝ) * q ^ U.card) :
    ∃ k : ℕ, ∃ m : ℕ → ℕ, ∃ T : ProbabilityTree X k,
      0 < k ∧ T.IsDisjoint ∧ T.HasCapacities m ∧
      T.HasSpread (fun _ => 128 * q) ∧
      (∀ i, i < k → 0 < m i) ∧
      (∀ i, i + 1 < k → 16 * m i ≤ m (i + 1)) ∧
      m (k - 1) ≤ H.card ∧
      ∀ p : T.Path, T.pathUnion p ∈ copyOrbit G H := by
  apply exists_spread_orbit_tree_of_predecessors G H hH (128 * q) (by positivity)
    (fun S I => S = maximizingPredecessor G I (128 * q))
  · intro I hIH hI
    refine ⟨maximizingPredecessor G I (128 * q),
      maximizingPredecessor_subset G I (128 * q), ?_, rfl⟩
    exact maximizingPredecessor_small G I hI hq
      (fun U hUI hU => hE U (hUI.trans hIH) hU)
  · intro I _ S hS S0 hS0 J _ hd
    subst S
    exact predecessor_conditional_ratio_le G I (by positivity) hS0 hd

end OrbitTrees

end LeanBlast.SecondKahnKalai

end

end OAI

-- ---- from OAI.Combinatorics.GraphThreshold.BernoulliMonotonicity ----
namespace OAI

/-!
# Monotonicity of finite Bernoulli probabilities

For `p ≤ q`, adjoin an independent Bernoulli set to a Bernoulli-`p` set.
The resulting union has parameter `q` and contains the first set. This gives
expectation and event monotonicity, including both endpoints of `[0, 1]`.
-/

noncomputable section
attribute [local instance] Classical.propDecidable

namespace LeanBlast.SecondKahnKalai

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- Inclusion-monotone events become more likely as the Bernoulli parameter
increases. The proof couples actual independent finite Bernoulli sets. -/
theorem bernoulliProbability_mono_parameter {p q : ℝ}
    (hp0 : 0 ≤ p) (hpq : p ≤ q) (hq1 : q ≤ 1) (P : Finset X → Prop)
    (hP : ∀ U V, U ⊆ V → P U → P V) :
    bernoulliProbability p P ≤ bernoulliProbability q P := by
  rw [bernoulliProbability_eq_expectation, bernoulliProbability_eq_expectation]
  apply bernoulliExpectation_mono_parameter hp0 hpq hq1
  intro U V hUV
  by_cases hu : P U
  · simp [hu, hP U V hUV hu]
  · by_cases hv : P V <;> simp [hu, hv]

end LeanBlast.SecondKahnKalai

end

end OAI

-- ---- from OAI.Combinatorics.GraphThreshold.ProbabilityTreeFacts ----
namespace OAI

/-! Path and locality facts for the stable finite probability-tree representation. -/

noncomputable section

namespace LeanBlast.SecondKahnKalai

section Locality

variable {X β : Type*} [DecidableEq X] {S T A : Finset X} {f : Finset X → β}

theorem DependsOnlyOn.dependsOutside (hf : DependsOnlyOn S f) (hAS : Disjoint A S) :
    DependsOutside A f := by
  intro W V hWV
  apply hf W V
  apply Finset.ext
  intro x
  by_cases hx : x ∈ S
  · have hxA : x ∉ A := fun hxA => Finset.disjoint_left.mp hAS hxA hx
    have he := Finset.ext_iff.mp hWV x
    simpa [hx, hxA] using he
  · simp [hx]

end Locality

namespace ProbabilityTree

variable {X : Type}

section Labels

variable [DecidableEq X]

theorem child_dependsOutside {d : ℕ} {B : Type} [Fintype B]
    {law : FiniteLaw B} {positive : law.IsPositive} {label : B → Finset X}
    {child : B → ProbabilityTree X d}
    (hT : (node B law positive label child).IsDisjoint) (b : B)
    {β : Type*} {f : Finset X → β} (hf : DependsOnlyOn (child b).support f) :
    DependsOutside (label b) f :=
  hf.dependsOutside (hT.1 b)

end Labels

end ProbabilityTree

end LeanBlast.SecondKahnKalai

end

end OAI

-- ---- from OAI.Combinatorics.GraphThreshold.CapacityIteration ----
-- Lean 4.34 name of Finset.prod_le_prod_of_subset_of_le_one (ordered-semiring version) in Mathlib 0df444a.
-- Lean 4.34 name, proved using the Mathlib 0df444a lemma (same statement).
private abbrev Finset.prod_le_one₀ := @Finset.prod_le_one

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-!
# Capacities and finite inflation products

The capacity after `t` successful reductions is natural-number division by
`2^t`. All product estimates below are finite; no infinite product is used.
-/

noncomputable section

open Finset Set

namespace LeanBlast.SecondKahnKalai

theorem retentionFactor_pos {m : ℕ} (hm : 0 < m) :
    0 < 1 - Real.exp (-(m : ℝ)) := by
  apply sub_pos.mpr
  rw [Real.exp_lt_one_iff]
  exact neg_neg_of_pos (by exact_mod_cast hm)

theorem retentionFactor_le_one (m : ℕ) :
    1 - Real.exp (-(m : ℝ)) ≤ 1 := sub_le_self _ (Real.exp_pos _).le

theorem capacityReserve_pos {σ : ℝ} (hσ : 0 < σ) (m : ℕ) :
    0 < capacityReserve σ m := by
  apply mul_pos (mul_pos (by norm_num) hσ)
  apply Finset.prod_pos
  intro j hj
  exact retentionFactor_pos (Finset.mem_Icc.mp hj).1

theorem capacityReserve_upper {σ : ℝ} (hσ : 0 ≤ σ) (m : ℕ) :
    capacityReserve σ m ≤ 4 * σ := by
  have hp : (∏ j ∈ Finset.Icc 1 m, (1 - Real.exp (-(j : ℝ)))) ≤ 1 := by
    apply Finset.prod_le_one₀
    · intro j hj
      exact (retentionFactor_pos (Finset.mem_Icc.mp hj).1).le
    · intro j _
      exact retentionFactor_le_one j
  have hm := mul_le_mul_of_nonneg_left hp (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hσ)
  simpa only [capacityReserve, mul_one] using hm

end LeanBlast.SecondKahnKalai

end

end OAI

-- ---- from OAI.Combinatorics.GraphThreshold.TreeReductionData ----
namespace OAI

/-! Fixed-input local masses and the deterministic good-node predicate. -/

noncomputable section
open scoped BigOperators
open Classical

namespace LeanBlast.SecondKahnKalai

section LocalMasses

variable {X B : Type*} [DecidableEq X] [Fintype B]

theorem localFailureMass_nonneg (μ : FiniteLaw B) (A : B → Finset X)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (m : ℕ) (W : Finset X) :
    0 ≤ localFailureMass μ A ρ m W := by
  apply Finset.sum_nonneg
  intro b _
  apply Finset.sum_nonneg
  intro c _
  split_ifs
  · exact resamplingWeight_nonneg μ A hρ W (c, b)
  · exact le_rfl

end LocalMasses

variable {X : Type} [DecidableEq X]

end LeanBlast.SecondKahnKalai

end

end OAI

-- ---- from OAI.Combinatorics.GraphThreshold.SpreadCounting ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

/-! Exact intersection counting for a finite, weighted spread family.

No injectivity of the label map and no strict positivity of individual weights
is required. The fixed target is an arbitrary finite set, and may be empty.
-/

noncomputable section

open scoped BigOperators

namespace LeanBlast.SecondKahnKalai

variable {X B : Type*} [DecidableEq X] [Fintype B]

/-- The spread bound also holds for the empty test set, by normalization. -/
theorem IsSpread.containment_le {μ : FiniteLaw B} {A : B → Finset X} {a : ℝ}
    (hs : IsSpread μ A a) (J : Finset X) :
    μ.prob (fun c => J ⊆ A c) ≤ a ^ J.card := by
  classical
  by_cases hJ : J.Nonempty
  · exact hs J hJ
  · have hJ' : J = ∅ := Finset.not_nonempty_iff_eq_empty.mp hJ
    simp [hJ', FiniteLaw.prob, μ.total]

/-- Exact binomial count of potential witnesses bounds the intersection tail. -/
theorem intersection_card_ge_le_target {μ : FiniteLaw B} {A : B → Finset X}
    {a : ℝ} (hs : IsSpread μ A a) (T : Finset X) (r : ℕ) :
    μ.prob (fun c => r ≤ (A c ∩ T).card) ≤
      (T.card.choose r : ℝ) * a ^ r := by
  classical
  calc
    μ.prob (fun c => r ≤ (A c ∩ T).card) ≤
        ∑ J ∈ T.powersetCard r, μ.prob (fun c => J ⊆ A c) :=
      intersection_card_ge_le_subsets μ A T r
    _ ≤ ∑ J ∈ T.powersetCard r, a ^ r := by
      apply Finset.sum_le_sum
      intro J hJ
      simpa [(Finset.mem_powersetCard.mp hJ).2] using hs.containment_le J
    _ = (T.card.choose r : ℝ) * a ^ r := by simp

/-- Uniform capacity version, including `r = 0` and empty target sets. -/
theorem intersection_card_ge_le {μ : FiniteLaw B} {A : B → Finset X}
    {a : ℝ} (hs : IsSpread μ A a) (ha : 0 ≤ a) {m : ℕ}
    {T : Finset X} (hT : T.card ≤ m) (r : ℕ) :
    μ.prob (fun c => r ≤ (A c ∩ T).card) ≤
      (m.choose r : ℝ) * a ^ r := by
  apply (intersection_card_ge_le_target hs T r).trans
  apply mul_le_mul_of_nonneg_right _ (pow_nonneg ha r)
  exact_mod_cast Nat.choose_le_choose r hT

/-- The exact intersection histogram is bounded by the same binomial count. -/
theorem intersection_card_eq_le {μ : FiniteLaw B} {A : B → Finset X}
    {a : ℝ} (hs : IsSpread μ A a) (ha : 0 ≤ a) {m : ℕ}
    {T : Finset X} (hT : T.card ≤ m) (r : ℕ) :
    μ.prob (fun c => (A c ∩ T).card = r) ≤
      (m.choose r : ℝ) * a ^ r := by
  classical
  apply le_trans _ (intersection_card_ge_le hs ha hT r)
  unfold FiniteLaw.prob
  apply Finset.sum_le_sum
  intro c hc
  by_cases hcr : (A c ∩ T).card = r
  · simp [hcr]
  · simp only [ite_eq_right hcr]
    split_ifs <;> first | exact μ.nonneg c | exact le_rfl

/-- Any nonnegative function of the intersection admits a binomial majorant. -/
theorem expectation_intersection_le_binomial {μ : FiniteLaw B} {A : B → Finset X}
    {a : ℝ} (hs : IsSpread μ A a) (ha : 0 ≤ a) {m : ℕ}
    {T : Finset X} (hT : T.card ≤ m) (g : ℕ → ℝ) (hg : ∀ r, 0 ≤ g r) :
    μ.expectation (fun c => g (A c ∩ T).card) ≤
      ∑ r ∈ Finset.range (m + 1), (m.choose r : ℝ) * a ^ r * g r := by
  rw [expectation_intersection_eq_sum μ A hT g]
  exact Finset.sum_le_sum fun r _ =>
    mul_le_mul_of_nonneg_right (intersection_card_eq_le hs ha hT r) (hg r)

/-- The full generating-function bound needs only a nonnegative argument. -/
theorem intersection_moment_le {μ : FiniteLaw B} {A : B → Finset X}
    {a : ℝ} (hs : IsSpread μ A a) (ha : 0 ≤ a) {m : ℕ}
    {T : Finset X} (hT : T.card ≤ m) {t : ℝ} (ht : 0 ≤ t) :
    μ.expectation (fun c => t ^ (A c ∩ T).card) ≤ (1 + a * t) ^ m := by
  calc
    _ ≤ ∑ r ∈ Finset.range (m + 1), (m.choose r : ℝ) * a ^ r * t ^ r :=
      expectation_intersection_le_binomial hs ha hT _ (fun r => pow_nonneg ht r)
    _ = (1 + a * t) ^ m := by
      rw [add_comm 1 (a * t), add_pow]
      apply Finset.sum_congr rfl
      intro r hr
      simp only [one_pow, mul_one, mul_pow]
      ring

/-- Inverse-parameter moment used by the resampling density estimate. -/
theorem intersection_inverse_moment_le {μ : FiniteLaw B} {A : B → Finset X}
    {a : ℝ} (hs : IsSpread μ A a) (ha : 0 ≤ a) {m : ℕ}
    {T : Finset X} (hT : T.card ≤ m) {ρ : ℝ} (hρ : 0 < ρ) :
    μ.expectation (fun c => (ρ⁻¹) ^ (A c ∩ T).card) ≤ (1 + a / ρ) ^ m := by
  simpa only [div_eq_mul_inv] using
    intersection_moment_le hs ha hT (inv_nonneg.mpr hρ.le)

end LeanBlast.SecondKahnKalai

end

end OAI

-- ---- from OAI.Combinatorics.GraphThreshold.OutsideChangeOfMeasure ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-!
# Outside-coordinate change of measure for the actual resampling transition

The observable may depend on the same Bernoulli set used at every other tree
node.  The only locality required here is that it ignores the fixed target's
incoming label.  No independence between different tree nodes is assumed.
-/

noncomputable section

open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace LeanBlast.SecondKahnKalai

variable {X B : Type*} [DecidableEq X] [Fintype B]

variable [Fintype X]

theorem outside_change_of_measure (ν : FiniteLaw B) (A : B → Finset X)
    {p a : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) (ha : 0 ≤ a)
    (hs : IsSpread ν A a) (m : ℕ) (b : B) (hAb : (A b).card ≤ m)
    (hsmall : a / p ≤ Real.exp (-50))
    (f : Finset X → ℝ) (hf : ∀ W, 0 ≤ f W) (hloc : DependsOutside (A b) f) :
    bernoulliExpectation p (fun W =>
      cutoffTargetMass ν A p (Real.exp (-10 * (m : ℝ))) W b * f W) ≤
      Real.exp (11 * (m : ℝ)) * ν.weight b * bernoulliExpectation p f := by
  have hEf : 0 ≤ bernoulliExpectation p f :=
    (bernoulliLaw (X := X) p hp.le hp1).expectation_nonneg hf
  have hmoment : ν.expectation (fun c => (p⁻¹) ^ (A c ∩ A b).card) ≤
      Real.exp (m : ℝ) :=
    (intersection_inverse_moment_le hs ha hAb hp).trans
      (one_add_pow_le_exp_nat (div_nonneg ha hp.le) hsmall m)
  have hcoef : 0 ≤ (Real.exp (-10 * (m : ℝ)))⁻¹ * ν.weight b *
      bernoulliExpectation p f :=
    mul_nonneg (mul_nonneg (inv_nonneg.mpr (Real.exp_pos _).le) (ν.nonneg b)) hEf
  have he : (Real.exp (-10 * (m : ℝ)))⁻¹ * Real.exp (m : ℝ) =
      Real.exp (11 * (m : ℝ)) := by
    rw [← Real.exp_neg, ← Real.exp_add]
    congr 1
    ring
  calc
    bernoulliExpectation p (fun W =>
        cutoffTargetMass ν A p (Real.exp (-10 * (m : ℝ))) W b * f W) ≤
        (Real.exp (-10 * (m : ℝ)))⁻¹ * ν.weight b * bernoulliExpectation p f *
          ν.expectation (fun c => (p⁻¹) ^ (A c ∩ A b).card) :=
      outside_change_of_measure_moment ν A hp hp1 (Real.exp_pos _) b f hf hloc
    _ ≤ (Real.exp (-10 * (m : ℝ)))⁻¹ * ν.weight b * bernoulliExpectation p f *
        Real.exp (m : ℝ) := mul_le_mul_of_nonneg_left hmoment hcoef
    _ = ((Real.exp (-10 * (m : ℝ)))⁻¹ * Real.exp (m : ℝ)) * ν.weight b *
        bernoulliExpectation p f := by ring
    _ = _ := by rw [he]

/-- Any smaller target mass, including local non-failure, obeys the same bound. -/
theorem outside_change_of_measure_of_le (ν : FiniteLaw B) (A : B → Finset X)
    {p a : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) (ha : 0 ≤ a)
    (hs : IsSpread ν A a) (m : ℕ) (b : B) (hAb : (A b).card ≤ m)
    (hsmall : a / p ≤ Real.exp (-50))
    (f : Finset X → ℝ) (hf : ∀ W, 0 ≤ f W) (hloc : DependsOutside (A b) f)
    (t : Finset X → ℝ)
    (ht : ∀ W, t W ≤ cutoffTargetMass ν A p (Real.exp (-10 * (m : ℝ))) W b) :
    bernoulliExpectation p (fun W => t W * f W) ≤
      Real.exp (11 * (m : ℝ)) * ν.weight b * bernoulliExpectation p f := by
  have hm : bernoulliExpectation p (fun W => t W * f W) ≤
      bernoulliExpectation p (fun W =>
        cutoffTargetMass ν A p (Real.exp (-10 * (m : ℝ))) W b * f W) :=
    (bernoulliLaw (X := X) p hp.le hp1).expectation_mono
      (fun W => mul_le_mul_of_nonneg_right (ht W) (hf W))
  exact hm.trans (outside_change_of_measure ν A hp hp1 ha hs m b hAb hsmall f hf hloc)

end LeanBlast.SecondKahnKalai

end

end OAI

-- ---- from OAI.Combinatorics.GraphThreshold.TreePotential ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
namespace OAI

/-!
# The bad-node potential for simultaneous tree reduction

All nodes in a reduction use the same random set. The expectation argument
uses an outside-coordinate change of measure, rather than independence of
node outcomes.
-/

noncomputable section

open scoped BigOperators
open Classical

namespace LeanBlast.SecondKahnKalai

theorem nodePotential_nonneg {B : Type*} [Fintype B] (m : ℕ) (failure : ℝ)
    (target childPotential : B → ℝ) (hf : 0 ≤ failure)
    (ht : ∀ b, 0 ≤ target b) (hc : ∀ b, 0 ≤ childPotential b) :
    0 ≤ nodePotential m failure target childPotential := by
  exact div_nonneg (add_nonneg hf (Finset.sum_nonneg (fun b _ => mul_nonneg (ht b) (hc b))))
    (Real.exp_pos _).le

theorem potentialEnvelope_eq_sum (d : ℕ) (m : ℕ → ℕ) :
    potentialEnvelope d m =
      ∑ j ∈ Finset.range d,
        Real.exp (12 * (∑ h ∈ Finset.range j, (m h : ℝ)) - 8 * (m j : ℝ)) := by
  induction d generalizing m with
  | zero => simp [potentialEnvelope]
  | succ d ih =>
    rw [potentialEnvelope, ih, Finset.sum_range_succ']
    simp only [Finset.range_zero, Finset.sum_empty, mul_zero, zero_sub, neg_mul]
    rw [Finset.mul_sum]
    rw [add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [← Real.exp_add, Finset.sum_range_succ']
    congr 1
    ring

section Trees

variable {X : Type} [Fintype X] [DecidableEq X]

omit [Fintype X] in
theorem treePotential_nonneg {p : ℝ} (hp : 0 ≤ p) (m : ℕ → ℕ) (W : Finset X)
    {d : ℕ} (T : ProbabilityTree X d) : 0 ≤ treePotential p m W T := by
  induction T generalizing m with
  | leaf => simp only [treePotential, le_refl]
  | @node d B inst ν hν A child ih =>
      simp only [treePotential]
      exact nodePotential_nonneg (m 0) _ _ _ (localFailureMass_nonneg ν A hp (m 0) W)
        (fun b => successfulTargetMass_nonneg ν A hp (m 0) W b)
        (fun b => ih b (fun j => m (j + 1)))

omit [Fintype X] in
theorem one_lt_treePotential_of_not_good {p : ℝ} (hp : 0 < p) (m : ℕ → ℕ)
    (W : Finset X) {d : ℕ} (T : ProbabilityTree X d) (hbad : ¬Good p m W T) :
    1 < treePotential p m W T := by
  induction T generalizing m with
  | leaf => simp only [Good, not_true_eq_false] at hbad
  | @node d B inst ν hν A child ih =>
      simp only [treePotential]
      simp only [Good] at hbad
      apply one_lt_nodePotential_of_bad (m 0) _ _ _
        (fun b => Good p (fun j => m (j + 1)) W (child b))
      · exact fun b => successfulTargetMass_nonneg ν A hp.le _ W b
      · exact fun b => treePotential_nonneg hp.le _ W (child b)
      · exact localFailureMass_add_successfulTargetMass ν A hν hp (m 0) W
      · exact fun b hb => ih b _ hb
      · exact lt_of_not_ge hbad

omit [Fintype X] in
/-- Path disjointness makes a descendant potential insensitive to its
incoming label; this is the locality needed by the change of measure. -/
theorem child_treePotential_dependsOutside {d : ℕ} {B : Type} [Fintype B]
    (ν : FiniteLaw B) (hν : ν.IsPositive) (A : B → Finset X)
    (child : B → ProbabilityTree X d)
    (hdis : (ProbabilityTree.node B ν hν A child).IsDisjoint)
    (p : ℝ) (m : ℕ → ℕ) (b : B) :
    DependsOutside (A b) (fun W => treePotential p m W (child b)) :=
  ProbabilityTree.child_dependsOutside hdis b (treePotential_dependsOnlyOn p m (child b))

theorem bad_probability_le_expected_treePotential {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1)
    (m : ℕ → ℕ) {d : ℕ} (T : ProbabilityTree X d) :
    bernoulliProbability p (fun W => ¬Good p m W T) ≤
      bernoulliExpectation p (fun W => treePotential p m W T) := by
  exact (bernoulliLaw p hp.le hp1).prob_le_expectation (fun W => ¬Good p m W T)
    (fun W => treePotential p m W T) (fun W => treePotential_nonneg hp.le m W T)
    (fun W hW => (one_lt_treePotential_of_not_good hp m W T hW).le)

omit [Fintype X] in
private theorem localFailureMass_eq_probability {B : Type} [Fintype B]
    (ν : FiniteLaw B) (hν : ν.IsPositive) (A : B → Finset X)
    {p : ℝ} (hp : 0 < p) (m : ℕ) (W : Finset X) :
    localFailureMass ν A p m W =
      (resamplingLaw ν A p W hν hp).prob (fun cb => LocalFailure ν A p m W cb.1 cb.2) := by
  simp only [localFailureMass, FiniteLaw.prob, resamplingLaw_weight, Fintype.sum_prod_type]
  exact Finset.sum_comm

omit [Fintype X] in
theorem successfulTargetMass_le_cutoff {B : Type} [Fintype B]
    (ν : FiniteLaw B) (A : B → Finset X) {p : ℝ} (hp : 0 ≤ p)
    (m : ℕ) (W : Finset X) (b : B) :
    successfulTargetMass ν A p m W b ≤
      cutoffTargetMass ν A p (Real.exp (-10 * (m : ℝ))) W b := by
  unfold successfulTargetMass cutoffTargetMass
  apply Finset.sum_le_sum
  intro c _
  by_cases hsuccess : LocalSuccess ν A p m W c b
  · have hcut : Real.exp (-10 * (m : ℝ)) ≤ resamplingZ ν A p (resamplingY A W c) :=
      hsuccess.1
    simp only [ite_eq_left hsuccess, ite_eq_left hcut, le_refl]
  · simp only [ite_eq_right hsuccess]
    split_ifs
    · exact resamplingWeight_nonneg ν A hp W (c, b)
    · exact le_rfl

theorem treePotential_expectation_node_le {d : ℕ} {B : Type} [Fintype B]
    (ν : FiniteLaw B) (hν : ν.IsPositive) (A : B → Finset X)
    (child : B → ProbabilityTree X d) (m : ℕ → ℕ)
    {p a : ℝ} (hp : 0 < p) (hp1 : p < 1) (ha : 0 ≤ a)
    (hspread : IsSpread ν A a) (hm : 1 ≤ m 0)
    (hsize : ∀ b, (A b).card ≤ m 0) (hsmall : a / p ≤ Real.exp (-50))
    (hdis : (ProbabilityTree.node B ν hν A child).IsDisjoint) :
    bernoulliExpectation p (fun W => treePotential p m W (ProbabilityTree.node B ν hν A child)) ≤
      Real.exp (-8 * (m 0 : ℝ)) + Real.exp (12 * (m 0 : ℝ)) *
        ν.expectation (fun b => bernoulliExpectation p
          (fun W => treePotential p (fun j => m (j + 1)) W (child b))) := by
  simp only [treePotential]
  apply bernoulliExpectation_nodePotential_le p (m 0) ν
  · have h := local_failure_bound ν A hν hp hp1 (m 0) hm hsize hspread ha hsmall
    simpa only [← localFailureMass_eq_probability ν hν A hp (m 0)] using h
  · intro b
    exact outside_change_of_measure_of_le ν A hp hp1.le ha hspread (m 0) b (hsize b) hsmall
      (fun W => treePotential p (fun j => m (j + 1)) W (child b))
      (fun W => treePotential_nonneg hp.le _ W (child b))
      (child_treePotential_dependsOutside ν hν A child hdis p _ b)
      (fun W => successfulTargetMass ν A p (m 0) W b)
      (fun W => successfulTargetMass_le_cutoff ν A hp.le (m 0) W b)

theorem treePotential_expectation_le {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (m : ℕ → ℕ) (a : ℕ → ℝ) {d : ℕ} (T : ProbabilityTree X d)
    (hdis : T.IsDisjoint) (hcap : T.HasCapacities m) (hspread : T.HasSpread a)
    (hm : ∀ j, j < d → 1 ≤ m j) (ha : ∀ j, j < d → 0 ≤ a j)
    (hsmall : ∀ j, j < d → a j / p ≤ Real.exp (-50)) :
    bernoulliExpectation p (fun W => treePotential p m W T) ≤ potentialEnvelope d m := by
  induction T generalizing m a with
  | leaf => simp [treePotential, potentialEnvelope, bernoulliExpectation]
  | @node d B inst ν hν A child ih =>
      have hnode := treePotential_expectation_node_le ν hν A child m hp hp1
        (ha 0 (by omega)) hspread.1 (hm 0 (by omega)) hcap.1 (hsmall 0 (by omega)) hdis
      have hchild (b : B) : bernoulliExpectation p
          (fun W => treePotential p (fun j => m (j + 1)) W (child b)) ≤
          potentialEnvelope d (fun j => m (j + 1)) := by
        apply ih b (fun j => m (j + 1)) (fun j => a (j + 1)) (hdis.2 b) (hcap.2 b) (hspread.2 b)
        · intro j hj
          exact hm (j + 1) (by omega)
        · intro j hj
          exact ha (j + 1) (by omega)
        · intro j hj
          exact hsmall (j + 1) (by omega)
      have havg : ν.expectation (fun b => bernoulliExpectation p
          (fun W => treePotential p (fun j => m (j + 1)) W (child b))) ≤
          potentialEnvelope d (fun j => m (j + 1)) := by
        unfold FiniteLaw.expectation
        calc
          _ ≤ ∑ b, ν.weight b * potentialEnvelope d (fun j => m (j + 1)) :=
            Finset.sum_le_sum (fun b _ => mul_le_mul_of_nonneg_left (hchild b) (ν.nonneg b))
          _ = _ := by rw [← Finset.sum_mul, ν.total, one_mul]
      exact hnode.trans (add_le_add le_rfl
        (mul_le_mul_of_nonneg_left havg (Real.exp_pos _).le))

/-- One simultaneous reduction fails with probability strictly below one
quarter under the geometric level-capacity assumptions. -/
theorem root_bad_probability_lt_one_quarter {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (m : ℕ → ℕ) (a : ℕ → ℝ) {d : ℕ} (T : ProbabilityTree X d)
    (hdis : T.IsDisjoint) (hcap : T.HasCapacities m) (hspread : T.HasSpread a)
    (hm : ∀ j, j < d → 1 ≤ m j) (ha : ∀ j, j < d → 0 ≤ a j)
    (hsmall : ∀ j, j < d → a j / p ≤ Real.exp (-50))
    (hgrowth : ∀ j, j + 1 < d → 16 * m j ≤ m (j + 1)) :
    bernoulliProbability p (fun W => ¬Good p m W T) < 1 / 4 := by
  have hbound := (bad_probability_le_expected_treePotential hp hp1.le m T).trans
    (treePotential_expectation_le hp hp1 m a T hdis hcap hspread hm ha hsmall)
  rw [potentialEnvelope_eq_sum] at hbound
  exact hbound.trans_lt (capacity_failure_sum_lt_one_quarter m d hm hgrowth)

theorem reduction_good_probability_ge {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (m : ℕ → ℕ) (a : ℕ → ℝ) {d : ℕ} (T : ProbabilityTree X d)
    (hdis : T.IsDisjoint) (hcap : T.HasCapacities m) (hspread : T.HasSpread a)
    (hm : ∀ j, j < d → 1 ≤ m j) (ha : ∀ j, j < d → 0 ≤ a j)
    (hsmall : ∀ j, j < d → a j / p ≤ Real.exp (-50))
    (hgrowth : ∀ j, j + 1 < d → 16 * m j ≤ m (j + 1)) :
    3 / 4 ≤ bernoulliProbability p (fun W => Good p m W T) := by
  have hbad := root_bad_probability_lt_one_quarter hp hp1 m a T
    hdis hcap hspread hm ha hsmall hgrowth
  have hcompl := (bernoulliLaw (X := X) p hp.le hp1.le).prob_compl (fun W => Good p m W T)
  change bernoulliProbability p (fun W => ¬Good p m W T) =
    1 - bernoulliProbability p (fun W => Good p m W T) at hcompl
  linarith

end Trees

end LeanBlast.SecondKahnKalai

end

end OAI

-- ---- from OAI.Combinatorics.GraphThreshold.TreeCovering ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-!
# Covering a probability tree by iterative reductions

Recovery keeps the original and retained path histories distinct, even when
their labels agree. All draws are retained in the accumulating union.
-/

noncomputable section
open Classical

namespace LeanBlast.SecondKahnKalai

theorem capacityReserve_div_sampling_le {σ : ℝ} (hσ : 0 < σ) (m : ℕ) :
    capacityReserve σ m / (Real.exp 50 * (4 * σ)) ≤ Real.exp (-50) := by
  have hp : 0 < Real.exp 50 * (4 * σ) := by positivity
  calc
    _ ≤ (4 * σ) / (Real.exp 50 * (4 * σ)) :=
      div_le_div_of_nonneg_right (capacityReserve_upper hσ.le m) hp.le
    _ = Real.exp (-50) := by
      rw [Real.exp_neg]
      field_simp

namespace ProbabilityTree

variable {X : Type} [DecidableEq X]

namespace CoverState

variable {k : ℕ} {original : ProbabilityTree X k} {σ : ℝ}

end CoverState

end ProbabilityTree

theorem tree_covering {X : Type} [Fintype X] [DecidableEq X] {k : ℕ}
    (T : ProbabilityTree X k) (hk : 0 < k) (hdis : T.IsDisjoint)
    (m : ℕ → ℕ) (hcap : T.HasCapacities m) (hpos : ∀ i, i < k → 0 < m i)
    (hgrowth : ∀ i, i + 1 < k → 16 * m i ≤ m (i + 1))
    (σ : ℝ) (hσ : 0 < σ) (hspread : T.HasSpread (fun _ => σ)) :
    (2 / 3 : ℝ) ≤ bernoulliProbability
      (min 1 (16 * Real.exp 50 * σ * (1 + Real.logb 2 (m (k - 1) : ℝ)))) T.CoveredBy := by
  apply tree_covering_of_progress T hk hdis m hcap hpos hgrowth σ hσ hspread
  intro hp1 state hrank
  have hp : 0 < Real.exp 50 * (4 * σ) := by positivity
  have hgood := reduction_good_probability_ge hp hp1 state.capacity
    (fun i => capacityReserve σ (state.capacity i)) state.tree
    state.disjoint state.capacities state.spread state.positive
    (fun i _ => (capacityReserve_pos hσ (state.capacity i)).le)
    (fun i _ => capacityReserve_div_sampling_le hσ (state.capacity i)) state.growth
  have hmono := (bernoulliLaw (X := X) (Real.exp 50 * (4 * σ)) hp.le hp1.le).prob_mono
    (P := fun W => Good (Real.exp 50 * (4 * σ)) state.capacity W state.tree)
    (Q := fun W => ∃ next, state.Advances W next)
    (fun W hW => state.exists_advance_of_good W hσ hp hrank hW)
  exact hgood.trans hmono

end LeanBlast.SecondKahnKalai

end

end OAI

-- ---- from OAI.Combinatorics.GraphThreshold.Main ----
namespace OAI

/-!
# The second Kahn–Kalai graph-threshold bounds

The graph-to-orbit bridge counts actual unlabelled subgraphs.  The hierarchy is
constructed from the constraints at the attained expectation threshold, and
covering one of its paths yields a copy of the original graph.
-/

noncomputable section

namespace LeanBlast.SecondKahnKalai

universe u

theorem secondKahnKalaiBounds (n : ℕ) (V : Type u) [Fintype V]
    (H : SimpleGraph V) (hn : 2 ≤ n) (hcard : Fintype.card V ≤ n)
    (hedge : 1 ≤ edgeCount H) : SecondKahnKalaiBounds n H := by
  classical
  let q := expectationThreshold n H
  have hq : 0 < q := expectationThreshold_pos n H hcard hedge
  obtain ⟨E, hEcard, hEevent, hEconstraint⟩ :=
    exists_graphRepresentationWithConstraints n H hcard q
      (expectationThreshold_attained n H hcard).2
  have hEnonempty : E.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨k, m, T, hk, hdisjoint, hcapacity, hspread, hpositive, hgrowth, hlast, hpath⟩ :=
    exists_spread_orbit_tree (Equiv.Perm (Fin n)) E q hq hEnonempty
      (fun S hS _ => hEconstraint S hS)
  have hm : 0 < m (k - 1) := hpositive (k - 1) (by omega)
  have hmh : m (k - 1) ≤ edgeCount H := by omega
  let p := min 1 (2048 * Real.exp 50 * q * (1 + logTwo (edgeCount H : ℝ)))
  let pTree := min 1 (16 * Real.exp 50 * (128 * q) *
    (1 + Real.logb 2 (m (k - 1) : ℝ)))
  have hp : p ∈ Set.Icc 0 1 := graphThresholdParameter_mem_unitInterval q _ hq.le hedge
  have hpTree : pTree ∈ Set.Icc 0 1 := treeSamplingParameter_mem_unitInterval q _ hq.le hm
  have hpTree_le : pTree ≤ p :=
    treeSamplingParameter_le_graphParameter q _ _ hq.le hm hmh
  have hcovered : (2 / 3 : ℝ) ≤ bernoulliProbability pTree T.CoveredBy :=
    tree_covering T hk hdisjoint m hcapacity hpositive hgrowth (128 * q)
      (by positivity) hspread
  have hincrease : bernoulliProbability pTree T.CoveredBy ≤
      bernoulliProbability p T.CoveredBy := by
    apply bernoulliProbability_mono_parameter hpTree.1 hpTree_le hp.2 T.CoveredBy
    rintro W W' hWW' ⟨path, hpathW⟩
    exact ⟨path, hpathW.trans hWW'⟩
  have hevent : bernoulliProbability p T.CoveredBy ≤ containmentProbability n p H := by
    change (bernoulliLaw p hp.1 hp.2).prob T.CoveredBy ≤
      (bernoulliLaw p hp.1 hp.2).prob (fun W => 0 < (graphOfEdges W).copyCount H)
    apply FiniteLaw.prob_mono
    rintro W ⟨path, hpathW⟩
    exact (hEevent W).mpr ⟨T.pathUnion path, hpath path, hpathW⟩
  have hpc : criticalThreshold n H ≤ p := by
    apply criticalThreshold_le_of_probability n H hp
    exact (by norm_num : (1 / 2 : ℝ) ≤ 2 / 3).trans
      (hcovered.trans (hincrease.trans hevent))
  exact ⟨hpc, hpc.trans (graphThresholdParameter_le_vertexBound n H q hn hcard hedge hq.le)⟩

end LeanBlast.SecondKahnKalai

end

end OAI

-- ---- mission target ----
open OAI OAI.LeanBlast OAI.LeanBlast.SecondKahnKalai
universe u

namespace OAI
namespace LeanBlast.SecondKahnKalai
theorem _root_.solution (n : ℕ) (V : Type u) [Fintype V]
    (H : SimpleGraph V) (hn : 2 ≤ n) (hcard : Fintype.card V ≤ n)
    (hedge : 1 ≤ edgeCount H) : SecondKahnKalaiBounds n H := by
  first
    | exact OAI.LeanBlast.SecondKahnKalai.secondKahnKalaiBounds n V H hn hcard hedge
    | exact OAI.LeanBlast.SecondKahnKalai.secondKahnKalaiBounds
    | (apply OAI.LeanBlast.SecondKahnKalai.secondKahnKalaiBounds <;> assumption)
    | (intros; apply OAI.LeanBlast.SecondKahnKalai.secondKahnKalaiBounds <;> assumption)
end LeanBlast.SecondKahnKalai
end OAI
