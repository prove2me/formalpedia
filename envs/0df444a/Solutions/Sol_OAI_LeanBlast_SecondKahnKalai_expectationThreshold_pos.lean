-- Prove2me | solution 1 for OAI.LeanBlast.SecondKahnKalai.expectationThreshold_pos
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T02:16:18.915235+00:00
-- url     : https://prove2.me/submissions/53a939bc-21cd-492c-b1b2-fc66d8058c4d

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/GraphThreshold/Thresholds.lean:L167-L188
-- (upload_full_project.md Phase 4): solution for node OAI.LeanBlast.SecondKahnKalai.expectationThreshold_pos. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
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

theorem edgeCount_eq_zero_iff {V : Type*} [Fintype V] (G : SimpleGraph V) :
    edgeCount G = 0 ↔ G = ⊥ := by
  classical
  rw [edgeCount_eq_card_edgeFinset, Finset.card_eq_zero]
  exact G.edgeFinset_eq_empty

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

theorem copyCount_bot_of_edge {V W : Type*} [Fintype V] [Fintype W]
    (H : SimpleGraph V) (he : 1 ≤ edgeCount H) :
    (⊥ : SimpleGraph W).copyCount H = 0 := by
  apply SimpleGraph.copyCount_eq_zero.mpr
  rintro ⟨f⟩
  have hbot : H = ⊥ := by
    apply SimpleGraph.eq_bot_iff_forall_not_adj.mpr
    intro a b hab
    exact f.toHom.map_adj hab
  have hz := (edgeCount_eq_zero_iff H).mpr hbot
  omega

theorem expectedCopies_zero {V : Type*} [Fintype V] (n : ℕ)
    (H : SimpleGraph V) (he : 1 ≤ edgeCount H) :
    expectedCopies n 0 H = 0 := by
  simp [expectedCopies, copyCount_bot_of_edge H he]

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

/-- A subgraph whose expectation vanishes at zero forces strict positivity
of the attained expectation threshold. -/
theorem expectationThreshold_pos_of_zero_constraint {V : Type*}
    (n : ℕ) (H : SimpleGraph V)
    (hone : ∀ F : H.Subgraph, (1 / 2 : ℝ) ≤ expectedCopies n 1 F.coe)
    (F : H.Subgraph) (hzero : expectedCopies n 0 F.coe = 0) :
    0 < expectationThreshold n H := by
  have hatt := expectationThreshold_attained_of_one n H hone
  have hne : expectationThreshold n H ≠ 0 := by
    intro hz
    have h := hatt.2 F
    rw [hz, hzero] at h
    norm_num at h
  exact lt_of_le_of_ne hatt.1.1 (Ne.symm hne)

theorem expectationFeasible_one {V : Type*} [Fintype V]
    (n : ℕ) (H : SimpleGraph V) (hcard : Fintype.card V ≤ n)
    (F : H.Subgraph) : (1 / 2 : ℝ) ≤ expectedCopies n 1 F.coe := by
  classical
  have hFcard : Fintype.card F.verts ≤ n :=
    (Fintype.card_le_of_injective (fun v : F.verts => (v : V)) Subtype.val_injective).trans hcard
  exact (by norm_num : (1 / 2 : ℝ) ≤ 1).trans (expectedCopies_one_ge_one n F.coe hFcard)

/-- Strict positivity follows from the constraint for an actual one-edge
subgraph, whose expected number of copies at parameter zero vanishes. -/
theorem expectationThreshold_pos {V : Type*} [Fintype V]
    (n : ℕ) (H : SimpleGraph V) (hcard : Fintype.card V ≤ n)
    (hedge : 1 ≤ edgeCount H) : 0 < expectationThreshold n H := by
  classical
  have hne : H ≠ ⊥ := by
    intro hz
    have hzero := (edgeCount_eq_zero_iff H).mpr hz
    omega
  obtain ⟨v, w, hvw⟩ := SimpleGraph.ne_bot_iff_exists_adj.mp hne
  let F : H.Subgraph := H.subgraphOfAdj hvw
  let a : F.verts := ⟨v, by simp [F]⟩
  let b : F.verts := ⟨w, by simp [F]⟩
  have hab : F.coe.Adj a b := by
    change s(v, w) = s(v, w)
    rfl
  have hFedge : 1 ≤ edgeCount F.coe := by
    let : Nonempty F.coe.edgeSet := ⟨⟨s(a, b), hab⟩⟩
    exact Nat.card_pos
  exact expectationThreshold_pos_of_zero_constraint n H
    (expectationFeasible_one n H hcard) F (expectedCopies_zero n F.coe hFedge)

end LeanBlast.SecondKahnKalai

end

end OAI

-- ---- platform node ----
open OAI OAI.LeanBlast OAI.LeanBlast.SecondKahnKalai
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.LeanBlast.SecondKahnKalai.expectationThreshold_pos := @_root_.OAI.LeanBlast.SecondKahnKalai.expectationThreshold_pos
