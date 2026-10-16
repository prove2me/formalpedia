-- Prove2me | solution 1 for OAI.LeanBlast.SecondKahnKalai.iid_bernoulli_union_expectation
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T02:41:18.335689+00:00
-- url     : https://prove2.me/submissions/f2d02d76-92e1-4fdf-8671-458a5c56d57f

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/GraphThreshold/BernoulliUnion.lean:L98-L117
-- (upload_full_project.md Phase 4): solution for node OAI.LeanBlast.SecondKahnKalai.iid_bernoulli_union_expectation. The node keeps its source
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
import Theorems.Thm_OAI_LeanBlast_SecondKahnKalai_FiniteLaw_iid_expectation_succ
import Theorems.Thm_OAI_LeanBlast_SecondKahnKalai_bernoulliExpectation_union

-- ---- from OAI.Combinatorics.GraphThreshold.BernoulliUnion ----
namespace OAI

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

namespace LeanBlast.SecondKahnKalai

variable {X : Type*} [Fintype X] [DecidableEq X]

omit [Fintype X] in
theorem biUnion_fin_cons {n : ℕ} (A : Finset X) (draws : Fin n → Finset X) :
    Finset.univ.biUnion (Fin.cases A draws) = A ∪ Finset.univ.biUnion draws := by
  ext x
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_union]
  constructor
  · rintro ⟨i, hi⟩
    revert hi
    refine Fin.cases ?_ (fun j => ?_) i
    · intro hi
      exact Or.inl hi
    · intro hi
      exact Or.inr ⟨j, hi⟩
  · rintro (hx | ⟨j, hj⟩)
    · exact ⟨0, hx⟩
    · exact ⟨j.succ, hj⟩

/-- Exact law of the union of a finite history of independent draws. -/
theorem iid_bernoulli_union_expectation (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (n : ℕ) (F : Finset X → ℝ) :
    ((bernoulliLaw p hp0 hp1).iid n).expectation (fun draws => F (Finset.univ.biUnion draws)) =
      bernoulliExpectation (1 - (1 - p) ^ n) F := by
  induction n generalizing F with
  | zero => simp
  | succ n ih =>
      rw [FiniteLaw.iid_expectation_succ]
      simp_rw [biUnion_fin_cons]
      have hi (A : Finset X) := ih (fun W => F (A ∪ W))
      have hrewrite : (fun A => ((bernoulliLaw p hp0 hp1).iid n).expectation
          (fun draws => F (A ∪ Finset.univ.biUnion draws))) =
          (fun A => bernoulliExpectation (1 - (1 - p) ^ n) (fun W => F (A ∪ W))) := by
        funext A
        exact hi A
      rw [hrewrite, bernoulliLaw_expectation, bernoulliExpectation_union]
      congr 1
      rw [pow_succ]
      ring

end LeanBlast.SecondKahnKalai

end

end OAI

-- ---- platform node ----
open OAI OAI.LeanBlast OAI.LeanBlast.SecondKahnKalai
open scoped BigOperators
attribute [local instance] Classical.propDecidable


theorem solution : type_of% @_root_.OAI.LeanBlast.SecondKahnKalai.iid_bernoulli_union_expectation := @_root_.OAI.LeanBlast.SecondKahnKalai.iid_bernoulli_union_expectation
