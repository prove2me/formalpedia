-- Prove2me | solution 1 for OAI.LeanBlast.SecondKahnKalai.bernoulliExpectation_union
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T02:40:18.544896+00:00
-- url     : https://prove2.me/submissions/12bee613-17c1-4f5d-8cf2-66e09505b4ad

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/GraphThreshold/BernoulliUnion.lean:L58-L79
-- (upload_full_project.md Phase 4): solution for node OAI.LeanBlast.SecondKahnKalai.bernoulliExpectation_union. The node keeps its source
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
import Theorems.Thm_OAI_LeanBlast_SecondKahnKalai_bernoulliExpectation_pushforward

-- ---- from OAI.Combinatorics.GraphThreshold.BernoulliCoupling ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

namespace LeanBlast.SecondKahnKalai

variable {X : Type*} [Fintype X] [DecidableEq X]

theorem bernoulliExpectation_congr (p : ℝ) {f g : Finset X → ℝ}
    (h : ∀ W, f W = g W) : bernoulliExpectation p f = bernoulliExpectation p g := by
  exact Finset.sum_congr rfl fun W _ => congrArg (fun z => bernoulliWeight p W * z) (h W)

theorem bernoulliExpectation_sum {ι : Type*} [Fintype ι] (p : ℝ)
    (f : ι → Finset X → ℝ) :
    bernoulliExpectation p (fun W => ∑ i, f i W) = ∑ i, bernoulliExpectation p (f i) := by
  simp only [bernoulliExpectation, Finset.mul_sum]
  exact Finset.sum_comm

theorem finset_eq_indicator_product (U V : Finset X) :
    (if U = V then (1 : ℝ) else 0) =
      ∏ x, if (x ∈ U ↔ x ∈ V) then (1 : ℝ) else 0 := by
  rw [Fintype.prod_boole]
  have h : (∀ x : X, x ∈ U ↔ x ∈ V) ↔ U = V :=
    ⟨Finset.ext, fun h => by subst V; simp⟩
  simp only [h]

end LeanBlast.SecondKahnKalai

end

end OAI

-- ---- from OAI.Combinatorics.GraphThreshold.BernoulliUnion ----
namespace OAI

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

namespace LeanBlast.SecondKahnKalai

variable {X : Type*} [Fintype X] [DecidableEq X]

theorem bernoulli_union_product (p q : ℝ) (f : X → Bool → ℝ) :
    bernoulliExpectation p (fun U => bernoulliExpectation q
      (fun V => ∏ x, f x (decide (x ∈ U ∪ V)))) =
      ∏ x, ((p + q - p * q) * f x true + (1 - (p + q - p * q)) * f x false) := by
  have hi (U : Finset X) :
      bernoulliExpectation q (fun V => ∏ x, f x (decide (x ∈ U ∪ V))) =
        ∏ x, (q * f x true + (1 - q) * f x (decide (x ∈ U))) := by
    have hfun : (fun V : Finset X => ∏ x, f x (decide (x ∈ U ∪ V))) =
        (fun V => ∏ x, f x (decide (x ∈ U) || decide (x ∈ V))) := by
      funext V
      apply Finset.prod_congr rfl
      intro x _
      by_cases hu : x ∈ U <;> by_cases hv : x ∈ V <;> simp [Finset.mem_union, hu, hv]
    rw [hfun]
    simpa using
      bernoulliExpectation_product q (fun x b => f x (decide (x ∈ U) || b))
  calc
    _ = bernoulliExpectation p (fun U =>
        ∏ x, (q * f x true + (1 - q) * f x (decide (x ∈ U)))) :=
      bernoulliExpectation_congr p hi
    _ = _ := by
      rw [bernoulliExpectation_product p (fun x b => q * f x true + (1 - q) * f x b)]
      apply Finset.prod_congr rfl
      intro x _
      ring

theorem bernoulli_union_mass (p q : ℝ) (Y : Finset X) :
    bernoulliExpectation p (fun U => bernoulliExpectation q
      (fun V => if U ∪ V = Y then 1 else 0)) = bernoulliWeight (p + q - p * q) Y := by
  let f : X → Bool → ℝ := fun x b => if (b = true ↔ x ∈ Y) then 1 else 0
  have hi (U V : Finset X) :
      (if U ∪ V = Y then (1 : ℝ) else 0) = ∏ x, f x (decide (x ∈ U ∪ V)) := by
    simpa [f] using finset_eq_indicator_product (U ∪ V) Y
  calc
    _ = bernoulliExpectation p (fun U => bernoulliExpectation q
        (fun V => ∏ x, f x (decide (x ∈ U ∪ V)))) :=
      bernoulliExpectation_congr p fun U => bernoulliExpectation_congr q (hi U)
    _ = _ := by
      rw [bernoulli_union_product]
      apply Finset.prod_congr rfl
      intro x _
      by_cases hy : x ∈ Y <;> simp [f, hy]

/-- The union of two independent Bernoulli subsets has the stated Bernoulli law. -/
theorem bernoulliExpectation_union (p q : ℝ) (F : Finset X → ℝ) :
    bernoulliExpectation p (fun U => bernoulliExpectation q (fun V => F (U ∪ V))) =
      bernoulliExpectation (p + q - p * q) F := by
  calc
    _ = bernoulliExpectation p (fun U => ∑ Y : Finset X,
        bernoulliExpectation q (fun V => if U ∪ V = Y then 1 else 0) * F Y) :=
      bernoulliExpectation_congr p fun U =>
        bernoulliExpectation_pushforward q (fun V => U ∪ V) F
    _ = ∑ Y : Finset X, bernoulliExpectation p (fun U =>
        bernoulliExpectation q (fun V => if U ∪ V = Y then 1 else 0) * F Y) :=
      bernoulliExpectation_sum p _
    _ = ∑ Y : Finset X, bernoulliWeight (p + q - p * q) Y * F Y := by
      apply Finset.sum_congr rfl
      intro Y _
      have hfactor : bernoulliExpectation p (fun U =>
          bernoulliExpectation q (fun V => if U ∪ V = Y then 1 else 0) * F Y) =
          bernoulliExpectation p (fun U =>
            bernoulliExpectation q (fun V => if U ∪ V = Y then 1 else 0)) * F Y := by
        simp only [bernoulliExpectation, Finset.sum_mul, mul_assoc]
      rw [hfactor, bernoulli_union_mass]
    _ = _ := rfl

end LeanBlast.SecondKahnKalai

end

end OAI

-- ---- platform node ----
open OAI OAI.LeanBlast OAI.LeanBlast.SecondKahnKalai
open scoped BigOperators
attribute [local instance] Classical.propDecidable


theorem solution : type_of% @_root_.OAI.LeanBlast.SecondKahnKalai.bernoulliExpectation_union := @_root_.OAI.LeanBlast.SecondKahnKalai.bernoulliExpectation_union
