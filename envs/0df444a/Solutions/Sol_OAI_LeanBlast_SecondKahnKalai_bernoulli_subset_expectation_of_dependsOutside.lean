-- Prove2me | solution 1 for OAI.LeanBlast.SecondKahnKalai.bernoulli_subset_expectation_of_dependsOutside
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T02:56:54.479746+00:00
-- url     : https://prove2.me/submissions/01452fb1-3a0b-4443-8ec1-9e3de003e486

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/GraphThreshold/OutsideChangeOfMeasure.lean:L131-L153
-- (upload_full_project.md Phase 4): solution for node OAI.LeanBlast.SecondKahnKalai.bernoulli_subset_expectation_of_dependsOutside. The node keeps its source
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
import Definitions.Def_OAI_Combinatorics_GraphThreshold_ProbabilityTreeFacts
import Definitions.Def_OAI_Combinatorics_GraphThreshold_ProbabilityTreeTrim
import Definitions.Def_OAI_Combinatorics_GraphThreshold_CapacityIteration
import Definitions.Def_OAI_Combinatorics_GraphThreshold_Resampling
import Definitions.Def_OAI_Combinatorics_GraphThreshold_ResamplingEvents
import Definitions.Def_OAI_Combinatorics_GraphThreshold_TreeReductionData
import Definitions.Def_OAI_Combinatorics_GraphThreshold_TreeReduction
import Definitions.Def_OAI_Combinatorics_GraphThreshold_OutsideChangeOfMeasure
import Theorems.Thm_OAI_LeanBlast_SecondKahnKalai_bernoulliExpectation_pushforward

-- ---- from OAI.Combinatorics.GraphThreshold.BernoulliCoupling ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

namespace LeanBlast.SecondKahnKalai

variable {X : Type*} [Fintype X] [DecidableEq X]

theorem finset_eq_indicator_product (U V : Finset X) :
    (if U = V then (1 : ℝ) else 0) =
      ∏ x, if (x ∈ U ↔ x ∈ V) then (1 : ℝ) else 0 := by
  rw [Fintype.prod_boole]
  have h : (∀ x : X, x ∈ U ↔ x ∈ V) ↔ U = V :=
    ⟨Finset.ext, fun h => by subst V; simp⟩
  simp only [h]

theorem bernoulli_union_fixed_mass (p : ℝ) (A Y : Finset X) :
    bernoulliExpectation p (fun W => if W ∪ A = Y then 1 else 0) =
      ∏ x, if x ∈ A then (if x ∈ Y then (1 : ℝ) else 0)
        else (if x ∈ Y then p else 1 - p) := by
  let f : X → Bool → ℝ := fun x b =>
    if (b = true ∨ x ∈ A) ↔ x ∈ Y then 1 else 0
  have hf : (fun W : Finset X => if W ∪ A = Y then (1 : ℝ) else 0) =
      (fun W => ∏ x, f x (decide (x ∈ W))) := by
    funext W
    simpa [f] using finset_eq_indicator_product (W ∪ A) Y
  rw [hf, bernoulliExpectation_product]
  apply Finset.prod_congr rfl
  intro x _
  by_cases ha : x ∈ A <;> by_cases hy : x ∈ Y <;> simp [f, ha, hy]

theorem bernoulli_union_fixed_mass_mul (p : ℝ) (A Y : Finset X) :
    p ^ A.card * bernoulliExpectation p (fun W => if W ∪ A = Y then 1 else 0) =
      if A ⊆ Y then bernoulliWeight p Y else 0 := by
  rw [bernoulli_union_fixed_mass]
  by_cases hAY : A ⊆ Y
  · rw [ite_eq_left hAY]
    have hp : p ^ A.card = ∏ x : X, if x ∈ A then p else 1 := by
      rw [Fintype.prod_ite_mem]
      simp
    rw [hp, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro x _
    by_cases ha : x ∈ A
    · simp [ha, hAY ha]
    · simp [ha]
  · rw [ite_eq_right hAY]
    obtain ⟨x, hxa, hxy⟩ := Finset.not_subset.mp hAY
    have hz : (∏ x, if x ∈ A then (if x ∈ Y then (1 : ℝ) else 0)
        else (if x ∈ Y then p else 1 - p)) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ x)
      simp [hxa, hxy]
    rw [hz, mul_zero]

theorem bernoulli_union_fixed_mass_div (p : ℝ) (hp : p ≠ 0) (A Y : Finset X) :
    bernoulliExpectation p (fun W => if W ∪ A = Y then 1 else 0) =
      (if A ⊆ Y then bernoulliWeight p Y else 0) / p ^ A.card := by
  apply (eq_div_iff (pow_ne_zero _ hp)).2
  simpa only [mul_comm] using bernoulli_union_fixed_mass_mul p A Y

/-- Forcing all coordinates of `A` to be present gives the literal Bernoulli
law conditioned on containing `A`. -/
theorem bernoulliExpectation_union_fixed (p : ℝ) (hp : p ≠ 0)
    (A : Finset X) (F : Finset X → ℝ) :
    bernoulliExpectation p (fun W => F (W ∪ A)) =
      bernoulliExpectation p (fun Y => if A ⊆ Y then F Y / p ^ A.card else 0) := by
  rw [bernoulliExpectation_pushforward]
  unfold bernoulliExpectation
  apply Finset.sum_congr rfl
  intro Y _
  rw [← bernoulliExpectation, bernoulli_union_fixed_mass_div p hp A Y]
  by_cases hAY : A ⊆ Y <;> simp [hAY]
  ring

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

/-- Modifying only coordinates inside the ignored label leaves the observable unchanged. -/
theorem dependsOutside_union {β : Type*} (A S : Finset X) (f : Finset X → β)
    (hf : DependsOutside A f) (hSA : S ⊆ A) (W : Finset X) :
    f (W ∪ S) = f W := by
  apply hf
  ext x
  simp only [Finset.mem_sdiff, Finset.mem_union]
  constructor
  · rintro ⟨hx | hx, hn⟩
    · exact ⟨hx, hn⟩
    · exact (hn (hSA hx)).elim
  · rintro ⟨hx, hn⟩
    exact ⟨Or.inl hx, hn⟩

variable [Fintype X]

/-- A containment event on ignored coordinates is independent of the observable.
This is derived from the fixed-union formula for the actual Bernoulli product weights. -/
theorem bernoulli_subset_expectation_of_dependsOutside
    {p : ℝ} (hp : p ≠ 0) (A S : Finset X) (f : Finset X → ℝ)
    (hf : DependsOutside A f) (hSA : S ⊆ A) :
    bernoulliExpectation p (fun W => if S ⊆ W then f W else 0) =
      p ^ S.card * bernoulliExpectation p f := by
  have hu : bernoulliExpectation p (fun W => f (W ∪ S)) =
      bernoulliExpectation p f := by
    congr 1
    funext W
    exact dependsOutside_union A S f hf hSA W
  have hd : bernoulliExpectation p (fun W => if S ⊆ W then f W / p ^ S.card else 0) =
      bernoulliExpectation p (fun W => if S ⊆ W then f W else 0) / p ^ S.card := by
    unfold bernoulliExpectation
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro W _
    by_cases hW : S ⊆ W <;> simp [hW, mul_div_assoc]
  have h := bernoulliExpectation_union_fixed (p := p) hp S f
  rw [hu, hd] at h
  have he := (eq_div_iff (pow_ne_zero _ hp)).mp h
  simpa only [mul_comm] using he.symm

end LeanBlast.SecondKahnKalai

end

end OAI

-- ---- platform node ----
open OAI OAI.LeanBlast OAI.LeanBlast.SecondKahnKalai
open scoped BigOperators
attribute [local instance] Classical.propDecidable


theorem solution : type_of% @_root_.OAI.LeanBlast.SecondKahnKalai.bernoulli_subset_expectation_of_dependsOutside := @_root_.OAI.LeanBlast.SecondKahnKalai.bernoulli_subset_expectation_of_dependsOutside
