-- Prove2me | solution 1 for OAI.LeanBlast.SecondKahnKalai.outside_change_of_measure_moment
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T02:57:53.824703+00:00
-- url     : https://prove2.me/submissions/006505ad-4468-4824-9edb-8e4a36b9416d

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/GraphThreshold/OutsideChangeOfMeasure.lean:L155-L214
-- (upload_full_project.md Phase 4): solution for node OAI.LeanBlast.SecondKahnKalai.outside_change_of_measure_moment. The node keeps its source
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
import Theorems.Thm_OAI_LeanBlast_SecondKahnKalai_bernoulli_subset_expectation_of_dependsOutside
import Theorems.Thm_OAI_LeanBlast_SecondKahnKalai_cutoff_source_weight_le

-- ---- from OAI.Combinatorics.GraphThreshold.FiniteProbability ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

namespace LeanBlast.SecondKahnKalai

namespace FiniteLaw

variable {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]

theorem expectation_smul (μ : FiniteLaw Ω) (c : ℝ) (f : Ω → ℝ) :
    μ.expectation (fun ω => c * f ω) = c * μ.expectation f := by
  simp [expectation, Finset.mul_sum, mul_left_comm]

theorem expectation_sum {ι : Type*} [Fintype ι] (μ : FiniteLaw Ω) (f : ι → Ω → ℝ) :
    μ.expectation (fun ω => ∑ i, f i ω) = ∑ i, μ.expectation (f i) := by
  simp only [expectation, Finset.mul_sum]
  exact Finset.sum_comm

theorem expectation_mono (μ : FiniteLaw Ω) {f g : Ω → ℝ} (hfg : ∀ ω, f ω ≤ g ω) :
    μ.expectation f ≤ μ.expectation g :=
  Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (hfg ω) (μ.nonneg ω)

end FiniteLaw

variable {X : Type*} [Fintype X] [DecidableEq X]

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

theorem inv_pow_card_mul_pow_sdiff (p : ℝ) (hp : p ≠ 0) (S T : Finset X) :
    (p⁻¹) ^ S.card * p ^ (S \ T).card = (p⁻¹) ^ (T ∩ S).card := by
  have hc : (S \ T).card + (T ∩ S).card = S.card := by
    simpa only [Finset.inter_comm] using Finset.card_sdiff_add_card_inter S T
  rw [← hc, pow_add]
  calc
    (p⁻¹) ^ (S \ T).card * (p⁻¹) ^ (T ∩ S).card * p ^ (S \ T).card =
        ((p⁻¹) ^ (S \ T).card * p ^ (S \ T).card) * (p⁻¹) ^ (T ∩ S).card := by ring
    _ = (p⁻¹) ^ (T ∩ S).card := by rw [← mul_pow, inv_mul_cancel₀ hp, one_pow, one_mul]

variable [Fintype X]

/-- Change of measure before applying spread: the exact loss is the intersection moment. -/
theorem outside_change_of_measure_moment (ν : FiniteLaw B) (A : B → Finset X)
    {p δ : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) (hδ : 0 < δ)
    (b : B) (f : Finset X → ℝ) (hf : ∀ W, 0 ≤ f W)
    (hloc : DependsOutside (A b) f) :
    bernoulliExpectation p (fun W => cutoffTargetMass ν A p δ W b * f W) ≤
      δ⁻¹ * ν.weight b * bernoulliExpectation p f *
        ν.expectation (fun c => (p⁻¹) ^ (A c ∩ A b).card) := by
  let μ := bernoulliLaw (X := X) p hp.le hp1
  change μ.expectation (fun W => cutoffTargetMass ν A p δ W b * f W) ≤
    δ⁻¹ * ν.weight b * μ.expectation f *
      ν.expectation (fun c => (p⁻¹) ^ (A c ∩ A b).card)
  calc
    μ.expectation (fun W => cutoffTargetMass ν A p δ W b * f W) ≤
        μ.expectation (fun W => ∑ c,
          (if A b \ A c ⊆ W then δ⁻¹ * ν.weight c * ν.weight b * (p⁻¹) ^ (A b).card
            else 0) * f W) := by
      apply μ.expectation_mono
      intro W
      unfold cutoffTargetMass
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum fun c _ =>
        mul_le_mul_of_nonneg_right (cutoff_source_weight_le ν A hp.le hδ W c b) (hf W)
    _ = ∑ c, μ.expectation (fun W =>
          (if A b \ A c ⊆ W then δ⁻¹ * ν.weight c * ν.weight b * (p⁻¹) ^ (A b).card
            else 0) * f W) := μ.expectation_sum _
    _ = ∑ c, δ⁻¹ * ν.weight c * ν.weight b * (p⁻¹) ^ (A c ∩ A b).card *
        μ.expectation f := by
      apply Finset.sum_congr rfl
      intro c _
      have hi : μ.expectation (fun W => if A b \ A c ⊆ W then f W else 0) =
          p ^ (A b \ A c).card * μ.expectation f :=
        bernoulli_subset_expectation_of_dependsOutside hp.ne' (A b) (A b \ A c) f
          hloc Finset.sdiff_subset
      have he : μ.expectation (fun W =>
            (if A b \ A c ⊆ W then δ⁻¹ * ν.weight c * ν.weight b * (p⁻¹) ^ (A b).card
              else 0) * f W) =
          (δ⁻¹ * ν.weight c * ν.weight b * (p⁻¹) ^ (A b).card) *
            μ.expectation (fun W => if A b \ A c ⊆ W then f W else 0) := by
        rw [← μ.expectation_smul]
        congr 1
        funext W
        split_ifs <;> simp
      rw [he, hi]
      calc
        δ⁻¹ * ν.weight c * ν.weight b * (p⁻¹) ^ (A b).card *
            (p ^ (A b \ A c).card * μ.expectation f) =
            δ⁻¹ * ν.weight c * ν.weight b *
              ((p⁻¹) ^ (A b).card * p ^ (A b \ A c).card) * μ.expectation f := by ring
        _ = _ := by rw [inv_pow_card_mul_pow_sdiff p hp.ne']
    _ = δ⁻¹ * ν.weight b * μ.expectation f *
        ν.expectation (fun c => (p⁻¹) ^ (A c ∩ A b).card) := by
      change (∑ c, δ⁻¹ * ν.weight c * ν.weight b * (p⁻¹) ^ (A c ∩ A b).card *
        μ.expectation f) =
        (δ⁻¹ * ν.weight b * μ.expectation f) *
          (∑ c, ν.weight c * (p⁻¹) ^ (A c ∩ A b).card)
      conv_rhs => rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c _
      ring

end LeanBlast.SecondKahnKalai

end

end OAI

-- ---- platform node ----
open OAI OAI.LeanBlast OAI.LeanBlast.SecondKahnKalai
open scoped BigOperators
attribute [local instance] Classical.propDecidable


theorem solution : type_of% @_root_.OAI.LeanBlast.SecondKahnKalai.outside_change_of_measure_moment := @_root_.OAI.LeanBlast.SecondKahnKalai.outside_change_of_measure_moment
