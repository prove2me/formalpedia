-- Prove2me | solution 1 for OAI.LeanBlast.SecondKahnKalai.cutoff_source_weight_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T02:55:38.163296+00:00
-- url     : https://prove2.me/submissions/4c0787cc-46d8-4045-8861-7315fb6128aa

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/GraphThreshold/OutsideChangeOfMeasure.lean:L99-L127
-- (upload_full_project.md Phase 4): solution for node OAI.LeanBlast.SecondKahnKalai.cutoff_source_weight_le. The node keeps its source
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

-- ---- from OAI.Combinatorics.GraphThreshold.OutsideChangeOfMeasure ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

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

theorem subset_union_iff_sdiff_subset (S T W : Finset X) :
    S ⊆ W ∪ T ↔ S \ T ⊆ W := by
  constructor
  · intro h x hx
    obtain ⟨hxS, hxT⟩ := Finset.mem_sdiff.mp hx
    exact (Finset.mem_union.mp (h hxS)).resolve_right hxT
  · intro h x hxS
    by_cases hxT : x ∈ T
    · exact Finset.mem_union.mpr (Or.inr hxT)
    · exact Finset.mem_union.mpr (Or.inl (h (Finset.mem_sdiff.mpr ⟨hxS, hxT⟩)))

/-- The only pointwise change of density is the reciprocal cutoff.
The remaining event uses coordinates inside the fixed target label. -/
theorem cutoff_source_weight_le (ν : FiniteLaw B) (A : B → Finset X)
    {p δ : ℝ} (hp : 0 ≤ p) (hδ : 0 < δ) (W : Finset X) (c b : B) :
    (if δ ≤ resamplingZ ν A p (resamplingY A W c)
      then resamplingWeight ν A p W (c, b) else 0) ≤
      if A b \ A c ⊆ W then δ⁻¹ * ν.weight c * ν.weight b * (p⁻¹) ^ (A b).card
      else 0 := by
  have hnum : 0 ≤ ν.weight b * (p⁻¹) ^ (A b).card :=
    mul_nonneg (ν.nonneg b) (pow_nonneg (inv_nonneg.mpr hp) _)
  by_cases he : A b \ A c ⊆ W
  · have he' : A b ⊆ resamplingY A W c :=
      (subset_union_iff_sdiff_subset (A b) (A c) W).mpr he
    rw [ite_eq_left he]
    by_cases hz : δ ≤ resamplingZ ν A p (resamplingY A W c)
    · rw [ite_eq_left hz]
      simp only [resamplingWeight, resamplingTargetWeight, resamplingNumerator, ite_eq_left he']
      calc
        ν.weight c * (ν.weight b * (p⁻¹) ^ (A b).card /
            resamplingZ ν A p (resamplingY A W c)) ≤
            ν.weight c * (ν.weight b * (p⁻¹) ^ (A b).card / δ) :=
          mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left hnum hδ hz) (ν.nonneg c)
        _ = _ := by ring
    · rw [ite_eq_right hz]
      exact mul_nonneg (mul_nonneg (mul_nonneg (inv_nonneg.mpr hδ.le) (ν.nonneg c))
        (ν.nonneg b)) (pow_nonneg (inv_nonneg.mpr hp) _)
  · have he' : ¬ A b ⊆ resamplingY A W c :=
      fun h => he ((subset_union_iff_sdiff_subset (A b) (A c) W).mp h)
    simp [he, resamplingWeight, resamplingTargetWeight, resamplingNumerator, he']

variable [Fintype X]

end LeanBlast.SecondKahnKalai

end

end OAI

-- ---- platform node ----
open OAI OAI.LeanBlast OAI.LeanBlast.SecondKahnKalai
open scoped BigOperators
attribute [local instance] Classical.propDecidable


theorem solution : type_of% @_root_.OAI.LeanBlast.SecondKahnKalai.cutoff_source_weight_le := @_root_.OAI.LeanBlast.SecondKahnKalai.cutoff_source_weight_le
