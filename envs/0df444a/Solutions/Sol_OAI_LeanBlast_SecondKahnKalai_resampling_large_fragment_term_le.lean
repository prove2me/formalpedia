-- Prove2me | solution 1 for OAI.LeanBlast.SecondKahnKalai.resampling_large_fragment_term_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T03:02:23.788715+00:00
-- url     : https://prove2.me/submissions/96696d23-c306-44ab-a70c-b1b2a43a4fc1

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/GraphThreshold/LocalFailure.lean:L62-L116
-- (upload_full_project.md Phase 4): solution for node OAI.LeanBlast.SecondKahnKalai.resampling_large_fragment_term_le. The node keeps its source
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

-- ---- from OAI.Combinatorics.GraphThreshold.Resampling ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section
open scoped BigOperators

namespace LeanBlast.SecondKahnKalai

variable {X B : Type*} [DecidableEq X] [Fintype B]

theorem resamplingWeight_eq_zero_of_not_subset (ν : FiniteLaw B) (A : B → Finset X)
    (ρ : ℝ) (W : Finset X) (c b : B) (hb : ¬A b ⊆ resamplingY A W c) :
    resamplingWeight ν A ρ W (c, b) = 0 := by
  simp [resamplingWeight, resamplingTargetWeight, resamplingNumerator, hb]

end LeanBlast.SecondKahnKalai

end

end OAI

-- ---- from OAI.Combinatorics.GraphThreshold.LocalFailure ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

/-! # Local failure of the actual resampling experiment -/

noncomputable section

open Finset

namespace LeanBlast.SecondKahnKalai

variable {X B : Type*} [Fintype X] [DecidableEq X] [Fintype B]

omit [Fintype X] [Fintype B] in
private theorem target_subset_iff_required_subset (A : B → Finset X)
    (W : Finset X) (c b : B) :
    A b ⊆ resamplingY A W c ↔ A b \ A c ⊆ W := by
  constructor
  · intro h x hx
    rcases Finset.mem_union.mp (h (Finset.mem_sdiff.mp hx).1) with hW | hc
    · exact hW
    · exact ((Finset.mem_sdiff.mp hx).2 hc).elim
  · intro h x hx
    by_cases hc : x ∈ A c
    · exact Finset.mem_union.mpr (Or.inr hc)
    · exact Finset.mem_union.mpr (Or.inl (h (Finset.mem_sdiff.mpr ⟨hx, hc⟩)))

omit [Fintype X] [Fintype B] in
private theorem fragment_subset_inter_of_target_subset (A : B → Finset X)
    (W : Finset X) (c b : B) (h : A b ⊆ resamplingY A W c) :
    A b \ W ⊆ A c ∩ A b := by
  intro x hx
  obtain ⟨hb, hW⟩ := Finset.mem_sdiff.mp hx
  rcases Finset.mem_union.mp (h hb) with hxW | hc
  · exact (hW hxW).elim
  · exact Finset.mem_inter.mpr ⟨hc, hb⟩

omit [Fintype X] in
/-- At a large denominator, the actual large-fragment weight is bounded by
an intersection-tail indicator and the required-coordinate indicator. -/
theorem resampling_large_fragment_term_le (ν : FiniteLaw B) (A : B → Finset X)
    {ρ : ℝ} (hρ : 0 < ρ) (m : ℕ) (W : Finset X) (c b : B) :
    (if Real.exp (-10 * (m : ℝ)) ≤ resamplingZ ν A ρ (resamplingY A W c) ∧
          m / 2 < (A b \ W).card then resamplingWeight ν A ρ W (c, b) else 0) ≤
      if m < 2 * (A c ∩ A b).card ∧ A b \ A c ⊆ W then
        Real.exp (10 * (m : ℝ)) * ν.weight c * ν.weight b * (ρ⁻¹) ^ (A b).card
      else 0 := by
  classical
  have hrhs : 0 ≤
      if m < 2 * (A c ∩ A b).card ∧ A b \ A c ⊆ W then
        Real.exp (10 * (m : ℝ)) * ν.weight c * ν.weight b * (ρ⁻¹) ^ (A b).card
      else 0 := by
    split_ifs
    · exact mul_nonneg (mul_nonneg (mul_nonneg (Real.exp_pos _).le (ν.nonneg c))
        (ν.nonneg b)) (pow_nonneg (inv_nonneg.mpr hρ.le) _)
    · exact le_rfl
  by_cases he : Real.exp (-10 * (m : ℝ)) ≤ resamplingZ ν A ρ (resamplingY A W c) ∧
      m / 2 < (A b \ W).card
  · rw [ite_eq_left he]
    by_cases hs : A b ⊆ resamplingY A W c
    · have hfrag := Finset.card_le_card (fragment_subset_inter_of_target_subset A W c b hs)
      have hlarge : m < 2 * (A c ∩ A b).card := by omega
      have hreq := (target_subset_iff_required_subset A W c b).mp hs
      rw [ite_eq_left ⟨hlarge, hreq⟩]
      have hZpos : 0 < resamplingZ ν A ρ (resamplingY A W c) :=
        (Real.exp_pos _).trans_le he.1
      have hscale : 1 ≤ Real.exp (10 * (m : ℝ)) *
          resamplingZ ν A ρ (resamplingY A W c) := by
        calc
          1 = Real.exp (10 * (m : ℝ)) * Real.exp (-10 * (m : ℝ)) := by
            rw [← Real.exp_add]; simp
          _ ≤ _ := mul_le_mul_of_nonneg_left he.1 (Real.exp_pos _).le
      have hnum : 0 ≤ ν.weight b * (ρ⁻¹) ^ (A b).card :=
        mul_nonneg (ν.nonneg b) (pow_nonneg (inv_nonneg.mpr hρ.le) _)
      have hdiv : (ν.weight b * (ρ⁻¹) ^ (A b).card) /
          resamplingZ ν A ρ (resamplingY A W c) ≤
          Real.exp (10 * (m : ℝ)) * (ν.weight b * (ρ⁻¹) ^ (A b).card) := by
        apply (div_le_iff₀ hZpos).mpr
        nlinarith [mul_le_mul_of_nonneg_left hscale hnum]
      unfold resamplingWeight resamplingTargetWeight
      rw [resamplingNumerator, ite_eq_left hs]
      calc
        ν.weight c * ((ν.weight b * (ρ⁻¹) ^ (A b).card) /
            resamplingZ ν A ρ (resamplingY A W c)) ≤
          ν.weight c * (Real.exp (10 * (m : ℝ)) *
            (ν.weight b * (ρ⁻¹) ^ (A b).card)) :=
          mul_le_mul_of_nonneg_left hdiv (ν.nonneg c)
        _ = _ := by ring
    · rw [resamplingWeight_eq_zero_of_not_subset ν A ρ W c b hs]
      exact hrhs
  · rw [ite_eq_right he]
    exact hrhs

end LeanBlast.SecondKahnKalai

end

end OAI

-- ---- platform node ----
open OAI OAI.LeanBlast OAI.LeanBlast.SecondKahnKalai
open Finset


theorem solution : type_of% @_root_.OAI.LeanBlast.SecondKahnKalai.resampling_large_fragment_term_le := @_root_.OAI.LeanBlast.SecondKahnKalai.resampling_large_fragment_term_le
