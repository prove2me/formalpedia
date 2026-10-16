-- Prove2me | solution 1 for OAI.LeanBlast.SecondKahnKalai.capacity_failure_sum_lt_one_quarter
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T02:44:13.640014+00:00
-- url     : https://prove2.me/submissions/77cab013-d7b0-46a7-9a26-e2a9507705f3

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/GraphThreshold/CapacityIteration.lean:L329-L355
-- (upload_full_project.md Phase 4): solution for node OAI.LeanBlast.SecondKahnKalai.capacity_failure_sum_lt_one_quarter. The node keeps its source
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

-- ---- from OAI.Combinatorics.GraphThreshold.CapacityIteration ----
-- Lean 4.34 name of Finset.prod_le_prod_of_subset_of_le_one (ordered-semiring version) in Mathlib 0df444a.
-- Lean 4.34 name, proved using the Mathlib 0df444a lemma (same statement).
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

/-- Geometric growth bounds every earlier prefix by one fifteenth of the
current capacity. The natural form avoids premature division. -/
theorem capacity_prefix_sum_le (m : ℕ → ℕ) (k : ℕ)
    (hgrowth : ∀ j, j + 1 < k → 16 * m j ≤ m (j + 1)) :
    ∀ j, j < k → 15 * (∑ h ∈ range j, m h) ≤ m j := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
      intro hj
      have hp := ih (by omega)
      have hn := hgrowth j hj
      rw [sum_range_succ]
      omega

theorem capacity_prefix_sum_real_le (m : ℕ → ℕ) (k : ℕ)
    (hgrowth : ∀ j, j + 1 < k → 16 * m j ≤ m (j + 1))
    {j : ℕ} (hj : j < k) :
    (∑ h ∈ range j, (m h : ℝ)) ≤ (m j : ℝ) / 15 := by
  have h : (15 : ℝ) * (∑ h ∈ range j, (m h : ℝ)) ≤ (m j : ℝ) := by
    exact_mod_cast capacity_prefix_sum_le m k hgrowth j hj
  linarith

theorem strictMonoOn_capacities (m : ℕ → ℕ) (k : ℕ)
    (hpos : ∀ j, j < k → 1 ≤ m j)
    (hgrowth : ∀ j, j + 1 < k → 16 * m j ≤ m (j + 1)) :
    StrictMonoOn m (Set.Iio k) := by
  intro i hi j hj hij
  change i < k at hi
  change j < k at hj
  have hmono : StrictMonoOn m (Set.Iic j) := by
    apply strictMonoOn_Iic_of_lt_succ
    intro a ha
    have hp := hpos a (by omega)
    have hg := hgrowth a (by omega)
    change m a < m (a + 1)
    omega
  exact hmono (show i ≤ j from hij.le) (show j ≤ j from Nat.le_refl j) hij

theorem exp_neg_seven_le_one_eighth : Real.exp (-7) ≤ (1 / 8 : ℝ) := by
  have he : (8 : ℝ) ≤ Real.exp 7 := by
    have h := Real.add_one_le_exp (7 : ℝ)
    norm_num at h
    exact h
  rw [Real.exp_neg]
  apply (inv_le_iff_one_le_mul₀ (Real.exp_pos 7)).mpr
  nlinarith

theorem sum_exp_neg_seven_capacities_lt_one_quarter (s : Finset ℕ)
    (hpos : ∀ m ∈ s, 1 ≤ m) :
    (∑ m ∈ s, Real.exp (-7 * (m : ℝ))) < (1 / 4 : ℝ) := by
  have hq0 := (Real.exp_pos (-7)).le
  have hq1 : Real.exp (-7) < 1 := lt_of_le_of_lt exp_neg_seven_le_one_eighth (by norm_num)
  have heq (m : ℕ) : Real.exp (-7 * (m : ℝ)) = Real.exp (-7) ^ m := by
    simpa only [mul_comm] using Real.exp_nat_mul (-7) m
  simp_rw [heq]
  have hsum := sum_positive_geometric_le s hq0 hq1 hpos
  have hfrac : Real.exp (-7) / (1 - Real.exp (-7)) ≤ (1 / 7 : ℝ) := by
    apply (div_le_iff₀ (sub_pos.mpr hq1)).mpr
    nlinarith [exp_neg_seven_le_one_eighth]
  exact lt_of_le_of_lt (hsum.trans hfrac) (by norm_num)

theorem capacity_failure_sum_lt_one_quarter (m : ℕ → ℕ) (k : ℕ)
    (hpos : ∀ j, j < k → 1 ≤ m j)
    (hgrowth : ∀ j, j + 1 < k → 16 * m j ≤ m (j + 1)) :
    (∑ j ∈ range k,
      Real.exp (12 * (∑ h ∈ range j, (m h : ℝ)) - 8 * (m j : ℝ))) < (1 / 4 : ℝ) := by
  have hmono := strictMonoOn_capacities m k hpos hgrowth
  have hinj : Set.InjOn m (↑(range k) : Set ℕ) := by
    intro i hi j hj hij
    exact hmono.injOn (mem_range.mp hi) (mem_range.mp hj) hij
  calc
    (∑ j ∈ range k,
        Real.exp (12 * (∑ h ∈ range j, (m h : ℝ)) - 8 * (m j : ℝ)))
        ≤ ∑ j ∈ range k, Real.exp (-7 * (m j : ℝ)) := by
      apply Finset.sum_le_sum
      intro j hj
      apply Real.exp_le_exp.mpr
      have hs := capacity_prefix_sum_real_le m k hgrowth (mem_range.mp hj)
      have hm : 0 ≤ (m j : ℝ) := Nat.cast_nonneg _
      nlinarith
    _ = ∑ n ∈ (range k).image m, Real.exp (-7 * (n : ℝ)) := by
      symm
      exact Finset.sum_image hinj
    _ < 1 / 4 := by
      apply sum_exp_neg_seven_capacities_lt_one_quarter
      intro n hn
      obtain ⟨j, hj, rfl⟩ := mem_image.mp hn
      exact hpos j (mem_range.mp hj)

end LeanBlast.SecondKahnKalai

end

end OAI

-- ---- platform node ----
open OAI OAI.LeanBlast OAI.LeanBlast.SecondKahnKalai
open Finset Set


theorem solution : type_of% @_root_.OAI.LeanBlast.SecondKahnKalai.capacity_failure_sum_lt_one_quarter := @_root_.OAI.LeanBlast.SecondKahnKalai.capacity_failure_sum_lt_one_quarter
