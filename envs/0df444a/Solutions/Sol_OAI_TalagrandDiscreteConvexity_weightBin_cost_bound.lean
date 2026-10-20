-- Prove2me | solution 1 for OAI.TalagrandDiscreteConvexity.weightBin_cost_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T16:24:49.29699+00:00
-- url     : https://prove2.me/submissions/1741c8e9-130b-4381-8727-57000650f0ae

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/DiscreteConvexity/Bins.lean:L81-L98
-- (upload_full_project.md Phase 4): solution for node OAI.TalagrandDiscreteConvexity.weightBin_cost_bound. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Pow
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Definitions.Def_TalagrandDiscreteConvexity
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_Model
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_Basic
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_DyadicBins
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_FiniteFibers
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_Bins
import Theorems.Thm_OAI_TalagrandDiscreteConvexity_binExponent_spec
import Theorems.Thm_OAI_TalagrandDiscreteConvexity_bin_card_cost_bound

-- ---- from OAI.Combinatorics.DiscreteConvexity.Bins ----
namespace OAI

open scoped BigOperators

namespace TalagrandDiscreteConvexity

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem mem_weightBin {W : Finset α → ℝ} {U : Finset α} {b : ℕ × ℕ} :
    U ∈ weightBin W b ↔ U ∈ smallWeightFamily W ∧ weightBinKey W U = b := by
  classical
  simp [weightBin, FiniteFibers.fiber]

theorem weightBin_card {W : Finset α → ℝ} {U : Finset α} {b : ℕ × ℕ}
    (hU : U ∈ weightBin W b) : U.card = b.1 := by
  exact congrArg Prod.fst (mem_weightBin.mp hU).2

theorem weightBin_bounds {W : Finset α → ℝ} {U : Finset α} {b : ℕ × ℕ}
    (hU : U ∈ weightBin W b) :
    (1 / 2 : ℝ) ^ (b.2 + 1) < W U ∧ W U ≤ (1 / 2 : ℝ) ^ b.2 := by
  have hmem := mem_weightBin.mp hU
  have hw := mem_smallWeightFamily.mp hmem.1
  have hle : W U ≤ 1 := hw.2.2.le.trans (pow_le_one₀ (by norm_num) (by norm_num))
  have hbin := binExponent_spec hw.2.1 hle
  have he : binExponent (W U) = b.2 := congrArg Prod.snd hmem.2
  simpa only [he] using hbin

omit [DecidableEq α] in
theorem subfamily_weight_sum_le {q : ℝ} {W : Finset α → ℝ}
    (hq : 0 ≤ q) (hW : ∀ U, 0 ≤ W U)
    (hglobal : (∑ U : Finset α, q ^ U.card * W U) ≤ 1) (A : Family α) :
    (∑ U ∈ A, q ^ U.card * W U) ≤ 1 := by
  exact (Finset.sum_le_univ_sum_of_nonneg
    (fun U => mul_nonneg (pow_nonneg hq _) (hW U))).trans hglobal

/-- Each occupied bin satisfies the size hypothesis of the covering lemma. -/
theorem weightBin_cost_bound {q : ℝ} {W : Finset α → ℝ}
    (hq : 0 < q) (hW : ∀ U, 0 ≤ W U)
    (hglobal : (∑ U : Finset α, q ^ U.card * W U) ≤ 1) (b : ℕ × ℕ) :
    ((weightBin W b).card : ℝ) * (q / (2 : ℝ) ^ 70) ^ b.1 ≤
      (2 : ℝ) ^ (b.2 + 1) := by
  have hlo : ((weightBin W b).card : ℝ) * q ^ b.1 *
      (1 / 2 : ℝ) ^ (b.2 + 1) ≤ 1 := by
    calc
      _ = ∑ U ∈ weightBin W b, q ^ b.1 * (1 / 2 : ℝ) ^ (b.2 + 1) := by
        simp [Finset.sum_const, nsmul_eq_mul, mul_assoc]
      _ ≤ ∑ U ∈ weightBin W b, q ^ U.card * W U := by
        apply Finset.sum_le_sum
        intro U hU
        rw [weightBin_card hU]
        exact mul_le_mul_of_nonneg_left (weightBin_bounds hU).1.le (pow_nonneg hq.le _)
      _ ≤ 1 := subfamily_weight_sum_le hq.le hW hglobal _
  exact bin_card_cost_bound hq hlo

end TalagrandDiscreteConvexity

end OAI

-- ---- platform node ----
open OAI OAI.TalagrandDiscreteConvexity
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.TalagrandDiscreteConvexity.weightBin_cost_bound := @_root_.OAI.TalagrandDiscreteConvexity.weightBin_cost_bound
