-- Prove2me | solution 1 for OAI.TalagrandDiscreteConvexity.Covering.NumericalBounds.final_cost_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T16:46:12.959205+00:00
-- url     : https://prove2.me/submissions/c2a8a69b-ab39-4384-94b1-50bb6117e5c8

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/DiscreteConvexity/CoveringNumericalBounds.lean:L215-L236
-- (upload_full_project.md Phase 4): solution for node OAI.TalagrandDiscreteConvexity.Covering.NumericalBounds.final_cost_le. The node keeps its source
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
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_CoveringBasic
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_CoveringSampledFamilies
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_FiniteProbability
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_Bernoulli
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_CoveringResidualTuples
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_CoveringNumericalBounds

-- ---- from OAI.Combinatorics.DiscreteConvexity.CoveringNumericalBounds ----
namespace OAI

namespace TalagrandDiscreteConvexity.Covering.NumericalBounds

theorem h_le_m (h : ℕ) : h ≤ m h := by
  calc
    h ≤ 2 ^ h := Nat.le_of_lt Nat.lt_two_pow_self
    _ ≤ 2 ^ (12 * h) :=
      pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 2) (by omega)

/-- The sum of the two initial-scale costs and the residual dyadic cost
is at most the final covering budget. -/
theorem final_cost_le (h : ℕ) (hh : 64 ≤ h) :
    4 * ((2 : ℝ) ^ (2 * h))⁻¹ + ((2 : ℝ) ^ m h)⁻¹ ≤
      3 * ((2 : ℝ) ^ h)⁻¹ := by
  have hpos : 0 < (2 : ℝ) ^ h := pow_pos (by norm_num) _
  have hfour : (4 : ℝ) ≤ (2 : ℝ) ^ h := by
    calc
      (4 : ℝ) = (2 : ℝ) ^ 2 := by norm_num
      _ ≤ (2 : ℝ) ^ h := pow_le_pow_right₀ (by norm_num) (by omega)
  have hfirst : 4 * ((2 : ℝ) ^ (2 * h))⁻¹ ≤ ((2 : ℝ) ^ h)⁻¹ := by
    apply (mul_inv_le_iff₀ (pow_pos (by norm_num : (0 : ℝ) < 2) (2 * h))).2
    rw [show 2 * h = h + h by omega, pow_add, inv_mul_cancel_left₀ hpos.ne']
    exact hfour
  have hlast : ((2 : ℝ) ^ m h)⁻¹ ≤ ((2 : ℝ) ^ h)⁻¹ :=
    inv_anti₀ hpos (pow_le_pow_right₀ (by norm_num) (h_le_m h))
  calc
    4 * ((2 : ℝ) ^ (2 * h))⁻¹ + ((2 : ℝ) ^ m h)⁻¹ ≤
        ((2 : ℝ) ^ h)⁻¹ + ((2 : ℝ) ^ h)⁻¹ := add_le_add hfirst hlast
    _ = 2 * ((2 : ℝ) ^ h)⁻¹ := by ring
    _ ≤ 3 * ((2 : ℝ) ^ h)⁻¹ :=
      mul_le_mul_of_nonneg_right (by norm_num) (inv_nonneg.mpr hpos.le)

end TalagrandDiscreteConvexity.Covering.NumericalBounds

end OAI

-- ---- platform node ----
open OAI OAI.TalagrandDiscreteConvexity OAI.TalagrandDiscreteConvexity.Covering OAI.TalagrandDiscreteConvexity.Covering.NumericalBounds


theorem solution : type_of% @_root_.OAI.TalagrandDiscreteConvexity.Covering.NumericalBounds.final_cost_le := @_root_.OAI.TalagrandDiscreteConvexity.Covering.NumericalBounds.final_cost_le
