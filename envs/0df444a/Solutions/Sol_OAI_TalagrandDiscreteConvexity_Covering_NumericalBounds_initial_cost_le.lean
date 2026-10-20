-- Prove2me | solution 1 for OAI.TalagrandDiscreteConvexity.Covering.NumericalBounds.initial_cost_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T16:44:11.840643+00:00
-- url     : https://prove2.me/submissions/d4037c97-9dcd-4b82-b25e-36b9e5bb0036

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/DiscreteConvexity/CoveringNumericalBounds.lean:L170-L191
-- (upload_full_project.md Phase 4): solution for node OAI.TalagrandDiscreteConvexity.Covering.NumericalBounds.initial_cost_le. The node keeps its source
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

/-- The initial weighted-degree generators have the required numerical cost
after inserting the assumed upper bound on the total edge mass. -/
theorem initial_cost_le (r h : ℕ) (hrh : r ≤ h) :
    (T h)⁻¹ * (2 : ℝ) ^ r * (2 : ℝ) ^ (h + 1) ≤
      2 * ((2 : ℝ) ^ (2 * h))⁻¹ := by
  change ((2 : ℝ) ^ (4 * h))⁻¹ * (2 : ℝ) ^ r * (2 : ℝ) ^ (h + 1) ≤ _
  have hpos : 0 < (2 : ℝ) ^ (4 * h) := pow_pos (by norm_num) _
  have hcancel :
      (2 : ℝ) ^ (4 * h) * (2 * ((2 : ℝ) ^ (2 * h))⁻¹) =
        2 * (2 : ℝ) ^ (2 * h) := by
    rw [show 4 * h = 2 * h + 2 * h by omega, pow_add]
    calc
      _ = 2 * ((2 : ℝ) ^ (2 * h) * (2 : ℝ) ^ (2 * h) *
          ((2 : ℝ) ^ (2 * h))⁻¹) := by ring
      _ = 2 * (2 : ℝ) ^ (2 * h) := by rw [mul_self_mul_inv]
  rw [mul_assoc, inv_mul_le_iff₀ hpos, hcancel]
  calc
    (2 : ℝ) ^ r * (2 : ℝ) ^ (h + 1) = (2 : ℝ) ^ (r + (h + 1)) :=
      (pow_add _ _ _).symm
    _ ≤ (2 : ℝ) ^ (2 * h + 1) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    _ = 2 * (2 : ℝ) ^ (2 * h) := by rw [pow_succ, mul_comm]

end TalagrandDiscreteConvexity.Covering.NumericalBounds

end OAI

-- ---- platform node ----
open OAI OAI.TalagrandDiscreteConvexity OAI.TalagrandDiscreteConvexity.Covering OAI.TalagrandDiscreteConvexity.Covering.NumericalBounds


theorem solution : type_of% @_root_.OAI.TalagrandDiscreteConvexity.Covering.NumericalBounds.initial_cost_le := @_root_.OAI.TalagrandDiscreteConvexity.Covering.NumericalBounds.initial_cost_le
