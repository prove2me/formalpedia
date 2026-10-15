-- Prove2me | solution 1 for OAI.Dixmier.l2_square_difference_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T01:39:27.120235+00:00
-- url     : https://prove2.me/submissions/275de6cd-ed6f-464c-8554-4775fce448cf

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Unitarizability/VectorMean.lean:L95-L116
-- (upload_full_project.md Phase 4): solution for node OAI.Dixmier.l2_square_difference_bound. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Shrink
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Combinatorics.Hall.Basic
import Mathlib.Data.Countable.Small
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Order.Filter.AtTopBot.Tendsto
import Mathlib.Order.Lattice.Nat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Topology.Instances.Discrete
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Definitions.Def_Dixmier
import Definitions.Def_OAI_Analysis_Unitarizability_SparseMask
import Definitions.Def_OAI_Analysis_Unitarizability_EndpointAssignment
import Definitions.Def_OAI_Analysis_Unitarizability_SparseSplitting
import Definitions.Def_OAI_Analysis_Unitarizability_Regular
import Definitions.Def_OAI_Analysis_Unitarizability_VectorMean

-- ---- from OAI.Analysis.Unitarizability.VectorMean ----
namespace OAI

/-! Vector means and their translation error bounds. -/
noncomputable section
namespace Dixmier
open scoped BoundedContinuousFunction
variable {G : Type*} [Group G] [TopologicalSpace G]

theorem norm_sq_difference_le (a b : ℂ) :
    |‖a‖^2 - ‖b‖^2| ≤ ‖a - b‖ * (‖a‖ + ‖b‖) := by
  have he : |‖a‖^2 - ‖b‖^2| = |‖a‖ - ‖b‖| * (‖a‖ + ‖b‖) := by
    conv_rhs => rw [← abs_of_nonneg (add_nonneg (norm_nonneg a) (norm_nonneg b))]
    rw [← abs_mul]
    congr 1
    ring
  rw [he]
  exact mul_le_mul_of_nonneg_right (abs_norm_sub_norm_le a b)
    (add_nonneg (norm_nonneg a) (norm_nonneg b))

omit [Group G] [TopologicalSpace G] in
/-- The l2-to-l1 estimate behind the vector-mean translation error bound. -/
theorem l2_square_difference_bound (ξ η : ScalarL2 G) :
    Summable (fun x => |‖ξ x‖^2 - ‖η x‖^2|) ∧
    (∑' x, |‖ξ x‖^2 - ‖η x‖^2|) ≤ ‖ξ - η‖ * (‖ξ‖ + ‖η‖) := by
  have hp : (2 : ENNReal).toReal.HolderConjugate (2 : ENNReal).toReal := by
    norm_num [Real.HolderConjugate]
    constructor <;> norm_num
  have h1 := lp.tsum_mul_le_mul_norm hp (ξ - η) ξ
  have h2 := lp.tsum_mul_le_mul_norm hp (ξ - η) η
  have hsum := h1.1.add h2.1
  have hb : ∀ x, |‖ξ x‖^2 - ‖η x‖^2| ≤ ‖(ξ - η) x‖ * ‖ξ x‖ + ‖(ξ - η) x‖ * ‖η x‖ := by
    intro x
    simpa [mul_add] using norm_sq_difference_le (ξ x) (η x)
  have hs := Summable.of_nonneg_of_le (fun x => abs_nonneg _) hb hsum
  refine ⟨hs, ?_⟩
  calc
    (∑' x, |‖ξ x‖^2 - ‖η x‖^2|) ≤ ∑' x, (‖(ξ - η) x‖ * ‖ξ x‖ + ‖(ξ - η) x‖ * ‖η x‖) :=
      Summable.tsum_le_tsum hb hs hsum
    _ = (∑' x, ‖(ξ - η) x‖ * ‖ξ x‖) + ∑' x, ‖(ξ - η) x‖ * ‖η x‖ := h1.1.tsum_add h2.1
    _ ≤ ‖ξ - η‖ * ‖ξ‖ + ‖ξ - η‖ * ‖η‖ := add_le_add h1.2 h2.2
    _ = ‖ξ - η‖ * (‖ξ‖ + ‖η‖) := (mul_add _ _ _).symm

end Dixmier

end

end OAI

-- ---- platform node ----
open OAI OAI.Dixmier
open scoped BoundedContinuousFunction
variable {G : Type*} [Group G] [TopologicalSpace G]

omit [Group G] [TopologicalSpace G] in
theorem solution (ξ η : ScalarL2 G) :
    Summable (fun x => |‖ξ x‖^2 - ‖η x‖^2|) ∧
    (∑' x, |‖ξ x‖^2 - ‖η x‖^2|) ≤ ‖ξ - η‖ * (‖ξ‖ + ‖η‖) := by
  first
    | exact OAI.Dixmier.l2_square_difference_bound ξ η
    | exact OAI.Dixmier.l2_square_difference_bound
    | (apply OAI.Dixmier.l2_square_difference_bound <;> assumption)
    | (intros; apply OAI.Dixmier.l2_square_difference_bound <;> assumption)
