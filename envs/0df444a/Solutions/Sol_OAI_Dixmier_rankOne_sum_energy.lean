-- Prove2me | solution 1 for OAI.Dixmier.rankOne_sum_energy
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T01:44:39.319173+00:00
-- url     : https://prove2.me/submissions/791da8be-967b-4b67-b902-662c241bd86d

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Unitarizability/KernelEnergy.lean:L55-L74
-- (upload_full_project.md Phase 4): solution for node OAI.Dixmier.rankOne_sum_energy. The node keeps its source
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
import Definitions.Def_OAI_Analysis_Unitarizability_FiniteSigns
import Definitions.Def_OAI_Analysis_Unitarizability_KernelEnergy

-- ---- from OAI.Analysis.Unitarizability.KernelEnergy ----
namespace OAI

/-! Positive rank-one kernel energy. Matrices are represented by their entries
with the unnormalized Hilbert–Schmidt (Euclidean coefficient) norm. -/
noncomputable section
namespace Dixmier
attribute [local instance] Classical.propDecidable
open Finset
open scoped ComplexConjugate
variable {K I G : Type*} [Fintype K] [Fintype I]

theorem rankOne_inner (v w : EuclideanSpace ℂ K) :
    inner ℂ (rankOneCoefficients v) (rankOneCoefficients w) =
      inner ℂ v w * conj (inner ℂ v w) := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Pi.star_apply,
    rankOneCoefficients, map_sum, map_mul]
  rw [Fintype.sum_prod_type, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  simp only [← Complex.star_def, star_mul, star_star]
  ring

theorem rankOne_inner_re (v w : EuclideanSpace ℂ K) :
    (inner ℂ (rankOneCoefficients v) (rankOneCoefficients w)).re = ‖inner ℂ v w‖^2 := by
  rw [rankOne_inner, Complex.mul_conj, Complex.ofReal_re]
  exact Complex.normSq_eq_norm_sq _

theorem rankOne_norm_sq (v : EuclideanSpace ℂ K) (hv : ‖v‖ = 1) :
    ‖rankOneCoefficients v‖^2 = 1 := by
  rw [← @inner_self_eq_norm_sq ℂ]
  change (inner ℂ (rankOneCoefficients v) (rankOneCoefficients v)).re = 1
  rw [rankOne_inner_re, inner_self_eq_norm_sq_to_K, hv]
  norm_num

omit [Fintype I] in
/-- Positivity of every pairwise Hilbert–Schmidt inner product makes each
block’s energy at least the number of its unit rank-one summands. -/
theorem rankOne_sum_energy (v : I → EuclideanSpace ℂ K) (hv : ∀ i, ‖v i‖ = 1)
    (J : Finset I) : (J.card : ℝ) ≤ ‖∑ i ∈ J, rankOneCoefficients (v i)‖^2 := by
  rw [← @inner_self_eq_norm_sq ℂ]
  simp only [sum_inner, inner_sum, map_sum]
  calc
    (J.card : ℝ) = ∑ i ∈ J, (1 : ℝ) := by simp
    _ ≤ ∑ i ∈ J, ∑ j ∈ J, (inner ℂ (rankOneCoefficients (v j)) (rankOneCoefficients (v i))).re := by
      apply Finset.sum_le_sum
      intro i hi
      have he : (inner ℂ (rankOneCoefficients (v i)) (rankOneCoefficients (v i))).re = 1 := by
        change RCLike.re (inner ℂ (rankOneCoefficients (v i)) (rankOneCoefficients (v i))) = 1
        rw [inner_self_eq_norm_sq, rankOne_norm_sq _ (hv i)]
      rw [← he]
      apply Finset.single_le_sum (f := fun j => (inner ℂ (rankOneCoefficients (v j)) (rankOneCoefficients (v i))).re) _ hi
      intro j hj
      rw [rankOne_inner_re]
      positivity

end Dixmier

end

end OAI

-- ---- platform node ----
open OAI OAI.Dixmier
attribute [local instance] Classical.propDecidable
open Finset
open scoped ComplexConjugate
variable {K I G : Type*} [Fintype K] [Fintype I]

omit [Fintype I] in
theorem solution (v : I → EuclideanSpace ℂ K) (hv : ∀ i, ‖v i‖ = 1)
    (J : Finset I) : (J.card : ℝ) ≤ ‖∑ i ∈ J, rankOneCoefficients (v i)‖^2 := by
  first
    | exact OAI.Dixmier.rankOne_sum_energy v hv J
    | exact OAI.Dixmier.rankOne_sum_energy
    | (apply OAI.Dixmier.rankOne_sum_energy <;> assumption)
    | (intros; apply OAI.Dixmier.rankOne_sum_energy <;> assumption)
