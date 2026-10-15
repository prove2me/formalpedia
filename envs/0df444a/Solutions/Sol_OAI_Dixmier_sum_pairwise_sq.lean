-- Prove2me | solution 1 for OAI.Dixmier.sum_pairwise_sq
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T01:37:59.371317+00:00
-- url     : https://prove2.me/submissions/7e82d18f-61a9-4901-9592-4f7ef6d4e4db

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Unitarizability/Average.lean:L14-L30
-- (upload_full_project.md Phase 4): solution for node OAI.Dixmier.sum_pairwise_sq. The node keeps its source
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

-- ---- from OAI.Analysis.Unitarizability.Average ----
namespace OAI

/-! Finite-average identities for contracting averages in Hilbert spaces. -/
noncomputable section
namespace Dixmier
open Finset
open scoped ComplexConjugate
variable {H I : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The finite Hilbert-space variance identity, without normalization. -/
theorem sum_pairwise_sq (S : Finset I) (v : I → H) :
    ∑ i ∈ S, ∑ j ∈ S, ‖v i - v j‖ ^ 2 =
      2 * (S.card : ℝ) * (∑ i ∈ S, ‖v i‖ ^ 2) - 2 * ‖∑ i ∈ S, v i‖ ^ 2 := by
  have hs : (∑ i ∈ S, ∑ j ∈ S, (inner ℂ (v i) (v j)).re) =
      ‖∑ i ∈ S, v i‖ ^ 2 := by
    rw [← @inner_self_eq_norm_sq ℂ]
    simp only [sum_inner, inner_sum, map_sum]
    exact Finset.sum_comm
  simp_rw [@norm_sub_sq ℂ H]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  simp only [← Finset.mul_sum]
  change _ - 2 * (∑ i ∈ S, ∑ j ∈ S, (inner ℂ (v i) (v j)).re) + _ = _
  rw [hs]
  ring

variable {G : Type*} [Group G]
end Dixmier

end

end OAI

-- ---- platform node ----
open OAI OAI.Dixmier
open Finset
open scoped ComplexConjugate
variable {H I : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem solution (S : Finset I) (v : I → H) :
    ∑ i ∈ S, ∑ j ∈ S, ‖v i - v j‖ ^ 2 =
      2 * (S.card : ℝ) * (∑ i ∈ S, ‖v i‖ ^ 2) - 2 * ‖∑ i ∈ S, v i‖ ^ 2 := by
  first
    | exact OAI.Dixmier.sum_pairwise_sq S v
    | exact OAI.Dixmier.sum_pairwise_sq
    | (apply OAI.Dixmier.sum_pairwise_sq <;> assumption)
    | (intros; apply OAI.Dixmier.sum_pairwise_sq <;> assumption)
