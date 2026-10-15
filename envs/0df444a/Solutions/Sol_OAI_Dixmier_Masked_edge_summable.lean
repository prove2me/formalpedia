-- Prove2me | solution 1 for OAI.Dixmier.Masked.edge_summable
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T01:53:49.962461+00:00
-- url     : https://prove2.me/submissions/5ecf5d9a-b52f-4d56-9e05-8757dd71df5c

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Unitarizability/Masked.lean:L55-L70
-- (upload_full_project.md Phase 4): solution for node OAI.Dixmier.Masked.edge_summable. The node keeps its source
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
import Definitions.Def_OAI_Analysis_Unitarizability_FiniteSynthesis
import Definitions.Def_OAI_Analysis_Unitarizability_SignMatrix
import Definitions.Def_OAI_Analysis_Unitarizability_Parameters
import Definitions.Def_OAI_Analysis_Unitarizability_FrameParameters
import Definitions.Def_OAI_Analysis_Unitarizability_ComplexFrames
import Definitions.Def_OAI_Analysis_Unitarizability_Frames
import Definitions.Def_OAI_Analysis_Unitarizability_KernelObstruction
import Definitions.Def_OAI_Analysis_Unitarizability_Cocycle
import Definitions.Def_OAI_Analysis_Unitarizability_HilbertSum
import Definitions.Def_OAI_Analysis_Unitarizability_Masked

-- ---- from OAI.Analysis.Unitarizability.KernelObstruction ----
namespace OAI

/-! Coordinate maps and the invariant-kernel obstruction.
The Hilbert space is the lp space with finite Euclidean fibres. -/
noncomputable section
namespace Dixmier
namespace KernelObstruction
open scoped ComplexConjugate
open Finset
variable {G K : Type*} [Fintype K]
attribute [local instance] OAI.Dixmier.KernelObstruction.instDecidableEq_oAI_1
theorem space_summable (ξ : Space G K) : Summable (fun x => ‖ξ x‖^2) := by
  simpa using (lp.memℓp ξ).summable (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal)

variable [Group G]

end KernelObstruction
end Dixmier

end

end OAI

-- ---- from OAI.Analysis.Unitarizability.Masked ----
namespace OAI

/-! Bounded masked operators. All labels remain separate, including
repeated values of the product list. -/
noncomputable section
namespace Dixmier
namespace Masked
open Finset
variable {G I K : Type*} [Group G] [Fintype I] [Fintype K]
attribute [local instance] OAI.Dixmier.Masked.instDecidableEqComplex_oAI
omit [Fintype I] in
theorem edge_summable (v : I → Fibre K) (s : I → G) (c : G → I → ℂ) (ξ : Space G K) (i : I) :
    Summable (fun x => if c x i ≠ 0 then ‖inner ℂ (v i) (ξ (x*s i))‖^2 else 0) := by
  have hs := ((KernelObstruction.space_summable ξ).comp_injective
    (Equiv.mulRight (s i)).injective).mul_left (‖v i‖^2)
  apply Summable.of_nonneg_of_le _ _ hs
  · intro x; split_ifs <;> positivity
  · intro x
    split_ifs
    · change ‖inner ℂ (v i) (ξ (x*s i))‖^2 ≤ ‖v i‖^2 * ‖ξ (x*s i)‖^2
      calc
        _ ≤ (‖v i‖ * ‖ξ (x*s i)‖)^2 := pow_le_pow_left₀ (norm_nonneg _)
          (norm_inner_le_norm (𝕜 := ℂ) (v i) (ξ (x*s i))) 2
        _ = _ := mul_pow _ _ _
    · change 0 ≤ ‖v i‖^2 * ‖ξ (x*s i)‖^2
      positivity

end Masked
end Dixmier

end

end OAI

-- ---- platform node ----
open OAI OAI.Dixmier OAI.Dixmier.Masked
open Finset
variable {G I K : Type*} [Group G] [Fintype I] [Fintype K]
private noncomputable local instance instDecidableEq_oAI : DecidableEq I := Classical.decEq I
private noncomputable local instance instDecidableEq_oAI_1 : DecidableEq G := Classical.decEq G
attribute [local instance] OAI.Dixmier.Masked.instDecidableEqComplex_oAI

omit [Fintype I] in
theorem solution (v : I → Fibre K) (s : I → G) (c : G → I → ℂ) (ξ : Space G K) (i : I) :
    Summable (fun x => if c x i ≠ 0 then ‖inner ℂ (v i) (ξ (x*s i))‖^2 else 0) := by
  first
    | exact OAI.Dixmier.Masked.edge_summable v s c ξ i
    | exact OAI.Dixmier.Masked.edge_summable
    | (apply OAI.Dixmier.Masked.edge_summable <;> assumption)
    | (intros; apply OAI.Dixmier.Masked.edge_summable <;> assumption)
