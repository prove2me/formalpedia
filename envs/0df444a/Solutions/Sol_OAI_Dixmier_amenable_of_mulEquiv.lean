-- Prove2me | solution 1 for OAI.Dixmier.amenable_of_mulEquiv
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T02:02:43.999197+00:00
-- url     : https://prove2.me/submissions/13436fbf-d162-416d-b51d-b39f86b5d6a6

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Unitarizability/UniverseTransport.lean:L27-L40
-- (upload_full_project.md Phase 4): solution for node OAI.Dixmier.amenable_of_mulEquiv. The node keeps its source
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
import Definitions.Def_OAI_Analysis_Unitarizability_MaskAlgebra
import Definitions.Def_OAI_Analysis_Unitarizability_LocalBounds
import Definitions.Def_OAI_Analysis_Unitarizability_Triangular
import Definitions.Def_OAI_Analysis_Unitarizability_InvariantProjection
import Definitions.Def_OAI_Analysis_Unitarizability_SumObstruction
import Definitions.Def_OAI_Analysis_Unitarizability_UniverseTransport

-- ---- from OAI.Analysis.Unitarizability.UniverseTransport ----
namespace OAI

/-! Countability lets a group be represented in any universe.
Transport by group equivalences preserves the positive normalized invariant mean
and the bounded nonunitarizable witness. -/
noncomputable section
namespace Dixmier
universe u v w
open scoped BoundedContinuousFunction
variable {G : Type u} {Q : Type v} [Group G] [Group Q]
variable [TopologicalSpace G] [DiscreteTopology G]
variable [TopologicalSpace Q] [DiscreteTopology Q]

/-- Amenability transport uses the same positive normalized invariant mean. -/
theorem amenable_of_mulEquiv (e : G ≃* Q) (hQ : Amenable Q) : Amenable G := by
  rcases hQ with ⟨m, h1, hp, hi⟩
  refine ⟨m.comp (meanPullback e), ?_, ?_, ?_⟩
  · have hc : meanPullback e (BoundedContinuousFunction.const G 1) =
        BoundedContinuousFunction.const Q 1 := by ext q; rfl
    simpa only [LinearMap.comp_apply, hc] using h1
  · intro f hf
    exact hp _ (fun q => hf (e.symm q))
  · intro g f
    have hc : meanPullback e (leftTranslate g f) = leftTranslate (e g) (meanPullback e f) := by
      ext q
      simp [meanPullback_apply, leftTranslate, map_mul, map_inv]
    simpa only [LinearMap.comp_apply, hc] using hi (e g) (meanPullback e f)

end Dixmier

end

end OAI

-- ---- platform node ----
open OAI OAI.Dixmier
universe u v w
open scoped BoundedContinuousFunction
variable {G : Type u} {Q : Type v} [Group G] [Group Q]
variable [TopologicalSpace G] [DiscreteTopology G]
variable [TopologicalSpace Q] [DiscreteTopology Q]

theorem solution (e : G ≃* Q) (hQ : Amenable Q) : Amenable G := by
  first
    | exact OAI.Dixmier.amenable_of_mulEquiv e hQ
    | exact OAI.Dixmier.amenable_of_mulEquiv
    | (apply OAI.Dixmier.amenable_of_mulEquiv <;> assumption)
    | (intros; apply OAI.Dixmier.amenable_of_mulEquiv <;> assumption)
