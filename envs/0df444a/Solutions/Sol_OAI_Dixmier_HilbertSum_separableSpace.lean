-- Prove2me | solution 1 for OAI.Dixmier.HilbertSum.separableSpace
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T01:53:06.865928+00:00
-- url     : https://prove2.me/submissions/8ddedb7e-3e52-4e78-97b0-7f9578bed9ce

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Unitarizability/HilbertSum.lean:L132-L151
-- (upload_full_project.md Phase 4): solution for node OAI.Dixmier.HilbertSum.separableSpace. The node keeps its source
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

-- ---- from OAI.Analysis.Unitarizability.HilbertSum ----
namespace OAI

/-! Uniformly bounded Hilbert direct sums. The component implementers
are never summed and need not be uniformly bounded. -/
noncomputable section
namespace Dixmier
namespace HilbertSum
variable {G I : Type*} [Group G] {E : I → Type*}
variable [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℂ (E i)]
attribute [local instance] OAI.Dixmier.HilbertSum.instDecidableEq_oAI
/-- Countably many separable fibres have a separable Hilbert sum. The proof
uses the dense span of coordinate inclusions and convergence of finite sums. -/
theorem separableSpace [Countable I] [∀ i, TopologicalSpace.SeparableSpace (E i)] :
    TopologicalSpace.SeparableSpace (Space E) := by
  let s : Set (Space E) := ⋃ i, Set.range (inclusion (E := E) i)
  let V : Submodule ℂ (Space E) := Submodule.span ℂ s
  have hs : TopologicalSpace.IsSeparable s :=
    TopologicalSpace.IsSeparable.iUnion (fun i =>
      TopologicalSpace.isSeparable_range (inclusion (E := E) i).continuous)
  have hv : TopologicalSpace.IsSeparable (V : Set (Space E)) := hs.span
  have hd : Dense (V : Set (Space E)) := by
    intro x
    apply isClosed_closure.mem_of_tendsto (lp.hasSum_single (by norm_num : (2 : ENNReal) ≠ ⊤) x)
    apply Filter.Eventually.of_forall
    intro F
    apply subset_closure
    apply V.sum_mem
    intro i hi
    exact Submodule.subset_span (Set.mem_iUnion.mpr ⟨i, ⟨x i, rfl⟩⟩)
  exact hd.isSeparable_iff.mp hv

end HilbertSum
end Dixmier

end

end OAI

-- ---- platform node ----
open OAI OAI.Dixmier OAI.Dixmier.HilbertSum
variable {G I : Type*} [Group G] {E : I → Type*}
variable [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℂ (E i)]
attribute [local instance] OAI.Dixmier.HilbertSum.instDecidableEq_oAI

theorem solution [Countable I] [∀ i, TopologicalSpace.SeparableSpace (E i)] :
    TopologicalSpace.SeparableSpace (Space E) := by
  first
    | exact OAI.Dixmier.HilbertSum.separableSpace
    | (apply OAI.Dixmier.HilbertSum.separableSpace <;> assumption)
    | (intros; apply OAI.Dixmier.HilbertSum.separableSpace <;> assumption)
