-- Prove2me | solution 1 for OAI.Dixmier.main_theorem_all_universes
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T02:03:37.864727+00:00
-- url     : https://prove2.me/submissions/41079cb7-9e03-4b47-a377-5401b974effb

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Unitarizability/UniverseTransport.lean:L54-L63
-- (upload_full_project.md Phase 4): solution for the platform mission target OAI.Dixmier.main_theorem_all_universes.
-- The source declaration is kept inside its namespace next to the proof-only helpers it needs;
-- `theorem solution` restates the platform stub (Theorems.Thm_OAI_Dixmier_main_theorem_all_universes) verbatim and is proved by it.
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
import Theorems.Thm_OAI_Dixmier_amenable_of_mulEquiv
import Theorems.Thm_OAI_Dixmier_nonamenable_witness

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

omit [TopologicalSpace G] [DiscreteTopology G] [TopologicalSpace Q] [DiscreteTopology Q] in
/-- Reindexing the group does not change the Hilbert space, bound or similarities. -/
theorem witness_of_mulEquiv (e : G ≃* Q) (hQ : NonamenableWitness.{v,w} Q) :
    NonamenableWitness.{u,w} G := by
  rcases hQ with ⟨H, hnorm, hinner, hcomplete, hsep, π, hb, hn⟩
  refine ⟨H, hnorm, hinner, hcomplete, hsep, π.comp e.toMonoidHom, fun g => hb (e g), ?_⟩
  rintro ⟨S, hS⟩
  apply hn
  refine ⟨S, ?_⟩
  intro q x
  simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, e.apply_symm_apply] using hS (e.symm q) x

/-- The main theorem with independent group and Hilbert-space universes. -/
theorem main_theorem_all_universes : MainTheorem.{u,v} := by
  intro G _ _ _ _ hG
  let Q := Shrink.{v} G
  let e : G ≃* Q := Shrink.mulEquiv.symm
  let : Countable Q := e.surjective.countable
  let : TopologicalSpace Q := ⊥
  let : DiscreteTopology Q := ⟨rfl⟩
  have hQ : ¬ Amenable Q := fun h => hG (amenable_of_mulEquiv e h)
  exact witness_of_mulEquiv e (nonamenable_witness hQ)

end Dixmier

end

end OAI

-- ---- mission target ----
open OAI OAI.Dixmier
universe u v
open scoped BoundedContinuousFunction

theorem solution : MainTheorem.{u,v} := by
  first
    | exact OAI.Dixmier.main_theorem_all_universes
    | (apply OAI.Dixmier.main_theorem_all_universes <;> assumption)
    | (intros; apply OAI.Dixmier.main_theorem_all_universes <;> assumption)
