-- Prove2me | solution 1 for OAI.Dixmier.InvariantProjection.exists_commuting_projection
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T01:57:19.475068+00:00
-- url     : https://prove2.me/submissions/9f9adaec-7aee-4e2b-b054-ba29e8131ca8

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Unitarizability/InvariantProjection.lean:L45-L77
-- (upload_full_project.md Phase 4): solution for node OAI.Dixmier.InvariantProjection.exists_commuting_projection. The node keeps its source
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

-- ---- from OAI.Analysis.Unitarizability.InvariantProjection ----
namespace OAI

/-! A unitarizing similarity gives a bounded commuting projection
onto every closed invariant subspace. -/
noncomputable section
namespace Dixmier
namespace InvariantProjection
variable {G H : Type*} [Group G]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem orthogonal_projection_commutes (U : G →* (H →L[ℂ] H))
    (hU : ∀ g x, ‖U g x‖ = ‖x‖) (M : ClosedSubmodule ℂ H)
    (hM : ∀ g x, x ∈ M → U g x ∈ M) (g : G) :
    Commute M.toSubmodule.starProjection (U g) := by
  change M.toSubmodule.starProjection * U g = U g * M.toSubmodule.starProjection
  apply ContinuousLinearMap.ext
  intro x
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact hM g _ (Submodule.starProjection_apply_mem _ _)
  · intro w hw
    have hi := (LinearMap.norm_map_iff_inner_map_map (U g)).mp (hU g)
    have hm : U g⁻¹ w ∈ M := hM g⁻¹ w hw
    have hz := M.toSubmodule.starProjection_inner_eq_zero x (U g⁻¹ w) hm
    have he := hi (x - M.toSubmodule.starProjection x) (U g⁻¹ w)
    rw [map_sub, rep_inv] at he
    exact he.trans hz

/-- The conclusion supplies one bounded projection; it assumes only the
actual similarity and closed invariance, not a cocycle implementer. -/
theorem exists_commuting_projection (π : G →* (H →L[ℂ] H))
    (hπ : SimilarToUnitary π) (M : ClosedSubmodule ℂ H)
    (hM : ∀ g x, x ∈ M → π g x ∈ M) :
    ∃ P : H →L[ℂ] H, (∀ x, P x ∈ M) ∧
      (∀ x, x ∈ M → P x = x) ∧ ∀ g, Commute P (π g) := by
  rcases hπ with ⟨S, hS⟩
  let N : ClosedSubmodule ℂ H := M.mapEquiv S
  have hN : ∀ g x, x ∈ N → conjugated π S g x ∈ N := by
    intro g x hx
    rcases hx with ⟨y, hy, rfl⟩
    exact ⟨π g y, hM g y hy, by simp⟩
  let Q := N.toSubmodule.starProjection
  let P : H →L[ℂ] H := S.symm.toContinuousLinearMap.comp (Q.comp S.toContinuousLinearMap)
  have hmem (x : H) : P x ∈ M := by
    have h := Submodule.starProjection_apply_mem N.toSubmodule (S x)
    rcases h with ⟨y, hy, he⟩
    change S.symm (Q (S x)) ∈ M
    rw [← he]
    simpa using hy
  have hfix (x : H) (hx : x ∈ M) : P x = x := by
    have hn : S x ∈ N := ⟨x, hx, rfl⟩
    change S.symm (Q (S x)) = x
    rw [Submodule.starProjection_eq_self_iff.mpr hn]
    simp
  refine ⟨P, hmem, hfix, ?_⟩
  intro g
  have hq := orthogonal_projection_commutes (conjugated π S) hS N hN g
  change P * π g = π g * P
  ext x
  have h := congrArg (fun T : H →L[ℂ] H => S.symm (T (S x))) hq.eq
  simpa [P, Q, mul_apply_eq_comp] using h

end InvariantProjection
end Dixmier

end

end OAI

-- ---- platform node ----
open OAI OAI.Dixmier OAI.Dixmier.InvariantProjection
variable {G H : Type*} [Group G]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem solution (π : G →* (H →L[ℂ] H))
    (hπ : SimilarToUnitary π) (M : ClosedSubmodule ℂ H)
    (hM : ∀ g x, x ∈ M → π g x ∈ M) :
    ∃ P : H →L[ℂ] H, (∀ x, P x ∈ M) ∧
      (∀ x, x ∈ M → P x = x) ∧ ∀ g, Commute P (π g) := by
  first
    | exact OAI.Dixmier.InvariantProjection.exists_commuting_projection π hπ M hM
    | exact OAI.Dixmier.InvariantProjection.exists_commuting_projection
    | (apply OAI.Dixmier.InvariantProjection.exists_commuting_projection <;> assumption)
    | (intros; apply OAI.Dixmier.InvariantProjection.exists_commuting_projection <;> assumption)
