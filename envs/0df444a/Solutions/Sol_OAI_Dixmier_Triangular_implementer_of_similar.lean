-- Prove2me | solution 1 for OAI.Dixmier.Triangular.implementer_of_similar
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T01:58:16.044109+00:00
-- url     : https://prove2.me/submissions/9f4958f7-39b1-4706-9572-45f374ea8026

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Unitarizability/Unitarizer.lean:L15-L53
-- (upload_full_project.md Phase 4): solution for node OAI.Dixmier.Triangular.implementer_of_similar. The node keeps its source
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
import Theorems.Thm_OAI_Dixmier_InvariantProjection_exists_commuting_projection

-- ---- from OAI.Analysis.Unitarizability.Unitarizer ----
namespace OAI

/-! The bounded implementer forced by a unitarizing similarity.
The commuting projection onto H ⊕ 0 has upper-right block equal to the
negative implementer, avoiding a bounded inverse for graph coordinates. -/
noncomputable section
namespace Dixmier
namespace Triangular
variable {G H : Type*} [Group G]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A global cocycle implementer obtained from the similarity itself. -/
theorem implementer_of_similar (U : G →* (H →L[ℂ] H)) (D : G → (H →L[ℂ] H))
    (h1 : D 1 = 0) (hD : ∀ g h, D (g*h) = D g + conjugate U g (D h))
    (hπ : SimilarToUnitary (representation U D h1 hD)) :
    ∃ B : H →L[ℂ] H, ∀ g, D g = coboundary U B g := by
  let π := representation U D h1 hD
  let M : ClosedSubmodule ℂ (Double H) :=
    ⟨(WithLp.sndL 2 ℂ H H).ker, (WithLp.sndL 2 ℂ H H).isClosed_ker⟩
  have hM : ∀ g x, x ∈ M → π g x ∈ M := by
    intro g x hx
    change x.snd = 0 at hx
    change (operator (U g) (D g) x).snd = 0
    simp [hx]
  rcases InvariantProjection.exists_commuting_projection π hπ M hM with ⟨P, hm, hf, hp⟩
  let q : H →L[ℂ] H := (WithLp.fstL 2 ℂ H H).comp (P.comp inr)
  have hzero (x : Double H) : (P x).snd = 0 := hm x
  have hfix (x : H) : P (inl x) = inl x := hf _ (by change (inl x).snd = 0; simp)
  have hdecomp (x : Double H) : x = inl x.fst + inr x.snd := by
    apply (WithLp.equiv 2 (H × H)).injective
    apply Prod.ext <;> simp
  have hfst (x : Double H) : (P x).fst = x.fst + q x.snd := by
    nth_rw 1 [hdecomp x]
    rw [map_add, hfix]
    simp [q]
  refine ⟨-q, ?_⟩
  intro g
  ext x
  have h := congrArg (fun T : Double H →L[ℂ] Double H => (T (inr (U g⁻¹ x))).fst) (hp g).eq
  change (P (operator (U g) (D g) (inr (U g⁻¹ x)))).fst =
    (operator (U g) (D g) (P (inr (U g⁻¹ x)))).fst at h
  rw [hfst, operator_fst, operator_snd, operator_fst, hzero] at h
  have hinv : U g (U g⁻¹ x) = x := InvariantProjection.rep_inv U g x
  simp only [inr_apply, WithLp.toLp_fst, WithLp.toLp_snd, map_zero, zero_add, hinv,
    add_zero] at h
  change D g x = (-q) x - U g ((-q) (U g⁻¹ x))
  simp only [neg_apply, map_neg, sub_neg_eq_add]
  change D g x + q x = U g (q (U g⁻¹ x)) at h
  apply eq_neg_add_iff_add_eq.mpr
  simpa only [add_comm] using h

end Triangular
end Dixmier

end

end OAI

-- ---- platform node ----
open OAI OAI.Dixmier OAI.Dixmier.Triangular
variable {G H : Type*} [Group G]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem solution (U : G →* (H →L[ℂ] H)) (D : G → (H →L[ℂ] H))
    (h1 : D 1 = 0) (hD : ∀ g h, D (g*h) = D g + conjugate U g (D h))
    (hπ : SimilarToUnitary (representation U D h1 hD)) :
    ∃ B : H →L[ℂ] H, ∀ g, D g = coboundary U B g := by
  first
    | exact OAI.Dixmier.Triangular.implementer_of_similar U D h1 hD hπ
    | exact OAI.Dixmier.Triangular.implementer_of_similar
    | (apply OAI.Dixmier.Triangular.implementer_of_similar <;> assumption)
    | (intros; apply OAI.Dixmier.Triangular.implementer_of_similar <;> assumption)
