-- Prove2me | solution 1 for OAI.Dixmier.SignMatrix.frames_for_fintype
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T01:49:57.57291+00:00
-- url     : https://prove2.me/submissions/fcb3aef2-6966-4f03-97a7-ee54d4c08f8c

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Unitarizability/Frames.lean:L84-L101
-- (upload_full_project.md Phase 4): solution for node OAI.Dixmier.SignMatrix.frames_for_fintype. The node keeps its source
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
import Theorems.Thm_OAI_Dixmier_FrameParameters_bounds
import Theorems.Thm_OAI_Dixmier_FrameParameters_failure_bound_lt_one
import Theorems.Thm_OAI_Dixmier_SignMatrix_all_subfamilies
import Theorems.Thm_OAI_Dixmier_SignMatrix_exists_sign_matrix

-- ---- from OAI.Analysis.Unitarizability.SignMatrix ----
namespace OAI

/-! Normalized sign matrices and their finite-dimensional bilinear
tests. The coordinate selections are injective and retain label identities. -/
noncomputable section
namespace Dixmier
namespace SignMatrix
open Finset
variable {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]
attribute [local instance] OAI.Dixmier.SignMatrix.instDecidableEq_oAI_2
theorem sign_sq (b : Bool) : (FiniteSigns.sign b)^2 = 1 := by cases b <;> norm_num [FiniteSigns.sign]

omit [Fintype I] in
theorem vector_norm [Nonempty K] (σ : K × I → Bool) (i : I) : ‖vector σ i‖ = 1 := by
  have hk : (0 : ℝ) < Fintype.card K := Nat.cast_pos.mpr Fintype.card_pos
  have h : ‖vector σ i‖^2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [vector_apply, Real.norm_eq_abs, sq_abs, div_pow, sign_sq,
      Real.sq_sqrt hk.le, Finset.sum_const, card_univ, nsmul_eq_mul]
    field_simp
  nlinarith [norm_nonneg (vector σ i)]

end SignMatrix
end Dixmier

end

end OAI

-- ---- from OAI.Analysis.Unitarizability.FrameParameters ----
namespace OAI

/-! Ceiling dimensions and finite union-bound arithmetic for frames. -/
noncomputable section
namespace Dixmier
namespace FrameParameters

theorem exact_failure_bound {n r : ℕ} (hn : 2 ≤ n) (hr : 1 ≤ r) :
    2 * (n : ℝ)^(subfamilySize n r) * 9^(dimension n r + subfamilySize n r) *
      Real.exp (-25*(dimension n r : ℝ)/2) < 1 :=
  failure_bound_lt_one hn (bounds hn hr).1 (bounds hn hr).2.1 (bounds hn hr).2.2

end FrameParameters
end Dixmier

end

end OAI

-- ---- from OAI.Analysis.Unitarizability.ComplexFrames ----
namespace OAI

/-! Complexification preserves real synthesis norm bounds.
The real and imaginary coefficient vectors are handled separately. -/
noncomputable section
namespace Dixmier
namespace ComplexFrames
open Finset
variable {I K : Type*} [Fintype K]
theorem ofReal_norm (v : EuclideanSpace ℝ K) : ‖ofReal v‖ = ‖v‖ := by
  have h : ‖ofReal v‖^2 = ‖v‖^2 := by
    simp only [EuclideanSpace.norm_sq_eq, ofReal, Complex.norm_real]
  nlinarith [norm_nonneg (ofReal v), norm_nonneg v]

end ComplexFrames
end Dixmier

end

end OAI

-- ---- from OAI.Analysis.Unitarizability.Frames ----
namespace OAI

/-! Frame existence with prescribed dimensions and bounds for all small subfamilies. -/
noncomputable section
namespace Dixmier
namespace SignMatrix
open Finset
variable {I J L K : Type*} [Fintype I] [Fintype J] [Fintype L] [Fintype K]
/-- The frame lemma for arbitrary finite label types. -/
theorem frames_for_fintype {r : ℕ} (hn : 2 ≤ Fintype.card I) (hr : 1 ≤ r) :
    ∃ v : I → EuclideanSpace ℂ (Fin (FrameParameters.dimension (Fintype.card I) r)),
      (∀ i, ‖v i‖ = 1) ∧
      FiniteSynthesis.FrameBound v (FrameParameters.subfamilySize (Fintype.card I) r) 10 := by
  have hk : 0 < FrameParameters.dimension (Fintype.card I) r := (FrameParameters.bounds hn hr).1
  let : Nonempty (Fin (FrameParameters.dimension (Fintype.card I) r)) := Fin.pos_iff_nonempty.mp hk
  obtain ⟨σ, hσ⟩ := exists_sign_matrix hk (FrameParameters.exact_failure_bound hn hr)
  let q := Fintype.equivFin I
  let σ' : Fin (FrameParameters.dimension (Fintype.card I) r) × I → Bool := fun ai => σ (ai.1, q ai.2)
  have hσ' (e : Fin (FrameParameters.subfamilySize (Fintype.card I) r) ↪ I) : ‖synthesis σ' e‖ ≤ 10 := by
    have hid : synthesis σ' e = synthesis σ (e.trans q.toEmbedding) := rfl
    rw [hid]
    exact hσ _
  refine ⟨fun i => ComplexFrames.ofReal (vector σ' i), ?_, ?_⟩
  · intro i
    rw [ComplexFrames.ofReal_norm, vector_norm]
  · exact all_subfamilies (Nat.min_le_right _ _) σ' hσ'

end SignMatrix
end Dixmier

end

end OAI

-- ---- platform node ----
open OAI OAI.Dixmier OAI.Dixmier.SignMatrix
open Finset
variable {I J L K : Type*} [Fintype I] [Fintype J] [Fintype L] [Fintype K]
private noncomputable local instance instDecidableEq_oAI_3 : DecidableEq I := Classical.decEq I
private noncomputable local instance instDecidableEq_oAI_4 : DecidableEq J := Classical.decEq J
private noncomputable local instance instDecidableEq_oAI_5 : DecidableEq L := Classical.decEq L
private noncomputable local instance instDecidableEq_oAI_6 : DecidableEq K := Classical.decEq K

theorem solution {r : ℕ} (hn : 2 ≤ Fintype.card I) (hr : 1 ≤ r) :
    ∃ v : I → EuclideanSpace ℂ (Fin (FrameParameters.dimension (Fintype.card I) r)),
      (∀ i, ‖v i‖ = 1) ∧
      FiniteSynthesis.FrameBound v (FrameParameters.subfamilySize (Fintype.card I) r) 10 := by
  first
    | exact OAI.Dixmier.SignMatrix.frames_for_fintype hn hr
    | exact OAI.Dixmier.SignMatrix.frames_for_fintype
    | (apply OAI.Dixmier.SignMatrix.frames_for_fintype <;> assumption)
    | (intros; apply OAI.Dixmier.SignMatrix.frames_for_fintype <;> assumption)
