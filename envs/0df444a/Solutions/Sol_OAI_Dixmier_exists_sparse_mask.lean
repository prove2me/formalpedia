-- Prove2me | solution 1 for OAI.Dixmier.exists_sparse_mask
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T01:35:31.186311+00:00
-- url     : https://prove2.me/submissions/48e752c5-176d-44c9-85c6-bd51186e3a0c

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Unitarizability/EndpointAssignment.lean:L108-L139
-- (upload_full_project.md Phase 4): solution for node OAI.Dixmier.exists_sparse_mask. The node keeps its source
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
import Theorems.Thm_OAI_Dixmier_assigned_col_card_le
import Theorems.Thm_OAI_Dixmier_assigned_row_card_le

-- ---- from OAI.Analysis.Unitarizability.EndpointAssignment ----
namespace OAI

/-! Infinite endpoint assignment from a finite density inequality.
No countability or distinctness assumption on the edge labels is needed. -/
noncomputable section
namespace Dixmier
open Finset
attribute [local instance] Classical.propDecidable

variable {E V W : Type*}

/-- All neighboring slots of a finite edge set: endpoints have distinct copies. -/
theorem endpointSlots_biUnion (row : E → V) (col : E → W) (r : ℕ)
    (F : Finset E) :
    F.biUnion (endpointSlots row col r) =
      ((F.image row) ×ˢ (univ : Finset (Fin r))).disjSum ((F.image col) ×ˢ univ) := by
  classical
  ext z
  rcases z with ⟨v, j⟩ | ⟨w, j⟩ <;> simp [endpointSlots]

/-- Infinite Hall matching with r slots at every row and every column. -/
theorem exists_endpoint_assignment (row : E → V) (col : E → W) (r : ℕ)
    (hdensity : ∀ F : Finset E, F.card ≤ r * ((F.image row).card + (F.image col).card)) :
    ∃ f : E → (V × Fin r) ⊕ (W × Fin r), Function.Injective f ∧
      ∀ e, f e ∈ endpointSlots row col r e := by
  classical
  apply (all_card_le_biUnion_card_iff_exists_injective (endpointSlots row col r)).mp
  intro F
  rw [endpointSlots_biUnion]
  simpa only [card_disjSum, card_product, card_univ, Fintype.card_fin, Nat.mul_add,
    Nat.mul_comm] using hdensity F

/-- A sparse mask from finite endpoint density. -/
theorem exists_sparse_mask {G I : Type*} [Group G] [Fintype I] (s : I → G) (r : ℕ)
    (hdensity : ∀ F : Finset (G × I), F.card ≤
      r * ((F.image Prod.fst).card + (F.image (fun e => e.1 * s e.2)).card)) :
    ∃ a : G → I → Bool, (∀ x, (rowOnes a x).card ≤ r) ∧
      ∀ y, (columnZeros a s y).card ≤ r := by
  classical
  obtain ⟨f, hinj, hf⟩ := exists_endpoint_assignment Prod.fst (fun e : G × I => e.1 * s e.2) r hdensity
  let a : G → I → Bool := fun x i => isRowSlot (f (x, i))
  refine ⟨a, ?_, ?_⟩
  · intro x
    let F := (rowOnes a x).image (fun i => (x, i))
    have hF : ∀ e ∈ F, e.1 = x ∧ isRowSlot (f e) = true := by
      rintro e he
      obtain ⟨i, hi, rfl⟩ := mem_image.mp he
      exact ⟨rfl, (mem_filter.mp hi).2⟩
    have hbound := assigned_row_card_le hinj hf x F hF
    have hi : Function.Injective (fun i : I => (x, i)) := by
      intro i j h
      exact congrArg Prod.snd h
    simpa only [F, card_image_of_injective _ hi] using hbound
  · intro y
    let F := (columnZeros a s y).image (fun i => (y * (s i)⁻¹, i))
    have hF : ∀ e ∈ F, e.1 * s e.2 = y ∧ isRowSlot (f e) = false := by
      rintro e he
      obtain ⟨i, hi, rfl⟩ := mem_image.mp he
      exact ⟨by simp, (mem_filter.mp hi).2⟩
    have hbound := assigned_col_card_le hinj hf y F hF
    have hi : Function.Injective (fun i => (y * (s i)⁻¹, i)) := by
      intro i j h
      exact congrArg Prod.snd h
    simpa only [F, card_image_of_injective _ hi] using hbound

end Dixmier

end

end OAI

-- ---- platform node ----
open OAI OAI.Dixmier
open Finset
attribute [local instance] Classical.propDecidable
variable {E V W : Type*}

theorem solution {G I : Type*} [Group G] [Fintype I] (s : I → G) (r : ℕ)
    (hdensity : ∀ F : Finset (G × I), F.card ≤
      r * ((F.image Prod.fst).card + (F.image (fun e => e.1 * s e.2)).card)) :
    ∃ a : G → I → Bool, (∀ x, (rowOnes a x).card ≤ r) ∧
      ∀ y, (columnZeros a s y).card ≤ r := by
  first
    | exact OAI.Dixmier.exists_sparse_mask s r hdensity
    | exact OAI.Dixmier.exists_sparse_mask
    | (apply OAI.Dixmier.exists_sparse_mask <;> assumption)
    | (intros; apply OAI.Dixmier.exists_sparse_mask <;> assumption)
