-- Prove2me | solution 1 for OAI.Dixmier.assigned_row_card_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T01:34:25.564147+00:00
-- url     : https://prove2.me/submissions/4ca48976-ffbd-438c-b4dc-bbec8346dd69

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Unitarizability/EndpointAssignment.lean:L72-L88
-- (upload_full_project.md Phase 4): solution for node OAI.Dixmier.assigned_row_card_le. The node keeps its source
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

-- ---- from OAI.Analysis.Unitarizability.EndpointAssignment ----
namespace OAI

/-! Infinite endpoint assignment from a finite density inequality.
No countability or distinctness assumption on the edge labels is needed. -/
noncomputable section
namespace Dixmier
open Finset
attribute [local instance] Classical.propDecidable

variable {E V W : Type*}

private theorem assigned_row_eq {row : E → V} {col : E → W} {r : ℕ}
    {f : E → (V × Fin r) ⊕ (W × Fin r)}
    (hf : ∀ e, f e ∈ endpointSlots row col r e) (e : E) (h : isRowSlot (f e) = true) :
    f e = Sum.inl (row e, slotIndex (f e)) := by
  have hm := hf e
  cases he : f e with
  | inl p =>
    simp [he, endpointSlots] at hm
    rcases p with ⟨v, j⟩
    simp_all [slotIndex]
  | inr p => simp [he, isRowSlot] at h

/-- Injectivity of the slot assignment bounds every finite row load. -/
theorem assigned_row_card_le {row : E → V} {col : E → W} {r : ℕ}
    {f : E → (V × Fin r) ⊕ (W × Fin r)}
    (hinj : Function.Injective f) (hf : ∀ e, f e ∈ endpointSlots row col r e)
    (v : V) (F : Finset E) (hF : ∀ e ∈ F, row e = v ∧ isRowSlot (f e) = true) :
    F.card ≤ r := by
  classical
  have hi : Set.InjOn (fun e => slotIndex (f e)) (↑F : Set E) := by
    intro e he e' he' hh
    dsimp only at hh
    apply hinj
    rw [assigned_row_eq hf e (hF e he).2, assigned_row_eq hf e' (hF e' he').2]
    rw [(hF e he).1, (hF e' he').1, hh]
  calc
    F.card = (F.image (fun e => slotIndex (f e))).card := (card_image_of_injOn hi).symm
    _ ≤ Fintype.card (Fin r) := card_le_univ _
    _ = r := Fintype.card_fin r

end Dixmier

end

end OAI

-- ---- platform node ----
open OAI OAI.Dixmier
open Finset
attribute [local instance] Classical.propDecidable
variable {E V W : Type*}

theorem solution {row : E → V} {col : E → W} {r : ℕ}
    {f : E → (V × Fin r) ⊕ (W × Fin r)}
    (hinj : Function.Injective f) (hf : ∀ e, f e ∈ endpointSlots row col r e)
    (v : V) (F : Finset E) (hF : ∀ e ∈ F, row e = v ∧ isRowSlot (f e) = true) :
    F.card ≤ r := by
  first
    | exact OAI.Dixmier.assigned_row_card_le hinj hf v F hF
    | exact OAI.Dixmier.assigned_row_card_le
    | (apply OAI.Dixmier.assigned_row_card_le <;> assumption)
    | (intros; apply OAI.Dixmier.assigned_row_card_le <;> assumption)
