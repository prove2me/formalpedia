-- Prove2me | solution 1 for OAI.Dixmier.Masked.difference_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T01:55:59.362252+00:00
-- url     : https://prove2.me/submissions/22502079-f62c-492f-ae54-18118ecdf6bf

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Unitarizability/MaskAlgebra.lean:L100-L118
-- (upload_full_project.md Phase 4): solution for node OAI.Dixmier.Masked.difference_norm_le. The node keeps its source
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
import Theorems.Thm_OAI_Dixmier_Masked_masked_bound

-- ---- from OAI.Analysis.Unitarizability.SparseMask ----
namespace OAI

/-! Finite support estimates for mask differences.
The label type is retained even when the products s_i collide. -/
namespace Dixmier

open Finset
variable {G I : Type*} [Group G] [Fintype I] [DecidableEq I]

private theorem bool_ne_true_union (b c : Bool) (h : b ≠ c) :
    b = true ∨ c = true := by cases b <;> cases c <;> simp_all

private theorem bool_ne_false_union (b c : Bool) (h : b ≠ c) :
    b = false ∨ c = false := by cases b <;> cases c <;> simp_all

/-- A row difference is supported on the union of the two one-sets. -/
theorem rowDifference_subset (a : G → I → Bool) (g x : G) :
    rowDifference a g x ⊆ rowOnes a x ∪ rowOnes a (g⁻¹ * x) := by
  intro i hi
  simp only [rowDifference, rowOnes, mem_filter, mem_univ, true_and, mem_union] at *
  exact bool_ne_true_union _ _ hi

/-- Column support uses zero-sets at y and g⁻¹y. -/
theorem columnDifference_subset (a : G → I → Bool) (s : I → G) (g y : G) :
    columnDifference a s g y ⊆ columnZeros a s y ∪ columnZeros a s (g⁻¹ * y) := by
  intro i hi
  simp only [columnDifference, columnZeros, mem_filter, mem_univ, true_and,
    mem_union, mul_assoc] at *
  exact bool_ne_false_union _ _ hi

/-- The row support bound p=min(2r,n), without distinctness of group products. -/
theorem rowDifference_card_le (a : G → I → Bool) (r : ℕ)
    (hr : ∀ x, (rowOnes a x).card ≤ r) (g x : G) :
    (rowDifference a g x).card ≤ min (2 * r) (Fintype.card I) := by
  apply le_min
  · calc
      _ ≤ (rowOnes a x ∪ rowOnes a (g⁻¹ * x)).card := card_le_card (rowDifference_subset a g x)
      _ ≤ (rowOnes a x).card + (rowOnes a (g⁻¹ * x)).card := card_union_le _ _
      _ ≤ r + r := Nat.add_le_add (hr x) (hr (g⁻¹ * x))
      _ = 2 * r := (two_mul r).symm
  · exact card_le_univ _

/-- The column support bound p=min(2r,n). -/
theorem columnDifference_card_le (a : G → I → Bool) (s : I → G) (r : ℕ)
    (hc : ∀ y, (columnZeros a s y).card ≤ r) (g y : G) :
    (columnDifference a s g y).card ≤ min (2 * r) (Fintype.card I) := by
  apply le_min
  · calc
      _ ≤ (columnZeros a s y ∪ columnZeros a s (g⁻¹ * y)).card :=
        card_le_card (columnDifference_subset a s g y)
      _ ≤ (columnZeros a s y).card + (columnZeros a s (g⁻¹ * y)).card := card_union_le _ _
      _ ≤ r + r := Nat.add_le_add (hc y) (hc (g⁻¹ * y))
      _ = 2 * r := (two_mul r).symm
  · exact card_le_univ _

/-- Nonzero complex mask coefficients correspond exactly to unequal bits. -/
theorem difference_mask_ne_zero (b c : Bool) :
    boolComplex b - boolComplex c ≠ 0 ↔ b ≠ c := by
  cases b <;> cases c <;> simp [boolComplex]

end Dixmier

end OAI

-- ---- from OAI.Analysis.Unitarizability.MaskAlgebra ----
namespace OAI

/-! Sparse masks yield operator conjugation identities, and the
constant mask has a rank-one collision kernel. -/
noncomputable section
namespace Dixmier
namespace Masked
open Finset
open scoped ComplexConjugate
variable {G I K : Type*} [Group G] [Fintype I] [Fintype K]
attribute [local instance] OAI.Dixmier.Masked.instDecidableEq_oAI_3
/-- The masked operator bound in finite-cardinality form. -/
theorem masked_bound_of_frame (v : I → Fibre K) (s : I → G) (c : G → I → ℂ)
    (hc : ∀ x i, ‖c x i‖ ≤ 1) {p : ℕ} {b : ℝ} (hb : 0 ≤ b)
    (hv : FiniteSynthesis.FrameBound v p b)
    (hr : ∀ x, (rowSet c x).card ≤ p) (hcol : ∀ y, (columnSet s c y).card ≤ p) :
    ‖operator v s c hc‖ ≤ b^2 :=
  masked_bound v s c hc hb (fun x => hv _ (hr x)) (fun y => hv _ (hcol y))

theorem operator_sub (v : I → Fibre K) (s : I → G) (c d : G → I → ℂ)
    (hc : ∀ x i, ‖c x i‖ ≤ 1) (hd : ∀ x i, ‖d x i‖ ≤ 1)
    (hcd : ∀ x i, ‖c x i - d x i‖ ≤ 1) :
    operator v s c hc - operator v s d hd = operator v s (fun x i => c x i-d x i) hcd := by
  apply ContinuousLinearMap.ext
  intro ξ
  apply lp.ext
  funext x
  change operator v s c hc ξ x - operator v s d hd ξ x = _
  simp only [operator_apply, sub_mul, sub_smul, Finset.sum_sub_distrib]

theorem conjugate_operator (v : I → Fibre K) (s : I → G) (c : G → I → ℂ)
    (hc : ∀ x i, ‖c x i‖ ≤ 1) (g : G) :
    conjugate KernelObstruction.translation g (operator v s c hc) =
      operator v s (fun x i => c (g⁻¹*x) i) (fun _ i => hc _ i) := by
  apply ContinuousLinearMap.ext
  intro ξ
  apply lp.ext
  funext x
  change KernelObstruction.translation g (operator v s c hc (KernelObstruction.translation g⁻¹ ξ)) x = _
  simp only [KernelObstruction.translation_apply, operator_apply, inv_inv,
    ← mul_assoc, mul_inv_cancel, one_mul]

theorem difference_operator (v : I → Fibre K) (s : I → G) (a : G → I → Bool) (g : G) :
    coboundary KernelObstruction.translation (oriented v s a) g =
      operator v s (fun x i => boolComplex (a x i) - boolComplex (a (g⁻¹*x) i))
        (fun _ _ => difference_mask_norm _ _) := by
  rw [coboundary, oriented, conjugate_operator]
  exact operator_sub _ _ _ _ _ _ _

theorem difference_norm_le (v : I → Fibre K) (s : I → G) (a : G → I → Bool)
    {r : ℕ} {b : ℝ} (hb : 0 ≤ b)
    (hv : FiniteSynthesis.FrameBound v (min (2*r) (Fintype.card I)) b)
    (hr : ∀ x, (rowOnes a x).card ≤ r) (hc : ∀ y, (columnZeros a s y).card ≤ r) (g : G) :
    ‖coboundary KernelObstruction.translation (oriented v s a) g‖ ≤ b^2 := by
  rw [difference_operator]
  apply masked_bound_of_frame _ _ _ _ hb hv
  · intro x
    have h : rowSet (fun x i => boolComplex (a x i) - boolComplex (a (g⁻¹*x) i)) x = rowDifference a g x := by
      ext i
      simp [rowSet, rowDifference, difference_mask_ne_zero]
    rw [h]
    exact rowDifference_card_le a r hr g x
  · intro y
    have h : columnSet s (fun x i => boolComplex (a x i) - boolComplex (a (g⁻¹*x) i)) y = columnDifference a s g y := by
      ext i
      simp [columnSet, columnDifference, difference_mask_ne_zero]
    rw [h]
    exact columnDifference_card_le a s r hc g y

end Masked
end Dixmier

end

end OAI

-- ---- platform node ----
open OAI OAI.Dixmier OAI.Dixmier.Masked
open Finset
open scoped ComplexConjugate
variable {G I K : Type*} [Group G] [Fintype I] [Fintype K]
private noncomputable local instance instDecidableEq_oAI_2 : DecidableEq I := Classical.decEq I
attribute [local instance] OAI.Dixmier.Masked.instDecidableEq_oAI_3
private noncomputable local instance instDecidableEqComplex_oAI_1 : DecidableEq ℂ := Classical.decEq ℂ

theorem solution (v : I → Fibre K) (s : I → G) (a : G → I → Bool)
    {r : ℕ} {b : ℝ} (hb : 0 ≤ b)
    (hv : FiniteSynthesis.FrameBound v (min (2*r) (Fintype.card I)) b)
    (hr : ∀ x, (rowOnes a x).card ≤ r) (hc : ∀ y, (columnZeros a s y).card ≤ r) (g : G) :
    ‖coboundary KernelObstruction.translation (oriented v s a) g‖ ≤ b^2 := by
  first
    | exact OAI.Dixmier.Masked.difference_norm_le v s a hb hv hr hc g
    | exact OAI.Dixmier.Masked.difference_norm_le
    | (apply OAI.Dixmier.Masked.difference_norm_le <;> assumption)
    | (intros; apply OAI.Dixmier.Masked.difference_norm_le <;> assumption)
