-- Prove2me | solution 1 for OAI.Dixmier.Masked.masked_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T01:54:51.937909+00:00
-- url     : https://prove2.me/submissions/b00f12f9-5777-4696-8ba5-5a40cb3a01fb

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Unitarizability/Masked.lean:L133-L159
-- (upload_full_project.md Phase 4): solution for node OAI.Dixmier.Masked.masked_bound. The node keeps its source
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
import Theorems.Thm_OAI_Dixmier_Masked_edge_summable

-- ---- from OAI.Analysis.Unitarizability.FiniteSynthesis ----
namespace OAI

/-! Finite synthesis maps and their adjoints, with bounds for all small subfamilies. -/
noncomputable section
namespace Dixmier
namespace FiniteSynthesis
open scoped ComplexConjugate
variable {I K : Type*} [Fintype K]
attribute [local instance] OAI.Dixmier.FiniteSynthesis.instDecidableEq_oAI
theorem synthesis_sq_le (v : I → EuclideanSpace ℂ K) (J : Finset I) {b : ℝ}
    (_hb : 0 ≤ b) (hJ : ‖synthesis v J‖ ≤ b) (z : J → ℂ) :
    ‖∑ i : J, z i • v i‖^2 ≤ b^2 * ∑ i : J, ‖z i‖^2 := by
  let z' : EuclideanSpace ℂ J := WithLp.toLp 2 z
  have h := (synthesis v J).le_of_opNorm_le hJ z'
  have hpow := pow_le_pow_left₀ (norm_nonneg _) h 2
  simpa only [synthesis_apply, mul_pow, EuclideanSpace.norm_sq_eq] using hpow

theorem analysis_sq_le (v : I → EuclideanSpace ℂ K) (J : Finset I) {b : ℝ}
    (_hb : 0 ≤ b) (hJ : ‖synthesis v J‖ ≤ b) (x : EuclideanSpace ℂ K) :
    ∑ i : J, ‖inner ℂ (v i) x‖^2 ≤ b^2 * ‖x‖^2 := by
  have hj : ‖(synthesis v J).adjoint‖ ≤ b := by simpa using hJ
  have h := (synthesis v J).adjoint.le_of_opNorm_le hj x
  have hpow := pow_le_pow_left₀ (norm_nonneg _) h 2
  simpa only [EuclideanSpace.norm_sq_eq, synthesis_adjoint_apply, mul_pow] using hpow

end FiniteSynthesis
end Dixmier

end

end OAI

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
theorem edgeEnergy_summable (v : I → Fibre K) (s : I → G) (c : G → I → ℂ) (ξ : Space G K) :
    Summable (edgeEnergy v s c ξ) := summable_sum (fun i _ => edge_summable v s c ξ i)

theorem sum_subfamily {R : Type*} [AddCommMonoid R] (c : I → ℂ) (f : I → R) :
    (∑ i : univ.filter (fun i => c i ≠ 0), f i) = ∑ i, if c i ≠ 0 then f i else 0 := by
  rw [Finset.sum_coe_sort, Finset.sum_filter]

theorem row_estimate (v : I → Fibre K) (s : I → G) (c : G → I → ℂ)
    (hc : ∀ x i, ‖c x i‖ ≤ 1) {b : ℝ} (hb : 0 ≤ b)
    (hrow : ∀ x, ‖FiniteSynthesis.synthesis v (rowSet c x)‖ ≤ b)
    (ξ : Space G K) (x : G) :
    ‖operator v s c hc ξ x‖^2 ≤ b^2 * edgeEnergy v s c ξ x := by
  let J := rowSet c x
  have hsum : operator v s c hc ξ x =
      ∑ i : J, (c x i * inner ℂ (v i) (ξ (x*s i))) • v i := by
    calc
      _ = ∑ i, (c x i * inner ℂ (v i) (ξ (x*s i))) • v i := operator_apply ..
      _ = ∑ i ∈ J, (c x i * inner ℂ (v i) (ξ (x*s i))) • v i := by
        symm
        apply Finset.sum_subset (Finset.subset_univ _)
        intro i hi hn
        have hz : c x i = 0 := by simpa [J, rowSet] using hn
        simp [hz]
      _ = _ := (Finset.sum_coe_sort J (fun i => (c x i * inner ℂ (v i) (ξ (x*s i))) • v i)).symm
  rw [hsum]
  have h := FiniteSynthesis.synthesis_sq_le v J hb (hrow x)
    (fun i => c x i * inner ℂ (v i) (ξ (x*s i)))
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg b)
  have he : edgeEnergy v s c ξ x = ∑ i : J, ‖inner ℂ (v i) (ξ (x*s i))‖^2 := by
    exact (sum_subfamily (c x) (fun i => ‖inner ℂ (v i) (ξ (x*s i))‖^2)).symm
  rw [he]
  apply Finset.sum_le_sum
  intro i hi
  rw [norm_mul, mul_pow]
  have hm : ‖c x i‖^2 ≤ 1 := by simpa using pow_le_pow_left₀ (norm_nonneg _) (hc x i) 2
  exact (mul_le_mul_of_nonneg_right hm (sq_nonneg _)).trans_eq (one_mul _)

theorem edgeEnergy_reindex (v : I → Fibre K) (s : I → G) (c : G → I → ℂ) (ξ : Space G K) :
    ∑' x, edgeEnergy v s c ξ x =
      ∑' y, ∑ i : columnSet s c y, ‖inner ℂ (v i) (ξ y)‖^2 := by
  let f : G → I → ℝ := fun y i => if c (y*(s i)⁻¹) i ≠ 0 then ‖inner ℂ (v i) (ξ y)‖^2 else 0
  have he (i : I) : (fun y => f y i) =
      (fun y => if c y i ≠ 0 then ‖inner ℂ (v i) (ξ (y*s i))‖^2 else 0) ∘
        (Equiv.mulRight (s i)⁻¹) := by
    funext y
    simp [f, mul_assoc]
  have hs (i : I) : Summable (fun y => f y i) := by
    rw [he]
    exact (edge_summable v s c ξ i).comp_injective (Equiv.mulRight (s i)⁻¹).injective
  change (∑' x, ∑ i, _) = _
  rw [Summable.tsum_finsetSum (fun i _ => edge_summable v s c ξ i)]
  have ht (i : I) : (∑' x, if c x i ≠ 0 then ‖inner ℂ (v i) (ξ (x*s i))‖^2 else 0) = ∑' y, f y i := by
    rw [he]
    exact ((Equiv.mulRight (s i)⁻¹).tsum_eq _).symm
  simp_rw [ht]
  rw [← Summable.tsum_finsetSum (fun i _ => hs i)]
  apply tsum_congr
  intro y
  exact (sum_subfamily (fun i => c (y*(s i)⁻¹) i) (fun i => ‖inner ℂ (v i) (ξ y)‖^2)).symm

/-- Row and column synthesis bounds imply the masked operator bound,
without assuming that the product labels s_i are distinct. -/
theorem masked_bound (v : I → Fibre K) (s : I → G) (c : G → I → ℂ)
    (hc : ∀ x i, ‖c x i‖ ≤ 1) {b : ℝ} (hb : 0 ≤ b)
    (hrow : ∀ x, ‖FiniteSynthesis.synthesis v (rowSet c x)‖ ≤ b)
    (hcol : ∀ y, ‖FiniteSynthesis.synthesis v (columnSet s c y)‖ ≤ b) :
    ‖operator v s c hc‖ ≤ b^2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (sq_nonneg b)
  intro ξ
  have hr := (KernelObstruction.space_summable (operator v s c hc ξ)).tsum_le_tsum
    (row_estimate v s c hc hb hrow ξ) ((edgeEnergy_summable v s c ξ).mul_left (b^2))
  rw [tsum_mul_left, ← KernelObstruction.space_norm_sq, edgeEnergy_reindex] at hr
  have hcs : Summable (fun y => ∑ i : columnSet s c y, ‖inner ℂ (v i) (ξ y)‖^2) := by
    have h (y : G) : (∑ i : columnSet s c y, ‖inner ℂ (v i) (ξ y)‖^2) =
        ∑ i : I, if c (y*(s i)⁻¹) i ≠ 0 then ‖inner ℂ (v i) (ξ y)‖^2 else 0 := by
      exact sum_subfamily (fun i => c (y*(s i)⁻¹) i) (fun i => ‖inner ℂ (v i) (ξ y)‖^2)
    simp_rw [h]
    apply summable_sum
    intro i hi
    have hs := (edge_summable v s c ξ i).comp_injective (Equiv.mulRight (s i)⁻¹).injective
    simpa [Function.comp_def, mul_assoc] using hs
  have hcol' := hcs.tsum_le_tsum (fun y => FiniteSynthesis.analysis_sq_le v _ hb (hcol y) (ξ y))
    ((KernelObstruction.space_summable ξ).mul_left (b^2))
  rw [tsum_mul_left, ← KernelObstruction.space_norm_sq] at hcol'
  have hh := hr.trans (mul_le_mul_of_nonneg_left hcol' (sq_nonneg b))
  have hpos : 0 ≤ b^2 * ‖ξ‖ := mul_nonneg (sq_nonneg b) (norm_nonneg ξ)
  nlinarith [norm_nonneg (operator v s c hc ξ)]

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

theorem solution (v : I → Fibre K) (s : I → G) (c : G → I → ℂ)
    (hc : ∀ x i, ‖c x i‖ ≤ 1) {b : ℝ} (hb : 0 ≤ b)
    (hrow : ∀ x, ‖FiniteSynthesis.synthesis v (rowSet c x)‖ ≤ b)
    (hcol : ∀ y, ‖FiniteSynthesis.synthesis v (columnSet s c y)‖ ≤ b) :
    ‖operator v s c hc‖ ≤ b^2 := by
  first
    | exact OAI.Dixmier.Masked.masked_bound v s c hc hb hrow hcol
    | exact OAI.Dixmier.Masked.masked_bound
    | (apply OAI.Dixmier.Masked.masked_bound <;> assumption)
    | (intros; apply OAI.Dixmier.Masked.masked_bound <;> assumption)
