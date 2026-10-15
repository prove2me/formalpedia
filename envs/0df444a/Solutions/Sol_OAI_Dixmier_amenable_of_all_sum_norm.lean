-- Prove2me | solution 1 for OAI.Dixmier.amenable_of_all_sum_norm
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T01:40:44.528283+00:00
-- url     : https://prove2.me/submissions/4bae29ba-c070-4ba1-9d4a-48d58624069a

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Unitarizability/Contracting.lean:L30-L52
-- (upload_full_project.md Phase 4): solution for node OAI.Dixmier.amenable_of_all_sum_norm. The node keeps its source
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
import Theorems.Thm_OAI_Dixmier_almost_invariant_of_sum_norm
import Theorems.Thm_OAI_Dixmier_amenable_of_approximate_means
import Theorems.Thm_OAI_Dixmier_l2_square_difference_bound

-- ---- from OAI.Analysis.Unitarizability.Regular ----
namespace OAI

/-! Regular convolution operators, product lists with multiplicity,
and sparse splitting from a contracting average. -/
noncomputable section
namespace Dixmier
universe u
open Finset
attribute [local instance] Classical.propDecidable

variable {G : Type*}

variable [Group G]

theorem rightRegular_norm_map (t : G) (ξ : ScalarL2 G) : ‖rightRegular t ξ‖ = ‖ξ‖ :=
  reindexL2_norm (Equiv.mulRight t) ξ

end Dixmier

end

end OAI

-- ---- from OAI.Analysis.Unitarizability.VectorMean ----
namespace OAI

/-! Vector means and their translation error bounds. -/
noncomputable section
namespace Dixmier
open scoped BoundedContinuousFunction
variable {G : Type*} [Group G] [TopologicalSpace G]

theorem vectorMean_one (ξ : ScalarL2 G) :
    vectorMean ξ (BoundedContinuousFunction.const G 1) = (‖ξ‖ ^ 2 : ℝ) := by
  simp only [vectorMean_apply, vectorMeanValue, BoundedContinuousFunction.const_apply, mul_one]
  rw [← Complex.ofReal_tsum, ← l2_norm_sq]

theorem vectorMean_opNorm_le (ξ : ScalarL2 G) : ‖vectorMean ξ‖ ≤ ‖ξ‖ ^ 2 :=
  ContinuousLinearMap.opNorm_le_bound _ (sq_nonneg _) (vectorMean_norm_le ξ)

theorem vectorMean_positive (ξ : ScalarL2 G) (b : G →ᵇ ℂ)
    (hb : ∀ x, 0 ≤ (b x).re ∧ (b x).im = 0) :
    0 ≤ (vectorMean ξ b).re ∧ (vectorMean ξ b).im = 0 := by
  change 0 ≤ (∑' x, (‖ξ x‖ ^ 2 : ℝ) * b (x⁻¹)).re ∧
    (∑' x, (‖ξ x‖ ^ 2 : ℝ) * b (x⁻¹)).im = 0
  rw [Complex.re_tsum (vectorMean_summable ξ b), Complex.im_tsum (vectorMean_summable ξ b)]
  constructor
  · apply tsum_nonneg
    intro x
    simpa only [← Complex.ofReal_pow, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] using mul_nonneg (sq_nonneg ‖ξ x‖) (hb x⁻¹).1
  · simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, zero_add, fun x => (hb x).2, mul_zero, tsum_zero]

theorem vectorMean_translate [DiscreteTopology G] (ξ : ScalarL2 G) (g : G) (b : G →ᵇ ℂ) :
    vectorMean ξ (leftTranslate g b) = vectorMean (rightRegular g⁻¹ ξ) b := by
  change (∑' x, (‖ξ x‖ ^ 2 : ℝ) * b (g⁻¹ * x⁻¹)) =
    ∑' x, (‖ξ (x * g⁻¹)‖ ^ 2 : ℝ) * b x⁻¹
  rw [← (Equiv.mulRight g).tsum_eq (fun x => (‖ξ (x * g⁻¹)‖ ^ 2 : ℝ) * b x⁻¹)]
  simp [mul_assoc]

theorem vectorMean_difference_bound (ξ η : ScalarL2 G) (b : G →ᵇ ℂ) :
    ‖vectorMean ξ b - vectorMean η b‖ ≤ ‖ξ - η‖ * (‖ξ‖ + ‖η‖) * ‖b‖ := by
  let f : G → ℂ := fun x => ((‖ξ x‖^2 - ‖η x‖^2 : ℝ) : ℂ) * b x⁻¹
  have hf : Summable f := ((vectorMean_summable ξ b).sub (vectorMean_summable η b)).congr
    (fun x => by dsimp [f]; push_cast; ring)
  have he : vectorMean ξ b - vectorMean η b = ∑' x, f x := by
    rw [vectorMean_apply, vectorMean_apply, vectorMeanValue, vectorMeanValue,
      ← (vectorMean_summable ξ b).tsum_sub (vectorMean_summable η b)]
    apply tsum_congr
    intro x
    dsimp [f]
    push_cast
    ring
  have hsq := l2_square_difference_bound ξ η
  have hb : ∀ x, ‖f x‖ ≤ |‖ξ x‖^2 - ‖η x‖^2| * ‖b‖ := by
    intro x
    dsimp [f]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (b.norm_coe_le_norm _) (abs_nonneg _)
  rw [he]
  calc
    ‖∑' x, f x‖ ≤ ∑' x, ‖f x‖ := norm_tsum_le_tsum_norm hf.norm
    _ ≤ ∑' x, |‖ξ x‖^2 - ‖η x‖^2| * ‖b‖ :=
      Summable.tsum_le_tsum hb hf.norm (hsq.1.mul_right ‖b‖)
    _ = (∑' x, |‖ξ x‖^2 - ‖η x‖^2|) * ‖b‖ := tsum_mul_right
    _ ≤ ‖ξ - η‖ * (‖ξ‖ + ‖η‖) * ‖b‖ := mul_le_mul_of_nonneg_right hsq.2 (norm_nonneg _)

/-- The vector-mean translation error estimate. -/
theorem vectorMean_translation_bound [DiscreteTopology G] (ξ : ScalarL2 G) (hξ : ‖ξ‖ = 1)
    (g : G) (b : G →ᵇ ℂ) :
    ‖vectorMean ξ (leftTranslate g b) - vectorMean ξ b‖ ≤
      2 * ‖b‖ * ‖rightRegular g⁻¹ ξ - ξ‖ := by
  rw [vectorMean_translate]
  have h := vectorMean_difference_bound (rightRegular g⁻¹ ξ) ξ b
  rw [rightRegular_norm_map, hξ] at h
  nlinarith

end Dixmier

end

end OAI

-- ---- from OAI.Analysis.Unitarizability.Contracting ----
namespace OAI

/-! Contracting averages and sparse splitting for nonamenable groups. -/
noncomputable section
namespace Dixmier
open Finset
open scoped BoundedContinuousFunction
variable {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]

/-- Contrapositive analytic argument using the invariant-mean definition. -/
theorem amenable_of_all_sum_norm
    (h : ∀ S : Finset G, 1 ∈ S → ‖∑ g ∈ S, rightRegular g‖ = (S.card : ℝ)) :
    Amenable G := by
  classical
  apply amenable_of_approximate_means
  intro S ε hε
  let T := insert 1 (S.image fun g => g⁻¹)
  have h1 : (1 : G) ∈ T := mem_insert_self _ _
  obtain ⟨ξ, hξ, hinv⟩ := almost_invariant_of_sum_norm T h1 (h T h1)
    (show 0 < ε / 2 by positivity)
  refine ⟨vectorMean ξ, ?_, ?_, vectorMean_positive ξ, ?_⟩
  · simpa [hξ] using vectorMean_opNorm_le ξ
  · rw [vectorMean_one, hξ]
    norm_num
  · intro g hg b
    have hg' : g⁻¹ ∈ T := mem_insert_of_mem (mem_image.mpr ⟨g, hg, rfl⟩)
    have hb := vectorMean_translation_bound ξ hξ g b
    have hi := hinv g⁻¹ hg'
    calc
      ‖vectorMean ξ (leftTranslate g b) - vectorMean ξ b‖ ≤ 2 * ‖b‖ * ‖rightRegular g⁻¹ ξ - ξ‖ := hb
      _ ≤ 2 * ‖b‖ * (ε / 2) := mul_le_mul_of_nonneg_left hi.le (by positivity)
      _ = ε * ‖b‖ := by ring

end Dixmier

end

end OAI

-- ---- platform node ----
open OAI OAI.Dixmier
open Finset
open scoped BoundedContinuousFunction
variable {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]

theorem solution
    (h : ∀ S : Finset G, 1 ∈ S → ‖∑ g ∈ S, rightRegular g‖ = (S.card : ℝ)) :
    Amenable G := by
  first
    | exact OAI.Dixmier.amenable_of_all_sum_norm h
    | exact OAI.Dixmier.amenable_of_all_sum_norm
    | (apply OAI.Dixmier.amenable_of_all_sum_norm <;> assumption)
    | (intros; apply OAI.Dixmier.amenable_of_all_sum_norm <;> assumption)
