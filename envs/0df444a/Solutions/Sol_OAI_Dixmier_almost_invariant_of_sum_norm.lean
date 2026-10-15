-- Prove2me | solution 1 for OAI.Dixmier.almost_invariant_of_sum_norm
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T01:38:32.366811+00:00
-- url     : https://prove2.me/submissions/ab982a20-b924-4ff1-9963-a285affd7966

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Unitarizability/Average.lean:L56-L82
-- (upload_full_project.md Phase 4): solution for node OAI.Dixmier.almost_invariant_of_sum_norm. The node keeps its source
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
import Theorems.Thm_OAI_Dixmier_sum_pairwise_sq

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

-- ---- from OAI.Analysis.Unitarizability.Average ----
namespace OAI

/-! Finite-average identities for contracting averages in Hilbert spaces. -/
noncomputable section
namespace Dixmier
open Finset
open scoped ComplexConjugate
variable {H I : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

omit [InnerProductSpace ℂ H] in
/-- A chosen pair contributes at most the total squared defect. -/
theorem pairwise_sq_le_sum (S : Finset I) (v : I → H) {i j : I}
    (hi : i ∈ S) (hj : j ∈ S) :
    ‖v i - v j‖ ^ 2 ≤ ∑ a ∈ S, ∑ b ∈ S, ‖v a - v b‖ ^ 2 := by
  exact (Finset.single_le_sum (fun b _ => sq_nonneg ‖v i - v b‖) hj).trans
    (Finset.single_le_sum (fun a _ => Finset.sum_nonneg (s := S) (fun b _ => sq_nonneg ‖v a - v b‖)) hi)

variable {G : Type*} [Group G]
/-- Defect in a finite sum of right translations of a unit vector. -/
theorem regular_sum_variance (S : Finset G) (ξ : ScalarL2 G) (hξ : ‖ξ‖ = 1) :
    ∑ g ∈ S, ∑ h ∈ S, ‖rightRegular g ξ - rightRegular h ξ‖ ^ 2 =
      2 * ((S.card : ℝ) ^ 2 - ‖∑ g ∈ S, rightRegular g ξ‖ ^ 2) := by
  rw [sum_pairwise_sq]
  simp only [rightRegular_norm_map, hξ, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one]
  ring

/-- A norm-one vector witnessing any strict lower bound for an operator norm. -/
theorem exists_unit_near_opNorm (A : H →L[ℂ] H) {c : ℝ}
    (hc : 0 ≤ c) (hA : c < ‖A‖) : ∃ ξ : H, ‖ξ‖ = 1 ∧ c < ‖A ξ‖ := by
  by_contra h
  push Not at h
  exact (not_le_of_gt hA) (ContinuousLinearMap.opNorm_le_of_unit_norm hc h)

/-- The norm-one-average hypothesis yields simultaneous almost invariance. -/
theorem almost_invariant_of_sum_norm (S : Finset G) (h1 : (1 : G) ∈ S)
    (hS : ‖∑ g ∈ S, rightRegular g‖ = (S.card : ℝ))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ ξ : ScalarL2 G, ‖ξ‖ = 1 ∧ ∀ g ∈ S, ‖rightRegular g ξ - ξ‖ < ε := by
  have hd : (0 : ℝ) < S.card := by exact_mod_cast Finset.card_pos.mpr ⟨1, h1⟩
  let c := Real.sqrt (max 0 ((S.card : ℝ)^2 - ε^2/2))
  have hc : 0 ≤ c := Real.sqrt_nonneg _
  have hc2 : c^2 = max 0 ((S.card : ℝ)^2 - ε^2/2) :=
    Real.sq_sqrt (le_max_left _ _)
  have hcd : c < (S.card : ℝ) := by
    have hm : max 0 ((S.card : ℝ)^2 - ε^2/2) < (S.card : ℝ)^2 :=
      max_lt (sq_pos_of_pos hd) (by nlinarith [sq_pos_of_pos hε])
    nlinarith
  obtain ⟨ξ, hξ, hclose⟩ := exists_unit_near_opNorm
    (∑ g ∈ S, rightRegular g) hc (by rwa [hS])
  have hclose' : c < ‖∑ g ∈ S, rightRegular g ξ‖ := by
    simpa only [_root_.sum_apply] using hclose
  have hdefect : 2 * ((S.card : ℝ)^2 - ‖∑ g ∈ S, rightRegular g ξ‖^2) < ε^2 := by
    have hm := le_max_right 0 ((S.card : ℝ)^2 - ε^2/2)
    nlinarith [norm_nonneg (∑ g ∈ S, rightRegular g ξ)]
  refine ⟨ξ, hξ, fun g hg => ?_⟩
  have hp := pairwise_sq_le_sum S (fun g => rightRegular g ξ) hg h1
  rw [regular_sum_variance S ξ hξ] at hp
  have he : rightRegular (1 : G) ξ = ξ := by ext x; simp
  rw [he] at hp
  nlinarith [norm_nonneg (rightRegular g ξ - ξ)]

end Dixmier

end

end OAI

-- ---- platform node ----
open OAI OAI.Dixmier
open Finset
open scoped ComplexConjugate
variable {H I : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {G : Type*} [Group G]

theorem solution (S : Finset G) (h1 : (1 : G) ∈ S)
    (hS : ‖∑ g ∈ S, rightRegular g‖ = (S.card : ℝ))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ ξ : ScalarL2 G, ‖ξ‖ = 1 ∧ ∀ g ∈ S, ‖rightRegular g ξ - ξ‖ < ε := by
  first
    | exact OAI.Dixmier.almost_invariant_of_sum_norm S h1 hS hε
    | exact OAI.Dixmier.almost_invariant_of_sum_norm
    | (apply OAI.Dixmier.almost_invariant_of_sum_norm <;> assumption)
    | (intros; apply OAI.Dixmier.almost_invariant_of_sum_norm <;> assumption)
