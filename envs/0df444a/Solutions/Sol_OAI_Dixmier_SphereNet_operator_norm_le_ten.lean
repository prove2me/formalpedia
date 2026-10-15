-- Prove2me | solution 1 for OAI.Dixmier.SphereNet.operator_norm_le_ten
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T01:44:01.377066+00:00
-- url     : https://prove2.me/submissions/55208dd4-e19c-4fc9-8e9b-8bb2a6020743

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Unitarizability/NetOperator.lean:L14-L47
-- (upload_full_project.md Phase 4): solution for node OAI.Dixmier.SphereNet.operator_norm_le_ten. The node keeps its source
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

-- ---- from OAI.Analysis.Unitarizability.NetOperator ----
namespace OAI

/-! Finite quarter-net tests imply the operator bound 10
for real operators. -/
noncomputable section
namespace Dixmier
namespace SphereNet
variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
variable [InnerProductSpace ℝ E] [InnerProductSpace ℝ F]

/-- The two quarter-net errors each cost at most a quarter of the
operator norm. Tests bounded by 5 therefore give operator norm at most 10. -/
theorem operator_norm_le_ten (M : E →L[ℝ] F) (s : Finset E) (t : Finset F)
    (_hs : ∀ x ∈ s, ‖x‖ = 1) (ht : ∀ y ∈ t, ‖y‖ = 1)
    (hsnet : ∀ x : E, ‖x‖ = 1 → ∃ x₀ ∈ s, ‖x-x₀‖ ≤ (1/4 : ℝ))
    (htnet : ∀ y : F, ‖y‖ = 1 → ∃ y₀ ∈ t, ‖y-y₀‖ ≤ (1/4 : ℝ))
    (hM : ∀ x ∈ s, ∀ y ∈ t, |inner ℝ (M x) y| ≤ 5) : ‖M‖ ≤ 10 := by
  have hb : ‖M‖ ≤ 5 + ‖M‖/2 := by
    apply ContinuousLinearMap.opNorm_le_of_re_inner_le (by positivity)
    intro x y hx hy
    obtain ⟨x₀, hx₀, hdx⟩ := hsnet x hx
    obtain ⟨y₀, hy₀, hdy⟩ := htnet y hy
    have heq : inner ℝ (M x) y = inner ℝ (M x₀) y₀ +
        inner ℝ (M x) (y-y₀) + inner ℝ (M (x-x₀)) y₀ := by
      simp only [map_sub, inner_sub_left, inner_sub_right]
      ring
    have h1 : |inner ℝ (M x) (y-y₀)| ≤ ‖M‖/4 := by
      calc
        _ ≤ ‖M x‖ * ‖y-y₀‖ := norm_inner_le_norm (𝕜 := ℝ) _ _
        _ ≤ (‖M‖ * ‖x‖) * (1/4) := mul_le_mul (M.le_opNorm x) hdy
          (norm_nonneg _) (mul_nonneg (norm_nonneg M) (norm_nonneg x))
        _ = _ := by rw [hx]; ring
    have h2 : |inner ℝ (M (x-x₀)) y₀| ≤ ‖M‖/4 := by
      calc
        _ ≤ ‖M (x-x₀)‖ * ‖y₀‖ := norm_inner_le_norm (𝕜 := ℝ) _ _
        _ = ‖M (x-x₀)‖ := by rw [ht y₀ hy₀, mul_one]
        _ ≤ ‖M‖ * ‖x-x₀‖ := M.le_opNorm _
        _ ≤ ‖M‖ * (1/4) := mul_le_mul_of_nonneg_left hdx (norm_nonneg M)
        _ = _ := by ring
    change inner ℝ (M x) y ≤ 5 + ‖M‖/2
    rw [heq]
    linarith [le_abs_self (inner ℝ (M x₀) y₀), hM x₀ hx₀ y₀ hy₀,
      le_abs_self (inner ℝ (M x) (y-y₀)), le_abs_self (inner ℝ (M (x-x₀)) y₀)]
  linarith

end SphereNet
end Dixmier

end

end OAI

-- ---- platform node ----
open OAI OAI.Dixmier OAI.Dixmier.SphereNet
variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
variable [InnerProductSpace ℝ E] [InnerProductSpace ℝ F]

theorem solution (M : E →L[ℝ] F) (s : Finset E) (t : Finset F)
    (_hs : ∀ x ∈ s, ‖x‖ = 1) (ht : ∀ y ∈ t, ‖y‖ = 1)
    (hsnet : ∀ x : E, ‖x‖ = 1 → ∃ x₀ ∈ s, ‖x-x₀‖ ≤ (1/4 : ℝ))
    (htnet : ∀ y : F, ‖y‖ = 1 → ∃ y₀ ∈ t, ‖y-y₀‖ ≤ (1/4 : ℝ))
    (hM : ∀ x ∈ s, ∀ y ∈ t, |inner ℝ (M x) y| ≤ 5) : ‖M‖ ≤ 10 := by
  first
    | exact OAI.Dixmier.SphereNet.operator_norm_le_ten M s t _hs ht hsnet htnet hM
    | exact OAI.Dixmier.SphereNet.operator_norm_le_ten
    | (apply OAI.Dixmier.SphereNet.operator_norm_le_ten <;> assumption)
    | (intros; apply OAI.Dixmier.SphereNet.operator_norm_le_ten <;> assumption)
