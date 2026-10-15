-- Prove2me | solution 1 for OAI.Dixmier.amenable_of_approximate_means
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T01:40:00.651616+00:00
-- url     : https://prove2.me/submissions/f279af56-0e10-44fb-9e21-1d86db66cbeb

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Unitarizability/CompactMean.lean:L14-L83
-- (upload_full_project.md Phase 4): solution for node OAI.Dixmier.amenable_of_approximate_means. The node keeps its source
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

-- ---- from OAI.Analysis.Unitarizability.CompactMean ----
namespace OAI

/-! Weak-star compactness for positive normalized invariant means. -/
noncomputable section
namespace Dixmier
open Filter Topology
open scoped BoundedContinuousFunction
variable {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]

/-- Approximate positive normalized means, with all finite translation tests,
have a positive normalized invariant weak-star cluster point. -/
theorem amenable_of_approximate_means
    (h : ∀ (S : Finset G) (ε : ℝ), 0 < ε →
      ∃ m : (G →ᵇ ℂ) →L[ℂ] ℂ,
        ‖m‖ ≤ 1 ∧ m (BoundedContinuousFunction.const G (1 : ℂ)) = 1 ∧
        (∀ b : G →ᵇ ℂ, (∀ x, 0 ≤ (b x).re ∧ (b x).im = 0) →
          0 ≤ (m b).re ∧ (m b).im = 0) ∧
        ∀ g ∈ S, ∀ b : G →ᵇ ℂ, ‖m (leftTranslate g b) - m b‖ ≤ ε * ‖b‖) :
    Amenable G := by
  classical
  let J := Finset G × ℕ
  have hm : ∀ a : J, ∃ m : (G →ᵇ ℂ) →L[ℂ] ℂ,
      ‖m‖ ≤ 1 ∧ m (BoundedContinuousFunction.const G (1 : ℂ)) = 1 ∧
      (∀ b : G →ᵇ ℂ, (∀ x, 0 ≤ (b x).re ∧ (b x).im = 0) →
        0 ≤ (m b).re ∧ (m b).im = 0) ∧
      ∀ g ∈ a.1, ∀ b : G →ᵇ ℂ, ‖m (leftTranslate g b) - m b‖ ≤
        (1 / ((a.2 : ℝ) + 1)) * ‖b‖ := by
    intro a
    exact h a.1 _ (by positivity)
  choose m hm using hm
  let μ : J → WeakDual ℂ (G →ᵇ ℂ) := fun a => StrongDual.toWeakDual (m a)
  have hball : ∀ a, μ a ∈ WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℂ (G →ᵇ ℂ)) 1 := by
    intro a
    change m a ∈ Metric.closedBall 0 1
    simpa [Metric.mem_closedBall, dist_zero_right] using (hm a).1
  obtain ⟨M, _, hM⟩ := (WeakDual.isCompact_closedBall (0 : StrongDual ℂ (G →ᵇ ℂ)) 1).exists_mapClusterPt
    (f := (atTop : Filter J)) (u := μ)
    (by
      rw [Filter.le_principal_iff]
      change ∀ᶠ a in (atTop : Filter J), μ a ∈ WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℂ (G →ᵇ ℂ)) 1
      exact Filter.Eventually.of_forall hball)
  refine ⟨M.toStrongDual.toLinearMap, ?_, ?_, ?_⟩
  · have hc : IsClosed {M : WeakDual ℂ (G →ᵇ ℂ) | M (BoundedContinuousFunction.const G (1 : ℂ)) = 1} :=
      isClosed_eq (WeakDual.eval_continuous _) continuous_const
    exact hc.mem_of_mapClusterPt hM (Filter.Eventually.of_forall (fun a => (hm a).2.1))
  · intro b hb
    have hr : IsClosed {M : WeakDual ℂ (G →ᵇ ℂ) | 0 ≤ (M b).re} :=
      isClosed_le continuous_const (Complex.continuous_re.comp (WeakDual.eval_continuous b))
    have hi : IsClosed {M : WeakDual ℂ (G →ᵇ ℂ) | (M b).im = 0} :=
      isClosed_eq (Complex.continuous_im.comp (WeakDual.eval_continuous b)) continuous_const
    exact (hr.inter hi).mem_of_mapClusterPt hM
      (Filter.Eventually.of_forall (fun a => (hm a).2.2.1 b hb))
  · intro g b
    have hsmall : ∀ ε : ℝ, 0 < ε → ‖M (leftTranslate g b) - M b‖ ≤ ε := by
      intro ε hε
      have hc : IsClosed {M : WeakDual ℂ (G →ᵇ ℂ) | ‖M (leftTranslate g b) - M b‖ ≤ ε} :=
        isClosed_le (((WeakDual.eval_continuous (leftTranslate g b)).sub
        (WeakDual.eval_continuous b)).norm) continuous_const
      apply hc.mem_of_mapClusterPt hM
      obtain ⟨n, hn⟩ := exists_nat_gt (‖b‖ / ε)
      apply Filter.eventually_atTop.mpr
      refine ⟨({g}, n), fun a ha => ?_⟩
      have hg : g ∈ a.1 := ha.1 (Finset.mem_singleton_self g)
      have hna : (n : ℝ) ≤ a.2 := by exact_mod_cast ha.2
      have hpos : (0 : ℝ) < a.2 + 1 := by positivity
      have hbn : ‖b‖ < ε * (n : ℝ) := by
        have := (div_lt_iff₀ hε).mp hn
        nlinarith
      have he : (1 / ((a.2 : ℝ) + 1)) * ‖b‖ ≤ ε := by
        rw [one_div_mul_eq_div]
        apply (div_le_iff₀ hpos).mpr
        nlinarith
      exact ((hm a).2.2.2 g hg b).trans he
    apply sub_eq_zero.mp
    apply norm_eq_zero.mp
    by_contra hne
    have hp : 0 < ‖M (leftTranslate g b) - M b‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
    have := hsmall (‖M (leftTranslate g b) - M b‖ / 2) (by positivity)
    linarith

end Dixmier

end

end OAI

-- ---- platform node ----
open OAI OAI.Dixmier
open Filter Topology
open scoped BoundedContinuousFunction
variable {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]

theorem solution
    (h : ∀ (S : Finset G) (ε : ℝ), 0 < ε →
      ∃ m : (G →ᵇ ℂ) →L[ℂ] ℂ,
        ‖m‖ ≤ 1 ∧ m (BoundedContinuousFunction.const G (1 : ℂ)) = 1 ∧
        (∀ b : G →ᵇ ℂ, (∀ x, 0 ≤ (b x).re ∧ (b x).im = 0) →
          0 ≤ (m b).re ∧ (m b).im = 0) ∧
        ∀ g ∈ S, ∀ b : G →ᵇ ℂ, ‖m (leftTranslate g b) - m b‖ ≤ ε * ‖b‖) :
    Amenable G := by
  first
    | exact OAI.Dixmier.amenable_of_approximate_means h
    | exact OAI.Dixmier.amenable_of_approximate_means
    | (apply OAI.Dixmier.amenable_of_approximate_means <;> assumption)
    | (intros; apply OAI.Dixmier.amenable_of_approximate_means <;> assumption)
