-- Prove2me | solution 1 for OAI.Dixmier.exists_contracting_sum
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T01:41:28.900545+00:00
-- url     : https://prove2.me/submissions/1c4076b9-956c-4bc5-bd70-244903292f92

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Unitarizability/Contracting.lean:L54-L77
-- (upload_full_project.md Phase 4): solution for node OAI.Dixmier.exists_contracting_sum. The node keeps its source
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
import Theorems.Thm_OAI_Dixmier_amenable_of_all_sum_norm

-- ---- from OAI.Analysis.Unitarizability.SparseSplitting ----
namespace OAI

/-! Spectral norm bounds imply sparse endpoint assignments.
The input is a bounded convolution operator with its coefficient formula. -/
noncomputable section
namespace Dixmier
open Finset
open scoped InnerProductSpace
attribute [local instance] Classical.propDecidable
variable {G I : Type*} [Fintype I]

theorem indicatorL2_norm_sq (U : Finset G) : ‖indicatorL2 U‖ ^ 2 = U.card := by
  have h := lp.norm_sum_single (p := 2) (by norm_num) (fun _ : G => (1 : ℂ)) U
  simpa [indicatorL2] using h

theorem indicatorL2_norm (U : Finset G) : ‖indicatorL2 U‖ = Real.sqrt U.card := by
  rw [← indicatorL2_norm_sq, Real.sqrt_sq (norm_nonneg _)]

variable [Group G]

end Dixmier

end

end OAI

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

-- ---- from OAI.Analysis.Unitarizability.Contracting ----
namespace OAI

/-! Contracting averages and sparse splitting for nonamenable groups. -/
noncomputable section
namespace Dixmier
open Finset
open scoped BoundedContinuousFunction
variable {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]

omit [TopologicalSpace G] [DiscreteTopology G] in
theorem rightRegular_opNorm (g : G) : ‖rightRegular g‖ = 1 := by
  classical
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro ξ
    simp [rightRegular_norm_map]
  · have h := (rightRegular g).le_opNorm (indicatorL2 ({1} : Finset G))
    simpa [rightRegular_norm_map, indicatorL2_norm] using h

omit [TopologicalSpace G] [DiscreteTopology G] in
theorem regular_sum_norm_le (S : Finset G) :
    ‖∑ g ∈ S, rightRegular g‖ ≤ (S.card : ℝ) := by
  calc
    ‖∑ g ∈ S, rightRegular g‖ ≤ ∑ g ∈ S, ‖rightRegular g‖ := norm_sum_le _ _
    _ = (S.card : ℝ) := by simp [rightRegular_opNorm]

/-- Nonamenability provides a strict contraction after normalization. -/
theorem exists_contracting_sum (hG : ¬ Amenable G) :
    ∃ S : Finset G, 1 ∈ S ∧ 2 ≤ S.card ∧
      ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧ ‖∑ g ∈ S, rightRegular g‖ ≤ (S.card : ℝ) * ρ := by
  classical
  have hex : ∃ S : Finset G, 1 ∈ S ∧ ‖∑ g ∈ S, rightRegular g‖ < (S.card : ℝ) := by
    by_contra hnot
    push Not at hnot
    exact hG (amenable_of_all_sum_norm (fun S h1 => le_antisymm (regular_sum_norm_le S) (hnot S h1)))
  obtain ⟨S, h1, hlt⟩ := hex
  have hd : 0 < S.card := card_pos.mpr ⟨1, h1⟩
  have hd2 : 2 ≤ S.card := by
    by_contra hnot
    have hc : S.card = 1 := by omega
    obtain ⟨g, rfl⟩ := card_eq_one.mp hc
    have hg : g = 1 := by simpa [eq_comm] using h1
    subst g
    simp only [sum_singleton, rightRegular_opNorm, card_singleton, Nat.cast_one, lt_self_iff_false] at hlt
  have hdR : (0 : ℝ) < S.card := by exact_mod_cast hd
  obtain ⟨t, hAt, htd⟩ := exists_between hlt
  have ht : 0 < t := lt_of_le_of_lt (norm_nonneg _) hAt
  refine ⟨S, h1, hd2, t / S.card, div_pos ht hdR, (div_lt_one hdR).mpr htd, ?_⟩
  rw [mul_div_cancel₀ _ hdR.ne']
  exact hAt.le

end Dixmier

end

end OAI

-- ---- platform node ----
open OAI OAI.Dixmier
open Finset
open scoped BoundedContinuousFunction
variable {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]

theorem solution (hG : ¬ Amenable G) :
    ∃ S : Finset G, 1 ∈ S ∧ 2 ≤ S.card ∧
      ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧ ‖∑ g ∈ S, rightRegular g‖ ≤ (S.card : ℝ) * ρ := by
  first
    | exact OAI.Dixmier.exists_contracting_sum hG
    | exact OAI.Dixmier.exists_contracting_sum
    | (apply OAI.Dixmier.exists_contracting_sum <;> assumption)
    | (intros; apply OAI.Dixmier.exists_contracting_sum <;> assumption)
