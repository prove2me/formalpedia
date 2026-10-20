-- Prove2me | solution 1 for OAI.TalagrandDiscreteConvexity.subset_power_sum_le_bins
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T16:26:23.611648+00:00
-- url     : https://prove2.me/submissions/41a817a9-1448-4827-800f-6527b3f5da4b

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/DiscreteConvexity/Bins.lean:L134-L163
-- (upload_full_project.md Phase 4): solution for node OAI.TalagrandDiscreteConvexity.subset_power_sum_le_bins. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Pow
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Definitions.Def_TalagrandDiscreteConvexity
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_Model
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_Basic
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_DyadicBins
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_FiniteFibers
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_Bins

-- ---- from OAI.Combinatorics.DiscreteConvexity.FiniteFibers ----
namespace OAI

/-!
# Finite partitions by a key

The fibers indexed by the image of a finite source partition that source.
Filtering the source commutes with taking fibers, so the same partition
identities apply to restrictions of a weighted sum.
-/

namespace TalagrandDiscreteConvexity.FiniteFibers

open scoped BigOperators

variable {α β M : Type*} [DecidableEq β]

/-- Restricting the source commutes with taking a fiber. -/
theorem filter_fiber (A : Finset α) (key : α → β) (b : β)
    (P : α → Prop) [DecidablePred P] :
    fiber (A.filter P) key b = (fiber A key b).filter P :=
  Finset.filter_comm P (fun a => key a = b) A

variable [AddCommMonoid M]

/-- The same partition identity after restricting every fiber by a predicate. -/
theorem sum_filter_fibers (A : Finset α) (key : α → β)
    (P : α → Prop) [DecidablePred P] (f : α → M) :
    (∑ b ∈ keys A key, ∑ a ∈ (fiber A key b).filter P, f a) =
      ∑ a ∈ A.filter P, f a := by
  calc
    (∑ b ∈ keys A key, ∑ a ∈ (fiber A key b).filter P, f a) =
        ∑ b ∈ keys A key, ∑ a ∈ fiber (A.filter P) key b, f a := by
      simp only [filter_fiber]
    _ = ∑ a ∈ A.filter P, f a := by
      exact Finset.sum_fiberwise_of_maps_to
        (fun a ha => Finset.mem_image_of_mem key (Finset.mem_filter.mp ha).1) f

/-- A restricted sum decomposed into the bins of the original source. -/
theorem sum_filter_eq_sum_fibers (A : Finset α) (key : α → β)
    (P : α → Prop) [DecidablePred P] (f : α → M) :
    (∑ a ∈ A.filter P, f a) =
      ∑ b ∈ keys A key, ∑ a ∈ (fiber A key b).filter P, f a :=
  (sum_filter_fibers A key P f).symm

end TalagrandDiscreteConvexity.FiniteFibers

end OAI

-- ---- from OAI.Combinatorics.DiscreteConvexity.Bins ----
namespace OAI

open scoped BigOperators

namespace TalagrandDiscreteConvexity

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Removing zero weights and partitioning the remainder is a finite identity. -/
theorem subset_power_sum_le_bins {W : Finset α → ℝ} (hW : ∀ U, 0 ≤ W U)
    (S : Finset α) (hlarge : ∀ U ∈ largeWeightFamily W, ¬ U ⊆ S) :
    (∑ U ∈ S.powerset.erase ∅, (W U) ^ 16) ≤
      ∑ b ∈ occupiedWeightBins W,
        ∑ U ∈ (weightBin W b).filter (fun U => U ⊆ S), (W U) ^ 16 := by
  classical
  let A := S.powerset.erase ∅
  have hzero : (∑ U ∈ A, (W U) ^ 16) =
      ∑ U ∈ A.filter (fun U => 0 < W U), (W U) ^ 16 := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro U hU hnot
    have hn : ¬ 0 < W U := fun h => hnot (Finset.mem_filter.mpr ⟨hU, h⟩)
    have hz : W U = 0 := le_antisymm (le_of_not_gt hn) (hW U)
    simp [hz]
  have hsub : A.filter (fun U => 0 < W U) ⊆
      (smallWeightFamily W).filter (fun U => U ⊆ S) := by
    intro U hU
    obtain ⟨hUA, hpos⟩ := Finset.mem_filter.mp hU
    obtain ⟨hne, hUS⟩ := Finset.mem_erase.mp hUA
    have hsubset : U ⊆ S := Finset.mem_powerset.mp hUS
    refine Finset.mem_filter.mpr ⟨mem_smallWeightFamily.mpr ⟨hne, hpos, ?_⟩, hsubset⟩
    by_contra hlt
    exact hlarge U (mem_largeWeightFamily.mpr ⟨hne, le_of_not_gt hlt⟩) hsubset
  calc
    _ = ∑ U ∈ A.filter (fun U => 0 < W U), (W U) ^ 16 := hzero
    _ ≤ ∑ U ∈ (smallWeightFamily W).filter (fun U => U ⊆ S), (W U) ^ 16 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun U _ _ => pow_nonneg (hW U) _)
    _ = _ := FiniteFibers.sum_filter_eq_sum_fibers _ _ _ _

end TalagrandDiscreteConvexity

end OAI

-- ---- platform node ----
open OAI OAI.TalagrandDiscreteConvexity
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.TalagrandDiscreteConvexity.subset_power_sum_le_bins := @_root_.OAI.TalagrandDiscreteConvexity.subset_power_sum_le_bins
