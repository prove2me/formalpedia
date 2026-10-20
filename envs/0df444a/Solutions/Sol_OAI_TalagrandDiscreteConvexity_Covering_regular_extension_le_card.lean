-- Prove2me | solution 1 for OAI.TalagrandDiscreteConvexity.Covering.regular_extension_le_card
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T16:31:26.821786+00:00
-- url     : https://prove2.me/submissions/95df8c93-e7ba-45f7-a579-e9cdc9de77ab

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/DiscreteConvexity/CoveringRegularization.lean:L174-L196
-- (upload_full_project.md Phase 4): solution for node OAI.TalagrandDiscreteConvexity.Covering.regular_extension_le_card. The node keeps its source
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
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_CoveringBasic
import Theorems.Thm_OAI_TalagrandDiscreteConvexity_Covering_regular_intersection_sum_le

-- ---- from OAI.Combinatorics.DiscreteConvexity.CoveringRegularization ----
namespace OAI

/-!
# Weighted-degree regularization

The initial family is the actual family of high weighted-degree subsets.
Double counting bounds its cost. An edge surviving this deletion has bounded
weighted degree at every one of its subsets. Grouping surviving edges by their
intersection with `B` gives the extension estimates used for pair sampling and
for residual tuples. No regularity property is assumed separately.
-/

namespace TalagrandDiscreteConvexity.Covering

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Extension cost for actual regular edges, with the exact number of possible
intersections with `B`. -/
theorem regular_extension_le_card {H : Family V} {rho T : ℝ} {r : ℕ}
    (hρ : 0 ≤ rho) (hT : 0 ≤ T) (hH : ∀ e ∈ H, e.card = r) (B : Finset V) :
    (∑ e ∈ regularEdges H rho r T, rho ^ (e \ B).card) ≤
      T * ((B.powerset.filter (fun I => I.card ≤ r)).card : ℝ) := by
  classical
  let D := B.powerset.filter (fun I => I.card ≤ r)
  have hmap : ∀ e ∈ regularEdges H rho r T, e ∩ B ∈ D := by
    intro e he
    refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr Finset.inter_subset_right, ?_⟩
    exact (Finset.card_le_card Finset.inter_subset_left).trans_eq
      (hH e (mem_regularEdges.mp he).1)
  calc
    (∑ e ∈ regularEdges H rho r T, rho ^ (e \ B).card) =
        ∑ I ∈ D, ∑ e ∈ (regularEdges H rho r T).filter (fun e => e ∩ B = I),
          rho ^ (e \ B).card :=
      (Finset.sum_fiberwise_of_maps_to hmap (fun e => rho ^ (e \ B).card)).symm
    _ ≤ ∑ _I ∈ D, T := by
      apply Finset.sum_le_sum
      intro I _
      exact regular_intersection_sum_le hρ hT hH B I
    _ = T * (D.card : ℝ) := by simp [mul_comm]

end TalagrandDiscreteConvexity.Covering

end OAI

-- ---- platform node ----
open OAI OAI.TalagrandDiscreteConvexity OAI.TalagrandDiscreteConvexity.Covering
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.TalagrandDiscreteConvexity.Covering.regular_extension_le_card := @_root_.OAI.TalagrandDiscreteConvexity.Covering.regular_extension_le_card
