-- Prove2me | solution 1 for OAI.TalagrandDiscreteConvexity.Covering.regular_intersection_sum_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T16:30:43.537402+00:00
-- url     : https://prove2.me/submissions/5965aaac-f0f4-4463-9f2b-e09c0d0d76cb

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/DiscreteConvexity/CoveringRegularization.lean:L130-L172
-- (upload_full_project.md Phase 4): solution for node OAI.TalagrandDiscreteConvexity.Covering.regular_intersection_sum_le. The node keeps its source
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

/-- Actual survival implies the weighted-degree bound at every subset of the
surviving edge. -/
theorem regular_weightedDegree_le {H : Family V} {rho T : ℝ} {r : ℕ}
    (hH : ∀ e ∈ H, e.card = r) {e I : Finset V}
    (he : e ∈ regularEdges H rho r T) (hIe : I ⊆ e) :
    weightedDegree H rho r I ≤ T := by
  have heH : e ∈ H := (mem_regularEdges.mp he).1
  have hIr : I.card ≤ r := (Finset.card_le_card hIe).trans_eq (hH e heH)
  apply le_of_not_gt
  intro hlarge
  exact (mem_regularEdges.mp he).2 I (mem_initialFamily.mpr ⟨hIr, hlarge⟩) hIe

/-- Each nonempty intersection class contributes at most `T`, and the empty
classes contribute zero. -/
private theorem regular_intersection_sum_le {H : Family V} {rho T : ℝ} {r : ℕ}
    (hρ : 0 ≤ rho) (hT : 0 ≤ T) (hH : ∀ e ∈ H, e.card = r)
    (B I : Finset V) :
    (∑ e ∈ (regularEdges H rho r T).filter (fun e => e ∩ B = I),
      rho ^ (e \ B).card) ≤ T := by
  classical
  let F := (regularEdges H rho r T).filter (fun e => e ∩ B = I)
  by_cases hne : F.Nonempty
  · obtain ⟨e₀, he₀⟩ := hne
    have he₀reg := (Finset.mem_filter.mp he₀).1
    have he₀I : e₀ ∩ B = I := (Finset.mem_filter.mp he₀).2
    have hIe₀ : I ⊆ e₀ := by rw [← he₀I]; exact Finset.inter_subset_left
    have hdegree := regular_weightedDegree_le hH he₀reg hIe₀
    have hsub : F ⊆ H.filter (fun e => I ⊆ e) := by
      intro e he
      obtain ⟨hereg, heI⟩ := Finset.mem_filter.mp he
      refine Finset.mem_filter.mpr ⟨(mem_regularEdges.mp hereg).1, ?_⟩
      rw [← heI]
      exact Finset.inter_subset_left
    have hcards : (F.card : ℝ) ≤ ((H.filter (fun e => I ⊆ e)).card : ℝ) :=
      Nat.cast_le.mpr (Finset.card_le_card hsub)
    calc
      (∑ e ∈ F, rho ^ (e \ B).card) = (F.card : ℝ) * rho ^ (r - I.card) := by
        calc
          (∑ e ∈ F, rho ^ (e \ B).card) = ∑ _e ∈ F, rho ^ (r - I.card) := by
            apply Finset.sum_congr rfl
            intro e he
            obtain ⟨hereg, heI⟩ := Finset.mem_filter.mp he
            have hecard := hH e (mem_regularEdges.mp hereg).1
            have hpartition := Finset.card_sdiff_add_card_inter e B
            rw [heI, hecard] at hpartition
            have hdiff : (e \ B).card = r - I.card := by omega
            rw [hdiff]
          _ = (F.card : ℝ) * rho ^ (r - I.card) := by simp
      _ ≤ weightedDegree H rho r I :=
        mul_le_mul_of_nonneg_right hcards (pow_nonneg hρ _)
      _ ≤ T := hdegree
  · have hF : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    change (∑ e ∈ F, rho ^ (e \ B).card) ≤ T
    rw [hF, Finset.sum_empty]
    exact hT

end TalagrandDiscreteConvexity.Covering

end OAI

-- ---- platform node ----
open OAI OAI.TalagrandDiscreteConvexity OAI.TalagrandDiscreteConvexity.Covering
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.TalagrandDiscreteConvexity.Covering.regular_intersection_sum_le := @_root_.OAI.TalagrandDiscreteConvexity.Covering.regular_intersection_sum_le
