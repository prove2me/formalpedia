-- Prove2me | solution 1 for OAI.TalagrandDiscreteConvexity.Covering.initial_cost_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T16:29:48.257856+00:00
-- url     : https://prove2.me/submissions/1365af9b-29a7-447e-93e1-88dfb97a6b11

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/DiscreteConvexity/CoveringRegularization.lean:L80-L116
-- (upload_full_project.md Phase 4): solution for node OAI.TalagrandDiscreteConvexity.Covering.initial_cost_le. The node keeps its source
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
import Theorems.Thm_OAI_TalagrandDiscreteConvexity_Covering_weighted_incidence_count

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

omit [Fintype V] in
theorem weightedDegree_nonneg {H : Family V} {rho : ℝ} {r : ℕ} {I : Finset V}
    (hρ : 0 ≤ rho) : 0 ≤ weightedDegree H rho r I := by
  classical
  exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hρ _)

/-- The initial generators cost at most their weighted-incidence budget divided
by the high-degree threshold. -/
theorem initial_cost_le {H : Family V} {rho T : ℝ} {r : ℕ}
    (hρ : 0 ≤ rho) (hT : 0 < T) (hH : ∀ e ∈ H, e.card = r) :
    cost rho (initialFamily H rho r T) ≤
      T⁻¹ * (2 : ℝ) ^ r * (H.card : ℝ) * rho ^ r := by
  classical
  let K : Finset (Finset V) := Finset.univ.filter (fun I => I.card ≤ r)
  have hsub : initialFamily H rho r T ⊆ K := by
    intro I hI
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (mem_initialFamily.mp hI).1⟩
  have hbudget : T * cost rho (initialFamily H rho r T) ≤
      (2 : ℝ) ^ r * (H.card : ℝ) * rho ^ r := by
    calc
      T * cost rho (initialFamily H rho r T) =
          ∑ I ∈ initialFamily H rho r T, T * rho ^ I.card := by
        rw [cost, Finset.mul_sum]
      _ ≤ ∑ I ∈ initialFamily H rho r T,
          weightedDegree H rho r I * rho ^ I.card := by
        apply Finset.sum_le_sum
        intro I hI
        exact mul_le_mul_of_nonneg_right (mem_initialFamily.mp hI).2.le
          (pow_nonneg hρ _)
      _ ≤ ∑ I ∈ K, weightedDegree H rho r I * rho ^ I.card := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsub
        intro I _ _
        exact mul_nonneg (weightedDegree_nonneg hρ) (pow_nonneg hρ _)
      _ = (2 : ℝ) ^ r * (H.card : ℝ) * rho ^ r :=
        weighted_incidence_count H rho r hH
  calc
    cost rho (initialFamily H rho r T) ≤
        ((2 : ℝ) ^ r * (H.card : ℝ) * rho ^ r) / T := by
      apply (le_div_iff₀ hT).mpr
      simpa only [mul_comm] using hbudget
    _ = T⁻¹ * (2 : ℝ) ^ r * (H.card : ℝ) * rho ^ r := by
      rw [div_eq_mul_inv]
      ac_rfl

end TalagrandDiscreteConvexity.Covering

end OAI

-- ---- platform node ----
open OAI OAI.TalagrandDiscreteConvexity OAI.TalagrandDiscreteConvexity.Covering
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.TalagrandDiscreteConvexity.Covering.initial_cost_le := @_root_.OAI.TalagrandDiscreteConvexity.Covering.initial_cost_le
