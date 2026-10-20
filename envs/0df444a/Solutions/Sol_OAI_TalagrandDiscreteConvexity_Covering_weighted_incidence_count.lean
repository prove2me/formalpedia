-- Prove2me | solution 1 for OAI.TalagrandDiscreteConvexity.Covering.weighted_incidence_count
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T16:29:06.6033+00:00
-- url     : https://prove2.me/submissions/fd3ac8a4-30cd-4dd7-9a69-6962aeca1b87

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/DiscreteConvexity/CoveringRegularization.lean:L56-L78
-- (upload_full_project.md Phase 4): solution for node OAI.TalagrandDiscreteConvexity.Covering.weighted_incidence_count. The node keeps its source
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
import Theorems.Thm_OAI_TalagrandDiscreteConvexity_Covering_incidence_count

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

/-- The weighted incidence identity is valid even at `rho = 0`. -/
theorem weighted_incidence_count (H : Family V) (rho : ℝ) (r : ℕ)
    (hH : ∀ e ∈ H, e.card = r) :
    (∑ I ∈ Finset.univ.filter (fun I : Finset V => I.card ≤ r),
      weightedDegree H rho r I * rho ^ I.card) =
      (2 : ℝ) ^ r * (H.card : ℝ) * rho ^ r := by
  classical
  let K : Finset (Finset V) := Finset.univ.filter (fun I => I.card ≤ r)
  have hcast : (∑ I ∈ K, ((H.filter (fun e => I ⊆ e)).card : ℝ)) =
      (H.card : ℝ) * (2 : ℝ) ^ r := by
    simpa only [Nat.cast_sum, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using
      congrArg (fun n : ℕ => (n : ℝ)) (incidence_count H r hH)
  calc
    (∑ I ∈ K, weightedDegree H rho r I * rho ^ I.card) =
        (∑ I ∈ K, ((H.filter (fun e => I ⊆ e)).card : ℝ)) * rho ^ r := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro I hI
      have hIr : I.card ≤ r := (Finset.mem_filter.mp hI).2
      rw [weightedDegree, mul_assoc, ← pow_add, Nat.sub_add_cancel hIr]
    _ = ((H.card : ℝ) * (2 : ℝ) ^ r) * rho ^ r := by rw [hcast]
    _ = (2 : ℝ) ^ r * (H.card : ℝ) * rho ^ r := by
      rw [mul_comm (H.card : ℝ) ((2 : ℝ) ^ r)]

end TalagrandDiscreteConvexity.Covering

end OAI

-- ---- platform node ----
open OAI OAI.TalagrandDiscreteConvexity OAI.TalagrandDiscreteConvexity.Covering
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.TalagrandDiscreteConvexity.Covering.weighted_incidence_count := @_root_.OAI.TalagrandDiscreteConvexity.Covering.weighted_incidence_count
