-- Prove2me | solution 1 for OAI.TalagrandDiscreteConvexity.Covering.incidence_count
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T16:27:52.976179+00:00
-- url     : https://prove2.me/submissions/269973e5-45a0-4a3c-a4cb-6a0198fb7cf5

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/DiscreteConvexity/CoveringRegularization.lean:L23-L48
-- (upload_full_project.md Phase 4): solution for node OAI.TalagrandDiscreteConvexity.Covering.incidence_count. The node keeps its source
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

/-- Count incidences between edges and subsets of cardinality at most `r`. -/
theorem incidence_count (H : Family V) (r : ℕ)
    (hH : ∀ e ∈ H, e.card = r) :
    (∑ I ∈ Finset.univ.filter (fun I : Finset V => I.card ≤ r),
      (H.filter (fun e => I ⊆ e)).card) = H.card * 2 ^ r := by
  classical
  let K : Finset (Finset V) := Finset.univ.filter (fun I => I.card ≤ r)
  have hbelow (e : Finset V) (he : e ∈ H) :
      K.filter (fun I => I ⊆ e) = e.powerset := by
    apply Finset.ext
    intro I
    simp only [K, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_powerset]
    constructor
    · exact fun h => h.2
    · intro hIe
      exact ⟨(Finset.card_le_card hIe).trans_eq (hH e he), hIe⟩
  calc
    (∑ I ∈ K, (H.filter (fun e => I ⊆ e)).card) =
        ∑ e ∈ H, (K.filter (fun I => I ⊆ e)).card := by
      exact Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
        (fun I e : Finset V => I ⊆ e)
    _ = ∑ _e ∈ H, 2 ^ r := by
      apply Finset.sum_congr rfl
      intro e he
      rw [hbelow e he, Finset.card_powerset, hH e he]
    _ = H.card * 2 ^ r := by simp

end TalagrandDiscreteConvexity.Covering

end OAI

-- ---- platform node ----
open OAI OAI.TalagrandDiscreteConvexity OAI.TalagrandDiscreteConvexity.Covering
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.TalagrandDiscreteConvexity.Covering.incidence_count := @_root_.OAI.TalagrandDiscreteConvexity.Covering.incidence_count
