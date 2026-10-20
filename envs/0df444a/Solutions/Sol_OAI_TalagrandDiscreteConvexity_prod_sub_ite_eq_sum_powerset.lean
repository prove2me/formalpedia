-- Prove2me | solution 1 for OAI.TalagrandDiscreteConvexity.prod_sub_ite_eq_sum_powerset
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T16:53:18.216126+00:00
-- url     : https://prove2.me/submissions/62160bf9-af64-4f12-8e39-4eb3680a4e03

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/DiscreteConvexity/ColumnExpansion.lean:L41-L66
-- (upload_full_project.md Phase 4): solution for node OAI.TalagrandDiscreteConvexity.prod_sub_ite_eq_sum_powerset. The node keeps its source
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
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_CoveringSampledFamilies
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_FiniteProbability
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_Bernoulli
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_CoveringResidualTuples
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_CoveringNumericalBounds
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_FourierWeights

-- ---- from OAI.Combinatorics.DiscreteConvexity.ColumnExpansion ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

/-!
# A product expansion on a prescribed set of coordinates

Only coordinates in `S` contribute correction terms.  Expanding their product
therefore gives a sum indexed by `S.powerset`, with the factors outside `S`
left unchanged.
-/

namespace TalagrandDiscreteConvexity

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem prod_ite_split (S U : Finset V) (P C : V → ℝ) (hU : U ⊆ S) :
    (∏ i, if i ∈ U then C i else P i) =
      ((∏ i ∈ U, C i) * ∏ i ∈ S \ U, P i) * ∏ i ∈ Sᶜ, P i := by
  calc
    (∏ i, if i ∈ U then C i else P i) =
        (∏ i ∈ S, if i ∈ U then C i else P i) *
          ∏ i ∈ Sᶜ, if i ∈ U then C i else P i :=
      (Finset.prod_mul_prod_compl S _).symm
    _ = ((∏ i ∈ U, C i) * ∏ i ∈ S \ U, P i) * ∏ i ∈ Sᶜ, P i := by
      congr 1
      · simpa only [Finset.piecewise, Finset.inter_eq_right.mpr hU] using
          Finset.prod_piecewise S U C P
      · apply Finset.prod_congr rfl
        intro i hi
        have hiU : i ∉ U := fun h => (Finset.mem_compl.mp hi) (hU h)
        simp only [ite_eq_right hiU]

/-- Expand a product with correction terms restricted to `S`. -/
theorem prod_sub_ite_eq_sum_powerset (S : Finset V) (P C : V → ℝ) :
    (∏ i, (P i - if i ∈ S then C i else 0)) =
      ∑ U ∈ S.powerset, (-1 : ℝ) ^ U.card * ∏ i, if i ∈ U then C i else P i := by
  have hsplit :
      (∏ i, (P i - if i ∈ S then C i else 0)) =
        (∏ i ∈ S, (P i - C i)) * ∏ i ∈ Sᶜ, P i := by
    calc
      (∏ i, (P i - if i ∈ S then C i else 0)) =
          (∏ i ∈ S, (P i - if i ∈ S then C i else 0)) *
            ∏ i ∈ Sᶜ, (P i - if i ∈ S then C i else 0) :=
        (Finset.prod_mul_prod_compl S _).symm
      _ = (∏ i ∈ S, (P i - C i)) * ∏ i ∈ Sᶜ, P i := by
        congr 1
        · apply Finset.prod_congr rfl
          intro i hi
          simp only [ite_eq_left hi]
        · apply Finset.prod_congr rfl
          intro i hi
          simp only [ite_eq_right (Finset.mem_compl.mp hi), sub_zero]
  rw [hsplit, Finset.prod_sub, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro U hU
  rw [prod_ite_split S U P C (Finset.mem_powerset.mp hU)]
  simp only [mul_assoc]
  rw [mul_left_comm (∏ i ∈ S \ U, P i) (∏ i ∈ U, C i)]

end TalagrandDiscreteConvexity

end OAI

-- ---- platform node ----
open OAI OAI.TalagrandDiscreteConvexity
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.TalagrandDiscreteConvexity.prod_sub_ite_eq_sum_powerset := @_root_.OAI.TalagrandDiscreteConvexity.prod_sub_ite_eq_sum_powerset
