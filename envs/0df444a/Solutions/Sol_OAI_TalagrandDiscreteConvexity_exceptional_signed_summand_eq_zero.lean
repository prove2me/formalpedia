-- Prove2me | solution 1 for OAI.TalagrandDiscreteConvexity.exceptional_signed_summand_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T16:55:32.598628+00:00
-- url     : https://prove2.me/submissions/614afb5c-19e7-4fa7-a021-67ea5f62d507

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/DiscreteConvexity/SignedArrays.lean:L88-L108
-- (upload_full_project.md Phase 4): solution for node OAI.TalagrandDiscreteConvexity.exceptional_signed_summand_eq_zero. The node keeps its source
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
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_SignedArrays

-- ---- from OAI.Combinatorics.DiscreteConvexity.Basic ----
namespace OAI

namespace TalagrandDiscreteConvexity

open scoped BigOperators

variable {α : Type*} [Fintype α] [DecidableEq α]

noncomputable section

theorem exceptional_tuple_misses {k : ℕ} {D : Family α} {S : Finset α}
    (hS : S ∈ exceptional k D) (f : Fin k → Finset α) (hf : ∀ j, f j ∈ D) :
    ∃ a ∈ S, ∀ j, a ∉ f j := by
  obtain ⟨a, ha, hmiss⟩ := Finset.not_subset.mp (mem_exceptional.mp hS f hf)
  exact ⟨a, ha, fun j hj => hmiss (mem_unionTuple.mpr ⟨j, hj⟩)⟩

end
end TalagrandDiscreteConvexity

end OAI

-- ---- from OAI.Combinatorics.DiscreteConvexity.SignedArrays ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

/-!
# Signed arrays force weight on every exceptional set

The arrays have one common set of rows. Each column in `S` receives the
Bernoulli product mass minus the product of the alternating corrections.
All-zero columns in `S` have zero signed mass. This gives pointwise vanishing
for exceptional sets, without any nonnegativity assumption on these masses.
Expanding the column products and summing independently over the rows gives
the exact signed coefficient identity.
-/

noncomputable section

open scoped BigOperators

namespace TalagrandDiscreteConvexity

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- An all-zero column in S cancels exactly; the masses may be signed. -/
theorem signedArrayMass_eq_zero_of_zero_column (q : ℝ) {k : ℕ}
    {S : Finset V} {X : Fin k → V → Bool} {i : V}
    (hi : i ∈ S) (hzero : ∀ j, X j i = false) :
    signedArrayMass q S X = 0 := by
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simp [hi, hzero, bitWeight, correction]

/-- On an exceptional set, either one row leaves the family or some column
of S is all zero. In either case the signed summand vanishes. -/
theorem exceptional_signed_summand_eq_zero (q : ℝ) {k : ℕ}
    {D : Family V} {S : Finset V} (hS : S ∈ exceptional k D)
    (X : Fin k → V → Bool) :
    (∏ j, familyIndicator D (X j)) * signedArrayMass q S X = 0 := by
  classical
  by_cases hrows : ∀ j, cubeSet (X j) ∈ D
  · obtain ⟨i, hi, hmissing⟩ :=
      exceptional_tuple_misses hS (fun j => cubeSet (X j)) hrows
    have hzero (j : Fin k) : X j i = false := by
      cases hbit : X j i with
      | false => rfl
      | true =>
        exact False.elim (hmissing j (by simp [cubeSet, hbit]))
    rw [signedArrayMass_eq_zero_of_zero_column q hi hzero, mul_zero]
  · obtain ⟨j, hj⟩ := not_forall.mp hrows
    have hprod : (∏ j, familyIndicator D (X j)) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ j)
      simp only [familyIndicator, ite_eq_right hj]
    rw [hprod, zero_mul]

end TalagrandDiscreteConvexity

end

end OAI

-- ---- platform node ----
open OAI OAI.TalagrandDiscreteConvexity
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.TalagrandDiscreteConvexity.exceptional_signed_summand_eq_zero := @_root_.OAI.TalagrandDiscreteConvexity.exceptional_signed_summand_eq_zero
