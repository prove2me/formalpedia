-- Prove2me | solution 1 for OAI.TalagrandDiscreteConvexity.signed_array_identity
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T16:54:44.396308+00:00
-- url     : https://prove2.me/submissions/7a01751d-762e-4a71-96e3-b0d4b24c16d1

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/DiscreteConvexity/SignedArrays.lean:L48-L78
-- (upload_full_project.md Phase 4): solution for node OAI.TalagrandDiscreteConvexity.signed_array_identity. The node keeps its source
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
import Theorems.Thm_OAI_TalagrandDiscreteConvexity_prod_sub_ite_eq_sum_powerset

-- ---- from OAI.Combinatorics.DiscreteConvexity.SignedArrays ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
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

/-- Choosing the correction columns factors into the same coefficient kernel
in every row. -/
theorem columnKernel_eq_rowKernel (q : ℝ) {k : ℕ} (U : Finset V)
    (X : Fin k → V → Bool) :
    (∏ i, if i ∈ U then ∏ j, correction q (X j i)
      else ∏ j, bitWeight q (X j i)) =
      ∏ j, rowKernel q U (X j) := by
  unfold rowKernel
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : i ∈ U <;> simp only [hi, ite_true, ite_false]

/-- The finite product expansion, followed by exact row factorization.
It is valid for every real q and every real-valued row function. -/
theorem signed_array_identity (q : ℝ) (k : ℕ)
    (f : (V → Bool) → ℝ) (S : Finset V) :
    (∑ X : Fin k → V → Bool, (∏ j, f (X j)) * signedArrayMass q S X) =
      ∑ U ∈ S.powerset, (-1 : ℝ) ^ U.card * b q f U ^ k := by
  classical
  calc
    (∑ X : Fin k → V → Bool, (∏ j, f (X j)) * signedArrayMass q S X) =
        ∑ X : Fin k → V → Bool, ∑ U ∈ S.powerset,
          (-1 : ℝ) ^ U.card * ∏ j, (f (X j) * rowKernel q U (X j)) := by
      apply Finset.sum_congr rfl
      intro X _
      rw [signedArrayMass, prod_sub_ite_eq_sum_powerset, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro U _
      rw [columnKernel_eq_rowKernel, Finset.prod_mul_distrib]
      exact mul_left_comm _ _ _
    _ = ∑ U ∈ S.powerset, (-1 : ℝ) ^ U.card *
        ∑ X : Fin k → V → Bool, ∏ j, (f (X j) * rowKernel q U (X j)) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro U _
      rw [Finset.mul_sum]
    _ = ∑ U ∈ S.powerset, (-1 : ℝ) ^ U.card * b q f U ^ k := by
      apply Finset.sum_congr rfl
      intro U _
      congr 1
      rw [← Fintype.prod_sum (fun (_ : Fin k) (x : V → Bool) =>
        f x * rowKernel q U x)]
      simp only [b, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

end TalagrandDiscreteConvexity

end

end OAI

-- ---- platform node ----
open OAI OAI.TalagrandDiscreteConvexity
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.TalagrandDiscreteConvexity.signed_array_identity := @_root_.OAI.TalagrandDiscreteConvexity.signed_array_identity
