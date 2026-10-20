-- Prove2me | solution 1 for OAI.TalagrandDiscreteConvexity.FiniteLaw.prob_prod
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T16:57:47.824995+00:00
-- url     : https://prove2.me/submissions/ff0a14f3-ac65-444b-876a-1060699eae8c

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/DiscreteConvexity/ProductProbability.lean:L92-L108
-- (upload_full_project.md Phase 4): solution for node OAI.TalagrandDiscreteConvexity.FiniteLaw.prob_prod. The node keeps its source
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
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_ProductProbability

-- ---- from OAI.Combinatorics.DiscreteConvexity.ProductProbability ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-!
# Marginals and pushforwards of finite product laws

All identities below follow from the weights of the actual finite laws.
-/

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

namespace TalagrandDiscreteConvexity.FiniteLaw

section ProductCoordinates

variable {I : Type*} [Fintype I] [DecidableEq I]
  {A : I → Type*} [∀ i, Fintype (A i)]

end ProductCoordinates

variable {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]

/-- Rectangle events factor under the binary product law. -/
theorem prob_prod (μ : FiniteLaw Ω) (ν : FiniteLaw Γ)
    (P : Ω → Prop) (Q : Γ → Prop) :
    (μ.prod ν).prob (fun z => P z.1 ∧ Q z.2) = μ.prob P * ν.prob Q := by
  classical
  simp only [prob, prod, Fintype.sum_prod_type]
  calc
    _ = ∑ ω, ∑ γ,
        (if P ω then μ.weight ω else 0) * (if Q γ then ν.weight γ else 0) := by
      apply Finset.sum_congr rfl
      intro ω _
      apply Finset.sum_congr rfl
      intro γ _
      by_cases hp : P ω <;> by_cases hq : Q γ <;> simp [hp, hq]
    _ = _ := by
      simp_rw [← Finset.mul_sum]
      rw [← Finset.sum_mul]

end TalagrandDiscreteConvexity.FiniteLaw

end

end OAI

-- ---- platform node ----
open OAI OAI.TalagrandDiscreteConvexity OAI.TalagrandDiscreteConvexity.FiniteLaw
open scoped BigOperators
attribute [local instance] Classical.propDecidable


theorem solution : type_of% @_root_.OAI.TalagrandDiscreteConvexity.FiniteLaw.prob_prod := @_root_.OAI.TalagrandDiscreteConvexity.FiniteLaw.prob_prod
