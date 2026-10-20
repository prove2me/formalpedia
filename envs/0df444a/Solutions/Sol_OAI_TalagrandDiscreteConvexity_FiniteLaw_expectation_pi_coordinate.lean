-- Prove2me | solution 1 for OAI.TalagrandDiscreteConvexity.FiniteLaw.expectation_pi_coordinate
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T16:56:17.980959+00:00
-- url     : https://prove2.me/submissions/5d811870-e2be-4e65-9f48-a5df6c1b9371

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/DiscreteConvexity/ProductProbability.lean:L38-L59
-- (upload_full_project.md Phase 4): solution for node OAI.TalagrandDiscreteConvexity.FiniteLaw.expectation_pi_coordinate. The node keeps its source
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

/-- Product observables factor under the product of the given finite laws. -/
theorem expectation_pi_product (μ : ∀ i, FiniteLaw (A i))
    (f : ∀ i, A i → ℝ) :
    (pi μ).expectation (fun ω => ∏ i, f i (ω i)) =
      ∏ i, (μ i).expectation (f i) := by
  classical
  simp only [expectation, pi_weight]
  simp_rw [← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i a => (μ i).weight a * f i a)).symm

/-- A coordinate of the product law has exactly its prescribed marginal. -/
theorem expectation_pi_coordinate (μ : ∀ i, FiniteLaw (A i))
    (i : I) (f : A i → ℝ) :
    (pi μ).expectation (fun ω => f (ω i)) = (μ i).expectation f := by
  classical
  let g : ∀ j, A j → ℝ := fun j a => if h : j = i then f (h ▸ a) else 1
  have hg (ω : ∀ j, A j) : (∏ j, g j (ω j)) = f (ω i) := by
    dsimp only [g]
    simp only [Fintype.prod_dite_eq']
  have he (j : I) : (μ j).expectation (g j) =
      if h : j = i then (μ i).expectation f else 1 := by
    by_cases h : j = i
    · subst j
      simp [g]
    · simp [g, h, expectation_const]
  calc
    _ = (pi μ).expectation (fun ω => ∏ j, g j (ω j)) := by
      congr 1
      funext ω
      exact (hg ω).symm
    _ = ∏ j, (μ j).expectation (g j) := expectation_pi_product μ g
    _ = _ := by simp_rw [he]; simp

end ProductCoordinates

variable {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]

end TalagrandDiscreteConvexity.FiniteLaw

end

end OAI

-- ---- platform node ----
open OAI OAI.TalagrandDiscreteConvexity OAI.TalagrandDiscreteConvexity.FiniteLaw
open scoped BigOperators
attribute [local instance] Classical.propDecidable


theorem solution : type_of% @_root_.OAI.TalagrandDiscreteConvexity.FiniteLaw.expectation_pi_coordinate := @_root_.OAI.TalagrandDiscreteConvexity.FiniteLaw.expectation_pi_coordinate
