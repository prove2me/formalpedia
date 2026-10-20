-- Prove2me | solution 1 for OAI.TalagrandDiscreteConvexity.FiniteLaw.prob_pi
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T16:56:59.703106+00:00
-- url     : https://prove2.me/submissions/6e60bb18-e597-4593-876d-92117cdabb0d

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/DiscreteConvexity/ProductProbability.lean:L69-L86
-- (upload_full_project.md Phase 4): solution for node OAI.TalagrandDiscreteConvexity.FiniteLaw.prob_pi. The node keeps its source
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

-- ---- from OAI.Combinatorics.DiscreteConvexity.FiniteProbability ----
namespace OAI

/-!
# Finite probability laws

All probabilities and expectations are finite real sums. Finite laws admit
elementary probability inequalities, product laws, independent samples, and
uniform distributions.
-/

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

namespace TalagrandDiscreteConvexity

namespace FiniteLaw

variable {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]

theorem prob_eq_expectation (μ : FiniteLaw Ω) (P : Ω → Prop) :
    μ.prob P = μ.expectation (fun ω => if P ω then 1 else 0) := by
  classical
  simp [prob, expectation, mul_ite]

end FiniteLaw

end TalagrandDiscreteConvexity

end

end OAI

-- ---- from OAI.Combinatorics.DiscreteConvexity.ProductProbability ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

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

/-- A cylinder event has the product of its coordinate probabilities. -/
theorem prob_pi (μ : ∀ i, FiniteLaw (A i)) (P : ∀ i, A i → Prop) :
    (pi μ).prob (fun ω => ∀ i, P i (ω i)) = ∏ i, (μ i).prob (P i) := by
  classical
  rw [prob_eq_expectation]
  calc
    _ = (pi μ).expectation (fun ω => ∏ i, if P i (ω i) then 1 else 0) := by
      congr 1
      funext ω
      symm
      by_cases h : ∀ i, P i (ω i)
      · simpa only [ite_eq_left h] using
          (Fintype.prod_boole (p := fun i => P i (ω i)) (M₀ := ℝ))
      · simpa only [ite_eq_right h] using
          (Fintype.prod_boole (p := fun i => P i (ω i)) (M₀ := ℝ))
    _ = ∏ i, (μ i).expectation (fun a => if P i a then 1 else 0) :=
      expectation_pi_product μ (fun i a => if P i a then 1 else 0)
    _ = _ := by simp_rw [prob_eq_expectation]

end ProductCoordinates

variable {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]

end TalagrandDiscreteConvexity.FiniteLaw

end

end OAI

-- ---- platform node ----
open OAI OAI.TalagrandDiscreteConvexity OAI.TalagrandDiscreteConvexity.FiniteLaw
open scoped BigOperators
attribute [local instance] Classical.propDecidable


theorem solution : type_of% @_root_.OAI.TalagrandDiscreteConvexity.FiniteLaw.prob_pi := @_root_.OAI.TalagrandDiscreteConvexity.FiniteLaw.prob_pi
