-- Prove2me | solution 1 for OAI.TalagrandDiscreteConvexity.prob_pi_cubeSet_mem_family
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T16:59:24.228114+00:00
-- url     : https://prove2.me/submissions/fccf8947-c561-44c9-883a-48593bca27d0

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/DiscreteConvexity/CoordinateObservations.lean:L49-L75
-- (upload_full_project.md Phase 4): solution for node OAI.TalagrandDiscreteConvexity.prob_pi_cubeSet_mem_family. The node keeps its source
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
import Theorems.Thm_OAI_TalagrandDiscreteConvexity_prob_pi_cubeSet_eq_mass

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

theorem map_weight_eq_prob (μ : FiniteLaw Ω) (f : Ω → Γ) (γ : Γ) :
    (map μ f).weight γ = μ.prob (fun ω => f ω = γ) := rfl

/-- Observables of a pushed law are evaluated along the defining map. -/
theorem expectation_map (μ : FiniteLaw Ω) (f : Ω → Γ) (g : Γ → ℝ) :
    (map μ f).expectation g = μ.expectation (fun ω => g (f ω)) := by
  unfold expectation
  simp only [map_weight, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  simp [ite_mul]

/-- The probability of an event under a pushed law is its preimage probability. -/
theorem prob_map (μ : FiniteLaw Ω) (f : Ω → Γ) (P : Γ → Prop) :
    (map μ f).prob P = μ.prob (fun ω => P (f ω)) := by
  rw [prob_eq_expectation, expectation_map, prob_eq_expectation]

end TalagrandDiscreteConvexity.FiniteLaw

end

end OAI

-- ---- from OAI.Combinatorics.DiscreteConvexity.CoordinateObservations ----
namespace OAI

/-!
# Boolean observations of finite product laws

Independent Boolean observations with common success probability have the
Bernoulli law on subsets, both on individual atoms and on arbitrary families.
-/

open scoped BigOperators
noncomputable section

namespace TalagrandDiscreteConvexity

variable {α : Type*} [Fintype α] [DecidableEq α]
  {Ω : α → Type*} [∀ i, Fintype (Ω i)]

/-- Membership of the observed set in a family has exactly its Bernoulli measure. -/
theorem prob_pi_cubeSet_mem_family (μ : ∀ i, FiniteLaw (Ω i))
    (obs : ∀ i, Ω i → Bool) (p : ℝ)
    (hobs : ∀ i, (μ i).prob (fun w => obs i w = true) = p) (D : Family α) :
    (FiniteLaw.pi μ).prob (fun ω => cubeSet (fun i => obs i (ω i)) ∈ D) =
      familyMeasure p D := by
  classical
  let f : (∀ i, Ω i) → Finset α := fun ω => cubeSet (fun i => obs i (ω i))
  calc
    (FiniteLaw.pi μ).prob (fun ω => cubeSet (fun i => obs i (ω i)) ∈ D) =
        ((FiniteLaw.pi μ).map f).prob (fun s => s ∈ D) :=
      (FiniteLaw.prob_map (FiniteLaw.pi μ) f (fun s => s ∈ D)).symm
    _ = ∑ s ∈ D, ((FiniteLaw.pi μ).map f).weight s := by
      calc
        ((FiniteLaw.pi μ).map f).prob (fun s => s ∈ D) =
            ∑ s : Finset α, if s ∈ D then ((FiniteLaw.pi μ).map f).weight s else 0 := by
          unfold FiniteLaw.prob
          apply Finset.sum_congr rfl
          intro s _
          by_cases hs : s ∈ D <;> simp [hs]
        _ = _ := Finset.sum_ite_mem_eq D ((FiniteLaw.pi μ).map f).weight
    _ = ∑ s ∈ D, bernoulliMass p s := by
      apply Finset.sum_congr rfl
      intro s _
      rw [FiniteLaw.map_weight_eq_prob]
      exact prob_pi_cubeSet_eq_mass μ obs p hobs s
    _ = familyMeasure p D := rfl

end TalagrandDiscreteConvexity

end

end OAI

-- ---- platform node ----
open OAI OAI.TalagrandDiscreteConvexity
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.TalagrandDiscreteConvexity.prob_pi_cubeSet_mem_family := @_root_.OAI.TalagrandDiscreteConvexity.prob_pi_cubeSet_mem_family
