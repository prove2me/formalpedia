-- Prove2me | solution 1 for OAI.TalagrandThreshold.expectation_productScore
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T13:23:55.794925+00:00
-- url     : https://prove2.me/submissions/9c2d088f-d463-4303-9446-324e93a9601a

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/ExpectationThreshold/RoundingExpectation.lean:L36-L53
-- (upload_full_project.md Phase 4): solution for node OAI.TalagrandThreshold.expectation_productScore. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Find
import Mathlib.Data.Real.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Order.Compact
import Definitions.Def_TalagrandExpectationThreshold
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_Model
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_Basic
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_RoundingMasses
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_ProbabilityFinite
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_ProbabilityProduct
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_RoundingExpectation
import Theorems.Thm_OAI_TalagrandThreshold_FiniteLaw_expectation_pi_subset_product

-- ---- from OAI.Combinatorics.ExpectationThreshold.ProbabilityFinite ----
namespace OAI

/-!
# Finite probability laws

Probabilities and expectations are finite real sums. Independent samples,
product laws, and uniform laws satisfy the usual elementary inequalities.
-/

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

namespace TalagrandThreshold

namespace FiniteLaw

variable {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]

theorem expectation_smul (μ : FiniteLaw Ω) (c : ℝ) (f : Ω → ℝ) :
    μ.expectation (fun ω => c * f ω) = c * μ.expectation f := by
  simp [expectation, Finset.mul_sum, mul_left_comm]

end FiniteLaw

end TalagrandThreshold

end

end OAI

-- ---- from OAI.Combinatorics.ExpectationThreshold.ProbabilitySubsetProduct ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-!
# Moments of products on a subset of coordinates

Under the actual product law, observables supported on a finite subset
factor into their coordinate expectations. Extending the factors by one
outside the subset reduces this to the full product moment identity.
-/

open scoped BigOperators
noncomputable section

namespace TalagrandThreshold.FiniteLaw

variable {I : Type*} [Fintype I] [DecidableEq I]
  {A : I → Type*} [∀ i, Fintype (A i)]

/-- Identically distributed coordinates give a power of their common mean. -/
theorem expectation_pi_subset_product_const {Ω : Type*} [Fintype Ω]
    (μ : FiniteLaw Ω) (S : Finset I) (f : Ω → ℝ) :
    (pi (fun _ : I => μ)).expectation (fun ω => ∏ i ∈ S, f (ω i)) =
      (μ.expectation f) ^ S.card := by
  rw [expectation_pi_subset_product, Finset.prod_const]

end TalagrandThreshold.FiniteLaw

end

end OAI

-- ---- from OAI.Combinatorics.ExpectationThreshold.RoundingExpectation ----
namespace OAI

/-!
# The upper expectation bound for rounding

The score sums over nonempty subsets of the original ground set. Its moments
come from the actual coordinate product law. Nonemptiness saves a factor of
one fifth in the fractional-cover cost.
-/

open scoped BigOperators

namespace TalagrandThreshold

noncomputable section

variable {α : Type*} [Fintype α] [DecidableEq α]

variable {Ω : Type*} [Fintype Ω]

/-- Independence of the coordinates gives the full subset-product expectation. -/
theorem expectation_productScore (ν : FiniteLaw Ω) (g : Finset α → ℝ) (Y : Ω → ℝ) :
    (FiniteLaw.pi (fun _ : α => ν)).expectation
        (fun ω => productScore g (fun x => Y (ω x))) =
      ∑ S ∈ (Finset.univ.erase ∅ : Finset (Finset α)),
        g S * (ν.expectation Y) ^ S.card := by
  classical
  calc
    _ = ∑ S ∈ (Finset.univ.erase ∅ : Finset (Finset α)),
        (FiniteLaw.pi (fun _ : α => ν)).expectation
          (fun ω => g S * ∏ x ∈ S, Y (ω x)) := by
      unfold FiniteLaw.expectation productScore
      simp only [Finset.mul_sum]
      exact Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro S _
      rw [FiniteLaw.expectation_smul, FiniteLaw.expectation_pi_subset_product_const]

end
end TalagrandThreshold

end OAI

-- ---- platform node ----
open OAI OAI.TalagrandThreshold
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.TalagrandThreshold.expectation_productScore := @_root_.OAI.TalagrandThreshold.expectation_productScore
