-- Prove2me | solution 1 for OAI.TalagrandThreshold.FiniteLaw.expectation_pi_subset_product
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T13:23:09.327626+00:00
-- url     : https://prove2.me/submissions/5bca00d5-c044-4812-8f2f-6b355d18ebc5

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/ExpectationThreshold/ProbabilitySubsetProduct.lean:L25-L46
-- (upload_full_project.md Phase 4): solution for node OAI.TalagrandThreshold.FiniteLaw.expectation_pi_subset_product. The node keeps its source
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

-- ---- from OAI.Combinatorics.ExpectationThreshold.ProbabilityProduct ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-!
# Marginals and pushforwards of finite product laws

Product moments, one-coordinate marginals, and pushforward identities follow
from the weights of the finite laws.
-/

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

namespace TalagrandThreshold.FiniteLaw

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

end ProductCoordinates

variable {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]

end TalagrandThreshold.FiniteLaw

end

end OAI

-- ---- from OAI.Combinatorics.ExpectationThreshold.ProbabilitySubsetProduct ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

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

/-- A product on a subset has the product of its actual coordinate means. -/
theorem expectation_pi_subset_product (μ : ∀ i, FiniteLaw (A i))
    (S : Finset I) (f : ∀ i, A i → ℝ) :
    (pi μ).expectation (fun ω => ∏ i ∈ S, f i (ω i)) =
      ∏ i ∈ S, (μ i).expectation (f i) := by
  classical
  let g : ∀ i, A i → ℝ := fun i a => if i ∈ S then f i a else 1
  have hg (ω : ∀ i, A i) : (∏ i, g i (ω i)) = ∏ i ∈ S, f i (ω i) := by
    simpa only [g] using Fintype.prod_ite_mem S (fun i => f i (ω i))
  have he (i : I) : (μ i).expectation (g i) =
      if i ∈ S then (μ i).expectation (f i) else 1 := by
    by_cases hi : i ∈ S
    · simp only [g, ite_eq_left hi]
    · simp only [g, ite_eq_right hi, expectation_const]
  calc
    _ = (pi μ).expectation (fun ω => ∏ i, g i (ω i)) := by
      congr 1
      funext ω
      exact (hg ω).symm
    _ = ∏ i, (μ i).expectation (g i) := expectation_pi_product μ g
    _ = ∏ i ∈ S, (μ i).expectation (f i) := by
      simp only [he, Finset.prod_ite_mem_eq]

end TalagrandThreshold.FiniteLaw

end

end OAI

-- ---- platform node ----
open OAI OAI.TalagrandThreshold OAI.TalagrandThreshold.FiniteLaw
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.TalagrandThreshold.FiniteLaw.expectation_pi_subset_product := @_root_.OAI.TalagrandThreshold.FiniteLaw.expectation_pi_subset_product
