-- Prove2me | solution 1 for OAI.TalagrandDiscreteConvexity.bernoulliLaw_expect_sum_mem
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T16:33:41.658289+00:00
-- url     : https://prove2.me/submissions/0952fdaf-f32e-468f-a645-380aa3b1cc8b

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/DiscreteConvexity/Bernoulli.lean:L268-L297
-- (upload_full_project.md Phase 4): solution for node OAI.TalagrandDiscreteConvexity.bernoulliLaw_expect_sum_mem. The node keeps its source
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

theorem expectation_smul (μ : FiniteLaw Ω) (c : ℝ) (f : Ω → ℝ) :
    μ.expectation (fun ω => c * f ω) = c * μ.expectation f := by
  simp [expectation, Finset.mul_sum, mul_left_comm]

theorem expectation_sum {ι : Type*} [Fintype ι] (μ : FiniteLaw Ω) (f : ι → Ω → ℝ) :
    μ.expectation (fun ω => ∑ i, f i ω) = ∑ i, μ.expectation (f i) := by
  simp only [expectation, Finset.mul_sum]
  exact Finset.sum_comm

theorem prob_eq_expectation (μ : FiniteLaw Ω) (P : Ω → Prop) :
    μ.prob P = μ.expectation (fun ω => if P ω then 1 else 0) := by
  classical
  simp [prob, expectation, mul_ite]

end FiniteLaw

end TalagrandDiscreteConvexity

end

end OAI

-- ---- from OAI.Combinatorics.DiscreteConvexity.Bernoulli ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

/-!
# Bernoulli product laws and Boolean cubes

The algebraic identities hold for every real parameter. Nonnegative normalized
laws additionally require a parameter in the closed unit interval.
-/

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

namespace TalagrandDiscreteConvexity

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem subset_indicator_product (A W : Finset α) :
    (if A ⊆ W then (1 : ℝ) else 0) =
      ∏ x, (if x ∈ A then (if x ∈ W then (1 : ℝ) else 0) else 1) := by
  rw [Fintype.prod_ite_mem, Finset.prod_boole]
  rfl

theorem bernoulliProbability_subset (p : ℝ) (A : Finset α) :
    bernoulliProbability p (fun W => A ⊆ W) = p ^ A.card := by
  trans bernoulliExpectation p (fun W =>
    ∏ x, (if x ∈ A then (if x ∈ W then (1 : ℝ) else 0) else 1))
  · unfold bernoulliProbability bernoulliExpectation
    apply Finset.sum_congr rfl
    intro W _
    dsimp only
    by_cases hs : A ⊆ W
    · have hh := (subset_indicator_product A W).symm
      simp only [ite_eq_left hs] at hh
      rw [hh]
      simp [hs]
    · have hh := (subset_indicator_product A W).symm
      simp only [ite_eq_right hs] at hh
      rw [hh]
      simp [hs]
  calc
    bernoulliExpectation p (fun W =>
        ∏ x, (if x ∈ A then (if x ∈ W then (1 : ℝ) else 0) else 1)) =
        ∏ x, (p * (if x ∈ A then (1 : ℝ) else 1) +
          (1 - p) * (if x ∈ A then (0 : ℝ) else 1)) := by
      simpa only [decide_eq_true_eq, Bool.true_eq, ite_true, Bool.false_eq_true, ite_false] using
        bernoulliExpectation_product p
          (fun x b => if x ∈ A then (if b then (1 : ℝ) else 0) else 1)
    _ = ∏ x, (if x ∈ A then p else 1) := by
      apply Finset.prod_congr rfl
      intro x _
      by_cases hx : x ∈ A <;> simp [hx]
    _ = p ^ A.card := by rw [Fintype.prod_ite_mem]; simp

theorem bernoulliLaw_prob_subset (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (A : Finset α) :
    (bernoulliLaw p hp0 hp1).prob (fun s => A ⊆ s) = p ^ A.card :=
  bernoulliProbability_subset p A

theorem bernoulliLaw_prob_mem (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (a : α) :
    (bernoulliLaw p hp0 hp1).prob (fun s => a ∈ s) = p := by
  simpa using bernoulliLaw_prob_subset p hp0 hp1 ({a} : Finset α)

theorem bernoulliLaw_expect_sum_mem (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (f : α → ℝ) :
    (bernoulliLaw p hp0 hp1).expectation (fun W => ∑ x ∈ W, f x) = p * ∑ x, f x := by
  classical
  let μ : FiniteLaw (Finset α) := bernoulliLaw p hp0 hp1
  have hsum (W : Finset α) :
      (∑ x ∈ W, f x) = ∑ x, if x ∈ W then f x else 0 := by
    rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
  have hx (x : α) :
      μ.expectation (fun W => if x ∈ W then f x else 0) = p * f x := by
    calc
      _ = μ.expectation (fun W => f x * (if x ∈ W then 1 else 0)) := by
        congr 1
        funext W
        by_cases h : x ∈ W <;> simp [h]
      _ = f x * μ.prob (fun W => x ∈ W) := by
        rw [FiniteLaw.expectation_smul]
        apply congrArg (fun z : ℝ => f x * z)
        rw [FiniteLaw.prob_eq_expectation]
        apply congrArg μ.expectation
        funext W
        by_cases h : x ∈ W <;> simp [h]
      _ = p * f x := by
        rw [show μ.prob (fun W => x ∈ W) = p from bernoulliLaw_prob_mem p hp0 hp1 x]
        exact mul_comm _ _
  change μ.expectation (fun W => ∑ x ∈ W, f x) = p * ∑ x, f x
  simp_rw [hsum]
  rw [FiniteLaw.expectation_sum]
  simp_rw [hx]
  simpa only [Finset.mem_univ, ite_true] using (Finset.mul_sum Finset.univ f p).symm

end TalagrandDiscreteConvexity

end

end OAI

-- ---- platform node ----
open OAI OAI.TalagrandDiscreteConvexity
open scoped BigOperators
attribute [local instance] Classical.propDecidable


theorem solution : type_of% @_root_.OAI.TalagrandDiscreteConvexity.bernoulliLaw_expect_sum_mem := @_root_.OAI.TalagrandDiscreteConvexity.bernoulliLaw_expect_sum_mem
