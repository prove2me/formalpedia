-- Prove2me | solution 1 for OAI.TalagrandDiscreteConvexity.Covering.expectation_residualFamily_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T16:46:56.606653+00:00
-- url     : https://prove2.me/submissions/02cce123-d769-4a12-8ba2-e55ab6835987

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/DiscreteConvexity/CoveringResidualCost.lean:L27-L63
-- (upload_full_project.md Phase 4): solution for node OAI.TalagrandDiscreteConvexity.Covering.expectation_residualFamily_le. The node keeps its source
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

-- ---- from OAI.Combinatorics.DiscreteConvexity.CoveringSampledFamilies ----
namespace OAI

/-!
# Deterministic covers from a pair-sampling outcome

Every sampling outcome gives a cover.  The cost bounds count generators
with multiplicity, indexed by ordered pairs or injective ordered tuples.
No independence or probability estimate is needed for these pointwise
statements.
-/

namespace TalagrandDiscreteConvexity.Covering

open scoped BigOperators

variable {V : Type*} [DecidableEq V]

/-- Counting each avoiding tuple separately bounds the residual cost.
The indicator has the same argument order as the sampling law. -/
theorem cost_residualFamily_le (H : Family V) (m : ℕ) (sample : Sample H)
    {rho : ℝ} (hrho : 0 ≤ rho) :
    cost rho (residualFamily H m sample) ≤
      ∑ f : EdgeTuple H m,
        if Disjoint sample (tuplePairs f) then rho ^ (tupleUnion f).card else 0 := by
  classical
  calc
    cost rho (residualFamily H m sample) ≤
        ∑ f ∈ Finset.univ.filter
            (fun f : EdgeTuple H m => Disjoint sample (tuplePairs f)),
          rho ^ (tupleUnion f).card := by
      unfold cost residualFamily
      exact Finset.sum_image_le_of_nonneg
        (fun I _ => pow_nonneg hrho I.card)
    _ = _ := Finset.sum_filter _ _

end TalagrandDiscreteConvexity.Covering

end OAI

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

theorem expectation_sum {ι : Type*} [Fintype ι] (μ : FiniteLaw Ω) (f : ι → Ω → ℝ) :
    μ.expectation (fun ω => ∑ i, f i ω) = ∑ i, μ.expectation (f i) := by
  simp only [expectation, Finset.mul_sum]
  exact Finset.sum_comm

theorem expectation_mono (μ : FiniteLaw Ω) {f g : Ω → ℝ} (hfg : ∀ ω, f ω ≤ g ω) :
    μ.expectation f ≤ μ.expectation g :=
  Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (hfg ω) (μ.nonneg ω)

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

theorem bernoulliProbability_eq_expectation (p : ℝ) (P : Finset α → Prop) :
    bernoulliProbability p P = bernoulliExpectation p (fun W => if P W then 1 else 0) := by
  classical
  simp [bernoulliProbability, bernoulliExpectation, mul_ite]

theorem disjoint_indicator_product (A W : Finset α) :
    (if Disjoint W A then (1 : ℝ) else 0) =
      ∏ x, (if x ∈ A then (if x ∈ W then (0 : ℝ) else 1) else 1) := by
  simp only [Finset.disjoint_right]
  rw [Fintype.prod_ite_mem]
  have h (x : α) : (if x ∈ W then (0 : ℝ) else 1) =
      if x ∉ W then 1 else 0 := by
    by_cases hx : x ∈ W <;> simp [hx]
  simp_rw [h]
  rw [Finset.prod_boole]
  by_cases hexp : ∀ i ∈ A, i ∉ W
  · have himp : ∀ ⦃i : α⦄, i ∈ A → i ∉ W := by
      intro i hi
      exact hexp i hi
    simp only [ite_eq_left himp]
  · have himp : ¬ (∀ ⦃i : α⦄, i ∈ A → i ∉ W) := by
      intro hi
      exact hexp (fun i hai => hi hai)
    simp only [ite_eq_right himp]

theorem bernoulliProbability_disjoint (p : ℝ) (A : Finset α) :
    bernoulliProbability p (fun W => Disjoint W A) = (1 - p) ^ A.card := by
  rw [bernoulliProbability_eq_expectation]
  trans bernoulliExpectation p (fun W =>
    ∏ x, (if x ∈ A then (if x ∈ W then (0 : ℝ) else 1) else 1))
  · congr 1
    funext W
    by_cases h : Disjoint W A <;>
      simpa [h] using disjoint_indicator_product A W
  calc
    bernoulliExpectation p (fun W =>
        ∏ x, (if x ∈ A then (if x ∈ W then (0 : ℝ) else 1) else 1)) =
        ∏ x, (p * (if x ∈ A then (0 : ℝ) else 1) +
          (1 - p) * (if x ∈ A then (1 : ℝ) else 1)) := by
      simpa only [decide_eq_true_eq, Bool.true_eq, ite_true, Bool.false_eq_true, ite_false] using
        bernoulliExpectation_product p
          (fun x b => if x ∈ A then (if b then (0 : ℝ) else 1) else 1)
    _ = ∏ x, (if x ∈ A then 1 - p else 1) := by
      apply Finset.prod_congr rfl
      intro x _
      by_cases hx : x ∈ A <;> simp [hx]
    _ = (1 - p) ^ A.card := by rw [Fintype.prod_ite_mem]; simp

theorem bernoulliLaw_prob_disjoint (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (A : Finset α) :
    (bernoulliLaw p hp0 hp1).prob (fun W => Disjoint W A) = (1 - p) ^ A.card :=
  bernoulliProbability_disjoint p A

end TalagrandDiscreteConvexity

end

end OAI

-- ---- from OAI.Combinatorics.DiscreteConvexity.CoveringResidualProbability ----
namespace OAI

/-!
# Exact survival probability of a tuple of distinct edges

The sampling coordinates are ordered pairs of edges, not their unions. Every
ordered pair of positions contributes a distinct coordinate, including each
diagonal position. The product Bernoulli law therefore assigns exactly
`(1 - p) ^ (m * m)` to the event that all these coordinates are absent.
-/

namespace TalagrandDiscreteConvexity.Covering

/-- Applying an injection in both coordinates preserves ordered pairs. -/
theorem orderedPairMap_injective {I E : Type*} {e : I → E}
    (he : Function.Injective e) :
    Function.Injective (fun ij : I × I => (e ij.1, e ij.2)) := by
  intro ij kl h
  apply Prod.ext
  · exact he (congrArg Prod.fst h)
  · exact he (congrArg Prod.snd h)

variable {X : Type*} [DecidableEq X]

noncomputable section

/-- The tuple uses all `m * m` ordered pair coordinates, including the diagonal. -/
theorem tuplePairs_card {H : Family X} {m : ℕ} (f : EdgeTuple H m) :
    (tuplePairs f).card = m * m := by
  classical
  rw [tuplePairs, Finset.card_image_of_injective _
    (orderedPairMap_injective f.property)]
  simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin]

/-- Exact residual probability under the actual finite product Bernoulli law. -/
theorem tuple_survival_probability {H : Family X} {m : ℕ}
    (f : EdgeTuple H m) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (bernoulliLaw (α := ↥H × ↥H) p hp0 hp1).prob
      (fun sample => Disjoint sample (tuplePairs f)) = (1 - p) ^ (m * m) := by
  rw [bernoulliLaw_prob_disjoint, tuplePairs_card]

end
end TalagrandDiscreteConvexity.Covering

end OAI

-- ---- from OAI.Combinatorics.DiscreteConvexity.CoveringResidualCost ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-!
# Expected cost of the actual residual generators

Repeated unions are first counted with multiplicity. Each injective tuple
avoids exactly its distinct ordered-pair indices under the product Bernoulli
law. Finite linearity then separates this common survival probability from
the weighted tuple sum.
-/

namespace TalagrandDiscreteConvexity.Covering

open scoped BigOperators Classical

variable {V : Type*} [DecidableEq V]

/-- The expected residual cost is bounded by the actual weighted tuple sum
times the exact probability of avoiding all ordered pairs of one tuple. -/
theorem expectation_residualFamily_le (H : Family V) (rho : ℝ)
    (hrho : 0 ≤ rho) (m : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (bernoulliLaw (α := PairIndex H) p hp0 hp1).expectation
        (fun sample => cost rho (residualFamily H m sample)) ≤
      tupleWeightSum H rho m * (1 - p) ^ (m * m) := by
  classical
  let μ := bernoulliLaw (α := PairIndex H) p hp0 hp1
  calc
    μ.expectation (fun sample => cost rho (residualFamily H m sample)) ≤
        μ.expectation (fun sample => ∑ f : EdgeTuple H m,
          if Disjoint sample (tuplePairs f) then rho ^ (tupleUnion f).card else 0) :=
      μ.expectation_mono (fun sample => cost_residualFamily_le H m sample hrho)
    _ = ∑ f : EdgeTuple H m, μ.expectation (fun sample =>
          if Disjoint sample (tuplePairs f) then rho ^ (tupleUnion f).card else 0) :=
      μ.expectation_sum _
    _ = ∑ f : EdgeTuple H m, (1 - p) ^ (m * m) * rho ^ (tupleUnion f).card := by
      apply Finset.sum_congr rfl
      intro f _
      calc
        μ.expectation (fun sample => if Disjoint sample (tuplePairs f)
            then rho ^ (tupleUnion f).card else 0) =
            μ.prob (fun sample => Disjoint sample (tuplePairs f)) *
              rho ^ (tupleUnion f).card := by
          simp only [FiniteLaw.expectation, FiniteLaw.prob, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro sample _
          by_cases hs : Disjoint sample (tuplePairs f)
          · simp only [ite_eq_left hs]
          · simp only [ite_eq_right hs, mul_zero, zero_mul]
        _ = _ := congrArg (fun q : ℝ => q * rho ^ (tupleUnion f).card)
          (tuple_survival_probability f p hp0 hp1)
    _ = tupleWeightSum H rho m * (1 - p) ^ (m * m) := by
      unfold tupleWeightSum tupleWeight
      rw [← Finset.mul_sum]
      exact mul_comm _ _

end TalagrandDiscreteConvexity.Covering

end OAI

-- ---- platform node ----
open OAI OAI.TalagrandDiscreteConvexity OAI.TalagrandDiscreteConvexity.Covering
open scoped BigOperators Classical


theorem solution : type_of% @_root_.OAI.TalagrandDiscreteConvexity.Covering.expectation_residualFamily_le := @_root_.OAI.TalagrandDiscreteConvexity.Covering.expectation_residualFamily_le
