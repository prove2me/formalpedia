-- Prove2me | solution 1 for OAI.TalagrandDiscreteConvexity.Covering.elementary_covering
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T16:48:36.946575+00:00
-- url     : https://prove2.me/submissions/e06a2a85-12cf-4577-a2c0-b7a169f9e0fa

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/DiscreteConvexity/ElementaryCovering.lean:L22-L90
-- (upload_full_project.md Phase 4): solution for node OAI.TalagrandDiscreteConvexity.Covering.elementary_covering. The node keeps its source
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
import Theorems.Thm_OAI_TalagrandDiscreteConvexity_Covering_NumericalBounds_final_cost_le
import Theorems.Thm_OAI_TalagrandDiscreteConvexity_Covering_NumericalBounds_initial_cost_le
import Theorems.Thm_OAI_TalagrandDiscreteConvexity_Covering_NumericalBounds_pair_cost_le
import Theorems.Thm_OAI_TalagrandDiscreteConvexity_Covering_NumericalBounds_residual_cost_le_inv_pow
import Theorems.Thm_OAI_TalagrandDiscreteConvexity_Covering_allTupleWeightSum_le
import Theorems.Thm_OAI_TalagrandDiscreteConvexity_Covering_covers_sampled_residual
import Theorems.Thm_OAI_TalagrandDiscreteConvexity_Covering_expectation_residualFamily_le
import Theorems.Thm_OAI_TalagrandDiscreteConvexity_Covering_expectation_sampledFamily_le
import Theorems.Thm_OAI_TalagrandDiscreteConvexity_Covering_initial_cost_le
import Theorems.Thm_OAI_TalagrandDiscreteConvexity_Covering_regular_extension_le_card
import Theorems.Thm_OAI_TalagrandDiscreteConvexity_Covering_sum_choose_range_le_pow
import Theorems.Thm_OAI_TalagrandDiscreteConvexity_Covering_tupleWeightSum_le_allTupleWeightSum
import Theorems.Thm_OAI_TalagrandDiscreteConvexity_FiniteLaw_exists_le_expectation

-- ---- from OAI.Combinatorics.DiscreteConvexity.Basic ----
namespace OAI

namespace TalagrandDiscreteConvexity

open scoped BigOperators

variable {α : Type*} [Fintype α] [DecidableEq α]

noncomputable section

omit [Fintype α] [DecidableEq α] in
theorem cost_nonneg {p : ℝ} (hp : 0 ≤ p) (G : Family α) : 0 ≤ cost p G :=
  Finset.sum_nonneg (fun generator _ => pow_nonneg hp generator.card)

omit [Fintype α] in
theorem cost_union_le {p : ℝ} (hp : 0 ≤ p) (G H : Family α) :
    cost p (G ∪ H) ≤ cost p G + cost p H := by
  calc
    cost p (G ∪ H) ≤ cost p (G ∪ H) + cost p (G ∩ H) :=
      le_add_of_nonneg_right (cost_nonneg hp _)
    _ = cost p G + cost p H := by
      exact Finset.sum_union_inter

end
end TalagrandDiscreteConvexity

end OAI

-- ---- from OAI.Combinatorics.DiscreteConvexity.CoveringBasic ----
namespace OAI

/-!
# Finite objects in the elementary covering argument

Sampling is indexed by ordered pairs of edges, including diagonal pairs.
Different pairs remain different indices even if their unions coincide.
Residual generators are indexed by injective ordered tuples.
-/

namespace TalagrandDiscreteConvexity.Covering

variable {V : Type*} [DecidableEq V]

theorem regularFamily_subset (H C0 : Family V) : regularFamily H C0 ⊆ H := by
  intro e he
  exact (mem_regularFamily.mp he).1

section FiniteGround

variable [Fintype V]

theorem regularEdges_subset (H : Family V) (rho : ℝ) (r : ℕ) (T : ℝ) :
    regularEdges H rho r T ⊆ H := regularFamily_subset _ _

end FiniteGround

end TalagrandDiscreteConvexity.Covering

end OAI

-- ---- from OAI.Combinatorics.DiscreteConvexity.CoveringBinomialBounds ----
namespace OAI

/-!
# Counting bounded-size subsets

Subsets of cardinality at most `r` are counted by a partial binomial sum.
The elementary bound by `(1 + B.card)^r` includes `r = 0` and empty `B`.
-/

namespace TalagrandDiscreteConvexity.Covering

open scoped BigOperators

/-- Partition the subsets of `B` of size at most `r` by their cardinality. -/
theorem card_subsets_card_le {V : Type*} [DecidableEq V] (B : Finset V) (r : ℕ) :
    (B.powerset.filter (fun I => I.card ≤ r)).card =
      ∑ i ∈ Finset.range (r + 1), Nat.choose B.card i := by
  simpa only [Finset.mem_range, Nat.lt_succ_iff,
    ← Finset.powersetCard_eq_filter, Finset.card_powersetCard] using
    (Finset.sum_card_fiberwise_eq_card_filter B.powerset
      (Finset.range (r + 1)) Finset.card).symm

/-- The number of subsets of `B` of size at most `r` is at most `(1 + B.card)^r`. -/
theorem card_subsets_card_le_pow {V : Type*} [DecidableEq V]
    (B : Finset V) (r : ℕ) :
    (B.powerset.filter (fun I => I.card ≤ r)).card ≤ (1 + B.card) ^ r := by
  rw [card_subsets_card_le]
  exact sum_choose_range_le_pow B.card r

end TalagrandDiscreteConvexity.Covering

end OAI

-- ---- from OAI.Combinatorics.DiscreteConvexity.CoveringRegularization ----
namespace OAI

/-!
# Weighted-degree regularization

The initial family is the actual family of high weighted-degree subsets.
Double counting bounds its cost. An edge surviving this deletion has bounded
weighted degree at every one of its subsets. Grouping surviving edges by their
intersection with `B` gives the extension estimates used for pair sampling and
for residual tuples. No regularity property is assumed separately.
-/

namespace TalagrandDiscreteConvexity.Covering

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The polynomial version used for extending a residual tuple prefix. -/
theorem regular_extension_le_pow {H : Family V} {rho T : ℝ} {r : ℕ}
    (hρ : 0 ≤ rho) (hT : 0 ≤ T) (hH : ∀ e ∈ H, e.card = r) (B : Finset V) :
    (∑ e ∈ regularEdges H rho r T, rho ^ (e \ B).card) ≤
      T * (1 + (B.card : ℝ)) ^ r := by
  have hc : ((B.powerset.filter (fun I => I.card ≤ r)).card : ℝ) ≤
      (((1 + B.card) ^ r : ℕ) : ℝ) :=
    Nat.cast_le.mpr (card_subsets_card_le_pow B r)
  have hc' : ((B.powerset.filter (fun I => I.card ≤ r)).card : ℝ) ≤
      (1 + (B.card : ℝ)) ^ r := by
    simpa only [Nat.cast_pow, Nat.cast_add, Nat.cast_one] using hc
  exact (regular_extension_le_card hρ hT hH B).trans (mul_le_mul_of_nonneg_left hc' hT)

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

theorem expectation_add (μ : FiniteLaw Ω) (f g : Ω → ℝ) :
    μ.expectation (fun ω => f ω + g ω) = μ.expectation f + μ.expectation g := by
  simp [expectation, mul_add, Finset.sum_add_distrib]

theorem expectation_mono (μ : FiniteLaw Ω) {f g : Ω → ℝ} (hfg : ∀ ω, f ω ≤ g ω) :
    μ.expectation f ≤ μ.expectation g :=
  Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (hfg ω) (μ.nonneg ω)

end FiniteLaw

end TalagrandDiscreteConvexity

end

end OAI

-- ---- from OAI.Combinatorics.DiscreteConvexity.CoveringResidualTuples ----
namespace OAI

/-!
# The total weight of residual tuples

We bound the sum over injective edge tuples by the sum over all edge tuples.
Splitting an unrestricted tuple into its first edge and its tail gives an
exact weighted recurrence. The per-union extension bound then controls every
step. No nonemptiness assumption on the edge family is needed.
-/

namespace TalagrandDiscreteConvexity.Covering

open scoped BigOperators

variable {V : Type*} [DecidableEq V]

noncomputable section

theorem tupleWeightSum_le (H : Family V) {rho T : ℝ} {r m : ℕ}
    (hrho : 0 ≤ rho) (hT : 0 ≤ T)
    (uniform : ∀ e ∈ H, (e : Finset V).card = r)
    (extension : ∀ B : Finset V,
      (∑ e ∈ H, rho ^ (e \ B).card) ≤ T * (1 + (B.card : ℝ)) ^ r) :
    tupleWeightSum H rho m ≤ (T * (1 + ((r * m : ℕ) : ℝ)) ^ r) ^ m :=
  (tupleWeightSum_le_allTupleWeightSum H hrho m).trans
    (allTupleWeightSum_le H hrho hT uniform extension m le_rfl)

end

end TalagrandDiscreteConvexity.Covering

end OAI

-- ---- from OAI.Combinatorics.DiscreteConvexity.CoveringNumericalBounds ----
namespace OAI

namespace TalagrandDiscreteConvexity.Covering.NumericalBounds

theorem T_pos (h : ℕ) : 0 < T h := by
  unfold T
  positivity

theorem T_nonneg (h : ℕ) : 0 ≤ T h := (T_pos h).le

end TalagrandDiscreteConvexity.Covering.NumericalBounds

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

/-- Applying the proved tuple recurrence bounds the expected residual cost
using only the actual extension estimate for the edge family. -/
theorem expectation_residualFamily_le_extension (H : Family V)
    {rho T : ℝ} {r m : ℕ} (hrho : 0 ≤ rho) (hT : 0 ≤ T)
    (uniform : ∀ e ∈ H, (e : Finset V).card = r)
    (extension : ∀ B : Finset V,
      (∑ e ∈ H, rho ^ (e \ B).card) ≤ T * (1 + (B.card : ℝ)) ^ r)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (bernoulliLaw (α := PairIndex H) p hp0 hp1).expectation
        (fun sample => cost rho (residualFamily H m sample)) ≤
      (T * (1 + ((r * m : ℕ) : ℝ)) ^ r) ^ m * (1 - p) ^ (m * m) := by
  exact (expectation_residualFamily_le H rho hrho m p hp0 hp1).trans
    (mul_le_mul_of_nonneg_right
      (tupleWeightSum_le H (rho := rho) (T := T) (r := r) (m := m)
        hrho hT uniform extension)
      (pow_nonneg (sub_nonneg.mpr hp1) _))

theorem expectation_residualFamily_le_inv_pow (H : Family V)
    {rho : ℝ} {r h : ℕ} (hrho : 0 ≤ rho)
    (uniform : ∀ e ∈ H, (e : Finset V).card = r)
    (extension : ∀ B : Finset V, (∑ e ∈ H, rho ^ (e \ B).card) ≤
      NumericalBounds.T h * (1 + (B.card : ℝ)) ^ r)
    (hrh : r ≤ h) (hh : 64 ≤ h) :
    (bernoulliLaw (α := PairIndex H) (NumericalBounds.p h)
      (NumericalBounds.p_nonneg h) (NumericalBounds.p_le_one h)).expectation
        (fun sample => cost rho (residualFamily H (NumericalBounds.m h) sample)) ≤
      ((2 : ℝ) ^ NumericalBounds.m h)⁻¹ := by
  have hbound := expectation_residualFamily_le_extension H
    (rho := rho) (r := r) (m := NumericalBounds.m h) hrho
    (NumericalBounds.T_nonneg h) uniform extension (NumericalBounds.p h)
    (NumericalBounds.p_nonneg h) (NumericalBounds.p_le_one h)
  apply hbound.trans
  simpa only [Nat.cast_mul] using NumericalBounds.residual_cost_le_inv_pow r h hrh hh

end TalagrandDiscreteConvexity.Covering

end OAI

-- ---- from OAI.Combinatorics.DiscreteConvexity.ElementaryCovering ----
namespace OAI

/-!
# The elementary covering lemma

The initial generators and regular edges are constructed from weighted
degrees. The remaining generators come from an actual finite Bernoulli
sample of ordered pairs. Every outcome is a containment cover, and finite
averaging selects an outcome meeting the claimed cost budget.
-/

namespace TalagrandDiscreteConvexity.Covering

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem elementary_covering (H : Family V) (rho : ℝ) (r h : ℕ)
    (hrho0 : 0 < rho) (_hrho1 : rho < 1)
    (uniform : ∀ e ∈ H, e.card = r)
    (_hr : 1 ≤ r) (hrh : r ≤ h) (hh : 64 ≤ h)
    (hweight : (H.card : ℝ) * rho ^ r ≤ (2 : ℝ) ^ (h + 1)) :
    ∃ G : Family V, Covers G (denseFamily H (2 ^ (12 * h))) ∧
      cost rho G ≤ 3 * ((2 : ℝ) ^ h)⁻¹ := by
  classical
  let T := NumericalBounds.T h
  let m := NumericalBounds.m h
  let p := NumericalBounds.p h
  let C0 := initialFamily H rho r T
  let K := regularEdges H rho r T
  let μ := bernoulliLaw (α := PairIndex K) p
    (NumericalBounds.p_nonneg h) (NumericalBounds.p_le_one h)
  let G : Sample K → Family V := fun sample =>
    C0 ∪ sampledFamily K sample ∪ residualFamily K m sample
  have hrho : 0 ≤ rho := hrho0.le
  have hT : 0 ≤ T := NumericalBounds.T_nonneg h
  have hK : K ⊆ H := regularEdges_subset H rho r T
  have hKuniform : ∀ e ∈ K, e.card = r := fun e he => uniform e (hK he)
  have hcover (sample : Sample K) : Covers (G sample) (denseFamily H m) :=
    covers_sampled_residual H C0 m sample
  have hC0 : cost rho C0 ≤ 2 * ((2 : ℝ) ^ (2 * h))⁻¹ := by
    calc
      cost rho C0 ≤ T⁻¹ * (2 : ℝ) ^ r * (H.card : ℝ) * rho ^ r :=
        initial_cost_le hrho (NumericalBounds.T_pos h) uniform
      _ = (T⁻¹ * (2 : ℝ) ^ r) * ((H.card : ℝ) * rho ^ r) := by ring
      _ ≤ (T⁻¹ * (2 : ℝ) ^ r) * (2 : ℝ) ^ (h + 1) :=
        mul_le_mul_of_nonneg_left hweight
          (mul_nonneg (inv_nonneg.mpr hT) (pow_nonneg (by norm_num) _))
      _ ≤ 2 * ((2 : ℝ) ^ (2 * h))⁻¹ := NumericalBounds.initial_cost_le r h hrh
  have hC1 : μ.expectation (fun sample => cost rho (sampledFamily K sample)) ≤
      2 * ((2 : ℝ) ^ (2 * h))⁻¹ := by
    calc
      μ.expectation (fun sample => cost rho (sampledFamily K sample)) ≤
          p * ((H.card : ℝ) * rho ^ r * (2 : ℝ) ^ r * T) :=
        expectation_sampledFamily_le hrho hT uniform
          (NumericalBounds.p_nonneg h) (NumericalBounds.p_le_one h)
      _ = (p * (2 : ℝ) ^ r * T) * ((H.card : ℝ) * rho ^ r) := by ring
      _ ≤ (p * (2 : ℝ) ^ r * T) * (2 : ℝ) ^ (h + 1) :=
        mul_le_mul_of_nonneg_left hweight
          (mul_nonneg (mul_nonneg (NumericalBounds.p_nonneg h)
            (pow_nonneg (by norm_num) _)) hT)
      _ = p * (2 : ℝ) ^ (h + 1) * (2 : ℝ) ^ r * T := by ring
      _ ≤ 2 * ((2 : ℝ) ^ (2 * h))⁻¹ := NumericalBounds.pair_cost_le r h hrh
  have hC2 : μ.expectation (fun sample => cost rho (residualFamily K m sample)) ≤
      ((2 : ℝ) ^ m)⁻¹ :=
    expectation_residualFamily_le_inv_pow K hrho hKuniform
      (fun B => regular_extension_le_pow hrho hT uniform B) hrh hh
  have hmean : μ.expectation (fun sample => cost rho (G sample)) ≤
      3 * ((2 : ℝ) ^ h)⁻¹ := by
    calc
      μ.expectation (fun sample => cost rho (G sample)) ≤
          μ.expectation (fun sample => cost rho C0 +
            cost rho (sampledFamily K sample) + cost rho (residualFamily K m sample)) := by
        apply μ.expectation_mono
        intro sample
        exact (cost_union_le hrho (C0 ∪ sampledFamily K sample)
          (residualFamily K m sample)).trans
            (add_le_add (cost_union_le hrho C0 (sampledFamily K sample)) le_rfl)
      _ = cost rho C0 + μ.expectation (fun sample => cost rho (sampledFamily K sample)) +
          μ.expectation (fun sample => cost rho (residualFamily K m sample)) := by
        rw [μ.expectation_add, μ.expectation_add, μ.expectation_const]
      _ ≤ 4 * ((2 : ℝ) ^ (2 * h))⁻¹ + ((2 : ℝ) ^ m)⁻¹ := by
        linarith
      _ ≤ 3 * ((2 : ℝ) ^ h)⁻¹ := NumericalBounds.final_cost_le h hh
  obtain ⟨sample, hsample⟩ := μ.exists_le_expectation (fun sample => cost rho (G sample))
  exact ⟨G sample, hcover sample, hsample.trans hmean⟩

end TalagrandDiscreteConvexity.Covering

end OAI

-- ---- platform node ----
open OAI OAI.TalagrandDiscreteConvexity OAI.TalagrandDiscreteConvexity.Covering
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.TalagrandDiscreteConvexity.Covering.elementary_covering := @_root_.OAI.TalagrandDiscreteConvexity.Covering.elementary_covering
