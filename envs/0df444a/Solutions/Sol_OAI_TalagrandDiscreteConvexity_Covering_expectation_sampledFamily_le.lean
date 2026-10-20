-- Prove2me | solution 1 for OAI.TalagrandDiscreteConvexity.Covering.expectation_sampledFamily_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T16:35:02.482003+00:00
-- url     : https://prove2.me/submissions/010c082e-008a-4a8c-a72c-8a8f119b2d42

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/DiscreteConvexity/CoveringPairCost.lean:L60-L78
-- (upload_full_project.md Phase 4): solution for node OAI.TalagrandDiscreteConvexity.Covering.expectation_sampledFamily_le. The node keeps its source
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
import Theorems.Thm_OAI_TalagrandDiscreteConvexity_Covering_regular_extension_le_card
import Theorems.Thm_OAI_TalagrandDiscreteConvexity_bernoulliLaw_expect_sum_mem

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

/-- The exact binomial extension bound from the covering lemma. -/
theorem regular_extension_le_choose {H : Family V} {rho T : ℝ} {r : ℕ}
    (hρ : 0 ≤ rho) (hT : 0 ≤ T) (hH : ∀ e ∈ H, e.card = r) (B : Finset V) :
    (∑ e ∈ regularEdges H rho r T, rho ^ (e \ B).card) ≤
      T * (∑ i ∈ Finset.range (r + 1), (Nat.choose B.card i : ℝ)) := by
  calc
    _ ≤ T * ((B.powerset.filter (fun I => I.card ≤ r)).card : ℝ) :=
      regular_extension_le_card hρ hT hH B
    _ = _ := by rw [card_subsets_card_le, Nat.cast_sum]

/-- An `r`-element prefix gives the sharper factor `2^r`, used for pairs. -/
theorem regular_extension_le_two_pow {H : Family V} {rho T : ℝ} {r : ℕ}
    (hρ : 0 ≤ rho) (hT : 0 ≤ T) (hH : ∀ e ∈ H, e.card = r)
    {B : Finset V} (hB : B.card = r) :
    (∑ e ∈ regularEdges H rho r T, rho ^ (e \ B).card) ≤ (2 : ℝ) ^ r * T := by
  have h := regular_extension_le_choose hρ hT hH B
  rw [hB, ← Nat.cast_sum, Nat.sum_range_choose, Nat.cast_pow, Nat.cast_ofNat] at h
  simpa only [mul_comm] using h

end TalagrandDiscreteConvexity.Covering

end OAI

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

/-- Counting each sampled ordered pair separately bounds the family cost. -/
theorem cost_sampledFamily_le (H : Family V) (sample : Sample H)
    {rho : ℝ} (hrho : 0 ≤ rho) :
    cost rho (sampledFamily H sample) ≤
      ∑ p ∈ sample, rho ^ (pairUnion p).card := by
  classical
  unfold cost sampledFamily
  exact Finset.sum_image_le_of_nonneg
    (fun I _ => pow_nonneg hrho I.card)

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

theorem expectation_mono (μ : FiniteLaw Ω) {f g : Ω → ℝ} (hfg : ∀ ω, f ω ≤ g ω) :
    μ.expectation f ≤ μ.expectation g :=
  Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (hfg ω) (μ.nonneg ω)

end FiniteLaw

end TalagrandDiscreteConvexity

end

end OAI

-- ---- from OAI.Combinatorics.DiscreteConvexity.CoveringPairCost ----
namespace OAI

/-!
# The cost of sampled ordered pairs

The expectation is bounded by counting pair unions with multiplicity. Its
deterministic bound uses the actual regularized edge family and the sharp
`2^r` extension estimate, rather than the coarser tuple-extension estimate.
-/

namespace TalagrandDiscreteConvexity.Covering

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem regular_pair_weight_sum_le {H : Family V} {rho T : ℝ} {r : ℕ}
    (hrho : 0 ≤ rho) (hT : 0 ≤ T) (hH : ∀ e ∈ H, e.card = r) :
    (∑ p : PairIndex (regularEdges H rho r T), rho ^ (pairUnion p).card) ≤
      (H.card : ℝ) * rho ^ r * (2 : ℝ) ^ r * T := by
  classical
  let K := regularEdges H rho r T
  have hK : K ⊆ H := regularEdges_subset H rho r T
  have hinner (a : K) :
      (∑ b : K, rho ^ (a.val ∪ b.val).card) ≤ rho ^ r * ((2 : ℝ) ^ r * T) := by
    have ha : a.val.card = r := hH a.val (hK a.property)
    have hext : (∑ b : K, rho ^ (b.val \ a.val).card) ≤ (2 : ℝ) ^ r * T := by
      rw [Finset.sum_coe_sort K (fun b : Finset V => rho ^ (b \ a.val).card)]
      exact regular_extension_le_two_pow hrho hT hH ha
    calc
      (∑ b : K, rho ^ (a.val ∪ b.val).card) =
          ∑ b : K, rho ^ r * rho ^ (b.val \ a.val).card := by
        apply Finset.sum_congr rfl
        intro b _
        rw [Finset.union_comm, ← Finset.card_sdiff_add_card, pow_add, ha]
        exact mul_comm _ _
      _ = rho ^ r * ∑ b : K, rho ^ (b.val \ a.val).card :=
        (Finset.mul_sum _ _ _).symm
      _ ≤ rho ^ r * ((2 : ℝ) ^ r * T) :=
        mul_le_mul_of_nonneg_left hext (pow_nonneg hrho _)
  have hcard : (K.card : ℝ) ≤ (H.card : ℝ) := by
    exact_mod_cast Finset.card_le_card hK
  have hfactor : 0 ≤ rho ^ r * ((2 : ℝ) ^ r * T) :=
    mul_nonneg (pow_nonneg hrho _) (mul_nonneg (pow_nonneg (by norm_num) _) hT)
  calc
    (∑ p : PairIndex K, rho ^ (pairUnion p).card) =
        ∑ a : K, ∑ b : K, rho ^ (a.val ∪ b.val).card := by
      simp only [PairIndex, Fintype.sum_prod_type, pairUnion]
    _ ≤ ∑ _a : K, rho ^ r * ((2 : ℝ) ^ r * T) :=
      Finset.sum_le_sum (fun a _ => hinner a)
    _ = (K.card : ℝ) * (rho ^ r * ((2 : ℝ) ^ r * T)) := by simp
    _ ≤ (H.card : ℝ) * (rho ^ r * ((2 : ℝ) ^ r * T)) :=
      mul_le_mul_of_nonneg_right hcard hfactor
    _ = (H.card : ℝ) * rho ^ r * (2 : ℝ) ^ r * T := by ring

/-- The actual independent pair sample has small expected generator cost.
No identification of equal unions is made at the probability-index level. -/
theorem expectation_sampledFamily_le {H : Family V} {rho T p : ℝ} {r : ℕ}
    (hrho : 0 ≤ rho) (hT : 0 ≤ T) (hH : ∀ e ∈ H, e.card = r)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (bernoulliLaw (α := PairIndex (regularEdges H rho r T)) p hp0 hp1).expectation
        (fun sample => cost rho (sampledFamily (regularEdges H rho r T) sample)) ≤
      p * ((H.card : ℝ) * rho ^ r * (2 : ℝ) ^ r * T) := by
  classical
  let K := regularEdges H rho r T
  let μ := bernoulliLaw (α := PairIndex K) p hp0 hp1
  calc
    μ.expectation (fun sample => cost rho (sampledFamily K sample)) ≤
        μ.expectation (fun sample => ∑ pair ∈ sample, rho ^ (pairUnion pair).card) :=
      μ.expectation_mono (fun sample => cost_sampledFamily_le K sample hrho)
    _ = p * ∑ pair : PairIndex K, rho ^ (pairUnion pair).card :=
      bernoulliLaw_expect_sum_mem p hp0 hp1 (fun pair => rho ^ (pairUnion pair).card)
    _ ≤ p * ((H.card : ℝ) * rho ^ r * (2 : ℝ) ^ r * T) :=
      mul_le_mul_of_nonneg_left (regular_pair_weight_sum_le hrho hT hH) hp0

end TalagrandDiscreteConvexity.Covering

end OAI

-- ---- platform node ----
open OAI OAI.TalagrandDiscreteConvexity OAI.TalagrandDiscreteConvexity.Covering
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.TalagrandDiscreteConvexity.Covering.expectation_sampledFamily_le := @_root_.OAI.TalagrandDiscreteConvexity.Covering.expectation_sampledFamily_le
