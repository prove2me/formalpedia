-- Prove2me | solution 1 for OAI.TalagrandDiscreteConvexity.original_density_small
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T17:03:06.363318+00:00
-- url     : https://prove2.me/submissions/63fcd4b3-c7ec-465d-9e48-35c095f2eb6d

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/DiscreteConvexity/Main.lean:L22-L59
-- (upload_full_project.md Phase 4): solution for node OAI.TalagrandDiscreteConvexity.original_density_small. The node keeps its source
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
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_LabelCoupling
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_MandatoryCoupling
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_UnionTuples
import Theorems.Thm_OAI_TalagrandDiscreteConvexity_FiniteLaw_expectation_pi_coordinate
import Theorems.Thm_OAI_TalagrandDiscreteConvexity_FiniteLaw_prob_exists_le
import Theorems.Thm_OAI_TalagrandDiscreteConvexity_FiniteLaw_prob_prod
import Theorems.Thm_OAI_TalagrandDiscreteConvexity_exceptional_lower_bound_of_signed_sum
import Theorems.Thm_OAI_TalagrandDiscreteConvexity_exceptional_signed_summand_eq_zero
import Theorems.Thm_OAI_TalagrandDiscreteConvexity_familyMeasure_unionFamily_label_lower
import Theorems.Thm_OAI_TalagrandDiscreteConvexity_prob_pi_cubeSet_mem_family
import Theorems.Thm_OAI_TalagrandDiscreteConvexity_rowKernel_gram
import Theorems.Thm_OAI_TalagrandDiscreteConvexity_signed_array_identity
import Theorems.Thm_OAI_TalagrandDiscreteConvexity_unionFamily_mul
import Theorems.Thm_OAI_TalagrandDiscreteConvexity_weighted_kernel_bilinear
import Theorems.Thm_OAI_TalagrandDiscreteConvexity_weights_small

-- ---- from OAI.Combinatorics.DiscreteConvexity.Basic ----
namespace OAI

namespace TalagrandDiscreteConvexity

open scoped BigOperators

variable {α : Type*} [Fintype α] [DecidableEq α]

noncomputable section

omit [Fintype α] [DecidableEq α] in
theorem small_empty (p : ℝ) : Small p (∅ : Family α) := by
  refine ⟨∅, covers_empty _, ?_⟩
  simp

theorem mem_exceptional_iff_unionFamily {k : ℕ} {D : Family α} {S : Finset α} :
    S ∈ exceptional k D ↔ ∀ T ∈ unionFamily k D, ¬ S ⊆ T := by
  constructor
  · intro h T hT
    obtain ⟨f, hf, rfl⟩ := mem_unionFamily.mp hT
    exact mem_exceptional.mp h f hf
  · intro h
    apply mem_exceptional.mpr
    intro f hf
    exact h (unionTuple f) (mem_unionFamily.mpr ⟨f, hf, rfl⟩)

theorem exceptional_eq_empty_of_full_union {k : ℕ} {D : Family α}
    (f : Fin k → Finset α) (hf : ∀ j, f j ∈ D) (hfull : unionTuple f = Finset.univ) :
    exceptional k D = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro S hS
  exact mem_exceptional.mp hS f hf (hfull.symm ▸ Finset.subset_univ S)

theorem familyIndicator_le_one (D : Family α) (x : α → Bool) :
    familyIndicator D x ≤ 1 := by
  unfold familyIndicator
  split_ifs <;> simp

theorem familyIndicator_sq (D : Family α) (x : α → Bool) :
    familyIndicator D x ^ 2 = familyIndicator D x := by
  unfold familyIndicator
  split_ifs <;> simp

end
end TalagrandDiscreteConvexity

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

theorem prob_eq_expectation (μ : FiniteLaw Ω) (P : Ω → Prop) :
    μ.prob P = μ.expectation (fun ω => if P ω then 1 else 0) := by
  classical
  simp [prob, expectation, mul_ite]

theorem uniform_prob (Ω : Type*) [Fintype Ω] [Nonempty Ω] (P : Ω → Prop) :
    (uniform Ω).prob P = ((Finset.univ.filter P).card : ℝ) / Fintype.card Ω := by
  simp [prob, uniform, ← Finset.sum_filter, div_eq_mul_inv]

end FiniteLaw

end TalagrandDiscreteConvexity

end

end OAI

-- ---- from OAI.Combinatorics.DiscreteConvexity.Bernoulli ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
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

theorem bernoulliWeight_eq_mass (p : ℝ) (s : Finset α) :
    bernoulliWeight p s = bernoulliMass p s := by
  simp only [bernoulliWeight, bernoulliMass, Finset.prod_ite,
    Finset.filter_mem_eq_inter, Finset.univ_inter,
    Finset.filter_notMem_eq_sdiff, Finset.prod_const]

omit [DecidableEq α] in
theorem cubeWeight_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (x : α → Bool) :
    0 ≤ cubeWeight p x :=
  Finset.prod_nonneg (fun i _ => bitWeight_nonneg hp0 hp1 (x i))

theorem cubeWeight_sum (p : ℝ) : ∑ x : α → Bool, cubeWeight p x = 1 := by
  rw [← (finsetBoolEquiv (α := α)).sum_comp (cubeWeight p)]
  simpa only [cubeWeight_finsetBoolEquiv] using bernoulliWeight_sum (α := α) p

theorem cubeExpectation_eq_bernoulliExpectation (p : ℝ) (f : (α → Bool) → ℝ) :
    cubeExpectation p f = bernoulliExpectation p (fun s => f (finsetBoolEquiv s)) := by
  unfold cubeExpectation bernoulliExpectation
  rw [← (finsetBoolEquiv (α := α)).sum_comp (fun x => cubeWeight p x * f x)]
  simp only [cubeWeight_finsetBoolEquiv]

theorem cubeExpectation_familyIndicator (p : ℝ) (D : Family α) :
    cubeExpectation p (familyIndicator D) = familyMeasure p D := by
  rw [cubeExpectation_eq_bernoulliExpectation]
  simp only [bernoulliExpectation, familyIndicator, cubeSet_finsetBoolEquiv,
    mul_ite, mul_one, mul_zero, bernoulliWeight_eq_mass]
  rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
  rfl

end TalagrandDiscreteConvexity

end

end OAI

-- ---- from OAI.Combinatorics.DiscreteConvexity.ProbabilisticExistence ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

/-!
# Extracting outcomes from a finite probability law

Normalization guarantees a positive-weight outcome. It also guarantees an
outcome below the expectation and a witness to every positive-probability
event; strict positivity of every individual mass is not required.
-/

namespace TalagrandDiscreteConvexity.FiniteLaw

open scoped BigOperators

variable {Ω : Type*} [Fintype Ω]

theorem exists_of_prob_pos (μ : FiniteLaw Ω) {P : Ω → Prop}
    (hP : 0 < μ.prob P) : ∃ ω, P ω := by
  classical
  by_contra h
  have hz : μ.prob P = 0 := by
    unfold prob
    apply Finset.sum_eq_zero
    intro ω _
    exact ite_eq_right (fun hp => h ⟨ω, hp⟩)
  exact (ne_of_gt hP) hz

end TalagrandDiscreteConvexity.FiniteLaw

end OAI

-- ---- from OAI.Combinatorics.DiscreteConvexity.FourierWeights ----
namespace OAI

noncomputable section
open scoped BigOperators

namespace TalagrandDiscreteConvexity

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem w_nonneg (q : ℝ) (f : (V → Bool) → ℝ) (U : Finset V) :
    0 ≤ w q f U := sq_nonneg _

end TalagrandDiscreteConvexity

end

end OAI

-- ---- from OAI.Combinatorics.DiscreteConvexity.FiniteParseval ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-!
# Finite Parseval identities from a weighted kernel

The algebraic statement below separates finite-sum rearrangement from the
concrete kernel identity. Neither the expansion nor the Parseval identity
requires nonnegative weights.
-/

namespace TalagrandDiscreteConvexity

open scoped BigOperators

variable {I J : Type*} [Fintype I] [Fintype J]

variable [DecidableEq J]

/-- Finite Parseval follows from the weighted kernel identity. -/
theorem weighted_kernel_parseval
    (K : I → J → ℝ) (r : I → ℝ) (μ : J → ℝ)
    (hkernel : ∀ x y, (∑ u, r u * K u x * K u y) =
      if x = y then μ x else 0) (f : J → ℝ) :
    (∑ u, r u * (∑ x, f x * K u x) ^ 2) =
      ∑ x, μ x * (f x) ^ 2 := by
  simpa only [pow_two, mul_assoc] using weighted_kernel_bilinear K r μ hkernel f f

end TalagrandDiscreteConvexity

end OAI

-- ---- from OAI.Combinatorics.DiscreteConvexity.FourierGlobalBound ----
namespace OAI

/-!
# Biased Parseval and the global weight bound

The exact Parseval multiplier for the unnormalized coefficients is
`(q / (1-q))^|U|`. The desired multiplier `q^|U|` is smaller for `0 < q < 1`.
The actual product-kernel identity proves Parseval here; it is not a hypothesis
of the global bound or its family-indicator specialization.
-/

noncomputable section
open scoped BigOperators

namespace TalagrandDiscreteConvexity

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Square-root-free biased Parseval for the actual alternating coefficients. -/
theorem biased_parseval (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1)
    (f : (V → Bool) → ℝ) :
    (∑ U : Finset V, (q / (1 - q)) ^ U.card * w q f U) =
      cubeExpectation q (fun x => (f x) ^ 2) := by
  simpa only [b, w, cubeExpectation] using
    weighted_kernel_parseval (rowKernel q)
      (fun U : Finset V => (q / (1 - q)) ^ U.card)
      (cubeWeight q) (rowKernel_gram q hq0 hq1) f

theorem weight_sum_le_second_moment (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1)
    (f : (V → Bool) → ℝ) :
    (∑ U : Finset V, q ^ U.card * w q f U) ≤
      cubeExpectation q (fun x => (f x) ^ 2) := by
  rw [← biased_parseval q hq0 hq1 f]
  have hratio : q ≤ q / (1 - q) := by
    apply (le_div_iff₀ (sub_pos.mpr hq1)).mpr
    nlinarith [sq_nonneg q]
  apply Finset.sum_le_sum
  intro U _
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ hq0.le hratio U.card) (w_nonneg q f U)

/-- A bounded-square function has global weight sum at most one. -/
theorem global_weight_bound (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1)
    (f : (V → Bool) → ℝ) (hf : ∀ x, (f x) ^ 2 ≤ 1) :
    (∑ U : Finset V, q ^ U.card * w q f U) ≤ 1 := by
  apply (weight_sum_le_second_moment q hq0 hq1 f).trans
  calc
    cubeExpectation q (fun x => (f x) ^ 2) ≤
        ∑ x : V → Bool, cubeWeight q x := by
      unfold cubeExpectation
      apply Finset.sum_le_sum
      intro x _
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left (hf x) (cubeWeight_nonneg hq0.le hq1.le x)
    _ = 1 := cubeWeight_sum q

/-- The global weight bound for the actual indicator of an arbitrary family.
No monotonicity or density assumption on the family is needed. -/
theorem indicator_global_weight_bound (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1)
    (D : Family V) :
    (∑ U : Finset V, q ^ U.card * w q (familyIndicator D) U) ≤ 1 := by
  apply global_weight_bound q hq0 hq1 (familyIndicator D)
  intro x
  rw [familyIndicator_sq]
  exact familyIndicator_le_one D x

end TalagrandDiscreteConvexity

end

end OAI

-- ---- from OAI.Combinatorics.DiscreteConvexity.SignedArrays ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-!
# Signed arrays force weight on every exceptional set

The arrays have one common set of rows. Each column in `S` receives the
Bernoulli product mass minus the product of the alternating corrections.
All-zero columns in `S` have zero signed mass. This gives pointwise vanishing
for exceptional sets, without any nonnegativity assumption on these masses.
Expanding the column products and summing independently over the rows gives
the exact signed coefficient identity.
-/

noncomputable section

open scoped BigOperators

namespace TalagrandDiscreteConvexity

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The exact vanishing signed expansion on an exceptional set. -/
theorem exceptional_signed_sum_eq_zero (q : ℝ) {k : ℕ}
    {D : Family V} {S : Finset V} (hS : S ∈ exceptional k D) :
    (∑ U ∈ S.powerset, (-1 : ℝ) ^ U.card * b q (familyIndicator D) U ^ k) = 0 := by
  rw [← signed_array_identity]
  apply Finset.sum_eq_zero
  intro X _
  exact exceptional_signed_summand_eq_zero q hS X

/-- The actual exceptional-weight bound, at the original family density. -/
theorem exceptional_weight_lower_bound (q : ℝ)
    {D : Family V} (hD : (1 / 2 : ℝ) ≤ familyMeasure q D)
    {S : Finset V} (hS : S ∈ exceptional 32 D) :
    (1 / 2 : ℝ) ^ 32 ≤
      ∑ U ∈ S.powerset.erase ∅, w q (familyIndicator D) U ^ 16 := by
  apply exceptional_lower_bound_of_signed_sum S (b q (familyIndicator D))
    (exceptional_signed_sum_eq_zero q hS)
  simpa only [b_empty, cubeExpectation_familyIndicator] using hD

end TalagrandDiscreteConvexity

end

end OAI

-- ---- from OAI.Combinatorics.DiscreteConvexity.HalfDensity ----
namespace OAI

/-!
# Small exceptional families at a fixed fraction of the density

The actual biased Fourier weights satisfy both estimates needed by the finite
bin construction.  No monotonicity of the given family is assumed.
-/

namespace TalagrandDiscreteConvexity

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem halfDensity_small {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (F : Family α) (hF : (1 / 2 : ℝ) ≤ familyMeasure q F) :
    Small (q / (2 : ℝ) ^ 70) (exceptional 32 F) := by
  exact weights_small hq0 hq1 (exceptional 32 F) (w q (familyIndicator F))
    (w_nonneg q (familyIndicator F)) (indicator_global_weight_bound q hq0 hq1 F)
    (fun _ hS => exceptional_weight_lower_bound q hF hS)

end TalagrandDiscreteConvexity

end OAI

-- ---- from OAI.Combinatorics.DiscreteConvexity.DensityConstants ----
namespace OAI

/-!
# Symbolic constants for the original-density argument

Only the small factor `32 = 2^5` is evaluated. The number of rows and the
final tuple length remain symbolic powers throughout the construction.
-/

namespace TalagrandDiscreteConvexity

theorem density_rows_gt_one : 1 < (2 : ℕ) ^ 70 :=
  one_lt_pow' (by decide : (1 : ℕ) < 2) (by decide : (70 : ℕ) ≠ 0)

theorem density_rows_pos : 0 < (2 : ℕ) ^ 70 :=
  lt_trans Nat.zero_lt_one density_rows_gt_one

theorem density_tuple_count : 32 * (2 : ℕ) ^ 70 = 2 ^ 75 := by
  rw [show (32 : ℕ) = 2 ^ 5 by decide, ← pow_add]

theorem density_tuple_count_real : (2 : ℝ) ^ 75 = 32 * (2 : ℝ) ^ 70 := by
  calc
    (2 : ℝ) ^ 75 = 2 ^ 5 * 2 ^ 70 := by rw [← pow_add]
    _ = 32 * 2 ^ 70 := by rw [show (2 : ℝ) ^ 5 = 32 by norm_num]

/-- A density loss of at most `1 / (32 L)` spends at most `1 / 32` across rows. -/
theorem density_failure_budget {L a : ℝ} (hL : 0 < L)
    (ha : 1 - 1 / (32 * L) ≤ a) : L * (1 - a) ≤ 1 / 32 := by
  have hbound : 1 - a ≤ 1 / (32 * L) := by linarith
  calc
    L * (1 - a) ≤ L * (1 / (32 * L)) :=
      mul_le_mul_of_nonneg_left hbound hL.le
    _ = 1 / 32 := by field_simp [ne_of_gt hL]

end TalagrandDiscreteConvexity

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

/-- Events depending on one coordinate have their original probabilities. -/
theorem prob_pi_coordinate (μ : ∀ i, FiniteLaw (A i))
    (i : I) (P : A i → Prop) :
    (pi μ).prob (fun ω => P (ω i)) = (μ i).prob P := by
  classical
  rw [prob_eq_expectation, prob_eq_expectation]
  exact expectation_pi_coordinate μ i (fun a => if P a then 1 else 0)

end ProductCoordinates

variable {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]

end TalagrandDiscreteConvexity.FiniteLaw

end

end OAI

-- ---- from OAI.Combinatorics.DiscreteConvexity.UnionBound ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

open scoped BigOperators

namespace TalagrandDiscreteConvexity.FiniteLaw

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι]

/-- Simultaneous success is bounded using only the individual marginals. -/
theorem prob_forall_ge (μ : FiniteLaw Ω) (P : ι → Ω → Prop) :
    1 - ∑ i, (1 - μ.prob (P i)) ≤ μ.prob (fun ω => ∀ i, P i ω) := by
  classical
  have hbad := prob_exists_le μ (fun i ω => ¬ P i ω)
  have hcompl : μ.prob (fun ω => ¬ ∀ i, P i ω) ≤
      ∑ i, μ.prob (fun ω => ¬ P i ω) := by
    simpa only [not_forall] using hbad
  rw [μ.prob_compl] at hcompl
  simp_rw [μ.prob_compl] at hcompl
  linarith

theorem prob_forall_ge_of_const (μ : FiniteLaw Ω) (P : ι → Ω → Prop)
    (a : ℝ) (hmarginal : ∀ i, μ.prob (P i) = a) :
    1 - (Fintype.card ι : ℝ) * (1 - a) ≤ μ.prob (fun ω => ∀ i, P i ω) := by
  have h := prob_forall_ge μ P
  simpa only [hmarginal, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using h

theorem exists_forall_of_const (μ : FiniteLaw Ω) (P : ι → Ω → Prop)
    (a : ℝ) (hmarginal : ∀ i, μ.prob (P i) = a)
    (hbudget : (Fintype.card ι : ℝ) * (1 - a) < 1) :
    ∃ ω, ∀ i, P i ω := by
  apply exists_of_prob_pos μ (P := fun ω => ∀ i, P i ω)
  have h := prob_forall_ge_of_const μ P a hmarginal
  linarith

end TalagrandDiscreteConvexity.FiniteLaw

end OAI

-- ---- from OAI.Combinatorics.DiscreteConvexity.MandatoryCoupling ----
namespace OAI

/-!
# The mandatory-row coupling at high density

The auxiliary inclusion probability is valid throughout the closed high-density
regime `1 ≤ L * p`, including equality, when it is zero.

At each coordinate the mandatory label is uniform and independent of the
independent Bernoulli marks. Taking a product of these laws across coordinates
gives each row its full Bernoulli subset law. The union is full in every outcome;
only marginal probabilities are used to obtain simultaneous family membership.
-/

noncomputable section

namespace TalagrandDiscreteConvexity

theorem mandatoryParameter_marginal {L : ℕ} (hL : 1 < L) (p : ℝ) :
    1 / (L : ℝ) + (1 - 1 / (L : ℝ)) * mandatoryParameter L p = p := by
  unfold mandatoryParameter
  rw [mul_div_cancel₀ _ (mandatoryParameter_den_pos hL).ne']
  ring

private theorem mandatory_prob_prod_or {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]
    (μ : FiniteLaw Ω) (ν : FiniteLaw Γ) (P : Ω → Prop) (Q : Γ → Prop) :
    (μ.prod ν).prob (fun z => P z.1 ∨ Q z.2) =
      μ.prob P + (1 - μ.prob P) * ν.prob Q := by
  classical
  have h := (μ.prod ν).prob_compl (fun z => P z.1 ∨ Q z.2)
  simp only [not_or] at h
  rw [FiniteLaw.prob_prod μ ν (fun ω => ¬ P ω) (fun γ => ¬ Q γ),
    μ.prob_compl P, ν.prob_compl Q] at h
  nlinarith only [h]

theorem mandatoryColumnLaw_marginal {L : ℕ} (hL : 1 < L) (p : ℝ)
    (hp : p < 1) (hLp : 1 ≤ (L : ℝ) * p) (j : Fin L) :
    (mandatoryColumnLaw hL p hp hLp).prob (fun z => mandatoryBit j z = true) = p := by
  classical
  let : Nonempty (Fin L) := ⟨⟨0, lt_trans Nat.zero_lt_one hL⟩⟩
  have hmandatory : (FiniteLaw.uniform (Fin L)).prob (fun k => k = j) =
      1 / (L : ℝ) := by
    rw [FiniteLaw.uniform_prob]
    simp only [Fintype.card_fin]
    congr 1
    norm_cast
    apply Finset.card_eq_one.mpr
    refine ⟨j, ?_⟩
    ext k
    simp
  have hmarks :
      (FiniteLaw.iid (bitLaw (mandatoryParameter L p)
        (mandatoryParameter_nonneg hL hLp) (mandatoryParameter_lt_one hL hp).le) L).prob
        (fun marks => marks j = true) = mandatoryParameter L p := by
    unfold FiniteLaw.iid
    rw [FiniteLaw.prob_pi_coordinate
      (fun _ : Fin L => bitLaw (mandatoryParameter L p)
        (mandatoryParameter_nonneg hL hLp) (mandatoryParameter_lt_one hL hp).le)
      j (fun b : Bool => b = true)]
    exact bitLaw_prob_true _ _ _
  unfold mandatoryColumnLaw
  simp only [mandatoryBit, decide_eq_true_eq]
  rw [mandatory_prob_prod_or (FiniteLaw.uniform (Fin L))
    (FiniteLaw.iid (bitLaw (mandatoryParameter L p)
      (mandatoryParameter_nonneg hL hLp) (mandatoryParameter_lt_one hL hp).le) L)
    (fun k : Fin L => k = j) (fun marks : Fin L → Bool => marks j = true),
    hmandatory, hmarks]
  exact mandatoryParameter_marginal hL p

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The row distribution agrees on arbitrary, potentially nonmonotone families. -/
theorem mandatoryRows_prob_mem_family {L : ℕ} (hL : 1 < L) (p : ℝ)
    (hp : p < 1) (hLp : 1 ≤ (L : ℝ) * p) (j : Fin L) (D : Family α) :
    (mandatoryArrayLaw (α := α) hL p hp hLp).prob
      (fun ω => mandatoryRows ω j ∈ D) = familyMeasure p D := by
  exact prob_pi_cubeSet_mem_family (fun _ : α => mandatoryColumnLaw hL p hp hLp)
    (fun _ => mandatoryBit j) p (fun _ => mandatoryColumnLaw_marginal hL p hp hLp j) D

/-- The selected mandatory row contains each coordinate in every outcome. -/
theorem mandatoryRows_union {L : ℕ} (ω : α → MandatoryColumn L) :
    unionTuple (mandatoryRows ω) = Finset.univ := by
  ext i
  simp only [Finset.mem_univ, iff_true]
  apply mem_unionTuple.mpr
  refine ⟨(ω i).1, ?_⟩
  exact mem_cubeSet.mpr (mandatoryBit_mandatory (ω i))

/-- Marginal success probabilities and the union bound give a covering tuple.
There is no independence assumption between the rows. -/
theorem exists_mandatory_cover {L : ℕ} (hL : 1 < L) (p : ℝ)
    (hp : p < 1) (hLp : 1 ≤ (L : ℝ) * p) (D : Family α)
    (hbudget : (L : ℝ) * (1 - familyMeasure p D) < 1) :
    ∃ rows : Fin L → Finset α,
      (∀ j, rows j ∈ D) ∧ unionTuple rows = Finset.univ := by
  have hmarginal (j : Fin L) :
      (mandatoryArrayLaw (α := α) hL p hp hLp).prob
        (fun ω => mandatoryRows ω j ∈ D) = familyMeasure p D :=
    mandatoryRows_prob_mem_family hL p hp hLp j D
  have hbudget' : (Fintype.card (Fin L) : ℝ) * (1 - familyMeasure p D) < 1 := by
    simpa only [Fintype.card_fin] using hbudget
  obtain ⟨ω, hω⟩ := FiniteLaw.exists_forall_of_const
    (mandatoryArrayLaw (α := α) hL p hp hLp)
    (fun j ω => mandatoryRows ω j ∈ D) (familyMeasure p D) hmarginal hbudget'
  exact ⟨mandatoryRows ω, hω, mandatoryRows_union ω⟩

end TalagrandDiscreteConvexity

end

end OAI

-- ---- from OAI.Combinatorics.DiscreteConvexity.UnionTuples ----
namespace OAI

/-!
# Grouping and repeating union tuples

Grouping `a * b` entries into `a` rows of length `b` preserves exactly the
possible unions. Repetition is allowed throughout, as in the definition of
the exceptional family. No positivity assumption is needed for grouping.
-/

namespace TalagrandDiscreteConvexity

variable {α : Type*} [Fintype α] [DecidableEq α]

omit [Fintype α] in
theorem unionTuple_flatten {a b : ℕ} (f : Fin a → Fin b → Finset α) :
    unionTuple (flattenTuple f) = unionTuple (fun i => unionTuple (f i)) := by
  ext x
  simp only [mem_unionTuple]
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨(finProdFinEquiv.symm t).1, (finProdFinEquiv.symm t).2, ht⟩
  · rintro ⟨i, j, hij⟩
    refine ⟨finProdFinEquiv (i, j), ?_⟩
    simpa only [flattenTuple, Equiv.symm_apply_apply] using hij

/-- Grouping tuples preserves failure of containment in every possible union. -/
theorem exceptional_unionFamily (a b : ℕ) (D : Family α) :
    exceptional a (unionFamily b D) = exceptional (a * b) D := by
  ext S
  simp only [mem_exceptional_iff_unionFamily, unionFamily_mul]

omit [Fintype α] [DecidableEq α] in
theorem repeatTuple_mem {a b : ℕ} {D : Family α} (f : Fin b → Finset α)
    (hf : ∀ j, f j ∈ D) (t : Fin (a * b)) : repeatTuple a f t ∈ D :=
  hf (finProdFinEquiv.symm t).2

omit [Fintype α] in
theorem unionTuple_repeat {a b : ℕ} (ha : 0 < a) (f : Fin b → Finset α) :
    unionTuple (repeatTuple a f) = unionTuple f := by
  rw [repeatTuple, unionTuple_flatten]
  ext x
  simp only [mem_unionTuple]
  constructor
  · rintro ⟨_, j, hj⟩
    exact ⟨j, hj⟩
  · rintro ⟨j, hj⟩
    exact ⟨⟨0, ha⟩, j, hj⟩

theorem exists_unionTuple_mul_eq_univ {a b : ℕ} (ha : 0 < a) {D : Family α}
    (f : Fin b → Finset α) (hf : ∀ j, f j ∈ D)
    (hfull : unionTuple f = Finset.univ) :
    ∃ g : Fin (a * b) → Finset α, (∀ j, g j ∈ D) ∧ unionTuple g = Finset.univ := by
  refine ⟨repeatTuple a f, repeatTuple_mem f hf, ?_⟩
  rw [unionTuple_repeat ha, hfull]

theorem exceptional_mul_eq_empty_of_full_union {a b : ℕ} (ha : 0 < a) {D : Family α}
    (f : Fin b → Finset α) (hf : ∀ j, f j ∈ D)
    (hfull : unionTuple f = Finset.univ) : exceptional (a * b) D = ∅ := by
  obtain ⟨g, hg, hgfull⟩ := exists_unionTuple_mul_eq_univ ha f hf hfull
  exact exceptional_eq_empty_of_full_union g hg hgfull

end TalagrandDiscreteConvexity

end OAI

-- ---- from OAI.Combinatorics.DiscreteConvexity.Main ----
namespace OAI

/-!
# Talagrand discrete convexity at the original density

Independent coordinate choices produce dependent rows with full Bernoulli
subset laws. The label construction raises the union density when `L p < 1`;
the mandatory-row construction covers every coordinate when `1 ≤ L p`.
Both cases use the same row-failure budget, without independence between rows.
-/

namespace TalagrandDiscreteConvexity

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The density reduction works on any finite ground set. -/
theorem original_density_small (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (D : Family α) (hD : 1 - 1 / (2 : ℝ) ^ 75 ≤ familyMeasure p D) :
    Small p (exceptional ((2 : ℕ) ^ 75) D) := by
  let L : ℕ := 2 ^ 70
  have hL : 1 < L := density_rows_gt_one
  have hLpos : (0 : ℝ) < (L : ℝ) := by
    exact_mod_cast density_rows_pos
  have hLcast : (L : ℝ) = (2 : ℝ) ^ 70 := by
    simp only [L, Nat.cast_pow, Nat.cast_ofNat]
  have hcount : 32 * L = (2 : ℕ) ^ 75 := density_tuple_count
  have hD' : 1 - 1 / (32 * (L : ℝ)) ≤ familyMeasure p D := by
    rw [hLcast, ← density_tuple_count_real]
    exact hD
  have hbudget : (L : ℝ) * (1 - familyMeasure p D) ≤ 1 / 32 :=
    density_failure_budget hLpos hD'
  by_cases hlow : (L : ℝ) * p < 1
  · have hq0 : 0 < (L : ℝ) * p := mul_pos hLpos hp0
    have hmeasure := familyMeasure_unionFamily_label_lower L p hp0.le hlow.le D
    have hhalf : (1 / 2 : ℝ) ≤ familyMeasure ((L : ℝ) * p) (unionFamily L D) := by
      calc
        (1 / 2 : ℝ) ≤ 1 - 1 / 32 := by norm_num
        _ ≤ 1 - (L : ℝ) * (1 - familyMeasure p D) := sub_le_sub_left hbudget 1
        _ ≤ familyMeasure ((L : ℝ) * p) (unionFamily L D) := hmeasure
    have hsmall := halfDensity_small hq0 hlow (unionFamily L D) hhalf
    have hquot : ((L : ℝ) * p) / (2 : ℝ) ^ 70 = p := by
      rw [← hLcast]
      exact mul_div_cancel_left₀ p hLpos.ne'
    rw [hquot, exceptional_unionFamily, hcount] at hsmall
    exact hsmall
  · have hhigh : 1 ≤ (L : ℝ) * p := le_of_not_gt hlow
    obtain ⟨rows, hrows, hfull⟩ := exists_mandatory_cover hL p hp1 hhigh D
      (hbudget.trans_lt (by norm_num : (1 / 32 : ℝ) < 1))
    have hempty := exceptional_mul_eq_empty_of_full_union
      (a := 32) (by decide : 0 < 32) rows hrows hfull
    rw [hcount] at hempty
    rw [hempty]
    exact small_empty p

end TalagrandDiscreteConvexity

end OAI

-- ---- platform node ----
open OAI OAI.TalagrandDiscreteConvexity


theorem solution : type_of% @_root_.OAI.TalagrandDiscreteConvexity.original_density_small := @_root_.OAI.TalagrandDiscreteConvexity.original_density_small
