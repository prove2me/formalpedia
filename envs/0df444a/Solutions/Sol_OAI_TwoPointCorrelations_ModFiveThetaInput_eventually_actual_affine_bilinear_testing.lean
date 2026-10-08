-- Prove2me | solution 1 for OAI.TwoPointCorrelations.ModFiveThetaInput.eventually_actual_affine_bilinear_testing
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T03:26:59.252821+00:00
-- url     : https://prove2.me/submissions/cb6b148b-c70c-4c54-9a57-fbefe044ca97

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs
import Theorems.Thm_OAI_TwoPointCorrelations_BravermanDepth22Input_eventually_padding_test_progression_norm
import Theorems.Thm_OAI_TwoPointCorrelations_ModFiveThetaInput_eventually_actual_affine_spectral_tail_uniform
import Theorems.Thm_OAI_TwoPointCorrelations_ModFiveThetaInput_eventually_actual_pool_masses

section
-- module Solutions.OAIChowla.Compat
/-!
Backports of a few Mathlib lemmas from Mathlib d13f23b (the openai/math pin) to
Mathlib 0df444a, with the same names and statements and Mathlib's own proofs.
-/

open _root_.Polynomial




namespace Finset



end Finset

section LogSubst
open _root_.Real _root_.Set _root_.MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]





end LogSubst


/-- Special case of Mathlib d13f23b's `spectralRadius_le_nnnorm` (which dropped the
`NormOneClass` assumption of the older `spectrum.spectralRadius_le_nnnorm`) for operators. -/
theorem spectralRadius_le_nnnorm_clm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] (T : E →L[ℂ] E) : spectralRadius ℂ T ≤ ‖T‖₊ := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · have : Subsingleton (E →L[ℂ] E) := inferInstance
    simp [spectralRadius, spectrum.of_subsingleton T]
  · exact spectrum.spectralRadius_le_nnnorm T

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.CenterDegree
namespace OAI

/-!
# Degree control for products of prime centers

The argument is uniform in the indicators, so it applies both to integer
residues and to independent product residues. One prime is chosen from each
family, and the total number of lit prime coordinates controls the sum of
squared tuple weights.
-/

namespace TwoPointCorrelations

open _root_.Finset

lemma nonneg_product_le_power_card {ι : Type*} [Fintype ι]
    (b : ι → ℝ) (C : ℝ) (hb : ∀ i, 0 ≤ b i)
    (hsum : ∑ i, b i ≤ C * Fintype.card ι) :
    ∏ i, b i ≤ C ^ Fintype.card ι := by
  classical
  by_cases hn : Fintype.card ι = 0
  · have : IsEmpty ι := Fintype.card_eq_zero_iff.mp hn
    simp
  have hp : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hmean := Real.geom_mean_le_arith_mean (univ : Finset ι) (fun _ => (1 : ℝ)) b
    (fun _ _ => zero_le_one) (by simpa using hp) (fun i _ => hb i)
  simp only [Real.rpow_one, sum_const, card_univ, nsmul_eq_mul, mul_one, one_mul] at hmean
  have hbound : (∏ i, b i) ^ ((Fintype.card ι : ℝ)⁻¹) ≤ C :=
    hmean.trans ((div_le_iff₀ hp).mpr hsum)
  have hpow := pow_le_pow_left₀ (Real.rpow_nonneg (prod_nonneg (fun i _ => hb i)) _) hbound
    (Fintype.card ι)
  rw [Real.rpow_inv_natCast_pow (prod_nonneg (fun i _ => hb i)) hn] at hpow
  exact hpow


lemma centerMagnitude_nonneg (θ : ℝ) (lit : Bool) : 0 ≤ centerMagnitude θ lit :=
  abs_nonneg _

lemma centerMagnitude_le_one (θ : ℝ) (lit : Bool) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    centerMagnitude θ lit ≤ 1 := by
  cases lit <;> simp [centerMagnitude, abs_of_nonneg, abs_of_nonpos, hθ, sub_nonneg.mpr hθ1]
  all_goals linarith

lemma centerMagnitude_le_indicator_add (θ : ℝ) (lit : Bool) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    centerMagnitude θ lit ≤ (if lit then 1 else 0) + θ := by
  cases lit <;> simp [centerMagnitude, abs_of_nonneg, abs_of_nonpos, hθ, sub_nonneg.mpr hθ1]
  all_goals linarith

lemma center_family_sum_le {α : Type*} [Fintype α]
    (θ : α → ℝ) (lit : α → Bool) (hθ : ∀ p, 0 ≤ θ p) (hθ1 : ∀ p, θ p ≤ 1) :
    (∑ p, centerMagnitude (θ p) (lit p)) ≤
      (∑ p, if lit p then (1 : ℝ) else 0) + ∑ p, θ p := by
  rw [← sum_add_distrib]
  exact sum_le_sum (fun p _ => centerMagnitude_le_indicator_add _ _ (hθ p) (hθ1 p))

lemma squared_center_products_le_product
    {ι : Type*} [Fintype ι] [DecidableEq ι] {P : ι → Type*} [∀ i, Fintype (P i)]
    (θ : (i : ι) → P i → ℝ) (lit : (i : ι) → P i → Bool)
    (hθ : ∀ i p, 0 ≤ θ i p) (hθ1 : ∀ i p, θ i p ≤ 1) :
    (∑ x : (i : ι) → P i, (∏ i, centerMagnitude (θ i (x i)) (lit i (x i))) ^ 2) ≤
      ∏ i, ((∑ p : P i, if lit i p then (1 : ℝ) else 0) + ∑ p, θ i p) := by
  classical
  calc
    _ ≤ ∑ x : (i : ι) → P i, ∏ i, centerMagnitude (θ i (x i)) (lit i (x i)) := by
      apply sum_le_sum
      intro x _
      have h0 : 0 ≤ ∏ i, centerMagnitude (θ i (x i)) (lit i (x i)) :=
        prod_nonneg (fun i _ => centerMagnitude_nonneg _ _)
      have h1 : (∏ i, centerMagnitude (θ i (x i)) (lit i (x i))) ≤ 1 :=
        Finset.prod_le_one (fun i _ => centerMagnitude_nonneg _ _) (fun i _ =>
          centerMagnitude_le_one _ _ (hθ i _) (hθ1 i _))
      simpa only [pow_two, mul_one] using mul_le_mul_of_nonneg_left h1 h0
    _ = ∏ i, ∑ p, centerMagnitude (θ i p) (lit i p) :=
      (Fintype.prod_sum (fun i p => centerMagnitude (θ i p) (lit i p))).symm
    _ ≤ _ := by
      apply Finset.prod_le_prod
      · intro i _
        exact sum_nonneg (fun p _ => centerMagnitude_nonneg _ _)
      · intro i _
        exact center_family_sum_le (θ i) (lit i) (hθ i) (hθ1 i)

lemma sum_degree_budget {ι : Type*} [Fintype ι] (ω V : ι → ℝ) (W : ℝ)
    (hV : ∀ i, V i ≤ 2 * W)
    (hdegree : ∑ i, ω i ≤ 6 * W * Fintype.card ι) :
    ∑ i, (ω i + V i) ≤ (8 * W) * Fintype.card ι := by
  have hv : (∑ i, V i) ≤ (2 * W) * Fintype.card ι := by
    calc
      _ ≤ ∑ _i : ι, 2 * W := sum_le_sum (fun i _ => hV i)
      _ = _ := by simp; ring
  rw [sum_add_distrib]
  exact (add_le_add hdegree hv).trans_eq (by ring)

/-- The sitewise estimate `sum_d a_d(n)^2 ≤ (8W)^J`, with actual
one-prime-per-family products and a total lit-prime degree at most `6WJ`. -/
theorem squared_center_products_le
    {ι : Type*} [Fintype ι] [DecidableEq ι] {P : ι → Type*} [∀ i, Fintype (P i)]
    (θ : (i : ι) → P i → ℝ) (lit : (i : ι) → P i → Bool)
    (W : ℝ)
    (hθ : ∀ i p, 0 ≤ θ i p) (hθ1 : ∀ i p, θ i p ≤ 1)
    (hV : ∀ i, ∑ p, θ i p ≤ 2 * W)
    (hdegree : (∑ i, ∑ p : P i, if lit i p then (1 : ℝ) else 0) ≤
      6 * W * Fintype.card ι) :
    (∑ x : (i : ι) → P i, (∏ i, centerMagnitude (θ i (x i)) (lit i (x i))) ^ 2) ≤
      (8 * W) ^ Fintype.card ι := by
  classical
  apply (squared_center_products_le_product θ lit hθ hθ1).trans
  apply nonneg_product_le_power_card
  · intro i
    exact add_nonneg (sum_nonneg (fun p _ => by split_ifs <;> norm_num))
      (sum_nonneg (fun p _ => hθ i p))
  · exact sum_degree_budget (fun i => ∑ p : P i, if lit i p then (1 : ℝ) else 0)
      (fun i => ∑ p, θ i p) W hV hdegree

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.FiniteProbability
namespace OAI

/-!
# Finite weighted sampling for the random-prime rank argument

The prime labels in the rank argument have a nonuniform reciprocal law.
The corresponding finite-sum probability identities account for that law.
-/

namespace TwoPointCorrelations

open _root_.Finset


namespace FiniteLaw

variable {α β ι : Type*} [Fintype α] [Fintype β] [Fintype ι]




lemma average_mono (μ : FiniteLaw α) {f g : α → ℝ} (h : ∀ x, f x ≤ g x) :
    μ.average f ≤ μ.average g := sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (h x) (μ.nonneg x))















end FiniteLaw

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.LabeledForest
namespace OAI

/-!
# Labeled ordered forests

Binary trees use the first-child / next-sibling convention. The labels
are auxiliary: erasing them keeps the finite shape used by the code.
-/

namespace TwoPointCorrelations

open _root_.BinaryTree

variable {V : Type*}











@[simp] lemma attachForestLeaf_roots [DecidableEq V] (parent leaf : V) (t : BinaryTree V) :
    forestRoots (attachForestLeaf parent leaf t) = forestRoots t := by
  induction t with
  | nil => rfl
  | node v l r hl hr =>
      by_cases hv : v = parent <;> simp [attachForestLeaf, hv, forestRoots, hr]










end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.IndependentSampling
namespace OAI

/-! Product sampling and the atom bound for independent linear equations. -/

namespace TwoPointCorrelations

open _root_.Finset

variable {ι A : Type*} [Fintype ι] [DecidableEq ι]


omit [Fintype ι] in
@[simp] lemma joinCoordinates_mem (S : Finset ι) (x : S → A) (y : {i // i ∉ S} → A)
    (i : S) : joinCoordinates S x y i = x i := by simp [joinCoordinates, i.property]

omit [Fintype ι] in
@[simp] lemma joinCoordinates_notMem (S : Finset ι) (x : S → A) (y : {i // i ∉ S} → A)
    (i : {i // i ∉ S}) : joinCoordinates S x y i = y i := by simp [joinCoordinates, i.property]

namespace FiniteLaw

variable [Fintype A]






end FiniteLaw

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.MatrixAction
namespace OAI

/-! Concrete continuous operators associated with finite matrices. -/

namespace TwoPointCorrelations

open _root_.Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]


@[simp] lemma matrixOperator_apply (A : ι → ι → ℂ) (v : EuclideanSpace ℂ ι) (i : ι) :
    matrixOperator A v i = ∑ j, A i j * v j := rfl

lemma matrixOperator_selfAdjoint (A : ι → ι → ℂ)
    (hA : ∀ i j, A i j = star (A j i)) : IsSelfAdjoint (matrixOperator A) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  change (Matrix.toEuclideanLin A).IsSymmetric
  apply Matrix.isSymmetric_toEuclideanLin_iff.mpr
  ext i j
  exact (hA i j).symm

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ComplexPolarization
namespace OAI

/-! Four bounded quadratic tests recover an arbitrary complex bilinear test. -/

namespace TwoPointCorrelations

open scoped _root_.ComplexConjugate

section Hilbert

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]


theorem complex_polarization_four (T : E →L[ℂ] E) (u v : E) :
    inner ℂ u (T v) =
      inner ℂ (halfPair u v 1) (T (halfPair u v 1)) -
      inner ℂ (halfPair u v (-1)) (T (halfPair u v (-1))) -
      Complex.I * inner ℂ (halfPair u v Complex.I) (T (halfPair u v Complex.I)) +
      Complex.I * inner ℂ (halfPair u v (-Complex.I)) (T (halfPair u v (-Complex.I))) := by
  simp only [halfPair, map_smul, map_add, inner_smul_left, inner_smul_right,
    inner_add_left, inner_add_right, inner_neg_left, inner_neg_right,
    map_inv₀, map_ofNat, map_neg, Complex.conj_I, one_smul, neg_smul]
  ring_nf
  simp [Complex.I_sq]
  ring

theorem complex_polarization_norm (T : E →L[ℂ] E) (u v : E) :
    ‖inner ℂ u (T v)‖ ≤
      ‖inner ℂ (halfPair u v 1) (T (halfPair u v 1))‖ +
      ‖inner ℂ (halfPair u v (-1)) (T (halfPair u v (-1)))‖ +
      ‖inner ℂ (halfPair u v Complex.I) (T (halfPair u v Complex.I))‖ +
      ‖inner ℂ (halfPair u v (-Complex.I)) (T (halfPair u v (-Complex.I)))‖ := by
  rw [complex_polarization_four]
  calc
    _ ≤ ‖inner ℂ (halfPair u v 1) (T (halfPair u v 1)) -
        inner ℂ (halfPair u v (-1)) (T (halfPair u v (-1))) -
        Complex.I * inner ℂ (halfPair u v Complex.I) (T (halfPair u v Complex.I))‖ +
        ‖Complex.I * inner ℂ (halfPair u v (-Complex.I)) (T (halfPair u v (-Complex.I)))‖ :=
      norm_add_le _ _
    _ ≤ (‖inner ℂ (halfPair u v 1) (T (halfPair u v 1)) -
        inner ℂ (halfPair u v (-1)) (T (halfPair u v (-1)))‖ +
        ‖Complex.I * inner ℂ (halfPair u v Complex.I) (T (halfPair u v Complex.I))‖) +
        ‖Complex.I * inner ℂ (halfPair u v (-Complex.I)) (T (halfPair u v (-Complex.I)))‖ :=
      add_le_add (norm_sub_le _ _) le_rfl
    _ ≤ _ := by
      simp only [norm_mul, Complex.norm_I, one_mul]
      linarith [norm_sub_le
        (inner ℂ (halfPair u v 1) (T (halfPair u v 1)))
        (inner ℂ (halfPair u v (-1)) (T (halfPair u v (-1))))]

end Hilbert


lemma halfPairFunction_norm_le {α : Type*} (f g : α → ℂ) (z : ℂ)
    (hf : ∀ x, ‖f x‖ ≤ 1) (hg : ∀ x, ‖g x‖ ≤ 1) (hz : ‖z‖ ≤ 1) (x : α) :
    ‖halfPairFunction f g z x‖ ≤ 1 := by
  have htwo : ‖(2 : ℂ)‖ = (2 : ℝ) := by norm_num
  rw [halfPairFunction, norm_div, htwo]
  apply (div_le_one (by norm_num : (0 : ℝ) < 2)).mpr
  calc
    ‖f x + z * g x‖ ≤ ‖f x‖ + ‖z * g x‖ := norm_add_le _ _
    _ ≤ 1 + 1 := add_le_add (hf x) (by rw [norm_mul]; exact
      (mul_le_mul hz (hg x) (norm_nonneg _) zero_le_one).trans_eq (by ring))
    _ = 2 := by norm_num

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.MixedDifference
namespace OAI

/-!
# Exact singleton centering

The product sampling law is kept fixed. Forcing a coordinate overwrites
that coordinate of the same sample, rather than drawing fresh coordinates
at different sites. This is the algebraic part of `q:mixed-difference`.
-/

namespace TwoPointCorrelations

open _root_.Finset

variable {ι A : Type*} [Fintype ι] [DecidableEq ι] [Fintype A] [DecidableEq A]


omit [Fintype ι] [Fintype A] [DecidableEq A] in
@[simp] lemma forceCoordinates_apply (S : Finset ι) (a x : ι → A) (i : ι) :
    forceCoordinates S a x i = if i ∈ S then a i else x i := rfl


namespace FiniteLaw











end FiniteLaw



end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.Nonbacktracking
namespace OAI

/-!
# Algebraic resolvent transfer for a nonbacktracking operator

This is the kernel argument in manuscript Lemma `q:noncommuting`. Each
edge operator has its own resolvent; distinct edge operators are never
commuted. The positivity and norm steps are separate from this algebraic
transfer.
-/

open scoped _root_.BigOperators

namespace TwoPointCorrelations

section

variable {ι E : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup E] [Module ℂ E]


/-- `R i` is the inverse of `1 + u B i`. These are the only inverse
identities needed to transfer injectivity. -/
theorem resolvent_transfer_injective (B : ι → E →ₗ[ℂ] E) (u : ℂ)
    (R : ι → E →ₗ[ℂ] E)
    (hR : ∀ i v, R i v + u • B i (R i v) = v)
    (hinj : Function.Injective (fun z : ι → E => z - u • nonbacktracking B z)) :
    Function.Injective (fun v : E => v - ∑ i, u • B i (R i v)) := by
  intro v w hvw
  let z : ι → E := fun i => R i (v - w)
  have hsum : ∑ i, u • B i (z i) = v - w := by
    have hs : (∑ i, u • B i (R i v)) - (∑ i, u • B i (R i w)) = v - w := by
      exact (sub_eq_sub_iff_sub_eq_sub.mp hvw).symm
    simpa only [z, map_sub, smul_sub, Finset.sum_sub_distrib] using hs
  have hkernel : z - u • nonbacktracking B z = 0 := by
    funext i
    have hsplit := Finset.sum_erase_add (Finset.univ : Finset ι)
      (fun j => u • B j (z j)) (Finset.mem_univ i)
    have hri := hR i (v - w)
    change z i - u • (∑ j ∈ Finset.univ.erase i, B j (z j)) = 0
    rw [Finset.smul_sum]
    change z i - (∑ j ∈ Finset.univ.erase i, u • B j (z j)) = 0
    change z i + u • B i (z i) = v - w at hri
    rw [hsum] at hsplit
    exact sub_eq_zero.mpr (add_right_cancel (hri.trans hsplit.symm))
  have hz : z = 0 := hinj (by simpa using hkernel)
  by_cases hι : Nonempty ι
  · obtain ⟨i⟩ := hι
    have hzi : R i (v - w) = 0 := by
      simpa [z] using congrFun hz i
    have hvwzero := hR i (v - w)
    rw [hzi, map_zero, smul_zero, add_zero] at hvwzero
    exact sub_eq_zero.mp hvwzero.symm
  · have : IsEmpty ι := not_nonempty_iff.mp hι
    simpa using hvw

end

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PaddedListCode
namespace OAI

/-! Fixed-length code slots for finite lists with a bounded length. -/

namespace TwoPointCorrelations

variable {α : Type*} {N : ℕ}


@[simp] theorem paddedListCode_ofFn (l : List α) (h : l.length ≤ N) (default : α) :
    List.ofFn (paddedListCode l h default) = l ++ List.replicate (N - l.length) default := by
  apply List.ext_getElem
  · simp only [List.length_ofFn, List.length_append, List.length_replicate]
    omega
  · intro i hi hj
    simp only [List.getElem_ofFn, paddedListCode]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.FiniteAverages
namespace OAI

/-! Elementary finite averaging identities used to assemble encoded marginals. -/

namespace TwoPointCorrelations

open _root_.Finset


@[simp] lemma uniformAverage_const {α : Type*} [Fintype α] [Nonempty α] (c : ℝ) :
    uniformAverage (fun _ : α => c) = c := by simp [uniformAverage]








end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.SelfAdjointPath
namespace OAI

/-!
# Positivity along an invertible self-adjoint path

The resolvent path in manuscript Lemma `q:noncommuting` starts at the
identity and is self-adjoint and invertible throughout a real interval.
Its positivity follows from continuity of the least Rayleigh quotient.
The argument is carried out in finite dimension.
-/

open _root_.Filter

namespace TwoPointCorrelations

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [Nontrivial E]


omit [Nontrivial E] in
lemma rayleigh_bddBelow (T : E →L[ℂ] E) :
    BddBelow (Set.range fun x : {x : E // x ≠ 0} => T.rayleighQuotient x) := by
  refine ⟨-‖T‖, ?_⟩
  rintro y ⟨x, rfl⟩
  exact (abs_le.mp (T.rayleighQuotient_le_norm x)).1

omit [Nontrivial E] in
lemma leastRayleigh_le (T : E →L[ℂ] E) (x : E) (hx : x ≠ 0) :
    leastRayleigh T ≤ T.rayleighQuotient x :=
  ciInf_le (rayleigh_bddBelow T) ⟨x, hx⟩

lemma leastRayleigh_le_add_norm (T S : E →L[ℂ] E) :
    leastRayleigh T ≤ leastRayleigh S + ‖T - S‖ := by
  let : Nonempty {x : E // x ≠ 0} := ⟨⟨Classical.choose (exists_ne (0 : E)),
    Classical.choose_spec (exists_ne (0 : E))⟩⟩
  have hpoint (x : {x : E // x ≠ 0}) :
      leastRayleigh T - ‖T - S‖ ≤ S.rayleighQuotient x := by
    have ht := leastRayleigh_le T x x.property
    have hb := (abs_le.mp ((T - S).rayleighQuotient_le_norm x)).2
    have heq : (T - S).rayleighQuotient x =
        T.rayleighQuotient x - S.rayleighQuotient x := by
      simp [sub_eq_add_neg, ContinuousLinearMap.rayleighQuotient_add]
    rw [heq] at hb
    linarith
  have hi : leastRayleigh T - ‖T - S‖ ≤ leastRayleigh S := le_ciInf hpoint
  linarith

lemma leastRayleigh_lipschitz : LipschitzWith 1 (leastRayleigh (E := E)) := by
  apply LipschitzWith.of_dist_le_mul
  intro T S
  have hTS := leastRayleigh_le_add_norm T S
  have hST := leastRayleigh_le_add_norm S T
  rw [norm_sub_rev S T] at hST
  simp only [NNReal.coe_one, one_mul, dist_eq_norm]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

@[simp] lemma leastRayleigh_id : leastRayleigh (ContinuousLinearMap.id ℂ E) = 1 := by
  let : Nonempty {x : E // x ≠ 0} := ⟨⟨Classical.choose (exists_ne (0 : E)),
    Classical.choose_spec (exists_ne (0 : E))⟩⟩
  have hpoint (x : {x : E // x ≠ 0}) :
      (ContinuousLinearMap.id ℂ E).rayleighQuotient x = 1 := by
    have hn : ‖(x : E)‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr x.property)
    simp only [ContinuousLinearMap.rayleighQuotient,
      ContinuousLinearMap.reApplyInnerSelf_apply, ContinuousLinearMap.id_apply,
      inner_self_eq_norm_sq_to_K]
    norm_cast
    exact div_self hn
  simp [leastRayleigh, hpoint]

lemma leastRayleigh_ne_zero [FiniteDimensional ℂ E] (T : E →L[ℂ] E)
    (hself : T.IsSymmetric) (hinj : Function.Injective T) : leastRayleigh T ≠ 0 := by
  intro hz
  have heig := hself.hasEigenvalue_iInf_of_finiteDimensional
  change Module.End.HasEigenvalue (T : E →ₗ[ℂ] E) (leastRayleigh T : ℂ) at heig
  rw [hz, Complex.ofReal_zero] at heig
  obtain ⟨x, hx, hxne⟩ := heig.exists_hasEigenvector
  rw [Module.End.mem_eigenspace_iff] at hx
  have hzero : T x = T 0 := by simpa using hx
  exact hxne (hinj hzero)

/-- A finite-dimensional continuous self-adjoint path that starts at the
identity and remains injective has strictly positive quadratic form. -/
theorem selfAdjoint_path_positive [FiniteDimensional ℂ E]
    (F : ℝ → E →L[ℂ] E) (a b : ℝ) (hab : a ≤ b)
    (hcont : ContinuousOn F (Set.Icc a b)) (hstart : F a = ContinuousLinearMap.id ℂ E)
    (hself : ∀ t ∈ Set.Icc a b, (F t).IsSymmetric)
    (hinj : ∀ t ∈ Set.Icc a b, Function.Injective (F t)) :
    ∀ x : E, x ≠ 0 → 0 < (inner ℂ (F b x) x).re := by
  have hc : ContinuousOn (fun t => leastRayleigh (F t)) (Set.Icc a b) :=
    leastRayleigh_lipschitz.continuous.comp_continuousOn hcont
  have hstart' : leastRayleigh (F a) = 1 := by rw [hstart, leastRayleigh_id]
  have hend : 0 < leastRayleigh (F b) := by
    by_contra! hn
    obtain ⟨t, ht, heq⟩ := intermediate_value_Icc' hab hc
      (show (0 : ℝ) ∈ Set.Icc (leastRayleigh (F b)) (leastRayleigh (F a)) by
        exact ⟨hn, by rw [hstart']; norm_num⟩)
    exact leastRayleigh_ne_zero (F t) (hself t ht) (hinj t ht) heq
  intro x hx
  have hr : 0 < (F b).rayleighQuotient x := hend.trans_le (leastRayleigh_le (F b) x hx)
  have hn : 0 < ‖x‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hx)
  exact (div_pos_iff_of_pos_right hn).mp hr

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ResolventTransfer
namespace OAI

/-!
# The resolvent path for noncommuting edge operators

The definitions and lemmas here implement the path used in manuscript
Lemma `q:noncommuting`. The only products that are commuted are an edge
operator and its own resolvent.
-/

open scoped _root_.BigOperators _root_.NNReal _root_.ENNReal

namespace TwoPointCorrelations

variable {ι E : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]




lemma isUnit_edge_shift (B : E →L[ℂ] E) (u : ℝ) (h : ‖u • B‖ < 1) :
    IsUnit (1 + u • B) := by
  simpa only [norm_neg, sub_neg_eq_add] using
    (isUnit_one_sub_of_norm_lt_one (x := -(u • B)) (by simpa using h))

omit [FiniteDimensional ℂ E] in
lemma edgeResolvent_mul (B : E →L[ℂ] E) (u : ℝ) (h : IsUnit (1 + u • B)) :
    (1 + u • B) * edgeResolvent B u = 1 :=
  Ring.mul_inverse_cancel _ h

omit [FiniteDimensional ℂ E] in
lemma edgeResolvent_commute (B : E →L[ℂ] E) (u : ℝ) (h : IsUnit (1 + u • B)) :
    B * edgeResolvent B u = edgeResolvent B u * B := by
  let A := 1 + u • B
  let R := edgeResolvent B u
  have hAR : A * R = 1 := Ring.mul_inverse_cancel _ h
  have hRA : R * A = 1 := Ring.inverse_mul_cancel _ h
  have hAB : A * B = B * A := by
    simp [A, add_mul, mul_add]
  calc
    B * R = (R * A) * (B * R) := by rw [hRA, one_mul]
    _ = R * (A * B) * R := by simp only [mul_assoc]
    _ = R * (B * A) * R := by rw [hAB]
    _ = (R * B) * (A * R) := by simp only [mul_assoc]
    _ = R * B := by rw [hAR, mul_one]

omit [DecidableEq ι] in
lemma transferResolvent_selfAdjoint (B : ι → E →L[ℂ] E)
    (hB : ∀ i, IsSelfAdjoint (B i)) (u : ℝ)
    (hunit : ∀ i, IsUnit (1 + u • B i)) : IsSelfAdjoint (transferResolvent B u) := by
  unfold transferResolvent
  apply IsSelfAdjoint.sub (by simp)
  apply isSelfAdjoint_sum
  intro i _
  apply (isSelfAdjoint_iff.mpr (by rfl) : IsSelfAdjoint u).smul
  have hR : IsSelfAdjoint (edgeResolvent (B i) u) :=
    ((IsSelfAdjoint.one (E →L[ℂ] E)).add ((isSelfAdjoint_iff.mpr (by rfl) : IsSelfAdjoint u).smul
      (hB i))).ringInverse
  change star (B i * edgeResolvent (B i) u) = B i * edgeResolvent (B i) u
  rw [star_mul, hR.star_eq, (hB i).star_eq]
  exact (edgeResolvent_commute (B i) u (hunit i)).symm

lemma clm_injective_of_isUnit {V : Type*} [AddCommGroup V] [Module ℂ V] [TopologicalSpace V]
    (T : V →L[ℂ] V) (h : IsUnit T) : Function.Injective T := by
  obtain ⟨v, rfl⟩ := h
  exact (ContinuousLinearEquiv.ofUnit v).injective

theorem transferResolvent_injective (B : ι → E →L[ℂ] E) (u : ℝ)
    (hunit : ∀ i, IsUnit (1 + u • B i))
    (hH : IsUnit (1 - (u : ℂ) • nonbacktrackingContinuous B)) :
    Function.Injective (transferResolvent B u) := by
  have hR (i : ι) (v : E) : edgeResolvent (B i) u v +
      (u : ℂ) • B i (edgeResolvent (B i) u v) = v := by
    have h := congrArg (fun T : E →L[ℂ] E => T v) (edgeResolvent_mul (B i) u (hunit i))
    simpa using h
  have h := resolvent_transfer_injective (fun i => (B i).toLinearMap) (u : ℂ)
    (fun i => (edgeResolvent (B i) u).toLinearMap) hR
    (clm_injective_of_isUnit (1 - (u : ℂ) • nonbacktrackingContinuous B) hH)
  intro v w hvw
  apply h
  change v - ∑ i, u • B i (edgeResolvent (B i) u v) =
    w - ∑ i, u • B i (edgeResolvent (B i) u w)
  simpa only [transferResolvent, sub_apply, one_apply_eq_self, sum_apply,
    smul_apply, mul_apply_eq_comp] using hvw

omit [DecidableEq ι] in
theorem transferResolvent_continuousOn (B : ι → E →L[ℂ] E) (a b : ℝ)
    (hunit : ∀ u ∈ Set.Icc a b, ∀ i, IsUnit (1 + u • B i)) :
    ContinuousOn (transferResolvent B) (Set.Icc a b) := by
  apply continuousOn_const.sub
  apply continuousOn_finsetSum
  intro i _
  apply continuousOn_id.smul
  apply continuousOn_const.mul
  intro u hu
  obtain ⟨v, hv⟩ := hunit u hu i
  have hi := NormedRing.inverse_continuousAt v
  rw [hv] at hi
  have hc : ContinuousWithinAt (fun s : ℝ => (1 : E →L[ℂ] E) + s • B i)
      (Set.Icc a b) u := by fun_prop
  change ContinuousWithinAt (fun s : ℝ => Ring.inverse ((1 : E →L[ℂ] E) + s • B i))
    (Set.Icc a b) u
  exact ContinuousAt.comp_continuousWithinAt (g := Ring.inverse) hi hc


lemma edgeResolvent_norm_le_two [Nontrivial E] (B : E →L[ℂ] E) (u : ℝ)
    (hnorm : ‖u • B‖ ≤ 1 / 2) : ‖edgeResolvent B u‖ ≤ 2 := by
  let x : E →L[ℂ] E := -(u • B)
  have hx : ‖x‖ < 1 := by simpa [x] using hnorm.trans_lt (by norm_num : (1 / 2 : ℝ) < 1)
  have hbound := tsum_geometric_le_of_norm_lt_one x hx
  have hinv : (1 - ‖x‖)⁻¹ ≤ 2 := by
    apply (inv_le_iff_one_le_mul₀ (by linarith : 0 < 1 - ‖x‖)).mpr
    have : ‖x‖ ≤ 1 / 2 := by simpa [x] using hnorm
    linarith
  have heq : edgeResolvent B u = ↑(Units.oneSub x hx)⁻¹ := by
    simpa [edgeResolvent, x] using NormedRing.inverse_one_sub x hx
  rw [heq]
  change ‖∑' n : ℕ, x ^ n‖ ≤ 2
  simpa only [norm_one, sub_self, zero_add] using hbound.trans
    (show ‖(1 : E →L[ℂ] E)‖ - 1 + (1 - ‖x‖)⁻¹ ≤ 2 by simpa using hinv)

lemma nonbacktracking_resolvent_isUnit (B : ι → E →L[ℂ] E) (m : ℝ≥0)
    (hm : 0 < m) (hrad : spectralRadius ℂ (nonbacktrackingContinuous B) ≤ (m : ℝ≥0∞))
    (u : ℝ) (hu : |u| < (m : ℝ)⁻¹) :
    IsUnit (1 - (u : ℂ) • nonbacktrackingContinuous B) := by
  apply spectrum.isUnit_one_sub_smul_of_lt_inv_radius (𝕜 := ℂ)
    (a := nonbacktrackingContinuous B) (z := (u : ℂ))
  apply lt_of_lt_of_le _ (ENNReal.inv_le_inv.mpr hrad)
  have hnn : ‖(u : ℂ)‖₊ < m⁻¹ := by
    exact_mod_cast (by simpa using hu : ‖(u : ℂ)‖ < ((m⁻¹ : ℝ≥0) : ℝ))
  rw [← ENNReal.coe_inv hm.ne']
  exact_mod_cast hnn

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ResolventBounds
namespace OAI

/-!
# Quadratic-form bounds for the noncommuting resolvent

The correction is estimated using the norm of each individual resolvent.
This avoids imposing any commutation relation between distinct edges.
-/

open scoped _root_.BigOperators

namespace TwoPointCorrelations

variable {ι E : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

theorem transferResolvent_positive_abs [Nontrivial E] (B : ι → E →L[ℂ] E)
    (hB : ∀ i, IsSelfAdjoint (B i)) (t : ℝ)
    (hsmall : ∀ u : ℝ, |u| ≤ |t| → ∀ i, ‖u • B i‖ < 1)
    (hH : ∀ u : ℝ, |u| ≤ |t| →
      IsUnit (1 - (u : ℂ) • nonbacktrackingContinuous B)) :
    ∀ v : E, v ≠ 0 → 0 < (inner ℂ (transferResolvent B t v) v).re := by
  have hu (u : ℝ) (h : |u| ≤ |t|) (i : ι) : IsUnit (1 + u • B i) :=
    isUnit_edge_shift _ _ (hsmall u h i)
  have hmul (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) : |s * t| ≤ |t| := by
    rw [abs_mul, abs_of_nonneg hs.1]
    exact mul_le_of_le_one_left (abs_nonneg t) hs.2
  have hc := transferResolvent_continuousOn B (-|t|) |t|
    (fun u hu' i => hu u (abs_le.mpr hu') i)
  have hpath : ContinuousOn (fun s : ℝ => transferResolvent B (s * t))
      (Set.Icc 0 1) := hc.comp (by fun_prop) (fun s hs => abs_le.mp (hmul s hs))
  have h := selfAdjoint_path_positive (fun s : ℝ => transferResolvent B (s * t)) 0 1
    zero_le_one hpath (by ext v; simp [transferResolvent])
    (fun s hs => (transferResolvent_selfAdjoint B hB (s * t)
      (hu (s * t) (hmul s hs))).isSymmetric)
    (fun s hs => transferResolvent_injective B (s * t)
      (hu (s * t) (hmul s hs)) (hH (s * t) (hmul s hs)))
  simpa only [one_mul] using h

omit [DecidableEq ι] [FiniteDimensional ℂ E] in
theorem transferResolvent_apply_expansion (B : ι → E →L[ℂ] E) (u : ℝ)
    (hunit : ∀ i, IsUnit (1 + u • B i)) (v : E) :
    transferResolvent B u v = v - u • (∑ i, B i v) +
      u ^ 2 • (∑ i, B i (B i (edgeResolvent (B i) u v))) := by
  have hi (i : ι) : u • B i (edgeResolvent (B i) u v) =
      u • B i v - u ^ 2 • B i (B i (edgeResolvent (B i) u v)) := by
    have hR := congrArg (fun T : E →L[ℂ] E => T v) (edgeResolvent_mul (B i) u (hunit i))
    have h := congrArg (fun z : E => u • B i z) hR
    simp only [add_apply, one_apply_eq_self, smul_apply, mul_apply_eq_comp,
      map_add, ContinuousLinearMap.map_smul_of_tower, smul_add, smul_smul, ← pow_two] at h
    exact eq_sub_of_add_eq h
  simp only [transferResolvent, sub_apply, one_apply_eq_self, sum_apply,
    smul_apply, mul_apply_eq_comp]
  simp_rw [hi]
  rw [Finset.sum_sub_distrib, ← Finset.smul_sum, ← Finset.smul_sum]
  abel

omit [DecidableEq ι] in
theorem resolventCorrection_bound [Nontrivial E] (B : ι → E →L[ℂ] E)
    (hB : ∀ i, IsSelfAdjoint (B i)) (u : ℝ)
    (hsmall : ∀ i, ‖u • B i‖ ≤ 1 / 2) (v : E) :
    |(inner ℂ (∑ i, B i (B i (edgeResolvent (B i) u v))) v).re| ≤
      2 * ∑ i, ‖B i v‖ ^ 2 := by
  have hi (i : ι) : |(inner ℂ (B i (B i (edgeResolvent (B i) u v))) v).re| ≤
      2 * ‖B i v‖ ^ 2 := by
    have hu := isUnit_edge_shift (B i) u ((hsmall i).trans_lt (by norm_num))
    have hc := congrArg (fun T : E →L[ℂ] E => T v) (edgeResolvent_commute (B i) u hu)
    have heq : inner ℂ (B i (B i (edgeResolvent (B i) u v))) v =
        inner ℂ (edgeResolvent (B i) u (B i v)) (B i v) := by
      calc
        _ = inner ℂ (B i (edgeResolvent (B i) u v)) (B i v) := (hB i).isSymmetric _ _
        _ = _ := by
          simpa only [mul_apply_eq_comp] using congrArg (fun w => inner ℂ w (B i v)) hc
    rw [heq]
    calc
      |(inner ℂ (edgeResolvent (B i) u (B i v)) (B i v)).re| ≤
          ‖inner ℂ (edgeResolvent (B i) u (B i v)) (B i v)‖ := Complex.abs_re_le_norm _
      _ ≤ ‖edgeResolvent (B i) u (B i v)‖ * ‖B i v‖ := norm_inner_le_norm _ _
      _ ≤ (2 * ‖B i v‖) * ‖B i v‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        exact (ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_mul_of_nonneg_right (edgeResolvent_norm_le_two (B i) u (hsmall i))
            (norm_nonneg _))
      _ = 2 * ‖B i v‖ ^ 2 := by ring
  simp only [sum_inner, Complex.re_sum]
  calc
    |∑ i, (inner ℂ (B i (B i (edgeResolvent (B i) u v))) v).re| ≤
        ∑ i, |(inner ℂ (B i (B i (edgeResolvent (B i) u v))) v).re| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, 2 * ‖B i v‖ ^ 2 := Finset.sum_le_sum (fun i _ => hi i)
    _ = _ := (Finset.mul_sum ..).symm

omit [DecidableEq ι] [FiniteDimensional ℂ E] in
theorem transferResolvent_inner_expansion (B : ι → E →L[ℂ] E) (u : ℝ)
    (hunit : ∀ i, IsUnit (1 + u • B i)) (v : E) :
    (inner ℂ (transferResolvent B u v) v).re = ‖v‖ ^ 2 -
      u * (inner ℂ (∑ i, B i v) v).re +
      u ^ 2 * (inner ℂ (∑ i, B i (B i (edgeResolvent (B i) u v))) v).re := by
  rw [transferResolvent_apply_expansion B u hunit v]
  simp only [inner_add_left, inner_sub_left, inner_smul_left_eq_star_smul,
    Complex.add_re, Complex.sub_re, inner_self_eq_norm_sq_to_K]
  simp [← Complex.ofReal_pow, sum_inner, Complex.re_sum]

omit [DecidableEq ι] in
/-- Positivity of the resolvent at both endpoints controls the quadratic
form of the edge sum on each vector satisfying the square-function bound. -/
theorem edge_sum_quadratic_bound [Nontrivial E] (B : ι → E →L[ℂ] E)
    (hB : ∀ i, IsSelfAdjoint (B i)) (t b : ℝ) (ht : 0 < t)
    (hsmall : ∀ i, ‖t • B i‖ ≤ 1 / 2)
    (hplus : ∀ v : E, 0 ≤ (inner ℂ (transferResolvent B t v) v).re)
    (hminus : ∀ v : E, 0 ≤ (inner ℂ (transferResolvent B (-t) v) v).re)
    (v : E) (hsq : ∑ i, ‖B i v‖ ^ 2 ≤ b ^ 2 * ‖v‖ ^ 2) :
    |(inner ℂ (∑ i, B i v) v).re| ≤ ((1 + 2 * t ^ 2 * b ^ 2) / t) * ‖v‖ ^ 2 := by
  have hsmallNeg (i : ι) : ‖(-t) • B i‖ ≤ 1 / 2 := by simpa using hsmall i
  have hup := (resolventCorrection_bound B hB t hsmall v).trans (mul_le_mul_of_nonneg_left hsq (by norm_num))
  have hum := (resolventCorrection_bound B hB (-t) hsmallNeg v).trans (mul_le_mul_of_nonneg_left hsq (by norm_num))
  have hp := hplus v
  have hm := hminus v
  rw [transferResolvent_inner_expansion B t
    (fun i => isUnit_edge_shift _ _ ((hsmall i).trans_lt (by norm_num)))] at hp
  rw [transferResolvent_inner_expansion B (-t)
    (fun i => isUnit_edge_shift _ _ ((hsmallNeg i).trans_lt (by norm_num)))] at hm
  rw [abs_le] at hup hum ⊢
  have hup' := mul_le_mul_of_nonneg_left hup.2 (sq_nonneg t)
  have hum' := mul_le_mul_of_nonneg_left hum.2 (sq_nonneg t)
  rw [div_mul_eq_mul_div]
  constructor
  · rw [← neg_div]
    apply (div_le_iff₀ ht).mpr
    nlinarith only [hm, hum']
  · apply (le_div_iff₀ ht).mpr
    nlinarith only [hp, hup']

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.BernoulliTail
namespace OAI

/-! Exact exponential moments and elementary upper tails for the finite
independent Boolean laws used by the two prime-degree deletions. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical



lemma booleanCount_eq_card {ι : Type*} [Fintype ι] (a : ι → Bool) :
    booleanCount a = ((univ.filter (fun i => a i = true)).card : ℝ) := by
  exact sum_boole (fun i => a i = true) univ





end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.SpectralTransfer
namespace OAI

/-!
# Noncommuting spectral transfer

The manuscript's Lemma `q:noncommuting`, in a form with any common upper
bound on the single-edge norms, the square function, and the spectral
radius. No commutation between distinct edges is assumed.
-/

open scoped _root_.BigOperators _root_.NNReal _root_.ENNReal

namespace TwoPointCorrelations

variable {ι E : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

lemma projection_norm_apply_le (P : E →L[ℂ] E) (hP : IsSelfAdjoint P)
    (hPP : P * P = P) (v : E) : ‖P v‖ ≤ ‖v‖ := by
  have heq : inner ℂ (P v) (P v) = inner ℂ (P v) v := by
    have h := congrArg (fun T : E →L[ℂ] E => T v) hPP
    calc
      _ = inner ℂ (P (P v)) v := (hP.isSymmetric _ _).symm
      _ = _ := by
        simpa only [mul_apply_eq_comp] using congrArg (fun w => inner ℂ w v) h
  have hi := Complex.abs_re_le_norm (inner ℂ (P v) v)
  have hj := norm_inner_le_norm (𝕜 := ℂ) (P v) v
  have heq' : (inner ℂ (P v) v).re = ‖P v‖ ^ 2 := by
    rw [← heq, inner_self_eq_norm_sq_to_K]
    simp [← Complex.ofReal_pow]
  rw [heq', abs_of_nonneg (sq_nonneg _)] at hi
  by_cases hzero : ‖P v‖ = 0
  · simp [hzero]
  · have hp : 0 < ‖P v‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hzero)
    nlinarith [hi.trans hj]

lemma compression_norm_le_of_quadratic (S P : E →L[ℂ] E)
    (hS : IsSelfAdjoint S) (hP : IsSelfAdjoint P) (hPP : P * P = P)
    (c : ℝ) (hc : 0 ≤ c)
    (hform : ∀ v : E, P v = v → |(inner ℂ (S v) v).re| ≤ c * ‖v‖ ^ 2) :
    ‖P * S * P‖ ≤ c := by
  have hself : IsSelfAdjoint (P * S * P) := by
    change star (P * S * P) = P * S * P
    simp only [star_mul, hP.star_eq, hS.star_eq, mul_assoc]
  rw [ContinuousLinearMap.norm_eq_iSup_rayleighQuotient _ hself.isSymmetric]
  apply ciSup_le
  intro v
  have hPv : P (P v) = P v := by
    simpa only [mul_apply_eq_comp] using
      congrArg (fun T : E →L[ℂ] E => T v) hPP
  have hbound := hform (P v) hPv
  have hnorm := projection_norm_apply_le P hP hPP v
  have heq : inner ℂ ((P * S * P) v) v = inner ℂ (S (P v)) (P v) := by
    simp only [mul_apply_eq_comp]
    exact hP.isSymmetric _ _
  by_cases hv : v = 0
  · simpa [hv] using hc
  · have hvp : 0 < ‖v‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hv)
    simp only [ContinuousLinearMap.rayleighQuotient,
      ContinuousLinearMap.reApplyInnerSelf_apply, heq, abs_div, abs_sq]
    apply (div_le_iff₀ hvp).mpr
    exact hbound.trans (mul_le_mul_of_nonneg_left
      (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _) |>.mpr hnorm) hc)

/-- A common-bound version of the noncommuting transfer lemma. -/
theorem noncommuting_spectral_transfer
    (B : ι → E →L[ℂ] E) (hB : ∀ i, IsSelfAdjoint (B i))
    (P : E →L[ℂ] E) (hP : IsSelfAdjoint P) (hPP : P * P = P)
    (m : ℝ≥0) (hnorm : ∀ i, ‖B i‖ ≤ (m : ℝ))
    (hsq : ∀ v : E, P v = v → ∑ i, ‖B i v‖ ^ 2 ≤ (m : ℝ) ^ 2 * ‖v‖ ^ 2)
    (hrad : spectralRadius ℂ (nonbacktrackingContinuous B) ≤ (m : ℝ≥0∞)) :
    ‖P * (∑ i, B i) * P‖ ≤ 3 * (m : ℝ) := by
  nontriviality E
  by_cases hm : m = 0
  · have hzero (i : ι) : B i = 0 := norm_eq_zero.mp (le_antisymm (by simpa [hm] using hnorm i) (norm_nonneg _))
    simp [hzero, hm]
  have hmpos : 0 < m := pos_iff_ne_zero.mpr hm
  have hmr : 0 < (m : ℝ) := by exact_mod_cast hmpos
  let t : ℝ := (2 * (m : ℝ))⁻¹
  have ht : 0 < t := by positivity
  have htm : t * (m : ℝ) = 1 / 2 := by dsimp [t]; field_simp
  have htinv : t < (m : ℝ)⁻¹ := by
    dsimp [t]
    exact (inv_lt_inv₀ (by positivity) hmr).mpr (by linarith)
  have hsmall (u : ℝ) (hu : |u| ≤ t) (i : ι) : ‖u • B i‖ ≤ 1 / 2 := by
    rw [norm_smul, Real.norm_eq_abs]
    calc
      |u| * ‖B i‖ ≤ t * (m : ℝ) := mul_le_mul hu (hnorm i) (norm_nonneg _) ht.le
      _ = _ := htm
  have hform (v : E) (hv : P v = v) :
      |(inner ℂ (∑ i, B i v) v).re| ≤ 3 * (m : ℝ) * ‖v‖ ^ 2 := by
    have hpositive (u : ℝ) (hu : |u| = t) (w : E) :
        0 ≤ (inner ℂ (transferResolvent B u w) w).re := by
      by_cases hw : w = 0
      · simp [hw]
      · apply (transferResolvent_positive_abs B hB u
          (fun s hs i => (hsmall s (hs.trans_eq hu) i).trans_lt (by norm_num))
          (fun s hs => nonbacktracking_resolvent_isUnit B m hmpos hrad s
            ((hs.trans_eq hu).trans_lt htinv)) w hw).le
    have h := edge_sum_quadratic_bound B hB t m ht (hsmall t (by rw [abs_of_pos ht]))
      (hpositive t (abs_of_pos ht))
      (hpositive (-t) (by simp [abs_of_pos ht])) v (hsq v hv)
    have hc : (1 + 2 * t ^ 2 * (m : ℝ) ^ 2) / t = 3 * (m : ℝ) := by
      dsimp [t]
      field_simp
      ring
    simpa only [hc] using h
  apply compression_norm_le_of_quadratic (∑ i, B i) P
    (isSelfAdjoint_sum _ (fun i _ => hB i)) hP hPP (3 * (m : ℝ)) (by positivity)
  intro v hv
  simpa only [sum_apply] using hform v hv


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.CoordinateProjection
namespace OAI

/-! The orthogonal projection deleting the high-degree vertices. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

variable {V : Type*} [Fintype V] [DecidableEq V]


lemma coordinateProjection_apply (keep : V → Prop) (v : EuclideanSpace ℂ V) (i : V) :
    coordinateProjection keep v i = if keep i then v i else 0 := by
  change (∑ j, Matrix.diagonal (fun i => if keep i then (1 : ℂ) else 0) i j * v j) = _
  simp [Matrix.diagonal_apply]

lemma coordinateProjection_selfAdjoint (keep : V → Prop) :
    IsSelfAdjoint (coordinateProjection keep) := by
  apply matrixOperator_selfAdjoint
  intro i j
  by_cases hij : i = j
  · subst j
    by_cases hi : keep i <;> simp [hi]
  · simp [hij, Ne.symm hij]

lemma coordinateProjection_idempotent (keep : V → Prop) :
    coordinateProjection keep * coordinateProjection keep = coordinateProjection keep := by
  ext v i
  change coordinateProjection keep (coordinateProjection keep v) i = coordinateProjection keep v i
  simp only [coordinateProjection_apply]
  split_ifs <;> rfl

lemma coordinateProjection_support (keep : V → Prop) (v : EuclideanSpace ℂ V)
    (hv : coordinateProjection keep v = v) (i : V) (hi : v i ≠ 0) : keep i := by
  by_contra hkeep
  have he := congrArg (fun w : EuclideanSpace ℂ V => w i) hv
  rw [coordinateProjection_apply, if_neg hkeep] at he
  exact hi he.symm


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.TriangularElimination
namespace OAI

/-! Successive elimination for finite product laws and triangular events. -/

namespace TwoPointCorrelations

open _root_.Finset

variable {ι A : Type*} [Fintype ι] [DecidableEq ι] [Fintype A]


omit [Fintype ι] [Fintype A] in
@[simp] lemma restoreCoordinate_same (i : ι) (a : A) (y : {j : ι // j ≠ i} → A) :
    restoreCoordinate i a y i = a := by simp [restoreCoordinate]

omit [Fintype ι] [Fintype A] in
@[simp] lemma restoreCoordinate_other (i : ι) (a : A) (y : {j : ι // j ≠ i} → A)
    (j : {j : ι // j ≠ i}) : restoreCoordinate i a y j = y j := by
  simp [restoreCoordinate, j.property]


namespace FiniteLaw





end FiniteLaw

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.UniformResidues
namespace OAI

/-! Uniform residue coordinates realized on one common finite carrier. -/

namespace TwoPointCorrelations

open _root_.Finset


@[simp] lemma uniformResidueLaw_weight (B p : ℕ) (hp : 0 < p) (hpB : p ≤ B)
    (x : Fin B) (hx : x.val < p) :
    (uniformResidueLaw B p hp hpB).weight x = (p : ℝ)⁻¹ := by
  simp [uniformResidueLaw, hx]


@[simp] lemma uniformResidueLaw_castLE (B p : ℕ) (hp : 0 < p) (hpB : p ≤ B)
    (x : Fin p) :
    (uniformResidueLaw B p hp hpB).weight (Fin.castLE hpB x) = (p : ℝ)⁻¹ := by
  exact uniformResidueLaw_weight B p hp hpB _ x.isLt


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.WeightedMatrixTest
namespace OAI

/-! Deterministic testing of a weighted matrix. Only rows on the support
of the test vector enter the estimate. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma weighted_matrix_test_le {V : Type*} [Fintype V] [DecidableEq V]
    (A : V → V → ℂ) (g R : V → ℝ) (hg : ∀ i, 0 < g i)
    (v : EuclideanSpace ℂ V) (hv : ∀ i, ‖v i‖ ≤ g i)
    (hrow : ∀ i, v i ≠ 0 → ∑ j, ‖A i j‖ * g j / g i ≤ R i) :
    ‖inner ℂ v (matrixOperator A v)‖ ≤
      ∑ i, if v i = 0 then 0 else R i * (g i) ^ 2 := by
  rw [PiLp.inner_apply]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro i _
  by_cases hi : v i = 0
  · simp [hi]
  · rw [if_neg hi]
    calc
      ‖inner ℂ (v i) (matrixOperator A v i)‖ ≤ ‖v i‖ * ‖matrixOperator A v i‖ :=
        norm_inner_le_norm _ _
      _ ≤ g i * (∑ j, ‖A i j‖ * g j) := by
        apply mul_le_mul (hv i) _ (norm_nonneg _) (hg i).le
        rw [matrixOperator_apply]
        apply (norm_sum_le _ _).trans
        exact sum_le_sum (fun j _ => by
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (hv j) (norm_nonneg _))
      _ = (∑ j, ‖A i j‖ * g j / g i) * (g i) ^ 2 := by
        rw [← sum_div]
        field_simp [(hg i).ne']
      _ ≤ _ := mul_le_mul_of_nonneg_right (hrow i hi) (sq_nonneg _)

lemma weighted_matrix_test_uniform {V : Type*} [Fintype V] [DecidableEq V]
    (A : V → V → ℂ) (g : V → ℝ) (R G : ℝ)
    (hg : ∀ i, 0 < g i) (hR : 0 ≤ R) (hGnonneg : 0 ≤ G)
    (v : EuclideanSpace ℂ V) (hv : ∀ i, ‖v i‖ ≤ g i)
    (hrow : ∀ i, v i ≠ 0 → ∑ j, ‖A i j‖ * g j / g i ≤ R)
    (hG : ∀ i, v i ≠ 0 → (g i) ^ 2 ≤ G) :
    ‖inner ℂ v (matrixOperator A v)‖ ≤ Fintype.card V * R * G := by
  apply (weighted_matrix_test_le A g (fun _ => R) hg v hv hrow).trans
  calc
    (∑ i, if v i = 0 then 0 else R * (g i) ^ 2) ≤ ∑ _i : V, R * G := by
      apply sum_le_sum
      intro i _
      by_cases hi : v i = 0
      · rw [if_pos hi]
        exact mul_nonneg hR hGnonneg
      · rw [if_neg hi]
        exact mul_le_mul_of_nonneg_left (hG i hi) hR
    _ = _ := by simp; ring

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.WeightedRows
namespace OAI

/-!
# Weighted rows and the localized square estimate

Finite weighted Cauchy--Schwarz proves the localized Schur estimate in
`q:weighted-rows`. Constancy of the site factor on the support replaces a
level-set decomposition. Summing the localized estimates only uses a bound
at the support of the vector; no commutation with a projection is needed.
-/

namespace TwoPointCorrelations

open _root_.Finset

variable {ι δ : Type*} [Fintype ι] [Fintype δ]

lemma weighted_row_square (B : ι → ι → ℝ) (g a : ι → ℝ) (c : ℝ)
    (hB : ∀ i j, 0 ≤ B i j) (hg : ∀ i, 0 < g i)
    (hrow : ∀ i, ∑ j, B i j * g j / g i ≤ c * a i)
    (v : ι → ℝ) (i : ι) :
    (∑ j, B i j * v j) ^ 2 ≤
      (c * a i) * ∑ j, B i j * g i / g j * (v j) ^ 2 := by
  have hcs := sum_sq_le_sum_mul_sum_of_sq_le_mul univ
    (f := fun j => B i j * g j / g i)
    (g := fun j => B i j * g i / g j * (v j) ^ 2)
    (r := fun j => B i j * v j)
    (fun j _ => div_nonneg (mul_nonneg (hB i j) (hg j).le) (hg i).le)
    (fun j _ => mul_nonneg (div_nonneg (mul_nonneg (hB i j) (hg i).le) (hg j).le) (sq_nonneg _))
    (fun j _ => le_of_eq (by field_simp [(hg i).ne', (hg j).ne']))
  exact hcs.trans (mul_le_mul_of_nonneg_right (hrow i)
    (sum_nonneg (fun j _ => mul_nonneg
      (div_nonneg (mul_nonneg (hB i j) (hg i).le) (hg j).le) (sq_nonneg _))))

lemma weighted_column_bound (B : ι → ι → ℝ) (g a : ι → ℝ) (c : ℝ)
    (ha : ∀ i, 0 ≤ a i)
    (hsymm : ∀ i j, B i j = B j i)
    (hlevel : ∀ i j, B i j ≠ 0 → a i = a j)
    (hrow : ∀ i, ∑ j, B i j * g j / g i ≤ c * a i) (j : ι) :
    ∑ i, a i * B i j * g i / g j ≤ c * (a j) ^ 2 := by
  have heq : (∑ i, a i * B i j * g i / g j) =
      a j * ∑ i, B j i * g i / g j := by
    rw [mul_sum]
    apply sum_congr rfl
    intro i _
    by_cases hij : B i j = 0
    · simp [hij, ← hsymm i j]
    · rw [hlevel i j hij, hsymm i j]
      ring
  rw [heq]
  calc
    _ ≤ a j * (c * a j) := mul_le_mul_of_nonneg_left (hrow j) (ha j)
    _ = _ := by ring

/-- The finite localized square bound. The input kernel is nonnegative,
so it can in particular be the entrywise norm of a Hermitian matrix. -/
theorem weighted_kernel_localized_square (B : ι → ι → ℝ)
    (g a : ι → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hB : ∀ i j, 0 ≤ B i j) (hg : ∀ i, 0 < g i) (ha : ∀ i, 0 ≤ a i)
    (hsymm : ∀ i j, B i j = B j i)
    (hlevel : ∀ i j, B i j ≠ 0 → a i = a j)
    (hrow : ∀ i, ∑ j, B i j * g j / g i ≤ c * a i)
    (v : ι → ℝ) :
    ∑ i, (∑ j, B i j * v j) ^ 2 ≤ c ^ 2 * ∑ i, (a i) ^ 2 * (v i) ^ 2 := by
  calc
    _ ≤ ∑ i, (c * a i) * ∑ j, B i j * g i / g j * (v j) ^ 2 :=
      sum_le_sum (fun i _ => weighted_row_square B g a c hB hg hrow v i)
    _ = c * ∑ j, (∑ i, a i * B i j * g i / g j) * (v j) ^ 2 := by
      simp only [mul_sum, sum_mul]
      rw [sum_comm]
      apply sum_congr rfl
      intro j _
      apply sum_congr rfl
      intro i _
      ring
    _ ≤ c * ∑ j, (c * (a j) ^ 2) * (v j) ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ hc
      apply sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_right
        (weighted_column_bound B g a c ha hsymm hlevel hrow j) (sq_nonneg _)
    _ = _ := by
      simp only [mul_sum]
      apply sum_congr rfl
      intro j _
      ring

/-- The manuscript's localized square bound for a complex matrix. -/
theorem weighted_matrix_localized_square (A : ι → ι → ℂ)
    (g a : ι → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hg : ∀ i, 0 < g i) (ha : ∀ i, 0 ≤ a i)
    (hsymm : ∀ i j, ‖A i j‖ = ‖A j i‖)
    (hlevel : ∀ i j, A i j ≠ 0 → a i = a j)
    (hrow : ∀ i, ∑ j, ‖A i j‖ * g j / g i ≤ c * a i)
    (v : ι → ℂ) :
    ∑ i, ‖∑ j, A i j * v j‖ ^ 2 ≤ c ^ 2 * ∑ i, (a i) ^ 2 * ‖v i‖ ^ 2 := by
  apply le_trans _ (weighted_kernel_localized_square (fun i j => ‖A i j‖) g a c hc
    (fun i j => norm_nonneg _) hg ha hsymm
    (fun i j hij => hlevel i j (fun hz => hij (by simp [hz]))) hrow (fun i => ‖v i‖))
  apply sum_le_sum
  intro i _
  apply (sq_le_sq₀ (norm_nonneg _)
    (sum_nonneg (fun j _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)))).mpr
  simpa only [norm_mul] using norm_sum_le univ (fun j => A i j * v j)

/-- Summing localized bounds only requires degree control where the
vector is nonzero. This is the support condition supplied by `v = E v`. -/
theorem localized_square_sum (A : δ → ι → ι → ℂ) (a : δ → ι → ℝ)
    (c M : ℝ) (v : ι → ℂ)
    (hlocal : ∀ d, ∑ i, ‖∑ j, A d i j * v j‖ ^ 2 ≤
      c ^ 2 * ∑ i, (a d i) ^ 2 * ‖v i‖ ^ 2)
    (hdegree : ∀ i, v i ≠ 0 → ∑ d, (a d i) ^ 2 ≤ M) :
    ∑ d, ∑ i, ‖∑ j, A d i j * v j‖ ^ 2 ≤ c ^ 2 * M * ∑ i, ‖v i‖ ^ 2 := by
  calc
    _ ≤ ∑ d, c ^ 2 * ∑ i, (a d i) ^ 2 * ‖v i‖ ^ 2 := sum_le_sum (fun d _ => hlocal d)
    _ = c ^ 2 * ∑ i, (∑ d, (a d i) ^ 2) * ‖v i‖ ^ 2 := by
      rw [← mul_sum, sum_comm]
      simp only [sum_mul]
    _ ≤ c ^ 2 * ∑ i, M * ‖v i‖ ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      apply sum_le_sum
      intro i _
      by_cases hi : v i = 0
      · simp [hi]
      · exact mul_le_mul_of_nonneg_right (hdegree i hi) (sq_nonneg _)
    _ = _ := by rw [← mul_sum, mul_assoc]

/-- Entrywise application identity lets the matrix estimate feed directly
into the finite-dimensional Hilbert-space spectral transfer. -/
theorem weighted_operator_norm_le
    (T : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι)
    (A : ι → ι → ℂ) (hT : ∀ v i, T v i = ∑ j, A i j * v j)
    (g a : ι → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hg : ∀ i, 0 < g i) (ha : ∀ i, 0 ≤ a i) (ha1 : ∀ i, a i ≤ 1)
    (hsymm : ∀ i j, ‖A i j‖ = ‖A j i‖)
    (hlevel : ∀ i j, A i j ≠ 0 → a i = a j)
    (hrow : ∀ i, ∑ j, ‖A i j‖ * g j / g i ≤ c * a i) : ‖T‖ ≤ c := by
  apply ContinuousLinearMap.opNorm_le_bound _ hc
  intro v
  have hlocal := weighted_matrix_localized_square A g a c hc hg ha hsymm hlevel hrow
    (fun i => v i)
  have hsum : (∑ i, (a i) ^ 2 * ‖v i‖ ^ 2) ≤ ∑ i, ‖v i‖ ^ 2 := by
    apply sum_le_sum
    intro i _
    have hi : (a i) ^ 2 ≤ 1 := by nlinarith [ha i, ha1 i]
    exact (mul_le_mul_of_nonneg_right hi (sq_nonneg _)).trans_eq (one_mul _)
  have hs : ‖T v‖ ^ 2 ≤ c ^ 2 * ‖v‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    simpa only [hT] using hlocal.trans (mul_le_mul_of_nonneg_left hsum (sq_nonneg _))
  have hn : 0 ≤ c * ‖v‖ := mul_nonneg hc (norm_nonneg _)
  nlinarith [norm_nonneg (T v)]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.IntegerEdges
namespace OAI

/-! Concrete centered integer edges and the padding-density cutoff. -/

namespace TwoPointCorrelations

open _root_.Finset








lemma integerEdgeMatrix_symmetric {ι : Type*} [Fintype ι]
    (site : ι → ℤ) (Q : Finset ℕ) (u : ℕ → ℝ)
    (eligible : ℕ → Prop) (g center : ℤ → ℝ) (L K : ℝ)
    (extra : ℤ → Prop) (h d : ℕ) (i j : ι) :
    integerEdgeMatrix site Q u eligible g center L K extra h d i j =
      integerEdgeMatrix site Q u eligible g center L K extra h d j i := by
  simp only [integerEdgeMatrix, add_comm]

lemma sum_indicator_site_le {ι : Type*} [Fintype ι]
    (site : ι → ℤ) (hinj : Function.Injective site) (n : ℤ)
    (C : ℝ) (hC : 0 ≤ C) : (∑ i, if site i = n then C else 0) ≤ C := by
  classical
  by_cases hex : ∃ i, site i = n
  · obtain ⟨i, hi⟩ := hex
    have heq (j : ι) : site j = n ↔ j = i := by
      constructor
      · intro hj
        exact hinj (hj.trans hi.symm)
      · rintro rfl
        exact hi
    simp [heq]
  · have hn (i : ι) : site i ≠ n := fun hi => hex ⟨i, hi⟩
    simpa [hn] using hC

/-- Divisibility by a padding divisor is unchanged along its integer edge. -/
lemma padding_dvd_along_edge (h q d : ℕ) (n m : ℤ)
    (hm : m = n + (h * q * d : ℕ)) : (q : ℤ) ∣ m ↔ (q : ℤ) ∣ n := by
  rw [hm]
  apply dvd_add_left
  norm_cast
  exact dvd_mul_of_dvd_left (dvd_mul_left q h) d


lemma retainedPaddingAtom_nonneg (Q : Finset ℕ) (u : ℕ → ℝ)
    (eligible : ℕ → Prop) (g : ℤ → ℝ) (L K : ℝ)
    (extra : ℤ → Prop) (n : ℤ) (q : ℕ) (hL : 0 ≤ L) (hu : 0 ≤ u q) :
    0 ≤ retainedPaddingAtom Q u eligible g L K extra n q := by
  unfold retainedPaddingAtom
  split_ifs
  · exact div_nonneg (mul_nonneg hL hu) (sq_nonneg _)
  · exact le_rfl

lemma retainedPaddingAtom_sum_le (Q : Finset ℕ) (u : ℕ → ℝ)
    (eligible : ℕ → Prop) (g : ℤ → ℝ) (L K : ℝ)
    (extra : ℤ → Prop) (n : ℤ) (hL : 0 < L) (hK : 0 ≤ K) :
    ∑ q ∈ Q, retainedPaddingAtom Q u eligible g L K extra n q ≤ K := by
  classical
  by_cases hk : integerEdgeKeep Q u eligible g L K extra n
  · have heq : (∑ q ∈ Q, retainedPaddingAtom Q u eligible g L K extra n q) =
        L * paddingDensity Q u eligible g n := by
      simp only [retainedPaddingAtom, paddingDensity]
      rw [← mul_div_assoc, mul_sum, sum_div]
      apply sum_congr rfl
      intro q _
      by_cases hq : eligible q ∧ (q : ℤ) ∣ n
      · simp [hq.1, hq.2, hk]
      · simp only [show ¬(eligible q ∧ (q : ℤ) ∣ n ∧ integerEdgeKeep Q u eligible g L K extra n) from
          fun hh => hq ⟨hh.1, hh.2.1⟩, hq, ite_false, mul_zero, zero_div]
    rw [heq]
    calc
      _ ≤ L * (K / L) := mul_le_mul_of_nonneg_left hk.1 hL.le
      _ = K := by field_simp
  · simpa [retainedPaddingAtom, hk] using hK



end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.IntegerEdgeRows
namespace OAI

/-! Derivation of the weighted row estimate for the concrete integer graph. -/

namespace TwoPointCorrelations

open _root_.Finset

variable (Q : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → Prop)
  (g center : ℤ → ℝ) (L K : ℝ) (extra : ℤ → Prop) (h d : ℕ)

lemma directedIntegerEdge_forward_bound
    (hL : 0 ≤ L) (hu : ∀ q ∈ Q, 0 ≤ u q) (hg : ∀ n, 0 < g n)
    (q : ℕ) (hq : q ∈ Q) (n m : ℤ) :
    |directedIntegerEdge Q u eligible g center L K extra h d q n m| * g m / g n ≤
      if m = n + (h * q * d : ℕ) then
        |center n| * retainedPaddingAtom Q u eligible g L K extra n q else 0 := by
  classical
  unfold directedIntegerEdge
  by_cases he : q ∈ Q ∧ m = n + (h * q * d : ℕ) ∧ eligible q ∧ (q : ℤ) ∣ n ∧
      integerEdgeKeep Q u eligible g L K extra n ∧ integerEdgeKeep Q u eligible g L K extra m
  · rw [if_pos he]
    have hkeep : eligible q ∧ (q : ℤ) ∣ n ∧ integerEdgeKeep Q u eligible g L K extra n :=
      ⟨he.2.2.1, he.2.2.2.1, he.2.2.2.2.1⟩
    rw [if_pos he.2.1, retainedPaddingAtom, if_pos hkeep]
    simp only [abs_div, abs_mul, abs_of_nonneg hL, abs_of_nonneg (hu q hq),
      abs_of_pos (hg n), abs_of_pos (hg m)]
    apply le_of_eq
    field_simp [(hg n).ne', (hg m).ne']
  · rw [if_neg he, abs_zero, zero_mul, zero_div]
    split_ifs
    · exact mul_nonneg (abs_nonneg _) (retainedPaddingAtom_nonneg Q u eligible g L K extra n q hL (hu q hq))
    · exact le_rfl

lemma directedIntegerEdge_backward_bound
    (hL : 0 ≤ L) (hu : ∀ q ∈ Q, 0 ≤ u q) (hg : ∀ n, 0 < g n)
    (hperiod : ∀ q ∈ Q, ∀ n, center (n + (h * q * d : ℕ)) = center n)
    (q : ℕ) (hq : q ∈ Q) (n m : ℤ) :
    |directedIntegerEdge Q u eligible g center L K extra h d q m n| * g m / g n ≤
      if m = n - (h * q * d : ℕ) then
        |center n| * retainedPaddingAtom Q u eligible g L K extra n q else 0 := by
  classical
  unfold directedIntegerEdge
  by_cases he : q ∈ Q ∧ n = m + (h * q * d : ℕ) ∧ eligible q ∧ (q : ℤ) ∣ m ∧
      integerEdgeKeep Q u eligible g L K extra m ∧ integerEdgeKeep Q u eligible g L K extra n
  · rw [if_pos he]
    have hm : m = n - (h * q * d : ℕ) := by omega
    have hdiv : (q : ℤ) ∣ n := (padding_dvd_along_edge h q d m n he.2.1).mpr he.2.2.2.1
    have hkeep : eligible q ∧ (q : ℤ) ∣ n ∧ integerEdgeKeep Q u eligible g L K extra n :=
      ⟨he.2.2.1, hdiv, he.2.2.2.2.2⟩
    have hc : center m = center n := by rw [he.2.1, hperiod q hq m]
    rw [if_pos hm, retainedPaddingAtom, if_pos hkeep, hc]
    simp only [abs_div, abs_mul, abs_of_nonneg hL, abs_of_nonneg (hu q hq),
      abs_of_pos (hg n), abs_of_pos (hg m)]
    apply le_of_eq
    field_simp [(hg n).ne', (hg m).ne']
  · rw [if_neg he, abs_zero, zero_mul, zero_div]
    split_ifs
    · exact mul_nonneg (abs_nonneg _) (retainedPaddingAtom_nonneg Q u eligible g L K extra n q hL (hu q hq))
    · exact le_rfl

lemma directedIntegerEdge_forward_row
    {ι : Type*} [Fintype ι] (site : ι → ℤ) (hinj : Function.Injective site)
    (hL : 0 ≤ L) (hu : ∀ q ∈ Q, 0 ≤ u q) (hg : ∀ n, 0 < g n)
    (q : ℕ) (hq : q ∈ Q) (i : ι) :
    (∑ j, |directedIntegerEdge Q u eligible g center L K extra h d q (site i) (site j)| *
      g (site j) / g (site i)) ≤
      |center (site i)| * retainedPaddingAtom Q u eligible g L K extra (site i) q := by
  apply le_trans (sum_le_sum (fun j _ =>
    directedIntegerEdge_forward_bound Q u eligible g center L K extra h d hL hu hg q hq _ _))
  exact sum_indicator_site_le site hinj _ _ (mul_nonneg (abs_nonneg _)
    (retainedPaddingAtom_nonneg Q u eligible g L K extra _ q hL (hu q hq)))

lemma directedIntegerEdge_backward_row
    {ι : Type*} [Fintype ι] (site : ι → ℤ) (hinj : Function.Injective site)
    (hL : 0 ≤ L) (hu : ∀ q ∈ Q, 0 ≤ u q) (hg : ∀ n, 0 < g n)
    (hperiod : ∀ q ∈ Q, ∀ n, center (n + (h * q * d : ℕ)) = center n)
    (q : ℕ) (hq : q ∈ Q) (i : ι) :
    (∑ j, |directedIntegerEdge Q u eligible g center L K extra h d q (site j) (site i)| *
      g (site j) / g (site i)) ≤
      |center (site i)| * retainedPaddingAtom Q u eligible g L K extra (site i) q := by
  apply le_trans (sum_le_sum (fun j _ =>
    directedIntegerEdge_backward_bound Q u eligible g center L K extra h d hL hu hg hperiod q hq _ _))
  exact sum_indicator_site_le site hinj _ _ (mul_nonneg (abs_nonneg _)
    (retainedPaddingAtom_nonneg Q u eligible g L K extra _ q hL (hu q hq)))

/-- Both edge orientations are bounded by the same retained padding mass.
Incoming divisibility uses the actual integer step `h*q*d`. -/
theorem integerEdgeMatrix_weighted_row
    {ι : Type*} [Fintype ι] (site : ι → ℤ) (hinj : Function.Injective site)
    (hL : 0 < L) (hK : 0 ≤ K) (hu : ∀ q ∈ Q, 0 ≤ u q) (hg : ∀ n, 0 < g n)
    (hperiod : ∀ q ∈ Q, ∀ n, center (n + (h * q * d : ℕ)) = center n)
    (i : ι) :
    ∑ j, |integerEdgeMatrix site Q u eligible g center L K extra h d i j| *
      g (site j) / g (site i) ≤ 2 * K * |center (site i)| := by
  have habs (j : ι) : |integerEdgeMatrix site Q u eligible g center L K extra h d i j| ≤
      ∑ q ∈ Q, (|directedIntegerEdge Q u eligible g center L K extra h d q (site i) (site j)| +
        |directedIntegerEdge Q u eligible g center L K extra h d q (site j) (site i)|) := by
    apply (abs_sum_le_sum_abs _ _).trans
    exact sum_le_sum (fun q _ => abs_add_le _ _)
  calc
    _ ≤ ∑ j, (∑ q ∈ Q, (|directedIntegerEdge Q u eligible g center L K extra h d q (site i) (site j)| +
        |directedIntegerEdge Q u eligible g center L K extra h d q (site j) (site i)|)) *
        g (site j) / g (site i) := by
      apply sum_le_sum
      intro j _
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (habs j) (hg _).le) (hg _).le
    _ = ∑ q ∈ Q, ∑ j, (|directedIntegerEdge Q u eligible g center L K extra h d q (site i) (site j)| +
        |directedIntegerEdge Q u eligible g center L K extra h d q (site j) (site i)|) *
        g (site j) / g (site i) := by
      simp only [sum_mul, sum_div]
      rw [sum_comm]
    _ = ∑ q ∈ Q,
        ((∑ j, |directedIntegerEdge Q u eligible g center L K extra h d q (site i) (site j)| * g (site j) / g (site i)) +
          ∑ j, |directedIntegerEdge Q u eligible g center L K extra h d q (site j) (site i)| * g (site j) / g (site i)) := by
      simp only [add_mul, add_div, sum_add_distrib]
    _ ≤ ∑ q ∈ Q, 2 * |center (site i)| * retainedPaddingAtom Q u eligible g L K extra (site i) q := by
      apply sum_le_sum
      intro q hq
      have hf := directedIntegerEdge_forward_row Q u eligible g center L K extra h d site hinj hL.le hu hg q hq i
      have hb := directedIntegerEdge_backward_row Q u eligible g center L K extra h d site hinj hL.le hu hg hperiod q hq i
      exact (add_le_add hf hb).trans_eq (by ring)
    _ = 2 * |center (site i)| * (∑ q ∈ Q, retainedPaddingAtom Q u eligible g L K extra (site i) q) :=
      (mul_sum ..).symm
    _ ≤ 2 * |center (site i)| * K := mul_le_mul_of_nonneg_left
      (retainedPaddingAtom_sum_le Q u eligible g L K extra _ hL hK) (by positivity)
    _ = _ := by ring

lemma integerEdgeMatrix_center_invariant
    {ι : Type*} [Fintype ι] (site : ι → ℤ)
    (hperiod : ∀ q ∈ Q, ∀ n, center (n + (h * q * d : ℕ)) = center n)
    (i j : ι)
    (hA : integerEdgeMatrix site Q u eligible g center L K extra h d i j ≠ 0) :
    center (site i) = center (site j) := by
  classical
  by_contra hc
  apply hA
  unfold integerEdgeMatrix
  apply sum_eq_zero
  intro q hq
  have hf : directedIntegerEdge Q u eligible g center L K extra h d q (site i) (site j) = 0 := by
    unfold directedIntegerEdge
    split_ifs with he
    · exact False.elim (hc (by rw [he.2.1, hperiod q hq (site i)]))
    · rfl
  have hb : directedIntegerEdge Q u eligible g center L K extra h d q (site j) (site i) = 0 := by
    unfold directedIntegerEdge
    split_ifs with he
    · exact False.elim (hc (by rw [he.2.1, hperiod q hq (site j)]))
    · rfl
  simp only [hf, hb, add_zero]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.MaskedRows
namespace OAI

/-! Edge deletions preserve the weighted-row estimates. -/

namespace TwoPointCorrelations

open _root_.Finset

variable {ι : Type*} [Fintype ι]


omit [Fintype ι] in
lemma maskMatrix_norm_le (gate : ι → ι → Prop) (A : ι → ι → ℂ) (i j : ι) :
    ‖maskMatrix gate A i j‖ ≤ ‖A i j‖ := by
  classical
  unfold maskMatrix
  split_ifs
  · exact le_rfl
  · simp


omit [Fintype ι] in
lemma maskMatrix_level (gate : ι → ι → Prop) (A : ι → ι → ℂ) (a : ι → ℝ)
    (hlevel : ∀ i j, A i j ≠ 0 → a i = a j) (i j : ι)
    (hij : maskMatrix gate A i j ≠ 0) : a i = a j := by
  classical
  apply hlevel i j
  intro hz
  exact hij (by simp [maskMatrix, hz])

lemma maskMatrix_weighted_row (gate : ι → ι → Prop) (A : ι → ι → ℂ)
    (g a : ι → ℝ) (c : ℝ) (hg : ∀ i, 0 < g i)
    (hrow : ∀ i, ∑ j, ‖A i j‖ * g j / g i ≤ c * a i) (i : ι) :
    ∑ j, ‖maskMatrix gate A i j‖ * g j / g i ≤ c * a i := by
  apply le_trans _ (hrow i)
  apply sum_le_sum
  intro j _
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (maskMatrix_norm_le gate A i j) (hg j).le) (hg i).le

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.MaskedIntegerEdges
namespace OAI

/-! Extra symmetric edge restrictions preserve the concrete graph estimates. -/

namespace TwoPointCorrelations

open _root_.Finset

variable {ι : Type*} [Fintype ι]


lemma maskedIntegerEdgeMatrix_symmetric
    (site : ι → ℤ) (Q : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → Prop)
    (g center : ℤ → ℝ) (L K : ℝ) (extra : ℤ → Prop) (h d : ℕ)
    (gate : ι → ι → Prop) (hgate : ∀ i j, gate i j ↔ gate j i) (i j : ι) :
    maskedIntegerEdgeMatrix site Q u eligible g center L K extra h d gate i j =
      star (maskedIntegerEdgeMatrix site Q u eligible g center L K extra h d gate j i) := by
  classical
  simp only [maskedIntegerEdgeMatrix, maskMatrix, hgate i j]
  split_ifs
  · simp only [Complex.star_def, Complex.conj_ofReal]
    rw [integerEdgeMatrix_symmetric site Q u eligible g center L K extra h d i j]
  · simp

lemma maskedIntegerEdgeMatrix_weighted_row
    (site : ι → ℤ) (hinj : Function.Injective site)
    (Q : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → Prop)
    (g center : ℤ → ℝ) (L K : ℝ) (extra : ℤ → Prop) (h d : ℕ)
    (gate : ι → ι → Prop)
    (hL : 0 < L) (hK : 0 ≤ K) (hu : ∀ q ∈ Q, 0 ≤ u q) (hg : ∀ n, 0 < g n)
    (hperiod : ∀ q ∈ Q, ∀ n, center (n + (h * q * d : ℕ)) = center n) (i : ι) :
    ∑ j, ‖maskedIntegerEdgeMatrix site Q u eligible g center L K extra h d gate i j‖ *
      g (site j) / g (site i) ≤ 2 * K * |center (site i)| := by
  apply maskMatrix_weighted_row gate _ (fun i => g (site i)) (fun i => |center (site i)|)
    (2 * K) (fun i => hg _)
  intro k
  simpa only [Complex.norm_real, Real.norm_eq_abs] using
    integerEdgeMatrix_weighted_row Q u eligible g center L K extra h d site hinj hL hK hu hg hperiod k

lemma maskedIntegerEdgeMatrix_level
    (site : ι → ℤ) (Q : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → Prop)
    (g center : ℤ → ℝ) (L K : ℝ) (extra : ℤ → Prop) (h d : ℕ)
    (gate : ι → ι → Prop)
    (hperiod : ∀ q ∈ Q, ∀ n, center (n + (h * q * d : ℕ)) = center n) (i j : ι)
    (hij : maskedIntegerEdgeMatrix site Q u eligible g center L K extra h d gate i j ≠ 0) :
    |center (site i)| = |center (site j)| := by
  apply maskMatrix_level gate _ (fun i => |center (site i)|) _ i j hij
  intro k m hkm
  exact congrArg abs (integerEdgeMatrix_center_invariant Q u eligible g center L K extra h d
    site hperiod k m (fun hz => hkm (by simp [hz])))

/-- The full localized estimate survives all symmetric entry restrictions. -/
theorem maskedIntegerEdgeMatrix_localized_square
    (site : ι → ℤ) (hinj : Function.Injective site)
    (Q : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → Prop)
    (g center : ℤ → ℝ) (L K : ℝ) (extra : ℤ → Prop) (h d : ℕ)
    (gate : ι → ι → Prop) (hgate : ∀ i j, gate i j ↔ gate j i)
    (hL : 0 < L) (hK : 0 ≤ K) (hu : ∀ q ∈ Q, 0 ≤ u q) (hg : ∀ n, 0 < g n)
    (hperiod : ∀ q ∈ Q, ∀ n, center (n + (h * q * d : ℕ)) = center n)
    (v : ι → ℂ) :
    (∑ i, ‖∑ j, maskedIntegerEdgeMatrix site Q u eligible g center L K extra h d gate i j * v j‖ ^ 2) ≤
      4 * K ^ 2 * ∑ i, |center (site i)| ^ 2 * ‖v i‖ ^ 2 := by
  have hs := weighted_matrix_localized_square
    (maskedIntegerEdgeMatrix site Q u eligible g center L K extra h d gate)
    (fun i => g (site i)) (fun i => |center (site i)|) (2 * K) (by positivity)
    (fun i => hg _) (fun i => abs_nonneg _)
    (fun i j => by rw [maskedIntegerEdgeMatrix_symmetric site Q u eligible g center L K extra h d gate hgate i j, norm_star])
    (maskedIntegerEdgeMatrix_level site Q u eligible g center L K extra h d gate hperiod)
    (maskedIntegerEdgeMatrix_weighted_row site hinj Q u eligible g center L K extra h d gate hL hK hu hg hperiod) v
  convert (preTransparency := .instances) hs using 1
  ring

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PrimeFamilyWeights
namespace OAI

/-! Tuple weights in integer and product residue environments. -/

namespace TwoPointCorrelations

open _root_.Finset

variable {α : Type*} [Fintype α] [DecidableEq α]
  {P : α → Type*} [∀ i, Fintype (P i)]



omit [DecidableEq α] [∀ i, Fintype (P i)] in
lemma familyCenter_abs (value : (i : α) → P i → ℕ)
    (offset : (i : α) → P i → ℤ) (x : (i : α) → P i) (n : ℤ) :
    |familyCenter value offset x n| =
      ∏ i, centerMagnitude (value i (x i) : ℝ)⁻¹ (decide ((value i (x i) : ℤ) ∣ offset i (x i) + n)) := by
  simp [familyCenter, abs_prod, centerMagnitude]

omit [DecidableEq α] [∀ i, Fintype (P i)] in
lemma familyCenter_abs_le_one (value : (i : α) → P i → ℕ)
    (hprime : ∀ i p, (value i p).Prime)
    (offset : (i : α) → P i → ℤ) (x : (i : α) → P i) (n : ℤ) :
    |familyCenter value offset x n| ≤ 1 := by
  rw [familyCenter_abs]
  apply Finset.prod_le_one
  · intro i _
    exact centerMagnitude_nonneg _ _
  · intro i _
    have hp : (1 : ℝ) ≤ value i (x i) := by exact_mod_cast (hprime i (x i)).one_lt.le
    exact centerMagnitude_le_one _ _ (by positivity) ((inv_le_one₀ (by positivity)).mpr hp)

omit [DecidableEq α] [∀ i, Fintype (P i)] in
lemma familyCenter_padding_periodic (value : (i : α) → P i → ℕ)
    (offset : (i : α) → P i → ℤ) (x : (i : α) → P i) (h q : ℕ) (n : ℤ) :
    familyCenter value offset x (n + (h * q * familyTuple value x : ℕ)) =
      familyCenter value offset x n := by
  unfold familyCenter
  apply prod_congr rfl
  intro i _
  have hdiv : value i (x i) ∣ h * q * familyTuple value x :=
    dvd_mul_of_dvd_right (dvd_prod_of_mem (fun i => value i (x i)) (mem_univ i)) (h * q)
  have hdivInt : (value i (x i) : ℤ) ∣ (h * q * familyTuple value x : ℕ) := by exact_mod_cast hdiv
  simp only [← add_assoc, dvd_add_left hdivInt]

/-- The exact degree estimate, uniform over all residue offsets. -/
theorem familyCenter_square_sum_le (value : (i : α) → P i → ℕ)
    (hprime : ∀ i p, (value i p).Prime)
    (offset : (i : α) → P i → ℤ) (n : ℤ) (W : ℝ)
    (hV : ∀ i, ∑ p, (value i p : ℝ)⁻¹ ≤ 2 * W)
    (hdegree : (∑ i, ∑ p : P i, if (value i p : ℤ) ∣ offset i p + n then (1 : ℝ) else 0) ≤
      6 * W * Fintype.card α) :
    (∑ x : (i : α) → P i, |familyCenter value offset x n| ^ 2) ≤
      (8 * W) ^ Fintype.card α := by
  simp only [familyCenter_abs]
  apply squared_center_products_le (fun i p => (value i p : ℝ)⁻¹)
    (fun i p => decide ((value i p : ℤ) ∣ offset i p + n)) W
  · intro i p
    positivity
  · intro i p
    have hp : (1 : ℝ) ≤ value i p := by exact_mod_cast (hprime i p).one_lt.le
    exact (inv_le_one₀ (by positivity)).mpr hp
  · exact hV
  · simpa using hdegree


omit [DecidableEq α] [∀ i, Fintype (P i)] in
/-- With distinct selected primes, the integer family center is exactly the
paper's product over prime divisors of the numerical tuple. -/
lemma familyCenter_zero_eq_centeredTuple (value : (i : α) → P i → ℕ)
    (hprime : ∀ i p, (value i p).Prime) (x : (i : α) → P i)
    (hinj : Function.Injective (fun i => value i (x i))) (n : ℤ) :
    familyCenter value (fun _ _ => 0) x n = centeredTuple (familyTuple value x).primeFactors n := by
  classical
  rw [familyTuple_primeFactors value hprime x hinj, centeredTuple, prod_image]
  · simp only [familyCenter, zero_add]
  · exact fun i _ j _ hij => hinj hij

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PrimeFamilyGraph
namespace OAI

/-!
# The weighted-row lemma for concrete prime-family graph operators

This constructs the operators, rather than assuming a coordinate formula.
Arbitrary prime residue offsets cover both models. The symmetric gate can
include the progression test and any further edge deletions. The cutoff
uses the explicitly defined padding density.
-/

namespace TwoPointCorrelations

open _root_.Finset

variable {α ι : Type*} [Fintype α] [DecidableEq α] [Fintype ι] [DecidableEq ι]
  {P : α → Type*} [∀ i, Fintype (P i)]


omit [DecidableEq α] [∀ i, Fintype (P i)] in
theorem primeFamilyGraphOperator_selfAdjoint
    (value : (i : α) → P i → ℕ) (offset : (i : α) → P i → ℤ)
    (site : ι → ℤ) (Q : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → ℕ → Prop)
    (g : ℤ → ℝ) (L K : ℝ) (extra : ℕ → ℤ → Prop) (h : ℕ)
    (gate : ℕ → ι → ι → Prop) (hgate : ∀ d i j, gate d i j ↔ gate d j i)
    (x : (i : α) → P i) :
    IsSelfAdjoint (primeFamilyGraphOperator value offset site Q u eligible g L K extra h gate x) := by
  apply matrixOperator_selfAdjoint
  exact maskedIntegerEdgeMatrix_symmetric site Q u (eligible (familyTuple value x))
    g (familyCenter value offset x) L K (extra (familyTuple value x)) h
    (familyTuple value x) (gate (familyTuple value x)) (hgate _)

omit [DecidableEq α] [∀ i, Fintype (P i)] in
/-- The single-operator assertion of manuscript `q:weighted-rows`. -/
theorem primeFamilyGraphOperator_norm_le
    (value : (i : α) → P i → ℕ) (hprime : ∀ i p, (value i p).Prime)
    (offset : (i : α) → P i → ℤ) (site : ι → ℤ) (hinj : Function.Injective site)
    (Q : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → ℕ → Prop)
    (g : ℤ → ℝ) (L K : ℝ) (extra : ℕ → ℤ → Prop) (h : ℕ)
    (gate : ℕ → ι → ι → Prop) (hgate : ∀ d i j, gate d i j ↔ gate d j i)
    (hL : 0 < L) (hK : 0 ≤ K) (hu : ∀ q ∈ Q, 0 ≤ u q) (hg : ∀ n, 0 < g n)
    (x : (i : α) → P i) :
    ‖primeFamilyGraphOperator value offset site Q u eligible g L K extra h gate x‖ ≤ 2 * K := by
  let d := familyTuple value x
  let center := familyCenter value offset x
  let A := maskedIntegerEdgeMatrix site Q u (eligible d) g center L K (extra d) h d (gate d)
  have hperiod : ∀ q ∈ Q, ∀ n, center (n + (h * q * d : ℕ)) = center n :=
    fun q _ n => familyCenter_padding_periodic value offset x h q n
  change ‖matrixOperator A‖ ≤ _
  apply weighted_operator_norm_le (matrixOperator A) A (matrixOperator_apply A)
    (fun i => g (site i)) (fun i => |center (site i)|) (2 * K) (by positivity)
    (fun i => hg _) (fun i => abs_nonneg _) (fun i => familyCenter_abs_le_one value hprime offset x _)
  · intro i j
    dsimp [A]
    rw [maskedIntegerEdgeMatrix_symmetric site Q u (eligible d) g center L K (extra d) h d (gate d) (hgate d) i j, norm_star]
  · exact maskedIntegerEdgeMatrix_level site Q u (eligible d) g center L K (extra d) h d (gate d) hperiod
  · exact maskedIntegerEdgeMatrix_weighted_row site hinj Q u (eligible d) g center L K (extra d) h d (gate d) hL hK hu hg hperiod

/-- The square-function assertion of manuscript `q:weighted-rows`, with
its exact `4 K² (8W)^J` constant and the degree projection's support condition. -/
theorem primeFamilyGraphOperator_square_sum
    (value : (i : α) → P i → ℕ) (hprime : ∀ i p, (value i p).Prime)
    (offset : (i : α) → P i → ℤ) (site : ι → ℤ) (hinj : Function.Injective site)
    (Q : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → ℕ → Prop)
    (g : ℤ → ℝ) (L K W : ℝ) (extra : ℕ → ℤ → Prop) (h : ℕ)
    (gate : ℕ → ι → ι → Prop) (hgate : ∀ d i j, gate d i j ↔ gate d j i)
    (hL : 0 < L) (hK : 0 ≤ K) (hu : ∀ q ∈ Q, 0 ≤ u q) (hg : ∀ n, 0 < g n)
    (hV : ∀ i, ∑ p, (value i p : ℝ)⁻¹ ≤ 2 * W)
    (v : EuclideanSpace ℂ ι)
    (hdegree : ∀ k, v k ≠ 0 →
      (∑ i, ∑ p : P i, if (value i p : ℤ) ∣ offset i p + site k then (1 : ℝ) else 0) ≤
        6 * W * Fintype.card α) :
    (∑ x, ‖primeFamilyGraphOperator value offset site Q u eligible g L K extra h gate x v‖ ^ 2) ≤
      4 * K ^ 2 * (8 * W) ^ Fintype.card α * ‖v‖ ^ 2 := by
  let A (x : (i : α) → P i) := maskedIntegerEdgeMatrix site Q u (eligible (familyTuple value x))
    g (familyCenter value offset x) L K (extra (familyTuple value x)) h
    (familyTuple value x) (gate (familyTuple value x))
  have hlocal (x : (i : α) → P i) :
      (∑ i, ‖∑ j, A x i j * v j‖ ^ 2) ≤
        (2 * K) ^ 2 * ∑ i, |familyCenter value offset x (site i)| ^ 2 * ‖v i‖ ^ 2 := by
    have hh := maskedIntegerEdgeMatrix_localized_square site hinj Q u (eligible (familyTuple value x))
      g (familyCenter value offset x) L K (extra (familyTuple value x)) h (familyTuple value x)
      (gate (familyTuple value x)) (hgate _) hL hK hu hg
      (fun q _ n => familyCenter_padding_periodic value offset x h q n) (fun i => v i)
    convert (preTransparency := .instances) hh using 1
    ring
  have hs := localized_square_sum A (fun x i => |familyCenter value offset x (site i)|)
    (2 * K) ((8 * W) ^ Fintype.card α) (fun i => v i) hlocal
    (fun i hi => familyCenter_square_sum_le value hprime offset (site i) W hV (hdegree i hi))
  calc
    _ = ∑ x, ∑ i, ‖∑ j, A x i j * v j‖ ^ 2 := by
      simp only [EuclideanSpace.norm_sq_eq, primeFamilyGraphOperator, matrixOperator_apply, A]
    _ ≤ (2 * K) ^ 2 * (8 * W) ^ Fintype.card α * ∑ i, ‖v i‖ ^ 2 := hs
    _ = _ := by rw [EuclideanSpace.norm_sq_eq]; ring

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.SpectralScale
namespace OAI

/-! The trace spectral threshold also dominates the single-edge and
square-function scales needed for the noncommuting transfer. -/

namespace TwoPointCorrelations

lemma actual_spectral_scale_bounds (J : ℕ) (K W : ℝ) (hK : 0 ≤ K) (hW : 1 ≤ W) :
    let R := Real.exp 1 * (2 * (K * (2 * Real.exp 150 * Real.sqrt W) ^ J))
    0 ≤ R ∧ 2 * K ≤ R ∧ 4 * K ^ 2 * (8 * W) ^ J ≤ R ^ 2 := by
  dsimp only
  let C := 2 * Real.exp 150 * Real.sqrt W
  have hs : 1 ≤ Real.sqrt W := by simpa using Real.sqrt_le_sqrt hW
  have he : 2 ≤ Real.exp 150 := by linarith [Real.add_one_le_exp (150 : ℝ)]
  have hC : 1 ≤ C := by
    dsimp [C]
    nlinarith [Real.exp_pos (150 : ℝ)]
  have hCJ : 1 ≤ C ^ J := one_le_pow₀ hC
  have he1 : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  have hbase : 8 * W ≤ C ^ 2 := by
    have hW0 : 0 ≤ W := by linarith
    have hx : 0 ≤ (4 * (Real.exp 150) ^ 2 - 8) * W :=
      mul_nonneg (by nlinarith) hW0
    have hsq := Real.sq_sqrt hW0
    dsimp [C]
    nlinarith
  have hpower : (8 * W) ^ J ≤ (C ^ J) ^ 2 := by
    have hp := pow_le_pow_left₀ (by positivity : 0 ≤ 8 * W) hbase J
    simpa only [← pow_mul, Nat.mul_comm 2 J] using hp
  have hlarge : 2 * K * C ^ J ≤ Real.exp 1 * (2 * (K * C ^ J)) := by
    have hp := mul_le_mul_of_nonneg_right he1 (show 0 ≤ 2 * (K * C ^ J) by positivity)
    simpa only [one_mul, mul_assoc] using hp
  refine ⟨by positivity, ?_, ?_⟩
  · exact (le_mul_of_one_le_right (by positivity : 0 ≤ 2 * K) hCJ).trans hlarge
  · calc
      4 * K ^ 2 * (8 * W) ^ J ≤ (2 * K * C ^ J) ^ 2 := by
        have hp := mul_le_mul_of_nonneg_left hpower (show 0 ≤ 4 * K ^ 2 by positivity)
        nlinarith
      _ ≤ _ := (sq_le_sq₀ (by positivity) (by positivity)).mpr hlarge

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Circuits.FourierCorrection
namespace OAI

/-!
# Correcting an almost independent Boolean density

This is the finite Fourier correction used in the proof of the manuscript's
finite-residue comparison (`q:finite-law`, `q:fourier-correction-tv`). The
construction removes the chosen nonconstant Walsh coefficients and adds the
constant `a` before normalization, retaining pointwise nonnegativity.
-/

namespace TwoPointCorrelations

open _root_.Finset










@[simp] lemma booleanSign_not (b : Bool) : booleanSign (!b) = -booleanSign b := by
  cases b <;> norm_num [booleanSign]

@[simp] lemma booleanSign_sq (b : Bool) : booleanSign b * booleanSign b = 1 := by
  cases b <;> norm_num [booleanSign]

@[simp] lemma abs_booleanSign (b : Bool) : |booleanSign b| = 1 := by
  cases b <;> norm_num [booleanSign]



@[simp] lemma abs_walsh {n : ℕ} (S : Finset (Fin n)) (x : BooleanCube n) :
    |walsh S x| = 1 := by
  simp [walsh, Finset.abs_prod]

@[simp] lemma walsh_mul_self {n : ℕ} (S : Finset (Fin n)) (x : BooleanCube n) :
    walsh S x * walsh S x = 1 := by
  unfold walsh
  rw [← Finset.prod_mul_distrib]
  simp
























end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Circuits.BitEncoding
namespace OAI

/-!
# Exact finite jitter encoding

For `Q = 2^B`, the integer code `⌊(r Q + j)/s⌋`, with `j` uniform in
`{0,…,Q-1}`, has exactly the distribution of the first `B` binary digits
of `(r + U)/s` for uniform `U` in `[0,1)`. This finite construction avoids
continuous auxiliary probability spaces. Jointly uniform residue and
jitter give a uniform code. Decoding can fail for at most `s` jitter values
at each fixed residue, giving the stronger bound `s/Q`.
-/

open _root_.Finset

namespace TwoPointCorrelations












@[simp] lemma decode_jitterBits {s B : ℕ} (hs : 0 < s) (r : Fin s) (j : Fin (2 ^ B)) :
    decodeBits hs (jitterBits r j) = jitterDecode hs (by positivity) (jitterCode r j) := by
  simp [decodeBits, jitterBits]


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.EncodedCoefficients
namespace OAI

/-!
# Low-order coefficients of the actual encoded interval law

A Walsh coefficient only uses the residue coordinates touched by its bits.
All other independent jitters integrate out. The remaining observable is
bounded by one, so CRT gives the product of its selected moduli divided by
the interval length as an explicit coefficient bound.
-/

namespace TwoPointCorrelations

open _root_.Finset





@[simp] lemma flattenBitBlocks_apply {m B : ℕ} (z : Fin m → BooleanCube B)
    (k : Fin (m * B)) : flattenBitBlocks m B z k = z k.divNat k.modNat := rfl






















end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.ModFivePrimes
namespace OAI

/-! The fixed modulus-five prime-number input used by the manuscript.

Published source: D. Koukoulopoulos, *The Distribution of Prime Numbers*,
AMS, 2019, Theorem 12.1 (Siegel--Walfisz), with modulus 5 fixed. That theorem
is stated for the prime-counting function. `ModFiveThetaInput` is its standard
partial-summation consequence for the logarithmically weighted prime count,
specialized to the two selections needed here. The complementary selection
includes the single prime 5, which changes the error by a bounded amount.
Source: https://dms.umontreal.ca/~koukoulo/documents/publications/primes.pdf

The estimate includes every prime in the selected classes. Removing a finite
exceptional prime set contributes an explicit finite-deletion correction.
-/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical _root_.Topology











lemma modFivePrimesUpTo_le {one : Bool} {x : ℝ} (hx : 0 ≤ x) {p : ℕ}
    (hp : p ∈ modFivePrimesUpTo one x) : (p : ℝ) ≤ x :=
  (Nat.le_floor_iff hx).mp (mem_Icc.mp (mem_filter.mp hp).1).2






end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.BlockOperatorSpectrum
namespace OAI

/-! Identify the concrete nonbacktracking matrix with the operator in
the spectral transfer lemma. The change of norm is by conjugacy. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

variable {D V : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]


omit [DecidableEq D] [DecidableEq V] in
lemma blockEuclideanEquiv_apply (v : D → EuclideanSpace ℂ V) (d : D) (i : V) :
    blockEuclideanEquiv v (d, i) = v d i := rfl

omit [DecidableEq D] [DecidableEq V] in
lemma blockEuclideanEquiv_symm_apply (v : EuclideanSpace ℂ (D × V)) (d : D) (i : V) :
    blockEuclideanEquiv.symm v d i = v (d, i) := rfl

set_option maxHeartbeats 1000000 in
lemma blockNonbacktracking_operator_conj (A : D → Matrix V V ℝ) :
    blockEuclideanEquiv.conjContinuousAlgEquiv
      (nonbacktrackingContinuous (fun d => matrixOperator (fun i j => (A d i j : ℂ)))) =
      matrixOperator (fun i j => (blockNonbacktrackingMatrix A i j : ℂ)) := by
  ext v x
  rcases x with ⟨d, i⟩
  rw [ContinuousLinearEquiv.conjContinuousAlgEquiv_apply_apply, blockEuclideanEquiv_apply]
  change (∑ l ∈ univ.erase d, matrixOperator (fun i j => (A l i j : ℂ))
    (blockEuclideanEquiv.symm v l)) i = _
  simp only [WithLp.ofLp_sum, Finset.sum_apply, matrixOperator_apply,
    blockEuclideanEquiv_symm_apply]
  rw [Fintype.sum_prod_type]
  calc
    _ = ∑ l : D, if d ≠ l then ∑ j : V, (A l i j : ℂ) * v (l, j) else 0 := by
      have he : univ.erase d = univ.filter (fun l : D => d ≠ l) := by
        ext l
        simp [ne_comm]
      rw [he, sum_filter]
    _ = _ := by
      apply sum_congr rfl
      intro l _
      by_cases hd : d ≠ l <;> simp [blockNonbacktrackingMatrix, hd]

theorem blockNonbacktracking_spectralRadius (A : D → Matrix V V ℝ) :
    spectralRadius ℂ
      (nonbacktrackingContinuous (fun d => matrixOperator (fun i j => (A d i j : ℂ)))) =
      spectralRadius ℂ (matrixOperator (fun i j => (blockNonbacktrackingMatrix A i j : ℂ))) := by
  let e := (blockEuclideanEquiv (D := D) (V := V)).conjContinuousAlgEquiv
  have hs := AlgEquiv.spectrum_eq e
    (nonbacktrackingContinuous (fun d => matrixOperator (fun i j => (A d i j : ℂ))))
  rw [blockNonbacktracking_operator_conj] at hs
  simp only [spectralRadius, hs]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.CanonicalForest
namespace OAI

/-! Equal ordered-forest shapes identify their graphs by preorder indices. -/

namespace TwoPointCorrelations

open _root_.SimpleGraph _root_.BinaryTree

variable {V W : Type*}


@[simp] lemma forestIndexEquiv_val [DecidableEq V] (t : BinaryTree V)
    (ht : (forestNodes t).Nodup) (hc : ∀ v, v ∈ forestNodes t) (v : V) :
    (forestIndexEquiv t ht hc v).val = (forestNodes t).idxOf v := rfl






end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.ColumnDecoder
namespace OAI

/-!
# Decoding complete column patterns

Three binary streams merge regular segments with omitted runs, mark new
runs, and mark imperfect positions. Representative indices supply omitted
labels and imperfect attachments. All decoding is independent of numerical
primes, quotient coordinates, and padding coefficients.
-/

namespace TwoPointCorrelations











@[simp] theorem expandColumnRuns_length (flags : List (Bool × Bool))
    (runs : List CanonicalColumnLabel) (previous : Option CanonicalColumnLabel) :
    (expandColumnRuns flags runs previous).length = flags.length := by
  induction flags generalizing runs previous with
  | nil => rfl
  | cons flag flags ih => cases flag with
    | mk imperfect newRun =>
      cases imperfect <;> cases newRun <;> simp [expandColumnRuns, ih]


@[simp] theorem attachImperfectLabels_length (full rest : List (Option CanonicalColumnLabel))
    (refs : List ℕ) : (attachImperfectLabels full rest refs).length = rest.length := by
  induction rest generalizing refs with
  | nil => rfl
  | cons a rest ih => cases a <;> simp [attachImperfectLabels, ih]







end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.ColumnRunEncoding
namespace OAI

/-! Reconstructing perfect runs and imperfect attachments from their bits. -/

namespace TwoPointCorrelations

variable {α : Type*} [DecidableEq α]




@[simp] theorem columnFlags_length (entries : List (Option α)) (previous : Option α) :
    (columnFlags entries previous).length = entries.length := by
  induction entries generalizing previous with
  | nil => rfl
  | cons a rest ih => cases a <;> simp [columnFlags, ih]










end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.ColumnBoundaryEncoding
namespace OAI

/-! Run bits may force a split at a perfect-block boundary without changing its label. -/

namespace TwoPointCorrelations

variable {α : Type*} [DecidableEq α]



@[simp] theorem columnFlagsWithCuts_length (entries : List (Option α × Bool)) (previous : Option α) :
    (columnFlagsWithCuts entries previous).length = entries.length := by
  induction entries generalizing previous with
  | nil => rfl
  | cons entry rest ih => rcases entry with ⟨a, cut⟩; cases a <;> simp [columnFlagsWithCuts, ih]


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.ProhibitedWords
namespace OAI

/-!
# Positive words, reversal, and descent to a minimal prohibited word

A step keeps its whole tuple and padding divisor. Positivity is the exact
integer divisibility `q*d ∣ x` at its departure. Since the displacement is
`±h*q*d`, this divisibility also holds at its arrival. Restriction and
reversal therefore preserve positivity, as required in the witness descent.
-/

namespace TwoPointCorrelations


namespace SignedStep


@[simp] lemma flip_flip (a : SignedStep) : a.flip.flip = a := by
  cases a
  simp [flip]



@[simp] lemma displacement_flip (h : ℕ) (a : SignedStep) :
    a.flip.displacement h = -a.displacement h := by
  rcases a with ⟨b, d, q⟩
  cases b <;> simp [flip, displacement]


@[simp] lemma divisor_flip (a : SignedStep) : a.flip.divisor = a.divisor := rfl



end SignedStep


@[simp] lemma wordDisplacement_nil (h : ℕ) : wordDisplacement h [] = 0 := rfl

@[simp] lemma wordDisplacement_cons (h : ℕ) (a : SignedStep) (w : List SignedStep) :
    wordDisplacement h (a :: w) = a.displacement h + wordDisplacement h w := rfl

@[simp] lemma wordDisplacement_append (h : ℕ) (u v : List SignedStep) :
    wordDisplacement h (u ++ v) = wordDisplacement h u + wordDisplacement h v := by
  simp [wordDisplacement]


@[simp] lemma reverseWord_nil : reverseWord [] = [] := rfl

@[simp] lemma reverseWord_cons (a : SignedStep) (w : List SignedStep) :
    reverseWord (a :: w) = reverseWord w ++ [a.flip] := by simp [reverseWord]

@[simp] lemma reverseWord_append (u v : List SignedStep) :
    reverseWord (u ++ v) = reverseWord v ++ reverseWord u := by simp [reverseWord]

@[simp] lemma reverseWord_length (w : List SignedStep) : (reverseWord w).length = w.length := by
  simp [reverseWord]

@[simp] lemma reverseWord_reverseWord (w : List SignedStep) : reverseWord (reverseWord w) = w := by
  simp [reverseWord, List.map_map, Function.comp_def]

@[simp] lemma wordDisplacement_reverseWord (h : ℕ) (w : List SignedStep) :
    wordDisplacement h (reverseWord w) = -wordDisplacement h w := by
  induction w with
  | nil => simp
  | cons a w ih => simp [ih]


@[simp] lemma positiveWord_nil (h : ℕ) (x : ℤ) : PositiveWord h x [] := trivial

@[simp] lemma positiveWord_cons (h : ℕ) (x : ℤ) (a : SignedStep) (w : List SignedStep) :
    PositiveWord h x (a :: w) ↔ a.divisor ∣ x ∧ PositiveWord h (x + a.displacement h) w := Iff.rfl






















end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.IntegerShiftWords
namespace OAI

/-! The actual centered integer-edge matrix as a matrix of forced signed shifts. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical


lemma forward_edge_as_shift (Q : Finset ℕ) (u : ℕ → ℝ)
    (eligible : ℕ → Prop) (g center : ℤ → ℝ) (L K : ℝ)
    (extra : ℤ → Prop) (h d q : ℕ) (n m : ℤ) :
    directedIntegerEdge Q u eligible g center L K extra h d q n m =
      if m = n + (SignedStep.mk true d q).displacement h then
        signedIntegerWeight Q u eligible g center L K extra h ⟨true, d, q⟩ n else 0 := by
  classical
  have hd : (SignedStep.mk true d q).displacement h = (h * q * d : ℕ) := by
    simp [SignedStep.displacement, Nat.cast_mul]
  rw [hd]
  by_cases he : m = n + (h * q * d : ℕ)
  · subst m
    simp only [signedIntegerWeight, ↓reduceIte, hd]
  · have hf : ¬(q ∈ Q ∧ m = n + (h * q * d : ℕ) ∧ eligible q ∧ (q : ℤ) ∣ n ∧
        integerEdgeKeep Q u eligible g L K extra n ∧
        integerEdgeKeep Q u eligible g L K extra m) := fun hh => he hh.2.1
    rw [directedIntegerEdge, if_neg hf, if_neg he]

lemma backward_edge_as_shift (Q : Finset ℕ) (u : ℕ → ℝ)
    (eligible : ℕ → Prop) (g center : ℤ → ℝ) (L K : ℝ)
    (extra : ℤ → Prop) (h d q : ℕ) (n m : ℤ) :
    directedIntegerEdge Q u eligible g center L K extra h d q m n =
      if m = n + (SignedStep.mk false d q).displacement h then
        signedIntegerWeight Q u eligible g center L K extra h ⟨false, d, q⟩ n else 0 := by
  classical
  have hd : (SignedStep.mk false d q).displacement h = -(h * q * d : ℕ) := by
    simp [SignedStep.displacement, Nat.cast_mul]
  rw [hd]
  by_cases he : m = n + -(h * q * d : ℕ)
  · subst m
    simp only [signedIntegerWeight, Bool.false_eq_true, ↓reduceIte, hd]
  · have hn : n ≠ m + (h * q * d : ℕ) := by omega
    have hf : ¬(q ∈ Q ∧ n = m + (h * q * d : ℕ) ∧ eligible q ∧ (q : ℤ) ∣ m ∧
        integerEdgeKeep Q u eligible g L K extra m ∧
        integerEdgeKeep Q u eligible g L K extra n) := fun hh => hn hh.2.1
    rw [directedIntegerEdge, if_neg hf, if_neg he]


lemma integerEdgeMatrix_signed_shifts {V : Type*} [Fintype V]
    (site : V → ℤ) (Q : Finset ℕ) (u : ℕ → ℝ)
    (eligible : ℕ → Prop) (g center : ℤ → ℝ) (L K : ℝ)
    (extra : ℤ → Prop) (h d : ℕ) (i j : V) :
    integerEdgeMatrix site Q u eligible g center L K extra h d i j =
      ∑ q : Q, ∑ b : Bool,
        if site j = site i + (SignedStep.mk b d q).displacement h then
          signedIntegerWeight Q u eligible g center L K extra h ⟨b, d, q⟩ (site i)
        else 0 := by
  classical
  rw [integerEdgeMatrix, ← sum_coe_sort Q]
  apply sum_congr rfl
  intro q _
  rw [Fintype.sum_bool, forward_edge_as_shift, backward_edge_as_shift]

variable {D V : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]



omit [DecidableEq V] in
/-- The step index is the actual tuple label, padding divisor and sign.
The finite state records the preceding tuple and the integer site. -/
theorem block_integer_matrix_eq_shift
    (site : V → ℤ) (Q : Finset ℕ) (tuple : D → ℕ)
    (u : ℕ → ℝ) (eligible : D → ℕ → Prop) (g : ℤ → ℝ) (center : D → ℤ → ℝ)
    (L K : ℝ) (extra : D → ℤ → Prop) (h : ℕ) (gate : D → ℤ → ℤ → Prop) :
    blockNonbacktrackingMatrix (fun d i j =>
      if gate d (site i) (site j) then
        integerEdgeMatrix site Q u (eligible d) g (center d) L K (extra d) h (tuple d) i j
      else 0) =
    shiftMatrix (fun x : D × V => (x.1, site x.2)) (integerShiftNext Q tuple h)
      (integerShiftWeight Q tuple u eligible g center L K extra h gate) := by
  classical
  ext x y
  change (if x.1 ≠ y.1 then
    (if gate y.1 (site x.2) (site y.2) then
      integerEdgeMatrix site Q u (eligible y.1) g (center y.1) L K (extra y.1) h
        (tuple y.1) x.2 y.2 else 0) else 0) =
    shiftMatrix (fun x : D × V => (x.1, site x.2)) (integerShiftNext Q tuple h)
      (integerShiftWeight Q tuple u eligible g center L K extra h gate) x y
  rw [shiftMatrix, Fintype.sum_prod_type]
  rw [sum_eq_single y.1]
  · rw [Fintype.sum_prod_type]
    have ht (q : Q) (b : Bool) :
        (if integerShiftNext Q tuple h (y.1, q, b) (x.1, site x.2) = (y.1, site y.2)
          then integerShiftWeight Q tuple u eligible g center L K extra h gate
            (y.1, q, b) (x.1, site x.2) else 0) =
        if x.1 ≠ y.1 ∧ gate y.1 (site x.2) (site y.2) then
          if site y.2 = site x.2 + (SignedStep.mk b (tuple y.1) q).displacement h then
            signedIntegerWeight Q u (eligible y.1) g (center y.1) L K (extra y.1) h
              ⟨b, tuple y.1, q⟩ (site x.2) else 0
        else 0 := by
      by_cases he : site y.2 = site x.2 + (SignedStep.mk b (tuple y.1) q).displacement h
      · simp only [integerShiftNext, ← he, ↓reduceIte]
        simp [integerShiftWeight, integerShiftNext, ← he]
      · simp [integerShiftNext, Ne.symm he, he]
    trans ∑ q : Q, ∑ b : Bool,
      if x.1 ≠ y.1 ∧ gate y.1 (site x.2) (site y.2) then
        if site y.2 = site x.2 + (SignedStep.mk b (tuple y.1) q).displacement h then
          signedIntegerWeight Q u (eligible y.1) g (center y.1) L K (extra y.1) h
            ⟨b, tuple y.1, q⟩ (site x.2) else 0
      else 0
    · by_cases hc : x.1 ≠ y.1 ∧ gate y.1 (site x.2) (site y.2)
      · rw [if_pos hc.1, if_pos hc.2]
        simp only [if_pos hc]
        exact integerEdgeMatrix_signed_shifts site Q u (eligible y.1) g (center y.1)
          L K (extra y.1) h (tuple y.1) x.2 y.2
      · simp only [hc, ↓reduceIte, sum_const_zero]
        by_cases hd : x.1 ≠ y.1
        · have hg : ¬gate y.1 (site x.2) (site y.2) := fun hg => hc ⟨hd, hg⟩
          simp [hd, hg]
        · simp [hd]
    · apply sum_congr rfl
      intro q _
      apply sum_congr rfl
      intro b _
      convert (preTransparency := .instances) (ht q b).symm using 1
      split_ifs <;> rfl
  · intro d _ hd
    apply sum_eq_zero
    intro e _
    have hn : integerShiftNext Q tuple h (d, e) (x.1, site x.2) ≠ (y.1, site y.2) := by
      intro he
      exact hd (congrArg Prod.fst he)
    simp only [hn, ↓reduceIte]
  · simp

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.BlockGeometry
namespace OAI

/-!
# The shortest-gap argument for perfect blocks

The finite combinatorial lemma isolates a shortest gap across all prime
coordinates. Every label has interval-shaped uses inside the intervening
substring. The arithmetic lemmas below use exact integer displacement sums.
-/

namespace TwoPointCorrelations

open _root_.Finset








@[simp] lemma intervalDisplacement_singleton (D : ℕ → ℤ) (a : ℕ) :
    intervalDisplacement D a (a + 1) = D a := by simp [intervalDisplacement]





end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ShiftedIntegerPaths
namespace OAI

/-! Arithmetic translation leaves the physical copy and block gates fixed. -/

namespace TwoPointCorrelations

open scoped _root_.Classical

variable {D V : Type*}



variable [Fintype V] [DecidableEq D]






theorem physicalShiftWeight_masked_eq_integer (Q : Finset ℕ) (tuple : D → ℕ)
    (u : ℕ → ℝ) (eligible : ℕ → ℕ → Prop) (g : ℤ → ℝ)
    (center : ℕ → ℤ → ℝ) (L K : ℝ) (extra : ℕ → ℤ → Prop)
    (h : ℕ) (gate : D → ℤ → ℤ → Prop) (keep : ℤ → Prop) :
    physicalShiftWeight Q tuple h gate
      (maskedSignedIntegerWeight Q u eligible g center L K extra h keep) =
      integerShiftWeight Q tuple u (fun d => eligible (tuple d)) g
        (fun d => center (tuple d)) L K (fun d => extra (tuple d)) h
        (integerVertexGate gate keep) := by
  funext e x
  by_cases hc : x.1 ≠ e.1 <;>
    by_cases hg : gate e.1 x.2 (integerShiftNext Q tuple h e x).2 <;>
    by_cases hn : keep x.2 <;>
    by_cases hm : keep (integerShiftNext Q tuple h e x).2 <;>
    simp_all [physicalShiftWeight, maskedSignedIntegerWeight, integerShiftWeight,
      integerVertexGate, vertexIndicator, integerShiftNext]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PhysicalMatrixComparison
namespace OAI

/-! Compare physical matrix moments by their signed closed scalar words.
Copy gates remain fixed while only the arithmetic origin is averaged. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical


lemma FiniteLaw.uniform_average {α : Type*} [Fintype α] [Nonempty α] (f : α → ℝ) :
    (FiniteLaw.uniform α).average f = uniformAverage f := by
  simp only [FiniteLaw.average, FiniteLaw.uniform, uniformAverage, ← mul_sum, div_eq_mul_inv]
  ring


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ShiftMatrixTranslation
namespace OAI

/-! Translate the physical block coordinates without changing its
matrix. Arithmetic weights and the numerical gate use the same origin. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

theorem physicalShiftMatrix_translate {D V : Type*}
    [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
    (embed : V → D × ℤ) (Q : Finset ℕ) (tuple : D → ℕ) (h : ℕ)
    (gate : D → ℤ → ℤ → Prop) (weight : SignedStep → ℤ → ℝ) (c : ℤ) :
    shiftMatrix embed (integerShiftNext Q tuple h)
      (physicalShiftWeight Q tuple h gate (fun t n => weight t (n + c))) =
    shiftMatrix (fun i => ((embed i).1, (embed i).2 + c)) (integerShiftNext Q tuple h)
      (physicalShiftWeight Q tuple h (fun d n m => gate d (n - c) (m - c)) weight) := by
  ext i j
  apply sum_congr rfl
  intro e _
  have he : integerShiftNext Q tuple h e ((embed i).1, (embed i).2 + c) =
      ((embed j).1, (embed j).2 + c) ↔
      integerShiftNext Q tuple h e (embed i) = embed j := by
    rw [Prod.ext_iff, Prod.ext_iff]
    change (e.1 = (embed j).1 ∧ (embed i).2 + c +
      (SignedStep.mk e.2.2 (tuple e.1) e.2.1).displacement h = (embed j).2 + c) ↔
      (e.1 = (embed j).1 ∧ (embed i).2 +
      (SignedStep.mk e.2.2 (tuple e.1) e.2.1).displacement h = (embed j).2)
    constructor <;> rintro ⟨hd, hz⟩ <;> refine ⟨hd, ?_⟩ <;> omega
  have hw : physicalShiftWeight Q tuple h (fun d n m => gate d (n - c) (m - c)) weight
      e ((embed i).1, (embed i).2 + c) =
      physicalShiftWeight Q tuple h gate (fun t n => weight t (n + c)) e (embed i) := by
    have hs : (embed i).2 + c +
        (SignedStep.mk e.2.2 (tuple e.1) e.2.1).displacement h - c =
        (embed i).2 + (SignedStep.mk e.2.2 (tuple e.1) e.2.1).displacement h := by omega
    have hc : ((embed i).1 ≠ e.1 ∧
        gate e.1 (((embed i).2 + c) - c)
          ((integerShiftNext Q tuple h e ((embed i).1, (embed i).2 + c)).2 - c)) ↔
        ((embed i).1 ≠ e.1 ∧
        gate e.1 (embed i).2 (integerShiftNext Q tuple h e (embed i)).2) := by
      simp only [integerShiftNext, add_sub_cancel_right, hs]
    by_cases hg : (embed i).1 ≠ e.1 ∧
        gate e.1 (embed i).2 (integerShiftNext Q tuple h e (embed i)).2
    · simp only [physicalShiftWeight, if_pos hg, if_pos (hc.mpr hg)]
    · simp only [physicalShiftWeight, if_neg hg, if_neg (mt hc.mp hg)]
  simp only [he, hw]
  by_cases hc : integerShiftNext Q tuple h e (embed i) = embed j
  · simp only [if_pos hc]
  · simp only [if_neg hc]

theorem physicalBlockMatrix_eq_integer {D V : Type*}
    [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
    (site : V → ℤ) (Q : Finset ℕ) (tuple : D → ℕ) (h : ℕ)
    (gate : D → ℤ → ℤ → Prop) (u : ℕ → ℝ) (eligible : ℕ → ℕ → Prop)
    (g : ℤ → ℝ) (center : ℕ → ℤ → ℝ) (L K : ℝ)
    (extra : ℕ → ℤ → Prop) (keep : ℤ → Prop) (c : ℤ) :
    shiftMatrix (fun x : D × V => (x.1, site x.2)) (integerShiftNext Q tuple h)
      (physicalShiftWeight Q tuple h gate (fun t n =>
        maskedSignedIntegerWeight Q u eligible g center L K extra h keep t (n + c))) =
      blockNonbacktrackingMatrix (fun d i j =>
        if gate d (site i) (site j) ∧ keep (site i + c) ∧ keep (site j + c) then
          integerEdgeMatrix (fun i => site i + c) Q u (eligible (tuple d)) g (center (tuple d))
            L K (extra (tuple d)) h (tuple d) i j else 0) := by
  rw [physicalShiftMatrix_translate, physicalShiftWeight_masked_eq_integer]
  have hb := block_integer_matrix_eq_shift (fun i => site i + c) Q tuple u
    (fun d => eligible (tuple d)) g (fun d => center (tuple d)) L K
    (fun d => extra (tuple d)) h (integerVertexGate (fun d n m => gate d (n - c) (m - c)) keep)
  apply hb.symm.trans
  congr 1
  funext d i j
  simp only [integerVertexGate, add_sub_cancel_right]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.ColumnChunkBudgets
namespace OAI

/-! Exact decoder budgets for lists of actual perfect blocks. -/

namespace TwoPointCorrelations

open _root_.Finset

variable {α : Type*} [DecidableEq α]

omit [DecidableEq α] in
@[simp] theorem regularPieceCount_append (a b : List (List α ⊕ α)) :
    regularPieceCount (a ++ b) = regularPieceCount a + regularPieceCount b := by
  simp [regularPieceCount, List.filterMap_append]

omit [DecidableEq α] in
@[simp] theorem omittedPieceCount_append (a b : List (List α ⊕ α)) :
    omittedPieceCount (a ++ b) = omittedPieceCount a + omittedPieceCount b := by
  simp [omittedPieceCount, List.filterMap_append]






end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ShortBlockPartition
namespace OAI

/-! The actual subdivision of perfect intervals into short blocks. -/

namespace TwoPointCorrelations

variable {α : Type*}





@[simp] theorem shortBlocks_length (s : ℕ) (l : List α) :
    (shortBlocks s l).length = l.length / s + 1 := by
  simp [shortBlocks, shortBlockLengths]











end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PaddingDivisorEncoding
namespace OAI

/-! Squarefree padding divisors encode prime selections without multiplicity.
This identifies the bin law with the paper's numerical divisor sum. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical






lemma paddingAvailablePrimes_card (Q : Finset ℕ) (a : Q → Bool) :
    (paddingAvailablePrimes Q a).card = (selectedCoordinates Q a).card := by
  exact card_image_iff.mpr (fun _ _ _ _ h => Subtype.ext h)










end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PaddingIntegerBins
namespace OAI

/-! The squarefree divisor formula uses literal divisibility by the site,
including the site zero. Bin membership is exactly the half-open interval
condition in the manuscript. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical




lemma paddingAvailablePrimes_integer (Q : Finset ℕ) (n : ℤ) :
    paddingAvailablePrimes Q (fun p => decide ((p.val : ℤ) ∣ n)) =
      Q.filter (fun (p : ℕ) => (p : ℤ) ∣ n) := by
  ext p
  constructor
  · intro hp
    have hpQ := paddingAvailablePrimes_subset Q _ hp
    exact mem_filter.mpr ⟨hpQ, by
      simpa using (mem_paddingAvailablePrimes Q _ ⟨p, hpQ⟩).mp hp⟩
  · intro hp
    exact (mem_paddingAvailablePrimes Q _ ⟨p, (mem_filter.mp hp).1⟩).mpr
      (by simpa using (mem_filter.mp hp).2)




end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.WordSegments
namespace OAI

/-! Exact identification of list segments with integer displacement intervals. -/

namespace TwoPointCorrelations

open _root_.Finset


@[simp] lemma wordStepDisplacement_nil (h i : ℕ) : wordStepDisplacement h [] i = 0 := by
  simp [wordStepDisplacement]

@[simp] lemma wordStepDisplacement_cons_zero (h : ℕ) (a : SignedStep) (w : List SignedStep) :
    wordStepDisplacement h (a :: w) 0 = a.displacement h := rfl

@[simp] lemma wordStepDisplacement_cons_succ (h i : ℕ) (a : SignedStep) (w : List SignedStep) :
    wordStepDisplacement h (a :: w) (i + 1) = wordStepDisplacement h w i := rfl












end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.FixedColumnWords
namespace OAI

/-! The actual resampling model after every other column and padding are fixed. -/

namespace TwoPointCorrelations


namespace ColumnWordPattern

variable {α : Type*}




@[simp] lemma word_length (w : ColumnWordPattern α) (value : α → ℕ) :
    (w.word value).length = w.length := by simp [word]





end ColumnWordPattern

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.WitnessSystemDecoding
namespace OAI

/-! Decode bounded witness metadata into the actual interval or comparison relations. -/

namespace TwoPointCorrelations


attribute [instance] PackedPrimeRelation.termFintype

namespace WitnessSystemData

variable {n N : ℕ} {ι : Type*} [DecidableEq ι]







@[simp] lemma toSystem_size (d : WitnessSystemData n N ι) (main : LabeledPrimeWord ι)
    (word : Fin n → LabeledPrimeWord ι) (h : ℕ) (ht : d.Triangular main word h) :
    (d.toSystem main word h ht).size = d.chosen.card := by
  exact Fintype.card_coe d.chosen

@[simp] lemma toSystem_holds (d : WitnessSystemData n N ι) (main : LabeledPrimeWord ι)
    (word : Fin n → LabeledPrimeWord ι) (h : ℕ) (ht : d.Triangular main word h) (x : ι → ℤ) :
    (d.toSystem main word h ht).Holds x ↔ d.Holds main word h x := Iff.rfl

end WitnessSystemData

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.LabeledWordSegments
namespace OAI

/-! Splitting a coded word into the main path and its attached witness paths. -/

namespace TwoPointCorrelations
namespace LabeledPrimeWord

variable {ι : Type*} [DecidableEq ι]


omit [DecidableEq ι] in
@[simp] lemma segment_length (w : LabeledPrimeWord ι) (a n : ℕ) :
    (w.segment a n).word.length = min n (w.word.length - a) := by
  simp only [segment, List.length_take, List.length_drop]



end LabeledPrimeWord
end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ResidueLawUniform
namespace OAI

/-! The common padded carrier law pushes forward to the genuine uniform
product of prime residue fields. Padding points contribute zero mass. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical


local instance residuePrime_neZero {h J M : ℕ} (data : ProhibitedPrimeFamily h J M)
    (p : ↥(data.P ∪ data.Q)) : NeZero p.val := ⟨(data.prime p).ne_zero⟩


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.TuplePrimeArithmetic
namespace OAI

/-! Disjoint prime pools give the actual tuple factorization and unique tuple labels. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical





/-- The numerical whole tuple determines its column choices, as used by
the nonbacktracking matrix's actual copy labels. -/
theorem primeTuple_injective {J : ℕ} {P : Fin J → Finset ℕ}
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l)) :
    Function.Injective (fun x : (j : Fin J) → P j => ∏ j, (x j).val) := by
  intro x y he
  change (∏ j, (x j).val) = (∏ j, (y j).val) at he
  funext j
  apply Subtype.ext
  have hp := hprime j _ (x j).property
  have hd : (x j).val ∣ ∏ l, (y l).val := by
    rw [← he]
    exact dvd_prod_of_mem (fun l => (x l).val) (mem_univ j)
  obtain ⟨l, _, hdiv⟩ := (hp.prime.dvd_finsetProd_iff (fun l => (y l).val)).mp hd
  have hv : (x j).val = (y l).val :=
    (Nat.prime_dvd_prime_iff_eq hp (hprime l _ (y l).property)).mp hdiv
  have hjl : j = l := by
    by_contra hne
    exact (disjoint_left.mp (hdisjoint j l (Ne.symm hne)))
      (x j).property (hv.symm ▸ (y l).property)
  subst l
  exact hv

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ActualPrimeFamily
namespace OAI

/-! The prohibited-word data are constructed from the actual prime bands,
not assumed. Padding divisors have the requested degree cap, and the
finite pair catalog can impose any numerical eligibility condition. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical










lemma paddingPrimeSupply_bounds (E : Finset ℕ) (L : ℝ) {p : ℕ}
    (hp : p ∈ paddingPrimeSupply E L) : (p : ℝ) ≤ Real.exp L :=
  modFivePrimesUpTo_le (Real.exp_pos _).le (Finset.mem_sdiff.mp hp).1




end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ActualPaddingWeights
namespace OAI

/-! The graph's literal padding weight and vertex normalization.
The normalization is the square root of `5^omega_Q(n)` and depends
only on the padding-prime residues, including at the integer zero. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical





lemma actualPaddingCoefficient_nonneg (q : ℕ) : 0 ≤ actualPaddingCoefficient q := by
  unfold actualPaddingCoefficient
  positivity

lemma actualPaddingWeight_one_le (Q : Finset ℕ) (n : ℤ) : 1 ≤ actualPaddingWeight Q n :=
  one_le_pow₀ (by norm_num)

lemma actualPaddingVertex_one_le (Q : Finset ℕ) (n : ℤ) : 1 ≤ actualPaddingVertex Q n := by
  simpa only [actualPaddingVertex, Real.sqrt_one] using
    Real.sqrt_le_sqrt (actualPaddingWeight_one_le Q n)

lemma actualPaddingVertex_pos (Q : Finset ℕ) (n : ℤ) : 0 < actualPaddingVertex Q n :=
  zero_lt_one.trans_le (actualPaddingVertex_one_le Q n)


lemma actualPaddingVertex_sq (Q : Finset ℕ) (n : ℤ) :
    actualPaddingVertex Q n ^ 2 = actualPaddingWeight Q n :=
  Real.sq_sqrt (zero_le_one.trans (actualPaddingWeight_one_le Q n))






lemma actualPaddingDegree_eq_available (Q : Finset ℕ) (n : ℤ) :
    actualPaddingDegree Q n =
      (paddingAvailablePrimes Q (fun p => decide ((p.val : ℤ) ∣ n))).card := by
  rw [paddingAvailablePrimes_integer]
  rfl










end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PrimeDegreeTail
namespace OAI

/-! The prime-degree deletion under the literal full residue law.  The
positive tuple majorant has mean `2^omega(d)/d`, and its tilted degree
tail is exponentially small in `W * omega(d)`. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical






lemma abs_centeredTuple_le_positivePrimeWeight (S : Finset ℕ) (n : ℤ) :
    |centeredTuple S n| ≤ positivePrimeWeight S n := by
  rw [centeredTuple, abs_prod]
  apply Finset.prod_le_prod (fun _ _ => abs_nonneg _)
  intro p _
  have hi : 0 ≤ (if (p : ℤ) ∣ n then (1 : ℝ) else 0) := by
    split_ifs <;> norm_num
  have hp : 0 ≤ (p : ℝ)⁻¹ := by positivity
  simpa only [sub_zero, zero_sub, abs_neg, abs_of_nonneg hi, abs_of_nonneg hp, one_div] using
    abs_sub_le (if (p : ℤ) ∣ n then (1 : ℝ) else 0) 0 (p : ℝ)⁻¹




lemma actualPrimeDegree_eq_count (P : Finset ℕ) (n : ℤ) :
    (actualPaddingDegree P n : ℝ) =
      booleanCount (fun p : P => decide ((p.val : ℤ) ∣ n)) := by
  rw [actualPaddingDegree_eq_available, paddingAvailablePrimes_card, booleanCount_eq_card]
  rfl

namespace ProhibitedPrimeFamily

variable {h J M B : ℕ} (data : ProhibitedPrimeFamily h J M)





end ProhibitedPrimeFamily

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ActualCenterDegree
namespace OAI

/-! Specialize the arithmetic-geometric mean bound to the literal tuple
centers and the degree projection of the integer graph. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma actualPaddingDegree_biUnion {J : ℕ} (P : Fin J → Finset ℕ)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l)) (n : ℤ) :
    actualPaddingDegree (univ.biUnion P) n = ∑ j, actualPaddingDegree (P j) n := by
  have he : (univ.biUnion P).filter (fun p : ℕ => (p : ℤ) ∣ n) =
      univ.biUnion (fun j => (P j).filter (fun p : ℕ => (p : ℤ) ∣ n)) := by
    ext p
    simp only [mem_filter, mem_biUnion, mem_univ, true_and]
    aesop
  unfold actualPaddingDegree
  rw [he, card_biUnion]
  intro j _ l _ hjl
  exact (hdisjoint j l (Ne.symm hjl)).mono (filter_subset _ _) (filter_subset _ _)

lemma prime_band_indicator_sum {J : ℕ} (P : Fin J → Finset ℕ)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l)) (n : ℤ) :
    (∑ j : Fin J, ∑ p : P j, if (p.val : ℤ) ∣ n then (1 : ℝ) else 0) =
      (actualPaddingDegree (univ.biUnion P) n : ℝ) := by
  rw [actualPaddingDegree_biUnion P hdisjoint, Nat.cast_sum]
  simp [actualPrimeDegree_eq_count, booleanCount]


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.GraphSpectralTransfer
namespace OAI

/-! Apply the noncommuting transfer to the literal prime graph and its
degree projection. The single-edge and square-function bounds are proved. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical _root_.NNReal _root_.ENNReal

theorem prime_graph_compression_bound {J : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    (P : Fin J → Finset ℕ) (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l))
    (site : V → ℤ) (hinj : Function.Injective site)
    (Q : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → ℕ → Prop)
    (g : ℤ → ℝ) (L K W : ℝ) (extra : ℕ → ℤ → Prop) (h : ℕ)
    (gate : ℕ → V → V → Prop) (hgate : ∀ d i j, gate d i j ↔ gate d j i)
    (hL : 0 < L) (hK : 0 ≤ K) (hu : ∀ q ∈ Q, 0 ≤ u q) (hg : ∀ n, 0 < g n)
    (hV : ∀ j, primeHarmonicMass (P j) ≤ 2 * W) :
    let B := primeFamilyGraphOperator (fun j (p : P j) => p.val) (fun _ _ => 0)
      site Q u eligible g L K extra h gate
    let proj := coordinateProjection (fun i : V =>
      (actualPaddingDegree (univ.biUnion P) (site i) : ℝ) ≤ 6 * W * J)
    ∀ R : ℝ, 0 ≤ R → 2 * K ≤ R → 4 * K ^ 2 * (8 * W) ^ J ≤ R ^ 2 →
      spectralRadius ℂ (nonbacktrackingContinuous B) ≤ ENNReal.ofReal R →
      ‖proj * (∑ d, B d) * proj‖ ≤ 3 * R := by
  dsimp only
  intro R hR hsingle hsquare hradius
  let B := primeFamilyGraphOperator (fun j (p : P j) => p.val) (fun _ _ => 0)
    site Q u eligible g L K extra h gate
  let keep := fun i : V => (actualPaddingDegree (univ.biUnion P) (site i) : ℝ) ≤ 6 * W * J
  let proj := coordinateProjection keep
  apply noncommuting_spectral_transfer B
    (fun d => primeFamilyGraphOperator_selfAdjoint _ _ _ _ _ _ _ _ _ _ _ _ hgate d)
    proj (coordinateProjection_selfAdjoint keep) (coordinateProjection_idempotent keep)
    ⟨R, hR⟩
  · intro d
    exact (primeFamilyGraphOperator_norm_le _ (fun j p => hprime j _ p.property)
      _ _ hinj _ _ _ _ _ _ _ _ _ hgate hL hK hu hg d).trans hsingle
  · intro v hv
    change (∑ d, ‖B d v‖ ^ 2) ≤ R ^ 2 * ‖v‖ ^ 2
    have hs := primeFamilyGraphOperator_square_sum (fun j (p : P j) => p.val)
      (fun j p => hprime j _ p.property) (fun _ _ => 0) site hinj
      Q u eligible g L K W extra h gate hgate hL hK hu hg hV v ?_
    · apply hs.trans
      exact mul_le_mul_of_nonneg_right (by simpa only [Fintype.card_fin] using hsquare)
        (sq_nonneg ‖v‖)
    · intro i hi
      have hk := coordinateProjection_support keep v hv i hi
      simpa only [zero_add, prime_band_indicator_sum P hdisjoint, Fintype.card_fin] using hk
  · convert (preTransparency := .instances) hradius using 1
    exact (ENNReal.ofReal_eq_coe_nnreal hR).symm

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.GraphMatrixCompression
namespace OAI

/-! The real integer-edge matrix, its complex graph operator, and the
nonbacktracking block have exactly the same spectral parameter. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical _root_.NNReal _root_.ENNReal


lemma primeFamilyGraphOperator_eq_realMatrix {J : ℕ} {V : Type*}
    [Fintype V] [DecidableEq V]
    (P : Fin J → Finset ℕ) (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l))
    (site : V → ℤ) (Q : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → ℕ → Prop)
    (g : ℤ → ℝ) (L K : ℝ) (extra : ℕ → ℤ → Prop) (h : ℕ)
    (gate : ℕ → V → V → Prop) (d : (j : Fin J) → P j) :
    primeFamilyGraphOperator (fun j (p : P j) => p.val) (fun _ _ => 0)
      site Q u eligible g L K extra h gate d =
    matrixOperator (fun i j => (primeRealEdgeMatrix P site Q u eligible g L K extra h gate d i j : ℂ)) := by
  have hc : familyCenter (fun j (p : P j) => p.val) (fun _ _ => 0) d =
      centeredTuple (∏ j, (d j).val).primeFactors := by
    funext n
    exact familyCenter_zero_eq_centeredTuple _ (fun j p => hprime j _ p.property)
      d (selectedPrimeValues_injective d hdisjoint) n
  unfold primeFamilyGraphOperator
  rw [hc]
  congr 1
  funext i j
  simp only [maskedIntegerEdgeMatrix, maskMatrix, primeRealEdgeMatrix, familyTuple]
  split_ifs <;> simp

theorem prime_graph_compression_of_matrix_radius {J : ℕ} {V : Type*}
    [Fintype V] [DecidableEq V]
    (P : Fin J → Finset ℕ) (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l))
    (site : V → ℤ) (hinj : Function.Injective site)
    (Q : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → ℕ → Prop)
    (g : ℤ → ℝ) (L K W : ℝ) (extra : ℕ → ℤ → Prop) (h : ℕ)
    (gate : ℕ → V → V → Prop) (hgate : ∀ d i j, gate d i j ↔ gate d j i)
    (hL : 0 < L) (hK : 0 ≤ K) (hu : ∀ q ∈ Q, 0 ≤ u q) (hg : ∀ n, 0 < g n)
    (hV : ∀ j, primeHarmonicMass (P j) ≤ 2 * W)
    (R : ℝ) (hR : 0 ≤ R) (hsingle : 2 * K ≤ R)
    (hsquare : 4 * K ^ 2 * (8 * W) ^ J ≤ R ^ 2)
    (hradius : realMatrixSpectralRadius (blockNonbacktrackingMatrix
      (primeRealEdgeMatrix P site Q u eligible g L K extra h gate)) ≤ R) :
    let B := primeFamilyGraphOperator (fun j (p : P j) => p.val) (fun _ _ => 0)
      site Q u eligible g L K extra h gate
    let proj := coordinateProjection (fun i : V =>
      (actualPaddingDegree (univ.biUnion P) (site i) : ℝ) ≤ 6 * W * J)
    ‖proj * (∑ d, B d) * proj‖ ≤ 3 * R := by
  apply prime_graph_compression_bound P hprime hdisjoint site hinj Q u eligible g
    L K W extra h gate hgate hL hK hu hg hV R hR hsingle hsquare
  have he : primeFamilyGraphOperator (fun j (p : P j) => p.val)
      (fun _ _ => 0) site Q u eligible g L K extra h gate =
      (fun d => matrixOperator (fun i j =>
        (primeRealEdgeMatrix P site Q u eligible g L K extra h gate d i j : ℂ))) := by
    funext d
    exact primeFamilyGraphOperator_eq_realMatrix P hprime hdisjoint site Q u eligible g
      L K extra h gate d
  rw [he, blockNonbacktracking_spectralRadius]
  have ht : spectralRadius ℂ (matrixOperator (fun i j =>
      (blockNonbacktrackingMatrix
        (primeRealEdgeMatrix P site Q u eligible g L K extra h gate) i j : ℂ))) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.coe_ne_top (spectralRadius_le_nnnorm_clm _)
  rw [← ENNReal.ofReal_toReal ht]
  exact ENNReal.ofReal_le_ofReal hradius

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PrimePhysicalMatrix
namespace OAI

/-! Match the translated physical matrix with the concrete prime graph,
including the original endpoint masks. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

theorem primePhysicalMatrix_eq {J : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    (P : Fin J → Finset ℕ) (site : V → ℤ) (Q : Finset ℕ)
    (u : ℕ → ℝ) (eligible : ℕ → ℕ → Prop) (g : ℤ → ℝ)
    (L K : ℝ) (extra : ℕ → ℤ → Prop) (h : ℕ)
    (gate : ℕ → ℤ → ℤ → Prop) (keep : ℤ → Prop) (c : ℤ) :
    shiftMatrix (fun x : ((j : Fin J) → P j) × V => (x.1, site x.2))
      (integerShiftNext Q (fun d => ∏ j, (d j).val) h)
      (physicalShiftWeight Q (fun d => ∏ j, (d j).val) h
        (fun d n m => gate (∏ j, (d j).val) n m)
        (fun t n => maskedSignedIntegerWeight Q u eligible g
          (fun d => centeredTuple d.primeFactors) L K extra h keep t (n + c))) =
    blockNonbacktrackingMatrix (primeRealEdgeMatrix P (fun i => site i + c)
      Q u eligible g L K extra h (fun d i j =>
        gate d (site i) (site j) ∧ keep (site i + c) ∧ keep (site j + c))) := by
  have hs := physicalBlockMatrix_eq_integer site Q (fun d : (j : Fin J) → P j => ∏ j, (d j).val) h
    (fun d n m => gate (∏ j, (d j).val) n m) u eligible g
    (fun d => centeredTuple d.primeFactors) L K extra keep c
  apply hs.trans
  congr 1
  funext d i j
  unfold primeRealEdgeMatrix
  by_cases hc : gate (∏ j, (d j).val) (site i) (site j) ∧
      keep (site i + c) ∧ keep (site j + c)
  · simp only [if_pos hc]
  · simp only [if_neg hc]

theorem prime_physical_compression {J : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    (P : Fin J → Finset ℕ) (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l))
    (site : V → ℤ) (hinj : Function.Injective site)
    (Q : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → ℕ → Prop)
    (g : ℤ → ℝ) (L K W : ℝ) (extra : ℕ → ℤ → Prop) (h : ℕ)
    (gate : ℕ → ℤ → ℤ → Prop) (hgate : ∀ d n m, gate d n m ↔ gate d m n)
    (keep : ℤ → Prop) (c : ℤ)
    (hL : 0 < L) (hK : 0 ≤ K) (hu : ∀ q ∈ Q, 0 ≤ u q) (hg : ∀ n, 0 < g n)
    (hV : ∀ j, primeHarmonicMass (P j) ≤ 2 * W)
    (R : ℝ) (hR : 0 ≤ R) (hsingle : 2 * K ≤ R)
    (hsquare : 4 * K ^ 2 * (8 * W) ^ J ≤ R ^ 2)
    (hradius : realMatrixSpectralRadius
      (shiftMatrix (fun x : ((j : Fin J) → P j) × V => (x.1, site x.2))
        (integerShiftNext Q (fun d => ∏ j, (d j).val) h)
        (physicalShiftWeight Q (fun d => ∏ j, (d j).val) h
          (fun d n m => gate (∏ j, (d j).val) n m)
          (fun t n => maskedSignedIntegerWeight Q u eligible g
            (fun d => centeredTuple d.primeFactors) L K extra h keep t (n + c)))) ≤ R) :
    let B := primeFamilyGraphOperator (fun j (p : P j) => p.val) (fun _ _ => 0)
      (fun i => site i + c) Q u eligible g L K extra h
      (fun d i j => gate d (site i) (site j) ∧ keep (site i + c) ∧ keep (site j + c))
    let proj := coordinateProjection (fun i : V =>
      (actualPaddingDegree (univ.biUnion P) (site i + c) : ℝ) ≤ 6 * W * J)
    ‖proj * (∑ d, B d) * proj‖ ≤ 3 * R := by
  rw [primePhysicalMatrix_eq] at hradius
  apply prime_graph_compression_of_matrix_radius P hprime hdisjoint (fun i => site i + c)
    (fun i j hij => hinj (add_right_cancel hij)) Q u eligible g L K W extra h
    (fun d i j => gate d (site i) (site j) ∧ keep (site i + c) ∧ keep (site j + c))
    ?_ hL hK hu hg hV R hR hsingle hsquare hradius
  intro d i j
  rw [hgate d (site i) (site j)]
  tauto

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PositiveRowMajorant
namespace OAI

/-! The literal sum of positive tuple weights is the row majorant
whose second moment was estimated under the product law. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma positivePrimeWeight_tuple {J : ℕ} (P : Fin J → Finset ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l))
    (d : (j : Fin J) → P j) (n : ℤ) :
    positivePrimeWeight (∏ j, (d j).val).primeFactors n =
      ∏ j, ((if ((d j).val : ℤ) ∣ n then 1 else 0) + 1 / ((d j).val : ℝ)) := by
  have hinj := selectedPrimeValues_injective d hdisjoint
  have hf : (∏ j, (d j).val).primeFactors = univ.image (fun j => (d j).val) :=
    familyTuple_primeFactors (fun j (p : P j) => p.val)
      (fun j p => hprime j _ p.property) d hinj
  rw [positivePrimeWeight, hf]
  rw [prod_image]
  intro i _ j _ hij
  exact hinj hij

lemma positivePrimeWeight_tuple_sum {J : ℕ} (P : Fin J → Finset ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l)) (n : ℤ) :
    (∑ d ∈ primeTupleDivisors P, positivePrimeWeight d.primeFactors n) =
      ∏ j, ((actualPaddingDegree (P j) n : ℝ) + primeHarmonicMass (P j)) := by
  rw [primeTupleDivisors, sum_image]
  · simp_rw [positivePrimeWeight_tuple P hprime hdisjoint]
    have he := (Fintype.prod_sum (fun j (p : P j) =>
      (if (p.val : ℤ) ∣ n then (1 : ℝ) else 0) + 1 / (p.val : ℝ))).symm
    apply he.trans
    apply prod_congr rfl
    intro j _
    rw [sum_add_distrib, actualPrimeDegree_eq_count]
    simp only [booleanCount, primeHarmonicMass, decide_eq_true_eq, one_div]
  · intro x _ y _ hxy
    exact primeTuple_injective hprime hdisjoint hxy

lemma positivePrimeWeight_tuple_sum_le {J : ℕ} (P : Fin J → Finset ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l)) (n : ℤ) (W : ℝ)
    (hV : ∀ j, primeHarmonicMass (P j) ≤ 2 * W)
    (hdegree : (actualPaddingDegree (univ.biUnion P) n : ℝ) ≤ 6 * W * J) :
    (∑ d ∈ primeTupleDivisors P, positivePrimeWeight d.primeFactors n) ≤ (8 * W) ^ J := by
  rw [positivePrimeWeight_tuple_sum P hprime hdisjoint]
  have hd : (∑ j, (actualPaddingDegree (P j) n : ℝ)) ≤ 6 * W * J := by
    rw [← Nat.cast_sum, ← actualPaddingDegree_biUnion P hdisjoint]
    exact hdegree
  have hb := nonneg_product_le_power_card
    (fun j => (actualPaddingDegree (P j) n : ℝ) + primeHarmonicMass (P j)) (8 * W)
    (fun j => add_nonneg (Nat.cast_nonneg _) (by unfold primeHarmonicMass; positivity))
    (sum_degree_budget (fun j => (actualPaddingDegree (P j) n : ℝ))
      (fun j => primeHarmonicMass (P j)) W hV (by simpa only [Fintype.card_fin] using hd))
  simpa only [Fintype.card_fin] using hb

/-- The deterministic first-power bound needed when testing the graph
against bounded vectors. The degree projection is the only site restriction. -/
lemma abs_centeredTuple_sum_le {J : ℕ} (P : Fin J → Finset ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l)) (n : ℤ) (W : ℝ)
    (hV : ∀ j, primeHarmonicMass (P j) ≤ 2 * W)
    (hdegree : (actualPaddingDegree (univ.biUnion P) n : ℝ) ≤ 6 * W * J) :
    (∑ d ∈ primeTupleDivisors P, |centeredTuple d.primeFactors n|) ≤ (8 * W) ^ J := by
  exact (sum_le_sum (fun d _ => abs_centeredTuple_le_positivePrimeWeight d.primeFactors n)).trans
    (positivePrimeWeight_tuple_sum_le P hprime hdisjoint n W hV hdegree)


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.GraphTesting
namespace OAI

/-! The deterministic quadratic-form estimate on every block, including
exceptional blocks. The projected support pays only a power of the mass. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma matrixOperator_sum {D V : Type*} [Fintype D] [Fintype V] [DecidableEq V]
    (A : D → V → V → ℂ) :
    matrixOperator (fun i j => ∑ d, A d i j) = ∑ d, matrixOperator (A d) := by
  ext v i
  simp only [_root_.sum_apply, matrixOperator_apply,
    WithLp.ofLp_sum, Finset.sum_apply, sum_mul]
  rw [sum_comm]

lemma sum_familyCenter_abs_le {J : ℕ} (P : Fin J → Finset ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l)) (n : ℤ) (W : ℝ)
    (hV : ∀ j, primeHarmonicMass (P j) ≤ 2 * W)
    (hdegree : (actualPaddingDegree (univ.biUnion P) n : ℝ) ≤ 6 * W * J) :
    (∑ d : (j : Fin J) → P j,
      |familyCenter (fun j (p : P j) => p.val) (fun _ _ => 0) d n|) ≤ (8 * W) ^ J := by
  have hb := abs_centeredTuple_sum_le P hprime hdisjoint n W hV hdegree
  rw [primeTupleDivisors, sum_image] at hb
  · simpa only [familyCenter_zero_eq_centeredTuple _ (fun j p => hprime j _ p.property)
      _ (selectedPrimeValues_injective _ hdisjoint), familyTuple] using hb
  · intro d _ e _ hde
    exact primeTuple_injective hprime hdisjoint hde

theorem prime_graph_test_deterministic {J : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    (P : Fin J → Finset ℕ) (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l))
    (site : V → ℤ) (hinj : Function.Injective site)
    (Q : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → ℕ → Prop)
    (g : ℤ → ℝ) (L K W : ℝ) (extra : ℕ → ℤ → Prop) (h : ℕ)
    (gate : ℕ → V → V → Prop)
    (hL : 0 < L) (hK : 0 ≤ K) (hW : 0 ≤ W)
    (hu : ∀ q ∈ Q, 0 ≤ u q) (hg : ∀ n, 0 < g n)
    (hV : ∀ j, primeHarmonicMass (P j) ≤ 2 * W)
    (v : EuclideanSpace ℂ V) (hv : ∀ i, ‖v i‖ ≤ g (site i))
    (hdegree : ∀ i, v i ≠ 0 →
      (actualPaddingDegree (univ.biUnion P) (site i) : ℝ) ≤ 6 * W * J)
    (G : ℝ) (hG : 0 ≤ G) (hweight : ∀ i, v i ≠ 0 → (g (site i)) ^ 2 ≤ G) :
    ‖inner ℂ v ((∑ d, primeFamilyGraphOperator (fun j (p : P j) => p.val)
      (fun _ _ => 0) site Q u eligible g L K extra h gate d) v)‖ ≤
        Fintype.card V * (2 * K * (8 * W) ^ J) * G := by
  let A (d : (j : Fin J) → P j) := maskedIntegerEdgeMatrix site Q u
    (eligible (familyTuple (fun j (p : P j) => p.val) d)) g
    (familyCenter (fun j (p : P j) => p.val) (fun _ _ => 0) d)
    L K (extra (familyTuple (fun j (p : P j) => p.val) d)) h
    (familyTuple (fun j (p : P j) => p.val) d)
    (gate (familyTuple (fun j (p : P j) => p.val) d))
  have hrow (i : V) (hi : v i ≠ 0) :
      (∑ j, ‖∑ d, A d i j‖ * g (site j) / g (site i)) ≤ 2 * K * (8 * W) ^ J := by
    calc
      _ ≤ ∑ j, (∑ d, ‖A d i j‖) * g (site j) / g (site i) := by
        apply sum_le_sum
        intro j _
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (norm_sum_le _ _) (hg _).le) (hg _).le
      _ = ∑ d, ∑ j, ‖A d i j‖ * g (site j) / g (site i) := by
        simp only [sum_mul, sum_div]
        rw [sum_comm]
      _ ≤ ∑ d : (j : Fin J) → P j,
          2 * K * |familyCenter (fun j (p : P j) => p.val) (fun _ _ => 0) d (site i)| := by
        apply sum_le_sum
        intro d _
        exact maskedIntegerEdgeMatrix_weighted_row site hinj Q u _ g _ L K _ h _ _
          hL hK hu hg (fun q _ n => familyCenter_padding_periodic _ _ d h q n) i
      _ = 2 * K * ∑ d : (j : Fin J) → P j,
          |familyCenter (fun j (p : P j) => p.val) (fun _ _ => 0) d (site i)| := by rw [mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (sum_familyCenter_abs_le P hprime hdisjoint (site i) W hV (hdegree i hi)) (by positivity)
  have ht := weighted_matrix_test_uniform (fun i j => ∑ d, A d i j)
    (fun i => g (site i)) (2 * K * (8 * W) ^ J) G
    (fun i => hg _) (by positivity) hG v hv hrow hweight
  rw [matrixOperator_sum] at ht
  exact ht

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.BlockTesting
namespace OAI

/-! Test the retained graph against bounded arithmetic functions. The
norm average uses the truncated integer padding estimate. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical

lemma norm_inner_operator_le {V : Type*} [Fintype V]
    (T : EuclideanSpace ℂ V →L[ℂ] EuclideanSpace ℂ V) (v : EuclideanSpace ℂ V) :
    ‖inner ℂ v (T v)‖ ≤ ‖T‖ * ‖v‖ ^ 2 := by
  calc
    _ ≤ ‖v‖ * ‖T v‖ := norm_inner_le_norm _ _
    _ ≤ ‖v‖ * (‖T‖ * ‖v‖) :=
      mul_le_mul_of_nonneg_left (T.le_opNorm v) (norm_nonneg _)
    _ = _ := by ring

theorem FiniteLaw.average_operator_test {Ω V : Type*} [Fintype Ω] [Fintype V]
    (μ : FiniteLaw Ω) (T : Ω → EuclideanSpace ℂ V →L[ℂ] EuclideanSpace ℂ V)
    (v : Ω → EuclideanSpace ℂ V) (B D Z δ : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hv : μ.average (fun x => ‖v x‖ ^ 2) ≤ Z)
    (hbad : μ.probability (fun x => B < ‖T x‖) ≤ δ)
    (hbound : ∀ x, B < ‖T x‖ → ‖inner ℂ (v x) (T x (v x))‖ ≤ D) :
    μ.average (fun x => ‖inner ℂ (v x) (T x (v x))‖) ≤ B * Z + D * δ := by
  have hp (x : Ω) : ‖inner ℂ (v x) (T x (v x))‖ ≤
      B * ‖v x‖ ^ 2 + D * (if B < ‖T x‖ then 1 else 0) := by
    by_cases hx : B < ‖T x‖
    · rw [if_pos hx, mul_one]
      exact (hbound x hx).trans (le_add_of_nonneg_left (mul_nonneg hB (sq_nonneg _)))
    · rw [if_neg hx, mul_zero, add_zero]
      exact (norm_inner_operator_le (T x) (v x)).trans
        (mul_le_mul_of_nonneg_right (le_of_not_gt hx) (sq_nonneg _))
  calc
    _ ≤ μ.average (fun x => B * ‖v x‖ ^ 2 + D * (if B < ‖T x‖ then 1 else 0)) :=
      μ.average_mono hp
    _ = B * μ.average (fun x => ‖v x‖ ^ 2) +
        D * μ.probability (fun x => B < ‖T x‖) := by
      simp only [FiniteLaw.average, FiniteLaw.probability, mul_add, sum_add_distrib]
      congr 1 <;> rw [mul_sum] <;> apply sum_congr rfl <;> intro x _ <;> ring
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hv hB)
      (mul_le_mul_of_nonneg_left hbad hD)






end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PaddingPolarization
namespace OAI

/-! Transfer the existing quadratic graph tests to two bounded sequences. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma paddingTestVector_halfPair {V : Type*} [Fintype V] (Q : Finset ℕ) (L : ℝ)
    (site : V → ℤ) (f g : ℤ → ℂ) (z : ℂ) :
    paddingTestVector Q L site (halfPairFunction f g z) =
      halfPair (paddingTestVector Q L site f) (paddingTestVector Q L site g) z := by
  ext i
  by_cases hi : actualPaddingDegreeCut Q L (site i)
  · simp [paddingTestVector, halfPairFunction, halfPair, hi, div_eq_mul_inv]
    ring
  · simp [paddingTestVector, halfPairFunction, halfPair, hi]

theorem uniformAverage_padding_bilinear {Ω V : Type*} [Fintype Ω] [Fintype V]
    (Q : Finset ℕ) (L : ℝ) (site : Ω → V → ℤ)
    (T : Ω → EuclideanSpace ℂ V →L[ℂ] EuclideanSpace ℂ V) (C : ℝ)
    (hquad : ∀ f : ℤ → ℂ, (∀ n, ‖f n‖ ≤ 1) →
      uniformAverage (fun x =>
        let v := paddingTestVector Q L (site x) f
        ‖inner ℂ v (T x v)‖) ≤ C)
    (f g : ℤ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1) (hg : ∀ n, ‖g n‖ ≤ 1) :
    uniformAverage (fun x => ‖inner ℂ (paddingTestVector Q L (site x) f)
      (T x (paddingTestVector Q L (site x) g))‖) ≤ 4 * C := by
  let q (z : ℂ) (x : Ω) :=
    let v := paddingTestVector Q L (site x) (halfPairFunction f g z)
    ‖inner ℂ v (T x v)‖
  have hb (z : ℂ) (hz : ‖z‖ ≤ 1) : uniformAverage (q z) ≤ C :=
    hquad (halfPairFunction f g z) (halfPairFunction_norm_le f g z hf hg hz)
  have hp (x : Ω) : ‖inner ℂ (paddingTestVector Q L (site x) f)
      (T x (paddingTestVector Q L (site x) g))‖ ≤
        q 1 x + q (-1) x + q Complex.I x + q (-Complex.I) x := by
    have h := complex_polarization_norm (T x)
      (paddingTestVector Q L (site x) f) (paddingTestVector Q L (site x) g)
    simpa only [q, paddingTestVector_halfPair] using h
  have hav : uniformAverage (fun x => ‖inner ℂ (paddingTestVector Q L (site x) f)
      (T x (paddingTestVector Q L (site x) g))‖) ≤
      uniformAverage (q 1) + uniformAverage (q (-1)) +
        uniformAverage (q Complex.I) + uniformAverage (q (-Complex.I)) := by
    unfold uniformAverage
    simpa only [sum_add_distrib, add_div] using
      div_le_div_of_nonneg_right (sum_le_sum (fun x _ => hp x))
        (Nat.cast_nonneg (α := ℝ) (Fintype.card Ω))
  have h1 := hb 1 (by simp)
  have hm := hb (-1) (by simp)
  have hi := hb Complex.I (by simp)
  have hmi := hb (-Complex.I) (by simp)
  linarith

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ProjectedGraphTesting
namespace OAI

/-! The deterministic bound for the manuscript's actual test vectors,
with both degree cutoffs and the square-root padding weight. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma paddingTestVector_apply_norm_le {V : Type*} (Q : Finset ℕ) (L : ℝ)
    (site : V → ℤ) (f : ℤ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1) (i : V) :
    ‖paddingTestVector Q L site f i‖ ≤ actualPaddingVertex Q (site i) := by
  by_cases hi : actualPaddingDegreeCut Q L (site i)
  · simp only [paddingTestVector, WithLp.ofLp_toLp, if_pos hi, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (actualPaddingVertex_pos Q _)]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (hf (site i))
      (actualPaddingVertex_pos Q _).le
  · simpa [paddingTestVector, hi] using (actualPaddingVertex_pos Q (site i)).le

lemma projected_paddingTestVector_support {V : Type*} [Fintype V] [DecidableEq V]
    (Q : Finset ℕ) (L : ℝ) (site : V → ℤ) (f : ℤ → ℂ) (keep : V → Prop)
    (i : V) (hi : coordinateProjection keep (paddingTestVector Q L site f) i ≠ 0) :
    keep i ∧ actualPaddingDegreeCut Q L (site i) := by
  constructor
  · by_contra hk
    apply hi
    simp only [coordinateProjection_apply, if_neg hk]
  · by_contra hq
    apply hi
    simp [coordinateProjection_apply, paddingTestVector, hq]

lemma paddingVertex_cut_bound (Q : Finset ℕ) (L : ℝ) (n : ℤ)
    (hn : actualPaddingDegreeCut Q L n) :
    actualPaddingVertex Q n ^ 2 ≤ (5 : ℝ) ^ (400 * Real.log L) := by
  rw [actualPaddingVertex_sq, actualPaddingWeight, ← Real.rpow_natCast]
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hn

theorem projected_padding_graph_test {J : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    (P : Fin J → Finset ℕ) (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l))
    (site : V → ℤ) (hinj : Function.Injective site)
    (Q Qp : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → ℕ → Prop)
    (L K W : ℝ) (extra : ℕ → ℤ → Prop) (h : ℕ) (gate : ℕ → V → V → Prop)
    (hL : 0 < L) (hK : 0 ≤ K) (hW : 0 ≤ W) (hu : ∀ q ∈ Q, 0 ≤ u q)
    (hV : ∀ j, primeHarmonicMass (P j) ≤ 2 * W)
    (f : ℤ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1) :
    let B := primeFamilyGraphOperator (fun j (p : P j) => p.val) (fun _ _ => 0)
      site Q u eligible (actualPaddingVertex Qp) L K extra h gate
    let proj := coordinateProjection (fun i : V =>
      (actualPaddingDegree (univ.biUnion P) (site i) : ℝ) ≤ 6 * W * J)
    let v := paddingTestVector Qp L site f
    ‖inner ℂ v ((proj * (∑ d, B d) * proj) v)‖ ≤
      Fintype.card V * (2 * K * (8 * W) ^ J) * (5 : ℝ) ^ (400 * Real.log L) := by
  dsimp only
  let keep := fun i : V => (actualPaddingDegree (univ.biUnion P) (site i) : ℝ) ≤ 6 * W * J
  let proj := coordinateProjection keep
  let v := paddingTestVector Qp L site f
  have hcoord (i : V) : ‖proj v i‖ ≤ actualPaddingVertex Qp (site i) := by
    dsimp only [proj]
    rw [coordinateProjection_apply]
    split_ifs
    · exact paddingTestVector_apply_norm_le Qp L site f hf i
    · simpa only [norm_zero] using (actualPaddingVertex_pos Qp (site i)).le
  have hsupp (i : V) (hi : proj v i ≠ 0) :
      keep i ∧ actualPaddingDegreeCut Qp L (site i) :=
    projected_paddingTestVector_support Qp L site f keep i hi
  have hb := prime_graph_test_deterministic P hprime hdisjoint site hinj Q u eligible
    (actualPaddingVertex Qp) L K W extra h gate hL hK hW hu
    (actualPaddingVertex_pos Qp) hV (proj v) hcoord (fun i hi => (hsupp i hi).1)
    ((5 : ℝ) ^ (400 * Real.log L)) (Real.rpow_nonneg (by norm_num) _)
    (fun i hi => paddingVertex_cut_bound Qp L (site i) (hsupp i hi).2)
  have he := (coordinateProjection_selfAdjoint keep).isSymmetric v
    ((∑ d, primeFamilyGraphOperator (fun j (p : P j) => p.val) (fun _ _ => 0)
      site Q u eligible (actualPaddingVertex Qp) L K extra h gate d) (proj v))
  change inner ℂ (proj v) _ = inner ℂ v (proj _) at he
  exact (le_of_eq (congrArg norm he.symm)).trans hb

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ActualAffineCompression
namespace OAI

/-! The literal compressed graph obeys the trace bound outside an
exponentially small set of origins in each fixed progression. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical


theorem ModFiveThetaInput.eventually_actual_affine_compression_uniform
    (hprime : ModFiveThetaInput) (hBr : BravermanDepth22Input) :
    ∃ A : ℕ, 1000 ≤ A ∧
      ∀ (h l : ℕ) (_hh : 0 < h) (E : Finset ℕ)
    (hE : ∀ p, p.Prime → p ∣ h → p ∈ E)
    (_hEl : ∀ p, p.Prime → p ∣ l → p ∈ E) (W : ℝ) (hW : 1 ≤ W),
      ∀ᶠ L : ℝ in atTop,
      ∀ (hL : 1 ≤ L) (η : ℝ), 0 < η → η ≤ 1 →
      ∀ eligible : ℕ → ℕ → Prop,
      (∀ d q, eligible d q → PaddingPairEligible L η d q) →
      let J := primeSupplyCount W L
      let P := centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W J
      let Qp := paddingPrimeSupply E L
      let Q := boundedPaddingDivisors Qp ⌊100 * Real.log L⌋₊
      let data := canonicalTraceFamily h E W L eligible hL hW hE
      let keep := fun z => ¬ProhibitedSite h ⌊L ^ (1 / 10 : ℝ)⌋₊
        (fun d q => (d, q) ∈ data.pairs) z
      ∀ gate : ℕ → ℤ → ℤ → Prop, (∀ d n m, gate d n m ↔ gate d m n) →
      ∀ a N : ℕ, Real.exp (L ^ A / 2) ≤ (N : ℝ) →
      uniformAverage (fun x : Fin N => if
        3 * (Real.exp 1 * (2 * (Real.exp (4 * J) *
          (2 * Real.exp 150 * Real.sqrt W) ^ J))) <
        ‖primeBlockCompression P ⌈Real.exp (103 * L)⌉₊ Q actualPaddingCoefficient
          (fun d q => (d, q) ∈ data.pairs) (actualPaddingVertex Qp)
          L (Real.exp (4 * J)) W (fun _ => actualPaddingDegreeCut Qp L) h gate keep
          (a + l * x.val : ℕ)‖ then (1 : ℝ) else 0) ≤
        Real.exp (-(2 * ⌊L⌋₊ : ℕ)) := by
  obtain ⟨A, hA, htail⟩ := hprime.eventually_actual_affine_spectral_tail_uniform hBr
  refine ⟨A, hA, ?_⟩
  intro h l hh E hE hEl W hW
  have htail := htail h l hh E hE hEl W hW
  filter_upwards [htail, hprime.eventually_actual_pool_masses E W hW] with L htail hmass
  intro hL η hη hηone eligible he
  dsimp only
  let J := primeSupplyCount W L
  let P := centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W J
  let Qp := paddingPrimeSupply E L
  let Q := boundedPaddingDivisors Qp ⌊100 * Real.log L⌋₊
  let data := canonicalTraceFamily h E W L eligible hL hW hE
  let keep := fun z => ¬ProhibitedSite h ⌊L ^ (1 / 10 : ℝ)⌋₊
    (fun d q => (d, q) ∈ data.pairs) z
  let K := Real.exp (4 * J)
  let R := Real.exp 1 * (2 * (K * (2 * Real.exp 150 * Real.sqrt W) ^ J))
  let M := ⌈Real.exp (103 * L)⌉₊
  have hbounds := actual_spectral_scale_bounds J K W (Real.exp_pos _).le hW
  have hprimeP := centeredPrimeBands_prime E (L ^ (199 / 200 : ℝ)) W J
  have hdisjoint := centeredPrimeBands_disjoint E (L ^ (199 / 200 : ℝ)) W J
    (Real.rpow_nonneg (by linarith) _) (by linarith)
  have hV : ∀ j, primeHarmonicMass (P j) ≤ 2 * W := fun j => (hmass.2.1 j).2.1
  intro gate hgate a N hN
  have ht := htail hL η hη hηone eligible he (fun d n m => gate (∏ j, (d j).val) n m) a N hN
  apply le_trans _ ht
  unfold uniformAverage
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply sum_le_sum
  intro x _
  by_cases hr : R < realMatrixSpectralRadius
      (shiftMatrix (primeBlockEmbedding (P := P) M)
        (integerShiftNext Q (fun d => ∏ j, (d j).val) h)
        (physicalShiftWeight Q (fun d => ∏ j, (d j).val) h
          (fun d n m => gate (∏ j, (d j).val) n m)
          (fun t n => maskedSignedIntegerWeight Q actualPaddingCoefficient
            (fun d q => (d, q) ∈ data.pairs) (actualPaddingVertex Qp)
            (fun d => centeredTuple d.primeFactors) L K
            (fun _ => actualPaddingDegreeCut Qp L) h keep t
            (n + (a + l * x.val : ℕ)))))
  · change (if _ then (1 : ℝ) else 0) ≤ if R < _ then 1 else 0
    rw [if_pos hr]
    split_ifs <;> norm_num
  · have hc := prime_physical_compression P hprimeP hdisjoint
      (fun i : Fin M => (i.val : ℤ))
      (fun i j hij => Fin.ext (Int.ofNat_inj.mp hij)) Q actualPaddingCoefficient
      (fun d q => (d, q) ∈ data.pairs) (actualPaddingVertex Qp) L K W
      (fun _ => actualPaddingDegreeCut Qp L) h gate hgate keep (a + l * x.val : ℕ)
      (by linarith) (Real.exp_pos _).le (fun q _ => actualPaddingCoefficient_nonneg q)
      (actualPaddingVertex_pos Qp) hV R hbounds.1 hbounds.2.1 hbounds.2.2
      (le_of_not_gt hr)
    change ‖primeBlockCompression P M Q actualPaddingCoefficient
      (fun d q => (d, q) ∈ data.pairs) (actualPaddingVertex Qp) L K W
      (fun _ => actualPaddingDegreeCut Qp L) h gate keep (a + l * x.val : ℕ)‖ ≤ 3 * R at hc
    change (if 3 * R < _ then (1 : ℝ) else 0) ≤ if R < _ then 1 else 0
    rw [if_neg (not_lt.mpr hc), if_neg hr]


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ActualAffineTesting
namespace OAI

/-! Average the actual graph test over fixed-progression block origins,
using compression on good blocks and the deterministic bound elsewhere. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical

theorem ModFiveThetaInput.eventually_actual_affine_testing_uniform
    (hprime : ModFiveThetaInput) (hBr : BravermanDepth22Input) :
    ∃ A : ℕ, 1000 ≤ A ∧
      ∀ (h l : ℕ) (_hh : 0 < h) (_hl : 0 < l) (E : Finset ℕ)
    (hE : ∀ p, p.Prime → p ∣ h → p ∈ E)
    (_hEl : ∀ p, p.Prime → p ∣ l → p ∈ E) (W : ℝ) (hW : 1 ≤ W),
      ∀ᶠ L : ℝ in atTop,
      ∀ (hL : 1 ≤ L) (η : ℝ), 0 < η → η ≤ 1 →
      ∀ eligible : ℕ → ℕ → Prop,
      (∀ d q, eligible d q → PaddingPairEligible L η d q) →
      let J := primeSupplyCount W L
      let P := centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W J
      let Qp := paddingPrimeSupply E L
      let Q := boundedPaddingDivisors Qp ⌊100 * Real.log L⌋₊
      let data := canonicalTraceFamily h E W L eligible hL hW hE
      let keep := fun z => ¬ProhibitedSite h ⌊L ^ (1 / 10 : ℝ)⌋₊
        (fun d q => (d, q) ∈ data.pairs) z
      ∀ gate : ℕ → ℤ → ℤ → Prop, (∀ d n m, gate d n m ↔ gate d m n) →
      ∀ f : ℤ → ℂ, (∀ n, ‖f n‖ ≤ 1) →
      ∀ a N : ℕ, Real.exp (L ^ A / 2) ≤ (N : ℝ) →
      let M := ⌈Real.exp (103 * L)⌉₊
      let K := Real.exp (4 * J)
      let R := Real.exp 1 * (2 * (K * (2 * Real.exp 150 * Real.sqrt W) ^ J))
      uniformAverage (fun x : Fin N =>
        let v := paddingTestVector Qp L (fun i : Fin M => (i.val : ℤ) + (a + l * x.val : ℕ)) f
        ‖inner ℂ v (primeBlockCompression P M Q actualPaddingCoefficient
          (fun d q => (d, q) ∈ data.pairs) (actualPaddingVertex Qp)
          L K W (fun _ => actualPaddingDegreeCut Qp L) h gate keep
          (a + l * x.val : ℕ) v)‖) ≤
        (3 * R) * ((l : ℝ) * (2 * M * paddingTiltNormalizer Qp)) +
          ((M : ℝ) * (2 * K * (8 * W) ^ J) * (5 : ℝ) ^ (400 * Real.log L)) *
            Real.exp (-(2 * ⌊L⌋₊ : ℕ)) := by
  obtain ⟨Ac, hAc, hcomp⟩ := hprime.eventually_actual_affine_compression_uniform hBr
  obtain ⟨Av, hAv, hnorm⟩ := hBr.eventually_padding_test_progression_norm
  refine ⟨Ac + Av, by omega, ?_⟩
  intro h l hh hl E hE hEl W hW
  have hcomp := hcomp h l hh E hE hEl W hW
  filter_upwards [hcomp, hnorm, hprime.eventually_actual_pool_masses E W hW]
    with L hcomp hnorm hmass
  intro hL η hη hηone eligible he
  dsimp only
  let J := primeSupplyCount W L
  let P := centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W J
  let Qp := paddingPrimeSupply E L
  let Q := boundedPaddingDivisors Qp ⌊100 * Real.log L⌋₊
  let data := canonicalTraceFamily h E W L eligible hL hW hE
  let keep := fun z => ¬ProhibitedSite h ⌊L ^ (1 / 10 : ℝ)⌋₊
    (fun d q => (d, q) ∈ data.pairs) z
  let M := ⌈Real.exp (103 * L)⌉₊
  let K := Real.exp (4 * J)
  let R := Real.exp 1 * (2 * (K * (2 * Real.exp 150 * Real.sqrt W) ^ J))
  have hprimeP := centeredPrimeBands_prime E (L ^ (199 / 200 : ℝ)) W J
  have hdisjoint := centeredPrimeBands_disjoint E (L ^ (199 / 200 : ℝ)) W J
    (Real.rpow_nonneg (by linarith) _) (by linarith)
  have hV : ∀ j, primeHarmonicMass (P j) ≤ 2 * W := fun j => (hmass.2.1 j).2.1
  intro gate hgate f hf a N hN
  have hNc : Real.exp (L ^ Ac / 2) ≤ (N : ℝ) :=
    (Real.exp_le_exp.mpr (div_le_div_of_nonneg_right
      (pow_le_pow_right₀ hL (Nat.le_add_right Ac Av)) (by norm_num))).trans hN
  have hNv : Real.exp (L ^ Av / 2) ≤ (N : ℝ) :=
    (Real.exp_le_exp.mpr (div_le_div_of_nonneg_right
      (pow_le_pow_right₀ hL (Nat.le_add_left Av Ac)) (by norm_num))).trans hN
  have hNpos : 0 < N := by exact_mod_cast (Real.exp_pos _).trans_le hN
  let : Nonempty (Fin N) := ⟨⟨0, hNpos⟩⟩
  let T (x : Fin N) := primeBlockCompression P M Q actualPaddingCoefficient
    (fun d q => (d, q) ∈ data.pairs) (actualPaddingVertex Qp)
    L K W (fun _ => actualPaddingDegreeCut Qp L) h gate keep (a + l * x.val : ℕ)
  let v (x : Fin N) := paddingTestVector Qp L
    (fun i : Fin M => (i.val : ℤ) + (a + l * x.val : ℕ)) f
  have hb := hcomp hL η hη hηone eligible he gate hgate a N hNc
  have hv := hnorm Qp (fun p hp => paddingPrimeSupply_prime hp)
    (fun p hp => paddingPrimeSupply_bounds E L hp) (fun i : Fin M => (i.val : ℤ)) f hf a l N hl hNv
  have hv' : uniformAverage (fun x : Fin N => ‖v x‖ ^ 2) ≤
      (l : ℝ) * (2 * M * paddingTiltNormalizer Qp) := by
    simpa only [v, add_comm ((a + l * _ : ℕ) : ℤ), Fintype.card_fin] using hv
  have htest := (FiniteLaw.uniform (Fin N)).average_operator_test T v
    (3 * R) ((M : ℝ) * (2 * K * (8 * W) ^ J) * (5 : ℝ) ^ (400 * Real.log L))
    ((l : ℝ) * (2 * M * paddingTiltNormalizer Qp)) (Real.exp (-(2 * ⌊L⌋₊ : ℕ)))
    (by positivity) (by positivity) ?_ ?_ ?_
  · simpa only [FiniteLaw.uniform_average, T, v, R, K, M, keep, data, Q, Qp, P, J] using htest
  · simpa only [FiniteLaw.uniform_average] using hv'
  · simpa only [FiniteLaw.probability, FiniteLaw.uniform_average, T, R, K, M, keep, data, Q, Qp, P, J] using hb
  · intro x _
    have ht := projected_padding_graph_test P hprimeP hdisjoint
      (fun i : Fin M => (i.val : ℤ) + (a + l * x.val : ℕ))
      (fun i j hij => Fin.ext (Int.ofNat_inj.mp (add_right_cancel hij)))
      Q Qp actualPaddingCoefficient (fun d q => (d, q) ∈ data.pairs) L K W
      (fun _ => actualPaddingDegreeCut Qp L) h
      (fun d i j => gate d i.val j.val ∧ keep ((i.val : ℤ) + (a + l * x.val : ℕ)) ∧
        keep ((j.val : ℤ) + (a + l * x.val : ℕ)))
      (by linarith) (Real.exp_pos _).le (by linarith)
      (fun q _ => actualPaddingCoefficient_nonneg q) hV f hf
    simpa only [primeBlockCompression, T, v, Fintype.card_fin] using ht


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ActualBilinearTesting
namespace OAI

/-! Two bounded sequences in the already-proved canonical graph estimate. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical

theorem ModFiveThetaInput.eventually_actual_affine_bilinear_testing_oai
    (hprime : ModFiveThetaInput) (hBr : BravermanDepth22Input) :
    ∃ A : ℕ, 1000 ≤ A ∧
      ∀ (h l : ℕ) (_hh : 0 < h) (_hl : 0 < l) (E : Finset ℕ)
    (hE : ∀ p, p.Prime → p ∣ h → p ∈ E)
    (_hEl : ∀ p, p.Prime → p ∣ l → p ∈ E) (W : ℝ) (hW : 1 ≤ W),
      ∀ᶠ L : ℝ in atTop,
      ∀ (hL : 1 ≤ L) (η : ℝ), 0 < η → η ≤ 1 →
      ∀ eligible : ℕ → ℕ → Prop,
      (∀ d q, eligible d q → PaddingPairEligible L η d q) →
      let J := primeSupplyCount W L
      let P := centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W J
      let Qp := paddingPrimeSupply E L
      let Q := boundedPaddingDivisors Qp ⌊100 * Real.log L⌋₊
      let data := canonicalTraceFamily h E W L eligible hL hW hE
      let keep := fun z => ¬ProhibitedSite h ⌊L ^ (1 / 10 : ℝ)⌋₊
        (fun d q => (d, q) ∈ data.pairs) z
      ∀ gate : ℕ → ℤ → ℤ → Prop, (∀ d n m, gate d n m ↔ gate d m n) →
      ∀ f g : ℤ → ℂ, (∀ n, ‖f n‖ ≤ 1) → (∀ n, ‖g n‖ ≤ 1) →
      ∀ a N : ℕ, Real.exp (L ^ A / 2) ≤ (N : ℝ) →
      let M := ⌈Real.exp (103 * L)⌉₊
      let K := Real.exp (4 * J)
      let R := Real.exp 1 * (2 * (K * (2 * Real.exp 150 * Real.sqrt W) ^ J))
      uniformAverage (fun x : Fin N =>
        let u := paddingTestVector Qp L (fun i : Fin M => (i.val : ℤ) + (a + l * x.val : ℕ)) f
        let v := paddingTestVector Qp L (fun i : Fin M => (i.val : ℤ) + (a + l * x.val : ℕ)) g
        ‖inner ℂ u (primeBlockCompression P M Q actualPaddingCoefficient
          (fun d q => (d, q) ∈ data.pairs) (actualPaddingVertex Qp)
          L K W (fun _ => actualPaddingDegreeCut Qp L) h gate keep
          (a + l * x.val : ℕ) v)‖) ≤
        4 * ((3 * R) * ((l : ℝ) * (2 * M * paddingTiltNormalizer Qp)) +
          ((M : ℝ) * (2 * K * (8 * W) ^ J) * (5 : ℝ) ^ (400 * Real.log L)) *
            Real.exp (-(2 * ⌊L⌋₊ : ℕ))) := by
  obtain ⟨A, hA, ht⟩ := hprime.eventually_actual_affine_testing_uniform hBr
  refine ⟨A, hA, ?_⟩
  intro h l hh hl E hE hEl W hW
  filter_upwards [ht h l hh hl E hE hEl W hW] with L htest
  intro hL η hη hηone eligible he
  dsimp only
  let J := primeSupplyCount W L
  let P := centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W J
  let Qp := paddingPrimeSupply E L
  let Q := boundedPaddingDivisors Qp ⌊100 * Real.log L⌋₊
  let data := canonicalTraceFamily h E W L eligible hL hW hE
  let keep := fun z => ¬ProhibitedSite h ⌊L ^ (1 / 10 : ℝ)⌋₊
    (fun d q => (d, q) ∈ data.pairs) z
  let M := ⌈Real.exp (103 * L)⌉₊
  let K := Real.exp (4 * J)
  let R := Real.exp 1 * (2 * (K * (2 * Real.exp 150 * Real.sqrt W) ^ J))
  intro gate hgate f g hf hg a N hN
  let site (x : Fin N) (i : Fin M) := (i.val : ℤ) + (a + l * x.val : ℕ)
  let T (x : Fin N) := primeBlockCompression P M Q actualPaddingCoefficient
    (fun d q => (d, q) ∈ data.pairs) (actualPaddingVertex Qp)
    L K W (fun _ => actualPaddingDegreeCut Qp L) h gate keep (a + l * x.val : ℕ)
  apply uniformAverage_padding_bilinear Qp L site T _ ?_ f g hf hg
  intro F hF
  exact htest hL η hη hηone eligible he gate hgate F hF a N hN

end TwoPointCorrelations

end OAI

end

theorem solution : type_of% @OAI.TwoPointCorrelations.ModFiveThetaInput.eventually_actual_affine_bilinear_testing_oai := @OAI.TwoPointCorrelations.ModFiveThetaInput.eventually_actual_affine_bilinear_testing_oai
