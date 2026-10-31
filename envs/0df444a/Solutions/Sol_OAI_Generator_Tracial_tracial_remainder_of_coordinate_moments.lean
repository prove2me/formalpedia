-- Prove2me | solution 1 for OAI.Generator.Tracial.tracial_remainder_of_coordinate_moments
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T16:25:16.706217+00:00
-- url     : https://prove2.me/submissions/d77f2a8f-85b4-462e-8911-7132ce76e8bd

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ11Fg020
import Definitions.Def_OAIQ11Fg014

section
-- module Solutions.OAIQ11_FG.FactorGeneration_Coefficients
attribute [-instance] _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator

/-! Coefficientwise absolute-value product comparison, retaining all convolution terms contributing to the same group element. -/
section
open scoped BigOperators
variable {G : Type*} [Monoid G]

omit [Monoid G] in
theorem normCoefficients_nonnegative (f : MonoidAlgebra ℂ G) (g : G) :
    0 ≤ (normCoefficients f).coeff g := by
  simpa only [normCoefficients_apply] using norm_nonneg (f.coeff g)

/-- Exact source inequality |fg|(w) ≤ (|f| |g|)(w), including cancellations. -/
theorem normCoefficients_mul_le (f g : MonoidAlgebra ℂ G) (w : G) :
    (normCoefficients (f * g)).coeff w ≤
      (normCoefficients f * normCoefficients g).coeff w := by
  classical
  rw [normCoefficients_apply, MonoidAlgebra.coeff_mul, MonoidAlgebra.coeff_mul]
  simp only [Finsupp.sum, normCoefficients_support, normCoefficients_apply]
  calc
    _ ≤ ∑ a ∈ f.coeff.support,
        ‖∑ b ∈ g.coeff.support, if a * b = w then f.coeff a * g.coeff b else 0‖ :=
      norm_sum_le _ _
    _ ≤ ∑ a ∈ f.coeff.support, ∑ b ∈ g.coeff.support,
        ‖if a * b = w then f.coeff a * g.coeff b else 0‖ :=
      Finset.sum_le_sum fun _ _ => norm_sum_le _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      split_ifs <;> simp

/-- The corresponding additive coefficient comparison. -/
theorem normCoefficients_add_le (f g : MonoidAlgebra ℂ G) (w : G) :
    (normCoefficients (f + g)).coeff w ≤
      (normCoefficients f + normCoefficients g).coeff w :=
  by simpa only [normCoefficients_apply, MonoidAlgebra.coeff_add, Finsupp.add_apply] using
    norm_add_le (f.coeff w) (g.coeff w)

end

/-! The coefficientwise ordered ring of real finite group-ring sums.
The multiplication is actual collected convolution. -/
open scoped BigOperators
namespace CoefficientOrder
variable {G : Type*} [Monoid G]

theorem mul_nonnegative {f g : MonoidAlgebra ℝ G} (hf : 0 ≤ f) (hg : 0 ≤ g) : 0 ≤ f * g := by
  classical
  intro w
  rw [MonoidAlgebra.coeff_mul]
  apply Finset.sum_nonneg
  intro a _
  apply Finset.sum_nonneg
  intro b _
  dsimp only
  split_ifs
  · exact mul_nonneg (hf a) (hg b)
  · exact le_refl _

theorem mul_le_left {f g : MonoidAlgebra ℝ G} (h : f ≤ g)
    (a : MonoidAlgebra ℝ G) (ha : 0 ≤ a) : a * f ≤ a * g := by
  have hd : 0 ≤ g - f := fun w => sub_nonneg.mpr (h w)
  have hm := mul_nonnegative ha hd
  rw [mul_sub] at hm
  exact fun w => sub_nonneg.mp (hm w)

theorem mul_le_right {f g : MonoidAlgebra ℝ G} (h : f ≤ g)
    (a : MonoidAlgebra ℝ G) (ha : 0 ≤ a) : f * a ≤ g * a := by
  have hd : 0 ≤ g - f := fun w => sub_nonneg.mpr (h w)
  have hm := mul_nonnegative hd ha
  rw [sub_mul] at hm
  exact fun w => sub_nonneg.mp (hm w)

instance coefficientOrderedRing : IsOrderedRing (MonoidAlgebra ℝ G) where
  mul_le_mul_of_nonneg_left := by
    intro a ha b c h
    exact mul_le_left h a ha
  mul_le_mul_of_nonneg_right := by
    intro a ha b c h
    exact mul_le_right h a ha

end CoefficientOrder

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_FreeWords
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

namespace Generator

/-! Distinct nonidentity off-diagonal prefix ratios, distinguished by abelian exponent coordinates. Labels start at zero. -/

theorem exponentCoordinate_ratio (i k j : ℕ) :
    Multiplicative.toAdd (exponentCoordinate i (prefixRatio k j)) =
      (if i < k then 1 else 0) - (if i < j then 1 else 0) := by
  simp [prefixRatio, exponentCoordinate_prefix, sub_eq_add_neg]

/-- Two differences of initial-segment indicators identify their endpoints,
provided the first interval is nonempty. -/
theorem indicator_difference_injective {k j k' j' : ℕ} (hkj : k ≠ j)
    (h : ∀ i : ℕ, (if i < k then (1 : ℤ) else 0) - (if i < j then 1 else 0) =
      (if i < k' then 1 else 0) - (if i < j' then 1 else 0)) :
    k = k' ∧ j = j' := by
  have hk := h k
  have hj := h j
  have hk' := h k'
  have hj' := h j'
  omega

theorem prefixRatio_injective_offDiagonal {k j k' j' : ℕ} (hkj : k ≠ j)
    (h : prefixRatio k j = prefixRatio k' j') : k = k' ∧ j = j' := by
  apply indicator_difference_injective hkj
  intro i
  simpa only [exponentCoordinate_ratio] using
    congrArg (fun g => Multiplicative.toAdd (exponentCoordinate i g)) h

/-! The exact multiplicity sum for prefix ratios, with labels g_(k+1) indexed by k : Fin n. -/
noncomputable section
open scoped BigOperators

attribute [local instance] OAI.Generator.instDecidableEqFreeGroupNat_solutions
theorem pairRatio_injective_offDiagonal {n : ℕ} {ij kl : Fin n × Fin n}
    (hij : ij.1 ≠ ij.2) (h : pairRatio ij = pairRatio kl) : ij = kl := by
  have hne : ij.1.val + 1 ≠ ij.2.val + 1 := by
    intro hval
    apply hij
    apply Fin.ext
    omega
  have he := prefixRatio_injective_offDiagonal hne h
  apply Prod.ext <;> apply Fin.ext <;> omega

theorem multiplicity_one (n : ℕ) : multiplicity n 1 = n := by
  classical
  have hset : (Finset.univ.filter fun ij : Fin n × Fin n => pairRatio ij = 1) =
      (Finset.univ : Finset (Fin n)).diag := by
    ext ij
    simp [pairRatio_eq_one_iff]
  simp [multiplicity, hset]

theorem multiplicity_offDiagonal {n : ℕ} {ij : Fin n × Fin n} (hij : ij.1 ≠ ij.2) :
    multiplicity n (pairRatio ij) = 1 := by
  classical
  have hset : (Finset.univ.filter fun kl : Fin n × Fin n => pairRatio kl = pairRatio ij) =
      {ij} := by
    ext kl
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ⟨fun h => (pairRatio_injective_offDiagonal hij h.symm).symm, fun h => h ▸ rfl⟩
  simp [multiplicity, hset]

/-- n_e = n and every off-diagonal label has multiplicity one. -/
theorem multiplicity_square_sum (n : ℕ) :
    ∑ p ∈ ratioLabels n, multiplicity n p ^ 2 = 2 * n ^ 2 - n := by
  classical
  have hnot : (1 : FreeGroup ℕ) ∉ (Finset.univ : Finset (Fin n)).offDiag.image pairRatio := by
    intro h
    obtain ⟨ij, hij, heq⟩ := Finset.mem_image.mp h
    exact (Finset.mem_offDiag.mp hij).2.2 ((pairRatio_eq_one_iff _).mp heq)
  have hsum : ∑ p ∈ (Finset.univ : Finset (Fin n)).offDiag.image pairRatio,
      multiplicity n p ^ 2 = n * n - n := by
    rw [Finset.sum_image]
    · calc
        _ = ∑ _ij ∈ (Finset.univ : Finset (Fin n)).offDiag, (1 : ℕ) := by
          apply Finset.sum_congr rfl
          intro ij hij
          rw [multiplicity_offDiagonal (Finset.mem_offDiag.mp hij).2.2]
          simp
        _ = n * n - n := by simp
    · intro ij hij kl _hkl heq
      exact pairRatio_injective_offDiagonal (Finset.mem_offDiag.mp hij).2.2 heq
  rw [ratioLabels, Finset.sum_insert hnot, multiplicity_one, hsum]
  have hn : n ≤ n * n := by nlinarith
  simp only [pow_two]
  omega

end

/-! Ordered prefix products. The element h denotes the unitary exponential of a self-adjoint operator, not its logarithm. The final letter is unperturbed. -/

end Generator

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_Convolution
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.quotientInnerProductSpace _root_.OAI.Generator.Tracial.quotientNormedAddCommGroup _root_.OAI.Generator.predualAlgebraDualNormed _root_.OAI.Generator.predualFunctionals_normed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator

/-! Coordinate masks and permutations on the actual complex square-summable space.
These implement the Hilbert-space operations used in lem:length-one-convolution. -/
section
open scoped BigOperators InnerProductSpace ENNReal
attribute [local instance] Classical.propDecidable

variable {X I : Type*}

theorem coordinateMask_norm_le (s : Set X) (f : SquareSpace X) :
    ‖coordinateMask s f‖ ≤ ‖f‖ := by
  apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
  intro x
  by_cases hx : x ∈ s <;> simp [hx]

/-- Disjoint coordinate support implies genuine Hilbert orthogonality. -/
theorem squareSpace_inner_zero {f g : SquareSpace X}
    (h : ∀ x, f x = 0 ∨ g x = 0) : inner ℂ f g = 0 := by
  change (∑' x, inner ℂ (f x) (g x)) = 0
  have hz : ∀ x, inner ℂ (f x) (g x) = 0 := by
    intro x
    rcases h x with hx | hx <;> simp [hx]
  simp only [hz, tsum_zero]

/-- Pythagoras for a finite family with disjoint supports. -/
theorem squareSpace_sum_norm_sq (s : Finset I) (f : I → SquareSpace X)
    (h : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ∀ x, f i x = 0 ∨ f j x = 0) :
    ‖∑ i ∈ s, f i‖ ^ 2 = ∑ i ∈ s, ‖f i‖ ^ 2 := by
  have hc : inner ℂ (∑ i ∈ s, f i) (∑ i ∈ s, f i) =
      ∑ i ∈ s, inner ℂ (f i) (f i) := by
    rw [sum_inner]
    apply Finset.sum_congr rfl
    intro i hi
    rw [inner_sum]
    exact Finset.sum_eq_single i
      (fun j hj hji => squareSpace_inner_zero (h i hi j hj hji.symm))
      (fun hn => (hn hi).elim)
  have hr := congrArg (RCLike.re : ℂ → ℝ) hc
  simpa only [map_sum, inner_self_eq_norm_sq] using hr

/-- The projections onto finitely many disjoint coordinate sets have total
squared mass at most that of the original vector. -/
theorem coordinateMask_sum_sq_le (s : Finset I) (U : I → Set X)
    (hU : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (U i) (U j))
    (f : SquareSpace X) :
    ∑ i ∈ s, ‖coordinateMask (U i) f‖ ^ 2 ≤ ‖f‖ ^ 2 := by
  have horth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ∀ x,
      coordinateMask (U i) f x = 0 ∨ coordinateMask (U j) f x = 0 := by
    intro i hi j hj hij x
    by_cases hx : x ∈ U i
    · right
      have hn : x ∉ U j := fun hxj => Set.disjoint_left.mp (hU i hi j hj hij) hx hxj
      simp [hn]
    · left; simp [hx]
  rw [← squareSpace_sum_norm_sq s _ horth]
  have hnorm : ‖∑ i ∈ s, coordinateMask (U i) f‖ ≤ ‖f‖ := by
    apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    intro x
    simp only [lp.coeFn_sum, Finset.sum_apply]
    by_cases hex : ∃ i ∈ s, x ∈ U i
    · obtain ⟨i, hi, hxi⟩ := hex
      rw [Finset.sum_eq_single i]
      · simp [hxi]
      · intro j hj hji
        have hn : x ∉ U j := fun hxj =>
          Set.disjoint_left.mp (hU i hi j hj hji.symm) hxi hxj
        simp [hn]
      · exact fun hn => (hn hi).elim
    · have hz : ∀ i ∈ s, coordinateMask (U i) f x = 0 := by
        intro i hi
        simp [show x ∉ U i from fun hx => hex ⟨i, hi, hx⟩]
      rw [Finset.sum_eq_zero hz, norm_zero]
      exact norm_nonneg _
  nlinarith [norm_nonneg (∑ i ∈ s, coordinateMask (U i) f), norm_nonneg f]

end

/-! Length-one convolution bounds for the left regular representation of a free group on an arbitrary basis. -/
section
open scoped BigOperators InnerProductSpace
attribute [local instance] Classical.propDecidable Classical.decEq
namespace FreeConvolution
variable {A : Type*}

theorem inverseLetter_injective : Function.Injective (inverseLetter : Letter A → Letter A) :=
  Function.Involutive.injective inverseLetter_inverse

/-- A noncancelling left multiplication creates its signed letter as the head. -/
theorem begins_letter_mul (a : Letter A) (w : FreeGroup A)
    (h : ¬ begins (inverseLetter a) w) : begins a (letter a * w) := by
  unfold begins at *
  rw [FreeGroup.toWord_mul, letter_toWord, List.singleton_append,
    FreeGroup.reduce.cons, FreeGroup.reduce_toWord]
  cases hw : w.toWord with
  | nil => simp
  | cons b bs =>
    have hn : ¬ (a.1 = b.1 ∧ a.2 = !b.2) := by
      intro he
      apply h
      simp only [hw, List.head?_cons, Option.some.injEq]
      apply Prod.ext
      · exact he.1.symm
      · simpa [inverseLetter] using congrArg Bool.not he.2.symm
    simp [hn]

theorem creation_add_cancellation (a : Letter A) (f : SquareSpace (FreeGroup A)) :
    creation a f + cancellation a f = leftRegular (letter a) f := by
  rw [creation, cancellation, ← map_add]
  congr 1
  ext x
  change coordinateMask {w | ¬ begins (inverseLetter a) w} f x +
    coordinateMask {w | begins (inverseLetter a) w} f x = f x
  by_cases hx : begins (inverseLetter a) x <;> simp [hx]

theorem creation_support (a : Letter A) (f : SquareSpace (FreeGroup A)) (x : FreeGroup A)
    (hx : ¬ begins a x) : creation a f x = 0 := by
  simp only [creation, leftRegular_apply, coordinateMask_apply, Set.mem_ofPred_eq]
  rw [ite_eq_right]
  intro hn
  apply hx
  simpa using begins_letter_mul a ((letter a)⁻¹ * x) hn

theorem begins_disjoint {a b : Letter A} (hab : a ≠ b) :
    Disjoint {w : FreeGroup A | begins a w} {w | begins b w} := by
  apply Set.disjoint_left.mpr
  intro w ha hb
  exact hab (Option.some.inj (ha.symm.trans hb))

theorem creation_norm_le (a : Letter A) (f : SquareSpace (FreeGroup A)) :
    ‖creation a f‖ ≤ ‖f‖ := by
  rw [creation, leftRegular_norm]
  exact coordinateMask_norm_le _ _

theorem creation_sum_bound (s : Finset (Letter A)) (b : Letter A → ℂ)
    (f : SquareSpace (FreeGroup A)) :
    ‖∑ a ∈ s, b a • creation a f‖ ≤ Real.sqrt (∑ a ∈ s, ‖b a‖ ^ 2) * ‖f‖ := by
  have horth : ∀ a ∈ s, ∀ c ∈ s, a ≠ c → ∀ x,
      (b a • creation a f) x = 0 ∨ (b c • creation c f) x = 0 := by
    intro a _ c _ hac x
    by_cases hx : begins a x
    · right
      have hn : ¬ begins c x := fun hc => Set.disjoint_left.mp (begins_disjoint hac) hx hc
      simp [lp.coeFn_smul, creation_support c f x hn]
    · left; simp [lp.coeFn_smul, creation_support a f x hx]
  have hsq : ‖∑ a ∈ s, b a • creation a f‖ ^ 2 ≤
      (∑ a ∈ s, ‖b a‖ ^ 2) * ‖f‖ ^ 2 := by
    rw [squareSpace_sum_norm_sq s _ horth, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro a _
    rw [norm_smul, mul_pow]
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    exact sq_le_sq₀ (norm_nonneg _) (norm_nonneg _) |>.mpr (creation_norm_le a f)
  have hS : 0 ≤ ∑ a ∈ s, ‖b a‖ ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have he : (Real.sqrt (∑ a ∈ s, ‖b a‖ ^ 2) * ‖f‖) ^ 2 =
      (∑ a ∈ s, ‖b a‖ ^ 2) * ‖f‖ ^ 2 := by rw [mul_pow, Real.sq_sqrt hS]
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
    (hsq.trans_eq he.symm)

theorem cancellation_sum_bound (s : Finset (Letter A)) (b : Letter A → ℂ)
    (f : SquareSpace (FreeGroup A)) :
    ‖∑ a ∈ s, b a • cancellation a f‖ ≤ Real.sqrt (∑ a ∈ s, ‖b a‖ ^ 2) * ‖f‖ := by
  have hmass : ∑ a ∈ s, ‖cancellation a f‖ ^ 2 ≤ ‖f‖ ^ 2 := by
    simp only [cancellation, leftRegular_norm]
    exact coordinateMask_sum_sq_le s _
      (fun a _ c _ hac => begins_disjoint (fun h => hac (inverseLetter_injective h))) f
  calc
    _ ≤ ∑ a ∈ s, ‖b a‖ * ‖cancellation a f‖ := by
      simpa only [norm_smul] using norm_sum_le s (fun a => b a • cancellation a f)
    _ ≤ Real.sqrt (∑ a ∈ s, ‖b a‖ ^ 2) *
        Real.sqrt (∑ a ∈ s, ‖cancellation a f‖ ^ 2) := Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ ≤ Real.sqrt (∑ a ∈ s, ‖b a‖ ^ 2) * Real.sqrt (‖f‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hmass) (Real.sqrt_nonneg _)
    _ = _ := by rw [Real.sqrt_sq (norm_nonneg f)]

/-- The manuscript's length-one bound on every vector of ℓ²(FreeGroup A). -/
theorem length_one_convolution_vector_bound (s : Finset (Letter A)) (b : Letter A → ℂ)
    (f : SquareSpace (FreeGroup A)) :
    ‖(∑ a ∈ s, b a • leftRegular (letter a)) f‖ ≤
      (2 * Real.sqrt (∑ a ∈ s, ‖b a‖ ^ 2)) * ‖f‖ := by
  have he : (∑ a ∈ s, b a • leftRegular (letter a)) f =
      (∑ a ∈ s, b a • creation a f) + (∑ a ∈ s, b a • cancellation a f) := by
    simp only [sum_apply, smul_apply,
      ← creation_add_cancellation, smul_add, Finset.sum_add_distrib]
  rw [he]
  have ht := norm_add_le (∑ a ∈ s, b a • creation a f) (∑ a ∈ s, b a • cancellation a f)
  have hc := creation_sum_bound s b f
  have hd := cancellation_sum_bound s b f
  linarith

/-- The length-one convolution estimate for the operator norm of the left regular action. -/
theorem length_one_convolution_operator_bound (s : Finset (Letter A)) (b : Letter A → ℂ) :
    ‖∑ a ∈ s, b a • leftRegular (letter a)‖ ≤
      2 * Real.sqrt (∑ a ∈ s, ‖b a‖ ^ 2) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  exact length_one_convolution_vector_bound s b

end FreeConvolution

end

/-! Group-ring action on ℓ² and the coefficient-vector identity. -/
section
open scoped BigOperators ENNReal
attribute [local instance] Classical.propDecidable Classical.decEq
namespace FreeConvolution
variable {A : Type*}

/-- Applying the actual convolution operator to δ₁ recovers every coefficient. -/
theorem regular_delta_apply (f : MonoidAlgebra ℂ (FreeGroup A)) (x : FreeGroup A) :
    regular f delta x = f.coeff x := by
  simp only [regular, MonoidAlgebra.lift_apply, Finsupp.sum, sum_apply, smul_apply,
    leftRegularHom]
  simp only [lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply]
  simp [inv_mul_eq_one, eq_comm, Finsupp.mem_support_iff]

theorem realRegular_delta_apply (f : MonoidAlgebra ℝ (FreeGroup A)) (x : FreeGroup A) :
    realRegular f delta x = (f.coeff x : ℂ) := by
  simp only [realRegular, MonoidAlgebra.lift_apply, Finsupp.sum, sum_apply, smul_apply,
    leftRegularHom]
  simp only [lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply]
  simp [inv_mul_eq_one, eq_comm, Finsupp.mem_support_iff]
  intro h
  simp [← h]

theorem regular_single_delta (g : FreeGroup A) :
    regular (MonoidAlgebra.single g 1) delta = lp.single 2 g 1 := by
  ext x
  rw [regular_delta_apply]
  by_cases hx : x = g <;> simp [MonoidAlgebra.coeff_single, lp.single_apply, hx]

theorem regular_delta_orthonormal :
    Orthonormal ℂ (fun g : FreeGroup A => regular (MonoidAlgebra.single g 1) delta) := by
  rw [orthonormal_iff_ite]
  intro g h
  simp only [regular_single_delta]
  by_cases hgh : g = h
  · subst h
    simp [inner_self_eq_norm_sq_to_K, lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2)]
  · rw [ite_eq_right hgh]
    apply squareSpace_inner_zero
    intro x
    by_cases hx : x = g
    · right
      have hx' : x ≠ h := by simpa [hx] using hgh
      simp [lp.single_apply, hx']
    · left; simp [lp.single_apply, hx]

/-- Coefficient domination implies the ℓ² inequality; no comparison between
operator norms in distinct representations is used. -/
theorem regular_delta_norm_le {f : MonoidAlgebra ℂ (FreeGroup A)}
    {a : MonoidAlgebra ℝ (FreeGroup A)} (h : ∀ x, ‖f.coeff x‖ ≤ a.coeff x) :
    ‖regular f delta‖ ≤ ‖realRegular a delta‖ := by
  apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
  intro x
  rw [regular_delta_apply, realRegular_delta_apply, Complex.norm_real]
  exact (h x).trans (le_abs_self _)

/-- Actual coefficient-vector power estimate. -/
theorem realRegular_pow_delta_norm_le (a : MonoidAlgebra ℝ (FreeGroup A)) (d : ℕ) :
    ‖realRegular (a ^ d) delta‖ ≤ ‖realRegular a‖ ^ d := by
  rw [map_pow]
  induction d with
  | zero => simp
  | succ d ih =>
    rw [pow_succ', pow_succ']
    exact (ContinuousLinearMap.le_opNorm (realRegular a) _).trans
      (mul_le_mul_of_nonneg_left ih (norm_nonneg _))

end FreeConvolution

end

/-! The finite coefficient L² identity from orthonormality of reduced-word images. -/
section
open scoped BigOperators InnerProductSpace
variable {G E : Type*} [Monoid G] [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Linear images of a group-ring sum are its literal finite coefficient combination. -/
theorem groupRing_linear_combination (Ψ : MonoidAlgebra ℂ G →ₗ[ℂ] E)
    (f : MonoidAlgebra ℂ G) :
    Ψ f = ∑ g ∈ f.coeff.support, f.coeff g • Ψ (MonoidAlgebra.single g 1) := by
  conv_lhs => rw [← MonoidAlgebra.sum_coeff_single f]
  simp only [Finsupp.sum, map_sum]
  apply Finset.sum_congr rfl
  intro g _
  rw [← map_smul]
  congr 1
  simp

/-- The source's coefficient isometry from actual orthonormal word images. -/
theorem groupRing_coefficient_isometry (Ψ : MonoidAlgebra ℂ G →ₗ[ℂ] E)
    (hΨ : Orthonormal ℂ (fun g => Ψ (MonoidAlgebra.single g 1)))
    (f : MonoidAlgebra ℂ G) :
    ‖Ψ f‖ ^ 2 = ∑ g ∈ f.coeff.support, ‖f.coeff g‖ ^ 2 := by
  rw [groupRing_linear_combination Ψ f, ← inner_self_eq_norm_sq (𝕜 := ℂ), hΨ.inner_sum]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro g _
  rw [mul_comm]
  exact inner_self_eq_norm_sq (𝕜 := ℂ) (f.coeff g)

/-- Two orthonormal realizations have exactly the same coefficient norm. -/
theorem groupRing_norm_eq_of_orthonormal {E' : Type*} [NormedAddCommGroup E']
    [InnerProductSpace ℂ E'] (Ψ : MonoidAlgebra ℂ G →ₗ[ℂ] E)
    (Θ : MonoidAlgebra ℂ G →ₗ[ℂ] E')
    (hΨ : Orthonormal ℂ (fun g => Ψ (MonoidAlgebra.single g 1)))
    (hΘ : Orthonormal ℂ (fun g => Θ (MonoidAlgebra.single g 1)))
    (f : MonoidAlgebra ℂ G) : ‖Ψ f‖ = ‖Θ f‖ := by
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    ((groupRing_coefficient_isometry Ψ hΨ f).trans
      (groupRing_coefficient_isometry Θ hΘ f).symm)

end

/-! Multiplicity-weighted length-one convolution bounds. -/
open scoped BigOperators
open Generator.FreeConvolution

/-- The exact collected multiplicities imply the required square-coefficient budget. -/
theorem prefixWeight_square_sum_le (n : ℕ) (hn : 0 < n) (α : ℝ) :
    ∑ a ∈ prefixLetterSupport n, ‖(prefixWeight n α a : ℂ)‖ ^ 2 ≤ α ^ 2 := by
  have hm : ∑ p ∈ ratioLabels n, (multiplicity n p : ℝ) ^ 2 ≤ 2 * (n : ℝ) ^ 2 := by
    have hNat : ∑ p ∈ ratioLabels n, multiplicity n p ^ 2 ≤ 2 * n ^ 2 := by
      rw [multiplicity_square_sum]
      exact Nat.sub_le _ _
    exact_mod_cast hNat
  have he : (∑ a ∈ prefixLetterSupport n, ‖(prefixWeight n α a : ℂ)‖ ^ 2) =
      2 * (α / (2 * n)) ^ 2 * ∑ p ∈ ratioLabels n, (multiplicity n p : ℝ) ^ 2 := by
    unfold prefixLetterSupport
    rw [Finset.product_eq_sprod, Finset.sum_product]
    simp only [prefixWeight, Complex.norm_real,
      Real.norm_eq_abs, sq_abs, mul_pow]
    simp only [Fintype.sum_bool]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    ring
  rw [he]
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  calc
    _ ≤ 2 * (α / (2 * n)) ^ 2 * (2 * (n : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left hm (by positivity)
    _ = α ^ 2 := by field_simp [hn']

/-- The manuscript's actual coefficient family has convolution norm at most 2α. -/
theorem prefix_convolution_operator_bound (n : ℕ) (hn : 0 < n)
    (α : ℝ) (hα : 0 ≤ α) :
    ‖∑ a ∈ prefixLetterSupport n, (prefixWeight n α a : ℂ) • leftRegular (letter a)‖ ≤
      2 * α := by
  calc
    _ ≤ 2 * Real.sqrt (∑ a ∈ prefixLetterSupport n, ‖(prefixWeight n α a : ℂ)‖ ^ 2) :=
      length_one_convolution_operator_bound _ _
    _ ≤ 2 * Real.sqrt (α ^ 2) := by
      gcongr
      exact prefixWeight_square_sum_le n hn α
    _ = _ := by rw [Real.sqrt_sq hα]

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_QuotientRepresentation
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.TraceUnitary.instMetricSpace _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.relativeTraceSpace_complete _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Complete operator-norm bounded sequences and their contractive map to the
actual quotient trace Hilbert space. This map is not asserted injective. -/
open Filter
open scoped Topology
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

/-- Literal ultralimit inner product, including the complex orientation. -/
theorem sequence_inner_tendsto (a b : Sequences M) :
    Tendsto (fun n => τ.trace (star (a n)*b n)) (ω : Filter ℕ)
      (𝓝 (inner ℂ (sequenceInclusion τ ω a) (sequenceInclusion τ ω b))) := by
  rw [sequenceInclusion_apply, sequenceInclusion_apply, inclusion_inner]
  exact traceRep_tendsto τ ω (star (boundedMap a)*boundedMap b)

end

/-! The faithful constant embedding into the tracial quotient, with its trace and trace norm, for every ultrafilter. -/
open Filter
open scoped Topology

/-! Left multiplication by bounded representatives on the completed trace
Hilbert space. The quotient ideal, not an assumed operator action, determines
which representatives induce the same operator. -/
open Filter
open scoped Topology

/-! Faithful concrete Hilbert-space representation of the tracial quotient
star algebra. Weak operator closedness of its image is not claimed here. -/
open Filter
open scoped Topology

/-! The standard completion/continuous-linear-map structures are not new hypotheses. -/

/-! Fixed-index selection for bounded coordinate representatives. -/
open Filter
open scoped Topology
open UltrapowerBridge

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_Words
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

namespace Generator

/-! All alternating word shapes, allowing either algebra at either endpoint. -/

/-! Splitting a reduced word at its first occurrence of a specified generator. -/

/-! Noncommutative ordered row words and coefficient majorization, without commuting-row assumptions. -/
variable {R : Type*} [Semiring R]

/-- Grouping nondecreasing row words by the number of initial first-row letters. -/
theorem orderedWords_cons (a : R) (as : List R) (d : ℕ) :
    orderedWords (a :: as) d =
      ∑ k ∈ Finset.range (d + 1), a ^ k * orderedWords as (d - k) := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [orderedWords, ih]
    conv_rhs => rw [Finset.sum_range_succ']
    simp only [pow_zero, one_mul, Nat.sub_zero, Nat.add_sub_add_right]
    rw [Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    rw [pow_succ', mul_assoc]

variable [PartialOrder R] [IsOrderedRing R]

theorem orderedWords_nonneg (xs : List R) (hx : ∀ a ∈ xs, 0 ≤ a) (d : ℕ) :
    0 ≤ orderedWords xs d := by
  induction d generalizing xs with
  | zero => simp
  | succ d ih =>
    induction xs with
    | nil => simp
    | cons a as iht =>
      rw [orderedWords]
      exact add_nonneg (mul_nonneg (hx a (by simp)) (ih _ hx))
        (iht (fun b hb => hx b (by simp [hb])))

theorem orderedWords_tail_le (a : R) (as : List R)
    (ha : 0 ≤ a) (has : ∀ b ∈ as, 0 ≤ b) (d : ℕ) :
    orderedWords as d ≤ orderedWords (a :: as) d := by
  cases d with
  | zero => simp
  | succ d =>
    rw [orderedWords]
    exact le_add_of_nonneg_left (mul_nonneg ha
      (orderedWords_nonneg _ (by simpa using And.intro ha has) d))

/-- Choosing the first row of a nondecreasing word gives a subset of all choices. -/
theorem orderedWords_step_le (xs : List R) (hx : ∀ a ∈ xs, 0 ≤ a) (d : ℕ) :
    orderedWords xs (d + 1) ≤ xs.sum * orderedWords xs d := by
  induction xs with
  | nil => simp
  | cons a as ih =>
    have ha := hx a (by simp)
    have has : ∀ b ∈ as, 0 ≤ b := fun b hb => hx b (by simp [hb])
    calc
      orderedWords (a :: as) (d + 1) =
          a * orderedWords (a :: as) d + orderedWords as (d + 1) := by rw [orderedWords]
      _ ≤ a * orderedWords (a :: as) d + as.sum * orderedWords as d :=
        add_le_add le_rfl (ih has)
      _ ≤ a * orderedWords (a :: as) d + as.sum * orderedWords (a :: as) d :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left (orderedWords_tail_le a as ha has d)
          (List.sum_nonneg has))
      _ = _ := by rw [List.sum_cons, add_mul]

/-- All-degree bound by the full distributive power, without commuting factors. -/
theorem orderedWords_le_sum_pow (xs : List R) (hx : ∀ a ∈ xs, 0 ≤ a) (d : ℕ) :
    orderedWords xs d ≤ xs.sum ^ d := by
  induction d with
  | zero => simp
  | succ d ih =>
    calc
      _ ≤ xs.sum * orderedWords xs d := orderedWords_step_le xs hx d
      _ ≤ xs.sum * xs.sum ^ d := mul_le_mul_of_nonneg_left ih (List.sum_nonneg hx)
      _ = _ := (pow_succ' _ _).symm

end Generator

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_Exponential
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

namespace Generator

/-! The homogeneous expansion of an ordered exponential product,
with factorial weights and multiplication order retained. -/
noncomputable section
open scoped BigOperators
section Algebra
variable {R : Type*} [Ring R] [Algebra ℝ R]

/-- Transport the finite original-degree polynomial through an algebra map. -/
theorem exponentialDegree_map {S : Type*} [Ring S] [Algebra ℝ S]
    (φ : R →ₐ[ℝ] S) (xs : List R) (d : ℕ) :
    φ (exponentialDegree xs d) = exponentialDegree (xs.map φ) d := by
  induction xs generalizing d with
  | nil => by_cases hd : d = 0 <;> simp [exponentialDegree, hd]
  | cons a as ih => simp [exponentialDegree, ih]

end Algebra

variable {R : Type*} [NormedRing R] [NormedAlgebra ℝ R]

/-- Absolute convergence for fixed row count. This is not the uniform bound. -/
theorem exponentialDegree_summable_norm (xs : List R) :
    Summable (fun d => ‖exponentialDegree xs d‖) := by
  induction xs with
  | nil =>
    have he : (fun d => ‖exponentialDegree ([] : List R) d‖) =
        (fun d : ℕ => if d = 0 then ‖(1 : R)‖ else 0) := by
      funext d
      by_cases hd : d = 0 <;> simp [exponentialDegree, hd]
    rw [he]
    exact (hasSum_ite_eq (0 : ℕ) ‖(1 : R)‖).summable
  | cons a as ih =>
    exact summable_norm_sum_mul_range_of_summable_norm
      (NormedSpace.norm_expSeries_summable' (𝕂 := ℝ) a) ih

variable [CompleteSpace R]

/-- The series sums to the ordered product, without requiring commuting rows. -/
theorem exponentialDegree_hasSum (xs : List R) :
    HasSum (exponentialDegree xs) ((xs.map NormedSpace.exp).prod) := by
  induction xs with
  | nil => simpa [exponentialDegree] using (hasSum_ite_eq (0 : ℕ) (1 : R))
  | cons a as ih =>
    have h := hasSum_sum_range_mul_of_summable_norm
      (NormedSpace.norm_expSeries_summable' (𝕂 := ℝ) a)
      (exponentialDegree_summable_norm as)
    rw [(NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) a).tsum_eq, ih.tsum_eq] at h
    exact h

end

/-! Summation of homogeneous-degree remainder bounds, given the expansion and its coefficient estimates. -/
variable {E : Type*} [NormedAddCommGroup E]

theorem geometric_second_order_remainder {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (f : ℕ → E) {S : E} (hs : HasSum f S)
    (hb : ∀ n : ℕ, ‖f (n + 2)‖ ≤ q ^ (n + 2)) :
    ‖S - f 0 - f 1‖ ≤ q ^ 2 / (1 - q) := by
  have hg : HasSum (fun n : ℕ => q ^ (n + 2)) (q ^ 2 / (1 - q)) := by
    simpa only [pow_add, div_eq_mul_inv, mul_comm] using
      (hasSum_geometric_of_lt_one hq0 hq1).mul_right (q ^ 2)
  have ht : HasSum (fun n : ℕ => f (n + 2)) (S - f 0 - f 1) := by
    simpa [Finset.sum_range_succ, sub_add_eq_sub_sub] using (hasSum_nat_add_iff' 2).mpr hs
  exact ht.norm_le_of_bounded hg hb

/-- The source's 4α²/(1−2α) expression, with precisely 0 < α < 1/2. -/
theorem perturbation_remainder_from_degree_bounds {α : ℝ} (hα : 0 < α) (hhalf : α < 1 / 2)
    (f : ℕ → E) {S : E} (hs : HasSum f S)
    (hb : ∀ n : ℕ, ‖f (n + 2)‖ ≤ (2 * α) ^ (n + 2)) :
    ‖S - f 0 - f 1‖ ≤ 4 * α ^ 2 / (1 - 2 * α) := by
  have h := geometric_second_order_remainder (by linarith : 0 ≤ 2 * α)
    (by linarith : 2 * α < 1) f hs hb
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ring

end Generator

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_LongWords
attribute [-instance] _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.quotientInnerProductSpace _root_.OAI.Generator.Tracial.quotientNormedAddCommGroup _root_.OAI.Generator.predualAlgebraDualNormed _root_.OAI.Generator.predualFunctionals_normed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator

/-! Factorial coefficient majorization in every homogeneous degree. -/
section
open scoped BigOperators
open Generator.CoefficientOrder
variable {G : Type*} [Monoid G]

theorem normCoefficients_sub_le (f g : MonoidAlgebra ℂ G) :
    normCoefficients (f - g) ≤ normCoefficients f + normCoefficients g := by
  intro w
  simpa using norm_sub_le (f.coeff w) (g.coeff w)

theorem normCoefficients_sum_le {I : Type*} (s : Finset I) (f : I → MonoidAlgebra ℂ G) :
    normCoefficients (∑ i ∈ s, f i) ≤ ∑ i ∈ s, normCoefficients (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact le_trans (normCoefficients_add_le _ _) (add_le_add le_rfl ih)

theorem normCoefficients_pow_le (b : MonoidAlgebra ℂ G) (a : MonoidAlgebra ℝ G)
    (ha : 0 ≤ a) (hb : normCoefficients b ≤ a) (d : ℕ) :
    normCoefficients (b ^ d) ≤ a ^ d := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [pow_succ, pow_succ]
    exact le_trans (normCoefficients_mul_le _ _)
      (mul_le_mul ih hb (fun w => normCoefficients_nonnegative b w) (pow_nonneg ha d))

theorem normCoefficients_real_smul (r : ℝ) (hr : 0 ≤ r) (b : MonoidAlgebra ℂ G) :
    normCoefficients (r • b) = r • normCoefficients b := by
  ext w
  simp [Real.norm_eq_abs, abs_of_nonneg hr]

/-- Original-degree factorial terms are bounded by nondecreasing row words. -/
theorem exponentialDegree_le_orderedWords
    (rows : List (MonoidAlgebra ℂ G × MonoidAlgebra ℝ G))
    (h : ∀ row ∈ rows, 0 ≤ row.2 ∧ normCoefficients row.1 ≤ row.2) (d : ℕ) :
    normCoefficients (exponentialDegree (rows.map Prod.fst) d) ≤
      orderedWords (rows.map Prod.snd) d := by
  induction rows generalizing d with
  | nil =>
    cases d <;> simp [exponentialDegree]
  | cons row rows ih =>
    have hr := h row (by simp)
    have ht : ∀ r ∈ rows, 0 ≤ r.2 ∧ normCoefficients r.1 ≤ r.2 :=
      fun r hm => h r (by simp [hm])
    have hp : ∀ a ∈ rows.map Prod.snd, 0 ≤ a := by
      intro a ha
      obtain ⟨r, hm, rfl⟩ := List.mem_map.mp ha
      exact (ht r hm).1
    simp only [List.map_cons, exponentialDegree]
    rw [orderedWords_cons]
    apply (normCoefficients_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro k _
    have hw0 : 0 ≤ (k.factorial : ℝ)⁻¹ := by positivity
    have hw1 : (k.factorial : ℝ)⁻¹ ≤ 1 := by
      apply inv_le_one_of_one_le₀
      exact_mod_cast Nat.factorial_pos k
    have hpow := normCoefficients_pow_le row.1 row.2 hr.1 hr.2 k
    have hfactor : normCoefficients ((k.factorial : ℝ)⁻¹ • row.1 ^ k) ≤ row.2 ^ k := by
      rw [normCoefficients_real_smul _ hw0]
      intro w
      change (k.factorial : ℝ)⁻¹ * ‖(row.1 ^ k).coeff w‖ ≤ (row.2 ^ k).coeff w
      exact (mul_le_mul_of_nonneg_left (hpow w) hw0).trans
        (by simpa using mul_le_mul_of_nonneg_right hw1 ((pow_nonneg hr.1 k) w))
    exact le_trans (normCoefficients_mul_le _ _)
      (mul_le_mul hfactor (ih ht (d - k))
        (fun w => normCoefficients_nonnegative _ w) (pow_nonneg hr.1 k))

/-- The source's full coefficient inequality, for arbitrary monoids and all d.
The sum on the right is the actual collected convolution power. -/
theorem exponentialDegree_coefficient_majorization
    (rows : List (MonoidAlgebra ℂ G × MonoidAlgebra ℝ G))
    (h : ∀ row ∈ rows, 0 ≤ row.2 ∧ normCoefficients row.1 ≤ row.2) (d : ℕ) :
    normCoefficients (exponentialDegree (rows.map Prod.fst) d) ≤
      (rows.map Prod.snd).sum ^ d := by
  apply (exponentialDegree_le_orderedWords rows h d).trans
  apply orderedWords_le_sum_pow
  intro a ha
  obtain ⟨r, hm, rfl⟩ := List.mem_map.mp ha
  exact (h r hm).1

end

/-! The nonlinear remainder of the actual ordered convolution-operator
exponentials, evaluated at δ₁, without assumed degree estimates. -/
section
open scoped BigOperators
open Generator.CoefficientOrder Generator.FreeConvolution
variable {A : Type*}

/-- All original-degree bounds follow from coefficient majorization and the
norm of the positive total convolution operator. -/
theorem free_exponentialDegree_bound
    (rows : List (MonoidAlgebra ℂ (FreeGroup A) × MonoidAlgebra ℝ (FreeGroup A)))
    (h : ∀ row ∈ rows, 0 ≤ row.2 ∧ normCoefficients row.1 ≤ row.2) (d : ℕ) :
    ‖regular (exponentialDegree (rows.map Prod.fst) d) delta‖ ≤
      ‖realRegular (rows.map Prod.snd).sum‖ ^ d := by
  exact (regular_delta_norm_le (exponentialDegree_coefficient_majorization rows h d)).trans
    (realRegular_pow_delta_norm_le _ d)

end

/-! Signed rows B_k and positive rows A_k with free basis indexed by prefix ratios in FreeGroup Nat. -/
section
open scoped BigOperators
open Generator.CoefficientOrder Generator.FreeConvolution
local notation "G" => FreeGroup ℕ
local notation "F" => FreeGroup G

attribute [local instance] OAI.Generator.instDecidableEqFreeGroupNat_solutions_1
attribute [local instance] OAI.Generator.instDecidableEqFreeGroupNat_solutions_2
theorem positiveLetterPair_nonnegative (p : G) : 0 ≤ positiveLetterPair p := by
  intro w
  simp only [positiveLetterPair, MonoidAlgebra.coeff_add, Finsupp.add_apply,
    MonoidAlgebra.coeff_single, Finsupp.single_apply]
  split_ifs <;> norm_num

theorem negativeLetterPair_dominated (p : G) :
    normCoefficients (negativeLetterPair p) ≤ positiveLetterPair p := by
  simpa [negativeLetterPair, positiveLetterPair] using
    normCoefficients_sub_le (MonoidAlgebra.single (letter (p, true)) 1)
      (MonoidAlgebra.single (letter (p, false)) 1)

/-- Positivity and domination are proved for the source rows, not assumed. -/
theorem perturbationRows_dominated (n : ℕ) (α : ℝ) (hα : 0 ≤ α) :
    ∀ row ∈ perturbationRows n α, 0 ≤ row.2 ∧ normCoefficients row.1 ≤ row.2 := by
  intro row hr
  obtain ⟨k, rfl⟩ := List.mem_ofFn.mp (show row ∈ List.ofFn (perturbationRow (n := n) α) from hr)
  have hc : 0 ≤ α / (2 * n) := by positivity
  have hp : 0 ≤ ∑ j : Fin n, positiveLetterPair (pairRatio (k, j)) :=
    Finset.sum_nonneg (fun j _ => positiveLetterPair_nonnegative _)
  constructor
  · intro w
    change 0 ≤ α / (2 * n) * (∑ j : Fin n, positiveLetterPair (pairRatio (k, j))).coeff w
    exact mul_nonneg hc (hp w)
  · change normCoefficients ((α / (2 * n)) • _) ≤ (α / (2 * n)) • _
    rw [normCoefficients_real_smul _ hc]
    have hb : normCoefficients (∑ j : Fin n, negativeLetterPair (pairRatio (k, j))) ≤
        ∑ j : Fin n, positiveLetterPair (pairRatio (k, j)) :=
      (normCoefficients_sum_le _ _).trans
        (Finset.sum_le_sum (fun j _ => negativeLetterPair_dominated _))
    intro w
    exact mul_le_mul_of_nonneg_left (hb w) hc

/-- Exact regrouping of the ordered-pair sum using the proved fiber counts. -/
theorem pairRatio_sum_multiplicity {R : Type*} [AddCommMonoid R]
    (n : ℕ) (hn : 0 < n) (f : G → R) :
    (∑ k : Fin n, ∑ j : Fin n, f (pairRatio (k, j))) =
      ∑ p ∈ ratioLabels n, multiplicity n p • f p := by
  have hm : ∀ ij ∈ (Finset.univ : Finset (Fin n × Fin n)), pairRatio ij ∈ ratioLabels n := by
    intro ij _
    rw [ratioLabels_eq_image hn]
    exact Finset.mem_image.mpr ⟨ij, Finset.mem_univ _, rfl⟩
  have h := Finset.sum_fiberwise_of_maps_to' hm f
  simpa [multiplicity, Fintype.sum_prod_type] using h.symm

/-- The sum of the source's positive rows is exactly its collected coefficient
family, including the n copies of the identity prefix ratio. -/
theorem perturbationRows_positive_total (n : ℕ) (hn : 0 < n) (α : ℝ) :
    (perturbationRows n α |>.map Prod.snd).sum =
      (α / (2 * n)) • ∑ p ∈ ratioLabels n, multiplicity n p • positiveLetterPair p := by
  simp only [perturbationRows, List.map_ofFn, List.sum_ofFn, Function.comp_def, perturbationRow]
  rw [← Finset.smul_sum, pairRatio_sum_multiplicity n hn]

/-- Identification of λ(A) with the signed-letter operator already bounded. -/
theorem perturbationRows_total_operator (n : ℕ) (hn : 0 < n) (α : ℝ) :
    realRegular (perturbationRows n α |>.map Prod.snd).sum =
      ∑ a ∈ prefixLetterSupport n, (prefixWeight n α a : ℂ) • leftRegular (letter a) := by
  rw [perturbationRows_positive_total n hn]
  simp only [map_smul, map_sum, map_nsmul, Finset.smul_sum]
  simp only [prefixLetterSupport, Finset.product_eq_sprod, prefixWeight,
    Finset.sum_product, Fintype.sum_bool]
  apply Finset.sum_congr rfl
  intro p _
  simp [positiveLetterPair, realRegular, MonoidAlgebra.lift_single, leftRegularHom,
    smul_add]
  simp only [← nsmul_eq_mul, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  norm_cast

/-- Uniform all-degree bound for the manuscript's literal formal rows. -/
theorem perturbationRows_degree_bound (n : ℕ) (hn : 0 < n)
    (α : ℝ) (hα : 0 ≤ α) (d : ℕ) :
    ‖regular (exponentialDegree (perturbationRows n α |>.map Prod.fst) d) delta‖ ≤
      (2 * α) ^ d := by
  apply (free_exponentialDegree_bound _ (perturbationRows_dominated n α hα) d).trans
  apply pow_le_pow_left₀ (norm_nonneg _)
  rw [perturbationRows_total_operator n hn]
  exact prefix_convolution_operator_bound n hn α hα

end

/-! Transfer of the nonlinear estimate to an algebra with a continuous Hilbert
realization and orthonormal reduced-word images, without an independence hypothesis. -/

/-! The exact finite free basis and its injective realization in a countable free basis. -/
section
open scoped BigOperators
open Generator.FreeConvolution
local notation "G" => FreeGroup ℕ

local instance instDecidableEqFreeGroupNat_solutions_3_rcb19d2_1 : DecidableEq G := Classical.decEq _
theorem prefixWordEmbedding_injective (n : ℕ) : Function.Injective (prefixWordEmbedding n) :=
  FreeGroup.map_injective Subtype.val_injective

theorem finitePerturbationRows_embed (n : ℕ) (α : ℝ) :
    (finitePerturbationRows n α).map (prefixRingEmbedding n) =
      (perturbationRows n α).map Prod.fst := by
  simp [finitePerturbationRows, perturbationRows, List.map_ofFn, Function.comp_def]

theorem embeddedCoefficientMap_orthonormal (n : ℕ) :
    Orthonormal ℂ (fun g => embeddedCoefficientMap n (MonoidAlgebra.single g 1)) := by
  have h := regular_delta_orthonormal.comp (prefixWordEmbedding n) (prefixWordEmbedding_injective n)
  simpa [embeddedCoefficientMap, LinearMap.comp_apply, Function.comp_def] using h

/-- All-degree estimate on the exact finite formal group F_S. -/
theorem finitePerturbationRows_degree_bound (n : ℕ) (hn : 0 < n)
    (α : ℝ) (hα : 0 ≤ α) (d : ℕ) :
    ‖embeddedCoefficientMap n (exponentialDegree (finitePerturbationRows n α) d)‖ ≤
      (2 * α) ^ d := by
  change ‖regular (prefixRingEmbedding n (exponentialDegree (finitePerturbationRows n α) d)) delta‖ ≤ _
  have hmap := exponentialDegree_map ((prefixRingEmbedding n).restrictScalars ℝ)
    (finitePerturbationRows n α) d
  change prefixRingEmbedding n (exponentialDegree (finitePerturbationRows n α) d) =
    exponentialDegree ((finitePerturbationRows n α).map (prefixRingEmbedding n)) d at hmap
  rw [hmap, finitePerturbationRows_embed]
  exact perturbationRows_degree_bound n hn α hα d

end

/-! Exact finite-basis version of the source's nonlinear estimate. Unlike the
ambient transport lemma, only reduced words in F_S occur in the hypothesis. -/
open scoped BigOperators InnerProductSpace
variable {B E : Type*} [NormedRing B] [NormedAlgebra ℂ B] [CompleteSpace B]
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Remainder bounds in a continuous Hilbert realization of the finite free group with orthonormal word images. -/
theorem finite_prefix_remainder_transfer (n : ℕ) (hn : 0 < n)
    (Φ : MonoidAlgebra ℂ (FreeGroup (PrefixLabel n)) →ₐ[ℂ] B) (ι : B →L[ℂ] E)
    (horth : Orthonormal ℂ (fun g => ι (Φ (MonoidAlgebra.single g 1))))
    (α : ℝ) (hα : 0 < α) (hhalf : α < 1 / 2) :
    ‖ι ((finitePerturbationRows n α |>.map (fun r => NormedSpace.exp (Φ r))).prod -
      1 - (finitePerturbationRows n α |>.map Φ).sum)‖ ≤
        4 * α ^ 2 / (1 - 2 * α) := by
  let xs : List B := (finitePerturbationRows n α).map Φ
  let coeff : ℕ → E := fun d => ι (exponentialDegree xs d)
  have hsum : HasSum coeff (ι (xs.map NormedSpace.exp).prod) :=
    (exponentialDegree_hasSum xs).map ι.toAddMonoidHom ι.continuous
  have hid (d : ℕ) : exponentialDegree xs d =
      Φ (exponentialDegree (finitePerturbationRows n α) d) := by
    exact (exponentialDegree_map (Φ.restrictScalars ℝ) _ d).symm
  have hdegree (d : ℕ) : ‖coeff d‖ ≤ (2 * α) ^ d := by
    change ‖ι (exponentialDegree xs d)‖ ≤ _
    rw [hid]
    have hiso := groupRing_norm_eq_of_orthonormal (ι.toLinearMap.comp Φ.toLinearMap)
      (embeddedCoefficientMap n) horth (embeddedCoefficientMap_orthonormal n)
      (exponentialDegree (finitePerturbationRows n α) d)
    change ‖ι (Φ (exponentialDegree (finitePerturbationRows n α) d))‖ = _ at hiso
    rw [hiso]
    exact finitePerturbationRows_degree_bound n hn α hα.le d
  have ht := perturbation_remainder_from_degree_bounds hα hhalf coeff hsum
    (fun k => hdegree (k + 2))
  simpa [coeff, xs, List.map_map, Function.comp_def, map_sub] using ht

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_CoordinatePerturbation
attribute [-instance] _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.projectionOrbitClosure_complete _root_.OAI.Generator.Tracial.relativeTraceSpace_complete _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Group-ring maps from actual bounded unitary coordinates, with quotient
transport and coordinate Gram limits. -/

/-! Prefix labels and conjugate-word Gram identities for free-group perturbations. -/

section

/-! The finite-prefix analytic bound in the actual bounded-sequence/tracial
quotient realization. Word moments remain explicit premises: no free-Haar
existence or perturbation construction is asserted by this transport theorem. -/
open Filter
open scoped Topology
attribute [local instance] Classical.propDecidable Classical.decEq
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

theorem orthonormal_of_coordinate_moments {G : Type*} [Monoid G]
    (Φ : MonoidAlgebra ℂ G →ₐ[ℂ] Sequences M)
    (hmom : ∀ g h : G,
      Tendsto (fun k => τ.trace (star (Φ (MonoidAlgebra.single g 1) k)*
        Φ (MonoidAlgebra.single h 1) k)) (ω : Filter ℕ)
        (𝓝 (if g = h then 1 else 0))) :
    Orthonormal ℂ (fun g => sequenceInclusion τ ω (Φ (MonoidAlgebra.single g 1))) := by
  classical
  rw [orthonormal_iff_ite]
  intro g h
  exact tendsto_nhds_unique (sequence_inner_tendsto τ ω
    (Φ (MonoidAlgebra.single g 1)) (Φ (MonoidAlgebra.single h 1))) (hmom g h)

/-- The actual quotient two-norm estimate from coordinate word moments. -/
theorem tracial_remainder_of_coordinate_moments_oai (n : ℕ) (hn : 0 < n)
    (Φ : MonoidAlgebra ℂ (FreeGroup (PrefixLabel n)) →ₐ[ℂ] Sequences M)
    (hmom : ∀ g h : FreeGroup (PrefixLabel n),
      Tendsto (fun k => τ.trace (star (Φ (MonoidAlgebra.single g 1) k)*
        Φ (MonoidAlgebra.single h 1) k)) (ω : Filter ℕ)
        (𝓝 (if g = h then 1 else 0)))
    (α : ℝ) (hα : 0 < α) (hhalf : α < 1/2) :
    ‖sequenceQuotient τ ω (remainderSequence n α Φ)‖ ≤ 4*α^2/(1-2*α) := by
  have h := finite_prefix_remainder_transfer (B := Sequences M) (E := L2 τ ω) n hn Φ (sequenceInclusion τ ω)
    (orthonormal_of_coordinate_moments τ ω Φ (by
      intro g h
      by_cases hgh : g = h
      · simpa only [ite_eq_left hgh] using hmom g h
      · simpa only [ite_eq_right hgh] using hmom g h)) α hα hhalf
  simpa only [remainderSequence, sequenceInclusion_apply, LinearIsometry.norm_map] using h

end

/-! The literal bounded coordinate model of the finite-prefix free group.
The t_j sequences are the witnesses retained by the successive construction. -/

/-! The one literal bounded skew-adjoint perturbation K = i h. Every formal
row is its conjugate by the corresponding actual coordinate prefix. -/
attribute [local instance] Classical.propDecidable Classical.decEq
open UltrapowerBridge
open scoped BigOperators

end Generator.Tracial

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Generator.Tracial.tracial_remainder_of_coordinate_moments_oai.{u_1} := @OAI.Generator.Tracial.tracial_remainder_of_coordinate_moments_oai.{u_1}
