-- Prove2me | solution 1 for OAI.TwoPointCorrelations.ModFiveThetaInput.eventually_canonical_retained_mass
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T01:43:33.872864+00:00
-- url     : https://prove2.me/submissions/5415c1b5-aa30-4f55-9b40-033fc52a7eed

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

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


lemma average_sum (μ : FiniteLaw α) (f : ι → α → ℝ) :
    μ.average (fun x => ∑ i, f i x) = ∑ i, μ.average (f i) := by
  simp only [average, mul_sum]
  rw [sum_comm]

lemma average_mul_const (μ : FiniteLaw α) (f : α → ℝ) (c : ℝ) :
    μ.average (fun x => f x * c) = μ.average f * c := by
  simp only [average, mul_assoc, sum_mul]








lemma independent_average_product [DecidableEq ι] (μ : ι → FiniteLaw α) (f : ι → α → ℝ) :
    (independent μ).average (fun x => ∏ i, f i (x i)) = ∏ i, (μ i).average (f i) := by
  simp only [average, independent, ← prod_mul_distrib]
  exact (Fintype.prod_sum (fun i x => (μ i).weight x * f i x)).symm


lemma probability_le_one (μ : FiniteLaw α) (E : α → Prop) : μ.probability E ≤ 1 := by
  classical
  apply (μ.average_mono (g := fun _ => 1) ?_).trans_eq (μ.average_const 1)
  intro x
  split_ifs <;> norm_num


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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PaddingTilt
namespace OAI

/-! The literal `5^omega` tilt of independent divisibility indicators gives
exactly the prime availability law used in the padding anti-concentration. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical






lemma paddingTiltNormalizer_pos (Q : Finset ℕ) : 0 < paddingTiltNormalizer Q := by
  apply prod_pos
  intro p _
  positivity










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









lemma modFiveTheta_eq_sum (one : Bool) (x : ℝ) :
    modFiveTheta one x = ∑ p ∈ modFivePrimesUpTo one x, Real.log p := by
  simp [modFiveTheta, modFivePrimesUpTo, modFiveLogWeight, sum_filter]





lemma log_nat_nonneg (p : ℕ) : 0 ≤ Real.log (p : ℝ) := by
  by_cases hp : p = 0
  · simp [hp]
  · exact Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hp)

/-- The entire cost of removing a finite exceptional prime set is explicit. -/
lemma deletedModFiveTheta_error (E : Finset ℕ) (one : Bool) (x : ℝ) :
    |deletedModFiveTheta E one x - modFiveTheta one x| ≤
      ∑ p ∈ E, Real.log p := by
  rw [modFiveTheta_eq_sum]
  have he : deletedModFiveTheta E one x -
      (∑ p ∈ modFivePrimesUpTo one x, Real.log p) =
      -(∑ p ∈ modFivePrimesUpTo one x ∩ E, Real.log p) := by
    unfold deletedModFiveTheta deletedModFivePrimes
    have hs := sum_sdiff (f := fun p : ℕ => Real.log (p : ℝ))
      (inter_subset_left : modFivePrimesUpTo one x ∩ E ⊆ modFivePrimesUpTo one x)
    rw [sdiff_inter_self_left] at hs
    linarith
  rw [he, abs_neg, abs_of_nonneg (sum_nonneg (fun p _ => log_nat_nonneg p))]
  exact sum_le_sum_of_subset_of_nonneg inter_subset_right (fun p _ _ => log_nat_nonneg p)


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PrimePartialSummation
namespace OAI

/-! Exact partial summation, with the prime-count error retained inside the
integral. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.Classical


theorem centered_partial_summation (c : ℕ → ℝ) (α a b : ℝ) (ha : 0 ≤ a)
    (hab : a ≤ b) (f : ℝ → ℝ)
    (hf : ∀ x ∈ Set.Icc a b, DifferentiableAt ℝ f x)
    (hdf : ContinuousOn (deriv f) (Set.Icc a b)) :
    (∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, f n * c n) - α * (∫ t in a..b, f t) =
      f b * (partialCoefficientSum c b - α * b) -
      f a * (partialCoefficientSum c a - α * a) -
      ∫ t in a..b, deriv f t * (partialCoefficientSum c t - α * t) := by
  have hfc : ContinuousOn f (Set.Icc a b) :=
    fun x hx => (hf x hx).continuousAt.continuousWithinAt
  have hfi : IntervalIntegrable f volume a b := hfc.intervalIntegrable_of_Icc hab
  have hdfi : IntervalIntegrable (deriv f) volume a b :=
    hdf.intervalIntegrable_of_Icc hab
  have hdmain : IntervalIntegrable (fun t => deriv f t * t) volume a b :=
    hdfi.mul_continuousOn continuous_id.continuousOn
  have hsum : IntervalIntegrable
      (fun t => deriv f t * partialCoefficientSum c t) volume a b := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
    exact integrableOn_mul_sum_Icc c ha
      (hdf.integrableOn_Icc)
  have hAbel := sum_mul_eq_sub_sub_integral_mul c ha hab hf hdf.integrableOn_Icc
  rw [← intervalIntegral.integral_of_le hab] at hAbel
  change (∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, f n * c n) =
    f b * partialCoefficientSum c b - f a * partialCoefficientSum c a -
      ∫ t in a..b, deriv f t * partialCoefficientSum c t at hAbel
  have hparts := intervalIntegral.integral_deriv_mul_eq_sub
    (fun x hx => (hf x (by simpa [Set.uIcc_of_le hab] using hx)).hasDerivAt)
    (fun x (_ : x ∈ Set.uIcc a b) => hasDerivAt_id x) hdfi intervalIntegrable_const
  simp only [id_eq] at hparts
  have hsplit : (∫ t in a..b, deriv f t * t + f t * 1) =
      (∫ t in a..b, deriv f t * t) + ∫ t in a..b, f t := by
    simp only [mul_one]
    exact intervalIntegral.integral_add hdmain hfi
  rw [hsplit] at hparts
  have herr : (∫ t in a..b, deriv f t * (partialCoefficientSum c t - α * t)) =
      (∫ t in a..b, deriv f t * partialCoefficientSum c t) -
        α * (∫ t in a..b, deriv f t * t) := by
    simp only [mul_sub, show ∀ t, deriv f t * (α * t) = α * (deriv f t * t) by
      intro t; ring]
    rw [intervalIntegral.integral_sub hsum (hdmain.const_mul α),
      intervalIntegral.integral_const_mul]
  rw [herr, hAbel]
  linear_combination -α * hparts


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ThetaLogError
namespace OAI

/-! An integrable logarithmic error bound obtained from the stated exponential
prime-number error. It also pays exactly for finite exceptional prime sets. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma exp_neg_sqrt_log_le (c x : ℝ) (hc : 0 < c) (hx : 1 < x) :
    Real.exp (-c * Real.sqrt (Real.log x)) ≤ 24 / (c ^ 4 * Real.log x ^ 2) := by
  have hl : 0 < Real.log x := Real.log_pos hx
  have hsq := Real.sq_sqrt hl.le
  have hpow : (c * Real.sqrt (Real.log x)) ^ 4 = c ^ 4 * Real.log x ^ 2 := by
    calc
      _ = c ^ 4 * ((Real.sqrt (Real.log x)) ^ 2) ^ 2 := by ring
      _ = _ := by rw [hsq]
  have he := Real.pow_div_factorial_le_exp (c * Real.sqrt (Real.log x))
    (mul_nonneg hc.le (Real.sqrt_nonneg (Real.log x))) 4
  norm_num at he
  rw [hpow] at he
  have hmul := mul_le_mul_of_nonneg_right he
    (Real.exp_pos (-c * Real.sqrt (Real.log x))).le
  have hexp : Real.exp (c * Real.sqrt (Real.log x)) *
      Real.exp (-c * Real.sqrt (Real.log x)) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    exact Real.exp_zero
  rw [hexp] at hmul
  apply (le_div_iff₀ (by positivity : 0 < c ^ 4 * Real.log x ^ 2)).mpr
  nlinarith [hmul]

lemma log_sq_le_two_mul (x : ℝ) (hx : 1 ≤ x) : Real.log x ^ 2 ≤ 2 * x := by
  have hh := Real.pow_div_factorial_le_exp (Real.log x) (Real.log_nonneg hx) 2
  norm_num at hh
  rw [Real.exp_log (zero_lt_one.trans_le hx)] at hh
  linarith

/-- A single constant controls the logarithmic PNT error for both residue
selections and every real endpoint at least two. -/
theorem ModFiveThetaInput.log_error (hP : ModFiveThetaInput) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (one : Bool) (x : ℝ), 2 ≤ x →
      |modFiveTheta one x - modFiveDensity one * x| ≤ K * x / Real.log x ^ 2 := by
  obtain ⟨c, C, hc, hC, h⟩ := hP
  refine ⟨24 * C / c ^ 4, by positivity, fun one x hx => ?_⟩
  apply (h one x hx).trans
  have hh := mul_le_mul_of_nonneg_left (exp_neg_sqrt_log_le c x hc (by linarith))
    (mul_nonneg hC (by linarith : 0 ≤ x))
  convert (preTransparency := .instances) hh using 1
  ring

theorem ModFiveThetaInput.deleted_log_error (hP : ModFiveThetaInput) (E : Finset ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (one : Bool) (x : ℝ), 2 ≤ x →
      |deletedModFiveTheta E one x - modFiveDensity one * x| ≤
        K * x / Real.log x ^ 2 := by
  obtain ⟨K, hK, h⟩ := hP.log_error
  let D : ℝ := ∑ p ∈ E, Real.log p
  have hD : 0 ≤ D := sum_nonneg (fun p _ => log_nat_nonneg p)
  refine ⟨K + 2 * D, by positivity, fun one x hx => ?_⟩
  have hl : 0 < Real.log x := Real.log_pos (by linarith)
  have hd : D ≤ 2 * D * x / Real.log x ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hl)).mpr
    have hh := mul_le_mul_of_nonneg_left (log_sq_le_two_mul x (by linarith)) hD
    nlinarith [hh]
  calc
    _ ≤ |modFiveTheta one x - modFiveDensity one * x| + D := by
      calc
        _ = |(modFiveTheta one x - modFiveDensity one * x) +
            (deletedModFiveTheta E one x - modFiveTheta one x)| := by congr 1; ring
        _ ≤ _ := abs_add_le _ _
        _ ≤ _ := add_le_add (le_refl _) (deletedModFiveTheta_error E one x)
    _ ≤ K * x / Real.log x ^ 2 + 2 * D * x / Real.log x ^ 2 :=
      add_le_add (h one x hx) hd
    _ = _ := by ring

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ReciprocalPrimeBands
namespace OAI

/-! Quantitative reciprocal-prime bands from the actual theta error.
Partial summation gives the reciprocal-prime estimates. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.Classical


lemma reciprocalLog_hasDerivAt {x : ℝ} (hx : 1 < x) :
    HasDerivAt reciprocalLog
      (-(Real.log x + 1) / (x ^ 2 * Real.log x ^ 2)) x := by
  have hx0 : x ≠ 0 := (zero_lt_one.trans hx).ne'
  have hl0 : Real.log x ≠ 0 := (Real.log_pos hx).ne'
  have hh := (hasDerivAt_inv hx0).div (Real.hasDerivAt_log hx0) hl0
  convert (preTransparency := .instances) hh using 1
  · rfl
  · field_simp
    ring

lemma reciprocalLog_error_le (K x E : ℝ) (hK : 0 ≤ K)
    (hx : 0 < x) (hl : 1 ≤ Real.log x)
    (hE : |E| ≤ K * x / Real.log x ^ 2) :
    |reciprocalLog x * E| ≤ K / Real.log x := by
  have hlp : 0 < Real.log x := zero_lt_one.trans_le hl
  rw [abs_mul, abs_of_nonneg (by unfold reciprocalLog; positivity)]
  calc
    _ ≤ reciprocalLog x * (K * x / Real.log x ^ 2) :=
      mul_le_mul_of_nonneg_left hE (by unfold reciprocalLog; positivity)
    _ = K / Real.log x ^ 3 := by unfold reciprocalLog; field_simp
    _ ≤ K / Real.log x := by
      apply div_le_div_of_nonneg_left hK hlp
      nlinarith [sq_nonneg (Real.log x - 1)]

lemma reciprocalLog_deriv_error_le (K x E : ℝ) (hK : 0 ≤ K)
    (hx : 1 < x) (hl : 1 ≤ Real.log x)
    (hE : |E| ≤ K * x / Real.log x ^ 2) :
    |deriv reciprocalLog x * E| ≤ 2 * K * (x⁻¹ / Real.log x ^ 2) := by
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hlp : 0 < Real.log x := zero_lt_one.trans_le hl
  rw [(reciprocalLog_hasDerivAt hx).deriv, abs_mul, abs_div, abs_neg,
    abs_of_pos (by positivity : 0 < Real.log x + 1),
    abs_of_pos (by positivity : 0 < x ^ 2 * Real.log x ^ 2)]
  calc
    _ ≤ ((Real.log x + 1) / (x ^ 2 * Real.log x ^ 2)) *
        (K * x / Real.log x ^ 2) := mul_le_mul_of_nonneg_left hE (by positivity)
    _ ≤ 2 * K * (x⁻¹ / Real.log x ^ 2) := by
      apply (mul_le_mul_iff_of_pos_right (by positivity : 0 < x * Real.log x ^ 4)).mp
      field_simp
      nlinarith [sq_nonneg (Real.log x - 1), mul_nonneg hK (sq_nonneg (Real.log x - 1))]

/-- A uniform band error. The upper endpoint is arbitrary, so this applies
simultaneously to all the logarithmically spaced supplies in the manuscript. -/
theorem reciprocal_band_error (c : ℕ → ℝ) (α K a b : ℝ) (hK : 0 ≤ K)
    (ha : Real.exp 1 ≤ a) (hab : a ≤ b)
    (hE : ∀ x ∈ Set.Icc a b,
      |partialCoefficientSum c x - α * x| ≤ K * x / Real.log x ^ 2) :
    |(∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, reciprocalLog n * c n) -
      α * (Real.log (Real.log b) - Real.log (Real.log a))| ≤ 4 * K / Real.log a := by
  have ha1 : 1 < a := (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 1)).trans_le ha
  have hb1 : 1 < b := ha1.trans_le hab
  have ha0 : 0 < a := zero_lt_one.trans ha1
  have hla : 1 ≤ Real.log a := by
    simpa using Real.log_le_log (Real.exp_pos 1) ha
  have hlap : 0 < Real.log a := Real.log_pos ha1
  have hx1 (x : ℝ) (hx : x ∈ Set.Icc a b) : 1 < x := ha1.trans_le hx.1
  have hlx (x : ℝ) (hx : x ∈ Set.Icc a b) : 1 ≤ Real.log x :=
    hla.trans (Real.log_le_log ha0 hx.1)
  have hf : ∀ x ∈ Set.Icc a b, DifferentiableAt ℝ reciprocalLog x :=
    fun x hx => (reciprocalLog_hasDerivAt (hx1 x hx)).differentiableAt
  have hxn : ∀ x ∈ Set.Icc a b, x ≠ 0 :=
    fun x hx => (zero_lt_one.trans (hx1 x hx)).ne'
  have hln : ∀ x ∈ Set.Icc a b, Real.log x ≠ 0 :=
    fun x hx => (Real.log_pos (hx1 x hx)).ne'
  have hclog : ContinuousOn Real.log (Set.Icc a b) :=
    fun x hx => (Real.continuousAt_log (hxn x hx)).continuousWithinAt
  have hdf : ContinuousOn (deriv reciprocalLog) (Set.Icc a b) := by
    apply ContinuousOn.congr (f := fun x => -(Real.log x + 1) / (x ^ 2 * Real.log x ^ 2))
    · exact (hclog.add continuousOn_const).neg.div
        ((continuousOn_id.pow 2).mul (hclog.pow 2))
        (fun x hx => mul_ne_zero (pow_ne_zero 2 (hxn x hx)) (pow_ne_zero 2 (hln x hx)))
    · intro x hx
      exact (reciprocalLog_hasDerivAt (hx1 x hx)).deriv
  have hAbel := centered_partial_summation c α a b ha0.le hab reciprocalLog hf hdf
  rw [show (∫ t in a..b, reciprocalLog t) =
      Real.log (Real.log b) - Real.log (Real.log a) from
    integral_inv_div_log ha1 hb1] at hAbel
  have hg : IntervalIntegrable (fun x : ℝ => 2 * K * (x⁻¹ / Real.log x ^ 2)) volume a b := by
    apply ContinuousOn.intervalIntegrable_of_Icc (h := hab)
    exact ((continuousOn_id.inv₀ hxn).div (hclog.pow 2)
      (fun x hx => pow_ne_zero 2 (hln x hx))).const_mul (2 * K)
  have hi : |∫ x in a..b, deriv reciprocalLog x * (partialCoefficientSum c x - α * x)| ≤
      2 * K / Real.log a := by
    have hbound := intervalIntegral.norm_integral_le_of_norm_le hab
      (Filter.Eventually.of_forall (fun x hx => by
        rw [Real.norm_eq_abs]
        exact reciprocalLog_deriv_error_le K x _ hK (hx1 x ⟨hx.1.le, hx.2⟩)
          (hlx x ⟨hx.1.le, hx.2⟩) (hE x ⟨hx.1.le, hx.2⟩))) hg
    rw [Real.norm_eq_abs, intervalIntegral.integral_const_mul,
      integral_inv_div_log_sq ha1 hb1] at hbound
    apply hbound.trans
    have hbnonneg : 0 ≤ (Real.log b)⁻¹ := inv_nonneg.mpr (Real.log_pos hb1).le
    simp only [div_eq_mul_inv]
    nlinarith [mul_nonneg (by positivity : 0 ≤ 2 * K) hbnonneg]
  have hA := reciprocalLog_error_le K a _ hK ha0 hla (hE a ⟨le_rfl, hab⟩)
  have hB := reciprocalLog_error_le K b _ hK (zero_lt_one.trans hb1)
    (hlx b ⟨hab, le_rfl⟩) (hE b ⟨hab, le_rfl⟩)
  have hBA : K / Real.log b ≤ K / Real.log a :=
    div_le_div_of_nonneg_left hK hlap (Real.log_le_log ha0 hab)
  rw [hAbel]
  calc
    _ ≤ |reciprocalLog b * (partialCoefficientSum c b - α * b)| +
        |reciprocalLog a * (partialCoefficientSum c a - α * a)| +
        |∫ t in a..b, deriv reciprocalLog t * (partialCoefficientSum c t - α * t)| :=
      (abs_sub _ _).trans (add_le_add (abs_sub _ _) (le_refl _))
    _ ≤ K / Real.log a + K / Real.log a + 2 * K / Real.log a :=
      add_le_add (add_le_add (hB.trans hBA) hA) hi
    _ = _ := by ring

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.WeightedThetaError
namespace OAI

/-! The bounded-error form of partial summation needed for the padding
oscillation. The constants retain the uniform derivative bounds explicitly. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.Classical

theorem weighted_theta_error (c : ℕ → ℝ) (α K F D a b : ℝ)
    (hK : 0 ≤ K) (hF : 0 ≤ F) (hD : 0 ≤ D)
    (ha : Real.exp 1 ≤ a) (hab : a ≤ b) (f : ℝ → ℝ)
    (hf : ∀ x ∈ Set.Icc a b, DifferentiableAt ℝ f x)
    (hdf : ContinuousOn (deriv f) (Set.Icc a b))
    (hsize : ∀ x ∈ Set.Icc a b, |f x| ≤ F / x)
    (hdsize : ∀ x ∈ Set.Icc a b, |deriv f x| ≤ D / x ^ 2)
    (hE : ∀ x ∈ Set.Icc a b,
      |partialCoefficientSum c x - α * x| ≤ K * x / Real.log x ^ 2) :
    |(∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, f n * c n) - α * (∫ x in a..b, f x)| ≤
      (2 * F + D) * K / Real.log a := by
  have ha1 : 1 < a := (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 1)).trans_le ha
  have ha0 : 0 < a := zero_lt_one.trans ha1
  have hb1 : 1 < b := ha1.trans_le hab
  have hla : 1 ≤ Real.log a := by simpa using Real.log_le_log (Real.exp_pos 1) ha
  have hlap : 0 < Real.log a := Real.log_pos ha1
  have hxp (x : ℝ) (hx : x ∈ Set.Icc a b) : 0 < x := ha0.trans_le hx.1
  have hlx (x : ℝ) (hx : x ∈ Set.Icc a b) : 1 ≤ Real.log x :=
    hla.trans (Real.log_le_log ha0 hx.1)
  have hln (x : ℝ) (hx : x ∈ Set.Icc a b) : Real.log x ≠ 0 :=
    (zero_lt_one.trans_le (hlx x hx)).ne'
  have hbound (x : ℝ) (hx : x ∈ Set.Icc a b) :
      |f x * (partialCoefficientSum c x - α * x)| ≤ F * K / Real.log a := by
    have hx0 := hxp x hx
    have hl0 := hln x hx
    rw [abs_mul]
    calc
      _ ≤ (F / x) * (K * x / Real.log x ^ 2) :=
        mul_le_mul (hsize x hx) (hE x hx) (abs_nonneg _) (by positivity)
      _ = F * K / Real.log x ^ 2 := by field_simp
      _ ≤ F * K / Real.log a := by
        apply div_le_div_of_nonneg_left (mul_nonneg hF hK) hlap
        have hm := Real.log_le_log ha0 hx.1
        nlinarith [sq_nonneg (Real.log x - 1), hlx x hx]
  have hderror (x : ℝ) (hx : x ∈ Set.Icc a b) :
      |deriv f x * (partialCoefficientSum c x - α * x)| ≤
        (D * K) * (x⁻¹ / Real.log x ^ 2) := by
    have hx0 := hxp x hx
    have hl0 := hln x hx
    rw [abs_mul]
    calc
      _ ≤ (D / x ^ 2) * (K * x / Real.log x ^ 2) :=
        mul_le_mul (hdsize x hx) (hE x hx) (abs_nonneg _) (by positivity)
      _ = _ := by field_simp
  have hclog : ContinuousOn Real.log (Set.Icc a b) :=
    fun x hx => (Real.continuousAt_log (hxp x hx).ne').continuousWithinAt
  have hg : IntervalIntegrable (fun x : ℝ => (D * K) * (x⁻¹ / Real.log x ^ 2)) volume a b := by
    apply ContinuousOn.intervalIntegrable_of_Icc (h := hab)
    exact ((continuousOn_id.inv₀ (fun x hx => (hxp x hx).ne')).div
      (hclog.pow 2) (fun x hx => pow_ne_zero 2 (hln x hx))).const_mul (D * K)
  have hi : |∫ x in a..b, deriv f x * (partialCoefficientSum c x - α * x)| ≤
      D * K / Real.log a := by
    have hh := intervalIntegral.norm_integral_le_of_norm_le hab
      (Filter.Eventually.of_forall (fun x hx => by
        rw [Real.norm_eq_abs]
        exact hderror x ⟨hx.1.le, hx.2⟩)) hg
    rw [Real.norm_eq_abs, intervalIntegral.integral_const_mul,
      integral_inv_div_log_sq ha1 hb1] at hh
    apply hh.trans
    have hbnonneg : 0 ≤ (Real.log b)⁻¹ := inv_nonneg.mpr (Real.log_pos hb1).le
    simp only [div_eq_mul_inv]
    nlinarith [mul_nonneg (mul_nonneg hD hK) hbnonneg]
  rw [centered_partial_summation c α a b ha0.le hab f hf hdf]
  calc
    _ ≤ |f b * (partialCoefficientSum c b - α * b)| +
        |f a * (partialCoefficientSum c a - α * a)| +
        |∫ t in a..b, deriv f t * (partialCoefficientSum c t - α * t)| :=
      (abs_sub _ _).trans (add_le_add (abs_sub _ _) (le_refl _))
    _ ≤ F * K / Real.log a + F * K / Real.log a + D * K / Real.log a :=
      add_le_add (add_le_add (hbound b ⟨hab, le_rfl⟩) (hbound a ⟨le_rfl, hab⟩)) hi
    _ = _ := by ring

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.ModFivePrimeBands
namespace OAI

/-! Concrete modulus-five supplies and their reciprocal masses. We use
half-open bands `(exp A, exp B]`; this harmless endpoint convention makes
adjacent supplies exactly disjoint and matches finite Abel summation. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical


lemma partialSum_deletedModFive (E : Finset ℕ) (one : Bool) (x : ℝ) :
    partialCoefficientSum (deletedModFiveLogWeight E one) x =
      deletedModFiveTheta E one x := by
  unfold partialCoefficientSum deletedModFiveTheta deletedModFivePrimes
    modFivePrimesUpTo deletedModFiveLogWeight
  rw [sdiff_eq_filter, sum_filter, sum_filter]
  apply sum_congr rfl
  intro p hp
  by_cases h : ModFivePrime one p <;> by_cases he : p ∈ E <;> simp [h, he]



lemma modFivePrimeBand_sum (E : Finset ℕ) (one : Bool) (a b : ℝ) :
    (∑ p ∈ modFivePrimeBand E one a b, 1 / (p : ℝ)) =
      ∑ p ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, reciprocalLog p * deletedModFiveLogWeight E one p := by
  rw [modFivePrimeBand, sum_filter]
  apply sum_congr rfl
  intro p hp
  by_cases hs : ModFivePrime one p ∧ p ∉ E
  · have hl : Real.log (p : ℝ) ≠ 0 :=
      (Real.log_pos (by exact_mod_cast hs.1.1.one_lt)).ne'
    rw [if_pos hs]
    unfold deletedModFiveLogWeight
    rw [if_pos hs]
    unfold reciprocalLog
    field_simp
  · simp [deletedModFiveLogWeight, hs]

/-- Both selected prime classes have their correct logarithmic-band mass,
uniformly over the upper endpoint and with any fixed finite exclusions. -/
theorem ModFiveThetaInput.band_error (hP : ModFiveThetaInput) (E : Finset ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (one : Bool) (A B : ℝ), 1 ≤ A → A ≤ B →
      |(∑ p ∈ modFivePrimeBand E one (Real.exp A) (Real.exp B), 1 / (p : ℝ)) -
          modFiveDensity one * (Real.log B - Real.log A)| ≤ 4 * K / A := by
  obtain ⟨K, hK, h⟩ := hP.deleted_log_error E
  refine ⟨K, hK, fun one A B hA hAB => ?_⟩
  rw [modFivePrimeBand_sum]
  have hh := reciprocal_band_error (deletedModFiveLogWeight E one) (modFiveDensity one)
    K (Real.exp A) (Real.exp B) hK (Real.exp_le_exp.mpr hA)
      (Real.exp_le_exp.mpr hAB) (fun x hx => by
        rw [partialSum_deletedModFive]
        apply h one x
        have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
        exact h2.trans ((Real.exp_le_exp.mpr hA).trans hx.1))
  simpa only [Real.log_exp] using hh

/-- The concrete centered-prime supplies have reciprocal mass in `[W,2W]`
once their lower logarithmic endpoint exceeds one fixed threshold. -/
theorem ModFiveThetaInput.centered_band_mass (hP : ModFiveThetaInput)
    (E : Finset ℕ) (W : ℝ) (hW : 0 < W) :
    ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ A : ℝ, A₀ ≤ A →
      W ≤ (∑ p ∈ modFivePrimeBand E true (Real.exp A)
        (Real.exp (A * Real.exp (6 * W))), 1 / (p : ℝ)) ∧
      (∑ p ∈ modFivePrimeBand E true (Real.exp A)
        (Real.exp (A * Real.exp (6 * W))), 1 / (p : ℝ)) ≤ 2 * W := by
  obtain ⟨K, hK, h⟩ := hP.band_error E
  refine ⟨max 1 (8 * K / W), le_max_left _ _, fun A hA => ?_⟩
  have hA1 : 1 ≤ A := (le_max_left _ _).trans hA
  have hA0 : 0 < A := zero_lt_one.trans_le hA1
  have hB : A ≤ A * Real.exp (6 * W) := by
    have hh := mul_le_mul_of_nonneg_left (Real.one_le_exp (by positivity : 0 ≤ 6 * W)) hA0.le
    simpa only [mul_one] using hh
  have hmass := h true A (A * Real.exp (6 * W)) hA1 hB
  have he : Real.log (A * Real.exp (6 * W)) - Real.log A = 6 * W := by
    rw [Real.log_mul hA0.ne' (Real.exp_pos _).ne', Real.log_exp]
    ring
  rw [he] at hmass
  have hsmall : 4 * K / A ≤ W / 2 := by
    have hh := (div_le_iff₀ hW).mp ((le_max_right 1 (8 * K / W)).trans hA)
    apply (div_le_iff₀ hA0).mpr
    nlinarith [hh]
  have hh := abs_le.mp hmass
  norm_num [modFiveDensity] at hh
  simp only [one_div]
  constructor <;> linarith

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PrimeSupplyGeometry
namespace OAI

/-! Actual disjoint prime supplies at geometric logarithmic scales. Their
mass follows from the published fixed-modulus input through the proved
partial-summation chain, and all support assertions are finite identities. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical




lemma primeSupplyEndpoint_zero (A W : ℝ) : primeSupplyEndpoint A W 0 = A := by
  simp [primeSupplyEndpoint]

lemma primeSupplyEndpoint_succ (A W : ℝ) (i : ℕ) :
    primeSupplyEndpoint A W (i + 1) = primeSupplyEndpoint A W i * Real.exp (6 * W) := by
  unfold primeSupplyEndpoint
  rw [Nat.cast_add, Nat.cast_one, mul_add, mul_one, Real.exp_add]
  ring






lemma primeSupplyEndpoint_sum_lt (A W : ℝ) (hA : 0 < A) (hW : 1 ≤ W) (J : ℕ) :
    (∑ i ∈ range J, primeSupplyEndpoint A W (i + 1)) < 2 * primeSupplyEndpoint A W J := by
  have hratio : 2 ≤ Real.exp (6 * W) := by
    linarith [Real.add_one_le_exp (6 * W)]
  induction J with
  | zero => simp [primeSupplyEndpoint, hA]
  | succ J ih =>
    have he : 0 ≤ primeSupplyEndpoint A W J := by unfold primeSupplyEndpoint; positivity
    have hstep : 2 * primeSupplyEndpoint A W J ≤ primeSupplyEndpoint A W (J + 1) := by
      rw [primeSupplyEndpoint_succ]
      nlinarith [mul_le_mul_of_nonneg_right hratio he]
    rw [sum_range_succ]
    linarith

lemma centeredPrimeSupply_tuple_log_bound {E : Finset ℕ} {A W L : ℝ}
    (hA : 0 < A) (hW : 1 ≤ W) {J : ℕ} (hL : primeSupplyEndpoint A W J ≤ L)
    (p : Fin J → ℕ) (hp : ∀ i : Fin J, p i ∈ centeredPrimeSupply E A W i.val) :
    Real.log ((∏ i, p i : ℕ) : ℝ) < 2 * L := by
  have hlog : Real.log ((∏ i, p i : ℕ) : ℝ) = ∑ i, Real.log (p i : ℝ) := by
    rw [Nat.cast_prod, Real.log_prod]
    intro i _
    exact_mod_cast (centeredPrimeSupply_mem (hp i)).1.ne_zero
  rw [hlog]
  calc
    _ ≤ ∑ i : Fin J, primeSupplyEndpoint A W (i.val + 1) :=
      sum_le_sum (fun i _ => (centeredPrimeSupply_mem (hp i)).2.2.2.2)
    _ = ∑ i ∈ range J, primeSupplyEndpoint A W (i + 1) :=
      Fin.sum_univ_eq_sum_range (fun i : ℕ => primeSupplyEndpoint A W (i + 1)) J
    _ < 2 * primeSupplyEndpoint A W J := primeSupplyEndpoint_sum_lt A W hA hW J
    _ ≤ 2 * L := by linarith

/-- Every centered supply is nonempty and has the required reciprocal mass.
The threshold is independent of the number of supplies and their indices. -/
theorem ModFiveThetaInput.centered_supplies (hP : ModFiveThetaInput)
    (E : Finset ℕ) (W : ℝ) (hW : 0 < W) :
    ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ A : ℝ, A₀ ≤ A → ∀ i : ℕ,
      (centeredPrimeSupply E A W i).Nonempty ∧
      W ≤ (∑ p ∈ centeredPrimeSupply E A W i, 1 / (p : ℝ)) ∧
      (∑ p ∈ centeredPrimeSupply E A W i, 1 / (p : ℝ)) ≤ 2 * W := by
  obtain ⟨A₀, hA₀, hmass⟩ := hP.centered_band_mass E W hW
  refine ⟨A₀, hA₀, fun A hA i => ?_⟩
  have hA0 : 0 ≤ A := (zero_le_one.trans hA₀).trans hA
  have hlower : A₀ ≤ primeSupplyEndpoint A W i := by
    calc
      A₀ ≤ A := hA
      _ = primeSupplyEndpoint A W 0 := (primeSupplyEndpoint_zero A W).symm
      _ ≤ _ := primeSupplyEndpoint_mono A W hA0 hW.le (Nat.zero_le _)
  have hh := hmass (primeSupplyEndpoint A W i) hlower
  rw [← primeSupplyEndpoint_succ] at hh
  change W ≤ (∑ p ∈ centeredPrimeSupply E A W i, 1 / (p : ℝ)) ∧
      (∑ p ∈ centeredPrimeSupply E A W i, 1 / (p : ℝ)) ≤ 2 * W at hh
  refine ⟨?_, hh⟩
  by_contra he
  rw [not_nonempty_iff_eq_empty.mp he, sum_empty] at hh
  linarith [hh.1]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PrimeSupplyScale
namespace OAI

/-! The literal scale choice of the manuscript satisfies all prime-supply
mass and support hypotheses; no prime-family existence premise remains. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical


lemma primeSupplyScale_endpoint (W L : ℝ) (hW : 0 < W) (hL : 1 ≤ L) :
    primeSupplyEndpoint (L ^ (199 / 200 : ℝ)) W (primeSupplyCount W L) ≤ L := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hl : 0 ≤ Real.log L := Real.log_nonneg hL
  have hj : (primeSupplyCount W L : ℝ) ≤ ((1 / 200 : ℝ) * Real.log L) / (6 * W) :=
    Nat.floor_le (by positivity)
  have hj' := (le_div_iff₀ (by positivity : 0 < 6 * W)).mp hj
  unfold primeSupplyEndpoint
  calc
    _ = Real.exp (Real.log L * (199 / 200 : ℝ) + 6 * W * primeSupplyCount W L) := by
      rw [Real.rpow_def_of_pos hLp, Real.exp_add]
    _ ≤ Real.exp (Real.log L) := Real.exp_le_exp.mpr (by nlinarith)
    _ = L := Real.exp_log hLp

lemma eventually_primeSupplyCount_pos (W : ℝ) (hW : 0 < W) :
    ∀ᶠ L : ℝ in atTop, 1 ≤ primeSupplyCount W L := by
  filter_upwards [eventually_ge_atTop (Real.exp (1200 * W))] with L hL
  have hLp : 0 < L := (Real.exp_pos _).trans_le hL
  have hl : 1200 * W ≤ Real.log L := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) hL
  have hl0 : 0 ≤ Real.log L := le_trans (by positivity : (0 : ℝ) ≤ 1200 * W) hl
  unfold primeSupplyCount
  apply (Nat.le_floor_iff (by positivity : 0 ≤ ((1 / 200 : ℝ) * Real.log L) / (6 * W))).mpr
  norm_num
  apply (le_div_iff₀ (by positivity : 0 < 6 * W)).mpr
  linarith

theorem ModFiveThetaInput.eventually_actual_prime_supplies (hP : ModFiveThetaInput)
    (E : Finset ℕ) (W : ℝ) (hW : 1 ≤ W) :
    ∀ᶠ L : ℝ in atTop,
      1 ≤ primeSupplyCount W L ∧
      primeSupplyEndpoint (L ^ (199 / 200 : ℝ)) W (primeSupplyCount W L) ≤ L ∧
      ∀ i : ℕ, (centeredPrimeSupply E (L ^ (199 / 200 : ℝ)) W i).Nonempty ∧
        W ≤ (∑ p ∈ centeredPrimeSupply E (L ^ (199 / 200 : ℝ)) W i, 1 / (p : ℝ)) ∧
        (∑ p ∈ centeredPrimeSupply E (L ^ (199 / 200 : ℝ)) W i, 1 / (p : ℝ)) ≤ 2 * W := by
  have hWp : 0 < W := zero_lt_one.trans_le hW
  obtain ⟨A₀, _, hmass⟩ := hP.centered_supplies E W hWp
  have hlarge := (tendsto_rpow_atTop (show 0 < (199 / 200 : ℝ) by norm_num)).eventually
    (eventually_ge_atTop A₀)
  filter_upwards [eventually_ge_atTop (1 : ℝ), eventually_primeSupplyCount_pos W hWp,
    hlarge] with L hL hJ hA
  exact ⟨hJ, primeSupplyScale_endpoint W L hWp hL,
    hmass (L ^ (199 / 200 : ℝ)) hA⟩

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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.RetainedDivisorMass
namespace OAI

/-! The literal finite retained-divisor set and its Euler-product mass.
Distinct prime subsets produce distinct integers, so the divisor sum does
not contain hidden multiplicities. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical



lemma retainedPrimeDivisor_pos (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p)
    {u : ℕ} (hu : u ∈ retainedPrimeDivisors S) : 0 < u := by
  obtain ⟨U, hU, rfl⟩ := mem_image.mp hu
  exact prod_pos (fun p hp => (hS p ((mem_powerset.mp hU) hp)).pos)




end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PaddingLiteralBins
namespace OAI

/-! The bin mass is the literal normalized sum of padding-divisor weights.
Boolean selections are finite subsets, so no extra multiplicity is present. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical





lemma paddingDivisorCoefficient_eq_four_pow (Q : Finset ℕ) (b : Q → Bool) :
    paddingDivisorCoefficient Q b = (4 : ℝ) ^ (selectedCoordinates Q b).card := by
  rw [← prod_const]
  simp only [selectedCoordinates, prod_filter, paddingDivisorCoefficient]


lemma paddingSelectedDivisor_log (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (b : Q → Bool) : Real.log (paddingSelectedDivisor Q b) = paddingLog Q b := by
  rw [paddingSelectedDivisor, Nat.cast_prod, Real.log_prod]
  · simp only [selectedCoordinates, sum_filter, paddingLog]
  · intro p _
    exact_mod_cast (hQ p p.property).ne_zero



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



lemma paddingBin_eq_iff (η c x : ℝ) (j : ℤ) (hη : 0 < η) :
    paddingBin η c x = j ↔ (j : ℝ) * η ≤ x + c ∧ x + c < ((j : ℝ) + 1) * η := by
  rw [paddingBin, Int.floor_eq_iff, le_div_iff₀ hη, div_lt_iff₀ hη]





end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ReciprocalPaddingLaw
namespace OAI

/-! The harmonic divisor law `4^omega(q)/(q S)` is an actual finite
independent prime-selection law with inclusion probabilities `4/(p+4)`. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical



lemma reciprocal_padding_atom (p : ℕ) (hp : 0 < p) (b : Bool) :
    (reciprocalPaddingPrimeLaw p).weight b * (1 + 4 / (p : ℝ)) =
      if b then 4 / (p : ℝ) else 1 := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  have hp4 : (p : ℝ) + 4 ≠ 0 := by positivity
  cases b <;> simp only [reciprocalPaddingPrimeLaw, booleanLaw, Bool.false_eq_true, ↓reduceIte]
  all_goals field_simp <;> ring

lemma paddingSelectedDivisor_cast (Q : Finset ℕ) (b : Q → Bool) :
    (paddingSelectedDivisor Q b : ℝ) = ∏ p : Q, if b p then (p.val : ℝ) else 1 := by
  rw [paddingSelectedDivisor, Nat.cast_prod]
  simp only [selectedCoordinates, prod_filter]

lemma reciprocal_padding_weight (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime) (b : Q → Bool) :
    (reciprocalPaddingLaw Q).weight b * paddingTiltNormalizer Q =
      paddingDivisorCoefficient Q b / (paddingSelectedDivisor Q b : ℝ) := by
  simp only [reciprocalPaddingLaw, FiniteLaw.independent, paddingTiltNormalizer,
    ← prod_mul_distrib]
  rw [paddingDivisorCoefficient, paddingSelectedDivisor_cast, ← prod_div_distrib]
  apply prod_congr rfl
  intro p _
  rw [reciprocal_padding_atom p (hQ p p.property).pos]
  cases b p <;> simp

lemma reciprocal_padding_average (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime) (F : ℕ → ℝ) :
    (reciprocalPaddingLaw Q).average (fun b => F (paddingSelectedDivisor Q b)) =
      (paddingTiltNormalizer Q)⁻¹ *
        ∑ q ∈ retainedPrimeDivisors Q, ((4 : ℝ) ^ q.primeFactors.card / (q : ℝ)) * F q := by
  have hS := paddingTiltNormalizer_pos Q
  let G (q : retainedPrimeDivisors Q) : ℝ :=
    ((4 : ℝ) ^ q.val.primeFactors.card / (q.val : ℝ)) * F q.val
  have hatom (b : Q → Bool) :
      (reciprocalPaddingLaw Q).weight b * F (paddingSelectedDivisor Q b) =
        (paddingTiltNormalizer Q)⁻¹ * G (paddingDivisorEquiv Q hQ b) := by
    have hw := reciprocal_padding_weight Q hQ b
    change _ = (paddingTiltNormalizer Q)⁻¹ *
      ((4 : ℝ) ^ (paddingSelectedDivisor Q b).primeFactors.card /
        (paddingSelectedDivisor Q b : ℝ) * F (paddingSelectedDivisor Q b))
    rw [paddingSelectedDivisor_primeFactors Q hQ b, paddingAvailablePrimes_card,
      ← paddingDivisorCoefficient_eq_four_pow]
    calc
      _ = (paddingTiltNormalizer Q)⁻¹ *
          (((reciprocalPaddingLaw Q).weight b * paddingTiltNormalizer Q) *
            F (paddingSelectedDivisor Q b)) := by field_simp [hS.ne']
      _ = _ := by rw [hw]
  unfold FiniteLaw.average
  simp_rw [hatom]
  rw [← mul_sum, (paddingDivisorEquiv Q hQ).sum_comp G]
  congr 1
  exact sum_coe_sort (retainedPrimeDivisors Q)
    (fun q : ℕ => ((4 : ℝ) ^ q.primeFactors.card / (q : ℝ)) * F q)

lemma FiniteLaw.independent_average_coordinate {ι A : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype A] (μ : ι → FiniteLaw A) (i : ι) (f : A → ℝ) :
    (FiniteLaw.independent μ).average (fun x => f (x i)) = (μ i).average f := by
  have hh := FiniteLaw.independent_average_product μ (fun j x => if j = i then f x else 1)
  have he (j : ι) : (μ j).average (fun x => if j = i then f x else 1) =
      if j = i then (μ i).average f else 1 := by
    by_cases hj : j = i
    · subst j
      simp
    · simp [hj]
  simpa only [he, prod_ite_eq', mem_univ, ite_true] using hh

lemma reciprocal_padding_count_average (Q : Finset ℕ) :
    (reciprocalPaddingLaw Q).average booleanCount = ∑ p : Q, 4 / ((p.val : ℝ) + 4) := by
  change (FiniteLaw.independent (fun p : Q => reciprocalPaddingPrimeLaw p)).average
    (fun b : Q → Bool => ∑ p : Q, if b p then 1 else 0) = _
  rw [FiniteLaw.average_sum]
  apply sum_congr rfl
  intro p _
  rw [FiniteLaw.independent_average_coordinate (fun p : Q => reciprocalPaddingPrimeLaw p) p
    (fun b : Bool => if b then 1 else 0)]
  simp [reciprocalPaddingPrimeLaw, booleanLaw, FiniteLaw.average]

lemma reciprocal_padding_log_average (Q : Finset ℕ) :
    (reciprocalPaddingLaw Q).average (paddingLog Q) =
      ∑ p : Q, (4 / ((p.val : ℝ) + 4)) * Real.log p.val := by
  change (FiniteLaw.independent (fun p : Q => reciprocalPaddingPrimeLaw p)).average
    (fun b : Q → Bool => ∑ p : Q, if b p then Real.log p.val else 0) = _
  rw [FiniteLaw.average_sum]
  apply sum_congr rfl
  intro p _
  rw [FiniteLaw.independent_average_coordinate (fun p : Q => reciprocalPaddingPrimeLaw p) p
    (fun b : Bool => if b then Real.log p.val else 0)]
  simp [reciprocalPaddingPrimeLaw, booleanLaw, FiniteLaw.average]

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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PaddingDegreeTail
namespace OAI

/-! The exact tilted padding law has mean at most `4 log L` eventually.
The finite exponential-moment bound gives the manuscript's `L^-100`
large-padding-degree error using the same fixed-modulus prime input. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical

lemma paddingPrimeSupply_split (E : Finset ℕ) (L : ℝ) (hL : 1 ≤ L) :
    paddingPrimeSupply E L = paddingPrimeSupply E 1 ∪
      modFivePrimeBand E false (Real.exp 1) (Real.exp L) := by
  have hfloor : ⌊Real.exp 1⌋₊ ≤ ⌊Real.exp L⌋₊ :=
    Nat.floor_mono (Real.exp_le_exp.mpr hL)
  ext p
  constructor
  · intro hp
    obtain ⟨hp, he⟩ := Finset.mem_sdiff.mp hp
    obtain ⟨hp, hprime⟩ := mem_filter.mp hp
    obtain ⟨hp0, hpL⟩ := mem_Icc.mp hp
    apply mem_union.mpr
    by_cases hsmall : p ≤ ⌊Real.exp 1⌋₊
    · exact Or.inl (Finset.mem_sdiff.mpr ⟨mem_filter.mpr ⟨mem_Icc.mpr ⟨hp0, hsmall⟩, hprime⟩, he⟩)
    · exact Or.inr (mem_filter.mpr ⟨mem_Ioc.mpr ⟨by omega, hpL⟩, hprime, he⟩)
  · intro hp
    apply Finset.mem_sdiff.mpr
    rcases mem_union.mp hp with hp | hp
    · obtain ⟨hp, he⟩ := Finset.mem_sdiff.mp hp
      obtain ⟨hp, hprime⟩ := mem_filter.mp hp
      obtain ⟨hp0, hp1⟩ := mem_Icc.mp hp
      exact ⟨mem_filter.mpr ⟨mem_Icc.mpr ⟨hp0, hp1.trans hfloor⟩, hprime⟩, he⟩
    · obtain ⟨hp, hprime, he⟩ := mem_filter.mp hp
      exact ⟨mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.zero_le p, (mem_Ioc.mp hp).2⟩, hprime⟩, he⟩

lemma paddingPrimeSupply_split_disjoint (E : Finset ℕ) (L : ℝ) :
    Disjoint (paddingPrimeSupply E 1)
      (modFivePrimeBand E false (Real.exp 1) (Real.exp L)) := by
  apply disjoint_left.mpr
  intro p hp hb
  have hp1 := (mem_Icc.mp (mem_filter.mp (Finset.mem_sdiff.mp hp).1).1).2
  have hp2 := (mem_Ioc.mp (mem_filter.mp hb).1).1
  omega

theorem ModFiveThetaInput.padding_reciprocal_mass (hP : ModFiveThetaInput) (E : Finset ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ L : ℝ, 1 ≤ L →
      (∑ p ∈ paddingPrimeSupply E L, 1 / (p : ℝ)) ≤ (3 / 4 : ℝ) * Real.log L + C := by
  obtain ⟨K, hK, hband⟩ := hP.band_error E
  refine ⟨(∑ p ∈ paddingPrimeSupply E 1, 1 / (p : ℝ)) + 4 * K,
    add_nonneg (sum_nonneg (fun _ _ => by positivity)) (by positivity), fun L hL => ?_⟩
  rw [paddingPrimeSupply_split E L hL, sum_union (paddingPrimeSupply_split_disjoint E L)]
  have hb := (abs_le.mp (hband false 1 L le_rfl hL)).2
  norm_num [modFiveDensity] at hb
  simp only [one_div]
  linarith

lemma padding_mean_le_reciprocal (Q : Finset ℕ) (hQ : ∀ p ∈ Q, 2 ≤ p) :
    (∑ p : Q, 5 / ((p.val : ℝ) + 4)) ≤ 5 * ∑ p ∈ Q, 1 / (p : ℝ) := by
  rw [← sum_coe_sort Q (fun p : ℕ => 1 / (p : ℝ)), mul_sum]
  apply sum_le_sum
  intro p _
  have hp : (0 : ℝ) < p.val := by exact_mod_cast (by have := hQ p p.property; omega : 0 < p.val)
  calc
    5 / ((p.val : ℝ) + 4) ≤ 5 / (p.val : ℝ) :=
      div_le_div_of_nonneg_left (by norm_num) hp (by linarith)
    _ = _ := by ring

theorem ModFiveThetaInput.eventually_padding_mean (hP : ModFiveThetaInput) (E : Finset ℕ) :
    ∀ᶠ L : ℝ in atTop,
      (∑ p : paddingPrimeSupply E L, 5 / ((p.val : ℝ) + 4)) ≤ 4 * Real.log L := by
  obtain ⟨C, hC, hmass⟩ := hP.padding_reciprocal_mass E
  filter_upwards [eventually_ge_atTop (Real.exp (20 * C)), eventually_ge_atTop (1 : ℝ)]
    with L hLC hL
  have hlog : 20 * C ≤ Real.log L := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) hLC
  have hh := padding_mean_le_reciprocal (paddingPrimeSupply E L)
    (fun _ hp => (paddingPrimeSupply_prime hp).two_le)
  nlinarith [hmass L hL]



end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PaddingLogMoment
namespace OAI

/-! The same fixed-modulus input bounds the logarithmic moment of the
reciprocal padding-divisor law, as needed for mass retained in bins. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter _root_.MeasureTheory
open scoped _root_.Classical

lemma modFivePrimeBand_log_mass (E : Finset ℕ) (one : Bool) (a b : ℝ) :
    (∑ p ∈ modFivePrimeBand E one a b, Real.log p / p) =
      ∑ p ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, (p : ℝ)⁻¹ * deletedModFiveLogWeight E one p := by
  rw [modFivePrimeBand, sum_filter]
  apply sum_congr rfl
  intro p _
  by_cases hs : ModFivePrime one p ∧ p ∉ E
  · simp only [if_pos hs, deletedModFiveLogWeight]
    ring
  · simp [deletedModFiveLogWeight, hs]

theorem ModFiveThetaInput.padding_log_mass (hP : ModFiveThetaInput) (E : Finset ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ L : ℝ, 1 ≤ L →
      (∑ p ∈ paddingPrimeSupply E L, Real.log p / p) ≤ (3 / 4 : ℝ) * L + C := by
  obtain ⟨K, hK, herror⟩ := hP.deleted_log_error E
  let C₀ := ∑ p ∈ paddingPrimeSupply E 1, Real.log p / p
  have hC₀ : 0 ≤ C₀ := sum_nonneg (fun p _ => div_nonneg (log_nat_nonneg p) (Nat.cast_nonneg p))
  refine ⟨C₀ + 3 * K, by positivity, fun L hL => ?_⟩
  have hab : Real.exp 1 ≤ Real.exp L := Real.exp_le_exp.mpr hL
  have hxp (x : ℝ) (hx : x ∈ Set.Icc (Real.exp 1) (Real.exp L)) : 0 < x :=
    (Real.exp_pos 1).trans_le hx.1
  have hh := weighted_theta_error (deletedModFiveLogWeight E false) (modFiveDensity false)
    K 1 1 (Real.exp 1) (Real.exp L) hK (by norm_num) (by norm_num) le_rfl hab
    (fun x : ℝ => x⁻¹)
    (fun x hx => (hasDerivAt_inv (hxp x hx).ne').differentiableAt)
    (fun x hx => by
      have hxn : x ≠ 0 := (hxp x hx).ne'
      have hc : ContDiffAt ℝ 2 (fun y : ℝ => y⁻¹) x := by fun_prop (disch := assumption)
      exact (hc.derivWithin (m := 0) (by norm_num)).continuousAt.continuousWithinAt)
    (fun x hx => by rw [abs_of_pos (inv_pos.mpr (hxp x hx))]; simp)
    (fun x hx => by
      rw [(hasDerivAt_inv (hxp x hx).ne').deriv]
      simp [abs_of_pos (hxp x hx), one_div])
    (fun x hx => by
      rw [partialSum_deletedModFive]
      apply herror false x
      have he : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
      exact he.trans hx.1)
  rw [← modFivePrimeBand_log_mass] at hh
  have hi : (∫ x in Real.exp 1..Real.exp L, x⁻¹) = L - 1 := by
    rw [integral_inv_of_pos (Real.exp_pos _) (Real.exp_pos _),
      Real.log_div (Real.exp_pos _).ne' (Real.exp_pos _).ne', Real.log_exp, Real.log_exp]
  rw [hi, Real.log_exp] at hh
  norm_num [modFiveDensity] at hh
  rw [paddingPrimeSupply_split E L hL, sum_union (paddingPrimeSupply_split_disjoint E L)]
  have hu := (abs_le.mp hh).2
  change C₀ + _ ≤ _
  linarith

theorem ModFiveThetaInput.eventually_reciprocal_padding_log_mean (hP : ModFiveThetaInput)
    (E : Finset ℕ) :
    ∀ᶠ L : ℝ in atTop,
      (∑ p : paddingPrimeSupply E L, (4 / ((p.val : ℝ) + 4)) * Real.log p.val) ≤ 4 * L := by
  obtain ⟨C, hC, hbound⟩ := hP.padding_log_mass E
  filter_upwards [eventually_ge_atTop (4 * C), eventually_ge_atTop (1 : ℝ)] with L hLC hL
  have hh : (∑ p : paddingPrimeSupply E L, (4 / ((p.val : ℝ) + 4)) * Real.log p.val) ≤
      4 * ∑ p ∈ paddingPrimeSupply E L, Real.log p / p := by
    rw [← sum_coe_sort _ (fun p : ℕ => Real.log p / p), mul_sum]
    apply sum_le_sum
    intro p _
    have hp : (0 : ℝ) < p.val := by exact_mod_cast (paddingPrimeSupply_prime p.property).pos
    calc
      (4 / ((p.val : ℝ) + 4)) * Real.log p.val ≤ (4 / p.val) * Real.log p.val :=
        mul_le_mul_of_nonneg_right
          (div_le_div_of_nonneg_left (by norm_num) hp (by linarith)) (log_nat_nonneg p.val)
      _ = _ := by ring
  nlinarith [hbound L hL]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PaddingRetainedProbability
namespace OAI

/-! Under the exact harmonic padding law, more than half the mass obeys
both the degree and logarithmic-size restrictions used to form the bins. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical

lemma FiniteLaw.probability_lt_le_average {A : Type*} [Fintype A]
    (μ : FiniteLaw A) (Z : A → ℝ) (hZ : ∀ x, 0 ≤ Z x) (t : ℝ) (ht : 0 < t) :
    μ.probability (fun x => t < Z x) ≤ μ.average Z / t := by
  calc
    _ ≤ μ.average (fun x => Z x / t) := by
      apply μ.average_mono
      intro x
      by_cases hx : t < Z x
      · rw [if_pos hx]
        exact (one_le_div ht).mpr hx.le
      · rw [if_neg hx]
        exact div_nonneg (hZ x) ht.le
    _ = _ := by
      simp only [div_eq_mul_inv, μ.average_mul_const]

lemma FiniteLaw.probability_and_ge {A : Type*} [Fintype A]
    (μ : FiniteLaw A) (E F : A → Prop) :
    1 - μ.probability (fun x => ¬ E x) - μ.probability (fun x => ¬ F x) ≤
      μ.probability (fun x => E x ∧ F x) := by
  have hh := μ.average_mono (f := fun x =>
    1 - (if ¬ E x then 1 else 0) - (if ¬ F x then 1 else 0))
    (g := fun x => if E x ∧ F x then 1 else 0) (fun x => by
      by_cases he : E x <;> by_cases hf : F x <;> simp [he, hf])
  simpa [FiniteLaw.average, FiniteLaw.probability, mul_sub,
    sum_sub_distrib, μ.total] using hh

lemma booleanCount_nonneg {ι : Type*} [Fintype ι] (a : ι → Bool) : 0 ≤ booleanCount a := by
  apply sum_nonneg
  intro i _
  split_ifs <;> norm_num

lemma paddingLog_nonneg (Q : Finset ℕ) (b : Q → Bool) : 0 ≤ paddingLog Q b := by
  apply sum_nonneg
  intro p _
  split_ifs
  · exact log_nat_nonneg p.val
  · exact le_refl _

theorem ModFiveThetaInput.eventually_reciprocal_padding_count_mean (hP : ModFiveThetaInput)
    (E : Finset ℕ) :
    ∀ᶠ L : ℝ in atTop,
      (reciprocalPaddingLaw (paddingPrimeSupply E L)).average booleanCount ≤ 4 * Real.log L := by
  filter_upwards [hP.eventually_padding_mean E] with L hL
  rw [reciprocal_padding_count_average]
  refine le_trans (sum_le_sum fun p _ => ?_) hL
  exact div_le_div_of_nonneg_right (by norm_num) (by positivity)

theorem ModFiveThetaInput.eventually_retained_padding_probability (hP : ModFiveThetaInput)
    (E : Finset ℕ) :
    ∀ᶠ L : ℝ in atTop,
      (1 / 2 : ℝ) ≤ (reciprocalPaddingLaw (paddingPrimeSupply E L)).probability
        (fun b => booleanCount b ≤ 100 * Real.log L ∧
          paddingLog (paddingPrimeSupply E L) b ≤ 98 * L) := by
  filter_upwards [hP.eventually_reciprocal_padding_count_mean E,
    hP.eventually_reciprocal_padding_log_mean E, eventually_ge_atTop (2 : ℝ)]
      with L hc hl hL
  let Q := paddingPrimeSupply E L
  let μ := reciprocalPaddingLaw Q
  have hLp : 0 < L := lt_of_lt_of_le (by norm_num) hL
  have hlog : 0 < Real.log L := Real.log_pos (lt_of_lt_of_le (by norm_num) hL)
  have hcount : μ.probability (fun b => 100 * Real.log L < booleanCount b) ≤ 1 / 25 := by
    apply (μ.probability_lt_le_average booleanCount booleanCount_nonneg
      (100 * Real.log L) (by positivity)).trans
    calc
      _ ≤ (4 * Real.log L) / (100 * Real.log L) :=
        div_le_div_of_nonneg_right hc (by positivity)
      _ = _ := by field_simp; norm_num
  have hsize : μ.probability (fun b => 98 * L < paddingLog Q b) ≤ 2 / 49 := by
    apply (μ.probability_lt_le_average (paddingLog Q) (paddingLog_nonneg Q)
      (98 * L) (by positivity)).trans
    calc
      _ ≤ (4 * L) / (98 * L) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        change (reciprocalPaddingLaw Q).average (paddingLog Q) ≤ 4 * L
        rw [reciprocal_padding_log_average]
        exact hl
      _ = _ := by field_simp; norm_num
  have hh := μ.probability_and_ge (fun b => booleanCount b ≤ 100 * Real.log L)
    (fun b => paddingLog Q b ≤ 98 * L)
  simp only [not_le] at hh
  linarith

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PaddingBinCoverage
namespace OAI

/-! The literal finite bin family covers every padding divisor surviving
the degree and logarithmic-size cuts. This includes the last bin whose
left endpoint, rather than its right endpoint, is at most `100 L`. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical



lemma paddingBin_mem_indices {L η x : ℝ} (hη : 0 < η)
    (hx : 0 ≤ x) (hxL : x ≤ 100 * L) :
    paddingBin η 0 x ∈ paddingBinIndices L η := by
  change ⌊(x + 0) / η⌋ ∈ Icc 0 ⌊100 * L / η⌋
  rw [add_zero, mem_Icc]
  exact ⟨Int.floor_nonneg.mpr (div_nonneg hx hη.le),
    Int.floor_mono (div_le_div_of_nonneg_right hxL hη.le)⟩



lemma paddingSelectedDivisor_count (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (b : Q → Bool) :
    ((paddingSelectedDivisor Q b).primeFactors.card : ℝ) = booleanCount b := by
  rw [paddingSelectedDivisor_primeFactors Q hQ b, paddingAvailablePrimes_card,
    booleanCount_eq_card]
  rfl

lemma padding_pair_eligible_of_retained (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    {L η : ℝ} (hη : 0 < η) (d : ℕ) (hd : 0 < d)
    (hdL : Real.log d ≤ 2 * L) (b : Q → Bool)
    (hb : booleanCount b ≤ 100 * Real.log L ∧ paddingLog Q b ≤ 98 * L) :
    PaddingPairEligible L η d (paddingSelectedDivisor Q b) := by
  refine ⟨?_, ?_⟩
  · rw [paddingSelectedDivisor_count Q hQ b]
    exact hb.1
  · apply paddingBin_mem_indices hη (log_nat_nonneg _)
    have hq : 0 < paddingSelectedDivisor Q b :=
      retainedPrimeDivisor_pos Q hQ (paddingSelectedDivisor_mem Q b)
    have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
    have hq0 : (paddingSelectedDivisor Q b : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
    rw [Nat.cast_mul, Real.log_mul hd0 hq0, paddingSelectedDivisor_log Q hQ b]
    linarith [hb.2]

lemma reciprocal_padding_eligible_probability (Q : Finset ℕ)
    (hQ : ∀ p ∈ Q, p.Prime) {L η : ℝ} (hη : 0 < η)
    (hhalf : (1 / 2 : ℝ) ≤ (reciprocalPaddingLaw Q).probability
      (fun b => booleanCount b ≤ 100 * Real.log L ∧ paddingLog Q b ≤ 98 * L))
    (d : ℕ) (hd : 0 < d) (hdL : Real.log d ≤ 2 * L) :
    (1 / 2 : ℝ) ≤ (reciprocalPaddingLaw Q).probability
      (fun b => PaddingPairEligible L η d (paddingSelectedDivisor Q b)) := by
  apply hhalf.trans
  apply FiniteLaw.average_mono
  intro b
  by_cases hb : booleanCount b ≤ 100 * Real.log L ∧ paddingLog Q b ≤ 98 * L
  · have he := padding_pair_eligible_of_retained Q hQ hη d hd hdL b hb
    simp only [if_pos hb, if_pos he, le_refl]
  · simp only [if_neg hb]
    split_ifs <;> norm_num


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PaddingBinMassTotal
namespace OAI

/-! The actual finite harmonic mass in the manuscript's half-open bins.
Its lower bound follows from the proved reciprocal padding law and its
upper bound simply removes the two restrictions. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical



lemma padding_bin_weight_sum (L η : ℝ) (d q : ℕ) (hη : 0 < η) :
    (∑ j ∈ paddingBinIndices L η,
      if (q.primeFactors.card : ℝ) ≤ 100 * Real.log L ∧
          (j : ℝ) * η ≤ Real.log (d * q : ℕ) ∧
          Real.log (d * q : ℕ) < ((j : ℝ) + 1) * η
      then (4 : ℝ) ^ q.primeFactors.card / (d * q : ℕ) else 0) =
      if PaddingPairEligible L η d q then
        (4 : ℝ) ^ q.primeFactors.card / (d * q : ℕ) else 0 := by
  have hi (j : ℤ) :
      ((j : ℝ) * η ≤ Real.log (d * q : ℕ) ∧
        Real.log (d * q : ℕ) < ((j : ℝ) + 1) * η) ↔
        paddingBin η 0 (Real.log (d * q : ℕ)) = j := by
    simpa only [add_zero] using
      (paddingBin_eq_iff η 0 (Real.log (d * q : ℕ)) j hη).symm
  simp only [hi, PaddingPairEligible]
  by_cases hc : (q.primeFactors.card : ℝ) ≤ 100 * Real.log L
  · simp [hc]
  · simp [hc]

lemma totalPaddingBinMass_eq (D Q : Finset ℕ) (L η : ℝ) (hη : 0 < η) :
    totalPaddingBinMass D Q L η = ∑ d ∈ D, paddingPairHarmonicMass Q L η d := by
  unfold totalPaddingBinMass paddingPairHarmonicMass
  rw [sum_comm]
  apply sum_congr rfl
  intro d _
  rw [sum_comm]
  apply sum_congr rfl
  intro q _
  exact padding_bin_weight_sum L η d q hη

lemma paddingPairHarmonicMass_probability (Q : Finset ℕ)
    (hQ : ∀ p ∈ Q, p.Prime) (L η : ℝ) (d : ℕ) :
    paddingPairHarmonicMass Q L η d =
      (paddingTiltNormalizer Q / d) * (reciprocalPaddingLaw Q).probability
        (fun b => PaddingPairEligible L η d (paddingSelectedDivisor Q b)) := by
  let T : ℝ := ∑ q ∈ retainedPrimeDivisors Q,
    ((4 : ℝ) ^ q.primeFactors.card / (q : ℝ)) *
      (if PaddingPairEligible L η d q then 1 else 0)
  have hP := reciprocal_padding_average Q hQ
    (fun q => if PaddingPairEligible L η d q then 1 else 0)
  change (reciprocalPaddingLaw Q).probability
    (fun b => PaddingPairEligible L η d (paddingSelectedDivisor Q b)) =
      (paddingTiltNormalizer Q)⁻¹ * T at hP
  have he : paddingPairHarmonicMass Q L η d = (1 / (d : ℝ)) * T := by
    unfold paddingPairHarmonicMass T
    rw [mul_sum]
    apply sum_congr rfl
    intro q _
    by_cases h : PaddingPairEligible L η d q
    · simp only [if_pos h, mul_one, Nat.cast_mul]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    · simp only [if_neg h, mul_zero]
  rw [he, hP]
  have hS := paddingTiltNormalizer_pos Q
  simp only [div_eq_mul_inv, one_mul]
  symm
  calc
    _ = (paddingTiltNormalizer Q * (paddingTiltNormalizer Q)⁻¹) *
        ((d : ℝ)⁻¹ * T) := by ring
    _ = _ := by rw [mul_inv_cancel₀ hS.ne', one_mul]

lemma paddingPairHarmonicMass_bounds (Q : Finset ℕ)
    (hQ : ∀ p ∈ Q, p.Prime) {L η : ℝ} (hη : 0 < η)
    (hhalf : (1 / 2 : ℝ) ≤ (reciprocalPaddingLaw Q).probability
      (fun b => booleanCount b ≤ 100 * Real.log L ∧ paddingLog Q b ≤ 98 * L))
    (d : ℕ) (hd : 0 < d) (hdL : Real.log d ≤ 2 * L) :
    (paddingTiltNormalizer Q / d) * (1 / 2) ≤ paddingPairHarmonicMass Q L η d ∧
      paddingPairHarmonicMass Q L η d ≤ paddingTiltNormalizer Q / d := by
  rw [paddingPairHarmonicMass_probability Q hQ]
  have hfactor : 0 ≤ paddingTiltNormalizer Q / (d : ℝ) :=
    div_nonneg (paddingTiltNormalizer_pos Q).le (Nat.cast_nonneg d)
  constructor
  · exact mul_le_mul_of_nonneg_left
      (reciprocal_padding_eligible_probability Q hQ hη hhalf d hd hdL) hfactor
  · exact (mul_le_mul_of_nonneg_left
      ((reciprocalPaddingLaw Q).probability_le_one _) hfactor).trans_eq (mul_one _)

theorem totalPaddingBinMass_bounds (D Q : Finset ℕ)
    (hQ : ∀ p ∈ Q, p.Prime) {L η : ℝ} (hη : 0 < η)
    (hhalf : (1 / 2 : ℝ) ≤ (reciprocalPaddingLaw Q).probability
      (fun b => booleanCount b ≤ 100 * Real.log L ∧ paddingLog Q b ≤ 98 * L))
    (hD : ∀ d ∈ D, 0 < d ∧ Real.log d ≤ 2 * L) :
    (1 / 2 : ℝ) * paddingTiltNormalizer Q * (∑ d ∈ D, 1 / (d : ℝ)) ≤
        totalPaddingBinMass D Q L η ∧
      totalPaddingBinMass D Q L η ≤
        paddingTiltNormalizer Q * (∑ d ∈ D, 1 / (d : ℝ)) := by
  rw [totalPaddingBinMass_eq D Q L η hη]
  have hl : (1 / 2 : ℝ) * paddingTiltNormalizer Q * (∑ d ∈ D, 1 / (d : ℝ)) =
      ∑ d ∈ D, (paddingTiltNormalizer Q / d) * (1 / 2) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro d _
    ring
  have hu : paddingTiltNormalizer Q * (∑ d ∈ D, 1 / (d : ℝ)) =
      ∑ d ∈ D, paddingTiltNormalizer Q / d := by
    rw [mul_sum]
    apply sum_congr rfl
    intro d _
    ring
  rw [hl, hu]
  constructor
  · exact sum_le_sum fun d hd =>
      (paddingPairHarmonicMass_bounds Q hQ hη hhalf d (hD d hd).1 (hD d hd).2).1
  · exact sum_le_sum fun d hd =>
      (paddingPairHarmonicMass_bounds Q hQ hη hhalf d (hD d hd).1 (hD d hd).2).2

/-- The manuscript's retained bin mass bound, uniform over every finite
centered divisor family with the proved logarithmic size restriction. -/
theorem ModFiveThetaInput.eventually_totalPaddingBinMass (hP : ModFiveThetaInput)
    (E : Finset ℕ) :
    ∀ᶠ L : ℝ in atTop, ∀ (D : Finset ℕ) (η : ℝ), 0 < η →
      (∀ d ∈ D, 0 < d ∧ Real.log d ≤ 2 * L) →
      (1 / 2 : ℝ) * paddingTiltNormalizer (paddingPrimeSupply E L) *
          (∑ d ∈ D, 1 / (d : ℝ)) ≤ totalPaddingBinMass D (paddingPrimeSupply E L) L η ∧
        totalPaddingBinMass D (paddingPrimeSupply E L) L η ≤
          paddingTiltNormalizer (paddingPrimeSupply E L) * (∑ d ∈ D, 1 / (d : ℝ)) := by
  filter_upwards [hP.eventually_retained_padding_probability E] with L hL
  intro D η hη hD
  exact totalPaddingBinMass_bounds D _ (fun _ hp => paddingPrimeSupply_prime hp) hη hL hD

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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PrimeTupleMass
namespace OAI

/-! The centered divisor family is the actual image of one prime choice
from each disjoint band. Its harmonic mass has no representation
multiplicity and is exactly the product of the band masses. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical


lemma primeTupleDivisors_mass {J : ℕ} (P : Fin J → Finset ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l)) :
    (∑ d ∈ primeTupleDivisors P, 1 / (d : ℝ)) =
      ∏ j, ∑ p ∈ P j, 1 / (p : ℝ) := by
  rw [primeTupleDivisors, sum_image]
  · calc
      _ = ∑ x : (j : Fin J) → P j, ∏ j, 1 / ((x j).val : ℝ) := by
        apply sum_congr rfl
        intro x _
        simp only [Nat.cast_prod, one_div, prod_inv_distrib]
      _ = ∏ j, ∑ p : P j, 1 / (p.val : ℝ) :=
        (Fintype.prod_sum (fun j (p : P j) => 1 / (p.val : ℝ))).symm
      _ = _ := by
        apply prod_congr rfl
        intro j _
        exact sum_coe_sort (P j) (fun p : ℕ => 1 / (p : ℝ))
  · intro x _ y _ hxy
    exact primeTuple_injective hprime hdisjoint hxy

lemma centeredPrimeTuple_log_bound {E : Finset ℕ} {A W L : ℝ}
    (hA : 0 < A) (hW : 1 ≤ W) {J : ℕ} (hL : primeSupplyEndpoint A W J ≤ L)
    {d : ℕ} (hd : d ∈ primeTupleDivisors (fun j : Fin J => centeredPrimeSupply E A W j)) :
    0 < d ∧ Real.log d ≤ 2 * L := by
  obtain ⟨x, _, rfl⟩ := mem_image.mp hd
  constructor
  · exact prod_pos fun j _ => (centeredPrimeSupply_mem (x j).property).1.pos
  · exact (centeredPrimeSupply_tuple_log_bound hA hW hL
      (fun j => (x j).val) (fun j => (x j).property)).le




end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PrimeTuplePool
namespace OAI

/-! Arithmetic support of the actual one-prime-per-band tuple family. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical




lemma primeHarmonicMass_eq_sum (S : Finset ℕ) :
    primeHarmonicMass S = ∑ p ∈ S, 1 / (p : ℝ) := by
  unfold primeHarmonicMass
  simpa only [one_div] using sum_coe_sort S (fun p : ℕ => 1 / (p : ℝ))








end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.CanonicalRetainedMass
namespace OAI

/-! The retained divisor bins carry at least half the original harmonic
mass, and the exact tuple mass is at least W^J. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical

theorem ModFiveThetaInput.eventually_canonical_retained_mass
    (hprime : ModFiveThetaInput) (E : Finset ℕ) (W : ℝ) (hW : 1 ≤ W) :
    ∀ᶠ L : ℝ in atTop, ∀ (_hL : 1 ≤ L) (η : ℝ), 0 < η →
      let J := primeSupplyCount W L
      let P := centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W J
      let V := ∏ j, primeHarmonicMass (P j)
      W ^ J ≤ V ∧
        paddingTiltNormalizer (paddingPrimeSupply E L) * V / 2 ≤
          totalPaddingBinMass (primeTupleDivisors P) (paddingPrimeSupply E L) L η := by
  filter_upwards [hprime.eventually_actual_prime_supplies E W hW,
    hprime.eventually_totalPaddingBinMass E] with L hs hm
  intro hL η hη
  dsimp only
  let J := primeSupplyCount W L
  let P := centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W J
  have hp : ∀ j, ∀ p ∈ P j, p.Prime := centeredPrimeBands_prime _ _ _ _
  have hd : ∀ j l, l ≠ j → Disjoint (P j) (P l) :=
    centeredPrimeBands_disjoint _ _ _ _ (Real.rpow_nonneg (by linarith) _) (by linarith)
  have hmass (j : Fin J) : W ≤ primeHarmonicMass (P j) := by
    simpa only [primeHarmonicMass_eq_sum, P, centeredPrimeBands] using (hs.2.2 j.val).2.1
  constructor
  · calc
      W ^ J = ∏ _j : Fin J, W := by simp
      _ ≤ _ := Finset.prod_le_prod (fun _ _ => by linarith) (fun j _ => hmass j)
  · have ht := (hm (primeTupleDivisors P) η hη (fun d hd =>
        centeredPrimeTuple_log_bound (Real.rpow_pos_of_pos (by linarith) _) hW
          (primeSupplyScale_endpoint W L (by linarith) hL) hd)).1
    rw [primeTupleDivisors_mass P hp hd] at ht
    have he : (∏ j, ∑ p ∈ P j, 1 / (p : ℝ)) = ∏ j, primeHarmonicMass (P j) := by
      simp only [primeHarmonicMass_eq_sum]
    rw [he] at ht
    linarith

end TwoPointCorrelations

end OAI

end

theorem solution : type_of% @OAI.TwoPointCorrelations.ModFiveThetaInput.eventually_canonical_retained_mass := @OAI.TwoPointCorrelations.ModFiveThetaInput.eventually_canonical_retained_mass
