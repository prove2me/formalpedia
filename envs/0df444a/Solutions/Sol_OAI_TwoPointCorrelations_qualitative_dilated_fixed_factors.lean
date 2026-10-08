-- Prove2me | solution 1 for OAI.TwoPointCorrelations.qualitative_dilated_fixed_factors
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T02:51:01.150058+00:00
-- url     : https://prove2.me/submissions/b08edb0d-0c79-41e0-98ba-7e73a0491d94

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs
import Theorems.Thm_OAI_TwoPointCorrelations_MRTShortExponentialInput_dilated_forward_windows
import Theorems.Thm_OAI_TwoPointCorrelations_PrimeReciprocalInput_qualitative_rough_fourier

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Basic
namespace OAI

/-!
# Ordinary two-point correlations: concrete sums and affine transfer

Definitions follow the introduction of the supplied manuscript
*Ordinary two-point correlations of multiplicative functions* (September 24, 2026).
The exact Liouville identities below are the algebraic part of §8.
No cancellation estimate is assumed or asserted here.
-/

open scoped _root_.BigOperators

namespace TwoPointCorrelations







@[simp] theorem liouville_mul (m n : ℕ) :
    liouville (m * n) = liouville m * liouville n := by
  simp [liouville, ArithmeticFunction.liouville_apply_mul]

@[simp] theorem liouville_sq {n : ℕ} (hn : n ≠ 0) : liouville n ^ 2 = 1 := by
  have h : (ArithmeticFunction.liouville n) ^ 2 = (1 : ℤ) := by
    rw [ArithmeticFunction.liouville_apply hn, ← pow_mul, Nat.mul_comm _ 2, pow_mul]
    norm_num
  unfold liouville
  exact_mod_cast h





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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.RoughShiftBoundary
namespace OAI

/-!
# The endpoint error in the rough-shift averaging argument

These are finite identities and bounds from the proof of (q:rough-shifts)
in quantitative/03-analytic.tex. No short-sum or sieve estimate is assumed.
The averages below use the positive integers `1,...,Y` and translations
`1,...,D`; the resulting error is at most `2D/Y` times the total weight.
-/

namespace TwoPointCorrelations

open scoped _root_.BigOperators



theorem positivePrefix_translate_identity (u : ℕ → ℂ) (Y m : ℕ) :
    positivePrefix (fun n => u (n + m)) Y - positivePrefix u Y =
      positivePrefix (fun n => u (n + Y)) m - positivePrefix u m := by
  have hsplit : positivePrefix u Y + positivePrefix (fun n => u (n + Y)) m =
      positivePrefix u m + positivePrefix (fun n => u (n + m)) Y := by
    have h₁ : positivePrefix u (Y + m) =
        positivePrefix u Y + positivePrefix (fun n => u (n + Y)) m := by
      simpa only [positivePrefix, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        Finset.sum_range_add (fun n => u (n + 1)) Y m
    have h₂ : positivePrefix u (m + Y) =
        positivePrefix u m + positivePrefix (fun n => u (n + m)) Y := by
      simpa only [positivePrefix, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        Finset.sum_range_add (fun n => u (n + 1)) m Y
    exact h₁.symm.trans ((congrArg (positivePrefix u) (Nat.add_comm Y m)).trans h₂)
  linear_combination -hsplit

theorem norm_positivePrefix_le (u : ℕ → ℂ) (Y : ℕ) (B : ℝ)
    (hu : ∀ n, 0 < n → ‖u n‖ ≤ B) : ‖positivePrefix u Y‖ ≤ Y * B := by
  calc
    _ ≤ ∑ v ∈ Finset.range Y, ‖u (v + 1)‖ := norm_sum_le _ _
    _ ≤ ∑ _v ∈ Finset.range Y, B :=
      Finset.sum_le_sum (fun v _ => hu (v + 1) (by omega))
    _ = _ := by simp

/-- Translating by `m` loses at most `m` terms at each endpoint. No relation
between the prefix length and the translation is needed. -/
theorem norm_positivePrefix_translate_sub_le (u : ℕ → ℂ) (Y m : ℕ) (B : ℝ)
    (hu : ∀ n, 0 < n → ‖u n‖ ≤ B) :
    ‖positivePrefix (fun n => u (n + m)) Y - positivePrefix u Y‖ ≤ 2 * m * B := by
  rw [positivePrefix_translate_identity]
  calc
    _ ≤ ‖positivePrefix (fun n => u (n + Y)) m‖ + ‖positivePrefix u m‖ :=
      norm_sub_le _ _
    _ ≤ (m : ℝ) * B + m * B := add_le_add
      (norm_positivePrefix_le _ _ _ (fun n hn => hu _ (by omega)))
      (norm_positivePrefix_le _ _ _ hu)
    _ = _ := by ring

/-- Averaging positive translations has the same finite endpoint bound. -/
theorem norm_translatedPrefixAverage_sub_le (u : ℕ → ℂ) (Y D : ℕ)
    (hD : 0 < D) (B : ℝ) (hB : 0 ≤ B)
    (hu : ∀ n, 0 < n → ‖u n‖ ≤ B) :
    ‖translatedPrefixAverage u Y D - positivePrefix u Y‖ ≤ 2 * D * B := by
  have hDc : (D : ℂ) ≠ 0 := by exact_mod_cast hD.ne'
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have heq : translatedPrefixAverage u Y D - positivePrefix u Y =
      (D : ℂ)⁻¹ * ∑ m ∈ Finset.range D,
        (positivePrefix (fun n => u (n + (m + 1))) Y - positivePrefix u Y) := by
    simp only [translatedPrefixAverage, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul, mul_sub]
    field_simp
  rw [heq, norm_mul, norm_inv, Complex.norm_natCast]
  calc
    _ ≤ (D : ℝ)⁻¹ * ∑ m ∈ Finset.range D,
        ‖positivePrefix (fun n => u (n + (m + 1))) Y - positivePrefix u Y‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr hDr.le)
    _ ≤ (D : ℝ)⁻¹ * ∑ _m ∈ Finset.range D, (2 * D * B) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hDr.le)
      apply Finset.sum_le_sum
      intro m hm
      apply (norm_positivePrefix_translate_sub_le u Y (m + 1) B hu).trans
      have hmD : ((m + 1 : ℕ) : ℝ) ≤ D := by
        exact_mod_cast (Nat.succ_le_of_lt (Finset.mem_range.mp hm))
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hmD (by norm_num : (0 : ℝ) ≤ 2)) hB
    _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; field_simp

/-- The normalized endpoint error, in exactly the `D/Y` scale used in
the rough-shift lemma. -/
theorem norm_normalized_translation_error (u : ℕ → ℂ) (Y D : ℕ)
    (hY : 0 < Y) (hD : 0 < D) (B : ℝ) (hB : 0 ≤ B)
    (hu : ∀ n, 0 < n → ‖u n‖ ≤ B) :
    ‖(translatedPrefixAverage u Y D - positivePrefix u Y) / (Y : ℂ)‖ ≤
      2 * (D : ℝ) / Y * B := by
  rw [norm_div, Complex.norm_natCast]
  have hYr : (0 : ℝ) < Y := by exact_mod_cast hY
  apply (div_le_div_of_nonneg_right
    (norm_translatedPrefixAverage_sub_le u Y D hD B hB hu) hYr.le).trans
  exact le_of_eq (by ring)


theorem norm_weightedShiftProfile_le {ι : Type*} (Z : Finset ι) (w : ι → ℂ)
    (shift : ι → ℕ) (f g : ℕ → ℂ) (hf : OneBounded f) (hg : OneBounded g)
    (l b n : ℕ) (hn : 0 < n) :
    ‖weightedShiftProfile Z w shift f g l b n‖ ≤ ∑ z ∈ Z, ‖w z‖ := by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro z _
  by_cases hmod : n % l = b % l
  · simp only [hmod, ite_true, norm_mul]
    have hprod := mul_le_mul (hf n hn) (hg _ (by omega))
      (norm_nonneg (g (n + shift z))) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hprod (norm_nonneg (w z))
  · simp only [hmod, ite_false, mul_zero, norm_zero]
    exact norm_nonneg _


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.QualitativeShiftScale
namespace OAI

/-! Final scale arithmetic in the qualitative rough-shift estimate. -/

namespace TwoPointCorrelations

open _root_.Filter


lemma eventually_qualitative_interval_lower :
    ∀ᶠ B : ℝ in atTop, ∀ D : ℕ,
      (1 / 2 : ℝ) * Real.exp (B ^ (9999 / 10000 : ℝ)) ≤ D → 10 ≤ D := by
  have hh := ((Real.tendsto_exp_atTop.comp
    (tendsto_rpow_atTop (show 0 < (9999 / 10000 : ℝ) by norm_num))).const_mul_atTop
      (show 0 < (1 / 2 : ℝ) by norm_num)).eventually (eventually_ge_atTop 10)
  filter_upwards [hh] with B hb
  intro D hD
  exact_mod_cast hb.trans hD

lemma eventually_fixed_interval_endpoint (D : ℕ) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ Y : ℕ in atTop, 0 < Y ∧ (D : ℝ) / Y ≤ η := by
  have hb : ∀ᶠ Y : ℕ in atTop, (D : ℝ) / η ≤ Y :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually (eventually_ge_atTop _)
  filter_upwards [hb, eventually_ge_atTop 1] with Y hy hY
  refine ⟨by omega, ?_⟩
  have hYr : (0 : ℝ) < Y := by exact_mod_cast (show 0 < Y by omega)
  apply (div_le_iff₀ hYr).mpr
  have ht := (div_le_iff₀ hη).mp hy
  nlinarith only [ht]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.QualitativeStrongScale
namespace OAI

/-! Final scale arithmetic in the qualitative rough-shift estimate. -/

namespace TwoPointCorrelations

open _root_.Filter

lemma eventually_strong_qualitative_frequency_gap :
    ∀ᶠ B : ℝ in atTop,
      (Real.log B / B ^ (9999 / 10000 : ℝ)) ^ (6 : ℕ) ≤
        (B ^ (-11 / 10 : ℝ)) ^ (5 : ℕ) := by
  have hs := (isLittleO_log_rpow_atTop
    (show 0 < (1 / 20 : ℝ) by norm_num)).bound (show 0 < (1 : ℝ) by norm_num)
  filter_upwards [eventually_ge_atTop 1, hs] with B hB hb
  have hBp : 0 < B := zero_lt_one.trans_le hB
  have hlog : 0 ≤ Real.log B := Real.log_nonneg hB
  rw [Real.norm_eq_abs, abs_of_nonneg hlog, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos hBp _), one_mul] at hb
  have hq : Real.log B / B ^ (9999 / 10000 : ℝ) ≤ B ^ (-9499 / 10000 : ℝ) := by
    calc
      _ ≤ B ^ (1 / 20 : ℝ) / B ^ (9999 / 10000 : ℝ) :=
        div_le_div_of_nonneg_right hb (by positivity)
      _ = _ := by rw [← Real.rpow_sub hBp]; norm_num
  calc
    _ ≤ (B ^ (-9499 / 10000 : ℝ)) ^ (6 : ℕ) :=
      pow_le_pow_left₀ (by positivity) hq 6
    _ = B ^ (-28497 / 5000 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hBp.le]
      norm_num
    _ ≤ B ^ (-11 / 2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hB (by norm_num)
    _ = _ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hBp.le]
      norm_num

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.SmoothProductBounds
namespace OAI

/-! Elementary bounds for the Euler cost of adjoining retained tuple primes. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma one_le_smoothReciprocalProduct (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (s : ℝ) (hs : 0 < s) :
    1 ≤ smoothReciprocalProduct P s := by
  apply Finset.one_le_prod
  intro p hp
  have hr : (p : ℝ) ^ (-s) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast (hP p hp).one_lt) (by linarith)
  exact (one_le_inv₀ (sub_pos.mpr hr)).mpr (by
    have hh := Real.rpow_nonneg (Nat.cast_nonneg p) (-s)
    linarith)






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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.RoughFourier
namespace OAI

/-!
# Exact finite Fourier identities for rough shifts

Orthogonality, convolution and the fourth moment are proved for arbitrary
finite coefficients. The sieve bounds on the number of rough integers are
not hypotheses of these identities. Haar measure on `AddCircle (1 : ℝ)` is the
ordinary integral over one period.
-/

namespace TwoPointCorrelations

open scoped _root_.BigOperators _root_.ComplexConjugate
open _root_.MeasureTheory


theorem continuous_fourierPolynomial {ι : Type*} (S : Finset ι)
    (frequency : ι → ℤ) (coefficient : ι → ℂ) :
    Continuous (fourierPolynomial S frequency coefficient) := by
  unfold fourierPolynomial
  exact continuous_finsetSum S (fun i _ =>
    continuous_const.mul (fourier (frequency i)).continuous)


theorem integral_fourier_character (n : ℤ) :
    (∫ θ : AddCircle (1 : ℝ), fourier n θ ∂AddCircle.haarAddCircle) =
      if n = 0 then 1 else 0 := by
  have h := congrFun (fourierCoeff_fourier (T := 1) n) 0
  simpa [fourierCoeff, Pi.single_apply, eq_comm] using h

theorem integrable_fourier_character (n : ℤ) :
    Integrable (fun θ : AddCircle (1 : ℝ) => fourier n θ)
      AddCircle.haarAddCircle := by
  simpa only [smul_eq_mul, mul_one] using
    (integrable_const (1 : ℂ) (μ := (AddCircle.haarAddCircle : Measure (AddCircle (1 : ℝ))))).fourier_smul n

theorem integral_fourierPolynomial {ι : Type*} (S : Finset ι)
    (frequency : ι → ℤ) (coefficient : ι → ℂ) :
    (∫ θ, fourierPolynomial S frequency coefficient θ ∂AddCircle.haarAddCircle) =
      ∑ i ∈ S, if frequency i = 0 then coefficient i else 0 := by
  classical
  unfold fourierPolynomial
  rw [integral_finsetSum S (fun i _ =>
    (integrable_fourier_character (frequency i)).const_mul (coefficient i))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_const_mul, integral_fourier_character]
  split_ifs <;> simp_all

theorem norm_fourierPolynomial_le {ι : Type*} (S : Finset ι)
    (frequency : ι → ℤ) (coefficient : ι → ℂ) (θ : AddCircle (1 : ℝ)) :
    ‖fourierPolynomial S frequency coefficient θ‖ ≤ ∑ i ∈ S, ‖coefficient i‖ := by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  simp only [norm_mul, fourier_apply, Circle.norm_coe, mul_one, le_refl]

theorem fourierPolynomial_mul {ι κ : Type*} (S : Finset ι) (T : Finset κ)
    (f : ι → ℤ) (g : κ → ℤ) (a : ι → ℂ) (b : κ → ℂ) (θ : AddCircle (1 : ℝ)) :
    fourierPolynomial S f a θ * fourierPolynomial T g b θ =
      fourierPolynomial (S ×ˢ T) (fun i => f i.1 + g i.2)
        (fun i => a i.1 * b i.2) θ := by
  classical
  simp only [fourierPolynomial, Finset.sum_product, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [fourier_add]
  ring

theorem fourierPolynomial_conj {ι : Type*} (S : Finset ι)
    (f : ι → ℤ) (a : ι → ℂ) (θ : AddCircle (1 : ℝ)) :
    conj (fourierPolynomial S f a θ) =
      fourierPolynomial S (fun i => -f i) (fun i => conj (a i)) θ := by
  simp only [fourierPolynomial, map_sum, map_mul, fourier_neg]

/-- Exact Fourier selection of all frequency-zero terms in a product. -/
theorem integral_fourier_product {ι κ : Type*} (S : Finset ι) (T : Finset κ)
    (f : ι → ℤ) (g : κ → ℤ) (a : ι → ℂ) (b : κ → ℂ) :
    (∫ θ, fourierPolynomial S f a θ * fourierPolynomial T g b θ
        ∂AddCircle.haarAddCircle) =
      ∑ i ∈ S ×ˢ T, if f i.1 + g i.2 = 0 then a i.1 * b i.2 else 0 := by
  simp_rw [fourierPolynomial_mul]
  exact integral_fourierPolynomial _ _ _

/-- Parseval for finite polynomials, retaining collisions of frequencies. -/
theorem integral_norm_fourierPolynomial_sq {ι : Type*} (S : Finset ι)
    (f : ι → ℤ) (a : ι → ℂ) :
    (∫ θ, ‖fourierPolynomial S f a θ‖ ^ 2 ∂AddCircle.haarAddCircle) =
      ∑ i ∈ S ×ˢ S, if f i.1 = f i.2 then (a i.1 * conj (a i.2)).re else 0 := by
  classical
  have hc : ((∫ θ, ‖fourierPolynomial S f a θ‖ ^ 2
        ∂AddCircle.haarAddCircle : ℝ) : ℂ) =
      ∑ i ∈ S ×ˢ S, if f i.1 = f i.2 then a i.1 * conj (a i.2) else 0 := by
    rw [← integral_complex_ofReal]
    simp_rw [Complex.ofReal_pow, ← Complex.mul_conj', fourierPolynomial_conj]
    rw [integral_fourier_product]
    apply Finset.sum_congr rfl
    intro i _
    simp only [add_neg_eq_zero]
  have hr := congrArg Complex.re hc
  simpa only [Complex.ofReal_re, Complex.re_sum, apply_ite, Complex.zero_re] using hr






end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.FourierRegionBound
namespace OAI

/-!
# The low/high Fourier split

The short-sum bound is uniform at a fixed frequency. It is applied after
summing the origins, and no supremum is moved through an integral.
-/

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.Classical

private lemma circle_integrable {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : AddCircle (1 : ℝ) → E) (hf : Continuous f) :
    Integrable f AddCircle.haarAddCircle :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

lemma circle_integral_mul_norm_le (F G : AddCircle (1 : ℝ) → ℂ)
    (hF : Continuous F) (hG : Continuous G) :
    (∫ θ, ‖F θ‖ * ‖G θ‖ ∂AddCircle.haarAddCircle) ≤
      Real.sqrt (∫ θ, ‖F θ‖ ^ 2 ∂AddCircle.haarAddCircle) *
        Real.sqrt (∫ θ, ‖G θ‖ ^ 2 ∂AddCircle.haarAddCircle) := by
  have hf : MemLp F (ENNReal.ofReal (2 : ℝ)) AddCircle.haarAddCircle :=
    hF.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hg : MemLp G (ENNReal.ofReal (2 : ℝ)) AddCircle.haarAddCircle :=
    hG.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hh := integral_mul_norm_le_Lp_mul_Lq
    (show (2 : ℝ).HolderConjugate 2 by norm_num [Real.holderConjugate_iff]) hf hg
  simpa only [Real.rpow_two, Real.sqrt_eq_rpow, one_div] using hh

private lemma fourier_pointwise_split {ι : Type*} (S : Finset ι)
    (B : AddCircle (1 : ℝ) → ℂ) (F G : ι → AddCircle (1 : ℝ) → ℂ)
    (ε Bmax Gmax K : ℝ) (hε : 0 < ε)
    (hBmax : 0 ≤ Bmax) (hGmax : 0 ≤ Gmax) (hK : 0 ≤ K)
    (hBbound : ∀ θ, ‖B θ‖ ≤ Bmax)
    (hGbound : ∀ v ∈ S, ∀ θ, ‖G v θ‖ ≤ Gmax)
    (hFsum : ∀ θ, (∑ v ∈ S, ‖F v θ‖) ≤ K) (θ : AddCircle (1 : ℝ)) :
    (∑ v ∈ S, ‖B θ‖ * ‖F v θ‖ * ‖G v θ‖) ≤
      ε * (∑ v ∈ S, ‖F v θ‖ * ‖G v θ‖) +
        (Bmax * Gmax * K / ε ^ 4) * ‖B θ‖ ^ 4 := by
  let A (θ : AddCircle (1 : ℝ)) := ∑ v ∈ S, ‖F v θ‖ * ‖G v θ‖
  let C : ℝ := Bmax * Gmax * K / ε ^ 4
  have hC : 0 ≤ C := by dsimp [C]; positivity
  by_cases ht : ‖B θ‖ ≤ ε
  · calc
      _ ≤ ∑ v ∈ S, ε * (‖F v θ‖ * ‖G v θ‖) := by
        apply sum_le_sum
        intro v _
        calc
          _ = ‖B θ‖ * (‖F v θ‖ * ‖G v θ‖) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_right ht
            (mul_nonneg (norm_nonneg (F v θ)) (norm_nonneg (G v θ)))
      _ = ε * A θ := by simp only [A, mul_sum]
      _ ≤ _ := le_add_of_nonneg_right (mul_nonneg hC (by positivity))
  · have hs : (∑ v ∈ S, ‖B θ‖ * ‖F v θ‖ * ‖G v θ‖) ≤ Bmax * Gmax * K := by
      calc
        _ ≤ ∑ v ∈ S, Bmax * Gmax * ‖F v θ‖ := by
          apply sum_le_sum
          intro v hv
          have hh := mul_le_mul (hBbound θ) (hGbound v hv θ)
            (norm_nonneg _) hBmax
          calc
            _ = (‖B θ‖ * ‖G v θ‖) * ‖F v θ‖ := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_right hh (norm_nonneg (F v θ))
        _ = Bmax * Gmax * ∑ v ∈ S, ‖F v θ‖ := (mul_sum _ _ _).symm
        _ ≤ _ := mul_le_mul_of_nonneg_left (hFsum θ) (mul_nonneg hBmax hGmax)
    have hp : ε ^ 4 ≤ ‖B θ‖ ^ 4 :=
      pow_le_pow_left₀ hε.le (le_of_lt (lt_of_not_ge ht)) 4
    have hc : Bmax * Gmax * K ≤ C * ‖B θ‖ ^ 4 := by
      dsimp [C]
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ (pow_pos hε 4)).mpr
      exact mul_le_mul_of_nonneg_left hp (mul_nonneg (mul_nonneg hBmax hGmax) hK)
    exact hs.trans (hc.trans (le_add_of_nonneg_left (mul_nonneg hε.le
      (sum_nonneg (fun v _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))))))


private lemma norm_sum_circle_integral_le {ι : Type*} (S : Finset ι)
    (U : ι → AddCircle (1 : ℝ) → ℂ) (hU : ∀ v ∈ S, Continuous (U v)) :
    ‖∑ v ∈ S, ∫ θ, U v θ ∂AddCircle.haarAddCircle‖ ≤
      ∫ θ, ∑ v ∈ S, ‖U v θ‖ ∂AddCircle.haarAddCircle := by
  calc
    _ ≤ ∑ v ∈ S, ‖∫ θ, U v θ ∂AddCircle.haarAddCircle‖ := norm_sum_le _ _
    _ ≤ ∑ v ∈ S, ∫ θ, ‖U v θ‖ ∂AddCircle.haarAddCircle := by
      exact sum_le_sum (fun v _ => norm_integral_le_integral_norm (U v))
    _ = _ := by
      rw [integral_finsetSum S (f := fun v θ => ‖U v θ‖)
        (fun v hv => (circle_integrable (U v) (hU v hv)).norm)]

private lemma circle_integral_sum_mul_norm_le {ι : Type*} (S : Finset ι)
    (F G : ι → AddCircle (1 : ℝ) → ℂ)
    (hF : ∀ v ∈ S, Continuous (F v)) (hG : ∀ v ∈ S, Continuous (G v)) :
    (∫ θ, ∑ v ∈ S, ‖F v θ‖ * ‖G v θ‖ ∂AddCircle.haarAddCircle) ≤
      ∑ v ∈ S, Real.sqrt (∫ θ, ‖F v θ‖ ^ 2 ∂AddCircle.haarAddCircle) *
        Real.sqrt (∫ θ, ‖G v θ‖ ^ 2 ∂AddCircle.haarAddCircle) := by
  rw [integral_finsetSum S (f := fun v θ => ‖F v θ‖ * ‖G v θ‖)
    (fun v hv => circle_integrable _ ((hF v hv).norm.mul (hG v hv).norm))]
  exact sum_le_sum (fun v hv => circle_integral_mul_norm_le _ _ (hF v hv) (hG v hv))

private lemma circle_integral_linear_bound
    (P A B : AddCircle (1 : ℝ) → ℝ) (hP : Continuous P) (hA : Continuous A)
    (hB : Continuous B) (ε C : ℝ) (hpoint : ∀ θ, P θ ≤ ε * A θ + C * B θ) :
    (∫ θ, P θ ∂AddCircle.haarAddCircle) ≤
      ε * (∫ θ, A θ ∂AddCircle.haarAddCircle) +
        C * ∫ θ, B θ ∂AddCircle.haarAddCircle := by
  have hl : Integrable (fun θ => ε * A θ) AddCircle.haarAddCircle :=
    (circle_integrable _ hA).const_mul _
  have hr : Integrable (fun θ => C * B θ) AddCircle.haarAddCircle :=
    (circle_integrable _ hB).const_mul _
  calc
    _ ≤ ∫ θ, ε * A θ + C * B θ ∂AddCircle.haarAddCircle :=
      integral_mono (circle_integrable _ hP) (hl.add hr) hpoint
    _ = _ := by rw [integral_add hl hr, integral_const_mul, integral_const_mul]

private lemma circle_integrate_pointwise_split {ι : Type*} (S : Finset ι)
    (B : AddCircle (1 : ℝ) → ℂ) (F G : ι → AddCircle (1 : ℝ) → ℂ)
    (hB : Continuous B) (hF : ∀ v ∈ S, Continuous (F v))
    (hG : ∀ v ∈ S, Continuous (G v)) (ε C : ℝ)
    (hpoint : ∀ θ, (∑ v ∈ S, ‖B θ‖ * ‖F v θ‖ * ‖G v θ‖) ≤
      ε * (∑ v ∈ S, ‖F v θ‖ * ‖G v θ‖) + C * ‖B θ‖ ^ 4) :
    ‖∑ v ∈ S, ∫ θ, B θ * F v θ * G v θ ∂AddCircle.haarAddCircle‖ ≤
      ε * (∫ θ, ∑ v ∈ S, ‖F v θ‖ * ‖G v θ‖ ∂AddCircle.haarAddCircle) +
        C * ∫ θ, ‖B θ‖ ^ 4 ∂AddCircle.haarAddCircle := by
  have hnorm := norm_sum_circle_integral_le S
    (fun v θ => B θ * F v θ * G v θ)
    (fun v hv => (hB.mul (hF v hv)).mul (hG v hv))
  apply hnorm.trans
  apply circle_integral_linear_bound
    (fun θ => ∑ v ∈ S, ‖B θ * F v θ * G v θ‖)
    (fun θ => ∑ v ∈ S, ‖F v θ‖ * ‖G v θ‖)
    (fun θ => ‖B θ‖ ^ 4)
    (continuous_finsetSum S (fun v hv => ((hB.mul (hF v hv)).mul (hG v hv)).norm))
    (continuous_finsetSum S (fun v hv => (hF v hv).norm.mul (hG v hv).norm))
    (hB.norm.pow 4) ε C
  intro θ
  simpa only [norm_mul] using hpoint θ

/-- A finite-family version of the analytic split. The threshold term uses
only Cauchy--Schwarz; the complementary term uses the fourth moment and
our fixed-frequency sum over origins. -/
theorem fourier_region_bound {ι : Type*} (S : Finset ι)
    (B : AddCircle (1 : ℝ) → ℂ) (F G : ι → AddCircle (1 : ℝ) → ℂ)
    (hB : Continuous B) (hF : ∀ v ∈ S, Continuous (F v))
    (hG : ∀ v ∈ S, Continuous (G v))
    (ε Bmax Gmax K : ℝ) (hε : 0 < ε)
    (hBmax : 0 ≤ Bmax) (hGmax : 0 ≤ Gmax) (hK : 0 ≤ K)
    (hBbound : ∀ θ, ‖B θ‖ ≤ Bmax)
    (hGbound : ∀ v ∈ S, ∀ θ, ‖G v θ‖ ≤ Gmax)
    (hFsum : ∀ θ, (∑ v ∈ S, ‖F v θ‖) ≤ K) :
    ‖∑ v ∈ S, ∫ θ, B θ * F v θ * G v θ ∂AddCircle.haarAddCircle‖ ≤
      ε * ∑ v ∈ S,
        Real.sqrt (∫ θ, ‖F v θ‖ ^ 2 ∂AddCircle.haarAddCircle) *
          Real.sqrt (∫ θ, ‖G v θ‖ ^ 2 ∂AddCircle.haarAddCircle) +
      (Bmax * Gmax * K / ε ^ 4) *
        ∫ θ, ‖B θ‖ ^ 4 ∂AddCircle.haarAddCircle := by
  apply (circle_integrate_pointwise_split S B F G hB hF hG ε
    (Bmax * Gmax * K / ε ^ 4)
    (fourier_pointwise_split S B F G ε Bmax Gmax K hε hBmax hGmax hK
      hBbound hGbound hFsum)).trans
  exact add_le_add (mul_le_mul_of_nonneg_left
    (circle_integral_sum_mul_norm_le S F G hF hG) hε.le) le_rfl

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ShortSumSampling
namespace OAI

/-!
# Sampling the published short-interval estimate

For integral short lengths, a moving short sum is constant on each unit
cell of its origin. Thus its published integral controls the actual finite
sum of integer origins, with outer cutoff `Y+1`. The progression restriction
is an average of fixed frequencies and has total coefficient mass one.
-/

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.Classical






lemma sum_Icc_shift (f : ℕ → ℂ) (v D : ℕ) :
    (∑ n ∈ Icc (v + 1) (v + D), f n) = ∑ m ∈ range D, f (v + m + 1) := by
  symm
  apply sum_bij (fun m _ => v + m + 1)
  · intro m hm
    simp only [mem_range] at hm
    simp only [mem_Icc]
    omega
  · intro m hm n hn he
    omega
  · intro n hn
    simp only [mem_Icc] at hn
    refine ⟨n - (v + 1), ?_, ?_⟩
    · simp only [mem_range]
      omega
    · omega
  · intro m _
    rfl









end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.WeightedRoughFourier
namespace OAI

/-! Arbitrary bounded complex coefficients on the same rough support.
These are needed for the qualitative Fourier multiplier. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.ComplexConjugate _root_.Classical


lemma rough_coefficient_norm_le (Z : Finset ℕ) (c : ℕ → ℂ) (D : ℝ)
    (hD : 0 < D) (hZ : ∀ z ∈ Z, D ≤ (z : ℝ)) (hc : ∀ z ∈ Z, ‖c z‖ ≤ 1)
    (z : ℕ) (hz : z ∈ Z) : ‖c z / (z : ℂ)‖ ≤ D⁻¹ := by
  rw [norm_div, Complex.norm_natCast]
  calc
    _ ≤ 1 / (z : ℝ) := div_le_div_of_nonneg_right (hc z hz) (Nat.cast_nonneg _)
    _ ≤ _ := by simpa only [one_div] using inv_anti₀ hD (hZ z hz)




end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.WeightedShiftConvolution
namespace OAI

/-! Exact convolution with arbitrary complex coefficients on the rough
support. The coefficient choice is kept outside the short-sum supremum. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.Classical

/-- Orthogonality imposes precisely `a=m+hz`; the long window contains
every selected frequency, so there is no further truncation error. -/
theorem weighted_rough_shift_convolution (f g : ℕ → ℂ) (Z : Finset ℕ) (c : ℕ → ℂ) (D h v : ℕ)
    (hZ : ∀ z ∈ Z, z ≤ 2 * D) :
    (∫ θ, weightedRoughFourier Z c h θ * forwardWindowPolynomial f D v θ *
      backwardWindowPolynomial g ((2 * h + 1) * D) v θ ∂AddCircle.haarAddCircle) =
      ∑ z ∈ Z, (c z / (z : ℂ)) * ∑ m ∈ Icc 1 D, f (v + m) * g (v + m + h * z) := by
  unfold weightedRoughFourier forwardWindowPolynomial backwardWindowPolynomial
  simp_rw [fourierPolynomial_mul]
  rw [integral_fourierPolynomial]
  simp only [sum_product]
  apply sum_congr rfl
  intro z hz
  rw [mul_sum]
  apply sum_congr rfl
  intro m hm
  have hm1 : 1 ≤ m := (mem_Icc.mp hm).1
  have hmD : m ≤ D := (mem_Icc.mp hm).2
  have ha : m + h * z ∈ Icc 1 ((2 * h + 1) * D) := by
    simp only [mem_Icc]
    constructor
    · omega
    · nlinarith [Nat.mul_le_mul_left h (hZ z hz)]
  rw [sum_eq_single (m + h * z)]
  · have he : (h : ℤ) * z + m + -(↑(m + h * z) : ℤ) = 0 := by
      push_cast
      ring
    rw [if_pos he]
    rw [show v + (m + h * z) = v + m + h * z by omega]
    ring
  · intro a _ hne
    have he : ¬((h : ℤ) * z + m + -(a : ℤ) = 0) := by
      intro hh
      apply hne
      exact_mod_cast (show (a : ℤ) = m + h * z by linarith)
    exact if_neg he
  · exact fun hnot => False.elim (hnot ha)

/-- Summing the convolution identity gives the exact translated average
used before the endpoint comparison. -/
theorem summed_weighted_rough_shift_convolution (f g : ℕ → ℂ) (Z : Finset ℕ) (c : ℕ → ℂ)
    (D h Y : ℕ) (hZ : ∀ z ∈ Z, z ≤ 2 * D) :
    (∑ v ∈ range Y, ∫ θ,
      weightedRoughFourier Z c h θ * forwardWindowPolynomial f D (v + 1) θ *
      backwardWindowPolynomial g ((2 * h + 1) * D) (v + 1) θ
        ∂AddCircle.haarAddCircle) =
      ∑ m ∈ Icc 1 D, ∑ v ∈ range Y, ∑ z ∈ Z,
        (c z / (z : ℂ)) * (f (v + 1 + m) * g (v + 1 + m + h * z)) := by
  simp_rw [weighted_rough_shift_convolution f g Z c D h _ hZ, mul_sum]
  calc
    _ = ∑ v ∈ range Y, ∑ m ∈ Icc 1 D, ∑ z ∈ Z,
        (c z / (z : ℂ)) * (f (v + 1 + m) * g (v + 1 + m + h * z)) := by
      apply sum_congr rfl
      intro v _
      rw [sum_comm]
    _ = _ := sum_comm

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.WindowPolynomialBounds
namespace OAI

/-! Concrete Parseval and short-sum bounds for the two window polynomials. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.Classical _root_.ComplexConjugate

lemma integral_fourierPolynomial_sq_injective {ι : Type*} (S : Finset ι)
    (frequency : ι → ℤ) (coefficient : ι → ℂ) (hinj : Set.InjOn frequency S) :
    (∫ θ, ‖fourierPolynomial S frequency coefficient θ‖ ^ 2
      ∂AddCircle.haarAddCircle) = ∑ i ∈ S, ‖coefficient i‖ ^ 2 := by
  rw [integral_norm_fourierPolynomial_sq, sum_product]
  apply sum_congr rfl
  intro i hi
  rw [sum_eq_single i]
  · simp only [ite_true, Complex.mul_conj', ← Complex.ofReal_pow, Complex.ofReal_re]
  · intro j hj hji
    have hf : frequency i ≠ frequency j := fun he => hji (hinj hi hj he).symm
    exact if_neg hf
  · exact fun hnot => False.elim (hnot hi)

lemma integral_fourierPolynomial_sq_le_card {ι : Type*} (S : Finset ι)
    (frequency : ι → ℤ) (coefficient : ι → ℂ) (hinj : Set.InjOn frequency S)
    (hbound : ∀ i ∈ S, ‖coefficient i‖ ≤ 1) :
    (∫ θ, ‖fourierPolynomial S frequency coefficient θ‖ ^ 2
      ∂AddCircle.haarAddCircle) ≤ S.card := by
  rw [integral_fourierPolynomial_sq_injective S frequency coefficient hinj]
  calc
    _ ≤ ∑ _i ∈ S, (1 : ℝ) := by
      apply sum_le_sum
      intro i hi
      have hh := hbound i hi
      have hn := norm_nonneg (coefficient i)
      nlinarith
    _ = _ := by simp

lemma continuous_forwardWindowPolynomial (f : ℕ → ℂ) (D v : ℕ) :
    Continuous (forwardWindowPolynomial f D v) := continuous_fourierPolynomial _ _ _

lemma continuous_backwardWindowPolynomial (g : ℕ → ℂ) (Q v : ℕ) :
    Continuous (backwardWindowPolynomial g Q v) := continuous_fourierPolynomial _ _ _

lemma norm_forwardWindowPolynomial_le (f : ℕ → ℂ) (hf : OneBounded f) (D v : ℕ)
    (θ : AddCircle (1 : ℝ)) : ‖forwardWindowPolynomial f D v θ‖ ≤ D := by
  apply (norm_fourierPolynomial_le _ _ _ θ).trans
  calc
    _ ≤ ∑ _m ∈ Icc 1 D, (1 : ℝ) := by
      apply sum_le_sum
      intro m hm
      have hm1 := (mem_Icc.mp hm).1
      exact hf _ (by omega)
    _ = _ := by simp

lemma norm_backwardWindowPolynomial_le (g : ℕ → ℂ) (hg : OneBounded g) (Q v : ℕ)
    (θ : AddCircle (1 : ℝ)) : ‖backwardWindowPolynomial g Q v θ‖ ≤ Q := by
  apply (norm_fourierPolynomial_le _ _ _ θ).trans
  calc
    _ ≤ ∑ _a ∈ Icc 1 Q, (1 : ℝ) := by
      apply sum_le_sum
      intro a ha
      have ha1 := (mem_Icc.mp ha).1
      exact hg _ (by omega)
    _ = _ := by simp

lemma integral_forwardWindowPolynomial_sq_le (f : ℕ → ℂ) (hf : OneBounded f)
    (D v : ℕ) :
    (∫ θ, ‖forwardWindowPolynomial f D v θ‖ ^ 2 ∂AddCircle.haarAddCircle) ≤ D := by
  have hi : Set.InjOn (fun m : ℕ => (m : ℤ)) (Icc 1 D) := by
    intro a _ b _ he
    change (a : ℤ) = (b : ℤ) at he
    exact_mod_cast he
  have hb : ∀ m ∈ Icc 1 D, ‖f (v + m)‖ ≤ 1 := by
    intro m hm
    have hm1 := (mem_Icc.mp hm).1
    exact hf _ (by omega)
  simpa only [forwardWindowPolynomial, Nat.card_Icc, Nat.add_sub_cancel,
    Nat.cast_id] using integral_fourierPolynomial_sq_le_card (Icc 1 D)
      (fun m : ℕ => (m : ℤ)) (fun m => f (v + m)) hi hb

lemma integral_backwardWindowPolynomial_sq_le (g : ℕ → ℂ) (hg : OneBounded g)
    (Q v : ℕ) :
    (∫ θ, ‖backwardWindowPolynomial g Q v θ‖ ^ 2 ∂AddCircle.haarAddCircle) ≤ Q := by
  have hi : Set.InjOn (fun a : ℕ => -(a : ℤ)) (Icc 1 Q) := by
    intro a _ b _ he
    exact_mod_cast neg_injective he
  have hb : ∀ a ∈ Icc 1 Q, ‖g (v + a)‖ ≤ 1 := by
    intro a ha
    have ha1 := (mem_Icc.mp ha).1
    exact hg _ (by omega)
  simpa only [backwardWindowPolynomial, Nat.card_Icc, Nat.add_sub_cancel,
    Nat.cast_id] using integral_fourierPolynomial_sq_le_card (Icc 1 Q)
      (fun a : ℕ => -(a : ℤ)) (fun a => g (v + a)) hi hb







end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.RoughShiftAverage
namespace OAI

/-!
# A finite rough-shift correlation inequality

The three terms are the explicit translation error, the low-frequency
Cauchy--Schwarz term, and the high-frequency fourth-moment term.  Sieve
estimates and MRT scale estimates enter only through their numerical bounds.
-/

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.Classical





lemma rough_window_energy_sum_bound (f g : ℕ → ℂ) (hf : OneBounded f)
    (hg : OneBounded g) (D Q Y : ℕ) :
    (∑ v ∈ range Y,
      Real.sqrt (∫ θ, ‖forwardWindowPolynomial f D (v + 1) θ‖ ^ 2
        ∂AddCircle.haarAddCircle) *
      Real.sqrt (∫ θ, ‖backwardWindowPolynomial g Q (v + 1) θ‖ ^ 2
        ∂AddCircle.haarAddCircle)) ≤ (Y : ℝ) * (Real.sqrt D * Real.sqrt Q) := by
  calc
    _ ≤ ∑ _v ∈ range Y, Real.sqrt (D : ℝ) * Real.sqrt Q := by
      apply sum_le_sum
      intro v _
      exact mul_le_mul
        (Real.sqrt_le_sqrt (integral_forwardWindowPolynomial_sq_le f hf D (v + 1)))
        (Real.sqrt_le_sqrt (integral_backwardWindowPolynomial_sq_le g hg Q (v + 1)))
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = _ := by simp




end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.WeightedShiftAverage
namespace OAI

/-! The finite correlation inequality for the arbitrary coefficients in
the qualitative rough multiplier. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.Classical



lemma norm_weightedRoughShiftProfile_le (f g : ℕ → ℂ) (hf : OneBounded f) (hg : OneBounded g)
    (Z : Finset ℕ) (c : ℕ → ℂ) (h n : ℕ) (hn : 0 < n) :
    ‖weightedRoughShiftProfile f g Z c h n‖ ≤ ∑ z ∈ Z, ‖c z / (z : ℂ)‖ := by
  have hh := norm_weightedShiftProfile_le Z (fun z => (c z / (z : ℂ)))
    (fun z => h * z) f g hf hg 1 0 n hn
  simpa only [weightedShiftProfile, weightedRoughShiftProfile, Nat.mod_one, ite_true] using hh

lemma translated_weightedRoughShiftProfile_eq (f g : ℕ → ℂ) (Z : Finset ℕ) (c : ℕ → ℂ) (D h Y : ℕ)
    (hZ : ∀ z ∈ Z, z ≤ 2 * D) :
    translatedPrefixAverage (weightedRoughShiftProfile f g Z c h) Y D =
      (D : ℂ)⁻¹ * ∑ v ∈ range Y, ∫ θ,
        weightedRoughFourier Z c h θ * forwardWindowPolynomial f D (v + 1) θ *
          backwardWindowPolynomial g ((2 * h + 1) * D) (v + 1) θ
            ∂AddCircle.haarAddCircle := by
  unfold translatedPrefixAverage
  congr 1
  calc
    _ = ∑ m ∈ Icc 1 D,
        positivePrefix (fun n => weightedRoughShiftProfile f g Z c h (n + m)) Y := by
      simpa only [Nat.zero_add] using (sum_Icc_shift
        (fun m => positivePrefix (fun n => weightedRoughShiftProfile f g Z c h (n + m)) Y) 0 D).symm
    _ = _ := by
      rw [summed_weighted_rough_shift_convolution f g Z c D h Y hZ]
      rfl

/-- All Fourier ingredients are now attached to the concrete two windows. -/
theorem weighted_rough_convolution_sum_bound (f g : ℕ → ℂ) (hf : OneBounded f)
    (hg : OneBounded g) (Z : Finset ℕ) (c : ℕ → ℂ) (D h Y : ℕ)
    (ε U V K : ℝ) (hε : 0 < ε) (hU : 0 ≤ U) (hK : 0 ≤ K)
    (hB : ∀ θ, ‖weightedRoughFourier Z c h θ‖ ≤ U)
    (hV : (∫ θ, ‖weightedRoughFourier Z c h θ‖ ^ 4
      ∂AddCircle.haarAddCircle) ≤ V)
    (hF : ∀ θ, (∑ v ∈ range Y, ‖forwardWindowPolynomial f D (v + 1) θ‖) ≤ K) :
    ‖∑ v ∈ range Y, ∫ θ,
      weightedRoughFourier Z c h θ * forwardWindowPolynomial f D (v + 1) θ *
        backwardWindowPolynomial g ((2 * h + 1) * D) (v + 1) θ
          ∂AddCircle.haarAddCircle‖ ≤
      ε * ((Y : ℝ) * (Real.sqrt D * Real.sqrt ((2 * h + 1) * D))) +
        (U * ((2 * h + 1) * D) * K / ε ^ 4) * V := by
  have hh := fourier_region_bound (range Y) (weightedRoughFourier Z c h)
    (fun v => forwardWindowPolynomial f D (v + 1))
    (fun v => backwardWindowPolynomial g ((2 * h + 1) * D) (v + 1))
    (continuous_fourierPolynomial _ _ _)
    (fun v _ => continuous_forwardWindowPolynomial f D (v + 1))
    (fun v _ => continuous_backwardWindowPolynomial g ((2 * h + 1) * D) (v + 1))
    ε U ((2 * h + 1) * D) K hε hU (by positivity) hK hB
    (fun v _ θ => by
      simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one] using
        norm_backwardWindowPolynomial_le g hg ((2 * h + 1) * D) (v + 1) θ) hF
  apply hh.trans
  apply add_le_add
  · apply mul_le_mul_of_nonneg_left _ hε.le
    simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one] using
      rough_window_energy_sum_bound f g hf hg D ((2 * h + 1) * D) Y
  · exact mul_le_mul_of_nonneg_left hV (by positivity)

lemma normalized_translated_weightedRoughShift_bound (f g : ℕ → ℂ)
    (Z : Finset ℕ) (c : ℕ → ℂ) (D h Y : ℕ) (hD : 0 < D) (hY : 0 < Y)
    (hZ : ∀ z ∈ Z, z ≤ 2 * D) (W : ℝ)
    (hW : ‖∑ v ∈ range Y, ∫ θ,
      weightedRoughFourier Z c h θ * forwardWindowPolynomial f D (v + 1) θ *
        backwardWindowPolynomial g ((2 * h + 1) * D) (v + 1) θ
          ∂AddCircle.haarAddCircle‖ ≤ W) :
    ‖translatedPrefixAverage (weightedRoughShiftProfile f g Z c h) Y D / (Y : ℂ)‖ ≤
      W / ((Y : ℝ) * D) := by
  rw [translated_weightedRoughShiftProfile_eq f g Z c D h Y hZ,
    norm_div, norm_mul, norm_inv, Complex.norm_natCast, Complex.norm_natCast]
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have hYr : (0 : ℝ) < Y := by exact_mod_cast hY
  calc
    _ ≤ (D : ℝ)⁻¹ * W / Y :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hW (by positivity)) hYr.le
    _ = _ := by simp only [div_eq_mul_inv, mul_inv_rev]; ring

/-- The finite correlation bound before inserting the sieve estimates and
the size estimates for the published MRT error. -/
theorem weighted_rough_shift_average_bound (f g : ℕ → ℂ) (hf : OneBounded f)
    (hg : OneBounded g) (Z : Finset ℕ) (c : ℕ → ℂ) (D h Y : ℕ) (hD : 0 < D) (hY : 0 < Y)
    (hZ : ∀ z ∈ Z, z ≤ 2 * D)
    (ε U V K : ℝ) (hε : 0 < ε) (hU : 0 ≤ U) (hK : 0 ≤ K)
    (hB : ∀ θ, ‖weightedRoughFourier Z c h θ‖ ≤ U)
    (hV : (∫ θ, ‖weightedRoughFourier Z c h θ‖ ^ 4
      ∂AddCircle.haarAddCircle) ≤ V)
    (hF : ∀ θ, (∑ v ∈ range Y, ‖forwardWindowPolynomial f D (v + 1) θ‖) ≤ K) :
    ‖weightedRoughShiftAverage f g Z c h Y‖ ≤
      2 * (D : ℝ) / Y * (∑ z ∈ Z, ‖c z / (z : ℂ)‖) +
      (ε * ((Y : ℝ) * (Real.sqrt D * Real.sqrt ((2 * h + 1) * D))) +
        (U * ((2 * h + 1) * D) * K / ε ^ 4) * V) / ((Y : ℝ) * D) := by
  let u := weightedRoughShiftProfile f g Z c h
  have he := norm_normalized_translation_error u Y D hY hD
    (∑ z ∈ Z, ‖c z / (z : ℂ)‖) (sum_nonneg (fun z _ => by positivity))
    (fun n hn => norm_weightedRoughShiftProfile_le f g hf hg Z c h n hn)
  have hc := normalized_translated_weightedRoughShift_bound f g Z c D h Y hD hY hZ _
    (weighted_rough_convolution_sum_bound f g hf hg Z c D h Y ε U V K hε hU hK hB hV hF)
  calc
    ‖weightedRoughShiftAverage f g Z c h Y‖ = ‖translatedPrefixAverage u Y D / (Y : ℂ) -
        (translatedPrefixAverage u Y D - positivePrefix u Y) / (Y : ℂ)‖ := by
      congr 1
      dsimp [weightedRoughShiftAverage, u]
      ring
    _ ≤ ‖translatedPrefixAverage u Y D / (Y : ℂ)‖ +
        ‖(translatedPrefixAverage u Y D - positivePrefix u Y) / (Y : ℂ)‖ := norm_sub_le _ _
    _ ≤ _ := by simpa only [add_comm] using add_le_add hc he

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.RoughShiftScale
namespace OAI

/-! Explicit power arithmetic in the rough-shift Fourier argument. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.Classical


lemma rough_window_sqrt_bound (D h : ℕ) :
    Real.sqrt (D : ℝ) * Real.sqrt ((2 * (h : ℝ) + 1) * D) ≤
      (2 * (h : ℝ) + 1) * D := by
  have ht : (D : ℝ) ≤ (2 * (h : ℝ) + 1) * D := by
    nlinarith [show (0 : ℝ) ≤ (h : ℝ) * D by positivity]
  calc
    _ ≤ Real.sqrt ((2 * (h : ℝ) + 1) * D) *
        Real.sqrt ((2 * (h : ℝ) + 1) * D) :=
      mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt ht) (Real.sqrt_nonneg _)
    _ = _ := by rw [← pow_two, Real.sq_sqrt (by positivity)]


lemma rough_low_term_bound (D h Y : ℕ) (hD : 0 < D) (hY : 0 < Y)
    (ε : ℝ) (hε : 0 ≤ ε) :
    (ε * ((Y : ℝ) * (Real.sqrt D * Real.sqrt ((2 * (h : ℝ) + 1) * D)))) /
      ((Y : ℝ) * D) ≤ (2 * (h : ℝ) + 1) * ε := by
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have hYr : (0 : ℝ) < Y := by exact_mod_cast hY
  calc
    _ ≤ (ε * ((Y : ℝ) * ((2 * (h : ℝ) + 1) * D))) / ((Y : ℝ) * D) := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (rough_window_sqrt_bound D h) hYr.le) hε)
        (mul_pos hYr hDr).le
    _ = _ := by field_simp



end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.WeightedShiftParameters
namespace OAI

/-! The three quantitative terms in the qualitative weighted shift
argument, separated from their eventual scale estimates. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.Classical

lemma rough_coefficient_mass_le_one (Z : Finset ℕ) (c : ℕ → ℂ) (D : ℕ)
    (hD : 0 < D) (hZ : ∀ z ∈ Z, D ≤ z ∧ z < D + D)
    (hc : ∀ z ∈ Z, ‖c z‖ ≤ 1) :
    (∑ z ∈ Z, ‖c z / (z : ℂ)‖) ≤ 1 := by
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have hcard : Z.card ≤ D := by
    have ht := card_le_card (show Z ⊆ Ico D (D + D) from
      fun z hz => mem_Ico.mpr (hZ z hz))
    simpa using ht
  calc
    _ ≤ ∑ _z ∈ Z, (D : ℝ)⁻¹ := sum_le_sum
      (rough_coefficient_norm_le Z c D hDr
        (fun z hz => by exact_mod_cast (hZ z hz).1) hc)
    _ = Z.card / (D : ℝ) := by simp [div_eq_mul_inv]
    _ ≤ 1 := (div_le_one hDr).mpr (by exact_mod_cast hcard)

lemma weighted_shift_high_identity (D h Y : ℕ) (hD : 0 < D) (hY : 0 < Y)
    (q η U V K : ℝ) (hη : 0 < η) :
    (((U * q) * ((2 * (h : ℝ) + 1) * D) *
        (K * Y * D * q) / η ^ 4) * (V / D * q ^ 4)) / ((Y : ℝ) * D) =
      ((2 * (h : ℝ) + 1) * U * V * K) * (q ^ 6 / η ^ 4) := by
  have hDr : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  have hYr : (Y : ℝ) ≠ 0 := by exact_mod_cast hY.ne'
  field_simp

/-- The high-frequency cost is controlled by `q^6 ≤ η^5`; all actual
correlation, boundary and short-window terms remain explicit. -/
theorem weighted_rough_shift_parameter_bound (f g : ℕ → ℂ) (hf : OneBounded f)
    (hg : OneBounded g) (Z : Finset ℕ) (c : ℕ → ℂ) (D h Y : ℕ)
    (hD : 0 < D) (hY : 0 < Y) (hZ : ∀ z ∈ Z, z ≤ 2 * D)
    (q η U V K : ℝ) (hq : 0 ≤ q) (hη : 0 < η)
    (hU : 0 ≤ U) (hV : 0 ≤ V) (hK : 0 ≤ K)
    (hmass : (∑ z ∈ Z, ‖c z / (z : ℂ)‖) ≤ 1)
    (hendpoint : (D : ℝ) / Y ≤ η) (hgap : q ^ 6 ≤ η ^ 5)
    (hB : ∀ θ, ‖weightedRoughFourier Z c h θ‖ ≤ U * q)
    (hfourth : (∫ θ, ‖weightedRoughFourier Z c h θ‖ ^ 4
      ∂AddCircle.haarAddCircle) ≤ V / D * q ^ 4)
    (hF : ∀ θ, (∑ v ∈ range Y, ‖forwardWindowPolynomial f D (v + 1) θ‖) ≤
      K * Y * D * q) :
    ‖weightedRoughShiftAverage f g Z c h Y‖ ≤
      (2 + (2 * (h : ℝ) + 1) + (2 * (h : ℝ) + 1) * U * V * K) * η := by
  have he : 2 * (D : ℝ) / Y * (∑ z ∈ Z, ‖c z / (z : ℂ)‖) ≤ 2 * η := by
    calc
      _ = 2 * ((D : ℝ) / Y) * (∑ z ∈ Z, ‖c z / (z : ℂ)‖) := by ring
      _ ≤ 2 * η * 1 := mul_le_mul
        (mul_le_mul_of_nonneg_left hendpoint (by norm_num)) hmass
        (sum_nonneg (fun _ _ => norm_nonneg _)) (by positivity)
      _ = _ := mul_one _
  have hraw := weighted_rough_shift_average_bound f g hf hg Z c D h Y hD hY hZ
    η (U * q) (V / D * q ^ 4) (K * Y * D * q) hη (by positivity) (by positivity)
    hB hfourth hF
  have hlow := rough_low_term_bound D h Y hD hY η hη.le
  have hhigh := weighted_shift_high_identity D h Y hD hY q η U V K hη
  have hfrac : q ^ 6 / η ^ 4 ≤ η := by
    apply (div_le_iff₀ (pow_pos hη 4)).mpr
    convert (preTransparency := .instances) hgap using 1
    ring
  have ht := mul_le_mul_of_nonneg_left hfrac
    (show 0 ≤ (2 * (h : ℝ) + 1) * U * V * K by positivity)
  apply hraw.trans
  rw [add_div, hhigh]
  nlinarith only [he, hlow, ht]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.QualitativeRoughBins
namespace OAI

/-! The actual real divisor bins in the analytic centering argument are
contained in the natural windows used by the finite Fourier proof. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical

lemma rough_bin_ceil_window (M τ : ℝ) (hM : 0 < M) (hτ : τ < 2)
    (z : ℕ) (hz : M < (z : ℝ) ∧ (z : ℝ) ≤ τ * M) :
    Nat.ceil M ≤ z ∧ z < Nat.ceil M + Nat.ceil M := by
  have hc : M ≤ (Nat.ceil M : ℝ) := Nat.le_ceil M
  constructor
  · exact Nat.ceil_le.mpr hz.1.le
  · have ht : (z : ℝ) < (Nat.ceil M : ℝ) + Nat.ceil M := by
      nlinarith only [hz.2, hτ, hM, hc]
    exact_mod_cast ht

lemma ceil_exp_scale_bound (B C₀ M : ℝ) (hB : 1 ≤ B) (hC₀ : 1 ≤ C₀)
    (hM : 0 ≤ M) (hupper : M ≤ Real.exp (C₀ * B)) :
    (Nat.ceil M : ℝ) ≤ Real.exp ((C₀ + 1) * B) := by
  have hc : (Nat.ceil M : ℝ) ≤ M + 1 := (Nat.ceil_lt_add_one hM).le
  have he : 1 ≤ Real.exp (C₀ * B) := Real.one_le_exp (by nlinarith)
  have heB : 2 ≤ Real.exp B := by linarith [Real.add_one_le_exp B]
  calc
    _ ≤ M + 1 := hc
    _ ≤ Real.exp (C₀ * B) + 1 := by linarith only [hupper]
    _ ≤ Real.exp (C₀ * B) * Real.exp B := by nlinarith only [he, heB]
    _ = _ := by rw [← Real.exp_add]; congr 1; ring


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.WeightedShiftRight
namespace OAI

/-! The same finite Fourier argument when the nonpretentious function is
in the second factor. No supremum is moved inside a sum over origins. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter _root_.MeasureTheory
open scoped _root_.Classical

lemma backwardWindowPolynomial_eq_forward_neg (g : ℕ → ℂ) (Q v : ℕ)
    (θ : AddCircle (1 : ℝ)) :
    backwardWindowPolynomial g Q v θ = forwardWindowPolynomial g Q v (-θ) := by
  simp only [backwardWindowPolynomial, forwardWindowPolynomial, fourierPolynomial,
    fourier_apply, smul_neg, neg_smul]

theorem weighted_rough_convolution_sum_bound_right (f g : ℕ → ℂ) (hf : OneBounded f)
    (hg : OneBounded g) (Z : Finset ℕ) (c : ℕ → ℂ) (D h Y : ℕ)
    (ε U V K : ℝ) (hε : 0 < ε) (hU : 0 ≤ U) (hK : 0 ≤ K)
    (hB : ∀ θ, ‖weightedRoughFourier Z c h θ‖ ≤ U)
    (hV : (∫ θ, ‖weightedRoughFourier Z c h θ‖ ^ 4
      ∂AddCircle.haarAddCircle) ≤ V)
    (hG : ∀ θ, (∑ v ∈ range Y,
      ‖backwardWindowPolynomial g ((2 * h + 1) * D) (v + 1) θ‖) ≤ K) :
    ‖∑ v ∈ range Y, ∫ θ,
      weightedRoughFourier Z c h θ * forwardWindowPolynomial f D (v + 1) θ *
        backwardWindowPolynomial g ((2 * h + 1) * D) (v + 1) θ
          ∂AddCircle.haarAddCircle‖ ≤
      ε * ((Y : ℝ) * (Real.sqrt D * Real.sqrt ((2 * h + 1) * D))) +
        (U * D * K / ε ^ 4) * V := by
  have he : (∑ v ∈ range Y, ∫ θ,
      weightedRoughFourier Z c h θ * forwardWindowPolynomial f D (v + 1) θ *
        backwardWindowPolynomial g ((2 * h + 1) * D) (v + 1) θ
          ∂AddCircle.haarAddCircle) =
      ∑ v ∈ range Y, ∫ θ,
        weightedRoughFourier Z c h θ * backwardWindowPolynomial g ((2 * h + 1) * D) (v + 1) θ *
          forwardWindowPolynomial f D (v + 1) θ ∂AddCircle.haarAddCircle := by
    apply sum_congr rfl
    intro v _
    apply integral_congr_ae
    exact Eventually.of_forall (fun θ => by ring)
  rw [he]
  have hh := fourier_region_bound (range Y) (weightedRoughFourier Z c h)
    (fun v => backwardWindowPolynomial g ((2 * h + 1) * D) (v + 1))
    (fun v => forwardWindowPolynomial f D (v + 1))
    (continuous_fourierPolynomial _ _ _)
    (fun v _ => continuous_backwardWindowPolynomial g ((2 * h + 1) * D) (v + 1))
    (fun v _ => continuous_forwardWindowPolynomial f D (v + 1))
    ε U D K hε hU (by positivity) hK hB
    (fun v _ θ => norm_forwardWindowPolynomial_le f hf D (v + 1) θ) hG
  apply hh.trans
  apply add_le_add
  · apply mul_le_mul_of_nonneg_left _ hε.le
    calc
      _ = ∑ v ∈ range Y,
          Real.sqrt (∫ θ, ‖forwardWindowPolynomial f D (v + 1) θ‖ ^ 2
            ∂AddCircle.haarAddCircle) *
          Real.sqrt (∫ θ, ‖backwardWindowPolynomial g ((2 * h + 1) * D) (v + 1) θ‖ ^ 2
            ∂AddCircle.haarAddCircle) := sum_congr rfl (fun _ _ => mul_comm _ _)
      _ ≤ _ := by
        simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one] using
          rough_window_energy_sum_bound f g hf hg D ((2 * h + 1) * D) Y
  · exact mul_le_mul_of_nonneg_left hV (by positivity)

/-- The second-factor version of the complete finite three-term bound. -/
theorem weighted_rough_shift_average_bound_right (f g : ℕ → ℂ) (hf : OneBounded f)
    (hg : OneBounded g) (Z : Finset ℕ) (c : ℕ → ℂ) (D h Y : ℕ) (hD : 0 < D) (hY : 0 < Y)
    (hZ : ∀ z ∈ Z, z ≤ 2 * D)
    (ε U V K : ℝ) (hε : 0 < ε) (hU : 0 ≤ U) (hK : 0 ≤ K)
    (hB : ∀ θ, ‖weightedRoughFourier Z c h θ‖ ≤ U)
    (hV : (∫ θ, ‖weightedRoughFourier Z c h θ‖ ^ 4
      ∂AddCircle.haarAddCircle) ≤ V)
    (hG : ∀ θ, (∑ v ∈ range Y,
      ‖backwardWindowPolynomial g ((2 * h + 1) * D) (v + 1) θ‖) ≤ K) :
    ‖weightedRoughShiftAverage f g Z c h Y‖ ≤
      2 * (D : ℝ) / Y * (∑ z ∈ Z, ‖c z / (z : ℂ)‖) +
      (ε * ((Y : ℝ) * (Real.sqrt D * Real.sqrt ((2 * h + 1) * D))) +
        (U * D * K / ε ^ 4) * V) / ((Y : ℝ) * D) := by
  let u := weightedRoughShiftProfile f g Z c h
  have he := norm_normalized_translation_error u Y D hY hD
    (∑ z ∈ Z, ‖c z / (z : ℂ)‖) (sum_nonneg (fun _ _ => by positivity))
    (fun n hn => norm_weightedRoughShiftProfile_le f g hf hg Z c h n hn)
  have hc := normalized_translated_weightedRoughShift_bound f g Z c D h Y hD hY hZ _
    (weighted_rough_convolution_sum_bound_right f g hf hg Z c D h Y ε U V K hε hU hK hB hV hG)
  calc
    _ = ‖translatedPrefixAverage u Y D / (Y : ℂ) -
        (translatedPrefixAverage u Y D - positivePrefix u Y) / (Y : ℂ)‖ := by
      congr 1
      dsimp [weightedRoughShiftAverage, u]
      ring
    _ ≤ ‖translatedPrefixAverage u Y D / (Y : ℂ)‖ +
        ‖(translatedPrefixAverage u Y D - positivePrefix u Y) / (Y : ℂ)‖ := norm_sub_le _ _
    _ ≤ _ := by simpa only [add_comm] using add_le_add hc he

/-- The sixth-power condition has the same exponent for either factor. -/
theorem weighted_rough_shift_parameter_bound_right (f g : ℕ → ℂ) (hf : OneBounded f)
    (hg : OneBounded g) (Z : Finset ℕ) (c : ℕ → ℂ) (D h Y : ℕ)
    (hD : 0 < D) (hY : 0 < Y) (hZ : ∀ z ∈ Z, z ≤ 2 * D)
    (q η U V K : ℝ) (hq : 0 ≤ q) (hη : 0 < η)
    (hU : 0 ≤ U) (hV : 0 ≤ V) (hK : 0 ≤ K)
    (hmass : (∑ z ∈ Z, ‖c z / (z : ℂ)‖) ≤ 1)
    (hendpoint : (D : ℝ) / Y ≤ η) (hgap : q ^ 6 ≤ η ^ 5)
    (hB : ∀ θ, ‖weightedRoughFourier Z c h θ‖ ≤ U * q)
    (hfourth : (∫ θ, ‖weightedRoughFourier Z c h θ‖ ^ 4
      ∂AddCircle.haarAddCircle) ≤ V / D * q ^ 4)
    (hG : ∀ θ, (∑ v ∈ range Y,
      ‖backwardWindowPolynomial g ((2 * h + 1) * D) (v + 1) θ‖) ≤
      K * Y * ((2 * (h : ℝ) + 1) * D) * q) :
    ‖weightedRoughShiftAverage f g Z c h Y‖ ≤
      (2 + (2 * (h : ℝ) + 1) + (2 * (h : ℝ) + 1) * U * V * K) * η := by
  have he : 2 * (D : ℝ) / Y * (∑ z ∈ Z, ‖c z / (z : ℂ)‖) ≤ 2 * η := by
    calc
      _ = 2 * ((D : ℝ) / Y) * (∑ z ∈ Z, ‖c z / (z : ℂ)‖) := by ring
      _ ≤ 2 * η * 1 := mul_le_mul
        (mul_le_mul_of_nonneg_left hendpoint (by norm_num)) hmass
        (sum_nonneg (fun _ _ => norm_nonneg _)) (by positivity)
      _ = _ := mul_one _
  have hraw := weighted_rough_shift_average_bound_right f g hf hg Z c D h Y hD hY hZ
    η (U * q) (V / D * q ^ 4) (K * Y * ((2 * (h : ℝ) + 1) * D) * q)
    hη (by positivity) (by positivity) hB hfourth hG
  have hlow := rough_low_term_bound D h Y hD hY η hη.le
  have hhigh : (((U * q) * D * (K * Y * ((2 * (h : ℝ) + 1) * D) * q) / η ^ 4) *
      (V / D * q ^ 4)) / ((Y : ℝ) * D) =
      ((2 * (h : ℝ) + 1) * U * V * K) * (q ^ 6 / η ^ 4) := by
    convert (preTransparency := .instances) weighted_shift_high_identity D h Y hD hY q η U V K hη using 1
    ring
  have hfrac : q ^ 6 / η ^ 4 ≤ η := by
    apply (div_le_iff₀ (pow_pos hη 4)).mpr
    convert (preTransparency := .instances) hgap using 1
    ring
  have ht := mul_le_mul_of_nonneg_left hfrac
    (show 0 ≤ (2 * (h : ℝ) + 1) * U * V * K by positivity)
  apply hraw.trans
  rw [add_div, hhigh]
  nlinarith only [he, hlow, ht]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.QualitativeRightShifts
namespace OAI

/-! The qualitative rough-shift estimate when the original second factor
is uniformly nonpretentious. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical


lemma long_window_exp_bound (B C₀ : ℝ) (D h : ℕ) (hB : 1 ≤ B)
    (hD : (D : ℝ) ≤ Real.exp (C₀ * B)) :
    (((2 * h + 1) * D : ℕ) : ℝ) ≤
      Real.exp ((C₀ + (2 * (h : ℝ) + 1)) * B) := by
  have ht : 0 < 2 * (h : ℝ) + 1 := by positivity
  have hexp : 2 * (h : ℝ) + 1 ≤ Real.exp ((2 * (h : ℝ) + 1) * B) := by
    have he := Real.add_one_le_exp ((2 * (h : ℝ) + 1) * B)
    nlinarith only [he, ht, hB]
  calc
    _ = (2 * (h : ℝ) + 1) * D := by push_cast; rfl
    _ ≤ Real.exp ((2 * (h : ℝ) + 1) * B) * Real.exp (C₀ * B) := by gcongr
    _ = _ := by rw [← Real.exp_add]; congr 1; ring


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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.DilatedForwardWindows
namespace OAI

/-! Positive-origin Fourier windows for the exact dilated sequence. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical

lemma OneBounded.mul_argument {f : ℕ → ℂ} (hf : OneBounded f)
    (q : ℕ) (hq : 0 < q) : OneBounded (fun n => f (q * n)) := by
  intro n hn
  exact hf _ (Nat.mul_pos hq hn)


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.DilatedRoughShifts
namespace OAI

/-! Rough-shift cancellation for the actual factors b(qn), g(qn).
The dilation is unrestricted and its sole cost is the averaged Euler factor. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical

theorem qualitative_dilated_rough_shifts (hM : PrimeReciprocalInput)
    (hMRT : MRTShortExponentialInput) {f : ℕ → ℂ}
    (hfnp : UniformlyNonpretentious f) (hf : OneBounded f)
    (h : ℕ) (hh : 0 < h) (C₀ : ℝ) (hC₀ : 1 ≤ C₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ B : ℝ in atTop,
      ∀ (P : Finset ℕ) (D : ℕ),
      (1 / 2 : ℝ) * Real.exp (B ^ (9999 / 10000 : ℝ)) ≤ D →
      (D : ℝ) ≤ Real.exp (C₀ * B ^ (2 : ℕ)) →
      ∀ q : ℕ, 0 < q → ∀ᶠ Y : ℕ in atTop,
      ∀ b g : ℕ → ℂ, Multiplicative b → OneBounded b → OneBounded g →
      (∀ p, Nat.Prime p → p ∉ P → b p = f p) →
      ∀ (Z : Finset ℕ) (c : ℕ → ℂ),
      (∀ z ∈ Z, D ≤ z ∧ z < D + D ∧
        HasNoPrimeFactorBelow (Real.exp (B ^ (9999 / 10000 : ℝ))) z) →
      (∀ z ∈ Z, ‖c z‖ ≤ 1) →
      ‖weightedRoughShiftAverage (fun n => b (q * n)) (fun n => g (q * n)) Z c h Y‖ ≤
        C * B ^ (-11 / 10 : ℝ) * smoothReciprocalProduct q.primeFactors (1 / 2 : ℝ) := by
  obtain ⟨U, V, hU, hV, hfourier⟩ := hM.qualitative_rough_fourier
  obtain ⟨K, hK, hwindows⟩ := hMRT.dilated_forward_windows hfnp hf C₀ hC₀
  let A := 2 + (2 * (h : ℝ) + 1)
  let T := (2 * (h : ℝ) + 1) * U * V * K
  refine ⟨A + T, by dsimp [A, T]; positivity, ?_⟩
  filter_upwards [hfourier, hwindows, eventually_strong_qualitative_frequency_gap,
    eventually_qualitative_interval_lower, eventually_ge_atTop (Real.exp 1)] with
    B hfour hwin hgap hlower hB
  intro P D hDlower hDupper q hq
  have hDten : 10 ≤ D := hlower D hDlower
  have hDpos : 0 < D := by omega
  have hBpos : 0 < B := (Real.exp_pos 1).trans_le hB
  have hB1 : 1 ≤ B := (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)).trans hB
  have hlog : 0 ≤ Real.log B := Real.log_nonneg hB1
  have hη : 0 < B ^ (-11 / 10 : ℝ) := Real.rpow_pos_of_pos hBpos _
  let M := smoothReciprocalProduct q.primeFactors (1 / 2 : ℝ)
  have hM1 : 1 ≤ M := one_le_smoothReciprocalProduct _
    (fun _ hp => Nat.prime_of_mem_primeFactors hp) (1 / 2) (by norm_num)
  have hM0 : 0 ≤ M := by linarith
  filter_upwards [hwin P D hDlower hDupper q hq,
    eventually_fixed_interval_endpoint D _ hη] with Y hY hend
  intro b g hb hbb hg heq Z c hZ hc
  have hfourZ := hfour D h hDlower hh Z c hZ hc
  have hZinterval : ∀ z ∈ Z, D ≤ z ∧ z < D + D :=
    fun z hz => ⟨(hZ z hz).1, (hZ z hz).2.1⟩
  have hZend : ∀ z ∈ Z, z ≤ 2 * D := by
    intro z hz
    have ht := (hZ z hz).2.1
    omega
  have hr := weighted_rough_shift_parameter_bound (fun n => b (q * n)) (fun n => g (q * n))
    (hbb.mul_argument q hq) (hg.mul_argument q hq) Z c D h Y hDpos hend.1 hZend
    (Real.log B / B ^ (9999 / 10000 : ℝ)) (B ^ (-11 / 10 : ℝ)) U V (K * M)
    (by positivity) hη hU.le hV.le (mul_nonneg hK.le hM0)
    (rough_coefficient_mass_le_one Z c D hDpos hZinterval hc)
    hend.2 hgap hfourZ.1 hfourZ.2 (fun θ => by
      convert (preTransparency := .instances) hY b hb hbb heq θ using 1
      dsimp [M]
      ring)
  calc
    _ ≤ (A + T * M) * B ^ (-11 / 10 : ℝ) := hr.trans_eq (by dsimp [A, T]; ring)
    _ ≤ (A + T) * B ^ (-11 / 10 : ℝ) * M := by
      have hA : 0 ≤ A := by dsimp [A]; positivity
      have hhA := mul_le_mul_of_nonneg_left hM1 hA
      nlinarith [mul_nonneg (sub_nonneg.mpr hhA) hη.le]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.DilatedRoughRight
namespace OAI

/-! The same dilated rough-shift estimate when the original second factor
is uniformly nonpretentious. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical

theorem qualitative_dilated_rough_shifts_right (hM : PrimeReciprocalInput)
    (hMRT : MRTShortExponentialInput) {f : ℕ → ℂ}
    (hfnp : UniformlyNonpretentious f) (hf : OneBounded f)
    (h : ℕ) (hh : 0 < h) (C₀ : ℝ) (hC₀ : 1 ≤ C₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ B : ℝ in atTop,
      ∀ (P : Finset ℕ) (D : ℕ),
      (1 / 2 : ℝ) * Real.exp (B ^ (9999 / 10000 : ℝ)) ≤ D →
      (D : ℝ) ≤ Real.exp (C₀ * B ^ (2 : ℕ)) →
      ∀ q : ℕ, 0 < q → ∀ᶠ Y : ℕ in atTop,
      ∀ b g : ℕ → ℂ, OneBounded b → Multiplicative g → OneBounded g →
      (∀ p, Nat.Prime p → p ∉ P → g p = f p) →
      ∀ (Z : Finset ℕ) (c : ℕ → ℂ),
      (∀ z ∈ Z, D ≤ z ∧ z < D + D ∧
        HasNoPrimeFactorBelow (Real.exp (B ^ (9999 / 10000 : ℝ))) z) →
      (∀ z ∈ Z, ‖c z‖ ≤ 1) →
      ‖weightedRoughShiftAverage (fun n => b (q * n)) (fun n => g (q * n)) Z c h Y‖ ≤
        C * B ^ (-11 / 10 : ℝ) * smoothReciprocalProduct q.primeFactors (1 / 2 : ℝ) := by
  obtain ⟨U, V, hU, hV, hfourier⟩ := hM.qualitative_rough_fourier
  obtain ⟨K, hK, hwindows⟩ := hMRT.dilated_forward_windows hfnp hf
    (C₀ + (2 * (h : ℝ) + 1)) (by
      have ht : (0 : ℝ) ≤ h := Nat.cast_nonneg h
      linarith only [hC₀, ht])
  let A := 2 + (2 * (h : ℝ) + 1)
  let T := (2 * (h : ℝ) + 1) * U * V * K
  refine ⟨A + T, by dsimp [A, T]; positivity, ?_⟩
  filter_upwards [hfourier, hwindows, eventually_strong_qualitative_frequency_gap,
    eventually_qualitative_interval_lower, eventually_ge_atTop (Real.exp 1)] with
    B hfour hwin hgap hlower hB
  intro P D hDlower hDupper q hq
  have hDten : 10 ≤ D := hlower D hDlower
  have hDpos : 0 < D := by omega
  have hB1 : 1 ≤ B := (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)).trans hB
  have hBpos : 0 < B := zero_lt_one.trans_le hB1
  have hlog : 0 ≤ Real.log B := Real.log_nonneg hB1
  have hη : 0 < B ^ (-11 / 10 : ℝ) := Real.rpow_pos_of_pos hBpos _
  let Q := (2 * h + 1) * D
  have hDQ : D ≤ Q := Nat.le_mul_of_pos_left D (by omega)
  have hQlower : (1 / 2 : ℝ) * Real.exp (B ^ (9999 / 10000 : ℝ)) ≤ Q :=
    hDlower.trans (by exact_mod_cast hDQ)
  have hQupper : (Q : ℝ) ≤ Real.exp ((C₀ + (2 * (h : ℝ) + 1)) * B ^ (2 : ℕ)) :=
    long_window_exp_bound (B ^ (2 : ℕ)) C₀ D h (by nlinarith) hDupper
  let M := smoothReciprocalProduct q.primeFactors (1 / 2 : ℝ)
  have hM1 : 1 ≤ M := one_le_smoothReciprocalProduct _
    (fun _ hp => Nat.prime_of_mem_primeFactors hp) (1 / 2) (by norm_num)
  have hM0 : 0 ≤ M := by linarith
  filter_upwards [hwin P Q hQlower hQupper q hq,
    eventually_fixed_interval_endpoint D _ hη] with Y hY hend
  intro b g hbb hg hgb heq Z c hZ hc
  have hfourZ := hfour D h hDlower hh Z c hZ hc
  have hZinterval : ∀ z ∈ Z, D ≤ z ∧ z < D + D :=
    fun z hz => ⟨(hZ z hz).1, (hZ z hz).2.1⟩
  have hZend : ∀ z ∈ Z, z ≤ 2 * D := by
    intro z hz
    have ht := (hZ z hz).2.1
    omega
  have hr := weighted_rough_shift_parameter_bound_right
    (fun n => b (q * n)) (fun n => g (q * n))
    (hbb.mul_argument q hq) (hgb.mul_argument q hq) Z c D h Y hDpos hend.1 hZend
    (Real.log B / B ^ (9999 / 10000 : ℝ)) (B ^ (-11 / 10 : ℝ)) U V (K * M)
    (by positivity) hη hU.le hV.le (mul_nonneg hK.le hM0)
    (rough_coefficient_mass_le_one Z c D hDpos hZinterval hc)
    hend.2 hgap hfourZ.1 hfourZ.2 (fun θ => by
      simp_rw [backwardWindowPolynomial_eq_forward_neg]
      convert (preTransparency := .instances) hY g hg hgb heq (-θ) using 1
      dsimp [M, Q]
      push_cast
      ring)
  calc
    _ ≤ (A + T * M) * B ^ (-11 / 10 : ℝ) := hr.trans_eq (by dsimp [A, T]; ring)
    _ ≤ (A + T) * B ^ (-11 / 10 : ℝ) * M := by
      have hA : 0 ≤ A := by dsimp [A]; positivity
      have hhA := mul_le_mul_of_nonneg_left hM1 hA
      nlinarith [mul_nonneg (sub_nonneg.mpr hhA) hη.le]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.DilatedRoughBins
namespace OAI

/-! Actual real bins for the direct dilation estimates, retaining their
single Euler cost for subsequent averaging over padding divisors. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical

theorem qualitative_dilated_rough_shifts_real_bins (hM : PrimeReciprocalInput)
    (hMRT : MRTShortExponentialInput) {f : ℕ → ℂ}
    (hfnp : UniformlyNonpretentious f) (hf : OneBounded f)
    (h : ℕ) (hh : 0 < h) (C₀ : ℝ) (hC₀ : 1 ≤ C₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ B : ℝ in atTop,
      ∀ (P : Finset ℕ) (M τ : ℝ), 1 < τ → τ < 2 →
      Real.exp (B ^ (9999 / 10000 : ℝ)) / τ ≤ M →
      M ≤ Real.exp (C₀ * B ^ (2 : ℕ)) →
      ∀ q : ℕ, 0 < q → ∀ᶠ Y : ℕ in atTop,
      ∀ b g : ℕ → ℂ, Multiplicative b → OneBounded b → OneBounded g →
      (∀ p, Nat.Prime p → p ∉ P → b p = f p) →
      ∀ (Z : Finset ℕ) (c : ℕ → ℂ),
      (∀ z ∈ Z, M < (z : ℝ) ∧ (z : ℝ) ≤ τ * M ∧
        HasNoPrimeFactorBelow (Real.exp (B ^ (9999 / 10000 : ℝ))) z) →
      (∀ z ∈ Z, ‖c z‖ ≤ 1) →
      ‖weightedRoughShiftAverage (fun n => b (q * n)) (fun n => g (q * n)) Z c h Y‖ ≤
        C * B ^ (-11 / 10 : ℝ) * smoothReciprocalProduct q.primeFactors (1 / 2 : ℝ) := by
  obtain ⟨C, hC, hrough⟩ := qualitative_dilated_rough_shifts hM hMRT hfnp hf h hh
    (C₀ + 1) (by linarith)
  refine ⟨C, hC, ?_⟩
  filter_upwards [hrough, eventually_ge_atTop 1] with B hb hB
  intro P M τ hτ₁ hτ₂ hMlower hMupper q hq
  have hτpos : 0 < τ := zero_lt_one.trans hτ₁
  have hMpos : 0 < M := (div_pos (Real.exp_pos _) hτpos).trans_le hMlower
  have hMc : M ≤ (Nat.ceil M : ℝ) := Nat.le_ceil M
  have hDlower : (1 / 2 : ℝ) * Real.exp (B ^ (9999 / 10000 : ℝ)) ≤ Nat.ceil M := by
    have ht := (div_le_iff₀ hτpos).mp hMlower
    nlinarith only [ht, hτ₂, hMpos, hMc]
  have hDupper := ceil_exp_scale_bound (B ^ (2 : ℕ)) C₀ M (by nlinarith) hC₀ hMpos.le hMupper
  filter_upwards [hb P (Nat.ceil M) hDlower hDupper q hq] with Y hy
  intro b g hbm hbb hgb heq Z c hZ hc
  apply hy b g hbm hbb hgb heq Z c _ hc
  intro z hz
  have hzw := rough_bin_ceil_window M τ hMpos hτ₂ z ⟨(hZ z hz).1, (hZ z hz).2.1⟩
  exact ⟨hzw.1, hzw.2, (hZ z hz).2.2⟩

theorem qualitative_dilated_rough_shifts_real_bins_right (hM : PrimeReciprocalInput)
    (hMRT : MRTShortExponentialInput) {f : ℕ → ℂ}
    (hfnp : UniformlyNonpretentious f) (hf : OneBounded f)
    (h : ℕ) (hh : 0 < h) (C₀ : ℝ) (hC₀ : 1 ≤ C₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ B : ℝ in atTop,
      ∀ (P : Finset ℕ) (M τ : ℝ), 1 < τ → τ < 2 →
      Real.exp (B ^ (9999 / 10000 : ℝ)) / τ ≤ M →
      M ≤ Real.exp (C₀ * B ^ (2 : ℕ)) →
      ∀ q : ℕ, 0 < q → ∀ᶠ Y : ℕ in atTop,
      ∀ b g : ℕ → ℂ, OneBounded b → Multiplicative g → OneBounded g →
      (∀ p, Nat.Prime p → p ∉ P → g p = f p) →
      ∀ (Z : Finset ℕ) (c : ℕ → ℂ),
      (∀ z ∈ Z, M < (z : ℝ) ∧ (z : ℝ) ≤ τ * M ∧
        HasNoPrimeFactorBelow (Real.exp (B ^ (9999 / 10000 : ℝ))) z) →
      (∀ z ∈ Z, ‖c z‖ ≤ 1) →
      ‖weightedRoughShiftAverage (fun n => b (q * n)) (fun n => g (q * n)) Z c h Y‖ ≤
        C * B ^ (-11 / 10 : ℝ) * smoothReciprocalProduct q.primeFactors (1 / 2 : ℝ) := by
  obtain ⟨C, hC, hrough⟩ := qualitative_dilated_rough_shifts_right hM hMRT hfnp hf h hh
    (C₀ + 1) (by linarith)
  refine ⟨C, hC, ?_⟩
  filter_upwards [hrough, eventually_ge_atTop 1] with B hb hB
  intro P M τ hτ₁ hτ₂ hMlower hMupper q hq
  have hτpos : 0 < τ := zero_lt_one.trans hτ₁
  have hMpos : 0 < M := (div_pos (Real.exp_pos _) hτpos).trans_le hMlower
  have hMc : M ≤ (Nat.ceil M : ℝ) := Nat.le_ceil M
  have hDlower : (1 / 2 : ℝ) * Real.exp (B ^ (9999 / 10000 : ℝ)) ≤ Nat.ceil M := by
    have ht := (div_le_iff₀ hτpos).mp hMlower
    nlinarith only [ht, hτ₂, hMpos, hMc]
  have hDupper := ceil_exp_scale_bound (B ^ (2 : ℕ)) C₀ M (by nlinarith) hC₀ hMpos.le hMupper
  filter_upwards [hb P (Nat.ceil M) hDlower hDupper q hq] with Y hy
  intro b g hbb hgm hgb heq Z c hZ hc
  apply hy b g hbb hgm hgb heq Z c _ hc
  intro z hz
  have hzw := rough_bin_ceil_window M τ hMpos hτ₂ z ⟨(hZ z hz).1, (hZ z hz).2.1⟩
  exact ⟨hzw.1, hzw.2, (hZ z hz).2.2⟩

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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.QualitativePartialCentering
namespace OAI

/-! Direct dilation gives qualitative centering for the actual complex
partial-tuple terms. The eventual cutoff is allowed to depend on the fixed
finite prime families, while the analytic constant is independent of them. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical

lemma qualitative_dilated_fixed_factors_oai (hM : PrimeReciprocalInput)
    (hMRT : MRTShortExponentialInput) {F G : ℕ → ℂ}
    (hFm : Multiplicative F) (hGm : Multiplicative G)
    (hF : OneBounded F) (hG : OneBounded G)
    (hnp : UniformlyNonpretentious F ∨ UniformlyNonpretentious G)
    (h : ℕ) (hh : 0 < h) (C₀ : ℝ) (hC₀ : 1 ≤ C₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ B : ℝ in atTop,
      ∀ (u : ℕ), 0 < u → ∀ M τ : ℝ, 1 < τ → τ < 2 →
      Real.exp (B ^ (9999 / 10000 : ℝ)) / τ ≤ M →
      M ≤ Real.exp (C₀ * B ^ (2 : ℕ)) →
      ∀ᶠ Y : ℕ in atTop, ∀ Z : Finset ℕ,
      (∀ z ∈ Z, M < (z : ℝ) ∧ (z : ℝ) ≤ τ * M ∧
        HasNoPrimeFactorBelow (Real.exp (B ^ (9999 / 10000 : ℝ))) z) →
      ‖weightedRoughShiftAverage (fun n => F (u * n)) (fun n => G (u * n))
        Z (fun _ => 1) h Y‖ ≤
        C * B ^ (-11 / 10 : ℝ) * smoothReciprocalProduct u.primeFactors (1 / 2 : ℝ) := by
  rcases hnp with hnp | hnp
  · obtain ⟨C, hC, hb⟩ := qualitative_dilated_rough_shifts_real_bins hM hMRT hnp hF h hh C₀ hC₀
    refine ⟨C, hC, ?_⟩
    filter_upwards [hb] with B hb
    intro u hu M τ hτ₁ hτ₂ hlow hupp
    filter_upwards [hb ∅ M τ hτ₁ hτ₂ hlow hupp u hu] with Y hY
    intro Z hZ
    exact hY F G hFm hF hG (fun _ _ _ => rfl) Z (fun _ => 1) hZ (by simp)
  · obtain ⟨C, hC, hb⟩ := qualitative_dilated_rough_shifts_real_bins_right hM hMRT hnp hG h hh C₀ hC₀
    refine ⟨C, hC, ?_⟩
    filter_upwards [hb] with B hb
    intro u hu M τ hτ₁ hτ₂ hlow hupp
    filter_upwards [hb ∅ M τ hτ₁ hτ₂ hlow hupp u hu] with Y hY
    intro Z hZ
    exact hY F G hF hGm hG (fun _ _ _ => rfl) Z (fun _ => 1) hZ (by simp)


end TwoPointCorrelations

end OAI

end

theorem solution : type_of% @OAI.TwoPointCorrelations.qualitative_dilated_fixed_factors_oai := @OAI.TwoPointCorrelations.qualitative_dilated_fixed_factors_oai
