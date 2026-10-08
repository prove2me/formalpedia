-- Prove2me | solution 1 for OAI.TwoPointCorrelations.quantitative_partial_tuple_bin
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T02:53:08.043226+00:00
-- url     : https://prove2.me/submissions/185142ac-f815-4515-a3ae-91ba6f812f09

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs
import Theorems.Thm_OAI_TwoPointCorrelations_PrimeReciprocalInput_rough_fourier

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




theorem liouville_oneBounded : OneBounded liouville := by
  intro n hn
  have hs : ‖liouville n‖ ^ 2 = 1 := by
    rw [← norm_pow, liouville_sq hn.ne', norm_one]
  nlinarith [norm_nonneg (liouville n)]

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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.RescaledPrefixSums
namespace OAI

/-! Finite weighted assembly at the actual divisor scale `Y = X/u`.
The factor `1/u` is retained exactly, including floor cutoffs. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical


lemma prefix_norm_of_average_bound (F : ℕ → ℂ) (N : ℕ) (E : ℝ)
    (hF : ‖positivePrefix F N / (N : ℂ)‖ ≤ E) :
    ‖positivePrefix F N‖ ≤ (N : ℝ) * E := by
  by_cases hN : N = 0
  · simp [hN, positivePrefix]
  have hNp : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  rw [norm_div, Complex.norm_natCast] at hF
  have ht := (div_le_iff₀ hNp).mp hF
  nlinarith only [ht]


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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ProgressionFourier
namespace OAI

/-!
# Additive Fourier resolution of every progression class

The coefficient mass is exactly one. There is no invertibility assumption
on the class, and no frequency supremum is put inside an integral.
-/

namespace TwoPointCorrelations

open scoped _root_.BigOperators

theorem additiveCharacter_add (α β : ℝ) (n : ℕ) :
    additiveCharacter (α + β) n = additiveCharacter α n * additiveCharacter β n := by
  unfold additiveCharacter
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem stdAddChar_nat_mul (l : ℕ) [NeZero l] (a : ZMod l) (n : ℕ) :
    ZMod.stdAddChar (a * (n : ZMod l)) = additiveCharacter ((a.val : ℝ) / l) n := by
  conv_lhs => rw [← ZMod.natCast_zmod_val a, ← Nat.cast_mul]
  rw [← Int.cast_natCast, ZMod.stdAddChar_coe]
  unfold additiveCharacter
  congr 1
  push_cast
  ring

theorem zmod_indicator_fourier (l : ℕ) [NeZero l] (n b : ZMod l) :
    (if n = b then (1 : ℂ) else 0) =
      (l : ℂ)⁻¹ * ∑ a : ZMod l, ZMod.stdAddChar (a * (n - b)) := by
  classical
  rw [AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar l), ZMod.card]
  have hlc : (l : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne l
  by_cases h : n = b
  · simp [h, hlc]
  · simp [h, sub_ne_zero.mpr h]

theorem progression_fourier_identity (S : Finset ℕ) (v : ℕ → ℂ)
    (l : ℕ) [NeZero l] (b : ZMod l) (α : ℝ) :
    (∑ n ∈ S, if (n : ZMod l) = b then v n * additiveCharacter α n else 0) =
      (l : ℂ)⁻¹ * ∑ a : ZMod l, ZMod.stdAddChar (-(a * b)) *
        ∑ n ∈ S, v n * additiveCharacter (α + (a.val : ℝ) / l) n := by
  classical
  have hi (n : ℕ) :
      (if (n : ZMod l) = b then v n * additiveCharacter α n else 0) =
        (l : ℂ)⁻¹ * ∑ a : ZMod l,
          ZMod.stdAddChar (-(a * b)) * (v n * additiveCharacter (α + (a.val : ℝ) / l) n) := by
    have h := congrArg (fun z : ℂ => z * (v n * additiveCharacter α n))
      (zmod_indicator_fourier l (n : ZMod l) b)
    simp only [ite_mul, one_mul, zero_mul] at h
    rw [h, mul_assoc]
    congr 1
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    rw [additiveCharacter_add, ← stdAddChar_nat_mul l a n]
    have hm : a * ((n : ZMod l) - b) = -(a * b) + a * n := by ring
    rw [hm, AddChar.map_add_eq_mul]
    ring
  simp_rw [hi]
  rw [← Finset.mul_sum, Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]

/-- The progression mask averages `l` shifted frequencies with total
absolute coefficient mass one. -/
theorem norm_progression_fourier_le (S : Finset ℕ) (v : ℕ → ℂ)
    (l : ℕ) [NeZero l] (b : ZMod l) (α : ℝ) :
    ‖∑ n ∈ S, if (n : ZMod l) = b then v n * additiveCharacter α n else 0‖ ≤
      (l : ℝ)⁻¹ * ∑ a : ZMod l,
        ‖∑ n ∈ S, v n * additiveCharacter (α + (a.val : ℝ) / l) n‖ := by
  rw [progression_fourier_identity, norm_mul, norm_inv, Complex.norm_natCast]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg l))
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro a _
  simp only [norm_mul, ZMod.stdAddChar_apply, Circle.norm_coe, one_mul, le_refl]

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

lemma shortExponentialSum_on_unit_cell (b : ℕ → ℂ) (D : ℕ) (α : ℝ)
    (v : ℕ) {y : ℝ} (hy : y ∈ Set.Ico (v : ℝ) (v + 1)) :
    shortExponentialSum b D α y = shortExponentialSum b D α v := by
  have hy0 : 0 ≤ y := (Nat.cast_nonneg v).trans hy.1
  have hf := Nat.floor_eq_on_Ico v y hy
  unfold shortExponentialSum
  rw [Nat.floor_add_natCast hy0, hf, Nat.floor_natCast,
    Nat.floor_add_natCast (Nat.cast_nonneg v) D, Nat.floor_natCast]

lemma shortExponentialSum_unit_integrable (b : ℕ → ℂ) (D : ℕ) (α : ℝ) (v : ℕ) :
    IntervalIntegrable (fun y => ‖shortExponentialSum b D α y‖)
      volume (v : ℝ) (v + 1) := by
  apply (intervalIntegrable_const : IntervalIntegrable
    (fun _ : ℝ => ‖shortExponentialSum b D α v‖) volume (v : ℝ) (v + 1)).congr_uIoo
  intro y hy
  rw [Set.uIoo_of_le (by linarith : (v : ℝ) ≤ v + 1)] at hy
  exact congrArg norm (shortExponentialSum_on_unit_cell b D α v ⟨hy.1.le, hy.2⟩).symm

lemma integral_shortExponentialSum_unit (b : ℕ → ℂ) (D : ℕ) (α : ℝ) (v : ℕ) :
    (∫ y in (v : ℝ)..(v + 1), ‖shortExponentialSum b D α y‖) =
      ‖shortExponentialSum b D α v‖ := by
  calc
    _ = ∫ _y in (v : ℝ)..(v + 1), ‖shortExponentialSum b D α v‖ := by
      apply intervalIntegral.integral_congr_Ioo_of_le (by linarith)
      intro y hy
      exact congrArg norm (shortExponentialSum_on_unit_cell b D α v ⟨hy.1.le, hy.2⟩)
    _ = _ := by simp

/-- Exact unit-cell decomposition, with no endpoint error. -/
theorem shortExponentialIntegral_eq_sum (b : ℕ → ℂ) (X D : ℕ) (α : ℝ) :
    shortExponentialIntegral b X D α =
      ∑ v ∈ range X, ‖shortExponentialSum b D α v‖ := by
  unfold shortExponentialIntegral
  symm
  calc
    _ = ∑ v ∈ range X, ∫ y in (v : ℝ)..((v + 1 : ℕ) : ℝ),
        ‖shortExponentialSum b D α y‖ := by
      apply sum_congr rfl
      intro v _
      simpa only [Nat.cast_add, Nat.cast_one] using
        (integral_shortExponentialSum_unit b D α v).symm
    _ = _ := by
      simpa only [Nat.cast_zero] using
        (intervalIntegral.sum_integral_adjacent_intervals
          (a := fun n : ℕ => (n : ℝ)) (n := X)
          (fun v _ => by simpa only [Nat.cast_add, Nat.cast_one] using
            shortExponentialSum_unit_integrable b D α v))

/-- The positive integer origins used in the manuscript occupy all but
the first unit cell of the published integral. -/
theorem sum_positive_shortExponentialSum_le (b : ℕ → ℂ) (Y D : ℕ) (α : ℝ) :
    (∑ v ∈ range Y, ‖shortExponentialSum b D α (v + 1 : ℕ)‖) ≤
      shortExponentialIntegral b (Y + 1) D α := by
  rw [shortExponentialIntegral_eq_sum, sum_range_succ']
  exact le_add_of_nonneg_right (norm_nonneg _)

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

lemma shortExponentialSum_at_nat (b : ℕ → ℂ) (D v : ℕ) (α : ℝ) :
    shortExponentialSum b D α v =
      ∑ n ∈ Icc (v + 1) (v + D), b n * additiveCharacter α n := by
  simp only [shortExponentialSum, Nat.floor_natCast,
    Nat.floor_add_natCast (Nat.cast_nonneg v) D]

lemma additiveCharacter_nat_add (α : ℝ) (m n : ℕ) :
    additiveCharacter α (m + n) = additiveCharacter α m * additiveCharacter α n := by
  unfold additiveCharacter
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma norm_additiveCharacter (α : ℝ) (n : ℕ) : ‖additiveCharacter α n‖ = 1 := by
  exact Complex.norm_exp_ofReal_mul_I _


lemma shortExponentialSum_eq_window (b : ℕ → ℂ) (D v : ℕ) (α : ℝ) :
    shortExponentialSum b D α v = additiveCharacter α v * shortWindowSum b D α v := by
  rw [shortExponentialSum_at_nat, sum_Icc_shift]
  unfold shortWindowSum
  rw [mul_sum]
  apply sum_congr rfl
  intro m _
  rw [show v + m + 1 = v + (m + 1) by omega, additiveCharacter_nat_add]
  ring

lemma norm_shortExponentialSum_eq_window (b : ℕ → ℂ) (D v : ℕ) (α : ℝ) :
    ‖shortExponentialSum b D α v‖ = ‖shortWindowSum b D α v‖ := by
  rw [shortExponentialSum_eq_window, norm_mul, norm_additiveCharacter, one_mul]

/-- A uniform fixed-frequency integral bound controls every progression
class of actual discrete windows, including nonunit classes. -/
theorem progression_short_sum_from_integral (b : ℕ → ℂ) (D Y l : ℕ)
    [NeZero l] (a : ZMod l) (α K : ℝ)
    (hK : ∀ β : ℝ, shortExponentialIntegral b (Y + 1) D β ≤ K) :
    (∑ v ∈ range Y, ‖∑ n ∈ Icc (v + 2) (v + 1 + D),
      if (n : ZMod l) = a then b n * additiveCharacter α n else 0‖) ≤ K := by
  calc
    _ ≤ ∑ v ∈ range Y, (l : ℝ)⁻¹ * ∑ j : ZMod l,
        ‖∑ n ∈ Icc (v + 2) (v + 1 + D),
          b n * additiveCharacter (α + (j.val : ℝ) / l) n‖ :=
      sum_le_sum (fun v _ => norm_progression_fourier_le _ b l a α)
    _ = (l : ℝ)⁻¹ * ∑ j : ZMod l, ∑ v ∈ range Y,
        ‖shortExponentialSum b D (α + (j.val : ℝ) / l) (v + 1 : ℕ)‖ := by
      rw [← mul_sum, sum_comm]
      congr 1
      apply sum_congr rfl
      intro j _
      apply sum_congr rfl
      intro v _
      rw [shortExponentialSum_at_nat]
    _ ≤ (l : ℝ)⁻¹ * ∑ _j : ZMod l, K := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact sum_le_sum (fun j _ =>
        (sum_positive_shortExponentialSum_le b Y D _).trans (hK _))
    _ = K := by
      simp only [sum_const, card_univ, ZMod.card, nsmul_eq_mul]
      have hl : (l : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne l
      field_simp


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.RoughShiftConvolution
namespace OAI

/-! Exact Fourier convolution for the translated rough-shift average. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.Classical



/-- Orthogonality imposes precisely `a=m+hz`; the long window contains
every selected frequency, so there is no further truncation error. -/
theorem rough_shift_convolution (f g : ℕ → ℂ) (Z : Finset ℕ) (D h v : ℕ)
    (hZ : ∀ z ∈ Z, z ≤ 2 * D) :
    (∫ θ, roughFourierPolynomial Z h θ * forwardWindowPolynomial f D v θ *
      backwardWindowPolynomial g ((2 * h + 1) * D) v θ ∂AddCircle.haarAddCircle) =
      ∑ z ∈ Z, (z : ℂ)⁻¹ * ∑ m ∈ Icc 1 D, f (v + m) * g (v + m + h * z) := by
  unfold roughFourierPolynomial forwardWindowPolynomial backwardWindowPolynomial
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
theorem summed_rough_shift_convolution (f g : ℕ → ℂ) (Z : Finset ℕ)
    (D h Y : ℕ) (hZ : ∀ z ∈ Z, z ≤ 2 * D) :
    (∑ v ∈ range Y, ∫ θ,
      roughFourierPolynomial Z h θ * forwardWindowPolynomial f D (v + 1) θ *
      backwardWindowPolynomial g ((2 * h + 1) * D) (v + 1) θ
        ∂AddCircle.haarAddCircle) =
      ∑ m ∈ Icc 1 D, ∑ v ∈ range Y, ∑ z ∈ Z,
        (z : ℂ)⁻¹ * (f (v + 1 + m) * g (v + 1 + m + h * z)) := by
  simp_rw [rough_shift_convolution f g Z D h _ hZ, mul_sum]
  calc
    _ = ∑ v ∈ range Y, ∑ m ∈ Icc 1 D, ∑ z ∈ Z,
        (z : ℂ)⁻¹ * (f (v + 1 + m) * g (v + 1 + m + h * z)) := by
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

lemma fourier_nat_at_real (m : ℕ) (θ : ℝ) :
    fourier (m : ℤ) (θ : AddCircle (1 : ℝ)) = additiveCharacter θ m := by
  rw [fourier_coe_apply]
  unfold additiveCharacter
  congr 1
  push_cast
  ring

lemma forwardWindowPolynomial_at_real (f : ℕ → ℂ) (D v : ℕ) (θ : ℝ) :
    forwardWindowPolynomial f D v (θ : AddCircle (1 : ℝ)) = shortWindowSum f D θ v := by
  unfold forwardWindowPolynomial fourierPolynomial
  simp_rw [fourier_nat_at_real]
  simpa only [Nat.zero_add, Nat.add_assoc, shortWindowSum] using
    (sum_Icc_shift (fun m => f (v + m) * additiveCharacter θ m) 0 D)


lemma OneBounded.progressionSequence {f : ℕ → ℂ} (hf : OneBounded f)
    (l : ℕ) [NeZero l] (a : ZMod l) : OneBounded (progressionSequence f l a) := by
  intro n hn
  unfold TwoPointCorrelations.progressionSequence
  split_ifs
  · exact hf n hn
  · simp

/-- Every circle frequency is represented by a real frequency, and the
unimodular origin phase disappears before applying MRT. -/
theorem progression_window_sum_from_integral (f : ℕ → ℂ) (D Y l : ℕ)
    [NeZero l] (a : ZMod l) (K : ℝ)
    (hK : ∀ α, shortExponentialIntegral f (Y + 1) D α ≤ K)
    (θ : AddCircle (1 : ℝ)) :
    (∑ v ∈ range Y,
      ‖forwardWindowPolynomial (progressionSequence f l a) D (v + 1) θ‖) ≤ K := by
  obtain ⟨α, rfl⟩ := QuotientAddGroup.mk_surjective θ
  calc
    _ = ∑ v ∈ range Y, ‖∑ n ∈ Icc (v + 2) (v + 1 + D),
        if (n : ZMod l) = a then f n * additiveCharacter α n else 0‖ := by
      apply sum_congr rfl
      intro v _
      rw [forwardWindowPolynomial_at_real, ← norm_shortExponentialSum_eq_window,
        shortExponentialSum_at_nat]
      simp only [progressionSequence, ite_mul, zero_mul]
    _ ≤ K := progression_short_sum_from_integral f D Y l a α K hK

theorem MRTLiouvilleShortInput.progression_window_polynomials
    (hMRT : MRTLiouvilleShortInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Y D l : ℕ), 10 ≤ D → D ≤ Y + 1 →
      ∀ [NeZero l] (a : ZMod l) (θ : AddCircle (1 : ℝ)),
        (∑ v ∈ range Y,
          ‖forwardWindowPolynomial (progressionSequence liouville l a) D (v + 1) θ‖) ≤
          C * (D : ℝ) * (Y + 1 : ℕ) * mrtShortError (Y + 1) D := by
  obtain ⟨C, hC, hbound⟩ := hMRT
  refine ⟨C, hC, ?_⟩
  intro Y D l hD hDY _ a θ
  exact progression_window_sum_from_integral liouville D Y l a _
    (fun α => hbound (Y + 1) D hD hDY α) θ

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



lemma norm_roughShiftProfile_le (f g : ℕ → ℂ) (hf : OneBounded f) (hg : OneBounded g)
    (Z : Finset ℕ) (h n : ℕ) (hn : 0 < n) :
    ‖roughShiftProfile f g Z h n‖ ≤ ∑ z ∈ Z, (z : ℝ)⁻¹ := by
  have hh := norm_weightedShiftProfile_le Z (fun z => (z : ℂ)⁻¹)
    (fun z => h * z) f g hf hg 1 0 n hn
  simpa only [weightedShiftProfile, roughShiftProfile, Nat.mod_one, ite_true,
    norm_inv, Complex.norm_natCast] using hh

lemma translated_roughShiftProfile_eq (f g : ℕ → ℂ) (Z : Finset ℕ) (D h Y : ℕ)
    (hZ : ∀ z ∈ Z, z ≤ 2 * D) :
    translatedPrefixAverage (roughShiftProfile f g Z h) Y D =
      (D : ℂ)⁻¹ * ∑ v ∈ range Y, ∫ θ,
        roughFourierPolynomial Z h θ * forwardWindowPolynomial f D (v + 1) θ *
          backwardWindowPolynomial g ((2 * h + 1) * D) (v + 1) θ
            ∂AddCircle.haarAddCircle := by
  unfold translatedPrefixAverage
  congr 1
  calc
    _ = ∑ m ∈ Icc 1 D,
        positivePrefix (fun n => roughShiftProfile f g Z h (n + m)) Y := by
      simpa only [Nat.zero_add] using (sum_Icc_shift
        (fun m => positivePrefix (fun n => roughShiftProfile f g Z h (n + m)) Y) 0 D).symm
    _ = _ := by
      rw [summed_rough_shift_convolution f g Z D h Y hZ]
      rfl

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

/-- All Fourier ingredients are now attached to the concrete two windows. -/
theorem rough_convolution_sum_bound (f g : ℕ → ℂ) (hf : OneBounded f)
    (hg : OneBounded g) (Z : Finset ℕ) (D h Y : ℕ)
    (ε U V K : ℝ) (hε : 0 < ε) (hU : 0 ≤ U) (hK : 0 ≤ K)
    (hB : ∀ θ, ‖roughFourierPolynomial Z h θ‖ ≤ U)
    (hV : (∫ θ, ‖roughFourierPolynomial Z h θ‖ ^ 4
      ∂AddCircle.haarAddCircle) ≤ V)
    (hF : ∀ θ, (∑ v ∈ range Y, ‖forwardWindowPolynomial f D (v + 1) θ‖) ≤ K) :
    ‖∑ v ∈ range Y, ∫ θ,
      roughFourierPolynomial Z h θ * forwardWindowPolynomial f D (v + 1) θ *
        backwardWindowPolynomial g ((2 * h + 1) * D) (v + 1) θ
          ∂AddCircle.haarAddCircle‖ ≤
      ε * ((Y : ℝ) * (Real.sqrt D * Real.sqrt ((2 * h + 1) * D))) +
        (U * ((2 * h + 1) * D) * K / ε ^ 4) * V := by
  have hh := fourier_region_bound (range Y) (roughFourierPolynomial Z h)
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

lemma normalized_translated_roughShift_bound (f g : ℕ → ℂ)
    (Z : Finset ℕ) (D h Y : ℕ) (hD : 0 < D) (hY : 0 < Y)
    (hZ : ∀ z ∈ Z, z ≤ 2 * D) (W : ℝ)
    (hW : ‖∑ v ∈ range Y, ∫ θ,
      roughFourierPolynomial Z h θ * forwardWindowPolynomial f D (v + 1) θ *
        backwardWindowPolynomial g ((2 * h + 1) * D) (v + 1) θ
          ∂AddCircle.haarAddCircle‖ ≤ W) :
    ‖translatedPrefixAverage (roughShiftProfile f g Z h) Y D / (Y : ℂ)‖ ≤
      W / ((Y : ℝ) * D) := by
  rw [translated_roughShiftProfile_eq f g Z D h Y hZ,
    norm_div, norm_mul, norm_inv, Complex.norm_natCast, Complex.norm_natCast]
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have hYr : (0 : ℝ) < Y := by exact_mod_cast hY
  calc
    _ ≤ (D : ℝ)⁻¹ * W / Y :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hW (by positivity)) hYr.le
    _ = _ := by simp only [div_eq_mul_inv, mul_inv_rev]; ring

/-- The finite correlation bound before inserting the sieve estimates and
the size estimates for the published MRT error. -/
theorem rough_shift_average_bound (f g : ℕ → ℂ) (hf : OneBounded f)
    (hg : OneBounded g) (Z : Finset ℕ) (D h Y : ℕ) (hD : 0 < D) (hY : 0 < Y)
    (hZ : ∀ z ∈ Z, z ≤ 2 * D)
    (ε U V K : ℝ) (hε : 0 < ε) (hU : 0 ≤ U) (hK : 0 ≤ K)
    (hB : ∀ θ, ‖roughFourierPolynomial Z h θ‖ ≤ U)
    (hV : (∫ θ, ‖roughFourierPolynomial Z h θ‖ ^ 4
      ∂AddCircle.haarAddCircle) ≤ V)
    (hF : ∀ θ, (∑ v ∈ range Y, ‖forwardWindowPolynomial f D (v + 1) θ‖) ≤ K) :
    ‖roughShiftAverage f g Z h Y‖ ≤
      2 * (D : ℝ) / Y * (∑ z ∈ Z, (z : ℝ)⁻¹) +
      (ε * ((Y : ℝ) * (Real.sqrt D * Real.sqrt ((2 * h + 1) * D))) +
        (U * ((2 * h + 1) * D) * K / ε ^ 4) * V) / ((Y : ℝ) * D) := by
  let u := roughShiftProfile f g Z h
  have he := norm_normalized_translation_error u Y D hY hD
    (∑ z ∈ Z, (z : ℝ)⁻¹) (sum_nonneg (fun z _ => by positivity))
    (fun n hn => norm_roughShiftProfile_le f g hf hg Z h n hn)
  have hc := normalized_translated_roughShift_bound f g Z D h Y hD hY hZ _
    (rough_convolution_sum_bound f g hf hg Z D h Y ε U V K hε hU hK hB hV hF)
  calc
    ‖roughShiftAverage f g Z h Y‖ = ‖translatedPrefixAverage u Y D / (Y : ℂ) -
        (translatedPrefixAverage u Y D - positivePrefix u Y) / (Y : ℂ)‖ := by
      congr 1
      dsimp [roughShiftAverage, u]
      ring
    _ ≤ ‖translatedPrefixAverage u Y D / (Y : ℂ)‖ +
        ‖(translatedPrefixAverage u Y D - positivePrefix u Y) / (Y : ℂ)‖ := norm_sub_le _ _
    _ ≤ _ := by simpa only [add_comm] using add_le_add hc he

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTScale
namespace OAI

/-! Numerical scale estimates for the published MRT short-sum error. -/

namespace TwoPointCorrelations

open _root_.Filter

lemma eventually_four_log_le_small_power :
    ∀ᶠ L : ℝ in atTop, 4 * Real.log L ≤ L ^ (39 / 200 : ℝ) := by
  have hh := (isLittleO_log_rpow_atTop
    (show 0 < (39 / 200 : ℝ) by norm_num)).bound (show 0 < (1 / 4 : ℝ) by norm_num)
  filter_upwards [eventually_ge_atTop 1, hh] with L hL h
  have hLp : 0 < L := by linarith
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hL),
    Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hLp _)] at h
  linarith

/-- The two published error terms have the required power saving under
the precise logarithmic consequences of the manuscript scale choices. -/
theorem eventually_mrtShortError_scale :
    ∀ᶠ L : ℝ in atTop, ∀ X D : ℕ,
      (1 / 2 : ℝ) * L ^ (199 / 200 : ℝ) ≤ Real.log D →
      Real.log D ≤ 2 * L → L ^ (560 : ℝ) ≤ Real.log X →
      mrtShortError X D ≤ 2 * L ^ (-4 / 5 : ℝ) := by
  filter_upwards [eventually_ge_atTop 2,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop 1),
    eventually_four_log_le_small_power] with L hL hlog hsmall
  intro X D hDlower hDupper hXlower
  have hLp : 0 < L := by linarith
  have hDlog : 0 < Real.log (D : ℝ) :=
    (mul_pos (by norm_num) (Real.rpow_pos_of_pos hLp _)).trans_le hDlower
  have hloglog : Real.log (Real.log (D : ℝ)) ≤ 2 * Real.log L := by
    have hh := Real.log_le_log hDlog hDupper
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hLp.ne'] at hh
    have htwo : Real.log 2 ≤ 1 := by
      have ht := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      linarith
    linarith
  have hfirst : Real.log (Real.log (D : ℝ)) / Real.log D ≤ L ^ (-4 / 5 : ℝ) := by
    calc
      _ ≤ (2 * Real.log L) / Real.log D := div_le_div_of_nonneg_right hloglog hDlog.le
      _ ≤ (2 * Real.log L) / ((1 / 2 : ℝ) * L ^ (199 / 200 : ℝ)) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hDlower
      _ = (4 * Real.log L) / L ^ (199 / 200 : ℝ) := by ring
      _ ≤ L ^ (39 / 200 : ℝ) / L ^ (199 / 200 : ℝ) :=
        div_le_div_of_nonneg_right hsmall (by positivity)
      _ = L ^ (-4 / 5 : ℝ) := by rw [← Real.rpow_sub hLp]; norm_num
  have hsecond : (Real.log (X : ℝ)) ^ (-1 / 700 : ℝ) ≤ L ^ (-4 / 5 : ℝ) := by
    calc
      _ ≤ (L ^ (560 : ℝ)) ^ (-1 / 700 : ℝ) :=
        Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hLp _) hXlower (by norm_num)
      _ = _ := by rw [← Real.rpow_mul hLp.le]; norm_num
  exact add_le_add hfirst hsecond |>.trans_eq (by ring)

/-- The original exponential cutoff hypotheses imply all logarithmic
conditions above, with no integer-floor or endpoint loss. -/
theorem eventually_mrtShortError_cutoffs :
    ∀ᶠ L : ℝ in atTop, ∀ X D : ℕ,
      (1 / 2 : ℝ) * Real.exp (L ^ (199 / 200 : ℝ)) ≤ D →
      (D : ℝ) ≤ Real.exp (2 * L) →
      Real.exp ((1 / 2 : ℝ) * L ^ (1000 : ℝ)) ≤ X →
      mrtShortError X D ≤ 2 * L ^ (-4 / 5 : ℝ) := by
  have hsmall := (tendsto_rpow_atTop
    (show 0 < (199 / 200 : ℝ) by norm_num)).eventually
      (eventually_ge_atTop (2 * Real.log 2))
  have hlarge := (tendsto_rpow_atTop
    (show 0 < (440 : ℝ) by norm_num)).eventually (eventually_ge_atTop 2)
  filter_upwards [eventually_ge_atTop 1, eventually_mrtShortError_scale, hsmall, hlarge]
    with L hL hscale hs hl
  intro X D hDlower hDupper hXlower
  have hLp : 0 < L := by linarith
  have hDp : (0 : ℝ) < D :=
    (mul_pos (by norm_num) (Real.exp_pos _)).trans_le hDlower
  apply hscale X D
  · have hh := Real.log_le_log (show (0 : ℝ) < (1 / 2 : ℝ) *
        Real.exp (L ^ (199 / 200 : ℝ)) by positivity) hDlower
    rw [Real.log_mul (by norm_num : (1 / 2 : ℝ) ≠ 0) (Real.exp_ne_zero _),
      Real.log_exp] at hh
    have hhalf : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
      rw [one_div, Real.log_inv]
    rw [hhalf] at hh
    linarith
  · have hh := Real.log_le_log hDp hDupper
    simpa only [Real.log_exp] using hh
  · have hh := Real.log_le_log (Real.exp_pos _) hXlower
    rw [Real.log_exp] at hh
    have hp : (1 / 2 : ℝ) * L ^ (1000 : ℝ) ≥ L ^ (560 : ℝ) := by
      have he : L ^ (1000 : ℝ) = L ^ (560 : ℝ) * L ^ (440 : ℝ) := by
        rw [← Real.rpow_add hLp]
        norm_num
      rw [he]
      nlinarith [Real.rpow_pos_of_pos hLp (560 : ℝ)]
    exact hp.trans hh

/-- The published short-interval theorem now bounds the actual progression
polynomials on the manuscript scales. The bound is uniform over the circle. -/
theorem MRTLiouvilleShortInput.progression_window_scale (hMRT : MRTLiouvilleShortInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ L : ℝ in atTop, ∀ (Y D l : ℕ),
      1 ≤ Y → 10 ≤ D → D ≤ Y + 1 →
      (1 / 2 : ℝ) * Real.exp (L ^ (199 / 200 : ℝ)) ≤ D →
      (D : ℝ) ≤ Real.exp (2 * L) →
      Real.exp ((1 / 2 : ℝ) * L ^ (1000 : ℝ)) ≤ (Y + 1 : ℕ) →
      ∀ [NeZero l] (a : ZMod l) (θ : AddCircle (1 : ℝ)),
        (∑ v ∈ Finset.range Y,
          ‖forwardWindowPolynomial (progressionSequence liouville l a) D (v + 1) θ‖) ≤
            C * Y * D * L ^ (-4 / 5 : ℝ) := by
  obtain ⟨C, hC, hbound⟩ := hMRT.progression_window_polynomials
  refine ⟨4 * C, by positivity, ?_⟩
  filter_upwards [eventually_mrtShortError_cutoffs, eventually_ge_atTop 1]
    with L hscale hL
  intro Y D l hY hD hDY hDlower hDupper hYlower _ a θ
  have he := hscale (Y + 1) D hDlower hDupper hYlower
  have hYr : (1 : ℝ) ≤ Y := by exact_mod_cast hY
  have hLp : 0 < L := by linarith
  calc
    _ ≤ C * (D : ℝ) * (Y + 1 : ℕ) * mrtShortError (Y + 1) D :=
      hbound Y D l hD hDY a θ
    _ ≤ C * (D : ℝ) * (Y + 1 : ℕ) * (2 * L ^ (-4 / 5 : ℝ)) :=
      mul_le_mul_of_nonneg_left he (by positivity)
    _ ≤ C * (D : ℝ) * (2 * Y) * (2 * L ^ (-4 / 5 : ℝ)) := by
      have hy : ((Y + 1 : ℕ) : ℝ) ≤ 2 * Y := by push_cast; linarith
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hy (by positivity)) (by positivity)
    _ = _ := by ring

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

lemma rough_reciprocal_mass_le_sup (Z : Finset ℕ) (h : ℕ) (U : ℝ)
    (hU : ‖roughFourierPolynomial Z h 0‖ ≤ U) :
    (∑ z ∈ Z, (z : ℝ)⁻¹) ≤ U := by
  have he : roughFourierPolynomial Z h 0 = ((∑ z ∈ Z, (z : ℝ)⁻¹ : ℝ) : ℂ) := by
    simp only [roughFourierPolynomial, fourierPolynomial, fourier_eval_zero, mul_one,
      Complex.ofReal_sum, Complex.ofReal_inv, Complex.ofReal_natCast]
  rw [he, Complex.norm_real, Real.norm_of_nonneg
    (sum_nonneg (fun z _ => by positivity))] at hU
  exact hU

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

lemma rough_fourier_exponent_identity (L : ℝ) (hL : 0 < L) :
    L ^ (-99 / 100 : ℝ) * L ^ (-4 / 5 : ℝ) * L ^ (-99 / 25 : ℝ) /
        (L ^ (-21 / 20 : ℝ)) ^ (4 : ℕ) = L ^ (-31 / 20 : ℝ) := by
  have hp : (L ^ (-21 / 20 : ℝ)) ^ (4 : ℕ) = L ^ ((-21 / 20 : ℝ) * 4) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL.le]
    norm_num
  rw [hp, ← Real.rpow_add hL, ← Real.rpow_add hL, ← Real.rpow_sub hL]
  norm_num

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

lemma rough_high_term_identity (D h Y : ℕ) (hD : 0 < D) (hY : 0 < Y)
    (L U V K : ℝ) (hL : 0 < L) :
    (((U * L ^ (-99 / 100 : ℝ)) * ((2 * (h : ℝ) + 1) * D) *
        (K * Y * D * L ^ (-4 / 5 : ℝ)) / (L ^ (-21 / 20 : ℝ)) ^ (4 : ℕ)) *
        (V / D * L ^ (-99 / 25 : ℝ))) / ((Y : ℝ) * D) =
      (2 * (h : ℝ) + 1) * U * V * K * L ^ (-31 / 20 : ℝ) := by
  have hDr : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  have hYr : (Y : ℝ) ≠ 0 := by exact_mod_cast hY.ne'
  have hpow : L ^ (-21 / 20 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hL _).ne'
  calc
    _ = ((2 * (h : ℝ) + 1) * U * V * K) *
        (L ^ (-99 / 100 : ℝ) * L ^ (-4 / 5 : ℝ) * L ^ (-99 / 25 : ℝ) /
          (L ^ (-21 / 20 : ℝ)) ^ (4 : ℕ)) := by
      field_simp
    _ = _ := by rw [rough_fourier_exponent_identity L hL]

/-- The Fourier bound has the exact exponent `-21/20`. The stronger
`-31/20` contribution is absorbed only at this final numerical step. -/
theorem rough_shift_power_bound (f g : ℕ → ℂ) (hf : OneBounded f)
    (hg : OneBounded g) (Z : Finset ℕ) (D h Y : ℕ) (hD : 0 < D) (hY : 0 < Y)
    (hZ : ∀ z ∈ Z, z ≤ 2 * D) (L U V K : ℝ)
    (hL : 1 ≤ L) (hU : 0 ≤ U) (hV : 0 ≤ V) (hK : 0 ≤ K)
    (hendpoint : (D : ℝ) / Y ≤ L ^ (-21 / 20 : ℝ))
    (hB : ∀ θ, ‖roughFourierPolynomial Z h θ‖ ≤ U * L ^ (-99 / 100 : ℝ))
    (hfourth : (∫ θ, ‖roughFourierPolynomial Z h θ‖ ^ 4
      ∂AddCircle.haarAddCircle) ≤ V / D * L ^ (-99 / 25 : ℝ))
    (hF : ∀ θ, (∑ v ∈ range Y, ‖forwardWindowPolynomial f D (v + 1) θ‖) ≤
      K * Y * D * L ^ (-4 / 5 : ℝ)) :
    ‖roughShiftAverage f g Z h Y‖ ≤
      (2 * U + (2 * (h : ℝ) + 1) + (2 * (h : ℝ) + 1) * U * V * K) *
        L ^ (-21 / 20 : ℝ) := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hmass : (∑ z ∈ Z, (z : ℝ)⁻¹) ≤ U := by
    apply (rough_reciprocal_mass_le_sup Z h _ (hB 0)).trans
    have hp : L ^ (-99 / 100 : ℝ) ≤ 1 := by
      simpa only [Real.rpow_zero] using
        Real.rpow_le_rpow_of_exponent_le hL (show (-99 / 100 : ℝ) ≤ 0 by norm_num)
    exact (mul_le_mul_of_nonneg_left hp hU).trans_eq (mul_one U)
  have he : 2 * (D : ℝ) / Y * (∑ z ∈ Z, (z : ℝ)⁻¹) ≤
      2 * U * L ^ (-21 / 20 : ℝ) := by
    calc
      _ = 2 * ((D : ℝ) / Y) * (∑ z ∈ Z, (z : ℝ)⁻¹) := by ring
      _ ≤ 2 * L ^ (-21 / 20 : ℝ) * U :=
        mul_le_mul (mul_le_mul_of_nonneg_left hendpoint (by norm_num)) hmass
          (sum_nonneg (fun z _ => by positivity)) (by positivity)
      _ = _ := by ring
  have hraw := rough_shift_average_bound f g hf hg Z D h Y hD hY hZ
    (L ^ (-21 / 20 : ℝ)) (U * L ^ (-99 / 100 : ℝ))
    (V / D * L ^ (-99 / 25 : ℝ)) (K * Y * D * L ^ (-4 / 5 : ℝ))
    (Real.rpow_pos_of_pos hLp _) (by positivity) (by positivity) hB hfourth hF
  have hlow := rough_low_term_bound D h Y hD hY
    (L ^ (-21 / 20 : ℝ)) (Real.rpow_nonneg hLp.le _)
  have hhigh := rough_high_term_identity D h Y hD hY L U V K hLp
  have hgap : L ^ (-31 / 20 : ℝ) ≤ L ^ (-21 / 20 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hL (by norm_num)
  apply hraw.trans
  rw [add_div, hhigh]
  have ht := mul_le_mul_of_nonneg_left hgap
    (show 0 ≤ (2 * (h : ℝ) + 1) * U * V * K by positivity)
  nlinarith

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.RoughShiftEndpoints
namespace OAI

/-! The physical interval scales imply every endpoint-size condition used
in the translated rough-shift average. -/

namespace TwoPointCorrelations

open _root_.Filter

theorem rough_shift_ratio (L : ℝ) (hL : 10 ≤ L) (D Y : ℕ)
    (hD : (D : ℝ) ≤ Real.exp (2 * L))
    (hY : Real.exp ((1 / 2 : ℝ) * L ^ (1000 : ℝ)) ≤ Y) :
    (D : ℝ) / Y ≤ L ^ (-21 / 20 : ℝ) := by
  have hL₁ : 1 ≤ L := by linarith
  have hLp : 0 < L := by linarith
  have hYp : (0 : ℝ) < Y := (Real.exp_pos _).trans_le hY
  have hp : L ^ (2 : ℝ) ≤ L ^ (1000 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hL₁ (by norm_num)
  have hsq : (10 : ℝ) * L ≤ L ^ 2 := by
    have hh := mul_le_mul_of_nonneg_right hL hLp.le
    nlinarith only [hh]
  have hlog : Real.log L ≤ L := (Real.log_le_sub_one_of_pos hLp).trans (by linarith)
  have hgap : 2 * L - (1 / 2 : ℝ) * L ^ (1000 : ℝ) ≤
      Real.log L * (-21 / 20 : ℝ) := by
    norm_num only [Real.rpow_two] at hp
    nlinarith only [hp, hsq, hlog, hL]
  calc
    _ ≤ Real.exp (2 * L) / Real.exp ((1 / 2 : ℝ) * L ^ (1000 : ℝ)) :=
      div_le_div₀ (Real.exp_pos _).le hD (Real.exp_pos _) hY
    _ = Real.exp (2 * L - (1 / 2 : ℝ) * L ^ (1000 : ℝ)) := (Real.exp_sub _ _).symm
    _ ≤ _ := by
      rw [Real.rpow_def_of_pos hLp (-21 / 20 : ℝ)]
      exact Real.exp_le_exp.mpr hgap

theorem eventually_rough_interval_lower :
    ∀ᶠ L : ℝ in atTop, ∀ D : ℕ,
      (1 / 2 : ℝ) * Real.exp (L ^ (199 / 200 : ℝ)) ≤ D → 10 ≤ D := by
  have hg := ((Real.tendsto_exp_atTop.comp
    (tendsto_rpow_atTop (show 0 < (199 / 200 : ℝ) by norm_num))).const_mul_atTop
      (show (0 : ℝ) < 1 / 2 by norm_num)).eventually (eventually_ge_atTop 10)
  filter_upwards [hg] with L hL
  intro D hD
  exact_mod_cast hL.trans hD

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.RoughLiouvilleShifts
namespace OAI

/-! The complete quantitative rough-shift analytic estimate, conditional
only on the stated published Mertens and MRT inputs. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical

/-- Manuscript `(q:rough-shifts)`, including arbitrary (possibly nonunit)
progression classes. The finite rough set is unrestricted within its interval. -/
theorem rough_liouville_shifts (hM : PrimeReciprocalInput)
    (hMRT : MRTLiouvilleShortInput) (h : ℕ) (hh : 0 < h) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ L : ℝ in atTop, ∀ Y D l : ℕ,
      (1 / 2 : ℝ) * Real.exp (L ^ (199 / 200 : ℝ)) ≤ D →
      (D : ℝ) ≤ Real.exp (2 * L) →
      Real.exp ((1 / 2 : ℝ) * L ^ (1000 : ℝ)) ≤ Y →
      ∀ [NeZero l] (a : ZMod l) (Z : Finset ℕ),
      (∀ z ∈ Z, D ≤ z ∧ z < D + D ∧
        avoidsPrimeSet (sievePrimesUpTo (Real.exp (L ^ (99 / 100 : ℝ)))) z) →
      ‖roughShiftAverage (progressionSequence liouville l a) liouville Z h Y‖ ≤
        C * L ^ (-21 / 20 : ℝ) := by
  obtain ⟨U, V, hU, hV, hFourier⟩ := hM.rough_fourier
  obtain ⟨K, hK, hWindow⟩ := hMRT.progression_window_scale
  let C := 2 * U + (2 * (h : ℝ) + 1) + (2 * (h : ℝ) + 1) * U * V * K
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  filter_upwards [hFourier, hWindow, eventually_rough_interval_lower,
    eventually_ge_atTop 10] with L hFourierL hWindowL hLowerL hL
  intro Y D l hDlower hDupper hYlower _ a Z hZ
  have hL₁ : 1 ≤ L := by linarith
  have hD₁₀ : 10 ≤ D := hLowerL D hDlower
  have hYp : (0 : ℝ) < Y := (Real.exp_pos _).trans_le hYlower
  have hYN : 0 < Y := by exact_mod_cast hYp
  have hratio := rough_shift_ratio L hL D Y hDupper hYlower
  have hrat₁ : (D : ℝ) / Y ≤ 1 := hratio.trans (by
    simpa only [Real.rpow_zero] using
      Real.rpow_le_rpow_of_exponent_le hL₁ (show (-21 / 20 : ℝ) ≤ 0 by norm_num))
  have hDY : D ≤ Y := by exact_mod_cast (div_le_one hYp).mp hrat₁
  have hYplus : Real.exp ((1 / 2 : ℝ) * L ^ (1000 : ℝ)) ≤ (Y + 1 : ℕ) :=
    hYlower.trans (by exact_mod_cast Nat.le_succ Y)
  obtain ⟨hB, hFourth⟩ := hFourierL D h hDlower hh Z hZ
  exact rough_shift_power_bound (progressionSequence liouville l a) liouville
    (liouville_oneBounded.progressionSequence l a) liouville_oneBounded Z D h Y
    (by omega) hYN (fun z hz => by have := (hZ z hz).2.1; omega)
    L U V K hL₁ hU.le hV.le hK.le hratio hB hFourth
    (fun θ => hWindowL Y D l (by omega) hD₁₀ (by omega)
      hDlower hDupper hYplus a θ)

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.QuantitativeRoughBins
namespace OAI

/-! The quantitative rough-shift estimate on the actual logarithmic
bins, retaining the absolute long-interval exponent 1000. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical

theorem quantitative_rough_real_bin (hM : PrimeReciprocalInput)
    (hMRT : MRTLiouvilleShortInput) (h : ℕ) (hh : 0 < h) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ L : ℝ in atTop,
      ∀ (Y l : ℕ), Real.exp ((1 / 2 : ℝ) * L ^ (1000 : ℝ)) ≤ (Y : ℝ) →
      ∀ [NeZero l] (a : ZMod l) (M τ : ℝ), 0 < τ → τ < 2 →
      ∀ Z : Finset ℕ,
      (∀ z ∈ Z, M ≤ (z : ℝ) ∧ (z : ℝ) ≤ τ * M ∧
        Real.exp (L ^ (199 / 200 : ℝ)) ≤ (z : ℝ) ∧ (z : ℝ) ≤ Real.exp (2 * L) ∧
        avoidsPrimeSet (sievePrimesUpTo (Real.exp (L ^ (99 / 100 : ℝ)))) z) →
      ‖roughShiftAverage (progressionSequence liouville l a) liouville Z h Y‖ ≤
        C * L ^ (-21 / 20 : ℝ) := by
  obtain ⟨C, hC, hb⟩ := rough_liouville_shifts hM hMRT h hh
  refine ⟨C, hC, ?_⟩
  filter_upwards [hb, eventually_ge_atTop (1 : ℝ)] with L hb hL
  intro Y l hY _ a M τ hτ hτtwo Z hZ
  by_cases hz : Z.Nonempty
  · obtain ⟨z, hz⟩ := hz
    have hzdata := hZ z hz
    have hzm : 0 < τ * M := (Real.exp_pos _).trans_le (hzdata.2.2.1.trans hzdata.2.1)
    have hMpos : 0 < M := by
      rcases mul_pos_iff.mp hzm with hpos | hneg
      · exact hpos.2
      · linarith [hneg.1]
    have hceil : (Nat.ceil M : ℝ) ≤ z := by exact_mod_cast Nat.ceil_le.mpr hzdata.1
    have hlow : (1 / 2 : ℝ) * Real.exp (L ^ (199 / 200 : ℝ)) ≤ Nat.ceil M := by
      have hMc : M ≤ (Nat.ceil M : ℝ) := Nat.le_ceil M
      nlinarith [hzdata.2.1, hzdata.2.2.1]
    have hupp : (Nat.ceil M : ℝ) ≤ Real.exp (2 * L) := hceil.trans hzdata.2.2.2.1
    apply hb Y (Nat.ceil M) l hlow hupp hY a Z
    intro z hz
    have hzD : Nat.ceil M ≤ z := Nat.ceil_le.mpr (hZ z hz).1
    have hMceil : M ≤ (Nat.ceil M : ℝ) := Nat.le_ceil M
    have hzupper : (z : ℝ) < 2 * (Nat.ceil M : ℝ) := by
      nlinarith [(hZ z hz).2.1]
    have hzupperNat : z < Nat.ceil M + Nat.ceil M := by
      have ht : z < 2 * Nat.ceil M := by exact_mod_cast hzupper
      omega
    exact ⟨hzD, hzupperNat, (hZ z hz).2.2.2.2⟩
  · have he : Z = ∅ := not_nonempty_iff_eq_empty.mp hz
    subst Z
    simp only [roughShiftAverage, roughShiftProfile, sum_empty, positivePrefix, sum_const_zero,
      zero_div, norm_zero]
    exact mul_nonneg hC.le (Real.rpow_nonneg (zero_le_one.trans hL) _)

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.QuantitativeResidueBins
namespace OAI

/-! The progression class in a partial centering term depends on the
rough shift. Splitting by its residue costs exactly the fixed modulus. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical

lemma sum_modulus_fibres (l : ℕ) [NeZero l] (Z : Finset ℕ)
    (F : ZMod l → ℕ → ℂ) :
    (∑ r : ZMod l, ∑ z ∈ Z.filter (fun z : ℕ => (z : ZMod l) = r), F r z) =
      ∑ z ∈ Z, F (z : ZMod l) z := by
  simp only [sum_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro z _
  simp



lemma residueScaledRoughProfile_partition (l : ℕ) [NeZero l] (b : ZMod l)
    (Z : Finset ℕ) (h n : ℕ) :
    residueScaledRoughProfile l b Z h n =
      ∑ r : ZMod l, roughShiftProfile (progressionSequence liouville l (b * r))
        liouville (Z.filter (fun z : ℕ => (z : ZMod l) = r)) h n := by
  exact (sum_modulus_fibres l Z (fun r z => (z : ℂ)⁻¹ *
    (progressionSequence liouville l (b * r) n * liouville (n + h * z)))).symm

lemma residueScaledRoughAverage_partition (l : ℕ) [NeZero l] (b : ZMod l)
    (Z : Finset ℕ) (h Y : ℕ) :
    residueScaledRoughAverage l b Z h Y =
      ∑ r : ZMod l, roughShiftAverage (progressionSequence liouville l (b * r))
        liouville (Z.filter (fun z : ℕ => (z : ZMod l) = r)) h Y := by
  simp only [residueScaledRoughAverage, positivePrefix, residueScaledRoughProfile_partition,
    roughShiftAverage]
  rw [sum_comm, sum_div]

theorem quantitative_residue_bin (hM : PrimeReciprocalInput)
    (hMRT : MRTLiouvilleShortInput) (h : ℕ) (hh : 0 < h) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ L : ℝ in atTop,
      ∀ (Y l : ℕ), Real.exp ((1 / 2 : ℝ) * L ^ (1000 : ℝ)) ≤ (Y : ℝ) →
      ∀ [NeZero l] (b : ZMod l) (M τ : ℝ), 0 < τ → τ < 2 →
      ∀ Z : Finset ℕ,
      (∀ z ∈ Z, M ≤ (z : ℝ) ∧ (z : ℝ) ≤ τ * M ∧
        Real.exp (L ^ (199 / 200 : ℝ)) ≤ (z : ℝ) ∧ (z : ℝ) ≤ Real.exp (2 * L) ∧
        avoidsPrimeSet (sievePrimesUpTo (Real.exp (L ^ (99 / 100 : ℝ)))) z) →
      ‖residueScaledRoughAverage l b Z h Y‖ ≤ (l : ℝ) * C * L ^ (-21 / 20 : ℝ) := by
  obtain ⟨C, hC, hb⟩ := quantitative_rough_real_bin hM hMRT h hh
  refine ⟨C, hC, ?_⟩
  filter_upwards [hb] with L hb
  intro Y l hY _ b M τ hτ hτtwo Z hZ
  rw [residueScaledRoughAverage_partition]
  calc
    _ ≤ ∑ r : ZMod l, ‖roughShiftAverage (progressionSequence liouville l (b * r))
        liouville (Z.filter (fun z : ℕ => (z : ZMod l) = r)) h Y‖ := norm_sum_le _ _
    _ ≤ ∑ _r : ZMod l, C * L ^ (-21 / 20 : ℝ) := by
      apply sum_le_sum
      intro r _
      exact hb Y l hY (b * r) M τ hτ hτtwo _ (fun z hz => hZ z (mem_filter.mp hz).1)
    _ = _ := by simp only [sum_const, card_univ, ZMod.card, nsmul_eq_mul]; ring

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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.DivisibilityPrefix
namespace OAI

/-! Exact change of variables `x=u*z` for a divisibility indicator,
including the floor endpoint `floor(X/u)`. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma positivePrefix_eq_Icc (F : ℕ → ℂ) (X : ℕ) :
    positivePrefix F X = ∑ n ∈ Icc 1 X, F n := by
  simpa only [Nat.zero_add, positivePrefix] using (sum_Icc_shift F 0 X).symm

theorem divisibility_positivePrefix (F : ℕ → ℂ) (u X : ℕ) (hu : 0 < u) :
    positivePrefix (fun n => natDivisibilityIndicator u n * F n) X =
      positivePrefix (fun z => F (u * z)) (X / u) := by
  calc
    _ = ∑ n ∈ (Icc 1 X).filter (fun n => u ∣ n), F n := by
      rw [positivePrefix_eq_Icc, sum_filter]
      apply sum_congr rfl
      intro n _
      by_cases hn : u ∣ n <;> simp only [natDivisibilityIndicator, hn, ite_true, ite_false,
        one_mul, zero_mul]
    _ = ∑ z ∈ Icc 1 (X / u), F (u * z) := by
      symm
      apply sum_bij (fun z _ => u * z)
      · intro z hz
        obtain ⟨hz₁, hzX⟩ := mem_Icc.mp hz
        apply mem_filter.mpr
        refine ⟨mem_Icc.mpr ⟨Nat.mul_pos hu hz₁, ?_⟩, dvd_mul_right u z⟩
        simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le hu).mp hzX
      · intro z _ w _ heq
        exact Nat.eq_of_mul_eq_mul_left hu heq
      · intro n hn
        obtain ⟨hnI, hdiv⟩ := mem_filter.mp hn
        obtain ⟨hn₁, hnX⟩ := mem_Icc.mp hnI
        refine ⟨n / u, mem_Icc.mpr ⟨?_, Nat.div_le_div_right hnX⟩, Nat.mul_div_cancel' hdiv⟩
        exact Nat.div_pos (Nat.le_of_dvd hn₁ hdiv) hu
      · intro z _
        rfl
    _ = _ := (positivePrefix_eq_Icc (fun z => F (u * z)) (X / u)).symm

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.LiouvilleDivisorExtraction
namespace OAI

/-! The exact partial-centering substitution n=u*v. Only u must be a
unit modulo l; the progression class and the removed product may be nonunits. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma unit_progression_cancel (l : ℕ) (b : ZMod l) (u z v : ℕ)
    (hu : IsUnit (u : ZMod l)) :
    ((u * v : ℕ) : ZMod l) = b * ((u * z : ℕ) : ZMod l) ↔
      (v : ZMod l) = b * (z : ZMod l) := by
  simp only [Nat.cast_mul]
  rw [show b * ((u : ZMod l) * z) = (u : ZMod l) * (b * z) by ring,
    hu.mul_right_inj]

lemma liouville_pair_dilate (u v z h : ℕ) (hu : 0 < u) :
    liouville (u * v) * liouville (u * v + h * (u * z)) =
      liouville v * liouville (v + h * z) := by
  rw [show u * v + h * (u * z) = u * (v + h * z) by ring]
  simp only [liouville_mul]
  calc
    _ = liouville u ^ 2 * (liouville v * liouville (v + h * z)) := by ring
    _ = _ := by rw [liouville_sq hu.ne', one_mul]

lemma liouville_progression_dilate (l : ℕ) [NeZero l] (b : ZMod l)
    (u v z h : ℕ) (hu : 0 < u) (hunit : IsUnit (u : ZMod l)) :
    progressionSequence liouville l (b * ((u * z : ℕ) : ZMod l)) (u * v) *
        liouville (u * v + h * (u * z)) =
      progressionSequence liouville l (b * (z : ZMod l)) v * liouville (v + h * z) := by
  simp only [progressionSequence, unit_progression_cancel l b u z v hunit]
  split_ifs
  · exact liouville_pair_dilate u v z h hu
  · simp only [zero_mul]


lemma partialLiouvilleProfile_prefix (l : ℕ) [NeZero l] (b : ZMod l)
    (u : ℕ) (Z : Finset ℕ) (h X : ℕ) (hu : 0 < u)
    (hunit : IsUnit (u : ZMod l)) :
    positivePrefix (partialLiouvilleProfile l b u Z h) X =
      positivePrefix (residueScaledRoughProfile l b Z h) (X / u) := by
  unfold partialLiouvilleProfile
  rw [divisibility_positivePrefix _ u X hu]
  congr 1
  funext v
  apply sum_congr rfl
  intro z _
  rw [liouville_progression_dilate l b u v z h hu hunit]


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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.TupleSlice
namespace OAI

/-! Exact splitting of a prime tuple into the removed and retained
supplies in the quantitative centering expansion. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma indexed_prime_product_injective {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : ι → Finset ℕ) (hprime : ∀ i, ∀ p ∈ P i, p.Prime)
    (hdisjoint : ∀ i j, j ≠ i → Disjoint (P i) (P j)) :
    Function.Injective (fun x : (i : ι) → P i => ∏ i, (x i).val) := by
  intro x y he
  change (∏ i, (x i).val) = ∏ i, (y i).val at he
  funext i
  apply Subtype.ext
  have hp := hprime i _ (x i).property
  have hd : (x i).val ∣ ∏ j, (y j).val := by
    rw [← he]
    exact dvd_prod_of_mem (fun j => (x j).val) (mem_univ i)
  obtain ⟨j, _, hdiv⟩ := (hp.prime.dvd_finsetProd_iff (fun j => (y j).val)).mp hd
  have hv : (x i).val = (y j).val :=
    (Nat.prime_dvd_prime_iff_eq hp (hprime j _ (y j).property)).mp hdiv
  have hij : i = j := by
    by_contra hne
    exact disjoint_left.mp (hdisjoint i j (Ne.symm hne)) (x i).property
      (hv.symm ▸ (y j).property)
  subst j
  exact hv


lemma primeTupleSlice_injective {J : ℕ} (P : Fin J → Finset ℕ) (I : Finset (Fin J))
    (hprime : ∀ i, ∀ p ∈ P i, p.Prime)
    (hdisjoint : ∀ i j, j ≠ i → Disjoint (P i) (P j)) :
    Function.Injective (fun x : (i : I) → P i => ∏ i, (x i).val) :=
  indexed_prime_product_injective _ (fun i => hprime i)
    (fun i j hne => hdisjoint i j (fun he => hne (Subtype.ext he)))




lemma primeTupleSlice_split_sum {J : ℕ} (P : Fin J → Finset ℕ) (I : Finset (Fin J))
    (hprime : ∀ i, ∀ p ∈ P i, p.Prime)
    (hdisjoint : ∀ i j, j ≠ i → Disjoint (P i) (P j)) (F : ℕ → ℕ → ℂ) :
    (∑ x : (j : Fin J) → P j,
      F (∏ j : {j // j ∉ I}, (x j).val) (∏ i : I, (x i).val)) =
      ∑ y : (j : {j // j ∉ I}) → P j, ∑ z ∈ primeTupleSlice P I,
        F (∏ j, (y j).val) z := by
  let e := Equiv.piEquivPiSubtypeProd (fun j : Fin J => j ∈ I) (fun j => P j)
  calc
    _ = ∑ xy : ((i : I) → P i) × ((j : {j // j ∉ I}) → P j),
        F (∏ j, (xy.2 j).val) (∏ i, (xy.1 i).val) := by
      simpa only [e, Equiv.piEquivPiSubtypeProd, Equiv.coe_fn_mk] using
        (e.sum_comp (fun xy => F (∏ j, (xy.2 j).val) (∏ i, (xy.1 i).val)))
    _ = ∑ y : (j : {j // j ∉ I}) → P j, ∑ x : (i : I) → P i,
        F (∏ j, (y j).val) (∏ i, (x i).val) := by
      rw [Fintype.sum_prod_type, sum_comm]
    _ = _ := by
      apply sum_congr rfl
      intro y _
      rw [primeTupleSlice, sum_image]
      exact fun x _ y _ he => primeTupleSlice_injective P I hprime hdisjoint he

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.PartialTupleProfiles
namespace OAI

/-! Reindex the actual partial-centering tuple sum by its retained and
removed supply products. Each removed numerical product occurs once. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical


lemma tuplePartialProfile_reindex {J : ℕ} (P : Fin J → Finset ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j k, k ≠ j → Disjoint (P j) (P k))
    (I : Finset (Fin J)) (q : ℕ) (eligible : ℕ → ℕ → Prop)
    (l : ℕ) [NeZero l] (b : ZMod l) (h n : ℕ) :
    tuplePartialProfile P I q eligible l b h n =
      ∑ y : (j : {j // j ∉ I}) → P j,
        partialLiouvilleProfile l b (q * ∏ j, (y j).val)
          ((primeTupleSlice P I).filter (fun z => eligible ((∏ j, (y j).val) * z) q)) h n := by
  let F : ℕ → ℕ → ℂ := fun t z =>
    if eligible (t * z) q then (z : ℂ)⁻¹ *
      (natDivisibilityIndicator (q * t) n *
        (progressionSequence liouville l (b * ((q * t * z : ℕ) : ZMod l)) n *
          liouville (n + h * (q * t * z)))) else 0
  have hs := primeTupleSlice_split_sum P I hprime hdisjoint F
  have hleft : tuplePartialProfile P I q eligible l b h n =
      ∑ x : (j : Fin J) → P j,
        F (∏ j : {j // j ∉ I}, (x j).val) (∏ i : I, (x i).val) := by
    apply sum_congr rfl
    intro x _
    have he : (∏ j : {j // j ∉ I}, (x j).val) * (∏ i : I, (x i).val) =
        ∏ j, (x j).val := by
      have hI := prod_coe_sort I (fun j : Fin J => (x j).val)
      have hIc := (prod_subtype (p := fun j : Fin J => j ∉ I) (F := inferInstance) (univ \ I) (by simp) (fun j : Fin J => (x j).val)).symm
      rw [hI, hIc, ← prod_union sdiff_disjoint, sdiff_union_of_subset (subset_univ I)]
    dsimp only [F]
    simp only [mul_assoc, he]
  rw [hleft, hs]
  apply sum_congr rfl
  intro y _
  rw [partialLiouvilleProfile, mul_sum, sum_filter]
  apply sum_congr rfl
  intro z _
  dsimp only [F]
  split_ifs
  · simp only [mul_assoc]
    ring
  · simp

lemma tuplePartialProfile_prefix {J : ℕ} (P : Fin J → Finset ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j k, k ≠ j → Disjoint (P j) (P k))
    (I : Finset (Fin J)) (q : ℕ) (hq : 0 < q) (eligible : ℕ → ℕ → Prop)
    (l : ℕ) [NeZero l] (b : ZMod l) (h X : ℕ)
    (hunit : ∀ y : (j : {j // j ∉ I}) → P j,
      IsUnit ((q * ∏ j, (y j).val : ℕ) : ZMod l)) :
    positivePrefix (tuplePartialProfile P I q eligible l b h) X =
      ∑ y : (j : {j // j ∉ I}) → P j,
        positivePrefix (residueScaledRoughProfile l b
          ((primeTupleSlice P I).filter (fun z => eligible ((∏ j, (y j).val) * z) q)) h)
          (X / (q * ∏ j, (y j).val)) := by
  simp only [positivePrefix, tuplePartialProfile_reindex P hprime hdisjoint]
  rw [sum_comm]
  apply sum_congr rfl
  intro y _
  exact partialLiouvilleProfile_prefix l b _ _ h X
    (Nat.mul_pos hq (prod_pos fun j _ => (hprime j _ (y j).property).pos)) (hunit y)


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.QuantitativeTupleBins
namespace OAI

/-! A partial-centering bin saves L^(-21/20) with exactly the reciprocal
mass of the retained supply products. The scale exponent is absolute. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical

lemma indexed_rescaled_prefix_bound {α : Type*} [Fintype α]
    (u : α → ℕ) (F : α → ℕ → ℂ) (X : ℕ) (E : ℝ)
    (hX : 0 < X) (hE : 0 ≤ E) (hu : ∀ a, 0 < u a)
    (hF : ∀ a, ‖positivePrefix (F a) (X / u a) / ((X / u a : ℕ) : ℂ)‖ ≤ E) :
    ‖(∑ a, positivePrefix (F a) (X / u a)) / (X : ℂ)‖ ≤
      E * ∑ a, 1 / (u a : ℝ) := by
  have hXp : (0 : ℝ) < X := by exact_mod_cast hX
  rw [sum_div]
  calc
    _ ≤ ∑ a, ‖positivePrefix (F a) (X / u a) / (X : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ a, E * (1 / (u a : ℝ)) := by
      apply sum_le_sum
      intro a _
      have hup : (0 : ℝ) < u a := by exact_mod_cast hu a
      have hb := prefix_norm_of_average_bound (F a) (X / u a) E (hF a)
      have hratio : ((X / u a : ℕ) : ℝ) ≤ (X : ℝ) / u a := Nat.cast_div_le
      have hp := hb.trans (mul_le_mul_of_nonneg_right hratio hE)
      rw [norm_div, Complex.norm_natCast]
      calc
        _ ≤ (((X : ℝ) / u a) * E) / X := div_le_div_of_nonneg_right hp hXp.le
        _ = _ := by field_simp
    _ = _ := by rw [mul_sum]

lemma retained_tuple_reciprocal_sum {J : ℕ} (P : Fin J → Finset ℕ)
    (I : Finset (Fin J)) (q : ℕ) :
    (∑ y : (j : {j // j ∉ I}) → P j,
      1 / ((q : ℝ) * ∏ j, ((y j).val : ℝ))) =
      (1 / (q : ℝ)) * ∏ j : {j // j ∉ I}, primeHarmonicMass (P j) := by
  calc
    _ = (1 / (q : ℝ)) *
        ∑ y : (j : {j // j ∉ I}) → P j, ∏ j, ((y j).val : ℝ)⁻¹ := by
      rw [mul_sum]
      apply sum_congr rfl
      intro y _
      simp only [one_div, mul_inv_rev, prod_inv_distrib]
      ring
    _ = _ := by
      congr 1
      exact (Fintype.prod_sum (fun j : {j // j ∉ I} =>
        fun p : P j => (p.val : ℝ)⁻¹)).symm

theorem quantitative_partial_tuple_bin_oai (hM : PrimeReciprocalInput)
    (hMRT : MRTLiouvilleShortInput) (h : ℕ) (hh : 0 < h) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ L : ℝ in atTop,
      ∀ (J : ℕ) (P : Fin J → Finset ℕ),
      (∀ j, ∀ p ∈ P j, p.Prime) →
      (∀ j k, k ≠ j → Disjoint (P j) (P k)) →
      ∀ (I : Finset (Fin J)) (q X l : ℕ) [NeZero l],
      0 < q → 0 < X →
      ∀ (eligible : ℕ → ℕ → Prop) (b : ZMod l) (M : ℝ) (τ : ℝ),
      0 < τ → τ < 2 →
      (∀ y : (j : {j // j ∉ I}) → P j,
        IsUnit ((q * ∏ j, (y j).val : ℕ) : ZMod l)) →
      (∀ y : (j : {j // j ∉ I}) → P j,
        Real.exp ((1 / 2 : ℝ) * L ^ (1000 : ℝ)) ≤
          ((X / (q * ∏ j, (y j).val) : ℕ) : ℝ)) →
      (∀ y : (j : {j // j ∉ I}) → P j, ∀ z ∈ primeTupleSlice P I,
        eligible ((∏ j, (y j).val) * z) q →
          M / (q * ∏ j, ((y j).val : ℝ)) ≤ (z : ℝ) ∧
          (z : ℝ) ≤ τ * (M / (q * ∏ j, ((y j).val : ℝ))) ∧
          Real.exp (L ^ (199 / 200 : ℝ)) ≤ (z : ℝ) ∧
          (z : ℝ) ≤ Real.exp (2 * L) ∧
          avoidsPrimeSet (sievePrimesUpTo (Real.exp (L ^ (99 / 100 : ℝ)))) z) →
      ‖positivePrefix (tuplePartialProfile P I q eligible l b h) X / (X : ℂ)‖ ≤
        ((l : ℝ) * C * L ^ (-21 / 20 : ℝ)) *
          ((1 / (q : ℝ)) * ∏ j : {j // j ∉ I}, primeHarmonicMass (P j)) := by
  obtain ⟨C, hC, hb⟩ := quantitative_residue_bin hM hMRT h hh
  refine ⟨C, hC, ?_⟩
  filter_upwards [hb, eventually_ge_atTop (1 : ℝ)] with L hb hL
  intro J P hp hd I q X l _ hq hX eligible b M τ hτ hτtwo hunit hY hZ
  rw [tuplePartialProfile_prefix P hp hd I q hq eligible l b h X hunit]
  have hu (y : (j : {j // j ∉ I}) → P j) : 0 < q * ∏ j, (y j).val :=
    Nat.mul_pos hq (prod_pos fun j _ => (hp j _ (y j).property).pos)
  have he := indexed_rescaled_prefix_bound
    (fun y : (j : {j // j ∉ I}) → P j => q * ∏ j, (y j).val)
    (fun y => residueScaledRoughProfile l b
      ((primeTupleSlice P I).filter (fun z => eligible ((∏ j, (y j).val) * z) q)) h)
    X ((l : ℝ) * C * L ^ (-21 / 20 : ℝ)) hX (by positivity) hu
    (fun y => hb _ l (hY y) b (M / (q * ∏ j, ((y j).val : ℝ))) τ hτ hτtwo _
      (fun z hz => hZ y z (mem_filter.mp hz).1 (mem_filter.mp hz).2))
  simpa only [Nat.cast_mul, Nat.cast_prod, retained_tuple_reciprocal_sum] using he

end TwoPointCorrelations

end OAI

end

theorem solution : type_of% @OAI.TwoPointCorrelations.quantitative_partial_tuple_bin_oai := @OAI.TwoPointCorrelations.quantitative_partial_tuple_bin_oai
