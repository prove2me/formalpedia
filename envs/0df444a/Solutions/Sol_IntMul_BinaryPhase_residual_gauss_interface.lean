-- Prove2me | solution 1 for IntMul.BinaryPhase.residual_gauss_interface
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T17:30:39.520182+00:00
-- url     : https://prove2.me/submissions/986f71cf-d112-4cee-a95f-9aa601b14238

import Definitions.Def_IntMul_BinaryQuadraticPhase
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Star.BigOperators
import Mathlib.Algebra.Group.Int.Even
import Mathlib.Algebra.Group.AddChar
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.FieldTheory.Finiteness
import Mathlib.Tactic
open scoped BigOperators

/-!
Completing the square for finite quadratic phase functions.

This is the algebraic kernel identity in the general binary residual normal form
of `notes/endpoint-gauge-complex.tex`.  The phase law is explicit; neither an
orthonormal basis nor a classification of alternating forms is assumed.
-/

namespace IntMul.QuadraticGauss

open scoped BigOperators

variable {V : Type*} [AddCommGroup V] [Fintype V]

/-- Translating the summation variable gives the Fourier value at a polar character.
The phase law makes sense for any finite additive group and complex quadratic phase. -/
theorem completing_square
    (q : V → ℂ) (χ : V → V → ℂ)
    (hphase : ∀ z w, q (z + w) = q z * q w * χ z w)
    (w : V) (hw : q w ≠ 0) :
    (∑ z : V, q z * χ z w) = (∑ z : V, q z) / q w := by
  apply (eq_div_iff hw).2
  calc
    (∑ z : V, q z * χ z w) * q w = ∑ z : V, q (z + w) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro z _
      rw [hphase]
      ring
    _ = ∑ z : V, q z := by
      exact Equiv.sum_comp (Equiv.addRight w) q

/-- The two-argument kernel separates into two diagonal phase corrections and
the bilinear character kernel.  Character values are assumed involutive, as for
binary dot-product characters. -/
theorem kernel_factorization
    (q : V → ℂ) (χ : V → V → ℂ)
    (hphase : ∀ z w, q (z + w) = q z * q w * χ z w)
    (hnonzero : ∀ z, q z ≠ 0)
    (hcharacter : ∀ x y, χ x y * χ x y = 1)
    (x y : V) :
    (∑ z : V, q z * χ z (x + y)) =
      (∑ z : V, q z) * (q x)⁻¹ * χ x y * (q y)⁻¹ := by
  rw [completing_square q χ hphase (x + y) (hnonzero (x + y)), hphase]
  have hc : χ x y ≠ 0 := by
    intro h
    simpa [h] using hcharacter x y
  have hi : (χ x y)⁻¹ = χ x y := by
    exact inv_eq_of_mul_eq_one_right (hcharacter x y)
  simp only [div_eq_mul_inv, mul_inv_rev, hi]
  ring

/-- Orthogonality of the polar characters determines the squared Gauss magnitude.
This supplies a nonvanishing guarantee without a choice of residual basis. -/
theorem gauss_norm_square
    [DecidableEq V]
    (q : V → ℂ) (χ : V → V → ℂ)
    (hphase : ∀ z w, q (z + w) = q z * q w * χ z w)
    (hunit : ∀ w, q w * star (q w) = 1)
    (hzero : q 0 = 1)
    (horthogonal : ∀ z, (∑ w : V, χ z w) = if z = 0 then (Fintype.card V : ℂ) else 0) :
    (∑ z : V, q z) * star (∑ z : V, q z) = (Fintype.card V : ℂ) := by
  classical
  calc
    (∑ z : V, q z) * star (∑ z : V, q z) =
        ∑ w : V, ∑ z : V, q z * star (q w) := by
      rw [star_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro w _
      rw [Finset.sum_mul]
    _ = ∑ w : V, ∑ z : V, q (z + w) * star (q w) := by
      apply Finset.sum_congr rfl
      intro w _
      exact (Equiv.sum_comp (Equiv.addRight w) (fun z => q z * star (q w))).symm
    _ = ∑ w : V, ∑ z : V, q z * χ z w := by
      apply Finset.sum_congr rfl
      intro w _
      apply Finset.sum_congr rfl
      intro z _
      rw [hphase]
      calc
        q z * q w * χ z w * star (q w) = q z * χ z w * (q w * star (q w)) := by ring
        _ = q z * χ z w := by rw [hunit, mul_one]
    _ = ∑ z : V, q z * (∑ w : V, χ z w) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro z _
      rw [Finset.mul_sum]
    _ = (Fintype.card V : ℂ) := by
      simp [horthogonal, hzero]

/-- A nonsingular finite quadratic phase has a nonzero Gauss sum. -/
theorem gauss_sum_ne_zero
    [DecidableEq V]
    (q : V → ℂ) (χ : V → V → ℂ)
    (hphase : ∀ z w, q (z + w) = q z * q w * χ z w)
    (hunit : ∀ w, q w * star (q w) = 1)
    (hzero : q 0 = 1)
    (horthogonal : ∀ z, (∑ w : V, χ z w) = if z = 0 then (Fintype.card V : ℂ) else 0) :
    (∑ z : V, q z) ≠ 0 := by
  have h := gauss_norm_square q χ hphase hunit hzero horthogonal
  intro hz
  rw [hz, zero_mul] at h
  have hc : (Fintype.card V : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  exact hc h.symm

end IntMul.QuadraticGauss



/-!
An arithmetic proof of the fourth-root scalar in the binary residual normal form.
The argument uses the Gaussian-integer norm, avoiding any orthonormal-basis
assumption on an alternating residual.
-/

namespace IntMul.GaussianNormalization

local notation "ℤ[i]" => GaussianInt

/-- A Gaussian integer of even norm is divisible by `1+i`. -/
theorem factor_one_add_i_of_even_norm (z : ℤ[i]) (hn : Even z.norm) :
    ∃ w : ℤ[i], z = (⟨1, 1⟩ : ℤ[i]) * w := by
  have he : Even (z.re ^ 2 + z.im ^ 2) := by
    simpa [Zsqrtd.norm, pow_two] using hn
  have hp : Even z.re ↔ Even z.im := by
    simpa [Int.even_pow] using Int.even_add.mp he
  obtain ⟨a, ha⟩ := Int.even_add.mpr hp
  obtain ⟨b, hb⟩ := Int.even_sub.mpr hp.symm
  refine ⟨⟨a, b⟩, ?_⟩
  apply Zsqrtd.ext
  · change z.re = 1 * a + (-1) * 1 * b
    omega
  · change z.im = 1 * b + 1 * a
    omega

/-- If a Gaussian integer has norm `2^r`, all of its ramified-prime factors
can be removed, leaving an element of norm one. -/
theorem norm_two_pow_factorization (r : ℕ) (z : ℤ[i]) (hz : z.norm = (2 : ℤ) ^ r) :
    ∃ u : ℤ[i], u.norm = 1 ∧ z = (⟨1, 1⟩ : ℤ[i]) ^ r * u := by
  induction r generalizing z with
  | zero =>
      exact ⟨z, by simpa using hz, by simp⟩
  | succ r ih =>
      have he : Even z.norm := by
        rw [hz, pow_succ]
        exact Even.mul_left (by decide : Even (2 : ℤ)) _
      obtain ⟨w, hw⟩ := factor_one_add_i_of_even_norm z he
      have hπ : Zsqrtd.norm (⟨1, 1⟩ : ℤ[i]) = 2 := by norm_num [Zsqrtd.norm]
      have hwn : w.norm = (2 : ℤ) ^ r := by
        rw [hw, Zsqrtd.norm_mul, hπ, pow_succ] at hz
        nlinarith
      obtain ⟨u, hu, hwu⟩ := ih w hwn
      refine ⟨u, hu, ?_⟩
      rw [hw, hwu, pow_succ]
      ring

/-- The only Gaussian integers of norm one are the four roots of unity. -/
theorem norm_one_fourth_root (z : ℤ[i]) (hz : z.norm = 1) :
    (z : ℂ) ^ 4 = 1 := by
  have hn : z.re ^ 2 + z.im ^ 2 = 1 := by simpa [Zsqrtd.norm, pow_two] using hz
  have hr : -1 ≤ z.re ∧ z.re ≤ 1 := by
    constructor <;> nlinarith [sq_nonneg z.im]
  have hi : -1 ≤ z.im ∧ z.im ≤ 1 := by
    constructor <;> nlinarith [sq_nonneg z.re]
  rcases z with ⟨a, b⟩
  dsimp at hn hr hi
  rcases hr with ⟨ha₁, ha₂⟩
  rcases hi with ⟨hb₁, hb₂⟩
  interval_cases a <;> interval_cases b <;>
    norm_num [GaussianInt.toComplex_def', Complex.I_sq, pow_succ] at *

/-- Normalizing a norm-`2^r` Gaussian integer by `((1-i)/2)^r` gives a fourth root
of unity.  Applied to the quadratic Gauss sum, this proves the scalar assertion
for both alternating and nonalternating residuals. -/
theorem normalized_fourth_root (r : ℕ) (z : ℤ[i]) (hz : z.norm = (2 : ℤ) ^ r) :
    ((z : ℂ) * ((1 - Complex.I) / 2) ^ r) ^ 4 = 1 := by
  obtain ⟨u, hu, hzu⟩ := norm_two_pow_factorization r z hz
  have hπ : ((⟨1, 1⟩ : ℤ[i]) : ℂ) * ((1 - Complex.I) / 2) = 1 := by
    rw [GaussianInt.toComplex_def']
    norm_num
    ring_nf
    simp [Complex.I_sq]
    norm_num
  have hnorm : (z : ℂ) * ((1 - Complex.I) / 2) ^ r = (u : ℂ) := by
    rw [hzu]
    simp only [GaussianInt.toComplex_mul, map_pow]
    calc
      _ = (((⟨1, 1⟩ : ℤ[i]) : ℂ) * ((1 - Complex.I) / 2)) ^ r * (u : ℂ) := by
        rw [mul_pow]
        ring
      _ = (u : ℂ) := by rw [hπ]; simp
  rw [hnorm]
  exact norm_one_fourth_root u hu

end IntMul.GaussianNormalization



namespace IntMul.BinaryPhase

open scoped BigOperators

theorem sign_add (a b : ZMod 2) : sign (a + b) = sign a * sign b := by
  fin_cases a <;> fin_cases b
  · change (1 : ℂ) = 1 * 1
    norm_num
  · change (-1 : ℂ) = 1 * (-1)
    norm_num
  · change (-1 : ℂ) = (-1) * 1
    norm_num
  · change (1 : ℂ) = (-1) * (-1)
    norm_num

theorem sign_square (a : ZMod 2) : sign a * sign a = 1 := by
  fin_cases a <;> norm_num [sign, ZMod.val, Fin.val_add, ZMod.commRing, Fin.add_def]

theorem phase_norm (a : ZMod 4) : (phase a).norm = 1 := by
  fin_cases a <;> norm_num [phase, Zsqrtd.norm, Zsqrtd.sqrtd, pow_succ,
    Zsqrtd.re_mul, Zsqrtd.im_mul, ZMod.val, Fin.ext_iff]

theorem phase_polarization (a b : ZMod 4) (c : ZMod 2) :
    ((phase (a + b + twice c)) : ℂ) = (phase a : ℂ) * (phase b : ℂ) * sign c := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    norm_num [phase, twice, sign, Zsqrtd.sqrtd, pow_succ, GaussianInt.toComplex_def',
      Zsqrtd.re_mul, Zsqrtd.im_mul, ZMod.val, Fin.ext_iff, Complex.I_sq, GaussianInt.toComplex_mul]
  · change Complex.I ^ 0 = (1 : ℂ)
    norm_num [Complex.I_sq, pow_succ]
  · change Complex.I ^ 2 = (-1 : ℂ)
    norm_num [Complex.I_sq, pow_succ]
  · change Complex.I ^ 1 = (Complex.I : ℂ)
    norm_num [Complex.I_sq, pow_succ]
  · change Complex.I ^ 3 = (-Complex.I : ℂ)
    norm_num [Complex.I_sq, pow_succ]
  · change Complex.I ^ 2 = (-1 : ℂ)
    norm_num [Complex.I_sq, pow_succ]
  · change Complex.I ^ 0 = (1 : ℂ)
    norm_num [Complex.I_sq, pow_succ]
  · change Complex.I ^ 3 = (-Complex.I : ℂ)
    norm_num [Complex.I_sq, pow_succ]
  · change Complex.I ^ 1 = (Complex.I : ℂ)
    norm_num [Complex.I_sq, pow_succ]
  · change Complex.I ^ 1 = (Complex.I : ℂ)
    norm_num [Complex.I_sq, pow_succ]
  · change Complex.I ^ 3 = (-Complex.I : ℂ)
    norm_num [Complex.I_sq, pow_succ]
  · change Complex.I ^ 2 = (-1 : ℂ)
    norm_num [Complex.I_sq, pow_succ]
  · change Complex.I ^ 0 = (1 : ℂ)
    norm_num [Complex.I_sq, pow_succ]
  · change Complex.I ^ 3 = (-Complex.I : ℂ)
    norm_num [Complex.I_sq, pow_succ]
  · change Complex.I ^ 1 = (Complex.I : ℂ)
    norm_num [Complex.I_sq, pow_succ]
  · change Complex.I ^ 0 = (1 : ℂ)
    norm_num [Complex.I_sq, pow_succ]
  · change Complex.I ^ 2 = (-1 : ℂ)
    norm_num [Complex.I_sq, pow_succ]
  · change Complex.I ^ 2 = (-1 : ℂ)
    norm_num [Complex.I_sq, pow_succ]
  · change Complex.I ^ 0 = (1 : ℂ)
    norm_num [Complex.I_sq, pow_succ]
  · change Complex.I ^ 3 = (-Complex.I : ℂ)
    norm_num [Complex.I_sq, pow_succ]
  · change Complex.I ^ 1 = (Complex.I : ℂ)
    norm_num [Complex.I_sq, pow_succ]
  · change Complex.I ^ 0 = (1 : ℂ)
    norm_num [Complex.I_sq, pow_succ]
  · change Complex.I ^ 2 = (-1 : ℂ)
    norm_num [Complex.I_sq, pow_succ]
  · change Complex.I ^ 1 = (Complex.I : ℂ)
    norm_num [Complex.I_sq, pow_succ]
  · change Complex.I ^ 3 = (-Complex.I : ℂ)
    norm_num [Complex.I_sq, pow_succ]
  · change Complex.I ^ 3 = (-Complex.I : ℂ)
    norm_num [Complex.I_sq, pow_succ]
  · change Complex.I ^ 1 = (Complex.I : ℂ)
    norm_num [Complex.I_sq, pow_succ]
  · change Complex.I ^ 0 = (1 : ℂ)
    norm_num [Complex.I_sq, pow_succ]
  · change Complex.I ^ 2 = (-1 : ℂ)
    norm_num [Complex.I_sq, pow_succ]
  · change Complex.I ^ 1 = (Complex.I : ℂ)
    norm_num [Complex.I_sq, pow_succ]
  · change Complex.I ^ 3 = (-Complex.I : ℂ)
    norm_num [Complex.I_sq, pow_succ]
  · change Complex.I ^ 2 = (-1 : ℂ)
    norm_num [Complex.I_sq, pow_succ]
  · change Complex.I ^ 0 = (1 : ℂ)
    norm_num [Complex.I_sq, pow_succ]

theorem phase_zero : phase 0 = 1 := by norm_num [phase]

theorem phase_unit (a : ZMod 4) : (phase a : ℂ) * star (phase a : ℂ) = 1 := by
  fin_cases a <;> norm_num [phase, Zsqrtd.sqrtd, pow_succ, GaussianInt.toComplex_def',
    Zsqrtd.re_mul, Zsqrtd.im_mul, ZMod.val_add, ZMod.val_mul, ZMod.val_natCast, ZMod.val, Fin.val_add, Fin.val_mul, ZMod.commRing, Fin.add_def, Fin.mul_def, Complex.I_sq, GaussianInt.toComplex_mul]

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]

/-- Nonsingularity of the binary polar form gives exact character orthogonality. -/
theorem polar_character_orthogonality [DecidableEq V]
    (B : LinearMap.BilinForm (ZMod 2) V) (hB : B.Nondegenerate) (z : V) :
    (∑ w : V, sign (B z w)) = if z = 0 then (Fintype.card V : ℂ) else 0 := by
  classical
  let χ : AddChar V ℂ :=
    { toFun := fun w => sign (B z w)
      map_zero_eq_one' := by simp [sign]
      map_add_eq_mul' := by intro x y; simp only [map_add]; exact sign_add _ _ }
  have hc : χ = 0 ↔ z = 0 := by
    constructor
    · intro hz
      apply hB.1 z
      intro w
      have hh : sign (B z w) = 1 := by
        change χ w = 1
        simp [hz]
      generalize h : B z w = a at hh ⊢
      fin_cases a
      · rfl
      · norm_num [sign, ZMod.val] at hh
    · intro hz
      subst z
      ext w
      simp [χ, sign]
  have hx := AddChar.sum_eq_ite χ
  have hx' : (∑ a : V, χ a) = if z = 0 then (Fintype.card V : ℂ) else 0 := by
    simpa only [hc] using hx
  exact hx'

/-- A nondegenerate binary quadratic phase has exact Gaussian norm equal to the
cardinality of its address space, with no alternating/nonalternating case split. -/
theorem quadratic_gauss_norm [DecidableEq V]
    (B : LinearMap.BilinForm (ZMod 2) V) (hB : B.Nondegenerate)
    (q : V → ZMod 4) (hq0 : q 0 = 0)
    (hpolar : ∀ z w, q (z + w) = q z + q w + twice (B z w)) :
    (∑ z : V, phase (q z)).norm = (Fintype.card V : ℤ) := by
  have hphase : ∀ z w, (phase (q (z + w)) : ℂ) =
      (phase (q z) : ℂ) * (phase (q w) : ℂ) * sign (B z w) := by
    intro z w
    rw [hpolar]
    exact phase_polarization _ _ _
  have hn := QuadraticGauss.gauss_norm_square
    (fun z => (phase (q z) : ℂ)) (fun z w => sign (B z w)) hphase
    (fun z => phase_unit (q z)) (by rw [hq0, phase_zero]; exact GaussianInt.toComplex_one)
    (polar_character_orthogonality B hB)
  have hs : ((∑ z : V, phase (q z) : GaussianInt) : ℂ) = ∑ z : V, (phase (q z) : ℂ) := by
    exact map_sum GaussianInt.toComplex _ _
  apply Int.cast_injective (α := ℂ)
  rw [GaussianInt.intCast_complex_norm, Int.cast_natCast]
  rw [Complex.normSq_eq_conj_mul_self, hs]
  simpa only [Complex.star_def, mul_comm] using hn

/-- The normalized scalar in the general complex residual interface is exactly
a fourth root of unity, including when its binary polar form is alternating. -/
theorem quadratic_gauss_normalized_fourth_root [DecidableEq V]
    (B : LinearMap.BilinForm (ZMod 2) V) (hB : B.Nondegenerate)
    (q : V → ZMod 4) (hq0 : q 0 = 0)
    (hpolar : ∀ z w, q (z + w) = q z + q w + twice (B z w))
    (r : ℕ) (hcard : Fintype.card V = 2 ^ r) :
    (((∑ z : V, phase (q z) : GaussianInt) : ℂ) * ((1 - Complex.I) / 2) ^ r) ^ 4 = 1 := by
  apply GaussianNormalization.normalized_fourth_root
  rw [quadratic_gauss_norm B hB q hq0 hpolar, hcard]
  norm_cast

/-- Completing the square separates the residual kernel into two diagonal
fourth-root phase corrections and its binary bilinear character kernel. -/
theorem quadratic_kernel_factorization
    (B : LinearMap.BilinForm (ZMod 2) V) (q : V → ZMod 4)
    (hpolar : ∀ z w, q (z + w) = q z + q w + twice (B z w))
    (x y : V) :
    (∑ z : V, (phase (q z) : ℂ) * sign (B z (x + y))) =
      (∑ z : V, (phase (q z) : ℂ)) * (phase (q x) : ℂ)⁻¹ *
        sign (B x y) * (phase (q y) : ℂ)⁻¹ := by
  refine QuadraticGauss.kernel_factorization (fun z => (phase (q z) : ℂ))
    (fun z w => sign (B z w)) ?_ ?_ ?_ x y
  · intro z w
    rw [hpolar]
    exact phase_polarization _ _ _
  · intro z hz
    have h := phase_unit (q z)
    rw [hz, zero_mul] at h
    exact zero_ne_one h
  · intro a b
    exact sign_square _

/-- The normalization exponent can be the dimension itself: every finite
binary vector space has cardinality two to its dimension. -/
theorem quadratic_gauss_dimension_fourth_root [DecidableEq V]
    (B : LinearMap.BilinForm (ZMod 2) V) (hB : B.Nondegenerate)
    (q : V → ZMod 4) (hq0 : q 0 = 0)
    (hpolar : ∀ z w, q (z + w) = q z + q w + twice (B z w)) :
    (((∑ z : V, phase (q z) : GaussianInt) : ℂ) *
      ((1 - Complex.I) / 2) ^ Module.finrank (ZMod 2) V) ^ 4 = 1 := by
  apply quadratic_gauss_normalized_fourth_root B hB q hq0 hpolar
  rw [Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card]

end IntMul.BinaryPhase



theorem solution
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V] [DecidableEq V]
    (B : LinearMap.BilinForm (ZMod 2) V) (hB : B.Nondegenerate)
    (q : V → ZMod 4) (hq0 : q 0 = 0)
    (hpolar : ∀ z w, q (z + w) = q z + q w + IntMul.BinaryPhase.twice (B z w)) :
    (∑ z : V, IntMul.BinaryPhase.phase (q z)).norm = (Fintype.card V : ℤ) ∧
    (((∑ z : V, IntMul.BinaryPhase.phase (q z) : GaussianInt) : ℂ) *
      ((1 - Complex.I) / 2) ^ Module.finrank (ZMod 2) V) ^ 4 = 1 ∧
    ∀ x y : V,
      (∑ z : V, (IntMul.BinaryPhase.phase (q z) : ℂ) * IntMul.BinaryPhase.sign (B z (x + y))) =
        (∑ z : V, (IntMul.BinaryPhase.phase (q z) : ℂ)) *
          (IntMul.BinaryPhase.phase (q x) : ℂ)⁻¹ * IntMul.BinaryPhase.sign (B x y) *
            (IntMul.BinaryPhase.phase (q y) : ℂ)⁻¹ := by
  refine ⟨IntMul.BinaryPhase.quadratic_gauss_norm B hB q hq0 hpolar,
    IntMul.BinaryPhase.quadratic_gauss_dimension_fourth_root B hB q hq0 hpolar, ?_⟩
  intro x y
  exact IntMul.BinaryPhase.quadratic_kernel_factorization B q hpolar x y

#print axioms solution
