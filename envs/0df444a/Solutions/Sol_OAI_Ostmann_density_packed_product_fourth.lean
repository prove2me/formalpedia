-- Prove2me | solution 1 for OAI.Ostmann.density_packed_product_fourth
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T06:34:49.773802+00:00
-- url     : https://prove2.me/submissions/73f589bb-3e42-492f-88f2-29e3be6e8387

import Mathlib
import Definitions.Def_OAIQ095D006
import Theorems.Thm_OAI_Ostmann_densitySmoothedSquare_mean

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_AdditiveFourier
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Probability-normalized additive Fourier identities

These finite identities provide the normalization used in Section 6.
Fourier inversion is the library's discrete Fourier inversion theorem.
-/

namespace Ostmann

open scoped BigOperators ComplexConjugate

theorem stdAddChar_conj {p : ℕ} [NeZero p] (x : ZMod p) :
    conj (ZMod.stdAddChar x) = ZMod.stdAddChar (-x) := by
  have hn : ‖ZMod.stdAddChar x‖ = 1 := by simp [ZMod.stdAddChar_apply]; exact Circle.norm_coe _
  rw [← Complex.inv_eq_conj hn, AddChar.map_neg_eq_inv]

theorem additiveFourier_inversion {p : ℕ} [NeZero p]
    (f : ZMod p → ℂ) (x : ZMod p) :
    f x = ∑ a : ZMod p, additiveFourier f a * ZMod.stdAddChar (a * x) := by
  have hinv := congrFun (ZMod.dft.symm_apply_apply f) x
  rw [ZMod.invDFT_apply] at hinv
  calc
    f x = (p : ℂ)⁻¹ * ∑ a : ZMod p, ZMod.stdAddChar (a * x) * ZMod.dft f a := by
      simpa only [smul_eq_mul] using hinv.symm
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      simp only [additiveFourier]
      ring

theorem additiveFourier_conjugate_coefficient {p : ℕ} [NeZero p]
    (f : ZMod p → ℂ) (a : ZMod p) :
    (∑ x : ZMod p, ZMod.stdAddChar (x * a) * conj (f x)) =
      (p : ℂ) * conj (additiveFourier f a) := by
  have hp : (p : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne p
  rw [additiveFourier_apply]
  simp only [map_mul, map_inv₀, map_natCast, map_sum, stdAddChar_conj, neg_neg]
  rw [← mul_assoc, mul_inv_cancel₀ hp, one_mul]
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem additiveFourier_energy {p : ℕ} [NeZero p] (f : ZMod p → ℂ) :
    (∑ x : ZMod p, ‖f x‖ ^ 2) =
      (p : ℝ) * ∑ a : ZMod p, ‖additiveFourier f a‖ ^ 2 := by
  have heq : (∑ x : ZMod p, f x * conj (f x)) =
      (p : ℂ) * ∑ a : ZMod p, additiveFourier f a * conj (additiveFourier f a) := by
    calc
      _ = ∑ x : ZMod p, ∑ a : ZMod p,
          additiveFourier f a * ZMod.stdAddChar (a * x) * conj (f x) := by
        apply Finset.sum_congr rfl
        intro x _
        rw [← Finset.sum_mul, ← additiveFourier_inversion]
      _ = ∑ a : ZMod p, additiveFourier f a *
          ∑ x : ZMod p, ZMod.stdAddChar (x * a) * conj (f x) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro a _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        rw [mul_comm x a]
        ring
      _ = _ := by
        simp_rw [additiveFourier_conjugate_coefficient]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a _
        ring
  simp_rw [Complex.mul_conj', ← Complex.ofReal_pow, ← Complex.ofReal_sum] at heq
  exact_mod_cast heq

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_PrimitiveGaussFourier
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact primitive-character Fourier transform at composite modulus

This supplies the complete transform and Gauss normalization needed in the
quadratic Poisson step, using the proved library character identities.
-/

namespace Ostmann

open scoped BigOperators ComplexConjugate

theorem primitive_character_fourier {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) (a : ZMod N) :
    additiveFourier χ a = (N : ℂ)⁻¹ * χ⁻¹ (-a) * gaussSum χ ZMod.stdAddChar := by
  rw [additiveFourier_apply]
  have heq : (∑ x : ZMod N, χ x * ZMod.stdAddChar (-(x * a))) =
      gaussSum χ ((ZMod.stdAddChar (N := N)).mulShift (-a)) := by
    simp only [gaussSum, AddChar.mulShift_apply]
    congr 1
    funext x
    rw [neg_mul, mul_comm a x]
  rw [heq, gaussSum_mulShift_of_isPrimitive ZMod.stdAddChar hχ (-a)]
  ring

/-- Parseval gives the primitive Gauss-sum norm without a prime-modulus
restriction and without assuming a separate analytic input. -/
theorem primitive_gauss_norm_sq {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) :
    ‖gaussSum χ (ZMod.stdAddChar (N := N))‖ ^ 2 = (N : ℝ) := by
  let E : ℝ := ∑ a : ZMod N, ‖χ a‖ ^ 2
  have hE : 0 < E := by
    have hh := Finset.single_le_sum (s := (Finset.univ : Finset (ZMod N)))
      (f := fun a => ‖χ a‖ ^ 2) (fun a _ => sq_nonneg ‖χ a‖) (Finset.mem_univ (1 : ZMod N))
    have h1 : (1 : ℝ) ≤ E := by simpa [E] using hh
    linarith
  have hinv : (∑ a : ZMod N, ‖χ⁻¹ (-a)‖ ^ 2) = E := by
    simp_rw [← MulChar.star_apply', norm_star]
    exact (Equiv.neg (ZMod N)).bijective.sum_comp (fun a => ‖χ a‖ ^ 2)
  have hfourier : (∑ a : ZMod N, ‖additiveFourier χ a‖ ^ 2) =
      (N : ℝ)⁻¹ ^ 2 * ‖gaussSum χ ZMod.stdAddChar‖ ^ 2 * E := by
    rw [← hinv, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    rw [primitive_character_fourier χ hχ a]
    simp only [Complex.norm_mul, norm_inv, Complex.norm_natCast, mul_pow]
    ring
  have heq := additiveFourier_energy χ
  rw [hfourier] at heq
  change E = (N : ℝ) * ((N : ℝ)⁻¹ ^ 2 * ‖gaussSum χ ZMod.stdAddChar‖ ^ 2 * E) at heq
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
  apply mul_right_cancel₀ hE.ne'
  field_simp [hN] at heq
  nlinarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_RealQuadraticPhase
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Real quadratic phases and their linear correlations

These are the concrete exponential sums used in the inverse quadratic step.
-/

namespace Ostmann

open scoped BigOperators ComplexConjugate

theorem realAdditivePhase_add (x y : ℝ) :
    realAdditivePhase (x + y) = realAdditivePhase x * realAdditivePhase y := by
  unfold realAdditivePhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_ScaledPoisson
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original scale in the quadratic-character Poisson formula -/

namespace Ostmann

open scoped BigOperators FourierTransform SchwartzMap
open MeasureTheory

theorem fourier_comp_positive_mul (f : ℝ → ℂ) {a : ℝ} (ha : 0 < a) (ξ : ℝ) :
    𝓕 (fun x => f (a * x)) ξ = (a : ℂ)⁻¹ * 𝓕 f (ξ / a) := by
  rw [Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul]
  let g : ℝ → ℂ := fun y => Complex.exp (((-2 * Real.pi * y * (ξ / a) : ℝ) : ℂ) * Complex.I) • f y
  have hi : (∫ x : ℝ, Complex.exp (((-2 * Real.pi * x * ξ : ℝ) : ℂ) * Complex.I) • f (a * x)) =
      ∫ x : ℝ, g (a * x) := by
    apply integral_congr_ae
    filter_upwards [] with x
    dsimp [g]
    have he : (-2 * Real.pi * (a * x) * (ξ / a) : ℝ) = -2 * Real.pi * x * ξ := by
      field_simp
    rw [he]
  rw [hi, Measure.integral_comp_mul_left]
  simp only [abs_of_pos (inv_pos.mpr ha), Complex.real_smul, Complex.ofReal_inv]
  rfl

theorem positiveDilate_apply (f : 𝓢(ℝ, ℂ)) (a : ℝ) (ha : 0 < a) (x : ℝ) :
    positiveDilate f a ha x = f (a * x) := rfl

theorem positiveDilate_fourier (f : 𝓢(ℝ, ℂ)) (a : ℝ) (ha : 0 < a) (ξ : ℝ) :
    𝓕 (positiveDilate f a ha) ξ = (a : ℂ)⁻¹ * 𝓕 f (ξ / a) := by
  change 𝓕 (fun x : ℝ => f (a * x)) ξ = (a : ℂ)⁻¹ * 𝓕 (f : ℝ → ℂ) (ξ / a)
  exact fourier_comp_positive_mul f ha ξ

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_AdditiveSieveProbability
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The additive large sieve for a uniform measure on an actual interval subset -/

namespace Ostmann
open scoped Classical BigOperators

theorem sieveAdditivePhase_eq_stdAddChar (q : ℕ) [NeZero q] (h : ℕ) (n : ℤ) :
    sieveAdditivePhase q h n = ZMod.stdAddChar ((h : ZMod q) * (n : ZMod q)) := by
  have hh : (h : ZMod q) * (n : ZMod q) = (((h : ℤ) * n : ℤ) : ZMod q) := by
    push_cast
    rfl
  rw [hh, ZMod.stdAddChar_coe]
  unfold sieveAdditivePhase
  congr 1
  push_cast
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_ReducedFrequencyEnergy
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reduced-frequency energy of a uniform set and its Ramanujan kernel -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

theorem sum_reducedNumerators_eq_units {q : ℕ} [NeZero q]
    {R : Type*} [AddCommMonoid R] (f : ℕ → R) :
    (∑ h ∈ reducedNumerators q, f h) = ∑ u : (ZMod q)ˣ, f (u : ZMod q).val := by
  change (∑ h ∈ reducedResidues q, f h) = _
  rw [← Finset.sum_coe_sort]
  exact ((unitReducedResidueEquiv q).sum_comp (fun a => f a.val)).symm

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterRootNumberUnit
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact modulus of the primitive character root number -/

namespace Ostmann

open Complex
open scoped Classical

 theorem PrimitiveComplexCharacter.rootNumber_norm_eq_one (χ : PrimitiveComplexCharacter) :
    ‖@DirichletCharacter.rootNumber χ.modulus ⟨χ.positive.ne'⟩ χ.character‖ = 1 := by
  let : NeZero χ.modulus := ⟨χ.positive.ne'⟩
  have hq : (0 : ℝ) < χ.modulus := by exact_mod_cast χ.positive
  have hn : ‖(χ.modulus : ℂ) ^ (1 / 2 : ℂ)‖ = Real.sqrt χ.modulus := by
    rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hq]
    norm_num only [div_ofNat_re, one_re]
    exact (Real.sqrt_eq_rpow _).symm
  have hG : ‖gaussSum χ.character ZMod.stdAddChar‖ = Real.sqrt χ.modulus := by
    apply (sq_eq_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
    rw [primitive_gauss_norm_sq χ.character χ.primitive, Real.sq_sqrt hq.le]
  simp only [DirichletCharacter.rootNumber, norm_div, norm_pow, norm_I, one_pow, div_one, hn, hG]
  exact div_self (Real.sqrt_pos.mpr hq).ne'

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_SkewKernelSquare
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A finite algebraic identity for the large-sieve kernel

This is the cancellation underlying Montgomery--Vaughan's equation (3.6).
The diagonal correction is retained explicitly before any norm estimate.
-/

namespace Ostmann

open scoped BigOperators

section
variable {ι K : Type*} [Fintype ι] [DecidableEq ι] [CommRing K]

 theorem skew_kernel_square_entry (h k : ι → ι → K)
    (hdiag : ∀ i, h i i = 0) (kdiag : ∀ i, k i i = 0)
    (kskew : ∀ i j, k i j = -k j i)
    (htriple : ∀ r s t, r ≠ s → r ≠ t → s ≠ t →
      h r s * h r t = h s t * (k r s - k r t)) (s t : ι) :
    (∑ r, h r s * h r t) =
      (if s = t then ∑ r, h r s ^ 2 else 0) +
        h s t * ((∑ r, k r s) - ∑ r, k r t) + 2 * h s t * k s t := by
  by_cases hst : s = t
  · subst t
    simp [hdiag, sq]
  · have he (r : ι) : h r s * h r t = h s t * (k r s - k r t) +
        (if r = s then h s t * k s t else 0) +
        (if r = t then h s t * k s t else 0) := by
      by_cases hrs : r = s
      · subst r
        simp [hdiag, kdiag, hst]
      · by_cases hrt : r = t
        · subst r
          rw [hdiag, kdiag, kskew t s]
          simp only [hrs, ↓reduceIte]
          ring
        · simp only [hrs, hrt, ↓reduceIte, add_zero]
          exact htriple r s t hrs hrt hst
    simp_rw [he]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    simp only [hst, ↓reduceIte, zero_add, ← Finset.mul_sum, Finset.sum_sub_distrib,
      Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    ring

end

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_HermitianEigenvector
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite Hermitian eigenvector cancellation -/

namespace Ostmann

open Matrix
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

theorem hermitian_eigenvector_left {A : Matrix ι ι ℂ} (hA : A.IsHermitian)
    (u : ι → ℂ) (μ : ℝ) (heig : A *ᵥ u = (μ : ℂ) • u) (v : ι → ℂ) :
    star u ⬝ᵥ (A *ᵥ v) = (μ : ℂ) * (star u ⬝ᵥ v) := by
  have h : star u ⬝ᵥ (A *ᵥ v) = star (A *ᵥ u) ⬝ᵥ v := by
    rw [Matrix.star_mulVec, hA.eq, Matrix.dotProduct_mulVec]
  rw [h, heig, star_smul, smul_dotProduct]
  simp

theorem hermitian_eigenvector_commutator {A : Matrix ι ι ℂ} (hA : A.IsHermitian)
    (D : Matrix ι ι ℂ) (u : ι → ℂ) (μ : ℝ) (heig : A *ᵥ u = (μ : ℂ) • u) :
    star u ⬝ᵥ ((D * A - A * D) *ᵥ u) = 0 := by
  rw [sub_mulVec, dotProduct_sub, ← mulVec_mulVec, ← mulVec_mulVec,
    heig, mulVec_smul, dotProduct_smul, hermitian_eigenvector_left hA u μ heig]
  simp only [smul_eq_mul, sub_self]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_CosecantMatrix
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact square of the finite cosecant matrix -/

namespace Ostmann

open Matrix
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
 theorem imaginaryKernelMatrix_hermitian (h : ι → ι → ℝ)
    (hskew : ∀ s t, h s t = -h t s) : (imaginaryKernelMatrix h).IsHermitian := by
  ext s t
  simp only [imaginaryKernelMatrix, conjTranspose_apply, Matrix.of_apply, map_mul, Complex.star_def,
    Complex.conj_I, Complex.conj_ofReal]
  rw [hskew t s]
  push_cast
  ring

 theorem imaginaryKernelMatrix_square_entry (h k : ι → ι → ℝ)
    (hdiag : ∀ i, h i i = 0) (kdiag : ∀ i, k i i = 0)
    (hskew : ∀ i j, h i j = -h j i) (kskew : ∀ i j, k i j = -k j i)
    (htriple : ∀ r s t, r ≠ s → r ≠ t → s ≠ t →
      h r s * h r t = h s t * (k r s - k r t)) (s t : ι) :
    (imaginaryKernelMatrix h * imaginaryKernelMatrix h) s t =
      (if s = t then ((∑ r, h r s ^ 2 : ℝ) : ℂ) else 0) +
        (h s t : ℂ) * ((∑ r, k r s : ℝ) - ∑ r, k r t) +
          2 * (h s t : ℂ) * (k s t : ℂ) := by
  have he (r : ι) : imaginaryKernelMatrix h s r * imaginaryKernelMatrix h r t =
      ((h r s * h r t : ℝ) : ℂ) := by
    dsimp [imaginaryKernelMatrix]
    rw [hskew s r]
    push_cast
    calc
      _ = -(Complex.I * Complex.I) * ((h r s : ℂ) * (h r t : ℂ)) := by ring
      _ = _ := by rw [Complex.I_mul_I]; ring
  rw [Matrix.mul_apply]
  simp_rw [he]
  rw [← Complex.ofReal_sum, skew_kernel_square_entry h k hdiag kdiag kskew htriple]
  push_cast
  by_cases hst : s = t <;> simp [hst]

 theorem imaginaryKernelMatrix_square (h k : ι → ι → ℝ)
    (hdiag : ∀ i, h i i = 0) (kdiag : ∀ i, k i i = 0)
    (hskew : ∀ i j, h i j = -h j i) (kskew : ∀ i j, k i j = -k j i)
    (htriple : ∀ r s t, r ≠ s → r ≠ t → s ≠ t →
      h r s * h r t = h s t * (k r s - k r t)) :
    let A : Matrix ι ι ℂ := imaginaryKernelMatrix h
    let D : Matrix ι ι ℂ := Matrix.diagonal (fun s => ((∑ r, k r s : ℝ) : ℂ))
    A * A = Matrix.diagonal (fun s => ((∑ r, h r s ^ 2 : ℝ) : ℂ)) -
      (Complex.I • (D * A - A * D) : Matrix ι ι ℂ) +
        (2 : ℂ) • Matrix.of (fun s t => ((h s t * k s t : ℝ) : ℂ)) := by
  dsimp only
  ext s t
  rw [imaginaryKernelMatrix_square_entry h k hdiag kdiag hskew kskew htriple]
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.diagonal_apply, Matrix.diagonal_mul, Matrix.mul_diagonal,
    imaginaryKernelMatrix, Matrix.of_apply]
  simp only [Complex.ofReal_sum, Complex.ofReal_pow, Complex.ofReal_mul,
    ]
  ring_nf
  simp only [Complex.I_sq]
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_SymmetricQuadraticBound
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The finite quadratic bound for the cosecant row estimate -/

namespace Ostmann

open Matrix
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

theorem real_symmetric_quadratic_upper (v : ι → ι → ℝ)
    (hv : ∀ s t, v s t = v t s) (u : ι → ℂ) :
    ‖star u ⬝ᵥ ((fun s t => (v s t : ℂ)) *ᵥ u)‖ ≤
      ∑ s, ‖u s‖ ^ 2 * ∑ t, |v s t| := by
  have he : star u ⬝ᵥ ((fun s t => (v s t : ℂ)) *ᵥ u) =
      ∑ s, ∑ t, star (u s) * (v s t : ℂ) * u t := by
    simp only [dotProduct, mulVec, Pi.star_apply, Finset.mul_sum, mul_assoc]
  have hswap : (∑ s, ∑ t, |v s t| * ‖u t‖ ^ 2) =
      ∑ s, ∑ t, |v s t| * ‖u s‖ ^ 2 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro t _
    rw [hv t s]
  have hfactor : (∑ s, ∑ t, |v s t| * ‖u s‖ ^ 2) =
      ∑ s, ‖u s‖ ^ 2 * ∑ t, |v s t| := by
    apply Finset.sum_congr rfl
    intro s _
    rw [← Finset.sum_mul, mul_comm]
  have havg : (∑ s, ∑ t, |v s t| * (‖u s‖ ^ 2 + ‖u t‖ ^ 2) / 2) =
      ∑ s, ‖u s‖ ^ 2 * ∑ t, |v s t| := by
    simp_rw [mul_add, add_div, Finset.sum_add_distrib, ← Finset.sum_div]
    rw [hswap]
    rw [hfactor]
    ring
  rw [he]
  calc
    _ ≤ ∑ s, ‖∑ t, star (u s) * (v s t : ℂ) * u t‖ := norm_sum_le _ _
    _ ≤ ∑ s, ∑ t, ‖star (u s) * (v s t : ℂ) * u t‖ :=
      Finset.sum_le_sum (fun s _ => norm_sum_le _ _)
    _ = ∑ s, ∑ t, |v s t| * ‖u s‖ * ‖u t‖ := by
      simp only [norm_mul, norm_star, Complex.norm_real, Real.norm_eq_abs]
      apply Finset.sum_congr rfl
      intro s _
      apply Finset.sum_congr rfl
      intro t _
      ring
    _ ≤ ∑ s, ∑ t, |v s t| * (‖u s‖ ^ 2 + ‖u t‖ ^ 2) / 2 := by
      apply Finset.sum_le_sum
      intro s _
      apply Finset.sum_le_sum
      intro t _
      have hh := mul_le_mul_of_nonneg_left (sq_nonneg (‖u s‖ - ‖u t‖)) (abs_nonneg (v s t))
      nlinarith
    _ = _ := havg

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_KernelEigenvalueBound
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Schur's eigenvalue bound for the concrete finite kernel identity -/

namespace Ostmann

open Matrix
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem complex_diagonal_quadratic (d : ι → ℝ) (u : ι → ℂ) :
    star u ⬝ᵥ ((Matrix.diagonal (fun s => (d s : ℂ))) *ᵥ u) =
      ((∑ s, d s * ‖u s‖ ^ 2 : ℝ) : ℂ) := by
  simp only [Matrix.mulVec_diagonal, dotProduct, Pi.star_apply, Complex.ofReal_sum,
    Complex.ofReal_mul, Complex.ofReal_pow]
  apply Finset.sum_congr rfl
  intro s _
  rw [show star (u s) * ((d s : ℂ) * u s) = (d s : ℂ) * (star (u s) * u s) by ring,
    Complex.star_def, Complex.conj_mul']

omit [DecidableEq ι] in
 theorem complex_self_quadratic (u : ι → ℂ) :
    star u ⬝ᵥ u = ((∑ s, ‖u s‖ ^ 2 : ℝ) : ℂ) := by
  simp only [dotProduct, Pi.star_apply, Complex.ofReal_sum, Complex.ofReal_pow]
  apply Finset.sum_congr rfl
  intro s _
  simpa only [Complex.star_def] using Complex.conj_mul' (u s)

 theorem kernel_eigenvalue_bound (h k : ι → ι → ℝ)
    (hdiag : ∀ i, h i i = 0) (kdiag : ∀ i, k i i = 0)
    (hskew : ∀ i j, h i j = -h j i) (kskew : ∀ i j, k i j = -k j i)
    (htriple : ∀ r s t, r ≠ s → r ≠ t → s ≠ t →
      h r s * h r t = h s t * (k r s - k r t))
    (B μ : ℝ) (hrow : ∀ s, (∑ r, h r s ^ 2) + 2 * ∑ r, |h s r * k s r| ≤ B)
    (u : ι → ℂ) (hu : 0 < ∑ s, ‖u s‖ ^ 2)
    (heig : imaginaryKernelMatrix h *ᵥ u = (μ : ℂ) • u) : μ ^ 2 ≤ B := by
  let A := imaginaryKernelMatrix h
  let D := Matrix.diagonal (fun s => ((∑ r, k r s : ℝ) : ℂ))
  let V : Matrix ι ι ℂ := Matrix.of (fun s t => ((h s t * k s t : ℝ) : ℂ))
  have hA : A.IsHermitian := imaginaryKernelMatrix_hermitian h hskew
  have hcomm := hermitian_eigenvector_commutator hA D u μ heig
  have hsq : star u ⬝ᵥ ((A * A) *ᵥ u) =
      ((μ ^ 2 * ∑ s, ‖u s‖ ^ 2 : ℝ) : ℂ) := by
    rw [← mulVec_mulVec, heig, mulVec_smul, heig, smul_smul, dotProduct_smul,
      complex_self_quadratic]
    push_cast
    simp only [smul_eq_mul, pow_two]
  have hidentity := imaginaryKernelMatrix_square h k hdiag kdiag hskew kskew htriple
  change A * A = Matrix.diagonal (fun s => ((∑ r, h r s ^ 2 : ℝ) : ℂ)) -
    Complex.I • (D * A - A * D) + (2 : ℂ) • V at hidentity
  rw [hidentity, add_mulVec, sub_mulVec, smul_mulVec, dotProduct_add, dotProduct_sub,
    dotProduct_smul, hcomm, smul_zero, sub_zero, smul_mulVec, dotProduct_smul,
    complex_diagonal_quadratic] at hsq
  have hreal := congrArg Complex.re hsq
  have htwo (z : ℂ) : ((2 : ℂ) • z).re = 2 * z.re := by simp [smul_eq_mul, Complex.mul_re]
  simp only [Complex.add_re, Complex.ofReal_re, htwo] at hreal
  have hsym : ∀ s t, h s t * k s t = h t s * k t s := by
    intro s t
    rw [hskew s t, kskew s t]
    ring
  have hv := real_symmetric_quadratic_upper (fun s t => h s t * k s t) hsym u
  have hvr : (star u ⬝ᵥ (V *ᵥ u)).re ≤
      ∑ s, ‖u s‖ ^ 2 * ∑ t, |h s t * k s t| :=
    (Complex.re_le_norm _).trans hv
  have hsum : (∑ s, (∑ r, h r s ^ 2) * ‖u s‖ ^ 2) +
      2 * (∑ s, ‖u s‖ ^ 2 * ∑ r, |h s r * k s r|) ≤
        B * ∑ s, ‖u s‖ ^ 2 := by
    calc
      _ = ∑ s, ‖u s‖ ^ 2 * ((∑ r, h r s ^ 2) + 2 * ∑ r, |h s r * k s r|) := by
        simp only [mul_add, Finset.sum_add_distrib]
        congr 1
        · apply Finset.sum_congr rfl
          intro s _
          ring
        · rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro s _
          ring
      _ ≤ ∑ s, ‖u s‖ ^ 2 * B := Finset.sum_le_sum (fun s _ =>
        mul_le_mul_of_nonneg_left (hrow s) (sq_nonneg _))
      _ = _ := by rw [← Finset.sum_mul, mul_comm]
  have hfinal : μ ^ 2 * (∑ s, ‖u s‖ ^ 2) ≤ B * (∑ s, ‖u s‖ ^ 2) := by
    nlinarith
  exact (mul_le_mul_iff_left₀ hu).mp hfinal

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_FiniteMatrixDuality
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite Hilbert-space duality for the large-sieve phase matrix -/

namespace Ostmann

open Matrix
open scoped BigOperators

 theorem finite_complex_cauchy_schwarz {ι : Type*} [Fintype ι] (u v : ι → ℂ) :
    ‖star u ⬝ᵥ v‖ ^ 2 ≤ (∑ i, ‖u i‖ ^ 2) * ∑ i, ‖v i‖ ^ 2 := by
  let U : EuclideanSpace ℂ ι := (EuclideanSpace.equiv ι ℂ).symm u
  let V : EuclideanSpace ℂ ι := (EuclideanSpace.equiv ι ℂ).symm v
  have hi : inner ℂ U V = star u ⬝ᵥ v := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    exact dotProduct_comm _ _
  have hh := pow_le_pow_left₀ (norm_nonneg (inner ℂ U V)) (norm_inner_le_norm U V) 2
  rw [hi, mul_pow, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq] at hh
  exact hh

 theorem finite_matrix_duality {ι κ : Type*} [Fintype ι] [Fintype κ]
    (F : Matrix ι κ ℂ) (K : ℝ) (hK : 0 ≤ K)
    (hdual : ∀ b : ι → ℂ, (∑ j, ‖(Fᴴ *ᵥ b) j‖ ^ 2) ≤ K * ∑ i, ‖b i‖ ^ 2)
    (c : κ → ℂ) :
    (∑ i, ‖(F *ᵥ c) i‖ ^ 2) ≤ K * ∑ j, ‖c j‖ ^ 2 := by
  let b := F *ᵥ c
  have hE : 0 ≤ ∑ i, ‖b i‖ ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hC : 0 ≤ ∑ j, ‖c j‖ ^ 2 := Finset.sum_nonneg (fun j _ => sq_nonneg _)
  by_cases hzero : (∑ i, ‖b i‖ ^ 2) = 0
  · change (∑ i, ‖b i‖ ^ 2) ≤ _
    rw [hzero]
    exact mul_nonneg hK hC
  have hEpos : 0 < ∑ i, ‖b i‖ ^ 2 := lt_of_le_of_ne hE (Ne.symm hzero)
  have hid : star (Fᴴ *ᵥ b) ⬝ᵥ c = star b ⬝ᵥ b := by
    rw [star_mulVec, conjTranspose_conjTranspose, ← dotProduct_mulVec]
  have hcauchy := finite_complex_cauchy_schwarz (Fᴴ *ᵥ b) c
  rw [hid, complex_self_quadratic, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hE] at hcauchy
  have hmul := mul_le_mul_of_nonneg_right (hdual b) hC
  change (∑ i, ‖b i‖ ^ 2) ≤ _
  have hh : (∑ i, ‖b i‖ ^ 2) * (∑ i, ‖b i‖ ^ 2) ≤
      (K * ∑ j, ‖c j‖ ^ 2) * (∑ i, ‖b i‖ ^ 2) := by nlinarith
  exact (mul_le_mul_iff_left₀ hEpos).mp hh

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_PrimitiveCharacterSieve
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The additive-sieve majorant for one primitive character -/

namespace Ostmann

open Matrix
open scoped BigOperators Classical

 theorem sum_units_eq_sum_ite {q : ℕ} [NeZero q] (f : ZMod q → ℂ) :
    (∑ u : (ZMod q)ˣ, f u) = ∑ x : ZMod q, if IsUnit x then f x else 0 := by
  classical
  calc
    _ = ∑ x ∈ (Finset.univ : Finset (ZMod q)).filter IsUnit, f x := by
      apply Finset.sum_bij (fun (u : (ZMod q)ˣ) _ => (u : ZMod q))
      · intro u _
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact u.isUnit
      · intro u _ v _ huv
        exact Units.val_injective huv
      · intro x hx
        obtain ⟨u, hu⟩ := (Finset.mem_filter.mp hx).2
        exact ⟨u, Finset.mem_univ _, hu⟩
      · intro _ _
        rfl
    _ = _ := by rw [Finset.sum_filter]

 theorem primitive_unit_gauss {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (a : ZMod q) :
    (∑ u : (ZMod q)ˣ, χ u * ZMod.stdAddChar ((u : ZMod q) * a)) =
      χ⁻¹ a * gaussSum χ ZMod.stdAddChar := by
  rw [sum_units_eq_sum_ite (fun x : ZMod q => χ x * ZMod.stdAddChar (x * a))]
  have he : (∑ x : ZMod q, if IsUnit x then χ x * ZMod.stdAddChar (x * a) else 0) =
      ∑ x : ZMod q, χ x * ZMod.stdAddChar (x * a) := by
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : IsUnit x
    · rw [ite_eq_left hx]
    · rw [ite_eq_right hx, χ.map_nonunit hx, zero_mul]
  rw [he]
  have hg := gaussSum_mulShift_of_isPrimitive ZMod.stdAddChar hχ a
  simpa only [gaussSum, AddChar.mulShift_apply, mul_comm a] using hg

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterUnitParseval
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Parseval on the full group of Dirichlet characters

The complete unit-group orthogonality is needed before restricting to primitive
characters; applying Cauchy--Schwarz separately would lose the conductor.
-/

namespace Ostmann

open scoped BigOperators ComplexConjugate

 theorem character_unit_gram {q : ℕ} [NeZero q] (u v : (ZMod q)ˣ) :
    (∑ χ : DirichletCharacter ℂ q, χ u * star (χ v)) =
      if u = v then (q.totient : ℂ) else 0 := by
  have hs (χ : DirichletCharacter ℂ q) : star (χ (v : ZMod q)) = χ ((v : ZMod q)⁻¹) := by
    rw [MulChar.star_apply', MulChar.inv_apply, Ring.inverse_unit]
    rw [ZMod.inv_coe_unit]
  calc
    _ = ∑ χ : DirichletCharacter ℂ q, χ ((v : ZMod q)⁻¹) * χ u := by
      apply Finset.sum_congr rfl
      intro χ _
      rw [hs χ, mul_comm]
    _ = _ := by
      rw [DirichletCharacter.sum_char_inv_mul_char_eq ℂ v.isUnit]
      congr 1
      exact propext ⟨fun h => (Units.val_injective h).symm,
        fun h => congrArg Units.val h.symm⟩

 theorem character_unit_parseval {q : ℕ} [NeZero q] (f : (ZMod q)ˣ → ℂ) :
    (∑ χ : DirichletCharacter ℂ q, ‖∑ u : (ZMod q)ˣ, χ u * f u‖ ^ 2) =
      (q.totient : ℝ) * ∑ u : (ZMod q)ˣ, ‖f u‖ ^ 2 := by
  apply Complex.ofReal_injective
  push_cast
  simp_rw [← Complex.mul_conj', map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Eq.trans (b := ∑ u : (ZMod q)ˣ, ∑ v : (ZMod q)ˣ,
    f u * star (f v) * (∑ χ : DirichletCharacter ℂ q, χ u * star (χ v)))
  · apply Finset.sum_congr rfl
    intro u _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro v _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro χ _
    simp only [starRingEnd_apply]
    ring
  · simp_rw [character_unit_gram]
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true, if_true]
    apply Finset.sum_congr rfl
    intro u _
    simp only [starRingEnd_apply]
    ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_PrimitiveCharacterEnergy
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Simultaneous primitive-character energy at a fixed modulus -/

namespace Ostmann

open scoped BigOperators ComplexConjugate

 theorem primitive_inverse_energy {q : ℕ} [NeZero q] {ι : Type*} [Fintype ι]
    (S : Finset (DirichletCharacter ℂ q)) (hS : ∀ χ ∈ S, χ.IsPrimitive)
    (c : ι → ℂ) (a : ι → ZMod q) :
    (q : ℝ) * ∑ χ ∈ S, ‖∑ j, c j * χ⁻¹ (a j)‖ ^ 2 ≤
      (q.totient : ℝ) * ∑ u : (ZMod q)ˣ,
        ‖∑ j, c j * ZMod.stdAddChar ((u : ZMod q) * a j)‖ ^ 2 := by
  let f : (ZMod q)ˣ → ℂ := fun u => ∑ j, c j * ZMod.stdAddChar ((u : ZMod q) * a j)
  have hid (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) :
      (q : ℝ) * ‖∑ j, c j * χ⁻¹ (a j)‖ ^ 2 = ‖∑ u : (ZMod q)ˣ, χ u * f u‖ ^ 2 := by
    have hg : (∑ u : (ZMod q)ˣ, χ u * f u) =
        (∑ j, c j * χ⁻¹ (a j)) * gaussSum χ ZMod.stdAddChar := by
      simp only [f, Finset.mul_sum]
      rw [Finset.sum_comm]
      calc
        _ = ∑ j, c j * ∑ u : (ZMod q)ˣ,
            χ u * ZMod.stdAddChar ((u : ZMod q) * a j) := by
          simp only [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          apply Finset.sum_congr rfl
          intro u _
          ring
        _ = _ := by
          simp_rw [primitive_unit_gauss χ hχ]
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro j _
          ring
    rw [hg, norm_mul, mul_pow, primitive_gauss_norm_sq χ hχ, mul_comm]
  calc
    _ = ∑ χ ∈ S, ‖∑ u : (ZMod q)ˣ, χ u * f u‖ ^ 2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun χ hχ => hid χ (hS χ hχ))
    _ ≤ ∑ χ : DirichletCharacter ℂ q, ‖∑ u : (ZMod q)ˣ, χ u * f u‖ ^ 2 :=
      Finset.sum_le_univ_sum_of_nonneg (fun _ => sq_nonneg _)
    _ = _ := character_unit_parseval f

 theorem primitive_inverse_energy_le {q : ℕ} [NeZero q] {ι : Type*} [Fintype ι]
    (S : Finset (DirichletCharacter ℂ q)) (hS : ∀ χ ∈ S, χ.IsPrimitive)
    (c : ι → ℂ) (a : ι → ZMod q) :
    (∑ χ ∈ S, ‖∑ j, c j * χ⁻¹ (a j)‖ ^ 2) ≤
      ∑ u : (ZMod q)ˣ, ‖∑ j, c j * ZMod.stdAddChar ((u : ZMod q) * a j)‖ ^ 2 := by
  have ht : q.totient ≤ q := Nat.totient_le q
  have h := primitive_inverse_energy S hS c a
  have he : 0 ≤ ∑ u : (ZMod q)ˣ,
      ‖∑ j, c j * ZMod.stdAddChar ((u : ZMod q) * a j)‖ ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  exact (mul_le_mul_iff_right₀ hq).mp
    (h.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast ht) he))

 theorem primitive_character_energy_le {q : ℕ} [NeZero q] {ι : Type*} [Fintype ι]
    (S : Finset (DirichletCharacter ℂ q)) (hS : ∀ χ ∈ S, χ.IsPrimitive)
    (c : ι → ℂ) (a : ι → ZMod q) :
    (∑ χ ∈ S, ‖∑ j, c j * χ (a j)‖ ^ 2) ≤
      ∑ u : (ZMod q)ˣ, ‖∑ j, star (c j) *
        ZMod.stdAddChar ((u : ZMod q) * a j)‖ ^ 2 := by
  have h := primitive_inverse_energy_le S hS (fun j => star (c j)) a
  have hn (χ : DirichletCharacter ℂ q) :
      ‖∑ j, star (c j) * χ⁻¹ (a j)‖ = ‖∑ j, c j * χ (a j)‖ := by
    calc
      _ = ‖star (∑ j, c j * χ (a j))‖ := by
        congr 1
        simp only [star_sum, star_mul, MulChar.star_apply', mul_comm]
      _ = _ := norm_star _
  simpa only [hn] using h

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_CosecantKernel
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The cosecant kernel in the sharp additive large sieve

The finite-kernel identity is equation (3.6) of Montgomery--Vaughan,
Hilbert's inequality, JLMS (2) 8 (1974), 73--82. The scalar majorant is
Lemma 1 there. Only these concrete trigonometric statements are used.
-/

namespace Ostmann

theorem cosecantKernel_skew (x y : ℝ) : cosecantKernel x y = -cosecantKernel y x := by
  have he : Real.pi * (x - y) = -(Real.pi * (y - x)) := by ring
  simp [cosecantKernel, he]

theorem cotangentKernel_skew (x y : ℝ) : cotangentKernel x y = -cotangentKernel y x := by
  have he : Real.pi * (x - y) = -(Real.pi * (y - x)) := by ring
  simp [cotangentKernel, he, div_neg]

theorem cosecantKernel_triple (x y z : ℝ)
    (hxy : Real.sin (Real.pi * (x - y)) ≠ 0)
    (hxz : Real.sin (Real.pi * (x - z)) ≠ 0)
    (hyz : Real.sin (Real.pi * (y - z)) ≠ 0) :
    cosecantKernel x y * cosecantKernel x z =
      cosecantKernel y z * (cotangentKernel x y - cotangentKernel x z) := by
  have he : Real.pi * (y - z) = Real.pi * (x - z) - Real.pi * (x - y) := by ring
  have hs := Real.sin_sub (Real.pi * (x - z)) (Real.pi * (x - y))
  rw [← he] at hs
  unfold cosecantKernel cotangentKernel
  field_simp
  nlinarith

theorem cos_quartic_upper {x : ℝ} (hx : 0 ≤ x) :
    Real.cos x ≤ 1 - x ^ 2 / 2 + x ^ 4 / 24 := by
  let f : ℝ → ℝ := fun t => 1 - t ^ 2 / 2 + t ^ 4 / 24 - Real.cos t
  have hd (t : ℝ) : deriv f t = Real.sin t - t + t ^ 3 / 6 := by
    dsimp [f]
    simp (disch := fun_prop)
    ring
  have hm : MonotoneOn f (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0) (by fun_prop) (by fun_prop)
    intro t ht
    rw [hd]
    have ht0 : 0 ≤ t := (Set.mem_Ici.mp (interior_subset ht))
    have hs := Real.sin_ge_sub_cube ht0
    linarith
  have hh := hm (show 0 ∈ Set.Ici (0 : ℝ) by simp) hx hx
  simpa [f] using hh

theorem sine_cosecant_majorant {x : ℝ} (hx : 0 < x) (hxp : x ≤ Real.pi / 2) :
    1 / (Real.sin x) ^ 2 + 2 * |Real.cos x / (Real.sin x) ^ 2| ≤ 3 / x ^ 2 := by
  have hx2 : x < 2 := by linarith [Real.pi_lt_four]
  have hs : 0 < Real.sin x := Real.sin_pos_of_pos_of_lt_pi hx (by linarith [Real.pi_pos])
  have hc : 0 ≤ Real.cos x := Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hxp⟩
  have hxSq : x ^ 2 ≤ 4 := by nlinarith
  have hcube := mul_le_mul_of_nonneg_right hxSq hx.le
  have hl : 0 ≤ x - x ^ 3 / 6 := by nlinarith
  have hsin := Real.sin_ge_sub_cube hx.le
  have hsq := mul_self_le_mul_self hl hsin
  have hcos := mul_le_mul_of_nonneg_left (cos_quartic_upper hx.le) (sq_nonneg x)
  have hpoly : (1 + 2 * Real.cos x) * x ^ 2 ≤ 3 * (Real.sin x) ^ 2 := by nlinarith
  rw [abs_of_nonneg (div_nonneg hc (sq_nonneg _))]
  have he : 1 / (Real.sin x) ^ 2 + 2 * (Real.cos x / (Real.sin x) ^ 2) =
      (1 + 2 * Real.cos x) / (Real.sin x) ^ 2 := by ring
  rw [he]
  exact (div_le_div_iff₀ (sq_pos_of_pos hs) (sq_pos_of_pos hx)).mpr hpoly

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_CosecantDistanceBound
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The cosecant row weight depends only on distance to an integer -/

namespace Ostmann

 theorem cosecantRowWeight_eq (x y : ℝ) :
    cosecantKernel x y ^ 2 + 2 * |cosecantKernel x y * cotangentKernel x y| =
      cosecantRowWeight (x - y) := by
  unfold cosecantKernel cotangentKernel cosecantRowWeight
  congr 1
  · ring
  · congr 2
    ring

 theorem cosecantRowWeight_shift (t : ℝ) (m : ℤ) :
    cosecantRowWeight (t - m) = cosecantRowWeight t := by
  have he : Real.pi * (t - m) = Real.pi * t - (m : ℝ) * Real.pi := by ring
  have hs : |Real.sin (Real.pi * (t - m))| = |Real.sin (Real.pi * t)| := by
    rw [he, Real.sin_sub_int_mul_pi, abs_mul]
    simp
  have hc : |Real.cos (Real.pi * (t - m))| = |Real.cos (Real.pi * t)| := by
    rw [he, Real.cos_sub_int_mul_pi, abs_mul]
    simp
  have hs2 := congrArg (fun x : ℝ => x ^ 2) hs
  simp only [sq_abs] at hs2
  unfold cosecantRowWeight
  rw [hs2, abs_div, abs_div, hc]

 theorem cosecantRowWeight_abs (t : ℝ) : cosecantRowWeight |t| = cosecantRowWeight t := by
  by_cases ht : 0 ≤ t
  · rw [abs_of_nonneg ht]
  · rw [abs_of_neg (lt_of_not_ge ht)]
    simp [cosecantRowWeight, Real.sin_neg, Real.cos_neg]

 theorem cosecantRowWeight_bound (t d : ℝ) (m : ℤ)
    (hd : 0 < d) (hdhalf : d ≤ 1 / 2) (he : |t - m| = d) :
    cosecantRowWeight t ≤ 3 / (Real.pi ^ 2 * d ^ 2) := by
  rw [← cosecantRowWeight_shift t m, ← cosecantRowWeight_abs, he]
  have hp : 0 < Real.pi * d := mul_pos Real.pi_pos hd
  have hh : Real.pi * d ≤ Real.pi / 2 := by nlinarith [Real.pi_pos]
  have hb := sine_cosecant_majorant hp hh
  simpa only [cosecantRowWeight, mul_pow] using hb

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_SeparatedInverseSquares
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The one-sided inverse-square estimate for separated sample points -/

namespace Ostmann

open scoped BigOperators

 theorem ordered_separated_lower {n : ℕ} (x : Fin n → ℝ) (δ : ℝ)
    (hfirst : ∀ i, δ ≤ x i)
    (hgap : ∀ i j, i < j → δ ≤ x j - x i) :
    ∀ i, δ * (i.val + 1) ≤ x i := by
  have hi : ∀ k : ℕ, ∀ hk : k < n, δ * ((k : ℝ) + 1) ≤ x ⟨k, hk⟩ := by
    intro k
    induction k with
    | zero => intro hk; simpa using hfirst ⟨0, hk⟩
    | succ k ih =>
      intro hk
      have hp := ih (by omega)
      have hg := hgap ⟨k, by omega⟩ ⟨k + 1, hk⟩ (by simp)
      push_cast
      linarith
  intro i
  exact hi i.val i.isLt

 theorem finite_positive_inverse_squares (n : ℕ) :
    (∑ i : Fin n, 1 / ((i.val : ℝ) + 1) ^ 2) ≤ Real.pi ^ 2 / 6 := by
  have he : (∑ i : Fin n, 1 / ((i.val : ℝ) + 1) ^ 2) =
      ∑ j ∈ Finset.range (n + 1), 1 / (j : ℝ) ^ 2 := by
    rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => 1 / ((j : ℝ) + 1) ^ 2) n,
      Finset.sum_range_succ']
    simp
  rw [he, ← hasSum_zeta_two.tsum_eq]
  exact hasSum_zeta_two.summable.sum_le_tsum _ (fun j _ => by positivity)

 theorem ordered_separated_inverse_squares {n : ℕ} (x : Fin n → ℝ) (δ : ℝ)
    (hδ : 0 < δ) (hfirst : ∀ i, δ ≤ x i)
    (hgap : ∀ i j, i < j → δ ≤ x j - x i) :
    (∑ i, 1 / (x i) ^ 2) ≤ Real.pi ^ 2 / (6 * δ ^ 2) := by
  have hx := ordered_separated_lower x δ hfirst hgap
  have hb (i : Fin n) : 1 / (x i) ^ 2 ≤
      (δ ^ 2)⁻¹ * (1 / ((i.val : ℝ) + 1) ^ 2) := by
    have hi : 0 < (i.val : ℝ) + 1 := by positivity
    have hxi : 0 < x i := lt_of_lt_of_le hδ (hfirst i)
    have hs : (δ * ((i.val : ℝ) + 1)) ^ 2 ≤ (x i) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (hx i) 2
    calc
      _ ≤ 1 / (δ * ((i.val : ℝ) + 1)) ^ 2 := one_div_le_one_div_of_le (by positivity) hs
      _ = _ := by simp only [mul_pow, one_div, mul_inv]
  calc
    _ ≤ ∑ i : Fin n, (δ ^ 2)⁻¹ * (1 / ((i.val : ℝ) + 1) ^ 2) := Finset.sum_le_sum (fun i _ => hb i)
    _ = (δ ^ 2)⁻¹ * ∑ i : Fin n, 1 / ((i.val : ℝ) + 1) ^ 2 := (Finset.mul_sum _ _ _).symm
    _ ≤ (δ ^ 2)⁻¹ * (Real.pi ^ 2 / 6) :=
      mul_le_mul_of_nonneg_left (finite_positive_inverse_squares n) (by positivity)
    _ = _ := by ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_SeparatedSetSquares
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The inverse-square row sum for a finite separated set -/

namespace Ostmann

open scoped BigOperators

 theorem positive_set_inverse_squares (S : Finset ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hfirst : ∀ x ∈ S, δ ≤ x)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ ≤ |x - y|) :
    (∑ x ∈ S, 1 / x ^ 2) ≤ Real.pi ^ 2 / (6 * δ ^ 2) := by
  classical
  let e := S.orderEmbOfFin rfl
  have he (i : Fin S.card) : e i ∈ S := S.orderEmbOfFin_mem rfl i
  have hg (i j : Fin S.card) (hij : i < j) : δ ≤ e j - e i := by
    have hij' : e i < e j := e.strictMono hij
    have hh := hsep (e j) (he j) (e i) (he i) (ne_of_gt hij')
    rwa [abs_of_pos (sub_pos.mpr hij')] at hh
  have hh := ordered_separated_inverse_squares (fun i => e i) δ hδ
    (fun i => hfirst _ (he i)) hg
  have hs : (∑ x ∈ S, 1 / x ^ 2) = ∑ i : Fin S.card, 1 / (e i) ^ 2 := by
    conv_lhs => rw [← S.image_orderEmbOfFin_univ rfl]
    rw [Finset.sum_image]
    exact fun i _ j _ hij => e.injective hij
  rwa [hs]

 theorem separated_set_inverse_squares (S : Finset ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hfirst : ∀ x ∈ S, δ ≤ |x|)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ ≤ |x - y|) :
    (∑ x ∈ S, 1 / x ^ 2) ≤ Real.pi ^ 2 / (3 * δ ^ 2) := by
  classical
  let P := S.filter (fun x => 0 < x)
  let N := S.filter (fun x => ¬0 < x)
  let R := N.image (fun x => -x)
  have hP := positive_set_inverse_squares P δ hδ
    (fun x hx => by
      have h := Finset.mem_filter.mp hx
      simpa only [abs_of_pos h.2] using hfirst x h.1)
    (fun x hx y hy hxy => hsep x (Finset.mem_filter.mp hx).1 y (Finset.mem_filter.mp hy).1 hxy)
  have hRfirst (x : ℝ) (hx : x ∈ R) : δ ≤ x := by
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    have hy' := Finset.mem_filter.mp hy
    simpa only [abs_of_nonpos (le_of_not_gt hy'.2)] using hfirst y hy'.1
  have hRsep (x : ℝ) (hx : x ∈ R) (y : ℝ) (hy : y ∈ R) (hxy : x ≠ y) : δ ≤ |x - y| := by
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
    have hh := hsep a (Finset.mem_filter.mp ha).1 b (Finset.mem_filter.mp hb).1
      (fun hab => hxy (congrArg Neg.neg hab))
    simpa only [neg_sub_neg, abs_sub_comm] using hh
  have hR := positive_set_inverse_squares R δ hδ hRfirst hRsep
  have hsum : (∑ x ∈ P, 1 / x ^ 2) + (∑ x ∈ N, 1 / x ^ 2) = ∑ x ∈ S, 1 / x ^ 2 :=
    Finset.sum_filter_add_sum_filter_not _ _ _
  have he : (∑ x ∈ R, 1 / x ^ 2) = ∑ x ∈ N, 1 / x ^ 2 := by
    rw [Finset.sum_image]
    · simp
    · exact fun _ _ _ _ hab => neg_injective hab
  rw [he] at hR
  rw [← hsum]
  have hid : Real.pi ^ 2 / (3 * δ ^ 2) = 2 * (Real.pi ^ 2 / (6 * δ ^ 2)) := by ring
  rw [hid]
  linarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_CircleSeparatedPoints
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Centering a separated finite family on the circle -/

namespace Ostmann

open scoped BigOperators

 theorem centeredCircleRemainder_bounds (t : ℝ) :
    -(1 / 2) ≤ centeredCircleRemainder t ∧ centeredCircleRemainder t < 1 / 2 := by
  have hl := Int.floor_le (t + 1 / 2)
  have hu := Int.lt_floor_add_one (t + 1 / 2)
  dsimp [centeredCircleRemainder]
  constructor <;> linarith

 theorem circleSeparated_sine_ne_zero {ι : Type*} (x : ι → ℝ) (δ : ℝ)
    (hδ : 0 < δ) (hx : CircleSeparated x δ) {s t : ι} (hst : s ≠ t) :
    Real.sin (Real.pi * (x s - x t)) ≠ 0 := by
  intro hz
  obtain ⟨m, hm⟩ := Real.sin_eq_zero_iff.mp hz
  have he : x s - x t - (m : ℝ) = 0 := by nlinarith [Real.pi_pos]
  have hh := hx s t hst m
  rw [he, abs_zero] at hh
  linarith

 theorem circleSeparated_remainders {ι : Type*} (x : ι → ℝ) (δ : ℝ)
    (hx : CircleSeparated x δ) (center s t : ι) (hst : s ≠ t) :
    δ ≤ |centeredCircleRemainder (x s - x center) -
      centeredCircleRemainder (x t - x center)| := by
  have hh := hx s t hst (⌊x s - x center + 1 / 2⌋ - ⌊x t - x center + 1 / 2⌋)
  push_cast at hh
  convert hh using 1 <;> first | (with_reducible_and_instances rfl) | (congr 1; dsimp [centeredCircleRemainder]; ring)

 theorem circleSeparated_inverse_square_row {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → ℝ) (δ : ℝ) (hδ : 0 < δ) (hx : CircleSeparated x δ) (center : ι) :
    (∑ s ∈ Finset.univ.erase center,
      1 / centeredCircleRemainder (x s - x center) ^ 2) ≤ Real.pi ^ 2 / (3 * δ ^ 2) := by
  classical
  let F := Finset.univ.erase center
  let r := fun s => centeredCircleRemainder (x s - x center)
  let S := F.image r
  have hfirst (s : ι) (hs : s ∈ F) : δ ≤ |r s| :=
    hx s center (Finset.mem_erase.mp hs).1 ⌊x s - x center + 1 / 2⌋
  have hinj : Set.InjOn r F := by
    intro s hs t ht he
    by_contra hst
    have hb := circleSeparated_remainders x δ hx center s t hst
    change δ ≤ |r s - r t| at hb
    rw [he, sub_self, abs_zero] at hb
    linarith
  have hb := separated_set_inverse_squares S δ hδ (by
    intro y hy
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hy
    exact hfirst s hs) (by
    intro y hy z hz hyz
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hz
    exact circleSeparated_remainders x δ hx center s t (fun hst => hyz (congrArg r hst)))
  have he : (∑ y ∈ S, 1 / y ^ 2) = ∑ s ∈ F, 1 / (r s) ^ 2 := by
    exact Finset.sum_image hinj
  rwa [he] at hb

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_ReducedFractionSeparation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact circle separation of reduced fractions -/

namespace Ostmann

 theorem reduced_fraction_cross_injective (q r h k : ℕ) (hq : 0 < q)
    (_hr : 0 < r) (hc : h.Coprime q) (kc : k.Coprime r) (he : h * r = k * q) :
    q = r ∧ h = k := by
  have hqr : q ∣ r := hc.symm.dvd_mul_left.mp (by rw [he]; exact dvd_mul_left q k)
  have hrq : r ∣ q := kc.symm.dvd_mul_left.mp (by rw [← he]; exact dvd_mul_left r h)
  have hqeq : q = r := Nat.dvd_antisymm hqr hrq
  refine ⟨hqeq, ?_⟩
  subst r
  exact Nat.eq_of_mul_eq_mul_right hq (by simpa only [mul_comm] using he)

 theorem reduced_fraction_circle_separation (Q q r h k : ℕ)
    (hq : 0 < q) (hr : 0 < r) (hqQ : q ≤ Q) (hrQ : r ≤ Q)
    (hh : h < q) (hk : k < r) (hc : h.Coprime q) (kc : k.Coprime r)
    (hne : (q, h) ≠ (r, k)) (m : ℤ) :
    1 / (Q : ℝ) ^ 2 ≤ |(h : ℝ) / q - (k : ℝ) / r - m| := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hQR : (0 : ℝ) < Q := lt_of_lt_of_le hqR (by exact_mod_cast hqQ)
  let t : ℝ := (h : ℝ) / q - (k : ℝ) / r - m
  have ht : t ≠ 0 := by
    intro ht0
    have hhlo : 0 ≤ (h : ℝ) / q := by positivity
    have hklo : 0 ≤ (k : ℝ) / r := by positivity
    have hhhi : (h : ℝ) / q < 1 := (div_lt_one hqR).mpr (by exact_mod_cast hh)
    have hkhi : (k : ℝ) / r < 1 := (div_lt_one hrR).mpr (by exact_mod_cast hk)
    have hmlo : (-1 : ℝ) < m := by dsimp [t] at ht0; linarith
    have hmhi : (m : ℝ) < 1 := by dsimp [t] at ht0; linarith
    have hm : m = 0 := by
      have hlo : (-1 : ℤ) < m := by exact_mod_cast hmlo
      have hhi : m < (1 : ℤ) := by exact_mod_cast hmhi
      omega
    have heR : (h : ℝ) * r = (k : ℝ) * q := by
      dsimp [t] at ht0
      rw [hm, Int.cast_zero, sub_zero, sub_eq_zero] at ht0
      exact (div_eq_div_iff hqR.ne' hrR.ne').mp ht0
    have heN : h * r = k * q := by exact_mod_cast heR
    obtain ⟨hqr, hhk⟩ := reduced_fraction_cross_injective q r h k hq hr hc kc heN
    exact hne (Prod.ext hqr hhk)
  let N : ℤ := (h : ℤ) * r - (k : ℤ) * q - m * q * r
  have hN : (N : ℝ) = (q : ℝ) * r * t := by
    dsimp [N, t]
    push_cast
    field_simp
  have hN0 : N ≠ 0 := by
    intro hzero
    rw [hzero, Int.cast_zero] at hN
    exact ht ((mul_eq_zero.mp hN.symm).resolve_left (mul_ne_zero hqR.ne' hrR.ne'))
  have hN1 : (1 : ℤ) ≤ |N| := Int.one_le_abs hN0
  have hN1R : (1 : ℝ) ≤ |(N : ℝ)| := by exact_mod_cast hN1
  rw [hN, abs_mul, abs_mul, abs_of_pos hqR, abs_of_pos hrR] at hN1R
  have hprod : (q : ℝ) * r ≤ (Q : ℝ) ^ 2 := by
    have hqQ' : (q : ℝ) ≤ Q := by exact_mod_cast hqQ
    have hrQ' : (r : ℝ) ≤ Q := by exact_mod_cast hrQ
    nlinarith
  have hhprod := mul_le_mul_of_nonneg_right hprod (abs_nonneg t)
  change 1 / (Q : ℝ) ^ 2 ≤ |t|
  apply (div_le_iff₀ (sq_pos_of_pos hQR)).mpr
  nlinarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_CosecantRowSum
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The sharp row budget for the cosecant matrix -/

namespace Ostmann

open scoped BigOperators

 theorem cosecant_row_sum_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → ℝ) (δ : ℝ) (hδ : 0 < δ) (hx : CircleSeparated x δ) (center : ι) :
    (∑ s, cosecantKernel (x s) (x center) ^ 2) +
        2 * ∑ s, |cosecantKernel (x center) (x s) * cotangentKernel (x center) (x s)| ≤
      1 / δ ^ 2 := by
  classical
  let F := Finset.univ.erase center
  let r := fun s => centeredCircleRemainder (x s - x center)
  have he (s : ι) : cosecantKernel (x center) (x s) * cotangentKernel (x center) (x s) =
      cosecantKernel (x s) (x center) * cotangentKernel (x s) (x center) := by
    rw [cosecantKernel_skew (x center) (x s), cotangentKernel_skew (x center) (x s)]
    ring
  have hsum : (∑ s, cosecantKernel (x s) (x center) ^ 2) +
      2 * ∑ s, |cosecantKernel (x center) (x s) * cotangentKernel (x center) (x s)| =
        ∑ s ∈ F, cosecantRowWeight (x s - x center) := by
    simp_rw [he]
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    simp_rw [cosecantRowWeight_eq]
    apply (Finset.sum_erase_add _ _ (Finset.mem_univ center)).symm.trans ?_
    simp [cosecantRowWeight, F]
  have hb (s : ι) (hs : s ∈ F) :
      cosecantRowWeight (x s - x center) ≤ 3 / (Real.pi ^ 2 * (r s) ^ 2) := by
    have hd := hx s center (Finset.mem_erase.mp hs).1 ⌊x s - x center + 1 / 2⌋
    change δ ≤ |r s| at hd
    have hhalf : |r s| ≤ 1 / 2 := abs_le.mpr
      ⟨(centeredCircleRemainder_bounds _).1, (centeredCircleRemainder_bounds _).2.le⟩
    have hh := cosecantRowWeight_bound (x s - x center) |r s|
      ⌊x s - x center + 1 / 2⌋ (lt_of_lt_of_le hδ hd) hhalf rfl
    simpa only [sq_abs] using hh
  rw [hsum]
  calc
    _ ≤ ∑ s ∈ F, 3 / (Real.pi ^ 2 * (r s) ^ 2) := Finset.sum_le_sum hb
    _ = (3 / Real.pi ^ 2) * ∑ s ∈ F, 1 / (r s) ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      ring
    _ ≤ (3 / Real.pi ^ 2) * (Real.pi ^ 2 / (3 * δ ^ 2)) :=
      mul_le_mul_of_nonneg_left (circleSeparated_inverse_square_row x δ hδ hx center) (by positivity)
    _ = _ := by field_simp

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_HermitianNormBound
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Passing a finite Hermitian eigenvalue bound to its quadratic form -/

namespace Ostmann

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

 theorem hermitian_norm_bound {A : Matrix ι ι ℂ} (hA : A.IsHermitian)
    (B : ℝ) (hB : 0 ≤ B) (heig : ∀ i, |hA.eigenvalues i| ≤ B) : ‖A‖ ≤ B := by
  rw [hA.spectral_theorem, Unitary.conjStarAlgAut_apply, ← Unitary.coe_star,
    CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul, Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg hB).mpr
  intro i
  simpa only [Function.comp_apply, RCLike.ofReal_eq_complex_ofReal, Complex.norm_real,
    Real.norm_eq_abs] using heig i

 theorem matrix_quadratic_norm_bound (A : Matrix ι ι ℂ) (B : ℝ)
    (hB : ‖A‖ ≤ B) (u : ι → ℂ) :
    ‖star u ⬝ᵥ (A *ᵥ u)‖ ≤ B * ∑ i, ‖u i‖ ^ 2 := by
  let v : EuclideanSpace ℂ ι := (EuclideanSpace.equiv ι ℂ).symm u
  let w : EuclideanSpace ℂ ι := (EuclideanSpace.equiv ι ℂ).symm (A *ᵥ u)
  have hinner : inner ℂ v w = star u ⬝ᵥ (A *ᵥ u) := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    exact dotProduct_comm _ _
  have hv : ‖v‖ ^ 2 = ∑ i, ‖u i‖ ^ 2 := EuclideanSpace.norm_sq_eq v
  have hw : ‖w‖ ≤ B * ‖v‖ := (Matrix.l2_opNorm_mulVec A v).trans
    (mul_le_mul_of_nonneg_right hB (norm_nonneg v))
  rw [← hinner]
  calc
    _ ≤ ‖v‖ * ‖w‖ := norm_inner_le_norm _ _
    _ ≤ ‖v‖ * (B * ‖v‖) := mul_le_mul_of_nonneg_left hw (norm_nonneg v)
    _ = B * ∑ i, ‖u i‖ ^ 2 := by rw [← hv]; ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_CosecantHilbertBound
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Montgomery--Vaughan's finite unweighted Hilbert inequality

This is Theorem 1, inequality (1.2), of Montgomery--Vaughan (1974).
It is derived from the checked finite kernel cancellation and row estimate.
-/

namespace Ostmann

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
 theorem cosecantMatrix_hermitian (x : ι → ℝ) : (cosecantMatrix x).IsHermitian :=
  imaginaryKernelMatrix_hermitian _ (fun _ _ => cosecantKernel_skew _ _)

 theorem cosecant_eigenvalue_bound (x : ι → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hx : CircleSeparated x δ) (μ : ℝ) (u : ι → ℂ)
    (hu : 0 < ∑ s, ‖u s‖ ^ 2) (heig : cosecantMatrix x *ᵥ u = (μ : ℂ) • u) :
    μ ^ 2 ≤ 1 / δ ^ 2 := by
  exact kernel_eigenvalue_bound
    (fun s t => cosecantKernel (x s) (x t))
    (fun s t => cotangentKernel (x s) (x t))
    (fun _ => cosecantKernel_self _) (fun _ => cotangentKernel_self _)
    (fun _ _ => cosecantKernel_skew _ _) (fun _ _ => cotangentKernel_skew _ _)
    (fun r s t hrs hrt hst => cosecantKernel_triple _ _ _
      (circleSeparated_sine_ne_zero x δ hδ hx hrs)
      (circleSeparated_sine_ne_zero x δ hδ hx hrt)
      (circleSeparated_sine_ne_zero x δ hδ hx hst))
    (1 / δ ^ 2) μ (cosecant_row_sum_bound x δ hδ hx) u hu heig

 theorem cosecantMatrix_norm_bound (x : ι → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hx : CircleSeparated x δ) : ‖cosecantMatrix x‖ ≤ 1 / δ := by
  apply hermitian_norm_bound (cosecantMatrix_hermitian x) (1 / δ) (by positivity)
  intro i
  let hA := cosecantMatrix_hermitian x
  have hnorm : ‖hA.eigenvectorBasis i‖ = 1 := hA.eigenvectorBasis.orthonormal.1 i
  have hu : 0 < ∑ s, ‖(hA.eigenvectorBasis i) s‖ ^ 2 := by
    rw [← EuclideanSpace.norm_sq_eq, hnorm]
    norm_num
  have hb := cosecant_eigenvalue_bound x δ hδ hx (hA.eigenvalues i)
    (hA.eigenvectorBasis i) hu (hA.mulVec_eigenvectorBasis i)
  have hinv : 0 < 1 / δ := by positivity
  have heq : 1 / δ ^ 2 = (1 / δ) ^ 2 := by ring
  rw [heq] at hb
  nlinarith [sq_abs (hA.eigenvalues i), abs_nonneg (hA.eigenvalues i)]

 theorem cosecant_hilbert_bound (x : ι → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hx : CircleSeparated x δ) (u : ι → ℂ) :
    ‖∑ s, ∑ t, star (u s) * (cosecantKernel (x s) (x t) : ℂ) * u t‖ ≤
      (1 / δ) * ∑ s, ‖u s‖ ^ 2 := by
  have hb := matrix_quadratic_norm_bound (cosecantMatrix x) (1 / δ)
    (cosecantMatrix_norm_bound x δ hδ hx) u
  have he : star u ⬝ᵥ (cosecantMatrix x *ᵥ u) =
      Complex.I * (∑ s, ∑ t, star (u s) * (cosecantKernel (x s) (x t) : ℂ) * u t) := by
    simp only [dotProduct, mulVec, Pi.star_apply, cosecantMatrix, imaginaryKernelMatrix,
      Matrix.of_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro t _
    ring
  rw [he, norm_mul, Complex.norm_I, one_mul] at hb
  exact hb

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_SieveGeometricKernel
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact finite exponential kernel for the additive large sieve -/

namespace Ostmann

open scoped BigOperators

 theorem sieveHalfPhase_add (s t : ℝ) :
    sieveHalfPhase (s + t) = sieveHalfPhase s * sieveHalfPhase t := by
  simp only [sieveHalfPhase, mul_add, Complex.ofReal_add, add_mul, Complex.exp_add]

 theorem sieveHalfPhase_sine (t : ℝ) :
    (2 : ℂ) * Complex.I * (Real.sin (Real.pi * t) : ℂ) =
      sieveHalfPhase t - sieveHalfPhase (-t) := by
  unfold sieveHalfPhase
  rw [Complex.exp_ofReal_mul_I, Complex.exp_ofReal_mul_I]
  simp only [mul_neg, Real.cos_neg, Real.sin_neg, Complex.ofReal_neg]
  ring

 theorem sieveHalfPhase_two_step (s t : ℝ) :
    ((2 : ℂ) * Complex.I * (Real.sin (Real.pi * t) : ℂ)) * sieveHalfPhase s =
      sieveHalfPhase (s + t) - sieveHalfPhase (s - t) := by
  rw [sieveHalfPhase_sine, sieveHalfPhase_add, sub_eq_add_neg s t, sieveHalfPhase_add]
  ring

 theorem sieve_geometric_kernel_mul (M : ℕ) (J t : ℝ) :
    ((2 : ℂ) * Complex.I * (Real.sin (Real.pi * t) : ℂ)) *
      (∑ n ∈ Finset.range M, sieveHalfPhase (2 * (J + (n : ℝ)) * t)) =
        sieveHalfPhase ((2 * (J + M) - 1) * t) - sieveHalfPhase ((2 * J - 1) * t) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    have hs := sieveHalfPhase_two_step (2 * (J + M) * t) t
    rw [show 2 * (J + (M : ℝ)) * t + t = (2 * (J + (M + 1 : ℕ)) - 1) * t by
      push_cast; ring,
      show 2 * (J + (M : ℝ)) * t - t = (2 * (J + M) - 1) * t by ring] at hs
    rw [hs]
    ring

 theorem sieve_geometric_kernel (M : ℕ) (J t : ℝ)
    (ht : Real.sin (Real.pi * t) ≠ 0) :
    (∑ n ∈ Finset.range M, sieveHalfPhase (2 * (J + (n : ℝ)) * t)) =
      ((sieveHalfPhase ((2 * (J + M) - 1) * t) - sieveHalfPhase ((2 * J - 1) * t)) /
        ((2 : ℂ) * Complex.I)) * (Real.sin (Real.pi * t) : ℂ)⁻¹ := by
  have hs := sieve_geometric_kernel_mul M J t
  have htC : (Real.sin (Real.pi * t) : ℂ) ≠ 0 := by exact_mod_cast ht
  have hfactor : (2 : ℂ) * Complex.I ≠ 0 := mul_ne_zero (by norm_num) Complex.I_ne_zero
  apply (mul_left_cancel₀ (mul_ne_zero hfactor htC))
  rw [hs, div_eq_mul_inv]
  symm
  calc
    _ = (((2 : ℂ) * Complex.I) * ((2 : ℂ) * Complex.I)⁻¹) *
        ((Real.sin (Real.pi * t) : ℂ) * (Real.sin (Real.pi * t) : ℂ)⁻¹) *
          (sieveHalfPhase ((2 * (J + M) - 1) * t) - sieveHalfPhase ((2 * J - 1) * t)) := by ring
    _ = _ := by rw [mul_inv_cancel₀ hfactor, mul_inv_cancel₀ htC]; ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_SievePhaseGram
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact finite Gram expansion of the large-sieve phase matrix -/

namespace Ostmann

open scoped BigOperators

 theorem sieveHalfPhase_star (t : ℝ) : star (sieveHalfPhase t) = sieveHalfPhase (-t) := by
  unfold sieveHalfPhase
  rw [Complex.exp_ofReal_mul_I, Complex.exp_ofReal_mul_I]
  simp only [mul_neg, Real.cos_neg, Real.sin_neg, Complex.ofReal_neg,
    star_add, star_mul, Complex.star_def, Complex.conj_ofReal, Complex.conj_I]
  ring

 theorem sieveHalfPhase_difference (s t : ℝ) :
    sieveHalfPhase s * star (sieveHalfPhase t) = sieveHalfPhase (s - t) := by
  rw [sieveHalfPhase_star, ← sieveHalfPhase_add, sub_eq_add_neg]

 theorem finite_complex_norm_expansion {ι : Type*} [Fintype ι] (f : ι → ℂ) :
    ((‖∑ s, f s‖ ^ 2 : ℝ) : ℂ) = ∑ s, ∑ t, f s * star (f t) := by
  rw [Complex.ofReal_pow, ← Complex.mul_conj']
  simp only [← Complex.star_def, star_sum, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_comm

 theorem sieve_phase_gram {ι : Type*} [Fintype ι] (x : ι → ℝ) (b : ι → ℂ)
    (M : ℕ) (J : ℝ) :
    ((∑ n ∈ Finset.range M, ‖∑ s, b s * sieveHalfPhase (2 * (J + (n : ℝ)) * x s)‖ ^ 2 : ℝ) : ℂ) =
      ∑ s, ∑ t, b s * star (b t) *
        ∑ n ∈ Finset.range M, sieveHalfPhase (2 * (J + (n : ℝ)) * (x s - x t)) := by
  simp only [Complex.ofReal_sum, finite_complex_norm_expansion]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  rw [star_mul]
  rw [show 2 * (J + (n : ℝ)) * (x s - x t) =
    2 * (J + (n : ℝ)) * x s - 2 * (J + (n : ℝ)) * x t by ring,
    ← sieveHalfPhase_difference]
  ring

 theorem twisted_cosecant_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → ℝ) (δ : ℝ) (hδ : 0 < δ) (hx : CircleSeparated x δ)
    (b : ι → ℂ) (L : ℝ) :
    ‖∑ s, ∑ t, b s * star (b t) * sieveHalfPhase (L * (x s - x t)) *
      (cosecantKernel (x s) (x t) : ℂ)‖ ≤ (1 / δ) * ∑ s, ‖b s‖ ^ 2 := by
  let u := fun s => star (b s * sieveHalfPhase (L * x s))
  have he : (∑ s, ∑ t, b s * star (b t) * sieveHalfPhase (L * (x s - x t)) *
      (cosecantKernel (x s) (x t) : ℂ)) =
      ∑ s, ∑ t, star (u s) * (cosecantKernel (x s) (x t) : ℂ) * u t := by
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro t _
    simp only [u, star_star, star_mul]
    rw [show L * (x s - x t) = L * x s - L * x t by ring,
      ← sieveHalfPhase_difference]
    ring
  rw [he]
  have hb := cosecant_hilbert_bound x δ hδ hx u
  simpa only [u, norm_star, norm_mul, sieveHalfPhase_norm, mul_one] using hb

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_SieveDualEnergy
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The sharp dual large-sieve estimate from the finite Hilbert inequality -/

namespace Ostmann

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
 theorem sieve_pair_kernel (x : ι → ℝ) (δ : ℝ) (hδ : 0 < δ) (hx : CircleSeparated x δ)
    (M : ℕ) (J : ℝ) (s t : ι) :
    (∑ n ∈ Finset.range M, sieveHalfPhase (2 * (J + (n : ℝ)) * (x s - x t))) =
      (if s = t then (M : ℂ) else 0) +
        ((sieveHalfPhase ((2 * (J + M) - 1) * (x s - x t)) -
          sieveHalfPhase ((2 * J - 1) * (x s - x t))) / ((2 : ℂ) * Complex.I)) *
          (cosecantKernel (x s) (x t) : ℂ) := by
  by_cases hst : s = t
  · subst t
    simp
  · rw [ite_eq_right hst, zero_add]
    simpa only [cosecantKernel, Complex.ofReal_inv] using
      sieve_geometric_kernel M J (x s - x t) (circleSeparated_sine_ne_zero x δ hδ hx hst)

 theorem sieve_dual_energy_identity (x : ι → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hx : CircleSeparated x δ) (b : ι → ℂ) (M : ℕ) (J : ℝ) :
    ((∑ n ∈ Finset.range M, ‖∑ s, b s * sieveHalfPhase (2 * (J + (n : ℝ)) * x s)‖ ^ 2 : ℝ) : ℂ) =
      ((M : ℝ) * ∑ s, ‖b s‖ ^ 2 : ℝ) +
        ((2 : ℂ) * Complex.I)⁻¹ *
          (twistedCosecantSum x b (2 * (J + M) - 1) - twistedCosecantSum x b (2 * J - 1)) := by
  rw [sieve_phase_gram]
  simp_rw [sieve_pair_kernel x δ hδ hx M J]
  have he (s t : ι) : b s * star (b t) *
      ((if s = t then (M : ℂ) else 0) +
        ((sieveHalfPhase ((2 * (J + M) - 1) * (x s - x t)) -
          sieveHalfPhase ((2 * J - 1) * (x s - x t))) / ((2 : ℂ) * Complex.I)) *
          (cosecantKernel (x s) (x t) : ℂ)) =
      (if s = t then (M : ℂ) * ((‖b s‖ ^ 2 : ℝ) : ℂ) else 0) +
        ((2 : ℂ) * Complex.I)⁻¹ *
          (b s * star (b t) * sieveHalfPhase ((2 * (J + M) - 1) * (x s - x t)) *
              (cosecantKernel (x s) (x t) : ℂ) -
            b s * star (b t) * sieveHalfPhase ((2 * J - 1) * (x s - x t)) *
              (cosecantKernel (x s) (x t) : ℂ)) := by
    by_cases hst : s = t
    · subst t
      simp only [↓reduceIte, sub_self, mul_zero, sieveHalfPhase_zero,
        cosecantKernel_self, Complex.ofReal_zero, mul_one, add_zero]
      rw [Complex.ofReal_pow, ← Complex.mul_conj', ← Complex.star_def]
      ring
    · simp only [hst, ↓reduceIte, zero_add, div_eq_mul_inv]
      ring
  simp_rw [he]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, ← Finset.mul_sum,
    Complex.ofReal_sum, Complex.ofReal_natCast, Complex.ofReal_mul, twistedCosecantSum]

 theorem sieve_dual_energy_bound (x : ι → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hx : CircleSeparated x δ) (b : ι → ℂ) (M : ℕ) (J : ℝ) :
    (∑ n ∈ Finset.range M, ‖∑ s, b s * sieveHalfPhase (2 * (J + (n : ℝ)) * x s)‖ ^ 2) ≤
      ((M : ℝ) + 1 / δ) * ∑ s, ‖b s‖ ^ 2 := by
  have hi := sieve_dual_energy_identity x δ hδ hx b M J
  have htop := twisted_cosecant_bound x δ hδ hx b (2 * (J + M) - 1)
  have hbottom := twisted_cosecant_bound x δ hδ hx b (2 * J - 1)
  change ‖twistedCosecantSum x b (2 * (J + M) - 1)‖ ≤ _ at htop
  change ‖twistedCosecantSum x b (2 * J - 1)‖ ≤ _ at hbottom
  have htri := norm_add_le (((M : ℝ) * ∑ s, ‖b s‖ ^ 2 : ℝ) : ℂ)
    (((2 : ℂ) * Complex.I)⁻¹ *
      (twistedCosecantSum x b (2 * (J + M) - 1) - twistedCosecantSum x b (2 * J - 1)))
  have hdiff := norm_sub_le (twistedCosecantSum x b (2 * (J + M) - 1))
    (twistedCosecantSum x b (2 * J - 1))
  rw [← hi] at htri
  have hE : 0 ≤ ∑ s, ‖b s‖ ^ 2 := Finset.sum_nonneg (fun s _ => sq_nonneg _)
  have hN : 0 ≤ ∑ n ∈ Finset.range M,
      ‖∑ s, b s * sieveHalfPhase (2 * (J + (n : ℝ)) * x s)‖ ^ 2 :=
    Finset.sum_nonneg (fun n _ => sq_nonneg _)
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hN,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Nat.cast_nonneg M) hE),
    norm_mul, norm_inv, norm_mul, Complex.norm_ofNat, Complex.norm_I] at htri
  norm_num at htri
  nlinarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_SeparatedAdditiveSieve
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The finite additive sieve for circle-separated frequencies -/

namespace Ostmann

open Matrix
open scoped BigOperators

 theorem sievePhaseMatrix_adjoint {ι : Type*} [Fintype ι] (x : ι → ℝ)
    (M : ℕ) (J : ℝ) (b : ι → ℂ) (n : Fin M) :
    ((sievePhaseMatrix x M J)ᴴ *ᵥ b) n =
      star (∑ s, star (b s) * sieveHalfPhase (2 * (J + (n.val : ℝ)) * x s)) := by
  simp only [mulVec, dotProduct, conjTranspose_apply, sievePhaseMatrix, Matrix.of_apply,
    star_sum, star_mul, star_star]

 theorem separated_additive_sieve {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → ℝ) (δ : ℝ) (hδ : 0 < δ) (hx : CircleSeparated x δ)
    (M : ℕ) (J : ℝ) (c : Fin M → ℂ) :
    (∑ s, ‖∑ n, c n * sieveHalfPhase (2 * (J + (n.val : ℝ)) * x s)‖ ^ 2) ≤
      ((M : ℝ) + 1 / δ) * ∑ n, ‖c n‖ ^ 2 := by
  have hdual (b : ι → ℂ) :
      (∑ n, ‖((sievePhaseMatrix x M J)ᴴ *ᵥ b) n‖ ^ 2) ≤
        ((M : ℝ) + 1 / δ) * ∑ s, ‖b s‖ ^ 2 := by
    simp only [sievePhaseMatrix_adjoint, norm_star]
    have hb := sieve_dual_energy_bound x δ hδ hx (fun s => star (b s)) M J
    rw [← Fin.sum_univ_eq_sum_range] at hb
    simpa only [norm_star] using hb
  have hK : 0 ≤ (M : ℝ) + 1 / δ := by positivity
  have h := finite_matrix_duality (sievePhaseMatrix x M J) ((M : ℝ) + 1 / δ) hK hdual c
  simpa only [mulVec, dotProduct, sievePhaseMatrix, Matrix.of_apply, mul_comm] using h

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_AdditiveSieveProof
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The published additive large sieve, with its precise downstream constant

The finite cosecant Hilbert inequality and duality prove the separated-frequency
estimate. Reduced fractions of denominator at most Q are 1/Q²-separated.
This proves the specialization of Montgomery--Vaughan (1973), Theorem 1,
used throughout the conditional development.
-/

namespace Ostmann

open scoped BigOperators

 theorem reducedFractionPoint_separated (Q : ℕ) :
    CircleSeparated (reducedFractionPoint Q) (1 / (Q : ℝ) ^ 2) := by
  intro s t hst m
  rcases s with ⟨⟨q, hq⟩, ⟨h, hh⟩⟩
  rcases t with ⟨⟨r, hr⟩, ⟨k, hk⟩⟩
  simp only [Finset.mem_Icc] at hq hr
  simp only [reducedNumerators, Finset.mem_filter, Finset.mem_range] at hh hk
  have hne : (q, h) ≠ (r, k) := by
    intro he
    have hqr := congrArg Prod.fst he
    have hhk := congrArg Prod.snd he
    dsimp at hqr hhk
    subst r
    subst k
    exact hst rfl
  exact reduced_fraction_circle_separation Q q r h k (by omega) (by omega)
    hq.2 hr.2 hh.1 hk.1 hh.2 hk.2 hne m

 theorem sieveAdditivePhase_eq_half (q h : ℕ) (J : ℤ) (n : ℕ) :
    sieveAdditivePhase q h (J + (n : ℤ)) =
      sieveHalfPhase (2 * ((J : ℝ) + (n : ℝ)) * ((h : ℝ) / q)) := by
  unfold sieveAdditivePhase sieveHalfPhase
  congr 1
  push_cast
  ring

 theorem reducedFraction_sum (Q : ℕ) (f : ℕ → ℕ → ℝ) :
    (∑ s : ReducedFractionIndex Q, f s.1.val s.2.val) =
      ∑ q ∈ Finset.Icc 1 Q, ∑ h ∈ reducedNumerators q, f q h := by
  rw [Fintype.sum_sigma]
  change (∑ q : Finset.Icc 1 Q, ∑ h : reducedNumerators q.val, f q.val h.val) = _
  simp_rw [Finset.sum_coe_sort]
  exact Finset.sum_coe_sort (Finset.Icc 1 Q)
    (fun q : ℕ => ∑ h ∈ reducedNumerators q, f q h)

 theorem publishedAdditiveLargeSieve : PublishedAdditiveLargeSieve := by
  classical
  intro M Q _hM hQ J c
  have hQpos : (0 : ℝ) < Q := by exact_mod_cast (show 0 < Q by omega)
  have hδ : 0 < 1 / (Q : ℝ) ^ 2 := by positivity
  have h := separated_additive_sieve (reducedFractionPoint Q) (1 / (Q : ℝ) ^ 2)
    hδ (reducedFractionPoint_separated Q) M (J : ℝ) c
  have hconst : 1 / (1 / (Q : ℝ) ^ 2) = (Q : ℝ) ^ 2 := by field_simp
  rw [hconst] at h
  change (∑ s : ReducedFractionIndex Q,
    ‖∑ n, c n * sieveHalfPhase (2 * ((J : ℝ) + (n.val : ℝ)) *
      ((s.2.val : ℝ) / s.1.val))‖ ^ 2) ≤ _ at h
  rw [reducedFraction_sum Q (fun q h =>
    ‖∑ n, c n * sieveHalfPhase (2 * ((J : ℝ) + (n.val : ℝ)) *
      ((h : ℝ) / q))‖ ^ 2)] at h
  simpa only [additiveSieveSum, sieveAdditivePhase_eq_half] using h

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_MultiplicativeSieveProof
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite multiplicative large sieve for the complex-zero density argument

Summing the full character Parseval identity before discarding imprimitive
characters retains the conductor saving in the Gauss normalization.
-/

namespace Ostmann

open scoped BigOperators ComplexConjugate

 theorem primitive_multiplicative_large_sieve (M Q : ℕ) (hM : 1 ≤ M) (hQ : 1 ≤ Q)
    (J : ℤ) (c : Fin M → ℂ)
    (S : (q : ℕ) → Finset (DirichletCharacter ℂ q))
    (hS : ∀ q ∈ Finset.Icc 1 Q, ∀ χ ∈ S q, χ.IsPrimitive) :
    (∑ q ∈ Finset.Icc 1 Q, ∑ χ ∈ S q,
      ‖∑ n, c n * χ ((J + (n.val : ℤ) : ℤ) : ZMod q)‖ ^ 2) ≤
      ((M : ℝ) + (Q : ℝ) ^ 2) * ∑ n, ‖c n‖ ^ 2 := by
  classical
  have hpoint (q : ℕ) (hq : q ∈ Finset.Icc 1 Q) :
      (∑ χ ∈ S q, ‖∑ n, c n * χ ((J + (n.val : ℤ) : ℤ) : ZMod q)‖ ^ 2) ≤
        ∑ h ∈ reducedNumerators q, ‖additiveSieveSum (fun n => star (c n)) J q h‖ ^ 2 := by
    have hqpos : 0 < q := (Finset.mem_Icc.mp hq).1
    let : NeZero q := ⟨ne_of_gt hqpos⟩
    have h := primitive_character_energy_le (S q) (hS q hq) c
      (fun n => ((J + (n.val : ℤ) : ℤ) : ZMod q))
    rw [sum_reducedNumerators_eq_units]
    simpa only [additiveSieveSum, sieveAdditivePhase_eq_stdAddChar,
      ZMod.natCast_zmod_val] using h
  calc
    _ ≤ ∑ q ∈ Finset.Icc 1 Q, ∑ h ∈ reducedNumerators q,
        ‖additiveSieveSum (fun n => star (c n)) J q h‖ ^ 2 :=
      Finset.sum_le_sum hpoint
    _ ≤ _ := by
      simpa only [norm_star] using
        publishedAdditiveLargeSieve M Q hM hQ J (fun n => star (c n))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_FiniteIntervalPacking
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Packing an arbitrary finite support into its actual integer interval -/

namespace Ostmann

open scoped BigOperators Classical

 theorem finite_interval_sum {A : Type*} [AddCommMonoid A]
    (S : Finset ℕ) (J M : ℕ) (hS : ∀ n ∈ S, J ≤ n ∧ n < J + M) (f : ℕ → A) :
    (∑ n ∈ S, f n) = ∑ j : Fin M, if J + j.val ∈ S then f (J + j.val) else 0 := by
  rw [← Finset.sum_filter]
  apply Finset.sum_bij (fun n hn =>
    (⟨n - J, by have hh := hS n hn; omega⟩ : Fin M))
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have hnJ := (hS n hn).1
    simpa only [Nat.add_sub_of_le hnJ] using hn
  · intro n hn m hm he
    have hval := congrArg Fin.val he
    have hnJ := (hS n hn).1
    have hmJ := (hS m hm).1
    dsimp at hval
    omega
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    refine ⟨J + j.val, hj, ?_⟩
    apply Fin.ext
    simp
  · intro n hn
    have hnJ := (hS n hn).1
    simp only [Nat.add_sub_of_le hnJ]

 theorem finite_support_multiplicative_sieve (S : Finset ℕ) (J M Q : ℕ)
    (hM : 1 ≤ M) (hQ : 1 ≤ Q) (hS : ∀ n ∈ S, J ≤ n ∧ n < J + M)
    (c : ℕ → ℂ) (F : (q : ℕ) → Finset (DirichletCharacter ℂ q))
    (hF : ∀ q ∈ Finset.Icc 1 Q, ∀ χ ∈ F q, χ.IsPrimitive) :
    (∑ q ∈ Finset.Icc 1 Q, ∑ χ ∈ F q,
      ‖∑ n ∈ S, c n * χ (n : ZMod q)‖ ^ 2) ≤
      ((M : ℝ) + (Q : ℝ) ^ 2) * ∑ n ∈ S, ‖c n‖ ^ 2 := by
  let b : Fin M → ℂ := fun j => if J + j.val ∈ S then c (J + j.val) else 0
  have hs (q : ℕ) (χ : DirichletCharacter ℂ q) :
      (∑ n ∈ S, c n * χ (n : ZMod q)) =
        ∑ j : Fin M, b j * χ (((J : ℤ) + (j.val : ℤ) : ℤ) : ZMod q) := by
    rw [finite_interval_sum S J M hS]
    apply Finset.sum_congr rfl
    intro j _
    simp only [b, Int.cast_add, Int.cast_natCast]
    split_ifs <;> simp [Nat.cast_add]
  have he : (∑ n ∈ S, ‖c n‖ ^ 2) = ∑ j : Fin M, ‖b j‖ ^ 2 := by
    rw [finite_interval_sum S J M hS]
    apply Finset.sum_congr rfl
    intro j _
    simp only [b]
    split_ifs <;> simp
  simp_rw [hs]
  rw [he]
  exact primitive_multiplicative_large_sieve M Q hM hQ J b F hF

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_LogWindowDiameter
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual integer length of a short logarithmic window -/

namespace Ostmann

open scoped Classical BigOperators

 theorem sub_le_mul_log_sub {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    y - x ≤ y * (Real.log y - Real.log x) := by
  have h := mul_le_mul_of_nonneg_right (Real.log_le_sub_one_of_pos (div_pos hx hy)) hy.le
  rw [Real.log_div hx.ne' hy.ne'] at h
  field_simp at h
  nlinarith

 theorem log_window_diameter {n m N : ℕ} {x h : ℝ}
    (hn : 1 ≤ n) (hm : 1 ≤ m) (hnN : n ≤ N) (hmN : m ≤ N) (hh : 0 ≤ h)
    (hln : |Real.log n - x| ≤ h) (hlm : |Real.log m - x| ≤ h) :
    |(n : ℝ) - m| ≤ 2 * N * h := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hnR : (n : ℝ) ≤ N := by exact_mod_cast hnN
  have hmR : (m : ℝ) ≤ N := by exact_mod_cast hmN
  have hdn := abs_le.mp hln
  have hdm := abs_le.mp hlm
  rcases le_total (m : ℝ) n with hmn | hnm
  · rw [abs_of_nonneg (sub_nonneg.mpr hmn)]
    have hlog : Real.log n - Real.log m ≤ 2 * h := by linarith
    have hl := sub_le_mul_log_sub hmpos hnpos
    have hprod := mul_le_mul_of_nonneg_left hlog hnpos.le
    have hsize := mul_le_mul_of_nonneg_right hnR (by linarith : 0 ≤ 2 * h)
    nlinarith
  · rw [abs_of_nonpos (sub_nonpos.mpr hnm)]
    have hlog : Real.log m - Real.log n ≤ 2 * h := by linarith
    have hl := sub_le_mul_log_sub hnpos hmpos
    have hprod := mul_le_mul_of_nonneg_left hlog hmpos.le
    have hsize := mul_le_mul_of_nonneg_right hmR (by linarith : 0 ≤ 2 * h)
    nlinarith

 theorem log_window_integer_interval (S : Finset ℕ) (N : ℕ) (x h : ℝ)
    (hh : 0 ≤ h)
    (hS : ∀ n ∈ S, 1 ≤ n ∧ n ≤ N ∧ |Real.log n - x| ≤ h) :
    ∃ J : ℕ, ∀ n ∈ S, J ≤ n ∧ n < J + (⌈2 * N * h⌉₊ + 1) := by
  by_cases hne : S.Nonempty
  · refine ⟨S.min' hne, ?_⟩
    intro n hn
    have hm := hS (S.min' hne) (Finset.min'_mem S hne)
    have hnn := hS n hn
    have hmin := Finset.min'_le S n hn
    refine ⟨hmin, ?_⟩
    have hd := log_window_diameter hnn.1 hm.1 hnn.2.1 hm.2.1 hh hnn.2.2 hm.2.2
    have hc := Nat.le_ceil (2 * (N : ℝ) * h)
    have hb : (n : ℝ) - S.min' hne ≤ ⌈2 * (N : ℝ) * h⌉₊ := (le_abs_self _).trans (hd.trans hc)
    have hi : n ≤ S.min' hne + ⌈2 * (N : ℝ) * h⌉₊ := by exact_mod_cast (by linarith : (n : ℝ) ≤ (S.min' hne : ℝ) + ⌈2 * (N : ℝ) * h⌉₊)
    omega
  · exact ⟨0, by simp [Finset.not_nonempty_iff_eq_empty.mp hne]⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_PositiveFourierCutoff
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A positive band-limited Schwartz cutoff

A narrow real even smooth bump has a real Fourier transform bounded away from
zero on the unit interval. Squaring this transform gives the required cutoff;
its Fourier support is controlled by the convolution of the original bumps.
-/

namespace Ostmann

open MeasureTheory
open scoped SchwartzMap FourierTransform ComplexConjugate Convolution

private theorem narrowSchwartz_apply (x : ℝ) : narrowSchwartz x = (narrowBump x : ℂ) := rfl

private theorem narrowSchwartz_even (x : ℝ) : narrowSchwartz (-x) = narrowSchwartz x := by
  simp only [narrowSchwartz_apply, narrowBump.neg]

private theorem narrow_fourier_lower (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    (∫ y : ℝ, narrowBump y) / 2 ≤ (𝓕 narrowSchwartz x).re := by
  let phase : ℝ → ℂ := fun y => Complex.exp ((-2 * Real.pi * y * x : ℝ) * Complex.I)
  have hc : HasCompactSupport (fun y : ℝ => narrowSchwartz y) := by
    change HasCompactSupport (Complex.ofReal ∘ (narrowBump : ℝ → ℝ))
    exact narrowBump.hasCompactSupport.comp_left (show Complex.ofReal 0 = 0 by simp)
  have hi : Integrable (fun y : ℝ => phase y * narrowSchwartz y) :=
    (by fun_prop : Continuous (fun y : ℝ => phase y * narrowSchwartz y)).integrable_of_hasCompactSupport hc.mul_left
  have hu : Integrable (narrowBump : ℝ → ℝ) :=
    narrowBump.continuous.integrable_of_hasCompactSupport narrowBump.hasCompactSupport
  have hphase (y : ℝ) : (phase y * narrowSchwartz y).re =
      Real.cos (-2 * Real.pi * y * x) * narrowBump y := by
    simp only [phase, narrowSchwartz_apply, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero, Complex.exp_ofReal_mul_I_re]
  have hire := hi.re
  change Integrable (fun y => (phase y * narrowSchwartz y).re) at hire
  have hint : Integrable (fun y => Real.cos (-2 * Real.pi * y * x) * narrowBump y) := by
    simpa only [hphase] using hire
  have he : (𝓕 narrowSchwartz x).re = ∫ y : ℝ, Real.cos (-2 * Real.pi * y * x) * narrowBump y := by
    rw [SchwartzMap.fourier_coe, Real.fourier_real_eq_integral_exp_smul]
    change (∫ y : ℝ, phase y * narrowSchwartz y).re = _
    have hh := integral_re hi
    change (∫ y : ℝ, (phase y * narrowSchwartz y).re) = (∫ y : ℝ, phase y * narrowSchwartz y).re at hh
    rw [← hh]
    simp only [hphase]
  rw [he, div_eq_mul_inv, ← integral_mul_const]
  apply integral_mono (hu.mul_const _) hint
  · intro y
    by_cases hy : narrowBump y = 0
    · simp [hy]
    have hylt : |y| < 1 / 100 := by
      have hm : y ∈ Function.support narrowBump := hy
      rw [narrowBump.support_eq, Metric.mem_ball, Real.dist_eq, sub_zero] at hm
      exact hm
    have hxabs : |x| ≤ 1 := by rw [abs_of_nonneg hx.1]; exact hx.2
    have hang : |(-2 * Real.pi * y * x)| ≤ 1 := by
      rw [abs_mul, abs_mul, abs_mul, abs_neg, abs_of_pos (show (0 : ℝ) < 2 by norm_num), abs_of_pos Real.pi_pos]
      have hh := mul_le_mul (le_of_lt hylt) hxabs (abs_nonneg x) (by norm_num : (0 : ℝ) ≤ 1 / 100)
      nlinarith [Real.pi_lt_four, Real.pi_pos]
    have hcos : (1 / 2 : ℝ) ≤ Real.cos (-2 * Real.pi * y * x) := by
      have hs := (abs_le.mp hang)
      nlinarith [Real.one_sub_sq_div_two_le_cos (x := -2 * Real.pi * y * x)]
    simpa only [div_eq_mul_inv, one_mul, mul_comm] using mul_le_mul_of_nonneg_right hcos (narrowBump.nonneg' y)

private theorem narrow_integral_pos : 0 < ∫ y : ℝ, narrowBump y := by
  apply integral_pos_of_integrable_nonneg_nonzero narrowBump.continuous
    (narrowBump.continuous.integrable_of_hasCompactSupport narrowBump.hasCompactSupport)
    narrowBump.nonneg'
  have hh : narrowBump (0 : ℝ) = 1 := narrowBump.one_of_mem_closedBall (by
    simp only [Metric.mem_closedBall, dist_self]; exact narrowBump.rIn_pos.le)
  rw [hh]
  norm_num

/-- The compact bump itself localizes a Dirichlet polynomial while its Fourier
transform is bounded below throughout the unit height window. -/
theorem exists_density_localizer :
    ∃ (c : ℝ) (W : 𝓢(ℝ, ℂ)), 0 < c ∧
      (∀ x, 1 ≤ |x| → W x = 0) ∧ (∀ x, ‖W x‖ ≤ 1) ∧
      (∀ t, |t| ≤ 1 → c ≤ ‖𝓕 W t‖) := by
  refine ⟨(∫ y : ℝ, narrowBump y) / 2, narrowSchwartz,
    div_pos narrow_integral_pos (by norm_num), ?_, ?_, ?_⟩
  · intro x hx
    have hz : narrowBump x = 0 := narrowBump.zero_of_le_dist (by
      change 1 / 100 ≤ |x - 0|
      rw [sub_zero]
      linarith)
    simp only [narrowSchwartz_apply, hz, Complex.ofReal_zero]
  · intro x
    rw [narrowSchwartz_apply, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (narrowBump.nonneg' x)]
    exact narrowBump.le_one
  · intro t ht
    have heven (y : ℝ) : 𝓕 narrowSchwartz (-y) = 𝓕 narrowSchwartz y := by
      have he := Real.fourier_comp_linearIsometry (LinearIsometryEquiv.neg ℝ (E := ℝ))
        (narrowSchwartz : ℝ → ℂ) y
      have hh : (narrowSchwartz : ℝ → ℂ) ∘ LinearIsometryEquiv.neg ℝ = narrowSchwartz := by
        funext z
        exact narrowSchwartz_even z
      rw [hh] at he
      exact he.symm
    have habs : ‖𝓕 narrowSchwartz |t|‖ = ‖𝓕 narrowSchwartz t‖ := by
      rcases le_total 0 t with h | h
      · rw [abs_of_nonneg h]
      · rw [abs_of_nonpos h, heven]
    rw [← habs]
    exact (narrow_fourier_lower |t| ⟨abs_nonneg t, ht⟩).trans (Complex.re_le_norm _)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_LocalizedMultiplicativeSieve
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The multiplicative sieve on the actual support of a logarithmic window -/

namespace Ostmann

open scoped BigOperators Classical

 theorem localized_multiplicative_sieve (N Q : ℕ) (hQ : 1 ≤ Q)
    (x h : ℝ) (hh : 0 < h) (W : ℝ → ℂ)
    (hW : ∀ y, 1 ≤ |y| → W y = 0) (a : ℕ → ℂ)
    (F : (q : ℕ) → Finset (DirichletCharacter ℂ q))
    (hF : ∀ q ∈ Finset.Icc 1 Q, ∀ χ ∈ F q, χ.IsPrimitive) :
    (∑ q ∈ Finset.Icc 1 Q, ∑ χ ∈ F q,
      ‖∑ n ∈ Finset.Icc 1 N, a n * W ((x - Real.log n) / h) * χ (n : ZMod q)‖ ^ 2) ≤
        (2 * N * h + (Q : ℝ) ^ 2 + 2) *
          ∑ n ∈ Finset.Icc 1 N, ‖a n * W ((x - Real.log n) / h)‖ ^ 2 := by
  let S : Finset ℕ := (Finset.Icc 1 N).filter fun n : ℕ => W ((x - Real.log n) / h) ≠ 0
  have hS (n : ℕ) (hn : n ∈ S) :
      1 ≤ n ∧ n ≤ N ∧ |Real.log n - x| ≤ h := by
    obtain ⟨hnN, hne⟩ := Finset.mem_filter.mp hn
    have hw : |(x - Real.log n) / h| < 1 := lt_of_not_ge (fun hy => hne (hW _ hy))
    have hh' : |x - Real.log n| < h := by
      rw [abs_div, abs_of_pos hh, div_lt_one hh] at hw
      exact hw
    exact ⟨(Finset.mem_Icc.mp hnN).1, (Finset.mem_Icc.mp hnN).2,
      by rw [abs_sub_comm]; exact hh'.le⟩
  obtain ⟨J, hJ⟩ := log_window_integer_interval S N x h hh.le hS
  have hs := finite_support_multiplicative_sieve S J (⌈2 * N * h⌉₊ + 1) Q
    (by omega) hQ hJ (fun n => a n * W ((x - Real.log n) / h)) F hF
  have hsum {A : Type} [AddCommMonoid A] (g : ℕ → A)
      (hg : ∀ n ∈ Finset.Icc 1 N, W ((x - Real.log n) / h) = 0 → g n = 0) :
      (∑ n ∈ S, g n) = ∑ n ∈ Finset.Icc 1 N, g n := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro n hn hnot
    apply hg n hn
    by_contra hne
    exact hnot (Finset.mem_filter.mpr ⟨hn, hne⟩)
  have hpoly (q : ℕ) (χ : DirichletCharacter ℂ q) := hsum (A := ℂ)
    (fun n => a n * W ((x - Real.log n) / h) * χ (n : ZMod q))
    (by intro n _ hn; simp only [hn, mul_zero, zero_mul])
  have henergy := hsum (A := ℝ) (fun n => ‖a n * W ((x - Real.log n) / h)‖ ^ 2)
    (by intro n _ hn; simp [hn])
  simp_rw [hpoly] at hs
  rw [henergy] at hs
  apply hs.trans
  apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have hc := Nat.ceil_lt_add_one (by positivity : 0 ≤ 2 * (N : ℝ) * h)
  push_cast
  linarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticLogTranslation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Translating the logarithmic cutoff preserves its Fourier L1 cost -/

namespace Ostmann

open MeasureTheory
open scoped SchwartzMap FourierTransform

 theorem quadratic_fourier_phase_integral (f : 𝓢(ℝ, ℂ)) (u : ℝ) :
    𝓕 f u = ∫ x : ℝ, realAdditivePhase (-(x * u)) * f x := by
  rw [SchwartzMap.fourier_coe, Real.fourier_real_eq_integral_exp_smul]
  apply integral_congr_ae
  filter_upwards with x
  change Complex.exp _ * f x = Complex.exp _ * f x
  congr 2
  push_cast
  ring

 theorem quadratic_fourier_translate (f : 𝓢(ℝ, ℂ)) (a u : ℝ) :
    𝓕 (f.compSubConstCLM ℂ a) u = realAdditivePhase (-(a * u)) * 𝓕 f u := by
  rw [quadratic_fourier_phase_integral, quadratic_fourier_phase_integral]
  have ht := integral_add_right_eq_self (μ := volume)
    (fun x : ℝ => realAdditivePhase (-(x * u)) * f (x - a)) a
  change (∫ x : ℝ, realAdditivePhase (-(x * u)) * f (x - a)) = _
  rw [← ht, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with x
  rw [add_sub_cancel_right]
  have he : -((x + a) * u) = -(a * u) + -(x * u) := by ring
  rw [he, realAdditivePhase_add]
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityCompletedSquare
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The entire completed square and its exact reflection -/

namespace Ostmann

open Complex

 theorem densityCompletedSquare_analytic (χ : PrimitiveComplexCharacter) (s : ℂ) :
    AnalyticAt ℂ (densityCompletedSquare χ) s := by
  have hq : (χ.modulus : ℂ) ≠ 0 := by exact_mod_cast χ.positive.ne'
  exact ((differentiable_id.const_cpow (Or.inl hq)).analyticAt s).mul
    ((χ.completed_analytic s).pow 2)

 theorem densityCompletedSquare_reflection (χ : PrimitiveComplexCharacter) (s : ℂ) :
    densityCompletedSquare χ s =
      (@DirichletCharacter.rootNumber χ.modulus ⟨χ.positive.ne'⟩ χ.character) ^ 2 *
        densityCompletedSquare χ.inverse (1 - s) := by
  let : NeZero χ.modulus := ⟨χ.positive.ne'⟩
  have hq : (χ.modulus : ℂ) ≠ 0 := by exact_mod_cast χ.positive.ne'
  have hf := χ.primitive.completedLFunction_one_sub (1 - s)
  rw [show (1 : ℂ) - (1 - s) = s by ring,
    show (1 : ℂ) - s - 1 / 2 = 1 / 2 - s by ring] at hf
  change χ.completed s = (χ.modulus : ℂ) ^ (1 / 2 - s) *
    DirichletCharacter.rootNumber χ.character * χ.inverse.completed (1 - s) at hf
  have hp : (χ.modulus : ℂ) ^ s * ((χ.modulus : ℂ) ^ (1 / 2 - s)) ^ 2 =
      (χ.modulus : ℂ) ^ (1 - s) := by
    rw [← Complex.cpow_mul_nat, ← Complex.cpow_add _ _ hq]
    congr 1
    norm_num
    ring
  unfold densityCompletedSquare
  rw [hf, mul_pow, mul_pow]
  change (χ.modulus : ℂ) ^ s *
    (((χ.modulus : ℂ) ^ (1 / 2 - s)) ^ 2 *
    (DirichletCharacter.rootNumber χ.character) ^ 2 * χ.inverse.completed (1 - s) ^ 2) = _
  calc
    _ = ((χ.modulus : ℂ) ^ s * ((χ.modulus : ℂ) ^ (1 / 2 - s)) ^ 2) *
        (DirichletCharacter.rootNumber χ.character) ^ 2 * χ.inverse.completed (1 - s) ^ 2 := by ring
    _ = _ := by rw [hp, PrimitiveComplexCharacter.inverse_modulus]; ring

 theorem densityCompletedSquare_eq (χ : PrimitiveComplexCharacter) (s : ℂ) (hs : 0 < s.re) :
    densityCompletedSquare χ s = (χ.modulus : ℂ) ^ s *
      (DirichletCharacter.gammaFactor χ.character s) ^ 2 * χ.L s ^ 2 := by
  rw [densityCompletedSquare, χ.completed_eq_L_mul_gamma s hs, mul_pow]
  ring

 theorem densitySquareNormalizer_ne_zero (χ : PrimitiveComplexCharacter) (s : ℂ)
    (hs : 0 < s.re) : densitySquareNormalizer χ s ≠ 0 := by
  have hq : (χ.modulus : ℂ) ≠ 0 := by exact_mod_cast χ.positive.ne'
  have hg : DirichletCharacter.gammaFactor χ.character s ≠ 0 := by
    intro he
    have hn := χ.gammaInverse_ne_zero s hs
    exact hn (by simp only [PrimitiveComplexCharacter.gammaInverse, he, inv_zero])
  exact mul_ne_zero (Complex.cpow_ne_zero_iff.mpr (Or.inl hq)) (pow_ne_zero 2 hg)

 theorem densityCompletedSquare_div (χ : PrimitiveComplexCharacter) (s : ℂ)
    (hs : 0 < s.re) : densityCompletedSquare χ s / densitySquareNormalizer χ s = χ.L s ^ 2 := by
  rw [densityCompletedSquare_eq χ s hs]
  exact mul_div_cancel_left₀ _ (densitySquareNormalizer_ne_zero χ s hs)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityCompletedStrip
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A polynomial bound for the entire completed square on the contour strip -/

namespace Ostmann

open Complex

 theorem density_completed_strip_bound : ∃ C : ℝ, 0 < C ∧
    ∀ (χ : PrimitiveComplexCharacter) (s : ℂ), -(1 / 2 : ℝ) ≤ s.re → s.re ≤ 3 / 2 →
      ‖χ.completed s‖ ≤ C * ((χ.modulus : ℝ) + 1) ^ 2 * (|s.im| + 2) := by
  obtain ⟨G, hG, hg, _⟩ := characterGamma_growth_bounds
  have hr (χ : PrimitiveComplexCharacter) (s : ℂ) (hs : 1 / 2 ≤ s.re) (hs3 : s.re ≤ 3 / 2) :
      ‖χ.completed s‖ ≤ (2 * G) * ((χ.modulus : ℝ) + 1) * (|s.im| + 2) := by
    have hpos : 0 < s.re := by linarith
    have hn : ‖s‖ ≤ |s.im| + 2 := by
      apply (Complex.norm_le_abs_re_add_abs_im s).trans
      rw [abs_of_pos hpos]
      linarith
    have hl : ‖χ.L s‖ ≤ 2 * ((χ.modulus : ℝ) + 1) * (|s.im| + 2) := by
      apply (χ.L_norm_bound_positive s hpos).trans
      apply (div_le_iff₀ hpos).mpr
      have h := mul_le_mul_of_nonneg_right hn (by positivity : 0 ≤ (χ.modulus : ℝ) + 1)
      have hm := mul_le_mul_of_nonneg_left hs (by positivity :
        0 ≤ 2 * ((χ.modulus : ℝ) + 1) * (|s.im| + 2))
      nlinarith
    rw [χ.completed_eq_L_mul_gamma s hpos, norm_mul]
    exact (mul_le_mul hl (hg χ s hs (by linarith)) (norm_nonneg _) (by positivity)).trans_eq
      (by ring)
  refine ⟨2 * G, by positivity, ?_⟩
  intro χ s hs hs3
  have hq : 1 ≤ (χ.modulus : ℝ) := by exact_mod_cast χ.positive
  by_cases hh : 1 / 2 ≤ s.re
  · apply (hr χ s hh hs3).trans
    have hqq : (χ.modulus : ℝ) + 1 ≤ ((χ.modulus : ℝ) + 1) ^ 2 := by nlinarith
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hqq (by positivity)) (by positivity)
  · let : NeZero χ.modulus := ⟨χ.positive.ne'⟩
    have hi := hr χ.inverse (1 - s) (by simp; linarith) (by simp; linarith)
    simp only [PrimitiveComplexCharacter.inverse_modulus, sub_im, one_im, zero_sub, abs_neg] at hi
    have hp : ‖(χ.modulus : ℂ) ^ (1 / 2 - s)‖ ≤ χ.modulus := by
      rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos (by linarith)]
      apply (Real.rpow_le_rpow_of_exponent_le hq (show (1 / 2 - s).re ≤ 1 by simp; linarith)).trans_eq
      exact Real.rpow_one _
    have hf := χ.primitive.completedLFunction_one_sub (1 - s)
    rw [show (1 : ℂ) - (1 - s) = s by ring,
      show (1 : ℂ) - s - 1 / 2 = 1 / 2 - s by ring] at hf
    change χ.completed s = (χ.modulus : ℂ) ^ (1 / 2 - s) *
      DirichletCharacter.rootNumber χ.character * χ.inverse.completed (1 - s) at hf
    rw [hf, norm_mul, norm_mul, χ.rootNumber_norm_eq_one, mul_one]
    calc
      _ ≤ (χ.modulus : ℝ) * ((2 * G) * ((χ.modulus : ℝ) + 1) * (|s.im| + 2)) :=
        mul_le_mul hp hi (norm_nonneg _) (by positivity)
      _ ≤ _ := by
        have hqq : (χ.modulus : ℝ) * ((χ.modulus : ℝ) + 1) ≤ ((χ.modulus : ℝ) + 1) ^ 2 := by nlinarith
        have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hqq
          (by positivity : 0 ≤ 2 * G)) (by positivity : 0 ≤ |s.im| + 2)
        nlinarith

 theorem density_completed_square_strip_bound : ∃ C : ℝ, 0 < C ∧
    ∀ (χ : PrimitiveComplexCharacter) (s : ℂ), -(1 / 2 : ℝ) ≤ s.re → s.re ≤ 3 / 2 →
      ‖densityCompletedSquare χ s‖ ≤ C * ((χ.modulus : ℝ) + 1) ^ 6 * (|s.im| + 2) ^ 2 := by
  obtain ⟨C, hC, hb⟩ := density_completed_strip_bound
  refine ⟨C ^ 2, by positivity, ?_⟩
  intro χ s hs hs3
  have hq : 1 ≤ (χ.modulus : ℝ) := by exact_mod_cast χ.positive
  have hp : ‖(χ.modulus : ℂ) ^ s‖ ≤ ((χ.modulus : ℝ) + 1) ^ 2 := by
    rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos (by linarith)]
    calc
      _ ≤ (χ.modulus : ℝ) ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hq (by linarith)
      _ ≤ _ := by rw [Real.rpow_two]; nlinarith
  rw [densityCompletedSquare, norm_mul, norm_pow]
  apply (mul_le_mul hp (pow_le_pow_left₀ (norm_nonneg _) (hb χ s hs hs3) 2)
    (by positivity) (by positivity)).trans_eq
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_RectangleAnalyticPole
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A single pole under an analytic rectangle integral -/

namespace Ostmann

open Complex Filter Set
open scoped Topology

 theorem analytic_dslope_of_analytic (f : ℂ → ℂ) (z s : ℂ)
    (hz : AnalyticAt ℂ f z) (hs : AnalyticAt ℂ f s) : AnalyticAt ℂ (dslope f z) s := by
  by_cases he : s = z
  · subst s
    obtain ⟨p, hp⟩ := hz
    exact ⟨p.fslope, hp.has_fpower_series_dslope_fslope⟩
  · have hh : dslope f z =ᶠ[𝓝 s] fun w => (w - z)⁻¹ * (f w - f z) := by
      filter_upwards [isOpen_ne.mem_nhds he] with w hw
      rw [dslope_of_ne f hw]
      rfl
    exact (((analyticAt_id.sub analyticAt_const).inv (sub_ne_zero.mpr he)).mul
      (hs.sub analyticAt_const)).congr hh.symm

 theorem rectangle_analytic_pole (f : ℂ → ℂ) (a b c d : ℝ)
    (ha : a < 0) (hb : 0 < b) (hc : c < 0) (hd : 0 < d)
    (hf : ∀ z ∈ uIcc a b ×ℂ uIcc c d, AnalyticAt ℂ f z) :
    rectangleBoundaryIntegral (fun z => f z / z) a b c d =
      (2 * (Real.pi : ℂ) * I) * f 0 := by
  have hz : (0 : ℂ) ∈ uIcc a b ×ℂ uIcc c d := by
    simp only [mem_reProdIm, zero_re, zero_im, uIcc_of_le (ha.trans hb).le,
      uIcc_of_le (hc.trans hd).le, mem_Icc]
    exact ⟨⟨ha.le, hb.le⟩, hc.le, hd.le⟩
  let g := dslope f 0
  have hg : ∀ z ∈ uIcc a b ×ℂ uIcc c d, AnalyticAt ℂ g z :=
    fun z hz' => analytic_dslope_of_analytic f 0 z (hf 0 hz) (hf z hz')
  have hn (z : ℂ) (hz' : z ∈ contourRectangleBoundary a b c d) : z ≠ 0 :=
    contourBoundary_ne_interior ⟨ha, hb, hc, hd⟩ hz'
  have hgI : RectangleIntegrable g a b c d := rectangleIntegrable_of_continuousOn
    (fun z hz' => (hg z ⟨hz'.1, hz'.2.1⟩).continuousAt.continuousWithinAt)
  have hpI : RectangleIntegrable (fun z => f 0 * (z - 0)⁻¹) a b c d :=
    (rectangleIntegrable_sub_inv ⟨ha, hb, hc, hd⟩).const_mul _
  have he : rectangleBoundaryIntegral (fun z => f z / z) a b c d =
      rectangleBoundaryIntegral (fun z => g z + f 0 * (z - 0)⁻¹) a b c d := by
    apply rectangleBoundaryIntegral_congr
    intro z hz'
    dsimp [g]
    rw [dslope_of_ne f (hn z hz')]
    simp only [slope, smul_eq_mul, vsub_eq_sub, sub_zero]
    ring
  rw [he, rectangleBoundaryIntegral_add hgI hpI, rectangleBoundaryIntegral_eq_zero hg,
    zero_add, rectangleBoundaryIntegral_const_mul,
    rectangleBoundaryIntegral_sub_inv 0 a b c d ha hb hc hd]
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensitySquareGaussian
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The Gaussian contour for the actual completed square -/

namespace Ostmann

open Complex

 theorem densitySquareGaussian_analytic (χ : PrimitiveComplexCharacter) (s w : ℂ) :
    AnalyticAt ℂ (densitySquareGaussian χ s) w := by
  exact ((densityCompletedSquare_analytic χ (s + w)).comp
    (analyticAt_const.add analyticAt_id)).mul ((analyticAt_id.pow 2).cexp)

 theorem densitySquareGaussian_reflection (χ : PrimitiveComplexCharacter) (s w : ℂ) :
    densitySquareGaussian χ s (-w) =
      (@DirichletCharacter.rootNumber χ.modulus ⟨χ.positive.ne'⟩ χ.character) ^ 2 *
        densitySquareGaussian χ.inverse (1 - s) w := by
  rw [densitySquareGaussian, densityCompletedSquare_reflection]
  simp only [neg_sq, densitySquareGaussian]
  rw [show 1 - (s + -w) = (1 - s) + w by ring]
  ring

 theorem densitySquareGaussian_rectangle (χ : PrimitiveComplexCharacter) (s : ℂ)
    (a b T : ℝ) (ha : a < 0) (hb : 0 < b) (hT : 0 < T) :
    rectangleBoundaryIntegral (fun w => densitySquareGaussian χ s w / w) a b (-T) T =
      (2 * (Real.pi : ℂ) * I) * densityCompletedSquare χ s := by
  have h := rectangle_analytic_pole (densitySquareGaussian χ s) a b (-T) T ha hb
    (by linarith) hT (fun w _ => densitySquareGaussian_analytic χ s w)
  simpa only [densitySquareGaussian, add_zero, zero_pow (by norm_num : 2 ≠ 0),
    Complex.exp_zero, mul_one] using h

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityGaussianEnvelope
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # An integrable envelope for the completed-square contour -/

namespace Ostmann

open Complex Filter MeasureTheory
open scoped Topology

 theorem densityGaussianEnvelope_integrable : Integrable densityGaussianEnvelope := by
  have h0 := integrable_exp_neg_mul_sq (b := (1 : ℝ)) (by norm_num)
  have h2 := integrable_rpow_mul_exp_neg_mul_sq (b := (1 : ℝ)) (by norm_num)
    (s := (2 : ℝ)) (by norm_num)
  convert h0.add h2 using 1
  all_goals try with_reducible_and_instances rfl
  funext u
  simp only [densityGaussianEnvelope, Real.rpow_two, neg_mul, one_mul, add_mul, Pi.add_apply]

 theorem densityGaussianEnvelope_tendsto :
    Tendsto densityGaussianEnvelope atTop (𝓝 0) := by
  have hp : Tendsto (fun t : ℝ => t ^ 2) atTop atTop :=
    tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)
  have h0 := Real.tendsto_exp_neg_atTop_nhds_zero.comp hp
  have h1 := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hp
  convert h0.add h1 using 1
  · funext u
    simp only [densityGaussianEnvelope, Function.comp_apply, pow_one, add_mul, one_mul]
  · norm_num

 theorem densitySquareGaussian_band_bound (χ : PrimitiveComplexCharacter) (s : ℂ)
    (hs : s.re = 1 / 2) : ∃ K : ℝ, 0 < K ∧ ∀ x u : ℝ, |x| ≤ 1 →
      ‖densitySquareGaussian χ s ((x : ℂ) + u * I)‖ ≤ K * densityGaussianEnvelope u := by
  obtain ⟨C, hC, hb⟩ := density_completed_square_strip_bound
  let a := |s.im| + 2
  let K := C * ((χ.modulus : ℝ) + 1) ^ 6 * 2 * a ^ 2 * Real.exp 1
  have ha : 2 ≤ a := by dsimp [a]; linarith [abs_nonneg s.im]
  refine ⟨K, by dsimp [K]; positivity, ?_⟩
  intro x u hx
  have hz : -(1 / 2 : ℝ) ≤ (s + ((x : ℂ) + u * I)).re ∧
      (s + ((x : ℂ) + u * I)).re ≤ 3 / 2 := by
    simp only [add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im, mul_zero,
      zero_mul, sub_self, add_zero, hs]
    exact ⟨by linarith [(abs_le.mp hx).1], by linarith [(abs_le.mp hx).2]⟩
  have hi : |(s + ((x : ℂ) + u * I)).im| + 2 ≤ a + |u| := by
    simp only [add_im, ofReal_im, mul_im, I_re, I_im, ofReal_re, mul_one,
      zero_mul, add_zero, zero_add]
    dsimp [a]
    linarith [abs_add_le s.im u]
  have hpoly : (|(s + ((x : ℂ) + u * I)).im| + 2) ^ 2 ≤ 2 * a ^ 2 * (1 + u ^ 2) := by
    have h1 := pow_le_pow_left₀ (by positivity : 0 ≤ |(s + ((x : ℂ) + u * I)).im| + 2) hi 2
    have haa : 1 ≤ a ^ 2 := by nlinarith
    have h2 := mul_nonneg (sub_nonneg.mpr haa) (sq_nonneg u)
    nlinarith [sq_nonneg (a - |u|), sq_abs u]
  have hexp : ‖Complex.exp (((x : ℂ) + u * I) ^ 2)‖ ≤ Real.exp 1 * Real.exp (-(u ^ 2)) := by
    rw [Complex.norm_exp, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hxx : x ^ 2 ≤ 1 := by nlinarith [(abs_le.mp hx).1, (abs_le.mp hx).2]
    have hre : (((x : ℂ) + u * I) ^ 2).re = x ^ 2 - u ^ 2 := by
      simp [pow_two, mul_re, mul_im]
    rw [hre]
    linarith
  rw [densitySquareGaussian, norm_mul]
  calc
    _ ≤ (C * ((χ.modulus : ℝ) + 1) ^ 6 * (|(s + ((x : ℂ) + u * I)).im| + 2) ^ 2) *
        (Real.exp 1 * Real.exp (-(u ^ 2))) :=
      mul_le_mul (hb χ _ hz.1 hz.2) hexp (norm_nonneg _) (by positivity)
    _ ≤ (C * ((χ.modulus : ℝ) + 1) ^ 6 * (2 * a ^ 2 * (1 + u ^ 2))) *
        (Real.exp 1 * Real.exp (-(u ^ 2))) := by gcongr
    _ = K * densityGaussianEnvelope u := by dsimp [K, densityGaussianEnvelope]; ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensitySquareContour
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The convergent vertical lines and vanishing horizontal edges -/

namespace Ostmann

open Complex Filter MeasureTheory Set
open scoped Topology Interval

 theorem densitySquareContour_bound (χ : PrimitiveComplexCharacter) (s : ℂ) (K : ℝ)
    (hK : ∀ x u : ℝ, |x| ≤ 1 →
      ‖densitySquareGaussian χ s ((x : ℂ) + u * I)‖ ≤ K * densityGaussianEnvelope u)
    (x u : ℝ) (hx : |x| ≤ 1) (hn : 1 ≤ ‖(x : ℂ) + u * I‖) :
    ‖densitySquareContour χ s ((x : ℂ) + u * I)‖ ≤ K * densityGaussianEnvelope u := by
  rw [densitySquareContour, norm_div]
  exact (div_le_self (norm_nonneg _) hn).trans (hK x u hx)

 theorem densitySquareContour_vertical_integrable (χ : PrimitiveComplexCharacter) (s : ℂ)
    (hs : s.re = 1 / 2) (x : ℝ) (hx : |x| = 1) :
    Integrable (fun u : ℝ => densitySquareContour χ s ((x : ℂ) + u * I)) := by
  obtain ⟨K, _, hK⟩ := densitySquareGaussian_band_bound χ s hs
  have hcont : Continuous (fun u : ℝ => densitySquareContour χ s ((x : ℂ) + u * I)) := by
    have hF : Continuous (densitySquareGaussian χ s) :=
      continuous_iff_continuousAt.mpr (fun w => (densitySquareGaussian_analytic χ s w).continuousAt)
    apply (hF.comp (by fun_prop)).div (by fun_prop)
    intro u he
    have hr := congrArg Complex.re he
    simp only [add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im, mul_zero,
      zero_mul, sub_self, add_zero, zero_re] at hr
    simp [hr] at hx
  apply (densityGaussianEnvelope_integrable.const_mul K).mono' hcont.aestronglyMeasurable
  filter_upwards with u
  apply densitySquareContour_bound χ s K hK x u hx.le
  have hn := Complex.abs_re_le_norm ((x : ℂ) + u * I)
  simpa only [add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im, mul_zero,
    zero_mul, sub_self, add_zero, hx] using hn

 theorem densitySquareContour_horizontal_bound (χ : PrimitiveComplexCharacter) (s : ℂ)
    (K : ℝ) (hK : ∀ x u : ℝ, |x| ≤ 1 →
      ‖densitySquareGaussian χ s ((x : ℂ) + u * I)‖ ≤ K * densityGaussianEnvelope u)
    (u : ℝ) (hu : 1 ≤ |u|) :
    ‖∫ x in (-1 : ℝ)..1, densitySquareContour χ s ((x : ℂ) + u * I)‖ ≤
      2 * K * densityGaussianEnvelope u := by
  have hb : ∀ x ∈ Ι (-1 : ℝ) 1,
      ‖densitySquareContour χ s ((x : ℂ) + u * I)‖ ≤ K * densityGaussianEnvelope u := by
    intro x hx
    have hxm : -1 ≤ x ∧ x ≤ 1 := by
      rw [uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hx
      exact ⟨hx.1.le, hx.2⟩
    apply densitySquareContour_bound χ s K hK x u (abs_le.mpr hxm)
    have hn := Complex.abs_im_le_norm ((x : ℂ) + u * I)
    have he : (((x : ℂ) + u * I).im) = u := by simp
    rw [he] at hn
    exact hu.trans hn
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hb
  norm_num at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ring

 theorem densitySquareContour_horizontal_tendsto (χ : PrimitiveComplexCharacter) (s : ℂ)
    (hs : s.re = 1 / 2) :
    Tendsto (fun u : ℝ => ∫ x in (-1 : ℝ)..1,
      densitySquareContour χ s ((x : ℂ) + u * I)) atTop (𝓝 0) ∧
    Tendsto (fun u : ℝ => ∫ x in (-1 : ℝ)..1,
      densitySquareContour χ s ((x : ℂ) + (-u) * I)) atTop (𝓝 0) := by
  obtain ⟨K, _, hK⟩ := densitySquareGaussian_band_bound χ s hs
  have he : Tendsto (fun u => 2 * K * densityGaussianEnvelope u) atTop (𝓝 0) := by
    simpa only [mul_zero] using densityGaussianEnvelope_tendsto.const_mul (2 * K)
  constructor
  · rw [tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero' (Filter.Eventually.of_forall (fun _ => norm_nonneg _)) _ he
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with u hu
    exact densitySquareContour_horizontal_bound χ s K hK u (by simpa [abs_of_pos (by linarith : 0 < u)])
  · rw [tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero' (Filter.Eventually.of_forall (fun _ => norm_nonneg _)) _ he
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with u hu
    have h := densitySquareContour_horizontal_bound χ s K hK (-u)
      (by simpa [abs_of_pos (by linarith : 0 < u)])
    simpa only [densityGaussianEnvelope, neg_sq, Complex.ofReal_neg] using h

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensitySquareEquation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual Gaussian functional equation for the completed square -/

namespace Ostmann

open Complex Filter MeasureTheory
open scoped Topology Interval

 theorem densitySquareContour_limit (χ : PrimitiveComplexCharacter) (s : ℂ)
    (hs : s.re = 1 / 2) :
    I * (∫ u : ℝ, densitySquareContour χ s (1 + u * I)) -
      I * (∫ u : ℝ, densitySquareContour χ s (-1 + u * I)) =
      (2 * (Real.pi : ℂ) * I) * densityCompletedSquare χ s := by
  obtain ⟨htop, hbot⟩ := densitySquareContour_horizontal_tendsto χ s hs
  have hr := intervalIntegral_tendsto_integral
    (densitySquareContour_vertical_integrable χ s hs 1 (by norm_num))
    tendsto_neg_atTop_atBot tendsto_id
  have hl := intervalIntegral_tendsto_integral
    (densitySquareContour_vertical_integrable χ s hs (-1) (by norm_num))
    tendsto_neg_atTop_atBot tendsto_id
  have hlim := ((hbot.sub htop).add (hr.const_mul I)).sub (hl.const_mul I)
  have hlim' : Tendsto (fun T : ℝ =>
      rectangleBoundaryIntegral (densitySquareContour χ s) (-1) 1 (-T) T) atTop
      (𝓝 (I * (∫ u : ℝ, densitySquareContour χ s (1 + u * I)) -
        I * (∫ u : ℝ, densitySquareContour χ s (-1 + u * I)))) := by
    simpa [rectangleBoundaryIntegral] using hlim
  apply tendsto_nhds_unique hlim'
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
  exact (densitySquareGaussian_rectangle χ s (-1) 1 T (by norm_num) (by norm_num)
    (by linarith)).symm

 theorem densitySquareContour_left_reflection (χ : PrimitiveComplexCharacter) (s : ℂ) :
    (∫ u : ℝ, densitySquareContour χ s (-1 + u * I)) =
      -(@DirichletCharacter.rootNumber χ.modulus ⟨χ.positive.ne'⟩ χ.character) ^ 2 *
        ∫ u : ℝ, densitySquareContour χ.inverse (1 - s) (1 + u * I) := by
  have he (u : ℝ) : densitySquareContour χ s (-1 + (-u) * I) =
      -(@DirichletCharacter.rootNumber χ.modulus ⟨χ.positive.ne'⟩ χ.character) ^ 2 *
        densitySquareContour χ.inverse (1 - s) (1 + u * I) := by
    have hw : (-1 : ℂ) + (-u) * I = -(1 + (u : ℂ) * I) := by ring
    rw [densitySquareContour, hw, densitySquareGaussian_reflection, densitySquareContour, div_neg]
    ring
  calc
    _ = ∫ u : ℝ, densitySquareContour χ s (-1 + (-u) * I) := by
      symm
      simpa only [Complex.ofReal_neg] using
        integral_neg_eq_self (fun u : ℝ => densitySquareContour χ s (-1 + u * I)) volume
    _ = _ := by simp_rw [he]; rw [integral_const_mul]

 theorem densityCompletedSquare_equation (χ : PrimitiveComplexCharacter) (s : ℂ)
    (hs : s.re = 1 / 2) :
    densityCompletedSquare χ s = densitySquareIntegral χ s +
      (@DirichletCharacter.rootNumber χ.modulus ⟨χ.positive.ne'⟩ χ.character) ^ 2 *
        densitySquareIntegral χ.inverse (1 - s) := by
  have h := densitySquareContour_limit χ s hs
  rw [densitySquareContour_left_reflection] at h
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have he : (2 * (Real.pi : ℂ)) * densityCompletedSquare χ s =
      (∫ u : ℝ, densitySquareContour χ s (1 + u * I)) +
      (@DirichletCharacter.rootNumber χ.modulus ⟨χ.positive.ne'⟩ χ.character) ^ 2 *
        ∫ u : ℝ, densitySquareContour χ.inverse (1 - s) (1 + u * I) := by
    apply mul_left_cancel₀ (show (I : ℂ) ≠ 0 from I_ne_zero)
    calc
      _ = (2 * (Real.pi : ℂ) * I) * densityCompletedSquare χ s := by ring
      _ = _ := h.symm.trans (by ring)
  unfold densitySquareIntegral
  field_simp
  simp_rw [mul_comm I]
  linear_combination he

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityNormalizedEquation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The normalized square functional equation on the critical line -/

namespace Ostmann

open Complex
open scoped ComplexConjugate

 theorem density_critical_reflection (s : ℂ) (hs : s.re = 1 / 2) : 1 - s = conj s := by
  apply Complex.ext <;> simp [hs]
  ring

 theorem densitySquareNormalizer_reflected_norm (χ : PrimitiveComplexCharacter) (s : ℂ)
    (hs : s.re = 1 / 2) :
    ‖densitySquareNormalizer χ.inverse (1 - s)‖ = ‖densitySquareNormalizer χ s‖ := by
  have hq : (0 : ℝ) < χ.modulus := by exact_mod_cast χ.positive
  rw [density_critical_reflection s hs]
  unfold densitySquareNormalizer
  rw [χ.gammaFactor_inverse_conj]
  simp only [norm_mul, norm_pow, norm_conj, PrimitiveComplexCharacter.inverse_modulus]
  congr 1
  rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hq,
    Complex.norm_cpow_eq_rpow_re_of_pos hq, Complex.conj_re]

 theorem densitySquareRootFactor_norm (χ : PrimitiveComplexCharacter) (s : ℂ)
    (hs : s.re = 1 / 2) : ‖densitySquareRootFactor χ s‖ = 1 := by
  rw [densitySquareRootFactor, norm_div, norm_mul, norm_pow, χ.rootNumber_norm_eq_one,
    one_pow, one_mul, densitySquareNormalizer_reflected_norm χ s hs]
  exact div_self (norm_ne_zero_iff.mpr (densitySquareNormalizer_ne_zero χ s (by linarith)))

 theorem density_L_square_equation (χ : PrimitiveComplexCharacter) (s : ℂ)
    (hs : s.re = 1 / 2) :
    χ.L s ^ 2 = densitySmoothedSquare χ s +
      densitySquareRootFactor χ s * densitySmoothedSquare χ.inverse (1 - s) := by
  have hp : 0 < s.re := by linarith
  have hi : 0 < (1 - s).re := by simp; linarith
  have hn := densitySquareNormalizer_ne_zero χ s hp
  have hni := densitySquareNormalizer_ne_zero χ.inverse (1 - s) hi
  have he := congrArg (fun z : ℂ => z / densitySquareNormalizer χ s)
    (densityCompletedSquare_equation χ s hs)
  rw [densityCompletedSquare_div χ s hp] at he
  rw [he]
  unfold densitySmoothedSquare densitySquareRootFactor
  field_simp

 theorem density_L_fourth_bound (χ : PrimitiveComplexCharacter) (s : ℂ)
    (hs : s.re = 1 / 2) :
    ‖χ.L s‖ ^ 4 ≤ 2 * ‖densitySmoothedSquare χ s‖ ^ 2 +
      2 * ‖densitySmoothedSquare χ.inverse (1 - s)‖ ^ 2 := by
  have he := norm_add_le (densitySmoothedSquare χ s)
    (densitySquareRootFactor χ s * densitySmoothedSquare χ.inverse (1 - s))
  rw [← density_L_square_equation χ s hs, norm_pow, norm_mul,
    densitySquareRootFactor_norm χ s hs, one_mul] at he
  have hh := pow_le_pow_left₀ (sq_nonneg ‖χ.L s‖) he 2
  nlinarith [sq_nonneg (‖densitySmoothedSquare χ s‖ -
    ‖densitySmoothedSquare χ.inverse (1 - s)‖)]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityLocalizedPolynomial
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact Fourier localization for finite Dirichlet polynomials -/

namespace Ostmann

open MeasureTheory
open scoped BigOperators SchwartzMap FourierTransform

 theorem densityLocalizedPolynomial_apply {ι : Type*} [Fintype ι]
    (W : 𝓢(ℝ, ℂ)) (h : ℝ) (hh : 0 < h) (a : ι → ℂ) (freq : ι → ℝ) (x : ℝ) :
    densityLocalizedPolynomial W h hh a freq x =
      ∑ j, a j * W ((x - freq j) / h) := by
  simp only [densityLocalizedPolynomial, sum_apply, smul_apply,
    SchwartzMap.compSubConstCLM_apply, positiveDilate_apply, smul_eq_mul]
  congr 1
  funext j
  rw [div_eq_inv_mul]

 theorem densityLocalizedPolynomial_fourier {ι : Type*} [Fintype ι]
    (W : 𝓢(ℝ, ℂ)) (h : ℝ) (hh : 0 < h) (a : ι → ℂ) (freq : ι → ℝ) (t : ℝ) :
    𝓕 (densityLocalizedPolynomial W h hh a freq) t =
      (h : ℂ) * 𝓕 W (h * t) * ∑ j, a j * realAdditivePhase (-(freq j * t)) := by
  simp only [densityLocalizedPolynomial, FourierTransform.fourier_sum, FourierTransform.fourier_smul,
    sum_apply, smul_apply, quadratic_fourier_translate,
    positiveDilate_fourier, div_inv_eq_mul, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_comm t h]
  push_cast
  rw [inv_inv]
  ring

 theorem density_localized_pointwise_bound {ι : Type*} [Fintype ι]
    (W : 𝓢(ℝ, ℂ)) (c h T : ℝ) (hc : 0 < c) (hh : 0 < h)
    (hwindow : h * T ≤ 1) (hW : ∀ t, |t| ≤ 1 → c ≤ ‖𝓕 W t‖)
    (a : ι → ℂ) (freq : ι → ℝ) (t : ℝ) (ht : |t| ≤ T) :
    h ^ 2 * c ^ 2 * ‖∑ j, a j * realAdditivePhase (-(freq j * t))‖ ^ 2 ≤
      ‖𝓕 (densityLocalizedPolynomial W h hh a freq) t‖ ^ 2 := by
  have ht' : |h * t| ≤ 1 := by
    rw [abs_mul, abs_of_pos hh]
    exact (mul_le_mul_of_nonneg_left ht hh.le).trans hwindow
  have hw := hW (h * t) ht'
  rw [densityLocalizedPolynomial_fourier, norm_mul, norm_mul, mul_pow, mul_pow,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh]
  gcongr

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityWindowEnergy
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A compact Fourier window controls the height mean square -/

namespace Ostmann

open MeasureTheory Set
open scoped BigOperators SchwartzMap FourierTransform

 theorem density_schwartz_square_integrable (W : 𝓢(ℝ, ℂ)) :
    Integrable (fun x : ℝ => ‖W x‖ ^ 2) :=
  (memLp_two_iff_integrable_sq_norm W.continuous.aestronglyMeasurable).mp (W.memLp 2)

 theorem density_height_window_bound {ι : Type*} [Fintype ι]
    (W : 𝓢(ℝ, ℂ)) (c h T : ℝ) (hc : 0 < c) (hh : 0 < h)
    (hwindow : h * T ≤ 1) (hW : ∀ t, |t| ≤ 1 → c ≤ ‖𝓕 W t‖)
    (a : ι → ℂ) (freq : ι → ℝ) :
    h ^ 2 * c ^ 2 * (∫ t in Icc (-T) T,
      ‖∑ j, a j * realAdditivePhase (-(freq j * t))‖ ^ 2) ≤
        ∫ x : ℝ, ‖∑ j, a j * W ((x - freq j) / h)‖ ^ 2 := by
  let P := densityLocalizedPolynomial W h hh a freq
  have hi : Integrable (fun t : ℝ => ‖𝓕 P t‖ ^ 2) :=
    density_schwartz_square_integrable (𝓕 P)
  have hl : IntegrableOn (fun t : ℝ => h ^ 2 * c ^ 2 *
      ‖∑ j, a j * realAdditivePhase (-(freq j * t))‖ ^ 2) (Icc (-T) T) := by
    apply ContinuousOn.integrableOn_Icc
    apply Continuous.continuousOn
    unfold realAdditivePhase
    fun_prop
  have hm : (∫ t in Icc (-T) T, h ^ 2 * c ^ 2 *
      ‖∑ j, a j * realAdditivePhase (-(freq j * t))‖ ^ 2) ≤
        ∫ t in Icc (-T) T, ‖𝓕 P t‖ ^ 2 := by
    apply setIntegral_mono_on hl hi.integrableOn measurableSet_Icc
    intro t ht
    exact density_localized_pointwise_bound W c h T hc hh hwindow hW a freq t
      (abs_le.mpr ht)
  rw [integral_const_mul] at hm
  have hb := setIntegral_le_integral (s := Icc (-T) T) hi
    (Filter.Eventually.of_forall (fun t => sq_nonneg ‖𝓕 P t‖))
  apply (hm.trans hb).trans_eq
  rw [SchwartzMap.integral_norm_sq_fourier]
  apply integral_congr_ae
  filter_upwards with x
  rw [show P = densityLocalizedPolynomial W h hh a freq from rfl,
    densityLocalizedPolynomial_apply]

 theorem density_shifted_window_square (W : 𝓢(ℝ, ℂ)) (h : ℝ) (hh : 0 < h) (v : ℝ) :
    (∫ x : ℝ, ‖W ((x - v) / h)‖ ^ 2) = h * ∫ x : ℝ, ‖W x‖ ^ 2 := by
  have ht := integral_add_right_eq_self (μ := volume)
    (fun x : ℝ => ‖W (x / h)‖ ^ 2) (-v)
  simp only [sub_eq_add_neg] at ⊢
  rw [ht]
  simpa only [abs_of_pos hh, smul_eq_mul] using
    Measure.integral_comp_div (fun x : ℝ => ‖W x‖ ^ 2) h

 theorem density_shifted_window_integrable (W : 𝓢(ℝ, ℂ)) (h : ℝ)
    (hh : 0 < h) (v : ℝ) :
    Integrable (fun x : ℝ => ‖W ((x - v) / h)‖ ^ 2) := by
  have hi := density_schwartz_square_integrable
    ((positiveDilate W h⁻¹ (inv_pos.mpr hh)).compSubConstCLM ℂ v)
  simpa only [SchwartzMap.compSubConstCLM_apply, positiveDilate_apply,
    div_eq_inv_mul] using hi

 theorem density_localized_square_integrable {ι : Type*} [Fintype ι]
    (W : 𝓢(ℝ, ℂ)) (h : ℝ) (hh : 0 < h) (a : ι → ℂ) (freq : ι → ℝ) :
    Integrable (fun x : ℝ => ‖∑ j, a j * W ((x - freq j) / h)‖ ^ 2) := by
  simpa only [densityLocalizedPolynomial_apply] using
    density_schwartz_square_integrable (densityLocalizedPolynomial W h hh a freq)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityHybridIntegral
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integrated short-window sieve for complex Dirichlet polynomials -/

namespace Ostmann

open MeasureTheory Set
open scoped BigOperators SchwartzMap FourierTransform Classical

 theorem density_finite_localized_integrable (S : Finset ℕ)
    (W : 𝓢(ℝ, ℂ)) (h : ℝ) (hh : 0 < h) (a : ℕ → ℂ) :
    Integrable (fun x : ℝ => ‖∑ n ∈ S, a n * W ((x - Real.log n) / h)‖ ^ 2) := by
  have hi := density_localized_square_integrable W h hh
    (fun n : S => a n) (fun n : S => Real.log n)
  have he (x : ℝ) : (∑ n : S, a n * W ((x - Real.log n) / h)) =
      ∑ n ∈ S, a n * W ((x - Real.log n) / h) :=
    Finset.sum_coe_sort S (fun n : ℕ => a n * W ((x - Real.log n) / h))
  simpa only [he] using hi

 theorem density_window_energy_integral (S : Finset ℕ)
    (W : 𝓢(ℝ, ℂ)) (h : ℝ) (hh : 0 < h) (a : ℕ → ℂ) :
    (∫ x : ℝ, ∑ n ∈ S, ‖a n * W ((x - Real.log n) / h)‖ ^ 2) =
      h * (∫ x : ℝ, ‖W x‖ ^ 2) * ∑ n ∈ S, ‖a n‖ ^ 2 := by
  rw [integral_finsetSum]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    simp only [norm_mul, mul_pow, integral_const_mul, density_shifted_window_square W h hh]
    ring
  · intro n _
    simpa only [norm_mul, mul_pow] using
      (density_shifted_window_integrable W h hh (Real.log n)).const_mul (‖a n‖ ^ 2)

 theorem density_integrated_localized_sieve (N Q : ℕ) (hQ : 1 ≤ Q)
    (W : 𝓢(ℝ, ℂ)) (h : ℝ) (hh : 0 < h)
    (hW : ∀ y, 1 ≤ |y| → W y = 0) (a : ℕ → ℂ)
    (F : (q : ℕ) → Finset (DirichletCharacter ℂ q))
    (hF : ∀ q ∈ Finset.Icc 1 Q, ∀ χ ∈ F q, χ.IsPrimitive) :
    (∫ x : ℝ, ∑ q ∈ Finset.Icc 1 Q, ∑ χ ∈ F q,
      ‖∑ n ∈ Finset.Icc 1 N, a n * W ((x - Real.log n) / h) * χ (n : ZMod q)‖ ^ 2) ≤
        (2 * N * h + (Q : ℝ) ^ 2 + 2) * h *
          (∫ x : ℝ, ‖W x‖ ^ 2) * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 := by
  have hi : Integrable (fun x : ℝ => (2 * N * h + (Q : ℝ) ^ 2 + 2) *
      ∑ n ∈ Finset.Icc 1 N, ‖a n * W ((x - Real.log n) / h)‖ ^ 2) := by
    apply Integrable.const_mul
    apply integrable_finsetSum
    intro n _
    simpa only [norm_mul, mul_pow] using
      (density_shifted_window_integrable W h hh (Real.log n)).const_mul (‖a n‖ ^ 2)
  have hm := integral_mono_of_nonneg
    (Filter.Eventually.of_forall (fun x => Finset.sum_nonneg (fun _ _ =>
      Finset.sum_nonneg (fun _ _ => sq_nonneg _)))) hi
    (Filter.Eventually.of_forall (fun x => localized_multiplicative_sieve N Q hQ x h hh W hW a F hF))
  rw [integral_const_mul, density_window_energy_integral _ W h hh] at hm
  simpa only [mul_assoc] using hm

 theorem density_hybrid_window (N Q : ℕ) (hQ : 1 ≤ Q)
    (W : 𝓢(ℝ, ℂ)) (c h T : ℝ) (hc : 0 < c) (hh : 0 < h)
    (hwindow : h * T ≤ 1) (hW : ∀ y, 1 ≤ |y| → W y = 0)
    (hWlower : ∀ t, |t| ≤ 1 → c ≤ ‖𝓕 W t‖) (a : ℕ → ℂ)
    (F : (q : ℕ) → Finset (DirichletCharacter ℂ q))
    (hF : ∀ q ∈ Finset.Icc 1 Q, ∀ χ ∈ F q, χ.IsPrimitive) :
    h ^ 2 * c ^ 2 * (∑ q ∈ Finset.Icc 1 Q, ∑ χ ∈ F q,
      ∫ t in Icc (-T) T, ‖∑ n ∈ Finset.Icc 1 N,
        a n * χ (n : ZMod q) * realAdditivePhase (-(Real.log n * t))‖ ^ 2) ≤
      (2 * N * h + (Q : ℝ) ^ 2 + 2) * h *
        (∫ x : ℝ, ‖W x‖ ^ 2) * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 := by
  have hint (q : ℕ) (χ : DirichletCharacter ℂ q) :
      Integrable (fun x : ℝ => ‖∑ n ∈ Finset.Icc 1 N,
        a n * χ (n : ZMod q) * W ((x - Real.log n) / h)‖ ^ 2) :=
    density_finite_localized_integrable _ W h hh _
  have hpoint (q : ℕ) (χ : DirichletCharacter ℂ q) :=
    density_height_window_bound W c h T hc hh hwindow hWlower
      (fun n : Finset.Icc 1 N => a n * χ (n.val : ZMod q))
      (fun n : Finset.Icc 1 N => Real.log n)
  have he1 (q : ℕ) (χ : DirichletCharacter ℂ q) (t : ℝ) :
      (∑ n : Finset.Icc 1 N, a n * χ (n.val : ZMod q) *
        realAdditivePhase (-(Real.log n * t))) =
      ∑ n ∈ Finset.Icc 1 N, a n * χ (n : ZMod q) *
        realAdditivePhase (-(Real.log n * t)) :=
    Finset.sum_coe_sort (Finset.Icc 1 N) (fun n : ℕ =>
      a n * χ (n : ZMod q) * realAdditivePhase (-(Real.log n * t)))
  have he2 (q : ℕ) (χ : DirichletCharacter ℂ q) (x : ℝ) :
      (∑ n : Finset.Icc 1 N, a n * χ (n.val : ZMod q) *
        W ((x - Real.log n) / h)) =
      ∑ n ∈ Finset.Icc 1 N, a n * χ (n : ZMod q) * W ((x - Real.log n) / h) :=
    Finset.sum_coe_sort (Finset.Icc 1 N) (fun n : ℕ =>
      a n * χ (n : ZMod q) * W ((x - Real.log n) / h))
  simp only [he1, he2] at hpoint
  have hs := Finset.sum_le_sum (s := Finset.Icc 1 Q) (fun q _ =>
    Finset.sum_le_sum (s := F q) (fun χ _ => hpoint q χ))
  simp only [← Finset.mul_sum] at hs
  have he : (∑ q ∈ Finset.Icc 1 Q, ∑ χ ∈ F q,
      ∫ x : ℝ, ‖∑ n ∈ Finset.Icc 1 N,
        a n * χ (n : ZMod q) * W ((x - Real.log n) / h)‖ ^ 2) =
      ∫ x : ℝ, ∑ q ∈ Finset.Icc 1 Q, ∑ χ ∈ F q,
        ‖∑ n ∈ Finset.Icc 1 N,
          a n * W ((x - Real.log n) / h) * χ (n : ZMod q)‖ ^ 2 := by
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro q _
      rw [integral_finsetSum _ (fun χ _ => by
        simpa only [mul_right_comm] using hint q χ)]
      apply Finset.sum_congr rfl
      intro χ _
      simp only [mul_right_comm]
    · intro q _
      apply integrable_finsetSum
      intro χ _
      simpa only [mul_right_comm] using hint q χ
  rw [he] at hs
  exact hs.trans (density_integrated_localized_sieve N Q hQ W h hh hW a F hF)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityHybridSieve
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A hybrid large sieve with an absolute constant

The character and height variables are averaged simultaneously. The proof uses
short logarithmic windows and the already proved finite additive large sieve.
-/

namespace Ostmann

open MeasureTheory Set
open scoped BigOperators SchwartzMap FourierTransform Classical

 theorem hybrid_multiplicative_large_sieve :
    ∃ C : ℝ, 0 < C ∧ ∀ N Q : ℕ, 1 ≤ Q → ∀ T : ℝ, 1 ≤ T →
      ∀ a : ℕ → ℂ, ∀ F : (q : ℕ) → Finset (DirichletCharacter ℂ q),
      (∀ q ∈ Finset.Icc 1 Q, ∀ χ ∈ F q, χ.IsPrimitive) →
      (∑ q ∈ Finset.Icc 1 Q, ∑ χ ∈ F q,
        ∫ t in Icc (-T) T, ‖∑ n ∈ Finset.Icc 1 N,
          a n * χ (n : ZMod q) * realAdditivePhase (-(Real.log n * t))‖ ^ 2) ≤
        C * ((N : ℝ) + (Q : ℝ) ^ 2 * T) * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 := by
  obtain ⟨c, W, hc, hW, _, hWlower⟩ := exists_density_localizer
  let K : ℝ := ∫ x : ℝ, ‖W x‖ ^ 2
  have hK : 0 ≤ K := integral_nonneg (fun _ => sq_nonneg _)
  refine ⟨3 * (K + 1) / c ^ 2, by positivity, ?_⟩
  intro N Q hQ T hT a F hF
  have hTpos : 0 < T := by linarith
  have hc2 : 0 < c ^ 2 := pow_pos hc 2
  have hh : 0 < T⁻¹ := inv_pos.mpr hTpos
  have hb := density_hybrid_window N Q hQ W c T⁻¹ T hc hh
    (by rw [inv_mul_cancel₀ hTpos.ne']) hW hWlower a F hF
  let E : ℝ := ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2
  have hE : 0 ≤ E := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hd : 0 < T⁻¹ ^ 2 * c ^ 2 := mul_pos (pow_pos hh 2) hc2
  have hb' := (le_div_iff₀' hd).mpr hb
  have hid : ((2 * (N : ℝ) * T⁻¹ + (Q : ℝ) ^ 2 + 2) * T⁻¹ * K * E) /
      (T⁻¹ ^ 2 * c ^ 2) =
        (K / c ^ 2) * (2 * N + ((Q : ℝ) ^ 2 + 2) * T) * E := by
    field_simp
    ring
  change _ ≤ ((2 * (N : ℝ) * T⁻¹ + (Q : ℝ) ^ 2 + 2) * T⁻¹ * K * E) /
    (T⁻¹ ^ 2 * c ^ 2) at hb'
  rw [hid] at hb'
  apply hb'.trans
  have hq : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hq2 : (1 : ℝ) ≤ (Q : ℝ) ^ 2 := by nlinarith
  have hsize : 2 * (N : ℝ) + ((Q : ℝ) ^ 2 + 2) * T ≤
      3 * ((N : ℝ) + (Q : ℝ) ^ 2 * T) := by
    nlinarith [Nat.cast_nonneg (α := ℝ) N, mul_nonneg (by linarith : 0 ≤ (Q : ℝ) ^ 2 - 1) hTpos.le]
  have hbase : 0 ≤ (N : ℝ) + (Q : ℝ) ^ 2 * T := by positivity
  have hfirst := mul_le_mul_of_nonneg_left hsize (div_nonneg hK hc2.le)
  have hsecond := mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right (by linarith : K ≤ K + 1) hc2.le)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) hbase)
  have hbound : (K / c ^ 2) * (2 * (N : ℝ) + ((Q : ℝ) ^ 2 + 2) * T) ≤
      (3 * (K + 1) / c ^ 2) * ((N : ℝ) + (Q : ℝ) ^ 2 * T) := by
    calc
      _ ≤ (K / c ^ 2) * (3 * ((N : ℝ) + (Q : ℝ) ^ 2 * T)) := hfirst
      _ ≤ ((K + 1) / c ^ 2) * (3 * ((N : ℝ) + (Q : ℝ) ^ 2 * T)) := hsecond
      _ = _ := by ring
  exact mul_le_mul_of_nonneg_right hbound hE

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityCharacterFamily
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Grouping the actual primitive characters by their conductors -/

namespace Ostmann

open MeasureTheory Set
open scoped BigOperators Classical

 theorem densityCharacterFamily_injective (F : Finset PrimitiveComplexCharacter) (q : ℕ) :
    Function.Injective (fun χ : {χ // χ ∈ F.filter (fun χ => χ.modulus = q)} =>
      χ.val.atModulus q (Finset.mem_filter.mp χ.property).2) := by
  intro χ ψ he
  apply Subtype.ext
  have hχ := (Finset.mem_filter.mp χ.property).2
  have hψ := (Finset.mem_filter.mp ψ.property).2
  obtain ⟨⟨m, hm, c, hc, hn⟩, hmem⟩ := χ
  obtain ⟨⟨n, hp, d, hd, hd'⟩, hmem'⟩ := ψ
  dsimp at hχ hψ
  subst m
  subst n
  dsimp [PrimitiveComplexCharacter.atModulus] at he
  cases he
  rfl

 theorem densityCharacterFamily_primitive (F : Finset PrimitiveComplexCharacter) (q : ℕ)
    (χ : DirichletCharacter ℂ q) (hχ : χ ∈ densityCharacterFamily F q) : χ.IsPrimitive := by
  obtain ⟨ψ, _, rfl⟩ := Finset.mem_image.mp hχ
  have hψ := (Finset.mem_filter.mp ψ.property).2
  obtain ⟨⟨n, hp, d, hd, hn⟩, hmem⟩ := ψ
  dsimp at hψ
  subst n
  exact hd

 theorem densityCharacterFamily_sum (F : Finset PrimitiveComplexCharacter) (Q : ℕ)
    (hF : ∀ χ ∈ F, χ.modulus ≤ Q)
    (f : (q : ℕ) → DirichletCharacter ℂ q → ℝ) :
    (∑ χ ∈ F, f χ.modulus χ.character) =
      ∑ q ∈ Finset.Icc 1 Q, ∑ χ ∈ densityCharacterFamily F q, f q χ := by
  have hm : ∀ χ ∈ F, χ.modulus ∈ Finset.Icc 1 Q := fun χ hχ =>
    Finset.mem_Icc.mpr ⟨χ.positive, hF χ hχ⟩
  rw [← Finset.sum_fiberwise_of_maps_to hm]
  apply Finset.sum_congr rfl
  intro q _
  rw [densityCharacterFamily, Finset.sum_image]
  · rw [← Finset.sum_attach (F.filter fun χ => χ.modulus = q)]
    apply Finset.sum_congr rfl
    intro χ _
    have hχ := (Finset.mem_filter.mp χ.property).2
    obtain ⟨⟨n, hp, d, hd, hn⟩, hmem⟩ := χ
    dsimp at hχ
    subst n
    rfl
  · exact fun χ _ ψ _ he => densityCharacterFamily_injective F q he

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensitySeparatedSampling
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Disjoint unit windows for separated height samples -/

namespace Ostmann

open MeasureTheory Set
open scoped BigOperators Classical

 theorem density_disjoint_sample_windows {ι : Type*} (S : Finset ι) (t : ι → ℝ)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → 1 ≤ |t i - t j|) :
    Set.Pairwise (↑S) (fun i j => Disjoint (Ioc (t i - 1 / 2) (t i + 1 / 2))
      (Ioc (t j - 1 / 2) (t j + 1 / 2))) := by
  intro i hi j hj hij
  apply Set.disjoint_left.mpr
  intro x hx hy
  have hh := hsep i hi j hj hij
  have hn : |t i - t j| < 1 := abs_lt.mpr ⟨by linarith [hx.2, hy.1], by linarith [hy.2, hx.1]⟩
  linarith

 theorem density_sample_window_integrals {ι : Type*} (S : Finset ι) (t : ι → ℝ)
    (T : ℝ) (hT : ∀ i ∈ S, |t i| ≤ T)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → 1 ≤ |t i - t j|)
    (F : ℝ → ℝ) (hF : Continuous F) (hFnon : ∀ x, 0 ≤ F x) :
    (∑ i ∈ S, ∫ x in t i - 1 / 2..t i + 1 / 2, F x) ≤
      ∫ x in Icc (-T - 1) (T + 1), F x := by
  have he : (∑ i ∈ S, ∫ x in t i - 1 / 2..t i + 1 / 2, F x) =
      ∫ x in ⋃ i ∈ S, Ioc (t i - 1 / 2) (t i + 1 / 2), F x := by
    have horder (i : ι) : t i - 1 / 2 ≤ t i + 1 / 2 := by linarith
    simp_rw [intervalIntegral.integral_of_le (horder _)]
    exact (integral_biUnion_finset S (fun _ _ => measurableSet_Ioc)
      (density_disjoint_sample_windows S t hsep)
      (fun i _ => hF.integrableOn_Icc.mono_set Ioc_subset_Icc_self)).symm
  rw [he]
  apply setIntegral_mono_set hF.integrableOn_Icc (Filter.Eventually.of_forall hFnon)
  apply Filter.Eventually.of_forall
  intro x hx
  obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hx
  have ht := abs_le.mp (hT i hi)
  exact ⟨by linarith [hxi.1], by linarith [hxi.2]⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityVerticalPolynomial
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Vertical Dirichlet polynomials with the actual complex powers -/

namespace Ostmann

open scoped BigOperators Classical

 theorem density_vertical_term (a : ℂ) (σ t : ℝ) (n : ℕ) (hn : 0 < n) :
    a / (n : ℂ) ^ densityVerticalPoint σ t =
      (a / (n : ℂ) ^ (σ : ℂ)) * realAdditivePhase (-(Real.log n * t)) := by
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hlog : Complex.log (n : ℂ) = (Real.log n : ℂ) := by
    simpa only [Complex.ofReal_natCast] using
      (Complex.ofReal_log (show (0 : ℝ) ≤ n by positivity)).symm
  have he : ((n : ℂ) ^ (2 * (Real.pi : ℂ) * Complex.I * t))⁻¹ =
      realAdditivePhase (-(Real.log n * t)) := by
    rw [Complex.cpow_def_of_ne_zero hnC, ← Complex.exp_neg, hlog]
    unfold realAdditivePhase
    congr 1
    push_cast
    ring
  rw [densityVerticalPoint, Complex.cpow_add _ _ hnC, div_mul_eq_div_mul_one_div,
    one_div, he]

 theorem densityVerticalCoeff_norm (a : ℕ → ℂ) (σ : ℝ) (n : ℕ) (hn : 0 < n) :
    ‖densityVerticalCoeff a σ n‖ = ‖a n‖ / (n : ℝ) ^ σ := by
  rw [densityVerticalCoeff, norm_div]
  congr 1
  rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
  rfl

 theorem densityVerticalCoeff_half_square (a : ℕ → ℂ) (n : ℕ) (hn : 0 < n) :
    ‖densityVerticalCoeff a (1 / 2) n‖ ^ 2 = ‖a n‖ ^ 2 / n := by
  have hden : ((n : ℝ) ^ (1 / 2 : ℝ)) ^ 2 = n := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num
  rw [densityVerticalCoeff_norm a _ n hn, div_pow, hden]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityDyadicShells
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A disjoint dyadic decomposition of the whole height line -/

namespace Ostmann

open Set Filter
open scoped Topology

 theorem densityHeightBall_mem (T : ℝ) (j : ℕ) (x : ℝ) :
    x ∈ densityHeightBall T j ↔ |x| ≤ (2 : ℝ) ^ j * T := by
  exact abs_le.symm

 theorem densityHeightBall_mono (T : ℝ) (hT : 0 ≤ T) {i j : ℕ} (hij : i ≤ j) :
    densityHeightBall T i ⊆ densityHeightBall T j := by
  intro x hx
  rw [densityHeightBall_mem] at hx ⊢
  exact hx.trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hij) hT)

 theorem densityHeightShell_measurable (T : ℝ) (j : ℕ) : MeasurableSet (densityHeightShell T j) := by
  cases j with
  | zero => exact measurableSet_Icc
  | succ j => exact measurableSet_Icc.diff measurableSet_Icc

 theorem densityHeightShell_subset (T : ℝ) (j : ℕ) :
    densityHeightShell T j ⊆ densityHeightBall T j := by
  cases j with
  | zero => exact Set.Subset.rfl
  | succ j => exact Set.sdiff_subset

 theorem densityHeightShell_disjoint (T : ℝ) (hT : 0 ≤ T) :
    Pairwise (fun i j => Disjoint (densityHeightShell T i) (densityHeightShell T j)) := by
  have hd (i j : ℕ) (hij : i < j) : Disjoint (densityHeightShell T i) (densityHeightShell T j) := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
    apply Set.disjoint_left.mpr
    intro x hx hy
    exact hy.2 (densityHeightBall_mono T hT (by omega) (densityHeightShell_subset T i hx))
  intro i j hij
  rcases lt_or_gt_of_ne hij with h | h
  · exact hd i j h
  · exact (hd j i h).symm

 theorem densityHeightShell_cover (T : ℝ) (hT : 0 < T) :
    (⋃ j : ℕ, densityHeightShell T j) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  have hex : ∃ j : ℕ, |x| ≤ (2 : ℝ) ^ j * T := by
    have ht : Tendsto (fun j : ℕ => (2 : ℝ) ^ j * T) atTop atTop :=
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).atTop_mul_const hT
    obtain ⟨j, hj⟩ := (ht.eventually (eventually_ge_atTop |x|)).exists
    exact ⟨j, hj⟩
  let j := Nat.find hex
  have hj : |x| ≤ (2 : ℝ) ^ j * T := Nat.find_spec hex
  apply Set.mem_iUnion.mpr
  refine ⟨j, ?_⟩
  cases he : j with
  | zero => exact (densityHeightBall_mem T 0 x).mpr (by simpa only [he] using hj)
  | succ k =>
    change x ∈ densityHeightBall T (k + 1) \ densityHeightBall T k
    refine ⟨(densityHeightBall_mem T (k + 1) x).mpr (by simpa only [he] using hj), ?_⟩
    rw [densityHeightBall_mem]
    exact Nat.find_min hex (by omega : k < Nat.find hex)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityKernelPacking
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The cubic detector kernel on separated ordinates -/

namespace Ostmann

open scoped BigOperators

 theorem densityCubicWeight_nonneg (u : ℝ) : 0 ≤ densityCubicWeight u := by
  unfold densityCubicWeight
  positivity

 theorem densityCubicWeight_le_one (u : ℝ) : densityCubicWeight u ≤ 1 := by
  unfold densityCubicWeight
  apply (div_le_one (by positivity)).mpr
  nlinarith [abs_nonneg u, sq_nonneg |u|]

 theorem densityCubicWeight_le_inverse_square (u : ℝ) (hu : u ≠ 0) :
    densityCubicWeight u ≤ 1 / u ^ 2 := by
  unfold densityCubicWeight
  apply one_div_le_one_div_of_le (sq_pos_of_ne_zero hu)
  have he : u ^ 2 = |u| ^ 2 := (sq_abs u).symm
  rw [he]
  nlinarith [abs_nonneg u, sq_nonneg |u|]

 theorem densityCubicWeight_rpow (u : ℝ) :
    densityCubicWeight u = (1 + |u|) ^ (-(3 : ℝ)) := by
  rw [Real.rpow_neg (by positivity), Real.rpow_ofNat]
  simp [densityCubicWeight]

 theorem densityCubicWeight_separated_sum (S : Finset ℝ)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 ≤ |x - y|) (v : ℝ) :
    (∑ x ∈ S, densityCubicWeight (v - x)) ≤ 1 + 4 * Real.pi ^ 2 / 3 := by
  classical
  let A := S.filter (fun x => |v - x| < 1 / 2)
  let B := S.filter (fun x => ¬ |v - x| < 1 / 2)
  have hA : A.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro x hx y hy
    by_contra hxy
    have hx' := Finset.mem_filter.mp hx
    have hy' := Finset.mem_filter.mp hy
    have hd := hsep x hx'.1 y hy'.1 hxy
    have ht : |x - y| ≤ |v - x| + |v - y| := by
      calc
        _ = |(v - y) - (v - x)| := by congr 1; ring
        _ ≤ |v - y| + |v - x| := by
          simpa only [sub_eq_add_neg, abs_neg] using abs_add_le (v - y) (-(v - x))
        _ = _ := by ring
    linarith
  have hnear : (∑ x ∈ A, densityCubicWeight (v - x)) ≤ 1 := by
    calc
      _ ≤ ∑ _x ∈ A, (1 : ℝ) := Finset.sum_le_sum (fun x _ => densityCubicWeight_le_one (v - x))
      _ = (A.card : ℝ) := by simp
      _ ≤ 1 := by exact_mod_cast hA
  let R := B.image (fun x => v - x)
  have hinj : Function.Injective (fun x : ℝ => v - x) := by
    intro x y h
    linarith
  have hRfirst : ∀ x ∈ R, (1 / 2 : ℝ) ≤ |x| := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    exact le_of_not_gt (Finset.mem_filter.mp hy).2
  have hRsep : ∀ x ∈ R, ∀ y ∈ R, x ≠ y → (1 / 2 : ℝ) ≤ |x - y| := by
    intro x hx y hy hxy
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
    have hab : a ≠ b := fun h => hxy (congrArg (fun z => v - z) h)
    have h := hsep a (Finset.mem_filter.mp ha).1 b (Finset.mem_filter.mp hb).1 hab
    have he : |(v - a) - (v - b)| = |a - b| := by
      rw [show (v - a) - (v - b) = -(a - b) by ring, abs_neg]
    rw [he]
    linarith
  have hfar := separated_set_inverse_squares R (1 / 2) (by norm_num) hRfirst hRsep
  have hsumR : (∑ x ∈ B, 1 / (v - x) ^ 2) = ∑ x ∈ R, 1 / x ^ 2 := by
    rw [Finset.sum_image]
    exact fun x _ y _ h => hinj h
  have hB : (∑ x ∈ B, densityCubicWeight (v - x)) ≤ 4 * Real.pi ^ 2 / 3 := by
    calc
      _ ≤ ∑ x ∈ B, 1 / (v - x) ^ 2 := by
        apply Finset.sum_le_sum
        intro x hx
        apply densityCubicWeight_le_inverse_square
        intro he
        have h := (Finset.mem_filter.mp hx).2
        simp only [he, abs_zero] at h
        norm_num at h
      _ = ∑ x ∈ R, 1 / x ^ 2 := hsumR
      _ ≤ Real.pi ^ 2 / (3 * (1 / 2) ^ 2) := hfar
      _ = _ := by ring
  have hsplit := Finset.sum_filter_add_sum_filter_not S
    (fun x => |v - x| < 1 / 2) (fun x => densityCubicWeight (v - x))
  change (∑ x ∈ A, densityCubicWeight (v - x)) +
    (∑ x ∈ B, densityCubicWeight (v - x)) = _ at hsplit
  linarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityHeightWeight
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Summable cubic weights on the dyadic height shells -/

namespace Ostmann

open Set

 theorem densityHeightWeight_nonneg (T x : ℝ) : 0 ≤ densityHeightWeight T x :=
  densityCubicWeight_nonneg _

 theorem densityHeightWeight_continuous (T : ℝ) : Continuous (densityHeightWeight T) := by
  unfold densityHeightWeight densityCubicWeight
  exact continuous_const.div
    ((continuous_const.add (continuous_id.div_const T).abs).pow 3) (fun x => by positivity)

 theorem densityHeightWeight_shell (T : ℝ) (hT : 0 < T) (j : ℕ) (x : ℝ)
    (hx : x ∈ densityHeightShell T (j + 1)) :
    densityHeightWeight T x ≤ (1 / 8 : ℝ) ^ j := by
  have ha : (2 : ℝ) ^ j * T < |x| := by
    have h := hx.2
    rw [densityHeightBall_mem] at h
    exact lt_of_not_ge h
  have hd : (2 : ℝ) ^ j ≤ 1 + |x / T| := by
    rw [abs_div, abs_of_pos hT]
    have hh : (2 : ℝ) ^ j < |x| / T := (lt_div_iff₀ hT).mpr ha
    linarith
  calc
    densityHeightWeight T x ≤ 1 / ((2 : ℝ) ^ j) ^ 3 := by
      apply one_div_le_one_div_of_le (by positivity)
      exact pow_le_pow_left₀ (by positivity) hd 3
    _ = (1 / 8 : ℝ) ^ j := by
      rw [← pow_mul, Nat.mul_comm, pow_mul, one_div_pow]
      norm_num

 theorem density_height_energy_summable (k : ℕ) :
    Summable (fun j : ℕ => (j + 2 : ℝ) ^ k * (1 / 4 : ℝ) ^ j) := by
  have h0 : Summable (fun j : ℕ => (j : ℝ) ^ k * (1 / 4 : ℝ) ^ j) :=
    summable_pow_mul_geometric_of_norm_lt_one k (by norm_num : ‖(1 / 4 : ℝ)‖ < 1)
  have h : Summable (fun j : ℕ => ((j + 2 : ℕ) : ℝ) ^ k * (1 / 4 : ℝ) ^ (j + 2)) :=
    (summable_nat_add_iff 2).mpr h0
  have hm := h.mul_right (16 : ℝ)
  convert hm using 1
  all_goals try with_reducible_and_instances rfl
  funext j
  push_cast
  rw [pow_add]
  ring

 theorem densityHeightEnergyConstant_pos (k : ℕ) : 0 < densityHeightEnergyConstant k := by
  have hh : 0 ≤ ∑' j : ℕ, (j + 2 : ℝ) ^ k * (1 / 4 : ℝ) ^ j := tsum_nonneg (fun _ => by positivity)
  unfold densityHeightEnergyConstant
  linarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityKernelHeightPacking
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The translated detector kernels keep the original height scale -/

namespace Ostmann

open MeasureTheory Set
open scoped BigOperators

 theorem density_separated_card (S : Finset ℝ) (T : ℝ) (hT : 0 ≤ T)
    (hS : ∀ x ∈ S, |x| ≤ T)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 ≤ |x - y|) :
    (S.card : ℝ) ≤ 2 * (T + 1) := by
  have h := density_sample_window_integrals S id T hS hsep (fun _ => (1 : ℝ))
    continuous_const (fun _ => by norm_num)
  simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one,
    show ∀ x : ℝ, x + 1 / 2 - (x - 1 / 2) = 1 by intro x; ring,
    Finset.sum_const, nsmul_eq_mul, mul_one] at h
  have he : (∫ _x in Icc (-T - 1) (T + 1), (1 : ℝ)) = 2 * (T + 1) := by
    rw [integral_const, smul_eq_mul, mul_one, Measure.real, Measure.restrict_apply_univ,
      Real.volume_Icc]
    simp only [ENNReal.toReal_ofReal (by linarith : 0 ≤ T + 1 - (-T - 1))]
    ring
  rwa [he] at h

 theorem densityHeightWeight_eq (T x : ℝ) (hT : 0 < T) :
    densityHeightWeight T x = T ^ 3 / (T + |x|) ^ 3 := by
  unfold densityHeightWeight densityCubicWeight
  rw [abs_div, abs_of_pos hT]
  field_simp

 theorem density_kernel_far_bound (T v x : ℝ) (hT : 0 < T)
    (hx : |x| ≤ T) (hv : 2 * T < |v|) :
    densityCubicWeight (v - x) ≤ 64 / (T + |v|) ^ 3 := by
  have ht : |v| ≤ |v - x| + |x| := by
    simpa only [sub_add_cancel] using abs_add_le (v - x) x
  have hd : T + |v| ≤ 4 * (1 + |v - x|) := by linarith [abs_nonneg (v - x)]
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ T + |v|) hd 3
  unfold densityCubicWeight
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith

 theorem density_kernel_height_packing (S : Finset ℝ) (T : ℝ) (hT : 1 ≤ T)
    (hS : ∀ x ∈ S, |x| ≤ T)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 ≤ |x - y|) (v : ℝ) :
    (∑ x ∈ S, densityCubicWeight (v - x)) ≤
      (256 + 27 * (1 + 4 * Real.pi ^ 2 / 3)) * densityHeightWeight T v := by
  have hTp : 0 < T := by linarith
  have hw : 0 ≤ densityHeightWeight T v := densityHeightWeight_nonneg T v
  have hK : 0 ≤ 1 + 4 * Real.pi ^ 2 / 3 := by positivity
  by_cases hv : |v| ≤ 2 * T
  · have hh : |v / T| ≤ 2 := by
      rw [abs_div, abs_of_pos hTp]
      exact (div_le_iff₀ hTp).mpr hv
    have hweight : 1 ≤ 27 * densityHeightWeight T v := by
      unfold densityHeightWeight densityCubicWeight
      have hd : (1 + |v / T|) ^ 3 ≤ 27 := by
        have h := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + |v / T|)
          (by linarith : 1 + |v / T| ≤ 3) 3
        norm_num at h ⊢
        exact h
      rw [mul_one_div]
      apply (le_div_iff₀ (by positivity : 0 < (1 + |v / T|) ^ 3)).mpr
      nlinarith
    calc
      _ ≤ 1 + 4 * Real.pi ^ 2 / 3 := densityCubicWeight_separated_sum S hsep v
      _ ≤ (1 + 4 * Real.pi ^ 2 / 3) * (27 * densityHeightWeight T v) :=
        le_mul_of_one_le_right hK hweight
      _ ≤ _ := by nlinarith
  · have hv' : 2 * T < |v| := lt_of_not_ge hv
    have hc : (S.card : ℝ) ≤ 4 * T := (density_separated_card S T hTp.le hS hsep).trans (by linarith)
    have hTc : T ≤ T ^ 3 := by nlinarith [sq_nonneg (T - 1)]
    calc
      _ ≤ ∑ _x ∈ S, 64 / (T + |v|) ^ 3 :=
        Finset.sum_le_sum (fun x hx => density_kernel_far_bound T v x hTp (hS x hx) hv')
      _ = (S.card : ℝ) * (64 / (T + |v|) ^ 3) := by simp
      _ ≤ (4 * T) * (64 / (T + |v|) ^ 3) := mul_le_mul_of_nonneg_right hc (by positivity)
      _ = 256 * T / (T + |v|) ^ 3 := by ring
      _ ≤ 256 * T ^ 3 / (T + |v|) ^ 3 :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hTc (by norm_num)) (by positivity)
      _ = 256 * densityHeightWeight T v := by rw [densityHeightWeight_eq T v hTp]; ring
      _ ≤ _ := by nlinarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityPackedMoment
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Summing translated moments over characterwise separated ordinates -/

namespace Ostmann

open MeasureTheory
open scoped BigOperators Classical

 theorem densityKernelPackingConstant_pos : 0 < densityKernelPackingConstant := by
  unfold densityKernelPackingConstant
  positivity

 theorem density_indexed_kernel_packing {ι : Type*} (S : Finset ι) (t : ι → ℝ)
    (T : ℝ) (hT : 1 ≤ T) (ht : ∀ i ∈ S, |t i| ≤ T)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → 1 ≤ |t i - t j|) (v : ℝ) :
    (∑ i ∈ S, densityCubicWeight (v - t i)) ≤ densityKernelPackingConstant * densityHeightWeight T v := by
  classical
  have hinj : Set.InjOn t S := by
    intro i hi j hj he
    by_contra hij
    have h := hsep i hi j hj hij
    rw [he, sub_self, abs_zero] at h
    norm_num at h
  have hb := density_kernel_height_packing (S.image t) T hT
    (by intro x hx; obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx; exact ht i hi)
    (by
      intro x hx y hy hxy
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hy
      exact hsep i hi j hj (fun he => hxy (congrArg t he))) v
  rwa [Finset.sum_image (fun _ hi _ hj he => hinj hi hj he)] at hb

 theorem density_packed_pointwise {ι κ : Type*} (S : Finset ι) (c : ι → κ) (t : ι → ℝ)
    (T : ℝ) (hT : 1 ≤ T) (ht : ∀ i ∈ S, |t i| ≤ T)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, c i = c j → i ≠ j → 1 ≤ |t i - t j|)
    (f : κ → ℝ → ℝ) (hf0 : ∀ a v, 0 ≤ f a v) (v : ℝ) :
    (∑ i ∈ S, densityCubicWeight (v - t i) * f (c i) v) ≤
      densityKernelPackingConstant * (densityHeightWeight T v * ∑ a ∈ S.image c, f a v) := by
  classical
  have hmap : ∀ i ∈ S, c i ∈ S.image c := fun i hi => Finset.mem_image.mpr ⟨i, hi, rfl⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmap]
  calc
    _ = ∑ a ∈ S.image c, (∑ i ∈ S.filter (fun i => c i = a), densityCubicWeight (v - t i)) * f a v := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      rw [(Finset.mem_filter.mp hi).2]
    _ ≤ ∑ a ∈ S.image c, (densityKernelPackingConstant * densityHeightWeight T v) * f a v := by
      apply Finset.sum_le_sum
      intro a _
      apply mul_le_mul_of_nonneg_right _ (hf0 a v)
      apply density_indexed_kernel_packing _ t T hT
      · intro i hi
        exact ht i (Finset.mem_filter.mp hi).1
      · intro i hi j hj hij
        have hi' := Finset.mem_filter.mp hi
        have hj' := Finset.mem_filter.mp hj
        exact hsep i hi'.1 j hj'.1 (hi'.2.trans hj'.2.symm) hij
    _ = _ := by rw [← Finset.mul_sum]; ring

 theorem density_packed_moment {ι κ : Type*} (S : Finset ι) (c : ι → κ) (t : ι → ℝ)
    (T : ℝ) (hT : 1 ≤ T) (ht : ∀ i ∈ S, |t i| ≤ T)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, c i = c j → i ≠ j → 1 ≤ |t i - t j|)
    (f : κ → ℝ → ℝ) (hf : ∀ a, Continuous (f a)) (hf0 : ∀ a v, 0 ≤ f a v)
    (hint : Integrable (fun v => densityHeightWeight T v * ∑ a ∈ S.image c, f a v)) :
    (∀ i ∈ S, Integrable (fun v => densityCubicWeight (v - t i) * f (c i) v)) ∧
    (∑ i ∈ S, ∫ v, densityCubicWeight (v - t i) * f (c i) v) ≤
      densityKernelPackingConstant * ∫ v, densityHeightWeight T v * ∑ a ∈ S.image c, f a v := by
  classical
  have hc : Continuous densityCubicWeight := by
    unfold densityCubicWeight
    exact continuous_const.div ((continuous_const.add continuous_abs).pow 3) (fun _ => by positivity)
  have hi (i : ι) (hi : i ∈ S) : Integrable (fun v => densityCubicWeight (v - t i) * f (c i) v) := by
    apply (hint.const_mul densityKernelPackingConstant).mono'
      (((hc.comp (continuous_id.sub continuous_const)).mul (hf (c i))).aestronglyMeasurable)
    filter_upwards with v
    change ‖densityCubicWeight (v - t i) * f (c i) v‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (densityCubicWeight_nonneg _) (hf0 _ _))]
    exact (Finset.single_le_sum
      (f := fun j => densityCubicWeight (v - t j) * f (c j) v)
      (fun j _ => mul_nonneg (densityCubicWeight_nonneg _) (hf0 _ _)) hi).trans
      (density_packed_pointwise S c t T hT ht hsep f hf0 v)
  refine ⟨hi, ?_⟩
  rw [← integral_finsetSum S hi, ← integral_const_mul]
  apply integral_mono (integrable_finsetSum S hi) (hint.const_mul _)
  intro v
  exact density_packed_pointwise S c t T hT ht hsep f hf0 v

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityDetectorAnalytic
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Cancellation of the detector contour pole at an actual L-function zero -/

namespace Ostmann

open Complex Set
open scoped BigOperators

 theorem densityMollifier_shift_analytic (χ : PrimitiveComplexCharacter) (X : ℕ)
    (s w : ℂ) : AnalyticAt ℂ (fun z => densityMollifier X χ.character (s + z)) w := by
  unfold densityMollifier
  apply Finset.analyticAt_fun_sum
  intro n hn
  have hnp : 0 < n := (Finset.mem_Icc.mp hn).1
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hnp.ne'
  have hp := ((differentiable_id.const_cpow (Or.inl hnC)).analyticAt (s + w)).comp
    (analyticAt_const.add analyticAt_id : AnalyticAt ℂ (fun z : ℂ => s + z) w)
  exact analyticAt_const.div hp (Complex.cpow_ne_zero_iff.mpr (Or.inl hnC))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityMollifierMean
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The mean square of the actual critical-line Möbius polynomial -/

namespace Ostmann

open MeasureTheory Set
open scoped BigOperators Classical

 theorem densityMollifier_vertical {q : ℕ} (X : ℕ) (χ : DirichletCharacter ℂ q) (σ t : ℝ) :
    densityMollifier X χ (densityVerticalPoint σ t) =
      ∑ n ∈ Finset.Icc 1 X,
        densityVerticalCoeff (fun n => (ArithmeticFunction.moebius n : ℂ)) σ n *
          χ (n : ZMod q) * realAdditivePhase (-(Real.log n * t)) := by
  unfold densityMollifier
  apply Finset.sum_congr rfl
  intro n hn
  rw [density_vertical_term _ σ t n (Finset.mem_Icc.mp hn).1]
  unfold densityVerticalCoeff
  ring

 theorem density_mobius_half_energy (X : ℕ) :
    (∑ n ∈ Finset.Icc 1 X,
      ‖densityVerticalCoeff (fun n => (ArithmeticFunction.moebius n : ℂ)) (1 / 2) n‖ ^ 2) ≤
        1 + Real.log X := by
  have hsum : (∑ n ∈ Finset.Icc 1 X,
      ‖densityVerticalCoeff (fun n => (ArithmeticFunction.moebius n : ℂ)) (1 / 2) n‖ ^ 2) ≤
        ∑ n ∈ Finset.Icc 1 X, (n : ℝ)⁻¹ := by
    apply Finset.sum_le_sum
    intro n hn
    rw [densityVerticalCoeff_half_square _ n (Finset.mem_Icc.mp hn).1]
    have hm : ‖(ArithmeticFunction.moebius n : ℂ)‖ ≤ 1 := by
      norm_cast
      exact ArithmeticFunction.abs_moebius_le_one
    have hsq : ‖(ArithmeticFunction.moebius n : ℂ)‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg (ArithmeticFunction.moebius n : ℂ)]
    simpa only [one_div] using div_le_div_of_nonneg_right hsq (Nat.cast_nonneg n)
  apply hsum.trans
  simpa only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    using harmonic_le_one_add_log X

 theorem critical_mollifier_mean :
    ∃ C : ℝ, 0 < C ∧ ∀ X Q : ℕ, 1 ≤ Q → ∀ T : ℝ, 1 ≤ T →
      ∀ F : (q : ℕ) → Finset (DirichletCharacter ℂ q),
      (∀ q ∈ Finset.Icc 1 Q, ∀ χ ∈ F q, χ.IsPrimitive) →
      (∑ q ∈ Finset.Icc 1 Q, ∑ χ ∈ F q,
        ∫ t in Icc (-T) T, ‖densityMollifier X χ (densityVerticalPoint (1 / 2) t)‖ ^ 2) ≤
          C * ((X : ℝ) + (Q : ℝ) ^ 2 * T) * (1 + Real.log X) := by
  obtain ⟨C, hC, hmean⟩ := hybrid_multiplicative_large_sieve
  refine ⟨C, hC, ?_⟩
  intro X Q hQ T hT F hF
  have h := hmean X Q hQ T hT
    (densityVerticalCoeff (fun n => (ArithmeticFunction.moebius n : ℂ)) (1 / 2)) F hF
  simp only [← densityMollifier_vertical] at h
  exact h.trans (mul_le_mul_of_nonneg_left (density_mobius_half_energy X) (by positivity))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityMomentCutoff
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The integer cutoff for the actual fourth moment -/

namespace Ostmann

 theorem density_moment_cutoff (Q : ℕ) (hQ : 1 ≤ Q) (T : ℝ) (hT : 2 ≤ T) :
    ∃ N : ℕ, 1 ≤ N ∧ 1 ≤ Real.log N ∧ 10 * (Q : ℝ) * T ≤ N ∧
      (N : ℝ) + (Q : ℝ) ^ 2 * T ≤ 17 * (Q : ℝ) ^ 2 * T ∧
      Real.log N ≤ 5 * Real.log ((Q : ℝ) * T) := by
  let N := ⌈10 * (Q : ℝ) * T⌉₊
  have hq : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hqt : 2 ≤ (Q : ℝ) * T := by nlinarith
  have hscale : 10 * (Q : ℝ) * T ≤ N := Nat.le_ceil _
  have hten : (10 : ℝ) ≤ N := by linarith
  have hN : 1 ≤ N := by exact_mod_cast (show (1 : ℝ) ≤ N by linarith)
  have hupper : (N : ℝ) ≤ 16 * ((Q : ℝ) * T) := by
    have h := Nat.ceil_lt_add_one (by positivity : 0 ≤ 10 * (Q : ℝ) * T)
    change (N : ℝ) < 10 * (Q : ℝ) * T + 1 at h
    linarith
  have hlogN : 1 ≤ Real.log N := by
    have hlog10 : (1 : ℝ) ≤ Real.log 10 := by
      have h := Real.le_log_one_add_of_nonneg (by norm_num : (0 : ℝ) ≤ 9)
      norm_num at h
      linarith
    exact hlog10.trans (Real.log_le_log (by norm_num) hten)
  refine ⟨N, hN, hlogN, hscale, ?_, ?_⟩
  · have hqtA : (Q : ℝ) * T ≤ (Q : ℝ) ^ 2 * T := by
      have h := mul_le_mul_of_nonneg_right hq (by positivity : 0 ≤ (Q : ℝ) * T)
      nlinarith
    linarith
  · have hlqt : Real.log 2 ≤ Real.log ((Q : ℝ) * T) := Real.log_le_log (by norm_num) hqt
    have hlog := Real.log_le_log (show (0 : ℝ) < N by linarith) hupper
    rw [Real.log_mul (by norm_num) (by positivity)] at hlog
    have h16 : Real.log 16 = 4 * Real.log 2 := by
      have h := Real.log_pow (2 : ℝ) 4
      norm_num at h
      exact h
    rw [h16] at hlog
    linarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensitySquareConjugation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Conjugating the actual smoothed square -/

namespace Ostmann

open Complex MeasureTheory
open scoped ComplexConjugate

 theorem density_nat_cpow_conj (q : ℕ) (s : ℂ) :
    (q : ℂ) ^ conj s = conj ((q : ℂ) ^ s) := by
  have ha : (q : ℂ).arg ≠ Real.pi := by
    rw [← Complex.ofReal_natCast, Complex.arg_ofReal_of_nonneg (Nat.cast_nonneg q)]
    exact Real.pi_pos.ne
  simpa only [map_natCast] using Complex.cpow_conj (q : ℂ) s ha

 theorem densityCompletedSquare_inverse_conj (χ : PrimitiveComplexCharacter) (s : ℂ) :
    densityCompletedSquare χ.inverse (conj s) = conj (densityCompletedSquare χ s) := by
  simp only [densityCompletedSquare, PrimitiveComplexCharacter.inverse_modulus,
    χ.inverse_completed_eq_conjugate, Function.comp_apply, Complex.conj_conj,
    density_nat_cpow_conj, map_mul, map_pow]

 theorem densitySquareNormalizer_inverse_conj (χ : PrimitiveComplexCharacter) (s : ℂ) :
    densitySquareNormalizer χ.inverse (conj s) = conj (densitySquareNormalizer χ s) := by
  unfold densitySquareNormalizer
  rw [χ.gammaFactor_inverse_conj, PrimitiveComplexCharacter.inverse_modulus,
    density_nat_cpow_conj, map_mul, map_pow]

 theorem densitySquareContour_inverse_conj (χ : PrimitiveComplexCharacter) (s w : ℂ) :
    densitySquareContour χ.inverse (conj s) (conj w) = conj (densitySquareContour χ s w) := by
  unfold densitySquareContour densitySquareGaussian
  rw [← map_add, densityCompletedSquare_inverse_conj]
  simp only [map_div₀, map_mul]
  rw [← map_pow, Complex.exp_conj]

 theorem densitySquareIntegral_inverse_conj (χ : PrimitiveComplexCharacter) (s : ℂ) :
    densitySquareIntegral χ.inverse (conj s) = conj (densitySquareIntegral χ s) := by
  have he (u : ℝ) : densitySquareContour χ.inverse (conj s) (1 + u * I) =
      conj (densitySquareContour χ s (1 + (-u : ℝ) * I)) := by
    simpa only [map_add, map_one, map_mul, map_neg, Complex.conj_ofReal, Complex.conj_I,
      Complex.ofReal_neg, neg_mul, mul_neg, neg_neg] using
      densitySquareContour_inverse_conj χ s (1 + (-u : ℝ) * I)
  unfold densitySquareIntegral
  simp_rw [he]
  rw [integral_conj]
  have hn := integral_neg_eq_self (fun u : ℝ => densitySquareContour χ s (1 + u * I)) volume
  rw [hn]
  simp only [map_mul, map_inv₀, map_ofNat, Complex.conj_ofReal]

 theorem densitySmoothedSquare_inverse_conj (χ : PrimitiveComplexCharacter) (s : ℂ) :
    densitySmoothedSquare χ.inverse (conj s) = conj (densitySmoothedSquare χ s) := by
  unfold densitySmoothedSquare
  rw [densitySquareIntegral_inverse_conj, densitySquareNormalizer_inverse_conj, map_div₀]

 theorem density_L_fourth_single_bound (χ : PrimitiveComplexCharacter) (s : ℂ)
    (hs : s.re = 1 / 2) :
    ‖χ.L s‖ ^ 4 ≤ 4 * ‖densitySmoothedSquare χ s‖ ^ 2 := by
  have h := density_L_fourth_bound χ s hs
  rw [density_critical_reflection s hs, densitySmoothedSquare_inverse_conj, norm_conj] at h
  linarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityFourthMoment
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual primitive-character fourth moment for the density argument -/

namespace Ostmann

open Complex MeasureTheory Set
open scoped BigOperators Classical

 theorem density_L_fourth_integrable (χ : PrimitiveComplexCharacter) (T : ℝ) :
    Integrable (fun t => ‖χ.L (densityVerticalPoint (1 / 2) t)‖ ^ 4)
      (volume.restrict (Icc (-T) T)) := by
  have hL : Continuous χ.L := continuous_iff_continuousAt.mpr (fun z => (χ.L_analytic z).continuousAt)
  have hs : Continuous (fun t : ℝ => densityVerticalPoint (1 / 2) t) := by
    unfold densityVerticalPoint
    fun_prop
  exact (((hL.comp hs).norm.pow 4).continuousOn).integrableOn_Icc

 theorem density_fourth_moment :
    ∃ C : ℝ, 0 < C ∧ ∀ Q : ℕ, 1 ≤ Q → ∀ T : ℝ, 2 ≤ T →
      ∀ F : Finset PrimitiveComplexCharacter, (∀ χ ∈ F, χ.modulus ≤ Q) →
      (∑ χ ∈ F, ∫ t in Icc (-T) T,
        ‖χ.L (densityVerticalPoint (1 / 2) t)‖ ^ 4) ≤
          C * ((Q : ℝ) ^ 2 * T) * (Real.log ((Q : ℝ) * T)) ^ 6 := by
  obtain ⟨C, hC, hb⟩ := densitySmoothedSquare_mean
  refine ⟨4 * C * 17 * 5 ^ 6, by positivity, ?_⟩
  intro Q hQ T hT F hF
  obtain ⟨N, hN, hL, hscale, hsize, hlog⟩ := density_moment_cutoff Q hQ T hT
  obtain ⟨hi, hm⟩ := hb N Q hN hQ T (by linarith) hL hscale F hF
  have hfirst : (∑ χ ∈ F, ∫ t in Icc (-T) T,
      ‖χ.L (densityVerticalPoint (1 / 2) t)‖ ^ 4) ≤
      4 * (∑ χ ∈ F, ∫ t in Icc (-T) T,
        ‖densitySmoothedSquare χ (densityVerticalPoint (1 / 2) t)‖ ^ 2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro χ hχ
    rw [← integral_const_mul]
    apply integral_mono (density_L_fourth_integrable χ T) ((hi χ hχ).const_mul 4)
    intro t
    exact density_L_fourth_single_bound χ _ (by simp [densityVerticalPoint])
  have hlog0 : 0 ≤ Real.log ((Q : ℝ) * T) := by
    apply Real.log_nonneg
    have hq : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
    nlinarith
  calc
    _ ≤ 4 * (C * ((N : ℝ) + (Q : ℝ) ^ 2 * T) * (Real.log N) ^ 6) :=
      hfirst.trans (mul_le_mul_of_nonneg_left hm (by norm_num))
    _ ≤ 4 * (C * (17 * ((Q : ℝ) ^ 2 * T)) *
        (5 * Real.log ((Q : ℝ) * T)) ^ 6) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply mul_le_mul _ (pow_le_pow_left₀ (by linarith) hlog 6) (by positivity) (by positivity)
      exact mul_le_mul_of_nonneg_left (by simpa only [mul_assoc] using hsize) hC.le
    _ = _ := by ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityWeightedMoment
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A whole-line weighted moment from compact height moments -/

namespace Ostmann

open MeasureTheory Set
open scoped BigOperators

 theorem densityShellBudget_summable (A : ℝ) (k : ℕ) : Summable (densityShellBudget A k) := by
  apply (summable_nat_add_iff 1).mp
  exact (density_height_energy_summable k).mul_left (2 * A)

 theorem densityShellBudget_sum (A : ℝ) (k : ℕ) :
    (∑' j, densityShellBudget A k j) = A * densityHeightEnergyConstant k := by
  rw [(densityShellBudget_summable A k).tsum_eq_zero_add]
  simp only [densityShellBudget]
  rw [tsum_mul_left]
  unfold densityHeightEnergyConstant
  ring

 theorem density_weighted_shell_bound (f : ℝ → ℝ) (hf : Continuous f)
    (hf0 : ∀ x, 0 ≤ f x) (T : ℝ) (hT : 0 < T) (A : ℝ) (k : ℕ)
    (hball : ∀ j : ℕ, (∫ x in densityHeightBall T j, f x) ≤
      A * (2 : ℝ) ^ j * (j + 1 : ℝ) ^ k) (j : ℕ) :
    (∫ x in densityHeightShell T j, densityHeightWeight T x * f x) ≤
      densityShellBudget A k j := by
  have hi (j : ℕ) : IntegrableOn f (densityHeightBall T j) := hf.continuousOn.integrableOn_Icc
  have hiw (j : ℕ) : IntegrableOn (fun x => densityHeightWeight T x * f x) (densityHeightShell T j) :=
    (((densityHeightWeight_continuous T).mul hf).continuousOn.integrableOn_Icc).mono_set
      (densityHeightShell_subset T j)
  cases j with
  | zero =>
    apply (integral_mono (hiw 0) (hi 0) (fun x => ?_)).trans
    · simpa only [densityHeightShell, densityShellBudget, pow_zero, mul_one, Nat.cast_zero, zero_add, one_pow] using hball 0
    · exact mul_le_of_le_one_left (hf0 x) (densityCubicWeight_le_one _)
  | succ j =>
    have hsub : (∫ x in densityHeightShell T (j + 1), f x) ≤
        ∫ x in densityHeightBall T (j + 1), f x :=
      setIntegral_mono_set (hi (j + 1)) (Filter.Eventually.of_forall hf0)
        (Filter.Eventually.of_forall (fun _ hx => densityHeightShell_subset T (j + 1) hx))
    calc
      _ ≤ (1 / 8 : ℝ) ^ j * ∫ x in densityHeightShell T (j + 1), f x := by
        rw [← integral_const_mul]
        apply setIntegral_mono_on (hiw (j + 1))
          (((hi (j + 1)).mono_set (densityHeightShell_subset T (j + 1))).const_mul _)
          (densityHeightShell_measurable T (j + 1))
        intro x hx
        exact mul_le_mul_of_nonneg_right (densityHeightWeight_shell T hT j x hx) (hf0 x)
      _ ≤ (1 / 8 : ℝ) ^ j * (A * (2 : ℝ) ^ (j + 1) * (j + 1 + 1 : ℝ) ^ k) :=
        mul_le_mul_of_nonneg_left (hsub.trans (by
          simpa only [Nat.cast_add, Nat.cast_one] using hball (j + 1))) (by positivity)
      _ = densityShellBudget A k (j + 1) := by
        simp only [densityShellBudget, pow_succ]
        have he : (1 / 8 : ℝ) ^ j * (2 : ℝ) ^ j = (1 / 4 : ℝ) ^ j := by
          rw [← mul_pow]
          norm_num
        rw [show (j + 1 + 1 : ℝ) = j + 2 by ring]
        calc
          _ = 2 * A * (j + 2 : ℝ) ^ k * ((1 / 8 : ℝ) ^ j * (2 : ℝ) ^ j) := by ring
          _ = _ := by rw [he]; ring

 theorem density_weighted_moment (f : ℝ → ℝ) (hf : Continuous f)
    (hf0 : ∀ x, 0 ≤ f x) (T : ℝ) (hT : 0 < T) (A : ℝ) (_hA : 0 ≤ A) (k : ℕ)
    (hball : ∀ j : ℕ, (∫ x in densityHeightBall T j, f x) ≤
      A * (2 : ℝ) ^ j * (j + 1 : ℝ) ^ k) :
    Integrable (fun x => densityHeightWeight T x * f x) ∧
      (∫ x, densityHeightWeight T x * f x) ≤ A * densityHeightEnergyConstant k := by
  let g := fun x => densityHeightWeight T x * f x
  have hg0 (x : ℝ) : 0 ≤ g x := mul_nonneg (densityHeightWeight_nonneg T x) (hf0 x)
  have hi (j : ℕ) : IntegrableOn g (densityHeightShell T j) :=
    (((densityHeightWeight_continuous T).mul hf).continuousOn.integrableOn_Icc).mono_set
      (densityHeightShell_subset T j)
  have hb (j : ℕ) : (∫ x in densityHeightShell T j, g x) ≤ densityShellBudget A k j :=
    density_weighted_shell_bound f hf hf0 T hT A k hball j
  have hsum : Summable (fun j => ∫ x in densityHeightShell T j, g x) :=
    (densityShellBudget_summable A k).of_nonneg_of_le
      (fun j => integral_nonneg (fun x => hg0 x)) hb
  have hnorm : Summable (fun j => ∫ x in densityHeightShell T j, ‖g x‖) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hg0 _)] using hsum
  have hgi := integrableOn_iUnion_of_summable_integral_norm hi hnorm
  rw [densityHeightShell_cover T hT, integrableOn_univ] at hgi
  refine ⟨hgi, ?_⟩
  have he := integral_iUnion (densityHeightShell_measurable T)
    (densityHeightShell_disjoint T hT.le) (show IntegrableOn g (⋃ j, densityHeightShell T j) by
      rwa [densityHeightShell_cover T hT, integrableOn_univ])
  rw [densityHeightShell_cover T hT, setIntegral_univ] at he
  change (∫ x, g x) ≤ _
  rw [he, ← densityShellBudget_sum A k]
  exact hsum.tsum_le_tsum hb (densityShellBudget_summable A k)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityMomentDyadic
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Dyadic height bounds for the actual fourth and mollifier moments -/

namespace Ostmann

open Complex MeasureTheory Set
open scoped BigOperators

 theorem density_dyadic_height_log (Q : ℕ) (hQ : 1 ≤ Q) (T : ℝ) (hT : 2 ≤ T) (j : ℕ) :
    Real.log ((Q : ℝ) * ((2 : ℝ) ^ j * T)) ≤
      (j + 1 : ℝ) * Real.log ((Q : ℝ) * T) := by
  have hq : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hqt : 0 < (Q : ℝ) * T := by positivity
  have hl : Real.log 2 ≤ Real.log ((Q : ℝ) * T) :=
    Real.log_le_log (by norm_num) (by nlinarith)
  calc
    _ = (j : ℝ) * Real.log 2 + Real.log ((Q : ℝ) * T) := by
      rw [show (Q : ℝ) * ((2 : ℝ) ^ j * T) = (2 : ℝ) ^ j * ((Q : ℝ) * T) by ring,
        Real.log_mul (by positivity) hqt.ne', Real.log_pow]
    _ ≤ (j : ℝ) * Real.log ((Q : ℝ) * T) + Real.log ((Q : ℝ) * T) :=
      add_le_add (mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg j)) le_rfl
    _ = _ := by ring

 theorem density_L_fourth_family_continuous (F : Finset PrimitiveComplexCharacter) :
    Continuous (fun t => ∑ χ ∈ F, ‖χ.L (densityVerticalPoint (1 / 2) t)‖ ^ 4) := by
  apply continuous_finsetSum
  intro χ _
  have hL : Continuous χ.L := continuous_iff_continuousAt.mpr (fun z => (χ.L_analytic z).continuousAt)
  exact ((hL.comp (by unfold densityVerticalPoint; fun_prop)).norm.pow 4)

 theorem density_mollifier_family_continuous (F : Finset PrimitiveComplexCharacter) (X : ℕ) :
    Continuous (fun t => ∑ χ ∈ F,
      ‖densityMollifier X χ.character (densityVerticalPoint (1 / 2) t)‖ ^ 2) := by
  apply continuous_finsetSum
  intro χ _
  have hM : Continuous (densityMollifier X χ.character) := by
    apply continuous_iff_continuousAt.mpr
    intro z
    simpa only [zero_add] using (densityMollifier_shift_analytic χ X 0 z).continuousAt
  exact ((hM.comp (by unfold densityVerticalPoint; fun_prop)).norm.pow 2)

 theorem density_mollifier_primitive_mean :
    ∃ C : ℝ, 0 < C ∧ ∀ X Q : ℕ, 1 ≤ Q → ∀ T : ℝ, 1 ≤ T →
      ∀ F : Finset PrimitiveComplexCharacter, (∀ χ ∈ F, χ.modulus ≤ Q) →
      (∑ χ ∈ F, ∫ t in Icc (-T) T,
        ‖densityMollifier X χ.character (densityVerticalPoint (1 / 2) t)‖ ^ 2) ≤
          C * ((X : ℝ) + (Q : ℝ) ^ 2 * T) * (1 + Real.log X) := by
  obtain ⟨C, hC, hb⟩ := critical_mollifier_mean
  refine ⟨C, hC, ?_⟩
  intro X Q hQ T hT F hF
  rw [densityCharacterFamily_sum F Q hF (fun q χ => ∫ t in Icc (-T) T,
    ‖densityMollifier X χ (densityVerticalPoint (1 / 2) t)‖ ^ 2)]
  exact hb X Q hQ T hT (densityCharacterFamily F)
    (fun q _ χ hχ => densityCharacterFamily_primitive F q χ hχ)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityWeightedFourth
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual fourth moment with a whole-line cubic height weight -/

namespace Ostmann

open MeasureTheory Set
open scoped BigOperators

 theorem density_weighted_fourth_moment :
    ∃ C : ℝ, 0 < C ∧ ∀ Q : ℕ, 1 ≤ Q → ∀ T : ℝ, 2 ≤ T →
      ∀ F : Finset PrimitiveComplexCharacter, (∀ χ ∈ F, χ.modulus ≤ Q) →
      Integrable (fun t => densityHeightWeight T t *
        ∑ χ ∈ F, ‖χ.L (densityVerticalPoint (1 / 2) t)‖ ^ 4) ∧
      (∫ t, densityHeightWeight T t *
        ∑ χ ∈ F, ‖χ.L (densityVerticalPoint (1 / 2) t)‖ ^ 4) ≤
          C * ((Q : ℝ) ^ 2 * T) * (Real.log ((Q : ℝ) * T)) ^ 6 := by
  obtain ⟨C, hC, hb⟩ := density_fourth_moment
  refine ⟨C * densityHeightEnergyConstant 6, mul_pos hC (densityHeightEnergyConstant_pos 6), ?_⟩
  intro Q hQ T hT F hF
  have hq : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hl0 : 0 ≤ Real.log ((Q : ℝ) * T) := Real.log_nonneg (by nlinarith)
  let A := C * ((Q : ℝ) ^ 2 * T) * (Real.log ((Q : ℝ) * T)) ^ 6
  have hball (j : ℕ) :
      (∫ t in densityHeightBall T j, ∑ χ ∈ F, ‖χ.L (densityVerticalPoint (1 / 2) t)‖ ^ 4) ≤
        A * (2 : ℝ) ^ j * (j + 1 : ℝ) ^ 6 := by
    have hp : (1 : ℝ) ≤ (2 : ℝ) ^ j := one_le_pow₀ (by norm_num)
    have hH : 2 ≤ (2 : ℝ) ^ j * T := by nlinarith
    have hh := hb Q hQ ((2 : ℝ) ^ j * T) hH F hF
    rw [densityHeightBall, integral_finsetSum F (fun χ _ =>
      density_L_fourth_integrable χ ((2 : ℝ) ^ j * T))]
    apply hh.trans
    have hlog := density_dyadic_height_log Q hQ T hT j
    have hlog0 : 0 ≤ Real.log ((Q : ℝ) * ((2 : ℝ) ^ j * T)) :=
      Real.log_nonneg (by nlinarith)
    calc
      _ ≤ C * ((Q : ℝ) ^ 2 * ((2 : ℝ) ^ j * T)) *
          ((j + 1 : ℝ) * Real.log ((Q : ℝ) * T)) ^ 6 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlog0 hlog 6) (by positivity)
      _ = _ := by dsimp [A]; ring
  obtain ⟨hi, hm⟩ := density_weighted_moment
    (fun t => ∑ χ ∈ F, ‖χ.L (densityVerticalPoint (1 / 2) t)‖ ^ 4)
    (density_L_fourth_family_continuous F) (fun _ => Finset.sum_nonneg (fun _ _ => by positivity))
    T (by linarith) A (by dsimp [A]; positivity) 6 hball
  refine ⟨hi, hm.trans_eq ?_⟩
  dsimp [A]
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityWeightedMollifier
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual mollifier mean with a whole-line cubic height weight -/

namespace Ostmann

open MeasureTheory Set
open scoped BigOperators

 theorem density_weighted_mollifier_mean :
    ∃ C : ℝ, 0 < C ∧ ∀ X Q : ℕ, 1 ≤ X → 1 ≤ Q → ∀ T : ℝ, 2 ≤ T →
      ∀ F : Finset PrimitiveComplexCharacter, (∀ χ ∈ F, χ.modulus ≤ Q) →
      Integrable (fun t => densityHeightWeight T t * ∑ χ ∈ F,
        ‖densityMollifier X χ.character (densityVerticalPoint (1 / 2) t)‖ ^ 2) ∧
      (∫ t, densityHeightWeight T t * ∑ χ ∈ F,
        ‖densityMollifier X χ.character (densityVerticalPoint (1 / 2) t)‖ ^ 2) ≤
          C * ((X : ℝ) + (Q : ℝ) ^ 2 * T) * (1 + Real.log X) := by
  obtain ⟨C, hC, hb⟩ := density_mollifier_primitive_mean
  refine ⟨C * densityHeightEnergyConstant 0, mul_pos hC (densityHeightEnergyConstant_pos 0), ?_⟩
  intro X Q hX hQ T hT F hF
  have hx : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hl0 : 0 ≤ Real.log X := Real.log_nonneg hx
  let A := C * ((X : ℝ) + (Q : ℝ) ^ 2 * T) * (1 + Real.log X)
  have hfχ (χ : PrimitiveComplexCharacter) :
      Continuous (fun t => ‖densityMollifier X χ.character (densityVerticalPoint (1 / 2) t)‖ ^ 2) := by
    have h := density_mollifier_family_continuous {χ} X
    simpa using h
  have hball (j : ℕ) :
      (∫ t in densityHeightBall T j, ∑ χ ∈ F,
        ‖densityMollifier X χ.character (densityVerticalPoint (1 / 2) t)‖ ^ 2) ≤
          A * (2 : ℝ) ^ j * (j + 1 : ℝ) ^ 0 := by
    have hp : (1 : ℝ) ≤ (2 : ℝ) ^ j := one_le_pow₀ (by norm_num)
    have hH : 1 ≤ (2 : ℝ) ^ j * T := by nlinarith
    have hh := hb X Q hQ ((2 : ℝ) ^ j * T) hH F hF
    rw [densityHeightBall, integral_finsetSum F (fun χ _ => (hfχ χ).continuousOn.integrableOn_Icc)]
    apply hh.trans
    have hsize : (X : ℝ) + (Q : ℝ) ^ 2 * ((2 : ℝ) ^ j * T) ≤
        ((X : ℝ) + (Q : ℝ) ^ 2 * T) * (2 : ℝ) ^ j := by
      have h := mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg X : (0 : ℝ) ≤ X)
      nlinarith
    calc
      _ ≤ C * (((X : ℝ) + (Q : ℝ) ^ 2 * T) * (2 : ℝ) ^ j) * (1 + Real.log X) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsize hC.le) (by positivity)
      _ = _ := by dsimp [A]; ring
  obtain ⟨hi, hm⟩ := density_weighted_moment
    (fun t => ∑ χ ∈ F, ‖densityMollifier X χ.character (densityVerticalPoint (1 / 2) t)‖ ^ 2)
    (density_mollifier_family_continuous F X) (fun _ => Finset.sum_nonneg (fun _ _ => by positivity))
    T (by linarith) A (by dsimp [A]; positivity) 0 hball
  refine ⟨hi, hm.trans_eq ?_⟩
  dsimp [A]
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityPackedCharacterMoments
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual moments at characterwise separated zero ordinates -/

namespace Ostmann

open MeasureTheory
open scoped BigOperators Classical

 theorem density_packed_fourth_moment :
    ∃ C : ℝ, 0 < C ∧ ∀ Q : ℕ, 1 ≤ Q → ∀ T : ℝ, 2 ≤ T →
      ∀ {ι : Type} (S : Finset ι) (c : ι → PrimitiveComplexCharacter) (t : ι → ℝ),
      (∀ i ∈ S, (c i).modulus ≤ Q) → (∀ i ∈ S, |t i| ≤ T) →
      (∀ i ∈ S, ∀ j ∈ S, c i = c j → i ≠ j → 1 ≤ |t i - t j|) →
      (∀ i ∈ S, Integrable (fun v => densityCubicWeight (v - t i) *
        ‖(c i).L (densityVerticalPoint (1 / 2) v)‖ ^ 4)) ∧
      (∑ i ∈ S, ∫ v, densityCubicWeight (v - t i) *
        ‖(c i).L (densityVerticalPoint (1 / 2) v)‖ ^ 4) ≤
          C * ((Q : ℝ) ^ 2 * T) * (Real.log ((Q : ℝ) * T)) ^ 6 := by
  obtain ⟨C, hC, hb⟩ := density_weighted_fourth_moment
  refine ⟨densityKernelPackingConstant * C, mul_pos densityKernelPackingConstant_pos hC, ?_⟩
  intro Q hQ T hT ι S c t hc ht hs
  have hF : ∀ χ ∈ S.image c, χ.modulus ≤ Q := by
    intro χ hχ
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hχ
    exact hc i hi
  obtain ⟨hi, hm⟩ := hb Q hQ T hT (S.image c) hF
  obtain ⟨hpi, hpm⟩ := density_packed_moment S c t T (by linarith) ht hs
    (fun χ v => ‖χ.L (densityVerticalPoint (1 / 2) v)‖ ^ 4)
    (fun χ => by simpa using density_L_fourth_family_continuous {χ})
    (fun _ _ => by positivity) hi
  refine ⟨hpi, hpm.trans ?_⟩
  have h := mul_le_mul_of_nonneg_left hm densityKernelPackingConstant_pos.le
  convert h using 1 <;> first | rfl | ring

 theorem density_packed_mollifier_mean :
    ∃ C : ℝ, 0 < C ∧ ∀ X Q : ℕ, 1 ≤ X → 1 ≤ Q → ∀ T : ℝ, 2 ≤ T →
      ∀ {ι : Type} (S : Finset ι) (c : ι → PrimitiveComplexCharacter) (t : ι → ℝ),
      (∀ i ∈ S, (c i).modulus ≤ Q) → (∀ i ∈ S, |t i| ≤ T) →
      (∀ i ∈ S, ∀ j ∈ S, c i = c j → i ≠ j → 1 ≤ |t i - t j|) →
      (∀ i ∈ S, Integrable (fun v => densityCubicWeight (v - t i) *
        ‖densityMollifier X (c i).character (densityVerticalPoint (1 / 2) v)‖ ^ 2)) ∧
      (∑ i ∈ S, ∫ v, densityCubicWeight (v - t i) *
        ‖densityMollifier X (c i).character (densityVerticalPoint (1 / 2) v)‖ ^ 2) ≤
          C * ((X : ℝ) + (Q : ℝ) ^ 2 * T) * (1 + Real.log X) := by
  obtain ⟨C, hC, hb⟩ := density_weighted_mollifier_mean
  refine ⟨densityKernelPackingConstant * C, mul_pos densityKernelPackingConstant_pos hC, ?_⟩
  intro X Q hX hQ T hT ι S c t hc ht hs
  have hF : ∀ χ ∈ S.image c, χ.modulus ≤ Q := by
    intro χ hχ
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hχ
    exact hc i hi
  obtain ⟨hi, hm⟩ := hb X Q hX hQ T hT (S.image c) hF
  obtain ⟨hpi, hpm⟩ := density_packed_moment S c t T (by linarith) ht hs
    (fun χ v => ‖densityMollifier X χ.character (densityVerticalPoint (1 / 2) v)‖ ^ 2)
    (fun χ => by simpa using density_mollifier_family_continuous {χ} X)
    (fun _ _ => by positivity) hi
  refine ⟨hpi, hpm.trans ?_⟩
  have h := mul_le_mul_of_nonneg_left hm densityKernelPackingConstant_pos.le
  convert h using 1 <;> first | rfl | ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityWeightedProductCauchy
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Weighted product Cauchy inequalities for the zero detector -/

namespace Ostmann

open MeasureTheory
open scoped BigOperators

 theorem density_product_cauchy (w f g : ℝ → ℝ)
    (hw : ∀ x, 0 ≤ w x)
    (hff : Integrable (fun x => w x * f x ^ 2))
    (hgg : Integrable (fun x => w x * g x ^ 2))
    (hfg : Integrable (fun x => w x * f x * g x)) :
    (∫ x, w x * f x * g x) ^ 2 ≤
      (∫ x, w x * f x ^ 2) * ∫ x, w x * g x ^ 2 := by
  let A := ∫ x, w x * f x ^ 2
  let B := ∫ x, w x * f x * g x
  let D := ∫ x, w x * g x ^ 2
  have hA : 0 ≤ A := integral_nonneg (fun x => mul_nonneg (hw x) (sq_nonneg _))
  have hq (t : ℝ) : 0 ≤ D - 2 * t * B + t ^ 2 * A := by
    have he : (fun x => w x * (g x - t * f x) ^ 2) =
        (fun x => (w x * g x ^ 2 - (2 * t) * (w x * f x * g x)) + t ^ 2 * (w x * f x ^ 2)) := by
      funext x
      ring
    have hh := integral_add (hgg.sub (hfg.const_mul (2 * t))) (hff.const_mul (t ^ 2))
    have hs := integral_sub hgg (hfg.const_mul (2 * t))
    simp only [Pi.sub_apply] at hh hs
    have hn : 0 ≤ ∫ x, w x * (g x - t * f x) ^ 2 :=
      integral_nonneg (fun x => mul_nonneg (hw x) (sq_nonneg _))
    rw [he, hh, hs, integral_const_mul, integral_const_mul] at hn
    exact hn
  change B ^ 2 ≤ A * D
  by_cases ha : 0 < A
  · have ht : (B / A) * A = B := div_mul_cancel₀ B ha.ne'
    have hh := hq (B / A)
    have hm := mul_nonneg ha.le hh
    have hs := congrArg (fun x : ℝ => x ^ 2) ht
    nlinarith
  · have ha0 : A = 0 := le_antisymm (le_of_not_gt ha) hA
    by_cases hb : B = 0
    · simp [ha0, hb]
    · have ht : ((D + 1) / (2 * B)) * (2 * B) = D + 1 :=
        div_mul_cancel₀ _ (mul_ne_zero (by norm_num) hb)
      have hh := hq ((D + 1) / (2 * B))
      rw [ha0, mul_zero, add_zero] at hh
      nlinarith

 theorem density_finite_product_cauchy {ι : Type*} (S : Finset ι)
    (w f g : ι → ℝ → ℝ) (hw : ∀ i ∈ S, ∀ x, 0 ≤ w i x)
    (hff : ∀ i ∈ S, Integrable (fun x => w i x * f i x ^ 2))
    (hgg : ∀ i ∈ S, Integrable (fun x => w i x * g i x ^ 2))
    (hfg : ∀ i ∈ S, Integrable (fun x => w i x * f i x * g i x)) :
    (∑ i ∈ S, ∫ x, w i x * f i x * g i x) ^ 2 ≤
      (∑ i ∈ S, ∫ x, w i x * f i x ^ 2) *
        ∑ i ∈ S, ∫ x, w i x * g i x ^ 2 := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul S
    (fun i hi => integral_nonneg (fun x => mul_nonneg (hw i hi x) (sq_nonneg _)))
    (fun i hi => integral_nonneg (fun x => mul_nonneg (hw i hi x) (sq_nonneg _)))
  intro i hi
  exact density_product_cauchy (w i) (f i) (g i) (hw i hi) (hff i hi) (hgg i hi) (hfg i hi)

 theorem density_finite_product_fourth {ι : Type*} (S : Finset ι)
    (w f g : ι → ℝ → ℝ) (hw : ∀ i ∈ S, ∀ x, 0 ≤ w i x)
    (h0 : ∀ i ∈ S, Integrable (w i))
    (h2 : ∀ i ∈ S, Integrable (fun x => w i x * f i x ^ 2))
    (h4 : ∀ i ∈ S, Integrable (fun x => w i x * f i x ^ 4))
    (hg : ∀ i ∈ S, Integrable (fun x => w i x * g i x ^ 2))
    (hfg : ∀ i ∈ S, Integrable (fun x => w i x * f i x * g i x)) :
    (∑ i ∈ S, ∫ x, w i x * f i x * g i x) ^ 4 ≤
      (∑ i ∈ S, ∫ x, w i x) * (∑ i ∈ S, ∫ x, w i x * f i x ^ 4) *
        (∑ i ∈ S, ∫ x, w i x * g i x ^ 2) ^ 2 := by
  have hfirst := density_finite_product_cauchy S w f g hw h2 hg hfg
  have hsecond := density_finite_product_cauchy S w (fun _ _ => 1) (fun i x => f i x ^ 2) hw
    (fun i hi => by simpa using h0 i hi)
    (fun i hi => by simpa only [← pow_mul] using h4 i hi)
    (fun i hi => by simpa using h2 i hi)
  simp only [one_pow, mul_one, ← pow_mul] at hsecond
  calc
    _ = ((∑ i ∈ S, ∫ x, w i x * f i x * g i x) ^ 2) ^ 2 := by ring
    _ ≤ ((∑ i ∈ S, ∫ x, w i x * f i x ^ 2) *
        (∑ i ∈ S, ∫ x, w i x * g i x ^ 2)) ^ 2 :=
      pow_le_pow_left₀ (sq_nonneg _) hfirst 2
    _ = (∑ i ∈ S, ∫ x, w i x * f i x ^ 2) ^ 2 *
        (∑ i ∈ S, ∫ x, w i x * g i x ^ 2) ^ 2 := mul_pow _ _ _
    _ ≤ _ := mul_le_mul_of_nonneg_right hsecond (sq_nonneg _)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityCubicIntegrability
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integrability of the mixed critical-line detector product -/

namespace Ostmann

open MeasureTheory

 theorem densityCubicWeight_continuous : Continuous densityCubicWeight := by
  unfold densityCubicWeight
  exact continuous_const.div ((continuous_const.add continuous_abs).pow 3) (fun _ => by positivity)

 theorem densityCubicWeight_integrable : Integrable densityCubicWeight := by
  have h : Integrable (fun v : ℝ => (1 + ‖v‖) ^ (-(3 : ℝ))) :=
    integrable_one_add_norm (E := ℝ) (by norm_num : (Module.finrank ℝ ℝ : ℝ) < 3)
  simpa only [Real.norm_eq_abs, ← densityCubicWeight_rpow] using h

 theorem densityCubicWeight_shift_integrable (t : ℝ) :
    Integrable (fun v => densityCubicWeight (v - t)) :=
  densityCubicWeight_integrable.comp_sub_right t

 theorem densityCubicWeight_shift_integral (t : ℝ) :
    (∫ v, densityCubicWeight (v - t)) = ∫ v, densityCubicWeight v :=
  integral_sub_right_eq_self densityCubicWeight t

 theorem density_cubic_mixed_integrable (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g)
    (hf0 : ∀ v, 0 ≤ f v) (hg0 : ∀ v, 0 ≤ g v) (t : ℝ)
    (h4 : Integrable (fun v => densityCubicWeight (v - t) * f v ^ 4))
    (h2g : Integrable (fun v => densityCubicWeight (v - t) * g v ^ 2)) :
    Integrable (fun v => densityCubicWeight (v - t) * f v ^ 2) ∧
    Integrable (fun v => densityCubicWeight (v - t) * f v * g v) := by
  have hwc : Continuous (fun v => densityCubicWeight (v - t)) :=
    densityCubicWeight_continuous.comp (continuous_id.sub continuous_const)
  have h2 : Integrable (fun v => densityCubicWeight (v - t) * f v ^ 2) := by
    apply ((densityCubicWeight_shift_integrable t).add h4).mono'
      (hwc.mul (hf.pow 2)).aestronglyMeasurable
    filter_upwards with v
    change ‖densityCubicWeight (v - t) * f v ^ 2‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (densityCubicWeight_nonneg _) (sq_nonneg _))]
    have h : f v ^ 2 ≤ 1 + f v ^ 4 := by nlinarith [sq_nonneg (f v ^ 2 - 1)]
    have hh := mul_le_mul_of_nonneg_left h (densityCubicWeight_nonneg (v - t))
    simpa only [mul_add, mul_one, Pi.add_apply] using hh
  refine ⟨h2, ?_⟩
  apply (h2.add h2g).mono' ((hwc.mul hf).mul hg).aestronglyMeasurable
  filter_upwards with v
  change ‖densityCubicWeight (v - t) * f v * g v‖ ≤ _
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg (mul_nonneg (densityCubicWeight_nonneg _) (hf0 v)) (hg0 v))]
  have h : f v * g v ≤ f v ^ 2 + g v ^ 2 := by nlinarith [sq_nonneg (f v - g v)]
  have hh := mul_le_mul_of_nonneg_left h (densityCubicWeight_nonneg (v - t))
  simpa only [mul_add, mul_assoc, Pi.add_apply] using hh

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityPackedProduct
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The fourth-power bound for the actual detector product -/

namespace Ostmann

open MeasureTheory
open scoped BigOperators Classical

 theorem density_packed_product_fourth_oai :
    ∃ C : ℝ, 0 < C ∧ ∀ X Q : ℕ, 1 ≤ X → 1 ≤ Q → ∀ T : ℝ, 2 ≤ T →
      ∀ {ι : Type} (S : Finset ι) (c : ι → PrimitiveComplexCharacter) (t : ι → ℝ),
      (∀ i ∈ S, (c i).modulus ≤ Q) → (∀ i ∈ S, |t i| ≤ T) →
      (∀ i ∈ S, ∀ j ∈ S, c i = c j → i ≠ j → 1 ≤ |t i - t j|) →
      (∑ i ∈ S, ∫ v, densityCubicWeight (v - t i) *
        ‖(c i).L (densityVerticalPoint (1 / 2) v)‖ *
        ‖densityMollifier X (c i).character (densityVerticalPoint (1 / 2) v)‖) ^ 4 ≤
          C * S.card * ((Q : ℝ) ^ 2 * T) * ((X : ℝ) + (Q : ℝ) ^ 2 * T) ^ 2 *
            (Real.log ((Q : ℝ) * T)) ^ 6 * (1 + Real.log X) ^ 2 := by
  obtain ⟨C4, hC4, hfourth⟩ := density_packed_fourth_moment
  obtain ⟨C2, hC2, hsecond⟩ := density_packed_mollifier_mean
  let W0 := 1 + ∫ v, densityCubicWeight v
  have hW0 : 0 < W0 := by
    have hn : 0 ≤ ∫ v : ℝ, densityCubicWeight v :=
      integral_nonneg (fun v => densityCubicWeight_nonneg v)
    dsimp [W0]
    linarith
  refine ⟨W0 * C4 * C2 ^ 2, by positivity, ?_⟩
  intro X Q hX hQ T hT ι S c t hc ht hs
  obtain ⟨hi4, hb4⟩ := hfourth Q hQ T hT S c t hc ht hs
  obtain ⟨hiM, hbM⟩ := hsecond X Q hX hQ T hT S c t hc ht hs
  let f := fun i v => ‖(c i).L (densityVerticalPoint (1 / 2) v)‖
  let g := fun i v => ‖densityMollifier X (c i).character (densityVerticalPoint (1 / 2) v)‖
  let w := fun i v => densityCubicWeight (v - t i)
  have hfc (i : ι) : Continuous (f i) := by
    have hl : Continuous (c i).L := continuous_iff_continuousAt.mpr (fun z => ((c i).L_analytic z).continuousAt)
    exact (hl.comp (by unfold densityVerticalPoint; fun_prop)).norm
  have hgc (i : ι) : Continuous (g i) := by
    have hm : Continuous (densityMollifier X (c i).character) := by
      apply continuous_iff_continuousAt.mpr
      intro z
      simpa only [zero_add] using (densityMollifier_shift_analytic (c i) X 0 z).continuousAt
    exact (hm.comp (by unfold densityVerticalPoint; fun_prop)).norm
  have hmixed (i : ι) (hi : i ∈ S) := density_cubic_mixed_integrable (f i) (g i)
    (hfc i) (hgc i) (fun _ => norm_nonneg _) (fun _ => norm_nonneg _) (t i) (hi4 i hi) (hiM i hi)
  have hpow := density_finite_product_fourth S w f g
    (fun _ _ _ => densityCubicWeight_nonneg _)
    (fun i _ => densityCubicWeight_shift_integrable (t i))
    (fun i hi => (hmixed i hi).1) hi4 hiM (fun i hi => (hmixed i hi).2)
  have hweight : (∑ i ∈ S, ∫ v, w i v) ≤ (S.card : ℝ) * W0 := by
    dsimp [w]
    simp_rw [densityCubicWeight_shift_integral]
    simp only [Finset.sum_const, nsmul_eq_mul]
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    dsimp [W0]
    linarith
  have hf4non : 0 ≤ ∑ i ∈ S, ∫ v, w i v * f i v ^ 4 :=
    Finset.sum_nonneg (fun i _ => integral_nonneg (fun v => mul_nonneg (densityCubicWeight_nonneg _) (by positivity)))
  have hmnon : 0 ≤ ∑ i ∈ S, ∫ v, w i v * g i v ^ 2 :=
    Finset.sum_nonneg (fun i _ => integral_nonneg (fun v => mul_nonneg (densityCubicWeight_nonneg _) (sq_nonneg _)))
  have hWnon : 0 ≤ (S.card : ℝ) * W0 := by positivity
  have hWM := mul_le_mul hweight hb4 hf4non hWnon
  have hMsq := pow_le_pow_left₀ hmnon hbM 2
  apply hpow.trans
  calc
    _ ≤ ((S.card : ℝ) * W0) *
        (C4 * ((Q : ℝ) ^ 2 * T) * (Real.log ((Q : ℝ) * T)) ^ 6) *
        (C2 * ((X : ℝ) + (Q : ℝ) ^ 2 * T) * (1 + Real.log X)) ^ 2 :=
      mul_le_mul hWM hMsq (sq_nonneg _) (by positivity)
    _ = _ := by ring

end Ostmann

end OAI
end

theorem solution : type_of% @OAI.Ostmann.density_packed_product_fourth_oai := @OAI.Ostmann.density_packed_product_fourth_oai
