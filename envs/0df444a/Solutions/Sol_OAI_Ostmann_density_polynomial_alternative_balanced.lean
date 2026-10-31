-- Prove2me | solution 1 for OAI.Ostmann.density_polynomial_alternative_balanced
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T06:34:51.027614+00:00
-- url     : https://prove2.me/submissions/38593d4d-c7d1-4ba6-9a09-34b4789a79cb

import Mathlib
import Definitions.Def_OAIQ095D006

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_LcmFrequencySum
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The reciprocal-lcm sum in the frequency budget

The gcd coordinates embed each frequency pair into three independent
positive harmonic sums. No asymptotic divisor estimate is used here.
-/

namespace Ostmann

open scoped BigOperators

theorem gcdFrequencyCoordinates_recover (x : ℕ × ℕ) :
    (gcdFrequencyCoordinates x).1 * (gcdFrequencyCoordinates x).2.1 = x.1 ∧
    (gcdFrequencyCoordinates x).1 * (gcdFrequencyCoordinates x).2.2 = x.2 := by
  exact ⟨Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _),
    Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)⟩

theorem gcdFrequencyCoordinates_injective : Function.Injective gcdFrequencyCoordinates := by
  intro x y h
  obtain ⟨hx₁, hx₂⟩ := gcdFrequencyCoordinates_recover x
  obtain ⟨hy₁, hy₂⟩ := gcdFrequencyCoordinates_recover y
  apply Prod.ext
  · exact hx₁.symm.trans ((congrArg (fun z : ℕ × ℕ × ℕ => z.1 * z.2.1) h).trans hy₁)
  · exact hx₂.symm.trans ((congrArg (fun z : ℕ × ℕ × ℕ => z.1 * z.2.2) h).trans hy₂)

theorem gcdFrequencyCoordinates_lcm (a b : ℕ) (ha : 0 < a) :
    (gcdFrequencyCoordinates (a, b)).1 * (gcdFrequencyCoordinates (a, b)).2.1 *
      (gcdFrequencyCoordinates (a, b)).2.2 = a.lcm b := by
  have hg := Nat.gcd_pos_of_pos_left b ha
  obtain ⟨ha', hb'⟩ := gcdFrequencyCoordinates_recover (a, b)
  apply Nat.eq_of_mul_eq_mul_left hg
  calc
    _ = ((gcdFrequencyCoordinates (a, b)).1 * (gcdFrequencyCoordinates (a, b)).2.1) *
        ((gcdFrequencyCoordinates (a, b)).1 * (gcdFrequencyCoordinates (a, b)).2.2) := by
      dsimp [gcdFrequencyCoordinates]
      ring
    _ = a * b := by rw [ha', hb']
    _ = _ := (Nat.gcd_mul_lcm a b).symm

theorem gcdFrequencyCoordinates_mem {N a b : ℕ}
    (ha : a ∈ Finset.Icc 1 N) (hb : b ∈ Finset.Icc 1 N) :
    gcdFrequencyCoordinates (a, b) ∈
      (Finset.Icc 1 N).product ((Finset.Icc 1 N).product (Finset.Icc 1 N)) := by
  obtain ⟨ha₀, haN⟩ := Finset.mem_Icc.mp ha
  obtain ⟨hb₀, hbN⟩ := Finset.mem_Icc.mp hb
  have hap : 0 < a := ha₀
  have hbp : 0 < b := hb₀
  have hg := Nat.gcd_pos_of_pos_left b hap
  have hga := Nat.le_of_dvd hap (Nat.gcd_dvd_left a b)
  have hgb := Nat.le_of_dvd hbp (Nat.gcd_dvd_right a b)
  apply Finset.mem_product.mpr
  refine ⟨Finset.mem_Icc.mpr ⟨hg, hga.trans haN⟩, Finset.mem_product.mpr ⟨?_, ?_⟩⟩
  · exact Finset.mem_Icc.mpr ⟨Nat.div_pos hga hg, (Nat.div_le_self _ _).trans haN⟩
  · exact Finset.mem_Icc.mpr ⟨Nat.div_pos hgb hg, (Nat.div_le_self _ _).trans hbN⟩

/-- Exact finite bound before estimating the harmonic sum. -/
theorem reciprocal_lcm_sum_le_harmonic_cube (N : ℕ) :
    (∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 N, ((a.lcm b : ℕ) : ℝ)⁻¹) ≤
      (∑ n ∈ Finset.Icc 1 N, (n : ℝ)⁻¹) ^ 3 := by
  let S := Finset.Icc 1 N
  let w : ℕ × ℕ × ℕ → ℝ := fun z => (z.1 : ℝ)⁻¹ * (z.2.1 : ℝ)⁻¹ * (z.2.2 : ℝ)⁻¹
  have hw (x : ℕ × ℕ) (hx : x ∈ S.product S) :
      ((x.1.lcm x.2 : ℕ) : ℝ)⁻¹ = w (gcdFrequencyCoordinates x) := by
    have ha : 0 < x.1 := (Finset.mem_Icc.mp (Finset.mem_product.mp hx).1).1
    rw [← gcdFrequencyCoordinates_lcm x.1 x.2 ha]
    simp only [w, Nat.cast_mul, mul_inv_rev]
    ring
  have hsub : (S.product S).image gcdFrequencyCoordinates ⊆ S.product (S.product S) := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    exact gcdFrequencyCoordinates_mem (Finset.mem_product.mp hx).1 (Finset.mem_product.mp hx).2
  calc
    _ = ∑ x ∈ S.product S, w (gcdFrequencyCoordinates x) := by
      simp only [Finset.product_eq_sprod]
      rw [Finset.sum_product S S (fun x => w (gcdFrequencyCoordinates x))]
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      exact hw (a, b) (Finset.mem_product.mpr ⟨ha, hb⟩)
    _ = ∑ z ∈ (S.product S).image gcdFrequencyCoordinates, w z := by
      exact (Finset.sum_image (fun _ _ _ _ h => gcdFrequencyCoordinates_injective h)).symm
    _ ≤ ∑ z ∈ S.product (S.product S), w z :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by dsimp [w]; positivity)
    _ = ∑ a ∈ S, ∑ b ∈ S, ∑ c ∈ S, (a : ℝ)⁻¹ * (b : ℝ)⁻¹ * (c : ℝ)⁻¹ := by
      simp only [Finset.product_eq_sprod]
      rw [Finset.sum_product S (S ×ˢ S) w]
      apply Finset.sum_congr rfl
      intro a _
      exact Finset.sum_product S S (fun z => w (a, z))
    _ = _ := by
      simp only [← Finset.mul_sum, ← Finset.sum_mul]
      dsimp [S]
      ring

/-- The quantitative frequency-pair estimate used by the norm comparison. -/
theorem reciprocal_lcm_sum_le_log_cube (N : ℕ) :
    (∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 N, ((a.lcm b : ℕ) : ℝ)⁻¹) ≤
      (1 + Real.log N) ^ 3 := by
  have hH : (∑ n ∈ Finset.Icc 1 N, (n : ℝ)⁻¹) ≤ 1 + Real.log N := by
    simpa only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
      using harmonic_le_one_add_log N
  exact (reciprocal_lcm_sum_le_harmonic_cube N).trans
    (pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => by positivity) hH 3)

end Ostmann

end OAI
end

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
-- module Solutions.OAIQ095_OS.Ostmann_Supply_MultiplierWeightedBudget
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Elementary divisor and logarithmic budgets for sieve multipliers -/

namespace Ostmann
open scoped Classical BigOperators

theorem positiveMultipliers_dvd_card (U d : ℕ) :
    ((positiveMultipliers U).filter (fun u => d ∣ u)).card = U / d := by
  have he : (positiveMultipliers U).filter (fun u => d ∣ u) =
      positiveMultiplesUpTo U d := by
    ext u
    simp only [positiveMultipliers, positiveMultiplesUpTo, Finset.mem_filter,
      Finset.mem_Icc, Finset.mem_range]
    omega
  rw [he]
  exact Nat.card_multiples' U d

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
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensitySobolevPoint
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Point sampling from the energy of a differentiable complex function -/

namespace Ostmann

open MeasureTheory Set
open scoped ComplexConjugate

 theorem density_energy_derivative_bound {f : ℝ → ℂ} {f' : ℂ} {x : ℝ}
    (hf : HasDerivAt f f' x) :
    ‖deriv (fun t => ‖f t‖ ^ 2) x‖ ≤ ‖f x‖ ^ 2 + ‖f'‖ ^ 2 := by
  rw [hf.norm_sq.deriv]
  have hi := norm_inner_le_norm (𝕜 := ℝ) (f x) f'
  have hnorm : ‖(2 : ℝ) * inner ℝ (f x) f'‖ ≤ 2 * (‖f x‖ * ‖f'‖) := by
    rw [norm_mul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact mul_le_mul_of_nonneg_left hi (by norm_num)
  exact hnorm.trans (by nlinarith [sq_nonneg (‖f x‖ - ‖f'‖)])

 theorem density_energy_oscillation (f g : ℝ → ℂ)
    (hf : ∀ x, HasDerivAt f (g x) x) (hg : Continuous g)
    (a b t u : ℝ) (ht : t ∈ Icc a b) (hu : u ∈ Icc a b) :
    ‖f t‖ ^ 2 ≤ ‖f u‖ ^ 2 + ∫ x in a..b, (‖f x‖ ^ 2 + ‖g x‖ ^ 2) := by
  have hcont : Continuous f := continuous_iff_continuousAt.mpr (fun x => (hf x).continuousAt)
  have hcE : Continuous (fun x => ‖f x‖ ^ 2) := hcont.norm.pow 2
  have hcB : Continuous (fun x => ‖f x‖ ^ 2 + ‖g x‖ ^ 2) :=
    (hcont.norm.pow 2).add (hg.norm.pow 2)
  have hdE : Differentiable ℝ (fun x => ‖f x‖ ^ 2) := fun x => (hf x).norm_sq.differentiableAt
  have hbound : ∀ᵐ x : ℝ, ‖deriv (fun t => ‖f t‖ ^ 2) x‖ ≤ ‖f x‖ ^ 2 + ‖g x‖ ^ 2 :=
    Filter.Eventually.of_forall (fun x => density_energy_derivative_bound (hf x))
  have hab : a ≤ b := ht.1.trans ht.2
  have hbnon : ∀ᵐ x : ℝ, 0 ≤ ‖f x‖ ^ 2 + ‖g x‖ ^ 2 :=
    Filter.Eventually.of_forall (fun x => add_nonneg (sq_nonneg _) (sq_nonneg _))
  have hstep (v w : ℝ) (hv : v ∈ Icc a b) (hw : w ∈ Icc a b) (hvw : v ≤ w) :
      ‖‖f w‖ ^ 2 - ‖f v‖ ^ 2‖ ≤ ∫ x in a..b, (‖f x‖ ^ 2 + ‖g x‖ ^ 2) := by
    have h := norm_sub_le_integral_of_norm_deriv_le_of_le hvw hcE.continuousOn
      hdE.differentiableOn (hbound.mono (fun _ hx _ => hx)) (hcB.intervalIntegrable v w)
    have hm := intervalIntegral.integral_mono_interval hv.1 hvw hw.2 (ae_restrict_of_ae hbnon)
      (hcB.intervalIntegrable a b)
    exact h.trans hm
  have hdiff : ‖‖f t‖ ^ 2 - ‖f u‖ ^ 2‖ ≤
      ∫ x in a..b, (‖f x‖ ^ 2 + ‖g x‖ ^ 2) := by
    rcases le_total u t with h | h
    · exact hstep u t hu ht h
    · simpa only [norm_sub_rev] using hstep t u ht hu h
  have hl := (le_abs_self (‖f t‖ ^ 2 - ‖f u‖ ^ 2)).trans
    (by simpa only [Real.norm_eq_abs] using hdiff)
  linarith

 theorem density_unit_interval_sample (f g : ℝ → ℂ)
    (hf : ∀ x, HasDerivAt f (g x) x) (hg : Continuous g) (t : ℝ) :
    ‖f t‖ ^ 2 ≤ 2 * (∫ x in t - 1 / 2..t + 1 / 2, ‖f x‖ ^ 2) +
      ∫ x in t - 1 / 2..t + 1 / 2, ‖g x‖ ^ 2 := by
  have hcont : Continuous f := continuous_iff_continuousAt.mpr (fun x => (hf x).continuousAt)
  have hab : t - 1 / 2 ≤ t + 1 / 2 := by linarith
  have hpoint (u : ℝ) (hu : u ∈ Icc (t - 1 / 2) (t + 1 / 2)) :=
    density_energy_oscillation f g hf hg (t - 1 / 2) (t + 1 / 2) t u
      ⟨by linarith, by linarith⟩ hu
  have hi := intervalIntegral.integral_mono_on (μ := volume) hab intervalIntegrable_const
    (((hcont.norm.pow 2).intervalIntegrable (t - 1 / 2) (t + 1 / 2)).add intervalIntegrable_const) hpoint
  rw [intervalIntegral.integral_const, intervalIntegral.integral_add,
    intervalIntegral.integral_const, intervalIntegral.integral_add] at hi
  · simp only [show t + 1 / 2 - (t - 1 / 2) = (1 : ℝ) by ring, smul_eq_mul,
      one_mul] at hi
    change ‖f t‖ ^ 2 ≤ (∫ x in t - 1 / 2..t + 1 / 2, ‖f x‖ ^ 2) +
      ((∫ x in t - 1 / 2..t + 1 / 2, ‖f x‖ ^ 2) +
       ∫ x in t - 1 / 2..t + 1 / 2, ‖g x‖ ^ 2) at hi
    linarith
  · exact (hcont.norm.pow 2).intervalIntegrable _ _
  · exact (hg.norm.pow 2).intervalIntegrable _ _
  · exact (hcont.norm.pow 2).intervalIntegrable _ _
  · exact intervalIntegrable_const

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityAbscissaSample
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Sampling a variable real part without moving left of the density line -/

namespace Ostmann

open MeasureTheory Set

 theorem density_forward_interval_sample (f g : ℝ → ℂ)
    (hf : ∀ x, HasDerivAt f (g x) x) (hg : Continuous g) (t : ℝ) :
    ‖f t‖ ^ 2 ≤ 2 * (∫ x in t..t + 1, ‖f x‖ ^ 2) +
      ∫ x in t..t + 1, ‖g x‖ ^ 2 := by
  have hcont : Continuous f := continuous_iff_continuousAt.mpr (fun x => (hf x).continuousAt)
  have hab : t ≤ t + 1 := by linarith
  have hpoint (u : ℝ) (hu : u ∈ Icc t (t + 1)) :=
    density_energy_oscillation f g hf hg t (t + 1) t u ⟨le_rfl, hab⟩ hu
  have hi := intervalIntegral.integral_mono_on (μ := volume) hab intervalIntegrable_const
    (((hcont.norm.pow 2).intervalIntegrable t (t + 1)).add intervalIntegrable_const) hpoint
  rw [intervalIntegral.integral_const, intervalIntegral.integral_add,
    intervalIntegral.integral_const, intervalIntegral.integral_add] at hi
  · simp only [show t + 1 - t = (1 : ℝ) by ring, smul_eq_mul, one_mul] at hi
    change ‖f t‖ ^ 2 ≤ (∫ x in t..t + 1, ‖f x‖ ^ 2) +
      ((∫ x in t..t + 1, ‖f x‖ ^ 2) + ∫ x in t..t + 1, ‖g x‖ ^ 2) at hi
    linarith
  · exact (hcont.norm.pow 2).intervalIntegrable _ _
  · exact (hg.norm.pow 2).intervalIntegrable _ _
  · exact (hcont.norm.pow 2).intervalIntegrable _ _
  · exact intervalIntegrable_const

 theorem density_abscissa_sample (f g : ℝ → ℂ)
    (hf : ∀ x, HasDerivAt f (g x) x) (hg : Continuous g)
    (σ β : ℝ) (hσβ : σ ≤ β) (hβ : β ≤ 1) :
    ‖f β‖ ^ 2 ≤ 2 * (∫ x in σ..2, ‖f x‖ ^ 2) + ∫ x in σ..2, ‖g x‖ ^ 2 := by
  have hcont : Continuous f := continuous_iff_continuousAt.mpr (fun x => (hf x).continuousAt)
  have h := density_forward_interval_sample f g hf hg β
  have hF := intervalIntegral.integral_mono_interval (μ := volume) hσβ (by linarith : β ≤ β + 1)
    (by linarith : β + 1 ≤ 2)
    (Filter.Eventually.of_forall (fun x => sq_nonneg ‖f x‖))
    ((hcont.norm.pow 2).intervalIntegrable σ 2)
  have hG := intervalIntegral.integral_mono_interval (μ := volume) hσβ (by linarith : β ≤ β + 1)
    (by linarith : β + 1 ≤ 2)
    (Filter.Eventually.of_forall (fun x => sq_nonneg ‖g x‖))
    ((hg.norm.pow 2).intervalIntegrable σ 2)
  linarith

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

 theorem density_separated_samples {ι : Type*} (S : Finset ι) (t : ι → ℝ)
    (T : ℝ) (hT : ∀ i ∈ S, |t i| ≤ T)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → 1 ≤ |t i - t j|)
    (f g : ℝ → ℂ) (hf : ∀ x, HasDerivAt f (g x) x) (hg : Continuous g) :
    (∑ i ∈ S, ‖f (t i)‖ ^ 2) ≤
      2 * (∫ x in Icc (-T - 1) (T + 1), ‖f x‖ ^ 2) +
        ∫ x in Icc (-T - 1) (T + 1), ‖g x‖ ^ 2 := by
  have hfc : Continuous f := continuous_iff_continuousAt.mpr (fun x => (hf x).continuousAt)
  have hs := Finset.sum_le_sum (s := S) (fun i _ => density_unit_interval_sample f g hf hg (t i))
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hs
  apply hs.trans
  exact add_le_add
    (mul_le_mul_of_nonneg_left (density_sample_window_integrals S t T hT hsep
      (fun x => ‖f x‖ ^ 2) (hfc.norm.pow 2) (fun _ => sq_nonneg _)) (by norm_num))
    (density_sample_window_integrals S t T hT hsep
      (fun x => ‖g x‖ ^ 2) (hg.norm.pow 2) (fun _ => sq_nonneg _))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityPolynomialDerivative
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The explicit height derivative and its coefficient energy -/

namespace Ostmann

open scoped BigOperators Classical

 theorem density_log_phase_derivative (l t : ℝ) :
    HasDerivAt (fun x : ℝ => realAdditivePhase (-(l * x)))
      ((-2 * (Real.pi : ℂ) * Complex.I * (l : ℂ)) * realAdditivePhase (-(l * t))) t := by
  let k : ℂ := -2 * (Real.pi : ℂ) * Complex.I * (l : ℂ)
  have he (x : ℝ) : realAdditivePhase (-(l * x)) = Complex.exp (k * (x : ℂ)) := by
    unfold realAdditivePhase
    congr 1
    dsimp [k]
    push_cast
    ring
  have hd := (((hasDerivAt_id t).ofReal_comp).const_mul k).cexp
  simp only [id_eq, Complex.ofReal_one, mul_one] at hd
  refine (hd.congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => ?_)).congr_deriv ?_
  · beta_reduce
    exact he x
  · rw [he]
    ring

 theorem density_polynomial_hasDerivAt (S : Finset ℕ) (a : ℕ → ℂ) (t : ℝ) :
    HasDerivAt (fun x : ℝ => ∑ n ∈ S, a n * realAdditivePhase (-(Real.log n * x)))
      (∑ n ∈ S, densityDerivativeCoeff a n * realAdditivePhase (-(Real.log n * t))) t := by
  convert HasDerivAt.fun_sum (u := S) (fun n _ =>
    (density_log_phase_derivative (Real.log n) t).const_mul (a n)) using 1
  all_goals try with_reducible_and_instances rfl
  apply Finset.sum_congr rfl
  intro n _
  unfold densityDerivativeCoeff
  ring

 theorem density_polynomial_continuous (S : Finset ℕ) (a : ℕ → ℂ) :
    Continuous (fun t : ℝ => ∑ n ∈ S, a n * realAdditivePhase (-(Real.log n * t))) :=
  continuous_iff_continuousAt.mpr (fun t => (density_polynomial_hasDerivAt S a t).continuousAt)

 theorem density_derivative_coefficient_bound (N : ℕ) (a : ℕ → ℂ) :
    (∑ n ∈ Finset.Icc 1 N, ‖densityDerivativeCoeff a n‖ ^ 2) ≤
      64 * (Real.log (N + 1 : ℕ)) ^ 2 * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  obtain ⟨hn1, hnN⟩ := Finset.mem_Icc.mp hn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hlog : 0 ≤ Real.log n := Real.log_nonneg hnR
  have hlogN : Real.log n ≤ Real.log (N + 1 : ℕ) :=
    Real.log_le_log (by positivity) (by exact_mod_cast (by omega : n ≤ N + 1))
  have hcoef : ‖-2 * (Real.pi : ℂ) * Complex.I * (Real.log n : ℂ)‖ ≤
      8 * Real.log (N + 1 : ℕ) := by
    simp only [norm_mul, norm_neg, Complex.norm_ofNat, Complex.norm_real,
      Real.norm_eq_abs, Complex.norm_I, mul_one, abs_of_pos Real.pi_pos,
      abs_of_nonneg hlog]
    nlinarith [Real.pi_lt_four, Real.pi_pos]
  rw [densityDerivativeCoeff, norm_mul, mul_pow]
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  nlinarith [norm_nonneg (-2 * (Real.pi : ℂ) * Complex.I * (Real.log n : ℂ))]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityDivisorMoment
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The elementary second moment of divisor coefficients

Pairs of divisors are counted by their least common multiple. The
harmonic-cube estimate gives the logarithmic third power without a
pointwise divisor bound.
-/

namespace Ostmann

open scoped BigOperators Classical

 theorem density_divisor_count_as_sum (N n : ℕ) (hn : n ∈ Finset.Icc 1 N) :
    (n.divisors.card : ℝ) = ∑ d ∈ Finset.Icc 1 N, if d ∣ n then (1 : ℝ) else 0 := by
  have he : (Finset.Icc 1 N).filter (fun d => d ∣ n) = n.divisors := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
    constructor
    · intro h
      exact ⟨h.2, by have hpos := (Finset.mem_Icc.mp hn).1; omega⟩
    · intro h
      have hpos : 0 < n := (Finset.mem_Icc.mp hn).1
      have hdpos := Nat.pos_of_dvd_of_pos h.1 hpos
      exact ⟨⟨hdpos, (Nat.le_of_dvd hpos h.1).trans (Finset.mem_Icc.mp hn).2⟩, h.1⟩
  rw [← Finset.sum_filter, he]
  simp

 theorem density_divisor_square_as_sum (N n : ℕ) (hn : n ∈ Finset.Icc 1 N) :
    (n.divisors.card : ℝ) ^ 2 = ∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 N,
      if d.lcm e ∣ n then (1 : ℝ) else 0 := by
  rw [density_divisor_count_as_sum N n hn, pow_two, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro d _
  apply Finset.sum_congr rfl
  intro e _
  by_cases hd : d ∣ n <;> by_cases he : e ∣ n <;>
    simp [Nat.lcm_dvd_iff, hd, he]

 theorem density_divisor_square_sum (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, (n.divisors.card : ℝ) ^ 2) ≤
      (N : ℝ) * (1 + Real.log N) ^ 3 := by
  calc
    _ = ∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 N,
        ((N / d.lcm e : ℕ) : ℝ) := by
      rw [Finset.sum_congr rfl (fun n hn => density_divisor_square_as_sum N n hn)]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro d _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro e _
      rw [← Finset.sum_filter]
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
      exact_mod_cast positiveMultipliers_dvd_card N (d.lcm e)
    _ ≤ (N : ℝ) * ∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 N,
        ((d.lcm e : ℕ) : ℝ)⁻¹ := by
      simp only [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro d _
      apply Finset.sum_le_sum
      intro e _
      simpa only [div_eq_mul_inv] using
        (Nat.cast_div_le (m := N) (n := d.lcm e) (α := ℝ))
    _ ≤ _ := mul_le_mul_of_nonneg_left (reciprocal_lcm_sum_le_log_cube N) (Nat.cast_nonneg _)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityDetectorCoefficients
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual truncated Möbius coefficients in the zero detector -/

namespace Ostmann

open scoped BigOperators Classical

 theorem densityMobiusCutoff_norm (X n : ℕ) : ‖densityMobiusCutoff X n‖ ≤ 1 := by
  unfold densityMobiusCutoff
  split_ifs
  · norm_cast
    exact ArithmeticFunction.abs_moebius_le_one
  · simp

 theorem densityDetectorCoefficient_norm (X n : ℕ) :
    ‖densityDetectorCoefficient X n‖ ≤ n.divisors.card := by
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ d ∈ n.divisors, (1 : ℝ) :=
      Finset.sum_le_sum (fun d _ => densityMobiusCutoff_norm X d)
    _ = _ := by simp

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

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityAbscissaPolynomial
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Differentiating the actual Dirichlet polynomial in its real part -/

namespace Ostmann

open Complex
open scoped BigOperators

 theorem densityVerticalCoeff_exp (a : ℕ → ℂ) (σ : ℝ) (n : ℕ) (hn : 0 < n) :
    densityVerticalCoeff a σ n = a n * Complex.exp (-(Real.log n : ℂ) * (σ : ℂ)) := by
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hl : Complex.log (n : ℂ) = (Real.log n : ℂ) := by
    simpa only [Complex.ofReal_natCast] using
      (Complex.ofReal_log (show (0 : ℝ) ≤ n by positivity)).symm
  rw [densityVerticalCoeff, Complex.cpow_def_of_ne_zero hnC, hl, div_eq_mul_inv, ← Complex.exp_neg]
  congr 2
  ring

 theorem densityVerticalCoeff_hasDerivAt (a : ℕ → ℂ) (n : ℕ) (hn : 0 < n) (σ : ℝ) :
    HasDerivAt (fun x : ℝ => densityVerticalCoeff a x n)
      (densityVerticalCoeff (densityAbscissaDerivativeCoeff a) σ n) σ := by
  have hd := ((((hasDerivAt_id σ).ofReal_comp).const_mul (-(Real.log n : ℂ))).cexp).const_mul (a n)
  simp only [id_eq, Complex.ofReal_one, mul_one] at hd
  refine (hd.congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => ?_)).congr_deriv ?_
  · beta_reduce
    exact densityVerticalCoeff_exp a x n hn
  · rw [densityVerticalCoeff_exp _ σ n hn]
    unfold densityAbscissaDerivativeCoeff
    ring

 theorem density_abscissa_polynomial_hasDerivAt {q : ℕ} (S : Finset ℕ)
    (hS : ∀ n ∈ S, 0 < n) (a : ℕ → ℂ) (χ : DirichletCharacter ℂ q) (t σ : ℝ) :
    HasDerivAt (fun x => densityCharacterPolynomial S (densityVerticalCoeff a x) χ t)
      (densityCharacterPolynomial S (densityVerticalCoeff (densityAbscissaDerivativeCoeff a) σ) χ t) σ := by
  unfold densityCharacterPolynomial
  exact HasDerivAt.fun_sum (fun n hn =>
    ((densityVerticalCoeff_hasDerivAt a n (hS n hn) σ).mul_const (χ (n : ZMod q))).mul_const
      (realAdditivePhase (-(Real.log n * t))))

 theorem density_abscissa_polynomial_continuous {q : ℕ} (S : Finset ℕ)
    (hS : ∀ n ∈ S, 0 < n) (a : ℕ → ℂ) (χ : DirichletCharacter ℂ q) (t : ℝ) :
    Continuous (fun x => densityCharacterPolynomial S (densityVerticalCoeff a x) χ t) :=
  continuous_iff_continuousAt.mpr (fun x =>
    (density_abscissa_polynomial_hasDerivAt S hS a χ t x).continuousAt)

 theorem density_abscissa_polynomial_sample {q : ℕ} (S : Finset ℕ)
    (hS : ∀ n ∈ S, 0 < n) (a : ℕ → ℂ) (χ : DirichletCharacter ℂ q) (t σ β : ℝ)
    (hσβ : σ ≤ β) (hβ : β ≤ 1) :
    ‖densityCharacterPolynomial S (densityVerticalCoeff a β) χ t‖ ^ 2 ≤
      2 * (∫ x in σ..2, ‖densityCharacterPolynomial S (densityVerticalCoeff a x) χ t‖ ^ 2) +
        ∫ x in σ..2, ‖densityCharacterPolynomial S
          (densityVerticalCoeff (densityAbscissaDerivativeCoeff a) x) χ t‖ ^ 2 := by
  exact density_abscissa_sample _ _
    (density_abscissa_polynomial_hasDerivAt S hS a χ t)
    (density_abscissa_polynomial_continuous S hS (densityAbscissaDerivativeCoeff a) χ t)
    σ β hσβ hβ

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityAbscissaEnergy
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Coefficient energy decreases to the right of the density line -/

namespace Ostmann

open Complex
open scoped BigOperators

 theorem densityVerticalCoeff_norm_mono (a : ℕ → ℂ) (σ x : ℝ) (hx : σ ≤ x)
    (n : ℕ) (hn : 1 ≤ n) :
    ‖densityVerticalCoeff a x n‖ ≤ ‖densityVerticalCoeff a σ n‖ := by
  have hp : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  rw [densityVerticalCoeff_norm a x n hp, densityVerticalCoeff_norm a σ n hp]
  exact div_le_div_of_nonneg_left (norm_nonneg _) (Real.rpow_pos_of_pos (by positivity) σ)
    (Real.rpow_le_rpow_of_exponent_le hnR hx)

 theorem density_abscissa_energy_mono (N : ℕ) (a : ℕ → ℂ) (σ x : ℝ) (hx : σ ≤ x) :
    (∑ n ∈ Finset.Icc 1 N, ‖densityVerticalCoeff a x n‖ ^ 2) ≤
      ∑ n ∈ Finset.Icc 1 N, ‖densityVerticalCoeff a σ n‖ ^ 2 := by
  apply Finset.sum_le_sum
  intro n hn
  exact pow_le_pow_left₀ (norm_nonneg _) (densityVerticalCoeff_norm_mono a σ x hx n (Finset.mem_Icc.mp hn).1) 2

 theorem density_abscissa_derivative_energy (N : ℕ) (a : ℕ → ℂ) (σ : ℝ) :
    (∑ n ∈ Finset.Icc 1 N, ‖densityVerticalCoeff (densityAbscissaDerivativeCoeff a) σ n‖ ^ 2) ≤
      (Real.log (N + 1 : ℕ)) ^ 2 * ∑ n ∈ Finset.Icc 1 N, ‖densityVerticalCoeff a σ n‖ ^ 2 := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
  have hl : 0 ≤ Real.log n := Real.log_nonneg hn1
  have hlN : Real.log n ≤ Real.log (N + 1 : ℕ) :=
    Real.log_le_log (by positivity) (by exact_mod_cast (by have := (Finset.mem_Icc.mp hn).2; omega : n ≤ N + 1))
  have he : densityVerticalCoeff (densityAbscissaDerivativeCoeff a) σ n =
      -(Real.log n : ℂ) * densityVerticalCoeff a σ n := by
    unfold densityVerticalCoeff densityAbscissaDerivativeCoeff
    ring
  rw [he, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hl, mul_pow]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hl hlN 2) (sq_nonneg _)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityDetectorWeight
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The compact quadratic Riesz weight for detecting actual zeros -/

namespace Ostmann

open Complex MeasureTheory Set

 theorem densityDetectorWeight_zero (x : ℝ) (hx : 1 ≤ x) : densityDetectorWeight x = 0 := by
  simp [densityDetectorWeight, max_eq_right (by linarith : 1 - x ≤ 0)]

 theorem densityDetectorWeight_eq (x : ℝ) (hx : x ≤ 1) :
    densityDetectorWeight x = ((1 - x) ^ 2 / 2 : ℝ) := by
  simp only [densityDetectorWeight, max_eq_left (by linarith : 0 ≤ 1 - x),
    ofReal_div, ofReal_pow, ofReal_ofNat]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityDetectorPolynomial
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original polynomial alternative as one common coefficient sequence -/

namespace Ostmann

open Complex
open scoped BigOperators Classical

 theorem densityDetectorWeight_norm_le_one (x : ℝ) (hx : 0 ≤ x) : ‖densityDetectorWeight x‖ ≤ 1 := by
  by_cases h1 : 1 ≤ x
  · rw [densityDetectorWeight_zero x h1, norm_zero]
    norm_num
  · have hle : x ≤ 1 := le_of_not_ge h1
    rw [densityDetectorWeight_eq x hle, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : 0 ≤ (1 - x) ^ 2 / 2)]
    nlinarith

 theorem densityPolynomialCoefficient_norm (X : ℕ) (Y : ℝ) (hY : 0 < Y) (n : ℕ) :
    ‖densityPolynomialCoefficient X Y n‖ ≤ n.divisors.card := by
  unfold densityPolynomialCoefficient
  split_ifs
  · rw [norm_mul]
    exact (mul_le_mul (densityDetectorCoefficient_norm X n)
      (densityDetectorWeight_norm_le_one (n / Y) (by positivity)) (norm_nonneg _) (by positivity)).trans_eq (mul_one _)
  · simp

 theorem densityPolynomialCoefficient_below (X n : ℕ) (Y : ℝ) (hn : n ≤ X) :
    densityPolynomialCoefficient X Y n = 0 := by
  simp [densityPolynomialCoefficient, Nat.not_lt.mpr hn]

 theorem densityPolynomialCoefficient_above (X n : ℕ) (Y : ℝ) (hY : 0 < Y) (hn : Y ≤ n) :
    densityPolynomialCoefficient X Y n = 0 := by
  simp [densityPolynomialCoefficient, densityDetectorWeight_zero (n / Y)
    ((le_div_iff₀ hY).mpr (by simpa using hn))]

 theorem densityDetector_polynomial (χ : PrimitiveComplexCharacter) (X : ℕ) (Y β t : ℝ) :
    (∑ n ∈ (Finset.Icc 1 ⌊Y⌋₊).filter (fun n => X < n),
      LSeries.term (densityDetectorCharacterCoefficient χ X) (densityVerticalPoint β t) n *
        densityDetectorWeight (n / Y)) =
      densityCharacterPolynomial (Finset.Icc 1 ⌊Y⌋₊)
        (densityVerticalCoeff (densityPolynomialCoefficient X Y) β) χ.character t := by
  rw [Finset.sum_filter]
  unfold densityCharacterPolynomial
  apply Finset.sum_congr rfl
  intro n hn
  have hnp : 0 < n := (Finset.mem_Icc.mp hn).1
  by_cases hX : X < n
  · rw [ite_eq_left hX, LSeries.term_of_ne_zero hnp.ne', densityDetectorCharacterCoefficient,
      density_vertical_term _ β t n hnp]
    unfold densityVerticalCoeff densityPolynomialCoefficient
    rw [ite_eq_left hX]
    ring
  · simp [hX, densityVerticalCoeff, densityPolynomialCoefficient]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityShiftedDivisorEnergy
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Divisor energies for the short head and the far coefficient blocks -/

namespace Ostmann

open scoped BigOperators Classical

 theorem densityVerticalCoeff_square (a : ℕ → ℂ) (σ : ℝ) (n : ℕ) (hn : 0 < n) :
    ‖densityVerticalCoeff a σ n‖ ^ 2 = ‖a n‖ ^ 2 / (n : ℝ) ^ (2 * σ) := by
  rw [densityVerticalCoeff_norm a σ n hn, div_pow]
  congr 1
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ n)]
  congr 1
  norm_num
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityDivisorBlock
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Divisor coefficient energy on a concrete positive block -/

namespace Ostmann

open scoped BigOperators

 theorem density_divisor_block_energy (S : Finset ℕ) (M N : ℕ) (hM : 1 ≤ M)
    (hS : S ⊆ Finset.Icc M N) (a : ℕ → ℂ)
    (ha : ∀ n ∈ S, ‖a n‖ ≤ n.divisors.card) (σ : ℝ) (hσ : 0 ≤ σ) :
    (∑ n ∈ S, ‖densityVerticalCoeff a σ n‖ ^ 2) ≤
      (N : ℝ) * (1 + Real.log N) ^ 3 / (M : ℝ) ^ (2 * σ) := by
  have hMp : (0 : ℝ) < M := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hM)
  calc
    _ ≤ ∑ n ∈ S, (n.divisors.card : ℝ) ^ 2 / (M : ℝ) ^ (2 * σ) := by
      apply Finset.sum_le_sum
      intro n hn
      have hMn := (Finset.mem_Icc.mp (hS hn)).1
      have hnp : 0 < n := lt_of_lt_of_le (lt_of_lt_of_le Nat.zero_lt_one hM) hMn
      rw [densityVerticalCoeff_square a σ n hnp]
      apply (div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (ha n hn) 2) (by positivity)).trans
      exact div_le_div_of_nonneg_left (sq_nonneg _) (Real.rpow_pos_of_pos hMp _)
        (Real.rpow_le_rpow hMp.le (by exact_mod_cast hMn) (by positivity))
    _ = (∑ n ∈ S, (n.divisors.card : ℝ) ^ 2) / (M : ℝ) ^ (2 * σ) := by rw [Finset.sum_div]
    _ ≤ (∑ n ∈ Finset.Icc 1 N, (n.divisors.card : ℝ) ^ 2) / (M : ℝ) ^ (2 * σ) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro n hn
        exact Finset.mem_Icc.mpr ⟨hM.trans (Finset.mem_Icc.mp (hS hn)).1, (Finset.mem_Icc.mp (hS hn)).2⟩
      · intro n _ _
        positivity
    _ ≤ _ := div_le_div_of_nonneg_right (density_divisor_square_sum N) (by positivity)

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
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityGaussianSubset
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Gaussian hybrid means on a finite coefficient interval or subset -/

namespace Ostmann

open MeasureTheory Set
open scoped BigOperators Classical

 theorem density_sum_truncate {A : Type*} [AddCommMonoid A]
    (S U : Finset ℕ) (hS : S ⊆ U) (f : ℕ → A) :
    (∑ n ∈ U, if n ∈ S then f n else 0) = ∑ n ∈ S, f n := by
  rw [← Finset.sum_subset hS (fun n _ hn => by simp [hn])]
  exact Finset.sum_congr rfl (fun n hn => by simp [hn])

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityPrimitiveHybrid
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The hybrid sieve for the actual primitive-character index type -/

namespace Ostmann

open MeasureTheory Set
open scoped BigOperators Classical

 theorem density_primitive_hybrid_mean :
    ∃ C : ℝ, 0 < C ∧ ∀ N Q : ℕ, 1 ≤ Q → ∀ T : ℝ, 1 ≤ T →
      ∀ a : ℕ → ℂ, ∀ F : Finset PrimitiveComplexCharacter,
      (∀ χ ∈ F, χ.modulus ≤ Q) →
      (∑ χ ∈ F, ∫ t in Icc (-T) T,
        ‖densityCharacterPolynomial (Finset.Icc 1 N) a χ.character t‖ ^ 2) ≤
          C * ((N : ℝ) + (Q : ℝ) ^ 2 * T) * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 := by
  obtain ⟨C, hC, hb⟩ := hybrid_multiplicative_large_sieve
  refine ⟨C, hC, ?_⟩
  intro N Q hQ T hT a F hF
  rw [densityCharacterFamily_sum F Q hF (fun q χ => ∫ t in Icc (-T) T,
    ‖densityCharacterPolynomial (Finset.Icc 1 N) a χ t‖ ^ 2)]
  exact hb N Q hQ T hT a (densityCharacterFamily F)
    (fun q _ χ hχ => densityCharacterFamily_primitive F q χ hχ)

 theorem density_primitive_discrete_hybrid :
    ∃ C : ℝ, 0 < C ∧ ∀ N Q : ℕ, 1 ≤ Q → ∀ T : ℝ, 1 ≤ T →
      ∀ a : ℕ → ℂ, ∀ {ι : Type} (R : Finset ι) (c : ι → PrimitiveComplexCharacter) (t : ι → ℝ),
      (∀ i ∈ R, (c i).modulus ≤ Q) → (∀ i ∈ R, |t i| ≤ T) →
      (∀ i ∈ R, ∀ j ∈ R, c i = c j → i ≠ j → 1 ≤ |t i - t j|) →
      (∑ i ∈ R, ‖densityCharacterPolynomial (Finset.Icc 1 N) a (c i).character (t i)‖ ^ 2) ≤
        C * ((N : ℝ) + (Q : ℝ) ^ 2 * (T + 1)) *
          (2 + 64 * (Real.log (N + 1 : ℕ)) ^ 2) * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 := by
  obtain ⟨C, hC, hb⟩ := density_primitive_hybrid_mean
  refine ⟨C, hC, ?_⟩
  intro N Q hQ T hT a ι R c t hc ht hsep
  let F := R.image c
  have hF : ∀ χ ∈ F, χ.modulus ≤ Q := by
    intro χ hχ
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hχ
    exact hc i hi
  have hpoint (χ : PrimitiveComplexCharacter) :
      (∑ i ∈ R.filter (fun i => c i = χ),
        ‖densityCharacterPolynomial (Finset.Icc 1 N) a χ.character (t i)‖ ^ 2) ≤
      2 * (∫ u in Icc (-(T + 1)) (T + 1),
        ‖densityCharacterPolynomial (Finset.Icc 1 N) a χ.character u‖ ^ 2) +
        ∫ u in Icc (-(T + 1)) (T + 1),
          ‖densityCharacterPolynomial (Finset.Icc 1 N) (densityDerivativeCoeff a) χ.character u‖ ^ 2 := by
    have hder (n : ℕ) : densityDerivativeCoeff (fun m => a m * χ.character (m : ZMod χ.modulus)) n =
        densityDerivativeCoeff a n * χ.character (n : ZMod χ.modulus) := by
      unfold densityDerivativeCoeff
      ring
    have h := density_separated_samples (R.filter (fun i => c i = χ)) t T
      (fun i hi => ht i (Finset.mem_filter.mp hi).1)
      (fun i hi j hj hij => hsep i (Finset.mem_filter.mp hi).1 j (Finset.mem_filter.mp hj).1
        ((Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hj).2.symm) hij)
      (fun u => ∑ n ∈ Finset.Icc 1 N, (a n * χ.character (n : ZMod χ.modulus)) *
        realAdditivePhase (-(Real.log n * u)))
      (fun u => ∑ n ∈ Finset.Icc 1 N,
        densityDerivativeCoeff (fun m => a m * χ.character (m : ZMod χ.modulus)) n *
          realAdditivePhase (-(Real.log n * u)))
      (density_polynomial_hasDerivAt _ _) (density_polynomial_continuous _ _)
    simpa only [hder, densityCharacterPolynomial, show -T - 1 = -(T + 1) by ring] using h
  have he : (∑ i ∈ R, ‖densityCharacterPolynomial (Finset.Icc 1 N) a (c i).character (t i)‖ ^ 2) =
      ∑ χ ∈ F, ∑ i ∈ R.filter (fun i => c i = χ),
        ‖densityCharacterPolynomial (Finset.Icc 1 N) a χ.character (t i)‖ ^ 2 := by
    have hmap : ∀ i ∈ R, c i ∈ F := fun i hi => Finset.mem_image.mpr ⟨i, hi, rfl⟩
    rw [← Finset.sum_fiberwise_of_maps_to hmap]
    apply Finset.sum_congr rfl
    intro χ _
    apply Finset.sum_congr rfl
    intro i hi
    rw [(Finset.mem_filter.mp hi).2]
  rw [he]
  have hs := Finset.sum_le_sum (s := F) (fun χ _ => hpoint χ)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hs
  have ha := hb N Q hQ (T + 1) (by linarith) a F hF
  have hd := hb N Q hQ (T + 1) (by linarith) (densityDerivativeCoeff a) F hF
  have hd' := hd.trans (mul_le_mul_of_nonneg_left (density_derivative_coefficient_bound N a) (by positivity))
  apply hs.trans
  have h := add_le_add (mul_le_mul_of_nonneg_left ha (by norm_num : (0 : ℝ) ≤ 2)) hd'
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityVariableAbscissaSieve
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The hybrid sieve with different real parts at the sampled zeros -/

namespace Ostmann

open MeasureTheory Set
open scoped BigOperators Classical

 theorem density_variable_abscissa_sieve :
    ∃ C : ℝ, 0 < C ∧ ∀ N Q : ℕ, 1 ≤ Q → ∀ T σ : ℝ, 1 ≤ T → 0 ≤ σ → σ ≤ 1 →
      ∀ a : ℕ → ℂ, ∀ {ι : Type} (R : Finset ι) (c : ι → PrimitiveComplexCharacter) (t β : ι → ℝ),
      (∀ i ∈ R, (c i).modulus ≤ Q) → (∀ i ∈ R, |t i| ≤ T) →
      (∀ i ∈ R, ∀ j ∈ R, c i = c j → i ≠ j → 1 ≤ |t i - t j|) →
      (∀ i ∈ R, σ ≤ β i ∧ β i ≤ 1) →
      (∑ i ∈ R, ‖densityCharacterPolynomial (Finset.Icc 1 N)
        (densityVerticalCoeff a (β i)) (c i).character (t i)‖ ^ 2) ≤
      C * ((N : ℝ) + (Q : ℝ) ^ 2 * (T + 1)) *
        (2 + 64 * (Real.log (N + 1 : ℕ)) ^ 2) * (2 + (Real.log (N + 1 : ℕ)) ^ 2) *
          ∑ n ∈ Finset.Icc 1 N, ‖densityVerticalCoeff a σ n‖ ^ 2 := by
  obtain ⟨C, hC, hb⟩ := density_primitive_discrete_hybrid
  refine ⟨2 * C, by positivity, ?_⟩
  intro N Q hQ T σ hT hσ0 hσ1 a ι R c t β hc ht hs hβ
  let E := ∑ n ∈ Finset.Icc 1 N, ‖densityVerticalCoeff a σ n‖ ^ 2
  let K := C * ((N : ℝ) + (Q : ℝ) ^ 2 * (T + 1)) * (2 + 64 * (Real.log (N + 1 : ℕ)) ^ 2)
  let F := fun x : ℝ => ∑ i ∈ R, ‖densityCharacterPolynomial (Finset.Icc 1 N)
    (densityVerticalCoeff a x) (c i).character (t i)‖ ^ 2
  let G := fun x : ℝ => ∑ i ∈ R, ‖densityCharacterPolynomial (Finset.Icc 1 N)
    (densityVerticalCoeff (densityAbscissaDerivativeCoeff a) x) (c i).character (t i)‖ ^ 2
  have hpos (n : ℕ) (hn : n ∈ Finset.Icc 1 N) : 0 < n := (Finset.mem_Icc.mp hn).1
  have hFc : Continuous F := continuous_finsetSum R (fun i _ =>
    ((density_abscissa_polynomial_continuous _ hpos a (c i).character (t i)).norm.pow 2))
  have hGc : Continuous G := continuous_finsetSum R (fun i _ =>
    ((density_abscissa_polynomial_continuous _ hpos (densityAbscissaDerivativeCoeff a) (c i).character (t i)).norm.pow 2))
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hE : 0 ≤ E := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hFb (x : ℝ) (hx : x ∈ Icc σ 2) : F x ≤ K * E := by
    have h := hb N Q hQ T hT (densityVerticalCoeff a x) R c t hc ht hs
    exact h.trans (mul_le_mul_of_nonneg_left (density_abscissa_energy_mono N a σ x hx.1) hK)
  have hGb (x : ℝ) (hx : x ∈ Icc σ 2) : G x ≤ K * ((Real.log (N + 1 : ℕ)) ^ 2 * E) := by
    have h := hb N Q hQ T hT (densityVerticalCoeff (densityAbscissaDerivativeCoeff a) x) R c t hc ht hs
    have he := (density_abscissa_energy_mono N (densityAbscissaDerivativeCoeff a) σ x hx.1).trans
      (density_abscissa_derivative_energy N a σ)
    exact h.trans (mul_le_mul_of_nonneg_left he hK)
  have hσ2 : σ ≤ 2 := by linarith
  have hIF : (∫ x in σ..2, F x) ≤ 2 * (K * E) := by
    have h := intervalIntegral.integral_mono_on (μ := volume) hσ2 (hFc.intervalIntegrable σ 2)
      intervalIntegrable_const hFb
    rw [intervalIntegral.integral_const, smul_eq_mul] at h
    exact h.trans (mul_le_mul_of_nonneg_right (by linarith : 2 - σ ≤ 2) (mul_nonneg hK hE))
  have hIG : (∫ x in σ..2, G x) ≤ 2 * (K * ((Real.log (N + 1 : ℕ)) ^ 2 * E)) := by
    have h := intervalIntegral.integral_mono_on (μ := volume) hσ2 (hGc.intervalIntegrable σ 2)
      intervalIntegrable_const hGb
    rw [intervalIntegral.integral_const, smul_eq_mul] at h
    exact h.trans (mul_le_mul_of_nonneg_right (by linarith : 2 - σ ≤ 2) (by positivity))
  have hsample := Finset.sum_le_sum (s := R) (fun i hi =>
    density_abscissa_polynomial_sample (Finset.Icc 1 N) hpos a (c i).character (t i) σ (β i)
      (hβ i hi).1 (hβ i hi).2)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hsample
  have heF : (∫ x in σ..2, F x) = ∑ i ∈ R, ∫ x in σ..2,
      ‖densityCharacterPolynomial (Finset.Icc 1 N) (densityVerticalCoeff a x) (c i).character (t i)‖ ^ 2 := by
    simpa only [F, Pi.pow_apply] using intervalIntegral.integral_finsetSum
      (μ := volume) (fun i (_hi : i ∈ R) =>
        ((density_abscissa_polynomial_continuous _ hpos a (c i).character (t i)).norm.pow 2).intervalIntegrable σ 2)
  have heG : (∫ x in σ..2, G x) = ∑ i ∈ R, ∫ x in σ..2,
      ‖densityCharacterPolynomial (Finset.Icc 1 N)
        (densityVerticalCoeff (densityAbscissaDerivativeCoeff a) x) (c i).character (t i)‖ ^ 2 := by
    simpa only [G, Pi.pow_apply] using intervalIntegral.integral_finsetSum
      (μ := volume) (fun i (_hi : i ∈ R) =>
        ((density_abscissa_polynomial_continuous _ hpos (densityAbscissaDerivativeCoeff a)
          (c i).character (t i)).norm.pow 2).intervalIntegrable σ 2)
  rw [← heF, ← heG] at hsample
  apply hsample.trans
  have h := add_le_add (mul_le_mul_of_nonneg_left hIF (by norm_num : (0 : ℝ) ≤ 2)) hIG
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  dsimp [K, E]
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensitySubsetAbscissaSieve
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Variable-abscissa sieve on a concrete coefficient block -/

namespace Ostmann

open scoped BigOperators Classical

 theorem density_subset_abscissa_sieve :
    ∃ C : ℝ, 0 < C ∧ ∀ N Q : ℕ, 1 ≤ Q → ∀ T σ : ℝ, 1 ≤ T → 0 ≤ σ → σ ≤ 1 →
      ∀ U : Finset ℕ, U ⊆ Finset.Icc 1 N → ∀ a : ℕ → ℂ,
      ∀ {ι : Type} (R : Finset ι) (c : ι → PrimitiveComplexCharacter) (t β : ι → ℝ),
      (∀ i ∈ R, (c i).modulus ≤ Q) → (∀ i ∈ R, |t i| ≤ T) →
      (∀ i ∈ R, ∀ j ∈ R, c i = c j → i ≠ j → 1 ≤ |t i - t j|) →
      (∀ i ∈ R, σ ≤ β i ∧ β i ≤ 1) →
      (∑ i ∈ R, ‖densityCharacterPolynomial U
        (densityVerticalCoeff a (β i)) (c i).character (t i)‖ ^ 2) ≤
      C * ((N : ℝ) + (Q : ℝ) ^ 2 * (T + 1)) *
        (2 + 64 * (Real.log (N + 1 : ℕ)) ^ 2) * (2 + (Real.log (N + 1 : ℕ)) ^ 2) *
          ∑ n ∈ U, ‖densityVerticalCoeff a σ n‖ ^ 2 := by
  obtain ⟨C, hC, hb⟩ := density_variable_abscissa_sieve
  refine ⟨C, hC, ?_⟩
  intro N Q hQ T σ hT hσ0 hσ1 U hU a ι R c t β hc ht hs hβ
  let b : ℕ → ℂ := fun n => if n ∈ U then a n else 0
  have hp (χ : PrimitiveComplexCharacter) (x u : ℝ) :
      densityCharacterPolynomial (Finset.Icc 1 N) (densityVerticalCoeff b x) χ.character u =
        densityCharacterPolynomial U (densityVerticalCoeff a x) χ.character u := by
    unfold densityCharacterPolynomial
    convert density_sum_truncate U (Finset.Icc 1 N) hU
      (fun n => densityVerticalCoeff a x n * χ.character (n : ZMod χ.modulus) *
        realAdditivePhase (-(Real.log n * u))) using 1
    all_goals try with_reducible_and_instances rfl
    apply Finset.sum_congr rfl
    intro n _
    by_cases hn : n ∈ U <;> simp [b, densityVerticalCoeff, hn]
  have he : (∑ n ∈ Finset.Icc 1 N, ‖densityVerticalCoeff b σ n‖ ^ 2) =
      ∑ n ∈ U, ‖densityVerticalCoeff a σ n‖ ^ 2 := by
    convert density_sum_truncate U (Finset.Icc 1 N) hU
      (fun n => ‖densityVerticalCoeff a σ n‖ ^ 2) using 1
    all_goals try with_reducible_and_instances rfl
    apply Finset.sum_congr rfl
    intro n _
    by_cases hn : n ∈ U <;> simp [b, densityVerticalCoeff, hn]
  simpa only [hp, he] using hb N Q hQ T σ hT hσ0 hσ1 b R c t β hc ht hs hβ

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityDivisorBlockSieve
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The variable-abscissa sieve on a divisor-bounded coefficient block -/

namespace Ostmann

open scoped BigOperators Classical

 theorem density_divisor_block_sieve :
    ∃ C : ℝ, 0 < C ∧ ∀ M N Q : ℕ, 1 ≤ M → 1 ≤ Q →
      ∀ T σ : ℝ, 1 ≤ T → 0 ≤ σ → σ ≤ 1 →
      ∀ U : Finset ℕ, U ⊆ Finset.Icc M N → ∀ a : ℕ → ℂ,
      (∀ n ∈ U, ‖a n‖ ≤ n.divisors.card) →
      ∀ {ι : Type} (R : Finset ι) (c : ι → PrimitiveComplexCharacter) (t β : ι → ℝ),
      (∀ i ∈ R, (c i).modulus ≤ Q) → (∀ i ∈ R, |t i| ≤ T) →
      (∀ i ∈ R, ∀ j ∈ R, c i = c j → i ≠ j → 1 ≤ |t i - t j|) →
      (∀ i ∈ R, σ ≤ β i ∧ β i ≤ 1) →
      (∑ i ∈ R, ‖densityCharacterPolynomial U
        (densityVerticalCoeff a (β i)) (c i).character (t i)‖ ^ 2) ≤
      C * ((N : ℝ) + (Q : ℝ) ^ 2 * (T + 1)) *
        (2 + 64 * (Real.log (N + 1 : ℕ)) ^ 2) * (2 + (Real.log (N + 1 : ℕ)) ^ 2) *
          ((N : ℝ) * (1 + Real.log N) ^ 3 / (M : ℝ) ^ (2 * σ)) := by
  obtain ⟨C, hC, hb⟩ := density_subset_abscissa_sieve
  refine ⟨C, hC, ?_⟩
  intro M N Q hM hQ T σ hT hσ0 hσ1 U hU a ha ι R c t β hc ht hs hβ
  have hU1 : U ⊆ Finset.Icc 1 N := by
    intro n hn
    obtain ⟨hMn, hnN⟩ := Finset.mem_Icc.mp (hU hn)
    exact Finset.mem_Icc.mpr ⟨hM.trans hMn, hnN⟩
  have h := hb N Q hQ T σ hT hσ0 hσ1 U hU1 a R c t β hc ht hs hβ
  exact h.trans (mul_le_mul_of_nonneg_left
    (density_divisor_block_energy U M N hM hU a ha σ hσ0) (by positivity))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityDyadicBlockCost
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The sharp length cost of one dyadic detector block -/

namespace Ostmann

 theorem density_dyadic_power_cost (m Y Q T σ : ℝ) (hm : 0 < m) (hmY : m ≤ Y)
    (hT : 1 ≤ T) (_hσ : 1 / 2 ≤ σ) (hσ1 : σ ≤ 1) :
    ((2 * m + Q ^ 2 * (T + 1)) * (2 * m)) / m ^ (2 * σ) ≤
      4 * (Y ^ (2 - 2 * σ) + (Q ^ 2 * T) * m ^ (1 - 2 * σ)) := by
  have hq : Q ^ 2 * (T + 1) ≤ 2 * (Q ^ 2 * T) := by nlinarith [sq_nonneg Q]
  have hfirst := Real.rpow_le_rpow hm.le hmY (by linarith : 0 ≤ 2 - 2 * σ)
  have hpower2 : m ^ (2 - 2 * σ) = m ^ 2 / m ^ (2 * σ) := by
    rw [Real.rpow_sub hm, Real.rpow_two]
  have hpower1 : m ^ (1 - 2 * σ) = m / m ^ (2 * σ) := by
    rw [Real.rpow_sub hm, Real.rpow_one]
  calc
    _ ≤ (4 * (m + Q ^ 2 * T) * m) / m ^ (2 * σ) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      nlinarith
    _ = 4 * (m ^ (2 - 2 * σ) + (Q ^ 2 * T) * m ^ (1 - 2 * σ)) := by
      rw [hpower2, hpower1]
      ring
    _ ≤ _ := by gcongr

 theorem density_dyadic_log_cost (m Y : ℝ) (hm : 1 ≤ m) (hmY : m ≤ Y) :
    (2 + 64 * (Real.log (2 * m + 1)) ^ 2) * (2 + (Real.log (2 * m + 1)) ^ 2) *
      (1 + Real.log (2 * m)) ^ 3 ≤ 198 * (1 + Real.log (2 * Y + 1)) ^ 7 := by
  let L := 1 + Real.log (2 * Y + 1)
  have hY : 1 ≤ Y := hm.trans hmY
  have hlog : 0 ≤ Real.log (2 * Y + 1) := Real.log_nonneg (by linarith)
  have hL : 1 ≤ L := by dsimp [L]; linarith
  have h1 : 0 ≤ Real.log (2 * m + 1) := Real.log_nonneg (by linarith)
  have h1L : Real.log (2 * m + 1) ≤ L := by
    have h := Real.log_le_log (by linarith : 0 < 2 * m + 1) (by linarith : 2 * m + 1 ≤ 2 * Y + 1)
    dsimp [L]
    linarith
  have hs : (Real.log (2 * m + 1)) ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ h1 h1L 2
  have hL2 : 1 ≤ L ^ 2 := one_le_pow₀ hL
  have ha : 2 + 64 * (Real.log (2 * m + 1)) ^ 2 ≤ 66 * L ^ 2 := by nlinarith
  have hb : 2 + (Real.log (2 * m + 1)) ^ 2 ≤ 3 * L ^ 2 := by nlinarith
  have hc0 : 0 ≤ 1 + Real.log (2 * m) := by
    have h := Real.log_nonneg (by linarith : 1 ≤ 2 * m)
    linarith
  have hc : 1 + Real.log (2 * m) ≤ L := by
    dsimp [L]
    have h : Real.log (2 * m) ≤ Real.log (2 * Y + 1) :=
      Real.log_le_log (by linarith : 0 < 2 * m) (by linarith : 2 * m ≤ 2 * Y + 1)
    exact add_le_add le_rfl h
  calc
    _ ≤ (66 * L ^ 2) * (3 * L ^ 2) * L ^ 3 := by
      exact mul_le_mul (mul_le_mul ha hb (by positivity) (by positivity))
        (pow_le_pow_left₀ hc0 hc 3) (by positivity) (by positivity)
    _ = _ := by dsimp [L]; ring

 theorem density_dyadic_total_cost (C x m Y Q T σ : ℝ) (hC : 0 ≤ C)
    (hx : 1 ≤ x) (hxm : x ≤ m) (hmY : m ≤ Y) (hT : 1 ≤ T)
    (hσ : 1 / 2 ≤ σ) (hσ1 : σ ≤ 1) :
    C * (2 * m + Q ^ 2 * (T + 1)) *
      (2 + 64 * (Real.log (2 * m + 1)) ^ 2) * (2 + (Real.log (2 * m + 1)) ^ 2) *
      (2 * m * (1 + Real.log (2 * m)) ^ 3 / m ^ (2 * σ)) ≤
    (792 * C) * (1 + Real.log (2 * Y + 1)) ^ 7 *
      (Y ^ (2 - 2 * σ) + Q ^ 2 * T * x ^ (1 - 2 * σ)) := by
  have hm : 0 < m := by linarith
  have hlogY : 0 ≤ Real.log (2 * Y + 1) := Real.log_nonneg (by linarith)
  have hl := density_dyadic_log_cost m Y (hx.trans hxm) hmY
  have hp := density_dyadic_power_cost m Y Q T σ hm hmY hT hσ hσ1
  have hr := Real.rpow_le_rpow_of_nonpos (by linarith : 0 < x) hxm (by linarith : 1 - 2 * σ ≤ 0)
  have hp' : ((2 * m + Q ^ 2 * (T + 1)) * (2 * m)) / m ^ (2 * σ) ≤
      4 * (Y ^ (2 - 2 * σ) + Q ^ 2 * T * x ^ (1 - 2 * σ)) := by
    apply hp.trans
    gcongr
  calc
    _ = C * ((2 + 64 * (Real.log (2 * m + 1)) ^ 2) * (2 + (Real.log (2 * m + 1)) ^ 2) *
      (1 + Real.log (2 * m)) ^ 3) * (((2 * m + Q ^ 2 * (T + 1)) * (2 * m)) / m ^ (2 * σ)) := by ring
    _ ≤ C * (198 * (1 + Real.log (2 * Y + 1)) ^ 7) *
        (4 * (Y ^ (2 - 2 * σ) + Q ^ 2 * T * x ^ (1 - 2 * σ))) := by
      apply mul_le_mul (mul_le_mul_of_nonneg_left hl hC) hp' (by positivity) (by positivity)
    _ = _ := by ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityActualBlock
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform estimates for the actual detector's dyadic blocks -/

namespace Ostmann

open scoped BigOperators Classical

 theorem density_actual_block_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ X M Q : ℕ, 1 ≤ X → X ≤ M → 1 ≤ Q →
      ∀ Y T σ : ℝ, 2 ≤ Y → 1 ≤ T → 1 / 2 ≤ σ → σ ≤ 1 →
      ∀ {ι : Type} (R : Finset ι) (c : ι → PrimitiveComplexCharacter) (t β : ι → ℝ),
      (∀ i ∈ R, (c i).modulus ≤ Q) → (∀ i ∈ R, |t i| ≤ T) →
      (∀ i ∈ R, ∀ j ∈ R, c i = c j → i ≠ j → 1 ≤ |t i - t j|) →
      (∀ i ∈ R, σ ≤ β i ∧ β i ≤ 1) →
      (∑ i ∈ R, ‖densityCharacterPolynomial (Finset.Ioc M (2 * M))
        (densityVerticalCoeff (densityPolynomialCoefficient X Y) (β i)) (c i).character (t i)‖ ^ 2) ≤
        C * (1 + Real.log (2 * Y + 1)) ^ 7 *
          (Y ^ (2 - 2 * σ) + (Q : ℝ) ^ 2 * T * (X : ℝ) ^ (1 - 2 * σ)) := by
  obtain ⟨C, hC, hb⟩ := density_divisor_block_sieve
  refine ⟨792 * C, by positivity, ?_⟩
  intro X M Q hX hXM hQ Y T σ hY hT hσ hσ1 ι R c t β hc ht hs hβ
  have hM : 1 ≤ M := hX.trans hXM
  have hXp : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hMp : (0 : ℝ) < M := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hM)
  by_cases hMY : (M : ℝ) ≤ Y
  · have hU : Finset.Ioc M (2 * M) ⊆ Finset.Icc M (2 * M) := by
      intro n hn
      exact Finset.mem_Icc.mpr ⟨(Finset.mem_Ioc.mp hn).1.le, (Finset.mem_Ioc.mp hn).2⟩
    have h := hb M (2 * M) Q hM hQ T σ hT (by linarith) hσ1 _ hU
      (densityPolynomialCoefficient X Y)
      (fun n _ => densityPolynomialCoefficient_norm X Y (by linarith) n) R c t β hc ht hs hβ
    have hcost := density_dyadic_total_cost C X M Y Q T σ hC.le hXp
      (by exact_mod_cast hXM) hMY hT hσ hσ1
    apply h.trans
    simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] using hcost
  · have hz (i : ι) : densityCharacterPolynomial (Finset.Ioc M (2 * M))
        (densityVerticalCoeff (densityPolynomialCoefficient X Y) (β i)) (c i).character (t i) = 0 := by
      unfold densityCharacterPolynomial
      apply Finset.sum_eq_zero
      intro n hn
      have hyn : Y ≤ n := (le_of_not_ge hMY).trans (by exact_mod_cast (Finset.mem_Ioc.mp hn).1.le)
      rw [densityVerticalCoeff, densityPolynomialCoefficient_above X n Y (by linarith) hyn]
      simp
    simp only [hz, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), Finset.sum_const_zero]
    have hl : 0 ≤ Real.log (2 * Y + 1) := Real.log_nonneg (by linarith)
    positivity

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityBalanceParameters
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The conductor-height parameters in the two zero-detector estimates -/

namespace Ostmann

 theorem density_conductor_height_log (Q : ℕ) (hQ : 1 ≤ Q) (T : ℝ) (hT : 2 ≤ T) :
    Real.log ((Q : ℝ) ^ 2 * T) ≤ 2 * Real.log ((Q : ℝ) * T) := by
  have hq : (0 : ℝ) < Q := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hQ)
  have ht : 0 < T := by linarith
  rw [Real.log_mul (by positivity) ht.ne', Real.log_pow,
    Real.log_mul hq.ne' ht.ne']
  have hl : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  norm_num only [Nat.cast_ofNat]
  linarith

 theorem density_balance_at_least_one (σ : ℝ) (hσ : 1 / 2 ≤ σ) (hσ1 : σ ≤ 1) :
    1 ≤ densityBalanceExponent σ := by
  unfold densityBalanceExponent
  apply (le_div_iff₀ (by linarith : 0 < 2 * (2 - σ))).mpr
  linarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityBlockCauchy
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Combining the finite coefficient blocks without a length loss -/

namespace Ostmann

open MeasureTheory Set
open scoped BigOperators Classical

 theorem density_weighted_sum_norm_sq {ι : Type*} (S : Finset ι)
    (f : ι → ℂ) (w : ι → ℝ) (hw : ∀ i ∈ S, 0 < w i) :
    ‖∑ i ∈ S, f i‖ ^ 2 ≤ (∑ i ∈ S, w i) * ∑ i ∈ S, ‖f i‖ ^ 2 / w i := by
  apply (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2).trans
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul S
    (fun i hi => (hw i hi).le) (fun i hi => div_nonneg (sq_nonneg _) (hw i hi).le)
  intro i hi
  rw [mul_div_cancel₀ _ (hw i hi).ne']

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityDyadicPartition
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual coefficient head and consecutive dyadic blocks -/

namespace Ostmann

open scoped BigOperators Classical

 theorem density_dyadic_partition (N J : ℕ) (hN : 1 ≤ N) (a : ℕ → ℂ) :
    (∑ n ∈ Finset.Icc 1 (2 ^ J * N), a n) =
      (∑ n ∈ Finset.Icc 1 N, a n) +
        ∑ j ∈ Finset.range J, ∑ n ∈ Finset.Ioc (2 ^ j * N) (2 ^ (j + 1) * N), a n := by
  induction J with
  | zero => simp
  | succ J ih =>
    have hM : 1 ≤ 2 ^ J * N := one_le_mul (one_le_pow₀ (by norm_num)) hN
    have hE : 2 ^ J * N ≤ 2 ^ (J + 1) * N := by rw [pow_succ]; nlinarith
    have he : Finset.Icc 1 (2 ^ (J + 1) * N) =
        Finset.Icc 1 (2 ^ J * N) ∪ Finset.Ioc (2 ^ J * N) (2 ^ (J + 1) * N) := by
      ext n
      simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ioc]
      omega
    have hd : Disjoint (Finset.Icc 1 (2 ^ J * N))
        (Finset.Ioc (2 ^ J * N) (2 ^ (J + 1) * N)) := by
      apply Finset.disjoint_left.mpr
      intro n hn hm
      have hn' := (Finset.mem_Icc.mp hn).2
      have hm' := (Finset.mem_Ioc.mp hm).1
      omega
    rw [he, Finset.sum_union hd, ih, Finset.sum_range_succ]
    ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityDetectorBlocks
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact dyadic decomposition of the original polynomial alternative -/

namespace Ostmann

open scoped BigOperators Classical

 theorem densityDetector_polynomial_extended (χ : PrimitiveComplexCharacter) (X N : ℕ)
    (Y : ℝ) (hY : 0 < Y) (hN : ⌊Y⌋₊ ≤ N) (β t : ℝ) :
    (∑ n ∈ (Finset.Icc 1 ⌊Y⌋₊).filter (fun n => X < n),
      LSeries.term (densityDetectorCharacterCoefficient χ X) (densityVerticalPoint β t) n *
        densityDetectorWeight (n / Y)) =
      densityCharacterPolynomial (Finset.Icc 1 N)
        (densityVerticalCoeff (densityPolynomialCoefficient X Y) β) χ.character t := by
  rw [densityDetector_polynomial]
  unfold densityCharacterPolynomial
  apply Finset.sum_subset
  · intro n hn
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hn).1, (Finset.mem_Icc.mp hn).2.trans hN⟩
  · intro n hn hn'
    have hn1 := (Finset.mem_Icc.mp hn).1
    have hfloor : ⌊Y⌋₊ < n := by
      have hnnot : ¬ n ≤ ⌊Y⌋₊ := fun h => hn' (Finset.mem_Icc.mpr ⟨hn1, h⟩)
      omega
    have hyn : Y < n := (Nat.floor_lt hY.le).mp hfloor
    rw [densityVerticalCoeff, densityPolynomialCoefficient_above X n Y hY hyn.le]
    simp

 theorem densityDetector_polynomial_blocks (χ : PrimitiveComplexCharacter) (X J : ℕ)
    (hX : 1 ≤ X) (Y : ℝ) (hY : 0 < Y) (hcover : ⌊Y⌋₊ ≤ 2 ^ J * X) (β t : ℝ) :
    (∑ n ∈ (Finset.Icc 1 ⌊Y⌋₊).filter (fun n => X < n),
      LSeries.term (densityDetectorCharacterCoefficient χ X) (densityVerticalPoint β t) n *
        densityDetectorWeight (n / Y)) =
      ∑ j ∈ Finset.range J, densityCharacterPolynomial
        (Finset.Ioc (2 ^ j * X) (2 * (2 ^ j * X)))
        (densityVerticalCoeff (densityPolynomialCoefficient X Y) β) χ.character t := by
  rw [densityDetector_polynomial_extended χ X (2 ^ J * X) Y hY hcover]
  unfold densityCharacterPolynomial
  rw [density_dyadic_partition X J hX]
  have hhead : (∑ n ∈ Finset.Icc 1 X,
      densityVerticalCoeff (densityPolynomialCoefficient X Y) β n * χ.character (n : ZMod χ.modulus) *
        realAdditivePhase (-(Real.log n * t))) = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    rw [densityVerticalCoeff, densityPolynomialCoefficient_below X n Y (Finset.mem_Icc.mp hn).2]
    simp
  rw [hhead, zero_add]
  apply Finset.sum_congr rfl
  intro j _
  congr 2
  rw [pow_succ]
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityDetectorDyadicCover
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A logarithmic number of blocks covers the detector polynomial -/

namespace Ostmann

 theorem density_detector_dyadic_cover (X : ℕ) (hX : 1 ≤ X) (Y : ℝ) (hY : 2 ≤ Y) :
    ∃ J : ℕ, 1 ≤ J ∧ ⌊Y⌋₊ ≤ 2 ^ J * X ∧
      (J : ℝ) ≤ (2 / Real.log 2) * Real.log Y := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlY : Real.log 2 ≤ Real.log Y := Real.log_le_log (by norm_num) hY
  have hratio : 1 ≤ Real.log Y / Real.log 2 := (le_div_iff₀ hl2).mpr (by simpa using hlY)
  let J := ⌈Real.log Y / Real.log 2⌉₊
  have hj : Real.log Y / Real.log 2 ≤ J := Nat.le_ceil _
  have hj1 : 1 ≤ J := by exact_mod_cast (hratio.trans hj)
  have hjup : (J : ℝ) < Real.log Y / Real.log 2 + 1 :=
    Nat.ceil_lt_add_one (by linarith : 0 ≤ Real.log Y / Real.log 2)
  have hlog : Real.log Y ≤ (J : ℝ) * Real.log 2 := (div_le_iff₀ hl2).mp hj
  have hpow : Y ≤ (2 : ℝ) ^ J := by
    apply (Real.log_le_log_iff (by linarith : 0 < Y) (by positivity)).mp
    simpa only [Real.log_pow] using hlog
  have hx : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hfloor : (⌊Y⌋₊ : ℝ) ≤ (2 : ℝ) ^ J * X := by
    apply (Nat.floor_le (by linarith : 0 ≤ Y)).trans
    exact hpow.trans (le_mul_of_one_le_right (by positivity) hx)
  refine ⟨J, hj1, by exact_mod_cast hfloor, ?_⟩
  have hratio2 : Real.log Y / Real.log 2 + 1 ≤ 2 * (Real.log Y / Real.log 2) := by linarith
  have he : 2 * (Real.log Y / Real.log 2) = (2 / Real.log 2) * Real.log Y := by ring
  exact hjup.le.trans (hratio2.trans_eq he)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityFiniteBlockSquare
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Summing finitely many actual polynomial blocks -/

namespace Ostmann

open scoped BigOperators

 theorem density_finite_block_square {ι : Type*} (R : Finset ι) (J : ℕ) (f : ι → ℕ → ℂ) :
    (∑ i ∈ R, ‖∑ j ∈ Finset.range J, f i j‖ ^ 2) ≤
      (J : ℝ) * ∑ j ∈ Finset.range J, ∑ i ∈ R, ‖f i j‖ ^ 2 := by
  calc
    _ ≤ ∑ i ∈ R, (J : ℝ) * ∑ j ∈ Finset.range J, ‖f i j‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      simpa using density_weighted_sum_norm_sq (Finset.range J) (f i) (fun _ => (1 : ℝ))
        (fun _ _ => by norm_num)
    _ = _ := by rw [← Finset.mul_sum, Finset.sum_comm]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityPolynomialAlternative
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Counting the polynomial alternative with its actual compact coefficients -/

namespace Ostmann

open scoped BigOperators Classical

 theorem density_polynomial_alternative_count :
    ∃ C : ℝ, 0 < C ∧ ∀ X Q : ℕ, 1 ≤ X → 1 ≤ Q → ∀ Y T σ : ℝ,
      2 ≤ Y → 1 ≤ T → 1 / 2 ≤ σ → σ ≤ 1 →
      ∀ {ι : Type} (R : Finset ι) (c : ι → PrimitiveComplexCharacter) (t β : ι → ℝ),
      (∀ i ∈ R, (c i).modulus ≤ Q) → (∀ i ∈ R, |t i| ≤ T) →
      (∀ i ∈ R, ∀ j ∈ R, c i = c j → i ≠ j → 1 ≤ |t i - t j|) →
      (∀ i ∈ R, σ ≤ β i ∧ β i ≤ 1) →
      (∀ i ∈ R, (1 / 8 : ℝ) ≤ ‖∑ n ∈ (Finset.Icc 1 ⌊Y⌋₊).filter (fun n => X < n),
        LSeries.term (densityDetectorCharacterCoefficient (c i) X) (densityVerticalPoint (β i) (t i)) n *
          densityDetectorWeight (n / Y)‖) →
      (R.card : ℝ) ≤ C * (1 + Real.log (2 * Y + 1)) ^ 9 *
        (Y ^ (2 - 2 * σ) + (Q : ℝ) ^ 2 * T * (X : ℝ) ^ (1 - 2 * σ)) := by
  obtain ⟨C, hC, hb⟩ := density_actual_block_bound
  let A := 2 / Real.log 2
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨64 * C * A ^ 2, by positivity, ?_⟩
  intro X Q hX hQ Y T σ hY hT hσ hσ1 ι R c t β hc ht hs hβ hlarge
  obtain ⟨J, _hJ, hcover, hJbound⟩ := density_detector_dyadic_cover X hX Y hY
  let L := 1 + Real.log (2 * Y + 1)
  let G := Y ^ (2 - 2 * σ) + (Q : ℝ) ^ 2 * T * (X : ℝ) ^ (1 - 2 * σ)
  let f := fun i j => densityCharacterPolynomial (Finset.Ioc (2 ^ j * X) (2 * (2 ^ j * X)))
    (densityVerticalCoeff (densityPolynomialCoefficient X Y) (β i)) (c i).character (t i)
  have hL0 : 0 ≤ L := by
    have h := Real.log_nonneg (by linarith : 1 ≤ 2 * Y + 1)
    dsimp [L]
    linarith
  have hG : 0 ≤ G := by dsimp [G]; positivity
  have hblock (j : ℕ) : (∑ i ∈ R, ‖f i j‖ ^ 2) ≤ C * L ^ 7 * G := by
    apply hb X (2 ^ j * X) Q hX _ hQ Y T σ hY hT hσ hσ1 R c t β hc ht hs hβ
    exact Nat.le_mul_of_pos_left X (by positivity)
  have hlower : (R.card : ℝ) / 64 ≤ ∑ i ∈ R, ‖∑ j ∈ Finset.range J, f i j‖ ^ 2 := by
    have h := Finset.sum_le_sum (s := R) (fun i hi => show (1 / 64 : ℝ) ≤ ‖∑ j ∈ Finset.range J, f i j‖ ^ 2 from by
      have hh := hlarge i hi
      rw [densityDetector_polynomial_blocks (c i) X J hX Y (by linarith) hcover] at hh
      change (1 / 8 : ℝ) ≤ ‖∑ j ∈ Finset.range J, f i j‖ at hh
      nlinarith [norm_nonneg (∑ j ∈ Finset.range J, f i j)])
    simpa only [Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv, one_mul] using h
  have hupper : (∑ i ∈ R, ‖∑ j ∈ Finset.range J, f i j‖ ^ 2) ≤
      (J : ℝ) ^ 2 * (C * L ^ 7 * G) := by
    apply (density_finite_block_square R J f).trans
    have h := mul_le_mul_of_nonneg_left (Finset.sum_le_sum (s := Finset.range J) (fun j _ => hblock j))
      (Nat.cast_nonneg J : (0 : ℝ) ≤ J)
    simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, pow_two, mul_assoc] using h
  have hlog : Real.log Y ≤ L := by
    have h := Real.log_le_log (by linarith : 0 < Y) (by linarith : Y ≤ 2 * Y + 1)
    dsimp [L]
    linarith
  have hJ : (J : ℝ) ≤ A * L := hJbound.trans (mul_le_mul_of_nonneg_left hlog hA.le)
  have hJ2 := pow_le_pow_left₀ (Nat.cast_nonneg J : (0 : ℝ) ≤ J) hJ 2
  have hfinal := hlower.trans (hupper.trans (mul_le_mul_of_nonneg_right hJ2 (by positivity)))
  have hh := mul_le_mul_of_nonneg_left hfinal (by norm_num : (0 : ℝ) ≤ 64)
  refine (le_of_eq ?_).trans (hh.trans (le_of_eq ?_))
  · ring
  · dsimp [L, G]
    ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityPolynomialBalance
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The balanced exponent and logarithms in the polynomial alternative -/

namespace Ostmann

 theorem density_balance_at_most (σ : ℝ) (hσ : σ ≤ 1) :
    densityBalanceExponent σ ≤ 3 / 2 := by
  unfold densityBalanceExponent
  apply (div_le_iff₀ (by linarith : 0 < 2 * (2 - σ))).mpr
  linarith

 theorem density_target_at_least (σ : ℝ) (hσ : 1 / 2 ≤ σ) (hσ1 : σ ≤ 1) :
    2 - 2 * σ ≤ densityTargetExponent σ := by
  unfold densityTargetExponent
  apply (le_div_iff₀ (by linarith : 0 < 2 - σ)).mpr
  nlinarith [mul_nonneg (show 0 ≤ σ - 1 / 2 by linarith) (show 0 ≤ 1 - σ by linarith)]

 theorem density_polynomial_balanced_powers (B X σ : ℝ) (hB : 1 ≤ B) (hBX : B ≤ X)
    (hσ : 1 / 2 ≤ σ) (hσ1 : σ ≤ 1) :
    (B ^ densityBalanceExponent σ) ^ (2 - 2 * σ) + B * X ^ (1 - 2 * σ) ≤
      2 * B ^ densityTargetExponent σ := by
  have hBp : 0 < B := lt_of_lt_of_le zero_lt_one hB
  have he : (B ^ densityBalanceExponent σ) ^ (2 - 2 * σ) = B ^ densityTargetExponent σ := by
    rw [← Real.rpow_mul hBp.le]
    congr 1
    unfold densityBalanceExponent densityTargetExponent
    have hd : 2 - σ ≠ 0 := by linarith
    field_simp [hd]
  have hx := Real.rpow_le_rpow_of_nonpos hBp hBX (by linarith : 1 - 2 * σ ≤ 0)
  have hb : B * B ^ (1 - 2 * σ) = B ^ (2 - 2 * σ) := by
    rw [show 2 - 2 * σ = 1 + (1 - 2 * σ) by ring, Real.rpow_add hBp, Real.rpow_one]
  have ht := Real.rpow_le_rpow_of_exponent_le hB (density_target_at_least σ hσ hσ1)
  rw [he]
  have h := (mul_le_mul_of_nonneg_left hx hBp.le).trans (hb.le.trans ht)
  linarith

 theorem density_balanced_log_cost (Q : ℕ) (hQ : 1 ≤ Q) (T σ : ℝ) (hT : 2 ≤ T)
    (hσ : 1 / 2 ≤ σ) (hσ1 : σ ≤ 1) :
    1 + Real.log (2 * (((Q : ℝ) ^ 2 * T) ^ densityBalanceExponent σ) + 1) ≤
      8 * Real.log ((Q : ℝ) * T) := by
  let B := (Q : ℝ) ^ 2 * T
  let L := Real.log ((Q : ℝ) * T)
  let Y := B ^ densityBalanceExponent σ
  have hq : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hB : 2 ≤ B := by dsimp [B]; nlinarith
  have hBp : 0 < B := by linarith
  have hY : 2 ≤ Y := by
    have h := Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ B)
      (density_balance_at_least_one σ hσ hσ1)
    rw [Real.rpow_one] at h
    exact hB.trans h
  have hL : Real.log 2 ≤ L := Real.log_le_log (by norm_num) (by nlinarith)
  have hlogB := density_conductor_height_log Q hQ T hT
  have hlogY : Real.log Y ≤ 3 * L := by
    rw [show Real.log Y = densityBalanceExponent σ * Real.log B by exact Real.log_rpow hBp _]
    have ha := density_balance_at_most σ hσ1
    have hlB : 0 ≤ Real.log B := Real.log_nonneg (by linarith)
    have hm := mul_le_mul_of_nonneg_right ha hlB
    dsimp [B, L] at *
    linarith
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    have h := Real.log_pow (2 : ℝ) 2
    norm_num at h
    exact h
  have hlog : Real.log (2 * Y + 1) ≤ Real.log 4 + Real.log Y := by
    rw [← Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) (by linarith : Y ≠ 0)]
    exact Real.log_le_log (by linarith) (by linarith)
  rw [hlog4] at hlog
  change 1 + Real.log (2 * Y + 1) ≤ 8 * L
  nlinarith [Real.log_two_gt_d9]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityPolynomialBalanced
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The balanced density exponent for the actual polynomial alternative -/

namespace Ostmann

open scoped BigOperators Classical

 theorem density_polynomial_alternative_balanced_oai :
    ∃ C : ℝ, 0 < C ∧ ∀ Q : ℕ, 1 ≤ Q → ∀ T σ : ℝ,
      2 ≤ T → 1 / 2 ≤ σ → σ ≤ 1 → ∀ X : ℕ, 1 ≤ X → (Q : ℝ) ^ 2 * T ≤ X →
      ∀ {ι : Type} (R : Finset ι) (c : ι → PrimitiveComplexCharacter) (t β : ι → ℝ),
      (∀ i ∈ R, (c i).modulus ≤ Q) → (∀ i ∈ R, |t i| ≤ T) →
      (∀ i ∈ R, ∀ j ∈ R, c i = c j → i ≠ j → 1 ≤ |t i - t j|) →
      (∀ i ∈ R, σ ≤ β i ∧ β i ≤ 1) →
      (∀ i ∈ R, (1 / 8 : ℝ) ≤ ‖∑ n ∈
        (Finset.Icc 1 ⌊((Q : ℝ) ^ 2 * T) ^ densityBalanceExponent σ⌋₊).filter (fun n => X < n),
        LSeries.term (densityDetectorCharacterCoefficient (c i) X) (densityVerticalPoint (β i) (t i)) n *
          densityDetectorWeight (n / (((Q : ℝ) ^ 2 * T) ^ densityBalanceExponent σ))‖) →
      (R.card : ℝ) ≤ C * ((Q : ℝ) ^ 2 * T) ^ densityTargetExponent σ *
        (Real.log ((Q : ℝ) * T)) ^ 9 := by
  obtain ⟨C, hC, hb⟩ := density_polynomial_alternative_count
  refine ⟨2 * C * 8 ^ 9, by positivity, ?_⟩
  intro Q hQ T σ hT hσ hσ1 X hX hBX ι R c t β hc ht hs hβ hlarge
  let B := (Q : ℝ) ^ 2 * T
  let Y := B ^ densityBalanceExponent σ
  let L := Real.log ((Q : ℝ) * T)
  have hq : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hB : 2 ≤ B := by dsimp [B]; nlinarith
  have hY : 2 ≤ Y := by
    have h := Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ B)
      (density_balance_at_least_one σ hσ hσ1)
    rw [Real.rpow_one] at h
    exact hB.trans h
  have hL : 0 ≤ L := Real.log_nonneg (by nlinarith)
  have hlog := density_balanced_log_cost Q hQ T σ hT hσ hσ1
  have hpow := density_polynomial_balanced_powers B X σ (by linarith) hBX hσ hσ1
  have h := hb X Q hX hQ Y T σ hY (by linarith) hσ hσ1 R c t β hc ht hs hβ hlarge
  apply h.trans
  calc
    _ ≤ C * (8 * L) ^ 9 * (2 * B ^ densityTargetExponent σ) := by
      apply mul_le_mul _ hpow (by positivity) (by positivity)
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by
        have := Real.log_nonneg (by linarith : 1 ≤ 2 * Y + 1)
        linarith) hlog 9) hC.le
    _ = _ := by ring

end Ostmann

end OAI
end

theorem solution : type_of% @OAI.Ostmann.density_polynomial_alternative_balanced_oai := @OAI.Ostmann.density_polynomial_alternative_balanced_oai
