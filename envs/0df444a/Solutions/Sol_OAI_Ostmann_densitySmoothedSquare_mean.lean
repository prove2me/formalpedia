-- Prove2me | solution 1 for OAI.Ostmann.densitySmoothedSquare_mean
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T06:33:26.581661+00:00
-- url     : https://prove2.me/submissions/f140854b-9bf8-4f15-89c1-69b0e84eff2c

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
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_LogNormDerivative
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Real derivatives of logarithmic complex norms -/

namespace Ostmann

open Complex

 theorem hasDerivAt_log_norm {f : ℝ → ℂ} {f' : ℂ} {x : ℝ}
    (hf : HasDerivAt f f' x) (hne : f x ≠ 0) :
    HasDerivAt (fun t => Real.log ‖f t‖) (f' / f x).re x := by
  have hn : ‖f x‖ ≠ 0 := norm_ne_zero_iff.mpr hne
  have hd := (hf.norm_sq.log (pow_ne_zero 2 hn)).div_const 2
  have he : (2 * inner ℝ (f x) f' / ‖f x‖ ^ 2) / 2 = (f' / f x).re := by
    rw [real_inner_eq_re_inner ℂ, RCLike.inner_apply, Complex.div_re,
      ← Complex.normSq_eq_norm_sq]
    change 2 * (f' * (starRingEnd ℂ) (f x)).re / Complex.normSq (f x) / 2 = _
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  rw [he] at hd
  convert hd using 1
  all_goals try with_reducible_and_instances rfl
  ext t
  rw [Real.log_pow]
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DigammaTailEstimate
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A bounded tail in the sharp positive-strip digamma comparison -/

namespace Ostmann

open Complex
open scoped BigOperators

 theorem density_digamma_hasSum (z : ℂ) (hz : 0 < z.re) :
    HasSum (densityDigammaTerm z) (Complex.digamma z + Real.eulerMascheroniConstant) := by
  have h := Complex.hasSum_digamma_of_re_pos hz
  apply h.congr
  intro n
  simp only [densityDigammaTerm]

 theorem density_digamma_tail_bound (z : ℂ) (hz : 1 / 8 ≤ z.re) (N : ℕ) (hN : 1 ≤ N) :
    ‖∑' i : ℕ, densityDigammaTerm z (i + N)‖ ≤
      8 * (‖z‖ + 1) / N := by
  have hpos : 0 < z.re := by linarith
  have hsum := (density_digamma_hasSum z hpos).summable
  have hnorm := (summable_nat_add_iff N).mpr hsum.norm
  have hmajor := (summable_nat_add_iff N).mpr Complex.summable_one_div_natCast_add_one_sq
  have hp (i : ℕ) : ‖densityDigammaTerm z (i + N)‖ ≤
      8 * (‖z‖ + 1) * (1 / (((i + N : ℕ) : ℝ) + 1) ^ 2) := by
    have h := Complex.norm_inv_add_one_sub_inv_le (a := 1 / 8) (R := ‖z‖)
      (by norm_num) (by norm_num) hz le_rfl (i + N)
    change ‖densityDigammaTerm z (i + N)‖ ≤ _ at h
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    field_simp
  calc
    _ ≤ ∑' i : ℕ, ‖densityDigammaTerm z (i + N)‖ := norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' i : ℕ, 8 * (‖z‖ + 1) * (1 / (((i + N : ℕ) : ℝ) + 1) ^ 2) :=
      hnorm.tsum_le_tsum hp (hmajor.mul_left _)
    _ = 8 * (‖z‖ + 1) * ∑' i : ℕ, 1 / (((i + N : ℕ) : ℝ) + 1) ^ 2 := tsum_mul_left
    _ ≤ 8 * (‖z‖ + 1) * (N : ℝ)⁻¹ :=
      mul_le_mul_of_nonneg_left (Complex.tsum_one_div_natCast_add_add_one_sq_le hN) (by positivity)
    _ = _ := by ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_SharpDigammaStrip
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The leading logarithm of digamma on the required positive strip

The bounded remainder, rather than a multiple of the logarithm, preserves the
correct length in the approximate functional equation for the fourth moment.
-/

namespace Ostmann

open Complex
open scoped BigOperators

 theorem sharp_digamma_strip (z : ℂ) (hz : 1 / 8 ≤ z.re) (hz3 : z.re ≤ 3) :
    ‖Complex.digamma z - (Real.log (|z.im| + 2) : ℂ)‖ ≤
      59 + |Real.eulerMascheroniConstant| := by
  let Y := |z.im|
  let N : ℕ := ⌈Y⌉₊ + 1
  let H : ℝ := harmonic N
  have hY : 0 ≤ Y := abs_nonneg _
  have hN : 1 ≤ N := by dsimp [N]; omega
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hNlo : Y + 1 ≤ (N : ℝ) := by
    have h := Nat.le_ceil Y
    dsimp [N]
    push_cast
    linarith
  have hNhi : (N : ℝ) ≤ Y + 2 := by
    have h := Nat.ceil_lt_add_one hY
    dsimp [N]
    push_cast
    linarith
  have hpos : 0 < z.re := by linarith
  have hnorm (m : ℕ) : (Y + 1) / 9 ≤ ‖z + m‖ := by
    have hr := Complex.re_le_norm (z + m)
    have hi := Complex.abs_im_le_norm (z + m)
    simp only [Complex.add_re, Complex.natCast_re, Complex.add_im, Complex.natCast_im, add_zero] at hr hi
    dsimp [Y]
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have hhead : ‖∑ m ∈ Finset.range N, (z + m)⁻¹‖ ≤ 18 := by
    have hp (m : ℕ) : ‖(z + m)⁻¹‖ ≤ 9 / (Y + 1) := by
      rw [norm_inv]
      have hh := one_div_le_one_div_of_le (by positivity : 0 < (Y + 1) / 9) (hnorm m)
      rw [← one_div (‖z + m‖)]
      simpa only [one_div_div] using hh
    apply (norm_sum_le _ _).trans
    have hs := Finset.sum_le_sum (s := Finset.range N) (fun m _ => hp m)
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hs
    apply hs.trans
    have hn : (N : ℝ) * 9 ≤ 18 * (Y + 1) := by nlinarith
    have hdiv := (div_le_iff₀ (by positivity : 0 < Y + 1)).mpr hn
    convert hdiv using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have htail : ‖∑' i : ℕ, densityDigammaTerm z (i + N)‖ ≤ 40 := by
    apply (density_digamma_tail_bound z hz N hN).trans
    apply (div_le_iff₀ hNpos).mpr
    have hzn := Complex.norm_le_abs_re_add_abs_im z
    rw [abs_of_pos hpos] at hzn
    dsimp [Y] at hNlo hY ⊢
    nlinarith
  have hHlo : Real.log (Y + 2) ≤ H := by
    have h := log_add_one_le_harmonic N
    have hle : Real.log (Y + 2) ≤ Real.log (N + 1 : ℕ) := by
      apply Real.log_le_log (by positivity)
      push_cast
      linarith
    exact hle.trans h
  have hHhi : H ≤ 1 + Real.log (Y + 2) := by
    exact (harmonic_le_one_add_log N).trans
      (add_le_add_right (Real.log_le_log hNpos hNhi) 1)
  have hHnorm : ‖((H : ℂ) - (Real.log (Y + 2) : ℂ))‖ ≤ 1 := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by linarith)]
    linarith
  have hsum := density_digamma_hasSum z hpos
  have hsplit := hsum.summable.sum_add_tsum_nat_add N
  have hfirst : (∑ m ∈ Finset.range N, densityDigammaTerm z m) =
      (H : ℂ) - ∑ m ∈ Finset.range N, (z + m)⁻¹ := by
    simp only [densityDigammaTerm, Finset.sum_sub_distrib]
    rw [Complex.sum_inv_natCast_add_one]
    norm_cast
  rw [hfirst, hsum.tsum_eq] at hsplit
  have hid : Complex.digamma z - (Real.log (Y + 2) : ℂ) =
      (((H : ℂ) - (Real.log (Y + 2) : ℂ)) -
        ∑ m ∈ Finset.range N, (z + m)⁻¹) +
          (∑' i : ℕ, densityDigammaTerm z (i + N)) - (Real.eulerMascheroniConstant : ℂ) := by
    linear_combination -hsplit
  change ‖Complex.digamma z - (Real.log (Y + 2) : ℂ)‖ ≤ _
  rw [hid]
  calc
    _ ≤ (‖(H : ℂ) - (Real.log (Y + 2) : ℂ)‖ +
      ‖∑ m ∈ Finset.range N, (z + m)⁻¹‖) +
      ‖∑' i : ℕ, densityDigammaTerm z (i + N)‖ + ‖(Real.eulerMascheroniConstant : ℂ)‖ := by
      calc
        _ ≤ (‖((H : ℂ) - (Real.log (Y + 2) : ℂ)) -
            ∑ m ∈ Finset.range N, (z + m)⁻¹‖ +
            ‖∑' i : ℕ, densityDigammaTerm z (i + N)‖) +
            ‖(Real.eulerMascheroniConstant : ℂ)‖ :=
          (norm_sub_le _ _).trans (add_le_add_left (norm_add_le _ _) _)
        _ ≤ _ := add_le_add_left (add_le_add_left (norm_sub_le _ _) _) _
    _ ≤ _ := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      linarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_GammaNormDerivative
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Horizontal and vertical logarithmic derivatives of Gamma -/

namespace Ostmann

open Complex

 theorem gamma_differentiableAt_pos {z : ℂ} (hz : 0 < z.re) :
    DifferentiableAt ℂ Complex.Gamma z := by
  apply Complex.differentiableAt_Gamma
  intro n he
  have hr := congrArg Complex.re he
  simp only [neg_re, natCast_re] at hr
  have hn := Nat.cast_nonneg (α := ℝ) n
  linarith

 theorem gamma_log_norm_horizontal (a t : ℝ) (ha : 0 < a) :
    HasDerivAt (fun x : ℝ => Real.log ‖Complex.Gamma ((x : ℂ) + t * I)‖)
      (Complex.digamma ((a : ℂ) + t * I)).re a := by
  have hz : 0 < ((a : ℂ) + t * I).re := by simpa
  have hp : HasDerivAt (fun x : ℝ => (x : ℂ) + t * I) 1 a := by
    simpa using Complex.ofRealCLM.hasDerivAt.add_const ((t : ℂ) * I)
  have hg := (gamma_differentiableAt_pos hz).hasDerivAt.scomp a hp
  have hd := hasDerivAt_log_norm hg (Complex.Gamma_ne_zero_of_re_pos hz)
  simpa only [Function.comp_apply, one_smul, digamma_def, logDeriv_apply] using hd

 theorem gamma_log_norm_vertical (a t : ℝ) (ha : 0 < a) :
    HasDerivAt (fun y : ℝ => Real.log ‖Complex.Gamma ((a : ℂ) + y * I)‖)
      (-(Complex.digamma ((a : ℂ) + t * I)).im) t := by
  have hz : 0 < ((a : ℂ) + t * I).re := by simpa
  have hp : HasDerivAt (fun y : ℝ => (a : ℂ) + y * I) I t := by
    simpa using (Complex.ofRealCLM.hasDerivAt.mul_const I).const_add (a : ℂ)
  have hg := (gamma_differentiableAt_pos hz).hasDerivAt.scomp t hp
  have hd := hasDerivAt_log_norm hg (Complex.Gamma_ne_zero_of_re_pos hz)
  simpa only [Function.comp_apply, digamma_def, logDeriv_apply, smul_eq_mul,
    mul_div_assoc, I_mul_re] using hd

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_SharpGammaHorizontal
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Gamma quotients with the exact horizontal power -/

namespace Ostmann

open Complex Set

 theorem sharp_gamma_log_horizontal_ordered (a b t : ℝ)
    (ha : 1 / 8 ≤ a) (hab : a ≤ b) (hb : b ≤ 3) :
    |Real.log ‖Complex.Gamma ((b : ℂ) + t * I)‖ -
        Real.log ‖Complex.Gamma ((a : ℂ) + t * I)‖ -
        (b - a) * Real.log (|t| + 2)| ≤
      (59 + |Real.eulerMascheroniConstant|) * (b - a) := by
  let F : ℝ → ℝ := fun x => Real.log ‖Complex.Gamma ((x : ℂ) + t * I)‖ -
    x * Real.log (|t| + 2)
  let F' : ℝ → ℝ := fun x => (Complex.digamma ((x : ℂ) + t * I)).re -
    Real.log (|t| + 2)
  have hd (x : ℝ) (hx : x ∈ Icc a b) : HasDerivAt F (F' x) x := by
    convert! (gamma_log_norm_horizontal x t (by linarith [hx.1])).sub
      ((hasDerivAt_id x).mul_const (Real.log (|t| + 2))) using 1
    all_goals try with_reducible_and_instances rfl
    simp only [F', one_mul]
  have hbound (x : ℝ) (hx : x ∈ Ico a b) : ‖F' x‖ ≤
      59 + |Real.eulerMascheroniConstant| := by
    have he := sharp_digamma_strip ((x : ℂ) + t * I)
      (by simp; linarith [hx.1]) (by simp; linarith [hx.2])
    have hr := (Complex.abs_re_le_norm
      (Complex.digamma ((x : ℂ) + t * I) - (Real.log (|t| + 2) : ℂ))).trans
      (by simpa using he)
    simpa [F', Real.norm_eq_abs] using hr
  have hm := norm_image_sub_le_of_norm_deriv_le_segment'
    (fun x hx => (hd x hx).hasDerivWithinAt) hbound b (right_mem_Icc.mpr hab)
  change ‖F b - F a‖ ≤ _ at hm
  have he : F b - F a = Real.log ‖Complex.Gamma ((b : ℂ) + t * I)‖ -
      Real.log ‖Complex.Gamma ((a : ℂ) + t * I)‖ -
      (b - a) * Real.log (|t| + 2) := by dsimp [F]; ring
  simpa only [he, Real.norm_eq_abs] using hm

 theorem sharp_gamma_horizontal_ordered (a b t : ℝ)
    (ha : 1 / 8 ≤ a) (hab : a ≤ b) (hb : b ≤ 3) :
    ‖Complex.Gamma ((b : ℂ) + t * I)‖ / ‖Complex.Gamma ((a : ℂ) + t * I)‖ ≤
      Real.exp ((59 + |Real.eulerMascheroniConstant|) * (b - a)) *
        (|t| + 2) ^ (b - a) := by
  have hGa : 0 < ‖Complex.Gamma ((a : ℂ) + t * I)‖ :=
    norm_pos_iff.mpr (Complex.Gamma_ne_zero_of_re_pos (by simp; linarith))
  have hGb : 0 < ‖Complex.Gamma ((b : ℂ) + t * I)‖ :=
    norm_pos_iff.mpr (Complex.Gamma_ne_zero_of_re_pos (by simp; linarith))
  have hh := le_abs_self (Real.log ‖Complex.Gamma ((b : ℂ) + t * I)‖ -
    Real.log ‖Complex.Gamma ((a : ℂ) + t * I)‖ - (b - a) * Real.log (|t| + 2))
  have h := sharp_gamma_log_horizontal_ordered a b t ha hab hb
  have hlog : Real.log (‖Complex.Gamma ((b : ℂ) + t * I)‖ /
      ‖Complex.Gamma ((a : ℂ) + t * I)‖) ≤
      (59 + |Real.eulerMascheroniConstant|) * (b - a) +
        Real.log (|t| + 2) * (b - a) := by
    rw [Real.log_div hGb.ne' hGa.ne']
    nlinarith
  have hexp := Real.exp_le_exp.mpr hlog
  rw [Real.exp_log (div_pos hGb hGa), Real.exp_add,
    ← Real.rpow_def_of_pos (by positivity : 0 < |t| + 2)] at hexp
  exact hexp

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_SharpGammaVertical
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bounded vertical logarithmic variation of Gamma -/

namespace Ostmann

open Complex Set

 theorem sharp_gamma_log_vertical_ordered (a u v : ℝ)
    (ha : 1 / 8 ≤ a) (ha3 : a ≤ 3) (huv : u ≤ v) :
    |Real.log ‖Complex.Gamma ((a : ℂ) + v * I)‖ -
        Real.log ‖Complex.Gamma ((a : ℂ) + u * I)‖| ≤
      (59 + |Real.eulerMascheroniConstant|) * (v - u) := by
  let F : ℝ → ℝ := fun y => Real.log ‖Complex.Gamma ((a : ℂ) + y * I)‖
  let F' : ℝ → ℝ := fun y => -(Complex.digamma ((a : ℂ) + y * I)).im
  have hd (y : ℝ) : HasDerivAt F (F' y) y :=
    gamma_log_norm_vertical a y (by linarith)
  have hb (y : ℝ) : ‖F' y‖ ≤ 59 + |Real.eulerMascheroniConstant| := by
    have h := sharp_digamma_strip ((a : ℂ) + y * I) (by simpa using ha) (by simpa using ha3)
    have hi := (Complex.abs_im_le_norm
      (Complex.digamma ((a : ℂ) + y * I) - (Real.log (|y| + 2) : ℂ))).trans
      (by simpa using h)
    simpa [F', Real.norm_eq_abs] using hi
  exact norm_image_sub_le_of_norm_deriv_le_segment'
    (fun y _ => (hd y).hasDerivWithinAt) (fun y _ => hb y) v
      (right_mem_Icc.mpr huv)

 theorem sharp_gamma_log_vertical (a u v : ℝ)
    (ha : 1 / 8 ≤ a) (ha3 : a ≤ 3) :
    |Real.log ‖Complex.Gamma ((a : ℂ) + v * I)‖ -
        Real.log ‖Complex.Gamma ((a : ℂ) + u * I)‖| ≤
      (59 + |Real.eulerMascheroniConstant|) * |v - u| := by
  rcases le_total u v with huv | hvu
  · simpa only [abs_of_nonneg (sub_nonneg.mpr huv)] using
      sharp_gamma_log_vertical_ordered a u v ha ha3 huv
  · have h := sharp_gamma_log_vertical_ordered a v u ha ha3 hvu
    calc
      _ = |Real.log ‖Complex.Gamma ((a : ℂ) + u * I)‖ -
          Real.log ‖Complex.Gamma ((a : ℂ) + v * I)‖| := abs_sub_comm _ _
      _ ≤ _ := h
      _ = _ := by rw [abs_of_nonpos (sub_nonpos.mpr hvu)]; ring

 theorem sharp_gamma_vertical (a u v : ℝ) (ha : 1 / 8 ≤ a) (ha3 : a ≤ 3) :
    ‖Complex.Gamma ((a : ℂ) + v * I)‖ / ‖Complex.Gamma ((a : ℂ) + u * I)‖ ≤
      Real.exp ((59 + |Real.eulerMascheroniConstant|) * |v - u|) := by
  have hGu : 0 < ‖Complex.Gamma ((a : ℂ) + u * I)‖ :=
    norm_pos_iff.mpr (Complex.Gamma_ne_zero_of_re_pos (by simp; linarith))
  have hGv : 0 < ‖Complex.Gamma ((a : ℂ) + v * I)‖ :=
    norm_pos_iff.mpr (Complex.Gamma_ne_zero_of_re_pos (by simp; linarith))
  have h := (le_abs_self _).trans (sharp_gamma_log_vertical a u v ha ha3)
  rw [← Real.log_div hGv.ne' hGu.ne'] at h
  have he := Real.exp_le_exp.mpr h
  rwa [Real.exp_log (div_pos hGv hGu)] at he

 theorem sharp_gamma_quotient (a b t u : ℝ)
    (ha : 1 / 8 ≤ a) (hab : a ≤ b) (hb : b ≤ 3) :
    ‖Complex.Gamma ((b : ℂ) + (t + u) * I)‖ / ‖Complex.Gamma ((a : ℂ) + t * I)‖ ≤
      Real.exp ((59 + |Real.eulerMascheroniConstant|) * (b - a + |u|)) *
        (|t| + 2) ^ (b - a) := by
  have hn : ‖Complex.Gamma ((b : ℂ) + t * I)‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (Complex.Gamma_ne_zero_of_re_pos (by simp; linarith))
  have hv := sharp_gamma_vertical b t (t + u) (ha.trans hab) hb
  simp only [add_sub_cancel_left] at hv
  calc
    _ = (‖Complex.Gamma ((b : ℂ) + (t + u) * I)‖ / ‖Complex.Gamma ((b : ℂ) + t * I)‖) *
        (‖Complex.Gamma ((b : ℂ) + t * I)‖ / ‖Complex.Gamma ((a : ℂ) + t * I)‖) := by
      field_simp
    _ ≤ Real.exp ((59 + |Real.eulerMascheroniConstant|) * |u|) *
        (Real.exp ((59 + |Real.eulerMascheroniConstant|) * (b - a)) *
        (|t| + 2) ^ (b - a)) :=
      by simpa only [Complex.ofReal_add] using
        mul_le_mul hv (sharp_gamma_horizontal_ordered a b t ha hab hb)
          (by positivity) (by positivity)
    _ = _ := by rw [← mul_assoc, ← Real.exp_add]; congr 2; ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_SharpGammaRealShift
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The Gamma factor along the smoothed functional-equation contour -/

namespace Ostmann

open Complex

 theorem gammaReal_shift_quotient (z w : ℂ) :
    Complex.Gammaℝ (z + w) / Complex.Gammaℝ z =
      (Real.pi : ℂ) ^ (-w / 2) * (Complex.Gamma ((z + w) / 2) / Complex.Gamma (z / 2)) := by
  have hp : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [Complex.Gammaℝ_def, Complex.Gammaℝ_def,
    show -(z + w) / 2 = -z / 2 + -w / 2 by ring, Complex.cpow_add _ _ hp,
    mul_assoc, mul_div_mul_left _ _ (Complex.cpow_ne_zero_iff.mpr (Or.inl hp)), mul_div_assoc]

 theorem sharp_gammaReal_shift (z w : ℂ)
    (hz : 1 / 4 ≤ z.re) (hz3 : z.re ≤ 3 / 2)
    (hw : 0 ≤ w.re) (hw2 : w.re ≤ 2) :
    ‖Complex.Gammaℝ (z + w) / Complex.Gammaℝ z‖ ≤
      Real.exp ((59 + |Real.eulerMascheroniConstant|) * (1 + |w.im|)) *
        (|z.im| + 2) ^ (w.re / 2) := by
  have he (s : ℂ) : ((s.re / 2 : ℝ) : ℂ) + (s.im / 2 : ℝ) * I = s / 2 := by
    apply Complex.ext <;> simp
  have he' : (((z.re / 2 + w.re / 2 : ℝ)) : ℂ) +
      ((z.im / 2 : ℝ) + (w.im / 2 : ℝ)) * I = (z + w) / 2 := by
    apply Complex.ext <;> simp <;> ring
  have hg := sharp_gamma_quotient (z.re / 2) (z.re / 2 + w.re / 2)
    (z.im / 2) (w.im / 2) (by linarith) (by linarith) (by linarith)
  rw [he', he, show z.re / 2 + w.re / 2 - z.re / 2 = w.re / 2 by ring] at hg
  have hp : ‖(Real.pi : ℂ) ^ (-w / 2)‖ ≤ 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    apply Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.pi_gt_three])
    simp only [div_ofNat_re, neg_re]
    linarith
  rw [gammaReal_shift_quotient, norm_mul, norm_div]
  calc
    _ ≤ 1 * (Real.exp ((59 + |Real.eulerMascheroniConstant|) * (w.re / 2 + |w.im / 2|)) *
        (|z.im / 2| + 2) ^ (w.re / 2)) := mul_le_mul hp hg (by positivity) (by norm_num)
    _ ≤ _ := by
      rw [one_mul]
      apply mul_le_mul
      · apply Real.exp_le_exp.mpr
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        linarith [abs_nonneg w.im]
      · apply Real.rpow_le_rpow (by positivity)
        · rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
          linarith [abs_nonneg z.im]
        · positivity
      · positivity
      · positivity

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_CharacterGammaShift
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform shifted Gamma factors for actual primitive characters -/

namespace Ostmann

open Complex
open scoped Classical

 theorem character_gamma_shift (χ : PrimitiveComplexCharacter) (s w : ℂ)
    (hs : s.re = 1 / 2) (hw : 0 ≤ w.re) (hw2 : w.re ≤ 2) :
    ‖DirichletCharacter.gammaFactor χ.character (s + w) /
        DirichletCharacter.gammaFactor χ.character s‖ ≤
      Real.exp ((59 + |Real.eulerMascheroniConstant|) * (1 + |w.im|)) *
        (|s.im| + 2) ^ (w.re / 2) := by
  by_cases he : χ.character.Even
  · simpa only [DirichletCharacter.gammaFactor, he, ↓reduceIte] using
      sharp_gammaReal_shift s w (by linarith) (by linarith) hw hw2
  · have h := sharp_gammaReal_shift (s + 1) w
      (by simp; linarith) (by simp; linarith) hw hw2
    simpa only [DirichletCharacter.gammaFactor, he, ↓reduceIte, add_im, one_im,
      add_zero, add_right_comm s w 1] using h

 theorem gaussian_linear_abs_bound (C σ u : ℝ) (hσ : 0 ≤ σ) (hσ2 : σ ≤ 2) :
    Real.exp (2 * C * (1 + |u|) + σ ^ 2 - u ^ 2) ≤
      Real.exp (2 * C + 4 + 2 * C ^ 2) * Real.exp (-(u ^ 2) / 2) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith [sq_nonneg (|u| - 2 * C), sq_abs u]

 theorem densityCompletedSquareWeight_bound (χ : PrimitiveComplexCharacter) (s w : ℂ)
    (hs : s.re = 1 / 2) (hw : 0 ≤ w.re) (hw2 : w.re ≤ 2) :
    ‖densityCompletedSquareWeight χ s w‖ ≤
      Real.exp (2 * (59 + |Real.eulerMascheroniConstant|) + 4 +
        2 * (59 + |Real.eulerMascheroniConstant|) ^ 2) *
      ((χ.modulus : ℝ) * (|s.im| + 2)) ^ w.re * Real.exp (-(w.im ^ 2) / 2) := by
  let C : ℝ := 59 + |Real.eulerMascheroniConstant|
  have hq : (0 : ℝ) < χ.modulus := by exact_mod_cast χ.positive
  have hG := character_gamma_shift χ s w hs hw hw2
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hG 2
  have hp : ‖(χ.modulus : ℂ) ^ w‖ = (χ.modulus : ℝ) ^ w.re := by
    rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hq]
  have he : ‖Complex.exp (w ^ 2)‖ = Real.exp (w.re ^ 2 - w.im ^ 2) := by
    rw [Complex.norm_exp]
    congr 1
    simp [pow_two, Complex.mul_re]
  have hsquare : (Real.exp (C * (1 + |w.im|)) * (|s.im| + 2) ^ (w.re / 2)) ^ 2 =
      Real.exp (2 * C * (1 + |w.im|)) * (|s.im| + 2) ^ w.re := by
    rw [mul_pow, ← Real.exp_nat_mul, ← Real.rpow_natCast,
      ← Real.rpow_mul (by positivity : 0 ≤ |s.im| + 2)]
    congr 1
    · congr 1
      norm_num
      ring
    · congr 1
      norm_num
  have hpow : (χ.modulus : ℝ) ^ w.re * (|s.im| + 2) ^ w.re =
      ((χ.modulus : ℝ) * (|s.im| + 2)) ^ w.re :=
    (Real.mul_rpow hq.le (by positivity)).symm
  calc
    _ ≤ (χ.modulus : ℝ) ^ w.re *
        (Real.exp (C * (1 + |w.im|)) * (|s.im| + 2) ^ (w.re / 2)) ^ 2 *
        Real.exp (w.re ^ 2 - w.im ^ 2) := by
      simpa only [densityCompletedSquareWeight, norm_mul, norm_pow, hp, he] using
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsq (by positivity))
          (Real.exp_nonneg (w.re ^ 2 - w.im ^ 2))
    _ = ((χ.modulus : ℝ) * (|s.im| + 2)) ^ w.re *
        Real.exp (2 * C * (1 + |w.im|) + w.re ^ 2 - w.im ^ 2) := by
      rw [hsquare, show 2 * C * (1 + |w.im|) + w.re ^ 2 - w.im ^ 2 =
        2 * C * (1 + |w.im|) + (w.re ^ 2 - w.im ^ 2) by ring, Real.exp_add, ← hpow]
      ring
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left (gaussian_linear_abs_bound C w.re w.im hw hw2)
        (Real.rpow_nonneg (mul_nonneg hq.le (by positivity : 0 ≤ |s.im| + 2)) w.re)
      simpa only [C, mul_assoc, mul_left_comm] using h

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

 theorem densityCompletedSquare_eq (χ : PrimitiveComplexCharacter) (s : ℂ) (hs : 0 < s.re) :
    densityCompletedSquare χ s = (χ.modulus : ℂ) ^ s *
      (DirichletCharacter.gammaFactor χ.character s) ^ 2 * χ.L s ^ 2 := by
  rw [densityCompletedSquare, χ.completed_eq_L_mul_gamma s hs, mul_pow]
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

 theorem densitySquareGaussian_normalized (χ : PrimitiveComplexCharacter) (s w : ℂ)
    (hs : 0 < s.re) (hsw : 0 < (s + w).re) :
    densitySquareGaussian χ s w / densitySquareNormalizer χ s =
      densityCompletedSquareWeight χ s w * χ.L (s + w) ^ 2 := by
  have hq : (χ.modulus : ℂ) ≠ 0 := by exact_mod_cast χ.positive.ne'
  have hp : (χ.modulus : ℂ) ^ s ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hq)
  have hg : DirichletCharacter.gammaFactor χ.character s ≠ 0 := by
    intro he
    exact χ.gammaInverse_ne_zero s hs
      (by simp only [PrimitiveComplexCharacter.gammaInverse, he, inv_zero])
  rw [densitySquareGaussian, densityCompletedSquare_eq χ (s + w) hsw,
    Complex.cpow_add _ _ hq]
  unfold densitySquareNormalizer densityCompletedSquareWeight
  field_simp

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensitySmoothedKernel
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The normalized right-hand kernel in the square functional equation -/

namespace Ostmann

open Complex MeasureTheory

 theorem densitySmoothedSquare_integral (χ : PrimitiveComplexCharacter) (s : ℂ)
    (hs : s.re = 1 / 2) :
    densitySmoothedSquare χ s = (2 * (Real.pi : ℂ))⁻¹ *
      ∫ u : ℝ, densitySquareKernel χ s (1 + u * I) * χ.L (s + (1 + u * I)) ^ 2 := by
  unfold densitySmoothedSquare densitySquareIntegral
  rw [mul_div_assoc, ← integral_div]
  congr 1
  apply integral_congr_ae
  filter_upwards with u
  have hp : 0 < s.re := by linarith
  have hu : 0 < (s + (1 + (u : ℂ) * I)).re := by norm_num [hs]
  calc
    _ = (densitySquareGaussian χ s (1 + u * I) / densitySquareNormalizer χ s) /
        (1 + u * I) := by unfold densitySquareContour; ring
    _ = _ := by rw [densitySquareGaussian_normalized χ s _ hp hu]; unfold densitySquareKernel; ring

 theorem densitySquareKernel_line_bound (χ : PrimitiveComplexCharacter) (s : ℂ)
    (hs : s.re = 1 / 2) (u : ℝ) :
    ‖densitySquareKernel χ s (1 + u * I)‖ ≤
      (Real.exp (2 * (59 + |Real.eulerMascheroniConstant|) + 4 +
        2 * (59 + |Real.eulerMascheroniConstant|) ^ 2) *
        ((χ.modulus : ℝ) * (|s.im| + 2))) * Real.exp (-(u ^ 2) / 2) := by
  have hn : 1 ≤ ‖(1 : ℂ) + u * I‖ := by
    simpa using Complex.re_le_norm ((1 : ℂ) + u * I)
  rw [densitySquareKernel, norm_div]
  apply (div_le_self (norm_nonneg _) hn).trans
  have h := densityCompletedSquareWeight_bound χ s (1 + u * I) hs
    (by norm_num) (by norm_num)
  simpa using h

 theorem densitySquareKernel_line_continuous (χ : PrimitiveComplexCharacter) (s : ℂ)
    (hs : s.re = 1 / 2) : Continuous (fun u : ℝ => densitySquareKernel χ s (1 + u * I)) := by
  have hΓ : Continuous (fun u : ℝ =>
      DirichletCharacter.gammaFactor χ.character (s + (1 + (u : ℂ) * I))) := by
    apply continuous_iff_continuousAt.mpr
    intro u
    apply (χ.gammaFactor_differentiableAt_pos _ (by norm_num [hs])).continuousAt.comp
    fun_prop
  unfold densitySquareKernel densityCompletedSquareWeight
  apply Continuous.div
  · apply Continuous.mul
    · apply Continuous.mul
      · have hq : (χ.modulus : ℂ) ≠ 0 := by exact_mod_cast χ.positive.ne'
        exact (differentiable_id.const_cpow (Or.inl hq)).continuous.comp (by fun_prop)
      · exact (hΓ.div_const _).pow 2
    · fun_prop
  · fun_prop
  · intro u h
    have hr := congrArg Complex.re h
    norm_num at hr

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityKernelStrip
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform control of the square kernel between two positive vertical lines -/

namespace Ostmann

open Complex

 theorem densitySquareKernel_analytic (χ : PrimitiveComplexCharacter) (s w : ℂ)
    (hs : s.re = 1 / 2) (hw : 0 < w.re) :
    AnalyticAt ℂ (densitySquareKernel χ s) w := by
  have hq : (χ.modulus : ℂ) ≠ 0 := by exact_mod_cast χ.positive.ne'
  have hpos : 0 < (s + w).re := by simp only [add_re]; linarith
  have hΓ : AnalyticAt ℂ (DirichletCharacter.gammaFactor χ.character) (s + w) := by
    rw [analyticAt_iff_eventually_differentiableAt]
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hpos] with z hz
    exact χ.gammaFactor_differentiableAt_pos z hz
  have hd : AnalyticAt ℂ (fun z => DirichletCharacter.gammaFactor χ.character (s + z)) w :=
    hΓ.comp (analyticAt_const.add analyticAt_id)
  have hgn : DirichletCharacter.gammaFactor χ.character s ≠ 0 := by
    intro he
    exact χ.gammaInverse_ne_zero s (by linarith)
      (by simp only [PrimitiveComplexCharacter.gammaInverse, he, inv_zero])
  have hwn : w ≠ 0 := by intro h; simp [h] at hw
  exact ((((differentiable_id.const_cpow (Or.inl hq)).analyticAt w).mul
    ((hd.div analyticAt_const hgn).pow 2)).mul ((analyticAt_id.pow 2).cexp)).div analyticAt_id hwn

 theorem densitySquareKernel_strip_bound (χ : PrimitiveComplexCharacter) (s : ℂ)
    (hs : s.re = 1 / 2) (c x u : ℝ) (hc : 0 < c) (hcx : c ≤ x) (hx : x ≤ 1) :
    ‖densitySquareKernel χ s ((x : ℂ) + u * I)‖ ≤
      (Real.exp (2 * (59 + |Real.eulerMascheroniConstant|) + 4 +
        2 * (59 + |Real.eulerMascheroniConstant|) ^ 2) *
        ((χ.modulus : ℝ) * (|s.im| + 2)) / c) * Real.exp (-(u ^ 2) / 2) := by
  let B := (χ.modulus : ℝ) * (|s.im| + 2)
  have hq : (1 : ℝ) ≤ χ.modulus := by exact_mod_cast χ.positive
  have hB : 1 ≤ B := by dsimp [B]; nlinarith [abs_nonneg s.im]
  have hw0 : 0 ≤ (((x : ℂ) + u * I).re) := by simp; linarith
  have hw2 : (((x : ℂ) + u * I).re) ≤ 2 := by simp; linarith
  have hb := densityCompletedSquareWeight_bound χ s ((x : ℂ) + u * I) hs hw0 hw2
  have he : ((x : ℂ) + u * I).re = x := by simp
  have hi : ((x : ℂ) + u * I).im = u := by simp
  rw [he, hi] at hb
  have hp : B ^ x ≤ B :=
    (Real.rpow_le_rpow_of_exponent_le hB hx).trans_eq (Real.rpow_one B)
  have hcn : c ≤ ‖(x : ℂ) + u * I‖ := by
    exact hcx.trans (by simpa only [he] using Complex.re_le_norm ((x : ℂ) + u * I))
  rw [densitySquareKernel, norm_div]
  apply (div_le_div_of_nonneg_left (norm_nonneg _) hc hcn).trans
  apply (div_le_div_of_nonneg_right hb hc.le).trans
  have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp
    (Real.exp_nonneg (2 * (59 + |Real.eulerMascheroniConstant|) + 4 +
      2 * (59 + |Real.eulerMascheroniConstant|) ^ 2))) (Real.exp_nonneg (-(u ^ 2) / 2))
  have hd := div_le_div_of_nonneg_right h hc.le
  convert hd using 1
  all_goals try with_reducible_and_instances rfl
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_GaussianContourShift
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Shifting a vertical Gaussian integral inside an analytic strip -/

namespace Ostmann

open Complex Filter MeasureTheory Set
open scoped Topology Interval

 theorem gaussian_strip_vertical_eq (f : ℂ → ℂ) (a b K : ℝ) (hab : a ≤ b)
    (hf : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → AnalyticAt ℂ f z)
    (hb : ∀ x ∈ Icc a b, ∀ u : ℝ, ‖f ((x : ℂ) + u * I)‖ ≤ K * Real.exp (-(u ^ 2) / 2)) :
    (∫ u : ℝ, f ((a : ℂ) + u * I)) = ∫ u : ℝ, f ((b : ℂ) + u * I) := by
  let g : ℝ → ℝ := fun u => Real.exp (-(u ^ 2) / 2)
  have hg : Integrable g := by
    convert integrable_exp_neg_mul_sq (b := (1 / 2 : ℝ)) (by norm_num) using 1
    all_goals try with_reducible_and_instances rfl
    funext u
    dsimp [g]
    congr 1
    ring
  have hlim : Tendsto g atTop (𝓝 0) := by
    have hp : Tendsto (fun u : ℝ => u ^ 2 / 2) atTop atTop :=
      (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).atTop_div_const (by norm_num)
    simpa only [g, Function.comp_def, neg_div] using Real.tendsto_exp_neg_atTop_nhds_zero.comp hp
  have hv (x : ℝ) (hx : x ∈ Icc a b) : Integrable (fun u : ℝ => f ((x : ℂ) + u * I)) := by
    have hc : Continuous (fun u : ℝ => f ((x : ℂ) + u * I)) := by
      apply continuous_iff_continuousAt.mpr
      intro u
      exact (hf _ (by simpa using hx.1) (by simpa using hx.2)).continuousAt.comp (by fun_prop)
    apply (hg.const_mul K).mono' hc.aestronglyMeasurable
    filter_upwards with u
    exact hb x hx u
  have hh (u : ℝ) : ‖∫ x in a..b, f ((x : ℂ) + u * I)‖ ≤
      (K * |b - a|) * g u := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (fun x (hx : x ∈ Ι a b) => hb x
        (by rw [uIoc_of_le hab] at hx; exact ⟨hx.1.le, hx.2⟩) u)
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have htop : Tendsto (fun u : ℝ => ∫ x in a..b, f ((x : ℂ) + u * I)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    exact squeeze_zero (fun _ => norm_nonneg _) hh (by simpa using hlim.const_mul (K * |b - a|))
  have hbot : Tendsto (fun u : ℝ => ∫ x in a..b, f ((x : ℂ) + (-u) * I)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero (fun _ => norm_nonneg _) _ (by simpa using hlim.const_mul (K * |b - a|))
    intro u
    simpa only [g, neg_sq, Complex.ofReal_neg] using hh (-u)
  have hr := intervalIntegral_tendsto_integral (hv b ⟨hab, le_rfl⟩)
    tendsto_neg_atTop_atBot tendsto_id
  have hl := intervalIntegral_tendsto_integral (hv a ⟨le_rfl, hab⟩)
    tendsto_neg_atTop_atBot tendsto_id
  have hbd : Tendsto (fun T : ℝ => rectangleBoundaryIntegral f a b (-T) T) atTop
      (𝓝 (I * (∫ u : ℝ, f ((b : ℂ) + u * I)) - I * ∫ u : ℝ, f ((a : ℂ) + u * I))) := by
    simpa [rectangleBoundaryIntegral] using ((hbot.sub htop).add (hr.const_mul I)).sub (hl.const_mul I)
  have hz : ∀ T : ℝ, rectangleBoundaryIntegral f a b (-T) T = 0 := by
    intro T
    apply rectangleBoundaryIntegral_eq_zero
    intro z hz
    have hre : z.re ∈ Icc a b := by simpa only [uIcc_of_le hab, mem_preimage] using hz.1
    exact hf z hre.1 hre.2
  have he : I * (∫ u : ℝ, f ((b : ℂ) + u * I)) - I * (∫ u : ℝ, f ((a : ℂ) + u * I)) = 0 :=
    tendsto_nhds_unique hbd (tendsto_const_nhds.congr (fun T => (hz T).symm))
  exact (mul_left_cancel₀ I_ne_zero (sub_eq_zero.mp he)).symm

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityFiniteContourShift
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Shifting the actual finite Dirichlet polynomial to a short positive line -/

namespace Ostmann

open Complex MeasureTheory Set
open scoped BigOperators

 theorem densityFiniteMellin_analytic (S : Finset ℕ) (a : ℕ → ℂ)
    (hS : ∀ n ∈ S, 1 ≤ n) (w : ℂ) : AnalyticAt ℂ (densityFiniteMellin S a) w := by
  apply Finset.analyticAt_fun_sum
  intro n hn
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (by have := hS n hn; omega : n ≠ 0)
  exact analyticAt_const.div ((differentiable_id.const_cpow (Or.inl hn0)).analyticAt w)
    (Complex.cpow_ne_zero_iff.mpr (Or.inl hn0))

 theorem densityFiniteMellin_norm (S : Finset ℕ) (a : ℕ → ℂ)
    (hS : ∀ n ∈ S, 1 ≤ n) (w : ℂ) (hw : 0 ≤ w.re) :
    ‖densityFiniteMellin S a w‖ ≤ ∑ n ∈ S, ‖a n‖ := by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro n hn
  rw [norm_div, norm_natCast_cpow_of_pos (lt_of_lt_of_le Nat.zero_lt_one (hS n hn))]
  apply div_le_self (norm_nonneg _)
  exact Real.one_le_rpow (by exact_mod_cast hS n hn) hw

 theorem densityFiniteKernel_shift (χ : PrimitiveComplexCharacter) (s : ℂ)
    (hs : s.re = 1 / 2) (S : Finset ℕ) (a : ℕ → ℂ) (hS : ∀ n ∈ S, 1 ≤ n)
    (c : ℝ) (hc : 0 < c) (hc1 : c ≤ 1) :
    (∫ u : ℝ, densityFiniteKernel χ s S a ((c : ℂ) + u * I)) =
      ∫ u : ℝ, densityFiniteKernel χ s S a (1 + u * I) := by
  let K := Real.exp (2 * (59 + |Real.eulerMascheroniConstant|) + 4 +
    2 * (59 + |Real.eulerMascheroniConstant|) ^ 2) *
    ((χ.modulus : ℝ) * (|s.im| + 2)) / c
  apply gaussian_strip_vertical_eq (densityFiniteKernel χ s S a) c 1
    (K * ∑ n ∈ S, ‖a n‖) hc1
  · intro w hw hw1
    exact (densitySquareKernel_analytic χ s w hs (hc.trans_le hw)).mul
      (densityFiniteMellin_analytic S a hS w)
  · intro x hx u
    have hk := densitySquareKernel_strip_bound χ s hs c x u hc hx.1 hx.2
    have hm := densityFiniteMellin_norm S a hS ((x : ℂ) + u * I) (by simp; linarith [hx.1])
    rw [densityFiniteKernel, norm_mul]
    have h := mul_le_mul hk hm (norm_nonneg _) (by positivity)
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    ring

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
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityHarmonicDivisors
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The harmonic second moment of the divisor function -/

namespace Ostmann

open scoped BigOperators Classical

 theorem density_harmonic_multiples (N d : ℕ) (hd : 0 < d) :
    (∑ n ∈ (Finset.Icc 1 N).filter (fun n => d ∣ n), (n : ℝ)⁻¹) =
      (d : ℝ)⁻¹ * ∑ k ∈ Finset.Icc 1 (N / d), (k : ℝ)⁻¹ := by
  rw [Finset.mul_sum]
  symm
  apply Finset.sum_bij (fun k _ => d * k)
  · intro k hk
    obtain ⟨hk1, hkN⟩ := Finset.mem_Icc.mp hk
    have hu := (Nat.le_div_iff_mul_le hd).mp hkN
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
      ⟨Nat.mul_pos hd hk1, by simpa only [mul_comm] using hu⟩, dvd_mul_right d k⟩
  · intro k _ l _ hkl
    exact Nat.eq_of_mul_eq_mul_left hd hkl
  · intro n hn
    obtain ⟨hnN, hdn⟩ := Finset.mem_filter.mp hn
    have hn1 := (Finset.mem_Icc.mp hnN).1
    have hdle : d ≤ n := Nat.le_of_dvd hn1 hdn
    refine ⟨n / d, Finset.mem_Icc.mpr ⟨Nat.div_pos hdle hd,
      Nat.div_le_div_right (Finset.mem_Icc.mp hnN).2⟩, ?_⟩
    exact Nat.mul_div_cancel' hdn
  · intro k _
    rw [Nat.cast_mul, mul_inv_rev, mul_comm]

 theorem density_harmonic_multiples_le (N d : ℕ) (hd : 0 < d) :
    (∑ n ∈ (Finset.Icc 1 N).filter (fun n => d ∣ n), (n : ℝ)⁻¹) ≤
      (d : ℝ)⁻¹ * ∑ k ∈ Finset.Icc 1 N, (k : ℝ)⁻¹ := by
  rw [density_harmonic_multiples N d hd]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg _))
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.Icc_subset_Icc_right (Nat.div_le_self N d)) (fun _ _ _ => by positivity)

 theorem density_divisor_square_harmonic (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, (n.divisors.card : ℝ) ^ 2 / n) ≤
      (1 + Real.log N) ^ 4 := by
  let H : ℝ := ∑ k ∈ Finset.Icc 1 N, (k : ℝ)⁻¹
  have hH : 0 ≤ H := Finset.sum_nonneg (fun _ _ => by positivity)
  have hHlog : H ≤ 1 + Real.log N := by
    simpa only [H, harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
      using harmonic_le_one_add_log N
  have hexp (n : ℕ) (hn : n ∈ Finset.Icc 1 N) :
      (n.divisors.card : ℝ) ^ 2 / n =
      ∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 N,
        if d.lcm e ∣ n then (n : ℝ)⁻¹ else 0 := by
    rw [density_divisor_square_as_sum N n hn, div_eq_mul_inv]
    simp only [Finset.sum_mul, ite_mul, one_mul, zero_mul]
  calc
    _ = ∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 N,
        ∑ n ∈ (Finset.Icc 1 N).filter (fun n => d.lcm e ∣ n), (n : ℝ)⁻¹ := by
      rw [Finset.sum_congr rfl hexp, Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro d _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro e _
      rw [Finset.sum_filter]
    _ ≤ ∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 N,
        ((d.lcm e : ℕ) : ℝ)⁻¹ * H := by
      apply Finset.sum_le_sum
      intro d hd
      apply Finset.sum_le_sum
      intro e he
      apply density_harmonic_multiples_le
      exact Nat.lcm_pos (Finset.mem_Icc.mp hd).1 (Finset.mem_Icc.mp he).1
    _ = (∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 N,
        ((d.lcm e : ℕ) : ℝ)⁻¹) * H := by simp only [Finset.sum_mul]
    _ ≤ (1 + Real.log N) ^ 3 * H :=
      mul_le_mul_of_nonneg_right (reciprocal_lcm_sum_le_log_cube N) hH
    _ ≤ (1 + Real.log N) ^ 3 * (1 + Real.log N) :=
      mul_le_mul_of_nonneg_left hHlog (pow_nonneg (hH.trans hHlog) 3)
    _ = _ := by ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensitySquareSeries
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual divisor coefficients of the squared character L-function -/

namespace Ostmann

open scoped BigOperators Classical

 theorem density_character_self_convolution {q : ℕ} (χ : DirichletCharacter ℂ q) :
    LSeries.convolution (fun n : ℕ => χ (n : ZMod q)) (fun n : ℕ => χ (n : ZMod q)) =
      fun n : ℕ => χ (n : ZMod q) * (n.divisors.card : ℂ) := by
  funext n
  rw [LSeries.convolution_def]
  calc
    _ = ∑ _p ∈ n.divisorsAntidiagonal, χ (n : ZMod q) := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [← map_mul, ← Nat.cast_mul, (Nat.mem_divisorsAntidiagonal.mp hp).1]
    _ = _ := by
      rw [Nat.sum_divisorsAntidiagonal' (fun _ _ => χ (n : ZMod q))]
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring

 theorem density_square_LSeries {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (s : ℂ) (hs : 1 < s.re) :
    LSeries (fun n : ℕ => χ (n : ZMod q) * (n.divisors.card : ℂ)) s =
      DirichletCharacter.LFunction χ s ^ 2 := by
  rw [← density_character_self_convolution χ,
    LSeries_convolution' (χ.LSeriesSummable_of_one_lt_re hs)
      (χ.LSeriesSummable_of_one_lt_re hs), ← DirichletCharacter.LFunction_eq_LSeries χ hs]
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensitySquareTerms
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Absolutely integrable Dirichlet terms on the initial right line -/

namespace Ostmann

open Complex MeasureTheory

 theorem densitySquareCoefficient_summable (χ : PrimitiveComplexCharacter) :
    LSeriesSummable (densitySquareCoefficient χ) (3 / 2 : ℂ) := by
  let : NeZero χ.modulus := ⟨χ.positive.ne'⟩
  have h := (χ.character.LSeriesSummable_of_one_lt_re (s := (3 / 2 : ℂ)) (by norm_num)).convolution
    (χ.character.LSeriesSummable_of_one_lt_re (s := (3 / 2 : ℂ)) (by norm_num))
  rw [density_character_self_convolution] at h
  exact h

 theorem densitySquareSeriesTerm_bound (χ : PrimitiveComplexCharacter) (s : ℂ)
    (hs : s.re = 1 / 2) (n : ℕ) (u : ℝ) :
    ‖densitySquareSeriesTerm χ s n u‖ ≤
      ((Real.exp (2 * (59 + |Real.eulerMascheroniConstant|) + 4 +
        2 * (59 + |Real.eulerMascheroniConstant|) ^ 2) *
        ((χ.modulus : ℝ) * (|s.im| + 2))) *
        ‖LSeries.term (densitySquareCoefficient χ) (3 / 2 : ℂ) n‖) *
          Real.exp (-(u ^ 2) / 2) := by
  have he : ‖LSeries.term (densitySquareCoefficient χ) (s + (1 + (u : ℂ) * I)) n‖ =
      ‖LSeries.term (densitySquareCoefficient χ) (3 / 2 : ℂ) n‖ := by
    simp only [LSeries.norm_term_eq]
    norm_num [hs]
  rw [densitySquareSeriesTerm, norm_mul, he]
  have h := mul_le_mul_of_nonneg_right (densitySquareKernel_line_bound χ s hs u)
    (norm_nonneg (LSeries.term (densitySquareCoefficient χ) (3 / 2 : ℂ) n))
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ring

 theorem densitySquareSeriesTerm_continuous (χ : PrimitiveComplexCharacter) (s : ℂ)
    (hs : s.re = 1 / 2) (n : ℕ) : Continuous (densitySquareSeriesTerm χ s n) := by
  apply (densitySquareKernel_line_continuous χ s hs).mul
  by_cases hn : n = 0
  · subst n
    simp only [LSeries.term_zero]
    exact continuous_const
  · simp only [LSeries.term_of_ne_zero hn]
    have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    have hp : Continuous (fun u : ℝ => (n : ℂ) ^ (s + (1 + u * I))) :=
      (differentiable_id.const_cpow (Or.inl hnC)).continuous.comp (by fun_prop)
    exact continuous_const.div hp (fun u => Complex.cpow_ne_zero_iff.mpr (Or.inl hnC))

 theorem densitySquareSeriesTerm_integrable (χ : PrimitiveComplexCharacter) (s : ℂ)
    (hs : s.re = 1 / 2) (n : ℕ) : Integrable (densitySquareSeriesTerm χ s n) := by
  have hg : Integrable (fun u : ℝ => Real.exp (-(u ^ 2) / 2)) := by
    convert integrable_exp_neg_mul_sq (b := (1 / 2 : ℝ)) (by norm_num) using 1
    all_goals try with_reducible_and_instances rfl
    funext u
    congr 1
    ring
  apply (hg.const_mul ((Real.exp (2 * (59 + |Real.eulerMascheroniConstant|) + 4 +
        2 * (59 + |Real.eulerMascheroniConstant|) ^ 2) *
        ((χ.modulus : ℝ) * (|s.im| + 2))) *
        ‖LSeries.term (densitySquareCoefficient χ) (3 / 2 : ℂ) n‖)).mono'
    (densitySquareSeriesTerm_continuous χ s hs n).aestronglyMeasurable
  filter_upwards with u
  exact densitySquareSeriesTerm_bound χ s hs n u

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensitySquareSeriesIntegral
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exchanging the actual divisor series and the Gaussian contour integral -/

namespace Ostmann

open Complex MeasureTheory

 theorem densitySquareSeriesTerm_integral_summable (χ : PrimitiveComplexCharacter) (s : ℂ)
    (hs : s.re = 1 / 2) :
    Summable (fun n : ℕ => ∫ u : ℝ, ‖densitySquareSeriesTerm χ s n u‖) := by
  let K := Real.exp (2 * (59 + |Real.eulerMascheroniConstant|) + 4 +
    2 * (59 + |Real.eulerMascheroniConstant|) ^ 2) * ((χ.modulus : ℝ) * (|s.im| + 2))
  let g : ℝ → ℝ := fun u => Real.exp (-(u ^ 2) / 2)
  have hg : Integrable g := by
    convert integrable_exp_neg_mul_sq (b := (1 / 2 : ℝ)) (by norm_num) using 1
    all_goals try with_reducible_and_instances rfl
    funext u
    dsimp [g]
    congr 1
    ring
  have hb (n : ℕ) : (∫ u : ℝ, ‖densitySquareSeriesTerm χ s n u‖) ≤
      (K * ‖LSeries.term (densitySquareCoefficient χ) (3 / 2 : ℂ) n‖) * ∫ u : ℝ, g u := by
    rw [← integral_const_mul]
    apply integral_mono_ae (densitySquareSeriesTerm_integrable χ s hs n).norm
      (hg.const_mul _)
    filter_upwards with u
    exact densitySquareSeriesTerm_bound χ s hs n u
  have hsum := ((densitySquareCoefficient_summable χ).norm.mul_left K).mul_right (∫ u : ℝ, g u)
  exact hsum.of_nonneg_of_le (fun n => integral_nonneg (fun u => norm_nonneg _)) hb

 theorem densitySmoothedSquare_series (χ : PrimitiveComplexCharacter) (s : ℂ)
    (hs : s.re = 1 / 2) : densitySmoothedSquare χ s = ∑' n : ℕ, densitySquareIntegralTerm χ s n := by
  let : NeZero χ.modulus := ⟨χ.positive.ne'⟩
  have he (u : ℝ) : densitySquareKernel χ s (1 + u * I) * χ.L (s + (1 + u * I)) ^ 2 =
      ∑' n : ℕ, densitySquareSeriesTerm χ s n u := by
    have hp : 1 < (s + (1 + (u : ℂ) * I)).re := by norm_num [hs]
    have hL : χ.L (s + (1 + u * I)) ^ 2 =
        LSeries (densitySquareCoefficient χ) (s + (1 + u * I)) :=
      (density_square_LSeries χ.character _ hp).symm
    rw [hL, LSeries, ← tsum_mul_left]
    rfl
  rw [densitySmoothedSquare_integral χ s hs]
  simp_rw [he]
  rw [← integral_tsum_of_summable_integral_norm (fun n => densitySquareSeriesTerm_integrable χ s hs n)
    (densitySquareSeriesTerm_integral_summable χ s hs)]
  exact tsum_mul_left.symm

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityFiniteSeriesBridge
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original divisor coefficients in each shifted finite contour -/

namespace Ostmann

open Complex MeasureTheory
open scoped BigOperators

 theorem density_LSeries_term_add (a : ℕ → ℂ) (s w : ℂ) (n : ℕ) :
    LSeries.term a (s + w) n = LSeries.term a s n / (n : ℂ) ^ w := by
  by_cases hn : n = 0
  · subst n
    simp
  · have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn, Complex.cpow_add _ _ hnC]
    ring

 theorem densityFiniteKernel_original_terms (χ : PrimitiveComplexCharacter) (s w : ℂ)
    (S : Finset ℕ) :
    densityFiniteKernel χ s S (fun n => LSeries.term (densitySquareCoefficient χ) s n) w =
      ∑ n ∈ S, densitySquareKernel χ s w * LSeries.term (densitySquareCoefficient χ) (s + w) n := by
  unfold densityFiniteKernel densityFiniteMellin
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  rw [density_LSeries_term_add]

 theorem densitySquareIntegralTerm_sum (χ : PrimitiveComplexCharacter) (s : ℂ)
    (hs : s.re = 1 / 2) (S : Finset ℕ) :
    (∑ n ∈ S, densitySquareIntegralTerm χ s n) =
      (2 * (Real.pi : ℂ))⁻¹ * ∫ u : ℝ,
        densityFiniteKernel χ s S (fun n => LSeries.term (densitySquareCoefficient χ) s n) (1 + u * I) := by
  unfold densitySquareIntegralTerm
  rw [← Finset.mul_sum, ← integral_finsetSum S (fun n _ => densitySquareSeriesTerm_integrable χ s hs n)]
  congr 1
  apply integral_congr_ae
  filter_upwards with u
  exact (densityFiniteKernel_original_terms χ s (1 + u * I) S).symm

 theorem densitySquareIntegralTerm_sum_shift (χ : PrimitiveComplexCharacter) (s : ℂ)
    (hs : s.re = 1 / 2) (S : Finset ℕ) (hS : ∀ n ∈ S, 1 ≤ n)
    (c : ℝ) (hc : 0 < c) (hc1 : c ≤ 1) :
    (∑ n ∈ S, densitySquareIntegralTerm χ s n) =
      (2 * (Real.pi : ℂ))⁻¹ * ∫ u : ℝ,
        densityFiniteKernel χ s S (fun n => LSeries.term (densitySquareCoefficient χ) s n)
          ((c : ℂ) + u * I) := by
  rw [densitySquareIntegralTerm_sum χ s hs S,
    densityFiniteKernel_shift χ s hs S (fun n => LSeries.term (densitySquareCoefficient χ) s n) hS c hc hc1]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityWeightedCauchy
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The weighted Cauchy inequality used for the finite contour polynomials -/

namespace Ostmann

open MeasureTheory

 theorem density_weighted_cauchy (g p : ℝ → ℝ)
    (hg : Integrable g) (hgp : Integrable (fun u => g u * p u))
    (hgpp : Integrable (fun u => g u * (p u) ^ 2))
    (hg0 : ∀ u, 0 ≤ g u) (hpos : 0 < ∫ u, g u) :
    (∫ u, g u * p u) ^ 2 ≤ (∫ u, g u) * ∫ u, g u * (p u) ^ 2 := by
  let A := ∫ u, g u
  let B := ∫ u, g u * p u
  let D := ∫ u, g u * (p u) ^ 2
  let t := B / A
  have hA : 0 < A := hpos
  have htA : t * A = B := div_mul_cancel₀ B hA.ne'
  have he : (∫ u, g u * (p u - t) ^ 2) = D - 2 * t * B + t ^ 2 * A := by
    have hf : (fun u => g u * (p u - t) ^ 2) =
        (fun u => (g u * (p u) ^ 2 - (2 * t) * (g u * p u)) + t ^ 2 * g u) := by
      funext u
      ring
    rw [hf]
    have hadd := integral_add (hgpp.sub (hgp.const_mul (2 * t))) (hg.const_mul (t ^ 2))
    have hsub := integral_sub hgpp (hgp.const_mul (2 * t))
    simp only [Pi.sub_apply] at hadd hsub
    rw [hadd, hsub, integral_const_mul, integral_const_mul]
  have hn : 0 ≤ D - 2 * t * B + t ^ 2 * A := by
    rw [← he]
    exact integral_nonneg (fun u => mul_nonneg (hg0 u) (sq_nonneg _))
  have hm := mul_nonneg hA.le hn
  have hs : (t * A) ^ 2 = B ^ 2 := congrArg (fun x : ℝ => x ^ 2) htA
  change B ^ 2 ≤ A * D
  nlinarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityGaussianCauchy
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Weighted square bounds for the Gaussian contour integral -/

namespace Ostmann

open MeasureTheory

 theorem densityHalfGaussian_integrable : Integrable densityHalfGaussian := by
  convert integrable_exp_neg_mul_sq (b := (1 / 2 : ℝ)) (by norm_num) using 1
  all_goals try with_reducible_and_instances rfl
  funext u
  unfold densityHalfGaussian
  congr 1
  ring

 theorem densityHalfGaussian_pos (u : ℝ) : 0 < densityHalfGaussian u := Real.exp_pos _

 theorem densityHalfGaussian_continuous : Continuous densityHalfGaussian := by
  unfold densityHalfGaussian
  fun_prop

 theorem densityHalfGaussian_integral_pos : 0 < ∫ u, densityHalfGaussian u :=
  integral_exp_pos densityHalfGaussian_integrable

 theorem density_gaussian_integral_cauchy (f : ℝ → ℂ) (p : ℝ → ℝ) (M A : ℝ)
    (hp : Continuous p) (hp0 : ∀ u, 0 ≤ p u) (hpA : ∀ u, p u ≤ A)
    (hb : ∀ u, ‖f u‖ ≤ M * densityHalfGaussian u * p u) :
    ‖∫ u, f u‖ ^ 2 ≤ M ^ 2 * (∫ u, densityHalfGaussian u) *
      ∫ u, densityHalfGaussian u * (p u) ^ 2 := by
  have hg := densityHalfGaussian_integrable
  have hc := densityHalfGaussian_continuous
  have hA : 0 ≤ A := (hp0 0).trans (hpA 0)
  have hgp : Integrable (fun u => densityHalfGaussian u * p u) := by
    apply (hg.const_mul A).mono' (hc.mul hp).aestronglyMeasurable
    filter_upwards with u
    simp only [Pi.mul_apply]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (densityHalfGaussian_pos u).le (hp0 u))]
    nlinarith [densityHalfGaussian_pos u, hpA u]
  have hgpp : Integrable (fun u => densityHalfGaussian u * (p u) ^ 2) := by
    apply (hg.const_mul (A ^ 2)).mono' (hc.mul (hp.pow 2)).aestronglyMeasurable
    filter_upwards with u
    simp only [Pi.mul_apply, Pi.pow_apply]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (densityHalfGaussian_pos u).le (sq_nonneg _))]
    have hh := pow_le_pow_left₀ (hp0 u) (hpA u) 2
    nlinarith [densityHalfGaussian_pos u]
  have hn : ‖∫ u, f u‖ ≤ M * ∫ u, densityHalfGaussian u * p u := by
    rw [← integral_const_mul]
    apply norm_integral_le_of_norm_le (hgp.const_mul M)
    filter_upwards with u
    simpa only [mul_assoc] using hb u
  have hs := density_weighted_cauchy densityHalfGaussian p hg hgp hgpp
    (fun u => (densityHalfGaussian_pos u).le) densityHalfGaussian_integral_pos
  calc
    _ ≤ (M * ∫ u, densityHalfGaussian u * p u) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hn 2
    _ = M ^ 2 * (∫ u, densityHalfGaussian u * p u) ^ 2 := mul_pow _ _ _
    _ ≤ M ^ 2 * ((∫ u, densityHalfGaussian u) * ∫ u, densityHalfGaussian u * (p u) ^ 2) :=
      mul_le_mul_of_nonneg_left hs (sq_nonneg M)
    _ = _ := by ring

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
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityShiftedHybrid
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The hybrid large sieve on translated height intervals -/

namespace Ostmann

open MeasureTheory Set
open scoped BigOperators Interval Classical

 theorem density_interval_translate_le (f : ℝ → ℝ) (hf : Continuous f)
    (hf0 : ∀ t, 0 ≤ f t) (T u : ℝ) (hT : 0 ≤ T) :
    (∫ t in Icc (-T) T, f (t + u)) ≤
      ∫ t in Icc (-(T + |u|)) (T + |u|), f t := by
  have he : (∫ t in Icc (-T) T, f (t + u)) =
      ∫ t in Icc (-T + u) (T + u), f t := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith : -T ≤ T),
      intervalIntegral.integral_comp_add_right, intervalIntegral.integral_of_le (by linarith : -T + u ≤ T + u),
      ← integral_Icc_eq_integral_Ioc]
  rw [he]
  apply setIntegral_mono_set hf.integrableOn_Icc (Filter.Eventually.of_forall hf0)
  apply Filter.Eventually.of_forall
  intro t ht
  exact ⟨by linarith [ht.1, neg_le_abs u], by linarith [ht.2, le_abs_self u]⟩

 theorem shifted_hybrid_multiplicative_large_sieve :
    ∃ C : ℝ, 0 < C ∧ ∀ N Q : ℕ, 1 ≤ Q → ∀ T u : ℝ, 1 ≤ T →
      ∀ a : ℕ → ℂ, ∀ F : (q : ℕ) → Finset (DirichletCharacter ℂ q),
      (∀ q ∈ Finset.Icc 1 Q, ∀ χ ∈ F q, χ.IsPrimitive) →
      (∑ q ∈ Finset.Icc 1 Q, ∑ χ ∈ F q,
        ∫ t in Icc (-T) T, ‖∑ n ∈ Finset.Icc 1 N,
          a n * χ (n : ZMod q) * realAdditivePhase (-(Real.log n * (t + u)))‖ ^ 2) ≤
        C * ((N : ℝ) + (Q : ℝ) ^ 2 * (T + |u|)) * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 := by
  obtain ⟨C, hC, hb⟩ := hybrid_multiplicative_large_sieve
  refine ⟨C, hC, ?_⟩
  intro N Q hQ T u hT a F hF
  apply le_trans _ (hb N Q hQ (T + |u|) (by linarith [abs_nonneg u]) a F hF)
  apply Finset.sum_le_sum
  intro q hq
  apply Finset.sum_le_sum
  intro χ hχ
  let f : ℝ → ℝ := fun t => ‖∑ n ∈ Finset.Icc 1 N,
    a n * χ (n : ZMod q) * realAdditivePhase (-(Real.log n * t))‖ ^ 2
  have hc : Continuous f := by
    dsimp [f, realAdditivePhase]
    fun_prop
  exact density_interval_translate_le f hc (fun t => sq_nonneg _) T u (by linarith)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityGaussianHybrid
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The hybrid mean square averaged over the Gaussian translation -/

namespace Ostmann

open MeasureTheory Set
open scoped BigOperators Classical

 theorem densityHalfGaussian_first_moment :
    Integrable (fun u : ℝ => densityHalfGaussian u * |u|) := by
  have h := (integrable_mul_exp_neg_mul_sq (b := (1 / 2 : ℝ)) (by norm_num)).norm
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext u
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  unfold densityHalfGaussian
  rw [mul_comm]
  congr 1
  congr 1
  ring

 theorem gaussian_hybrid_multiplicative_large_sieve :
    ∃ C : ℝ, 0 < C ∧ ∀ N Q : ℕ, 1 ≤ Q → ∀ T : ℝ, 1 ≤ T →
      ∀ a : ℕ → ℂ, ∀ F : (q : ℕ) → Finset (DirichletCharacter ℂ q),
      (∀ q ∈ Finset.Icc 1 Q, ∀ χ ∈ F q, χ.IsPrimitive) →
      (∫ u : ℝ, densityHalfGaussian u *
        (∑ q ∈ Finset.Icc 1 Q, ∑ χ ∈ F q,
          ∫ t in Icc (-T) T, ‖∑ n ∈ Finset.Icc 1 N,
            a n * χ (n : ZMod q) * realAdditivePhase (-(Real.log n * (t + u)))‖ ^ 2)) ≤
          C * ((N : ℝ) + (Q : ℝ) ^ 2 * T) * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 := by
  obtain ⟨C, hC, hb⟩ := shifted_hybrid_multiplicative_large_sieve
  let G0 := ∫ u : ℝ, densityHalfGaussian u
  let G1 := ∫ u : ℝ, densityHalfGaussian u * |u|
  have hG0 : 0 < G0 := densityHalfGaussian_integral_pos
  have hG1 : 0 ≤ G1 := integral_nonneg (fun u => mul_nonneg (densityHalfGaussian_pos u).le (abs_nonneg u))
  refine ⟨C * (G0 + G1), by positivity, ?_⟩
  intro N Q hQ T hT a F hF
  let E := ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2
  let A := (N : ℝ) + (Q : ℝ) ^ 2 * T
  have hE : 0 ≤ E := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  let H : ℝ → ℝ := fun u => ∑ q ∈ Finset.Icc 1 Q, ∑ χ ∈ F q,
    ∫ t in Icc (-T) T, ‖∑ n ∈ Finset.Icc 1 N,
      a n * χ (n : ZMod q) * realAdditivePhase (-(Real.log n * (t + u)))‖ ^ 2
  have hmaj : Integrable (fun u => densityHalfGaussian u * (C * (A + (Q : ℝ) ^ 2 * |u|) * E)) := by
    have he : (fun u => densityHalfGaussian u * (C * (A + (Q : ℝ) ^ 2 * |u|) * E)) =
        (fun u => (C * E * A) * densityHalfGaussian u +
          (C * E * (Q : ℝ) ^ 2) * (densityHalfGaussian u * |u|)) := by
      funext u
      ring
    rw [he]
    exact (densityHalfGaussian_integrable.const_mul _).add (densityHalfGaussian_first_moment.const_mul _)
  have hmean : (∫ u, densityHalfGaussian u * H u) ≤
      ∫ u, densityHalfGaussian u * (C * (A + (Q : ℝ) ^ 2 * |u|) * E) := by
    apply integral_mono_of_nonneg
      (Filter.Eventually.of_forall (fun u => mul_nonneg (densityHalfGaussian_pos u).le
        (Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ =>
          integral_nonneg (fun _ => sq_nonneg _)))))) hmaj
    apply Filter.Eventually.of_forall
    intro u
    have h := hb N Q hQ T u hT a F hF
    have he : (N : ℝ) + (Q : ℝ) ^ 2 * (T + |u|) = A + (Q : ℝ) ^ 2 * |u| := by dsimp [A]; ring
    rw [he] at h
    exact mul_le_mul_of_nonneg_left h (densityHalfGaussian_pos u).le
  have heval : (∫ u, densityHalfGaussian u * (C * (A + (Q : ℝ) ^ 2 * |u|) * E)) =
      C * E * (A * G0 + (Q : ℝ) ^ 2 * G1) := by
    have he : (fun u => densityHalfGaussian u * (C * (A + (Q : ℝ) ^ 2 * |u|) * E)) =
        (fun u => (C * E * A) * densityHalfGaussian u +
          (C * E * (Q : ℝ) ^ 2) * (densityHalfGaussian u * |u|)) := by
      funext u
      ring
    rw [he, integral_add (densityHalfGaussian_integrable.const_mul _)
      (densityHalfGaussian_first_moment.const_mul _), integral_const_mul, integral_const_mul]
    dsimp [G0, G1]
    ring
  change (∫ u, densityHalfGaussian u * H u) ≤ _
  apply hmean.trans
  rw [heval]
  have hQA : (Q : ℝ) ^ 2 ≤ A := by dsimp [A]; nlinarith [Nat.cast_nonneg (α := ℝ) N, sq_nonneg (Q : ℝ)]
  have hg := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hQA hG1) (mul_nonneg hC.le hE)
  change _ ≤ C * (G0 + G1) * A * E
  nlinarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityGaussianFubini
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The Gaussian and height integrals for actual character polynomials -/

namespace Ostmann

open MeasureTheory Set
open scoped BigOperators Classical

 theorem densityCharacterPolynomial_continuous {q : ℕ} (S : Finset ℕ) (a : ℕ → ℂ)
    (χ : DirichletCharacter ℂ q) : Continuous (densityCharacterPolynomial S a χ) := by
  unfold densityCharacterPolynomial realAdditivePhase
  fun_prop

 theorem densityCharacterPolynomial_norm {q : ℕ} [NeZero q] (S : Finset ℕ) (a : ℕ → ℂ)
    (χ : DirichletCharacter ℂ q) (t : ℝ) :
    ‖densityCharacterPolynomial S a χ t‖ ≤ ∑ n ∈ S, ‖a n‖ := by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro n _
  rw [norm_mul, norm_mul, norm_realAdditivePhase, mul_one]
  exact mul_le_of_le_one_right (norm_nonneg _) (χ.norm_le_one _)

 theorem density_gaussian_character_integrable {q : ℕ} [NeZero q] (S : Finset ℕ)
    (a : ℕ → ℂ) (χ : DirichletCharacter ℂ q) (T : ℝ) :
    Integrable (fun z : ℝ × ℝ => densityHalfGaussian z.2 *
      ‖densityCharacterPolynomial S a χ (z.1 + z.2)‖ ^ 2)
      ((volume.restrict (Icc (-T) T)).prod volume) := by
  let μ := volume.restrict (Icc (-T) T)
  have : IsFiniteMeasure μ := by dsimp [μ]; infer_instance
  have hbase : Integrable (fun z : ℝ × ℝ => densityHalfGaussian z.2) (μ.prod volume) := by
    simpa only [one_mul] using (integrable_const (1 : ℝ) (μ := μ)).mul_prod densityHalfGaussian_integrable
  have hc : Continuous (fun z : ℝ × ℝ => densityHalfGaussian z.2 *
      ‖densityCharacterPolynomial S a χ (z.1 + z.2)‖ ^ 2) := by
    exact (densityHalfGaussian_continuous.comp continuous_snd).mul
      (((densityCharacterPolynomial_continuous S a χ).comp (continuous_fst.add continuous_snd)).norm.pow 2)
  apply (hbase.const_mul ((∑ n ∈ S, ‖a n‖) ^ 2)).mono' hc.aestronglyMeasurable
  filter_upwards with z
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (densityHalfGaussian_pos z.2).le (sq_nonneg _))]
  have h := pow_le_pow_left₀ (norm_nonneg _) (densityCharacterPolynomial_norm S a χ (z.1 + z.2)) 2
  nlinarith [densityHalfGaussian_pos z.2]

 theorem density_gaussian_character_fubini {q : ℕ} [NeZero q] (S : Finset ℕ)
    (a : ℕ → ℂ) (χ : DirichletCharacter ℂ q) (T : ℝ) :
    (∫ t in Icc (-T) T, ∫ u : ℝ, densityHalfGaussian u *
      ‖densityCharacterPolynomial S a χ (t + u)‖ ^ 2) =
      ∫ u : ℝ, densityHalfGaussian u * ∫ t in Icc (-T) T,
        ‖densityCharacterPolynomial S a χ (t + u)‖ ^ 2 := by
  rw [integral_integral_swap (density_gaussian_character_integrable S a χ T)]
  apply integral_congr_ae
  filter_upwards with u
  rw [integral_const_mul]

 theorem gaussian_hybrid_mean :
    ∃ C : ℝ, 0 < C ∧ ∀ N Q : ℕ, 1 ≤ Q → ∀ T : ℝ, 1 ≤ T →
      ∀ a : ℕ → ℂ, ∀ F : (q : ℕ) → Finset (DirichletCharacter ℂ q),
      (∀ q ∈ Finset.Icc 1 Q, ∀ χ ∈ F q, χ.IsPrimitive) →
      (∑ q ∈ Finset.Icc 1 Q, ∑ χ ∈ F q,
        ∫ t in Icc (-T) T, ∫ u : ℝ, densityHalfGaussian u *
          ‖densityCharacterPolynomial (Finset.Icc 1 N) a χ (t + u)‖ ^ 2) ≤
            C * ((N : ℝ) + (Q : ℝ) ^ 2 * T) * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 := by
  obtain ⟨C, hC, hb⟩ := gaussian_hybrid_multiplicative_large_sieve
  refine ⟨C, hC, ?_⟩
  intro N Q hQ T hT a F hF
  have hi (q : ℕ) (hq : q ∈ Finset.Icc 1 Q) (χ : DirichletCharacter ℂ q) :
      Integrable (fun u : ℝ => densityHalfGaussian u * ∫ t in Icc (-T) T,
        ‖densityCharacterPolynomial (Finset.Icc 1 N) a χ (t + u)‖ ^ 2) := by
    let : NeZero q := ⟨by have := (Finset.mem_Icc.mp hq).1; omega⟩
    have h := (density_gaussian_character_integrable (Finset.Icc 1 N) a χ T).integral_prod_right
    simpa only [integral_const_mul] using h
  calc
    _ = ∑ q ∈ Finset.Icc 1 Q, ∑ χ ∈ F q,
        ∫ u : ℝ, densityHalfGaussian u * ∫ t in Icc (-T) T,
          ‖densityCharacterPolynomial (Finset.Icc 1 N) a χ (t + u)‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro q hq
      let : NeZero q := ⟨by have := (Finset.mem_Icc.mp hq).1; omega⟩
      apply Finset.sum_congr rfl
      intro χ _
      exact density_gaussian_character_fubini (Finset.Icc 1 N) a χ T
    _ = ∫ u : ℝ, densityHalfGaussian u *
        (∑ q ∈ Finset.Icc 1 Q, ∑ χ ∈ F q, ∫ t in Icc (-T) T,
          ‖densityCharacterPolynomial (Finset.Icc 1 N) a χ (t + u)‖ ^ 2) := by
      symm
      simp_rw [Finset.mul_sum]
      rw [integral_finsetSum _ (fun q hq => integrable_finsetSum _ (fun χ _ => hi q hq χ))]
      apply Finset.sum_congr rfl
      intro q hq
      exact integral_finsetSum _ (fun χ _ => hi q hq χ)
    _ ≤ _ := by simpa only [densityCharacterPolynomial] using hb N Q hQ T hT a F hF

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
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityFourierContour
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact Fourier scaling of the original finite contour sums -/

namespace Ostmann

open Complex MeasureTheory
open scoped BigOperators

 theorem density_fourier_integral_scale (f : ℝ → ℂ) :
    (2 * (Real.pi : ℂ))⁻¹ * (∫ u : ℝ, f u) = ∫ u : ℝ, f (2 * Real.pi * u) := by
  rw [Measure.integral_comp_mul_left f (2 * Real.pi),
    abs_of_pos (inv_pos.mpr (mul_pos (by norm_num) Real.pi_pos))]
  simp only [Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_mul, Complex.ofReal_ofNat]

 theorem densitySquareIntegralTerm_sum_fourier (χ : PrimitiveComplexCharacter) (s : ℂ)
    (hs : s.re = 1 / 2) (S : Finset ℕ) (hS : ∀ n ∈ S, 1 ≤ n)
    (c : ℝ) (hc : 0 < c) (hc1 : c ≤ 1) :
    (∑ n ∈ S, densitySquareIntegralTerm χ s n) =
      ∫ u : ℝ, densityFiniteKernel χ s S (fun n => LSeries.term (densitySquareCoefficient χ) s n)
        ((c : ℂ) + (2 * Real.pi * u : ℝ) * I) := by
  rw [densitySquareIntegralTerm_sum_shift χ s hs S hS c hc hc1,
    density_fourier_integral_scale]

 theorem densityFiniteMellin_original_polynomial (χ : PrimitiveComplexCharacter)
    (S : Finset ℕ) (hS : ∀ n ∈ S, 1 ≤ n) (c t u : ℝ) :
    densityFiniteMellin S (fun n => LSeries.term (densitySquareCoefficient χ)
      (densityVerticalPoint (1 / 2) t) n) ((c : ℂ) + (2 * Real.pi * u : ℝ) * I) =
      densityCharacterPolynomial S
        (densityVerticalCoeff (fun n : ℕ => (n.divisors.card : ℂ)) (1 / 2 + c))
        χ.character (t + u) := by
  unfold densityFiniteMellin densityCharacterPolynomial
  apply Finset.sum_congr rfl
  intro n hn
  rw [← density_LSeries_term_add]
  have hp : 0 < n := lt_of_lt_of_le Nat.zero_lt_one (hS n hn)
  have he : densityVerticalPoint (1 / 2) t + ((c : ℂ) + (2 * Real.pi * u : ℝ) * I) =
      densityVerticalPoint (1 / 2 + c) (t + u) := by
    unfold densityVerticalPoint
    push_cast
    ring
  rw [he, LSeries.term_of_ne_zero hp.ne', density_vertical_term _ _ _ n hp]
  unfold densitySquareCoefficient densityVerticalCoeff
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityKernelLineBound
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The short-line kernel bound retaining its exact conductor exponent -/

namespace Ostmann

open Complex

 theorem densitySquareKernel_short_line (χ : PrimitiveComplexCharacter) (s : ℂ)
    (hs : s.re = 1 / 2) (c u : ℝ) (hc : 0 < c) (hc1 : c ≤ 1) :
    ‖densitySquareKernel χ s ((c : ℂ) + u * I)‖ ≤
      (Real.exp (2 * (59 + |Real.eulerMascheroniConstant|) + 4 +
        2 * (59 + |Real.eulerMascheroniConstant|) ^ 2) *
        ((χ.modulus : ℝ) * (|s.im| + 2)) ^ c / c) * densityHalfGaussian u := by
  have hb := densityCompletedSquareWeight_bound χ s ((c : ℂ) + u * I) hs
    (by simp; linarith) (by simp; linarith)
  have he : ((c : ℂ) + u * I).re = c := by simp
  have hi : ((c : ℂ) + u * I).im = u := by simp
  rw [he, hi] at hb
  have hn : c ≤ ‖(c : ℂ) + u * I‖ := by simpa only [he] using Complex.re_le_norm ((c : ℂ) + u * I)
  rw [densitySquareKernel, norm_div]
  apply (div_le_div_of_nonneg_left (norm_nonneg _) hc hn).trans
  have hd := div_le_div_of_nonneg_right hb hc.le
  unfold densityHalfGaussian
  convert hd using 1
  all_goals try with_reducible_and_instances rfl
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityFiniteSquareEnergy
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original finite square sum bounded by its Gaussian polynomial energy -/

namespace Ostmann

open Complex MeasureTheory
open scoped BigOperators

 theorem densityHalfGaussian_fourier_scale (u : ℝ) :
    densityHalfGaussian (2 * Real.pi * u) ≤ densityHalfGaussian u := by
  unfold densityHalfGaussian
  apply Real.exp_le_exp.mpr
  have hp : 1 ≤ (2 * Real.pi) ^ 2 := by nlinarith [Real.pi_gt_three]
  have h := mul_nonneg (sub_nonneg.mpr hp) (sq_nonneg u)
  nlinarith

 theorem densityFiniteSquare_energy (χ : PrimitiveComplexCharacter)
    (S : Finset ℕ) (hS : ∀ n ∈ S, 1 ≤ n) (c t : ℝ) (hc : 0 < c) (hc1 : c ≤ 1) :
    ‖∑ n ∈ S, densitySquareIntegralTerm χ (densityVerticalPoint (1 / 2) t) n‖ ^ 2 ≤
      (Real.exp (2 * (59 + |Real.eulerMascheroniConstant|) + 4 +
        2 * (59 + |Real.eulerMascheroniConstant|) ^ 2) *
        ((χ.modulus : ℝ) * (|(densityVerticalPoint (1 / 2) t).im| + 2)) ^ c / c) ^ 2 *
      (∫ u : ℝ, densityHalfGaussian u) * ∫ u : ℝ, densityHalfGaussian u *
        ‖densityCharacterPolynomial S
          (densityVerticalCoeff (fun n : ℕ => (n.divisors.card : ℂ)) (1 / 2 + c))
          χ.character (t + u)‖ ^ 2 := by
  let a := densityVerticalCoeff (fun n : ℕ => (n.divisors.card : ℂ)) (1 / 2 + c)
  let s := densityVerticalPoint (1 / 2) t
  have hs : s.re = 1 / 2 := by simp [s, densityVerticalPoint]
  let M := Real.exp (2 * (59 + |Real.eulerMascheroniConstant|) + 4 +
    2 * (59 + |Real.eulerMascheroniConstant|) ^ 2) *
    ((χ.modulus : ℝ) * (|s.im| + 2)) ^ c / c
  have hM : 0 ≤ M := by dsimp [M]; positivity
  rw [densitySquareIntegralTerm_sum_fourier χ s hs S hS c hc hc1]
  have hp : Continuous (fun u : ℝ => ‖densityCharacterPolynomial S a χ.character (t + u)‖) :=
    (((densityCharacterPolynomial_continuous S a χ.character).comp (continuous_const.add continuous_id)).norm)
  let : NeZero χ.modulus := ⟨χ.positive.ne'⟩
  apply density_gaussian_integral_cauchy _ _ M (∑ n ∈ S, ‖a n‖) hp (fun _ => norm_nonneg _)
    (fun u => densityCharacterPolynomial_norm S a χ.character (t + u))
  intro u
  rw [densityFiniteKernel, norm_mul, densityFiniteMellin_original_polynomial χ S hS c t u]
  have hk := densitySquareKernel_short_line χ s hs c (2 * Real.pi * u) hc hc1
  calc
    _ ≤ (M * densityHalfGaussian (2 * Real.pi * u)) * ‖densityCharacterPolynomial S a χ.character (t + u)‖ :=
      mul_le_mul_of_nonneg_right hk (norm_nonneg _)
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (densityHalfGaussian_fourier_scale u) hM) (norm_nonneg _)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityKernelCost
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A common height and conductor cost for the smoothed square -/

namespace Ostmann

open Complex

 theorem densityKernelConstant_pos : 0 < densityKernelConstant := Real.exp_pos _

 theorem densityKernelCost_pos (Q : ℕ) (hQ : 1 ≤ Q) (T c : ℝ)
    (hT : 1 ≤ T) (hc : 0 < c) : 0 < densityKernelCost Q T c := by
  unfold densityKernelCost
  apply div_pos (mul_pos densityKernelConstant_pos _) hc
  apply Real.rpow_pos_of_pos
  have hq : (0 : ℝ) < Q := by exact_mod_cast (show 0 < Q by omega)
  positivity

 theorem density_vertical_height_bound (Q : ℕ) (_hQ : 1 ≤ Q) (T : ℝ) (hT : 1 ≤ T)
    (χ : PrimitiveComplexCharacter) (hχ : χ.modulus ≤ Q) (t : ℝ) (ht : |t| ≤ T) :
    (χ.modulus : ℝ) * (|(densityVerticalPoint (1 / 2) t).im| + 2) ≤ 10 * Q * T := by
  have hq : (χ.modulus : ℝ) ≤ Q := by exact_mod_cast hχ
  have him : (densityVerticalPoint (1 / 2) t).im = 2 * Real.pi * t := by
    simp [densityVerticalPoint]
  rw [him, abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
  have hb : 2 * Real.pi * |t| + 2 ≤ 10 * T := by
    nlinarith [Real.pi_lt_four, Real.pi_pos]
  calc
    _ ≤ (χ.modulus : ℝ) * (10 * T) := mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg _)
    _ ≤ (Q : ℝ) * (10 * T) := mul_le_mul_of_nonneg_right hq (by positivity)
    _ = _ := by ring

 theorem density_kernel_cost_bound (Q : ℕ) (hQ : 1 ≤ Q) (T c : ℝ)
    (hT : 1 ≤ T) (hc : 0 < c) (χ : PrimitiveComplexCharacter) (hχ : χ.modulus ≤ Q)
    (t : ℝ) (ht : |t| ≤ T) :
    densityKernelConstant *
        ((χ.modulus : ℝ) * (|(densityVerticalPoint (1 / 2) t).im| + 2)) ^ c / c ≤
      densityKernelCost Q T c := by
  unfold densityKernelCost
  apply div_le_div_of_nonneg_right _ hc.le
  apply mul_le_mul_of_nonneg_left _ densityKernelConstant_pos.le
  exact Real.rpow_le_rpow (by positivity)
    (density_vertical_height_bound Q hQ T hT χ hχ t ht) hc.le

 theorem densitySquareKernel_common_bound (Q : ℕ) (hQ : 1 ≤ Q) (T c : ℝ)
    (hT : 1 ≤ T) (hc : 0 < c) (hc1 : c ≤ 1)
    (χ : PrimitiveComplexCharacter) (hχ : χ.modulus ≤ Q) (t u : ℝ) (ht : |t| ≤ T) :
    ‖densitySquareKernel χ (densityVerticalPoint (1 / 2) t)
      ((c : ℂ) + (2 * Real.pi * u : ℝ) * I)‖ ≤
        densityKernelCost Q T c * densityHalfGaussian u := by
  have hs : (densityVerticalPoint (1 / 2) t).re = 1 / 2 := by simp [densityVerticalPoint]
  apply (densitySquareKernel_short_line χ _ hs c (2 * Real.pi * u) hc hc1).trans
  calc
    _ ≤ densityKernelCost Q T c * densityHalfGaussian (2 * Real.pi * u) :=
      mul_le_mul_of_nonneg_right (density_kernel_cost_bound Q hQ T c hT hc χ hχ t ht)
        (densityHalfGaussian_pos _).le
    _ ≤ _ := mul_le_mul_of_nonneg_left (densityHalfGaussian_fourier_scale u)
      (densityKernelCost_pos Q hQ T c hT hc).le

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityFiniteContinuity
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Continuity of the actual finite square on a bounded height interval -/

namespace Ostmann

open Complex MeasureTheory Set
open scoped BigOperators

 theorem densitySquareKernel_vertical_continuous (χ : PrimitiveComplexCharacter)
    (c : ℝ) (hc : 0 < c) :
    Continuous (fun z : ℝ × ℝ => densitySquareKernel χ
      (densityVerticalPoint (1 / 2) z.1) ((c : ℂ) + (2 * Real.pi * z.2 : ℝ) * I)) := by
  have hs : Continuous (fun z : ℝ × ℝ => densityVerticalPoint (1 / 2) z.1) := by
    unfold densityVerticalPoint
    fun_prop
  have hw : Continuous (fun z : ℝ × ℝ => (c : ℂ) + (2 * Real.pi * z.2 : ℝ) * I) := by fun_prop
  have hg : Continuous (fun z : ℝ × ℝ => DirichletCharacter.gammaFactor χ.character
      (densityVerticalPoint (1 / 2) z.1 + ((c : ℂ) + (2 * Real.pi * z.2 : ℝ) * I))) := by
    apply continuous_iff_continuousAt.mpr
    intro z
    apply (χ.gammaFactor_differentiableAt_pos _ (by simp [densityVerticalPoint]; linarith)).continuousAt.comp
    exact (hs.add hw).continuousAt
  have hg0 : Continuous (fun z : ℝ × ℝ =>
      DirichletCharacter.gammaFactor χ.character (densityVerticalPoint (1 / 2) z.1)) := by
    apply continuous_iff_continuousAt.mpr
    intro z
    apply (χ.gammaFactor_differentiableAt_pos _ (by norm_num [densityVerticalPoint])).continuousAt.comp
    exact hs.continuousAt
  have hgn (z : ℝ × ℝ) :
      DirichletCharacter.gammaFactor χ.character (densityVerticalPoint (1 / 2) z.1) ≠ 0 := by
    intro h
    exact χ.gammaInverse_ne_zero (densityVerticalPoint (1 / 2) z.1) (by norm_num [densityVerticalPoint])
      (by simp only [PrimitiveComplexCharacter.gammaInverse, h, inv_zero])
  have hq : (χ.modulus : ℂ) ≠ 0 := by exact_mod_cast χ.positive.ne'
  unfold densitySquareKernel densityCompletedSquareWeight
  apply Continuous.div
  · exact (((differentiable_id.const_cpow (Or.inl hq)).continuous.comp hw).mul
      ((hg.div hg0 hgn).pow 2)).mul ((hw.pow 2).cexp)
  · exact hw
  · intro z h
    have hr := congrArg Complex.re h
    simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero,
      zero_mul, sub_self, add_zero, zero_re] at hr
    exact hc.ne' hr

 theorem densityFiniteSquare_continuousOn (χ : PrimitiveComplexCharacter)
    (S : Finset ℕ) (hS : ∀ n ∈ S, 1 ≤ n) (T : ℝ) (hT : 1 ≤ T) :
    ContinuousOn (fun t : ℝ => ∑ n ∈ S,
      densitySquareIntegralTerm χ (densityVerticalPoint (1 / 2) t) n) (Icc (-T) T) := by
  let a := densityVerticalCoeff (fun n : ℕ => (n.divisors.card : ℂ)) (1 / 2 + (1 : ℝ))
  let K : ℝ := densityKernelCost χ.modulus T 1 * ∑ n ∈ S, ‖a n‖
  let f : ℝ → ℝ → ℂ := fun t u => densitySquareKernel χ
    (densityVerticalPoint (1 / 2) t) ((1 : ℂ) + (2 * Real.pi * u : ℝ) * I) *
      densityCharacterPolynomial S a χ.character (t + u)
  let : NeZero χ.modulus := ⟨χ.positive.ne'⟩
  have hf : Continuous (Function.uncurry f) := by
    exact (densitySquareKernel_vertical_continuous χ 1 (by norm_num)).mul
      ((densityCharacterPolynomial_continuous S a χ.character).comp
        (continuous_fst.add continuous_snd))
  have hI : ContinuousOn (fun t => ∫ u : ℝ, f t u) (Icc (-T) T) := by
    apply continuousOn_of_dominated (bound := fun u => K * densityHalfGaussian u)
    · intro t _
      exact (hf.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
    · intro t ht
      filter_upwards with u
      have hk := densitySquareKernel_common_bound χ.modulus χ.positive T 1 hT
        (by norm_num) (by norm_num) χ le_rfl t u (abs_le.mpr ht)
      have hp := densityCharacterPolynomial_norm S a χ.character (t + u)
      dsimp [f, K]
      rw [norm_mul]
      calc
        _ ≤ (densityKernelCost χ.modulus T 1 * densityHalfGaussian u) *
            (∑ n ∈ S, ‖a n‖) := mul_le_mul hk hp (norm_nonneg _)
              (mul_nonneg (densityKernelCost_pos χ.modulus χ.positive T 1 hT (by norm_num)).le
                (densityHalfGaussian_pos u).le)
        _ = _ := by ring
    · exact densityHalfGaussian_integrable.const_mul K
    · filter_upwards with u
      exact (hf.comp (continuous_id.prodMk continuous_const)).continuousOn
  have he (t : ℝ) : (∑ n ∈ S,
      densitySquareIntegralTerm χ (densityVerticalPoint (1 / 2) t) n) = ∫ u : ℝ, f t u := by
    rw [densitySquareIntegralTerm_sum_fourier χ _ (by simp [densityVerticalPoint]) S hS 1
      (by norm_num) (by norm_num)]
    apply integral_congr_ae
    filter_upwards with u
    rw [densityFiniteKernel, densityFiniteMellin_original_polynomial χ S hS 1 t u]
    rfl
  simpa only [← he] using hI

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

 theorem density_weighted_block_mean {α ι : Type*} (F : Finset α) (S : Finset ι)
    (f : α → ι → ℝ → ℂ) (w : ι → ℝ) (hw : ∀ i ∈ S, 0 < w i) (T : ℝ)
    (hf : ∀ χ ∈ F, ∀ i ∈ S, ContinuousOn (f χ i) (Icc (-T) T)) :
    (∑ χ ∈ F, ∫ t in Icc (-T) T, ‖∑ i ∈ S, f χ i t‖ ^ 2) ≤
      (∑ i ∈ S, w i) * ∑ i ∈ S,
        (∑ χ ∈ F, ∫ t in Icc (-T) T, ‖f χ i t‖ ^ 2) / w i := by
  have hi (χ : α) (hχ : χ ∈ F) (i : ι) (hi : i ∈ S) :
      Integrable (fun t => ‖f χ i t‖ ^ 2 / w i) (volume.restrict (Icc (-T) T)) :=
    (((hf χ hχ i hi).norm.pow 2).div_const _).integrableOn_Icc
  calc
    _ ≤ ∑ χ ∈ F, ∫ t in Icc (-T) T,
        (∑ i ∈ S, w i) * ∑ i ∈ S, ‖f χ i t‖ ^ 2 / w i := by
      apply Finset.sum_le_sum
      intro χ hχ
      apply integral_mono
      · exact ((continuousOn_finsetSum S (fun i hi => hf χ hχ i hi)).norm.pow 2).integrableOn_Icc
      · exact (integrable_finsetSum S (fun i hi' => hi χ hχ i hi')).const_mul _
      · intro t
        exact density_weighted_sum_norm_sq S (fun i => f χ i t) w hw
    _ = _ := by
      simp_rw [integral_const_mul]
      rw [← Finset.mul_sum]
      congr 1
      calc
        _ = ∑ χ ∈ F, ∑ i ∈ S, ∫ t in Icc (-T) T, ‖f χ i t‖ ^ 2 / w i := by
          apply Finset.sum_congr rfl
          intro χ hχ
          exact integral_finsetSum S (fun i hi' => hi χ hχ i hi')
        _ = _ := by
          rw [Finset.sum_comm]
          simp only [integral_div, Finset.sum_div]

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

 theorem gaussian_hybrid_primitive_mean :
    ∃ C : ℝ, 0 < C ∧ ∀ N Q : ℕ, 1 ≤ Q → ∀ T : ℝ, 1 ≤ T →
      ∀ a : ℕ → ℂ, ∀ F : Finset PrimitiveComplexCharacter,
      (∀ χ ∈ F, χ.modulus ≤ Q) →
      (∑ χ ∈ F, ∫ t in Icc (-T) T, ∫ u : ℝ, densityHalfGaussian u *
        ‖densityCharacterPolynomial (Finset.Icc 1 N) a χ.character (t + u)‖ ^ 2) ≤
          C * ((N : ℝ) + (Q : ℝ) ^ 2 * T) * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 := by
  obtain ⟨C, hC, hb⟩ := gaussian_hybrid_mean
  refine ⟨C, hC, ?_⟩
  intro N Q hQ T hT a F hF
  rw [densityCharacterFamily_sum F Q hF (fun q χ => ∫ t in Icc (-T) T,
    ∫ u : ℝ, densityHalfGaussian u *
      ‖densityCharacterPolynomial (Finset.Icc 1 N) a χ (t + u)‖ ^ 2)]
  exact hb N Q hQ T hT a (densityCharacterFamily F)
    (fun q _ χ hχ => densityCharacterFamily_primitive F q χ hχ)

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

 theorem gaussian_hybrid_primitive_subset :
    ∃ C : ℝ, 0 < C ∧ ∀ N Q : ℕ, 1 ≤ Q → ∀ T : ℝ, 1 ≤ T →
      ∀ S : Finset ℕ, S ⊆ Finset.Icc 1 N → ∀ a : ℕ → ℂ,
      ∀ F : Finset PrimitiveComplexCharacter, (∀ χ ∈ F, χ.modulus ≤ Q) →
      (∑ χ ∈ F, ∫ t in Icc (-T) T, ∫ u : ℝ, densityHalfGaussian u *
        ‖densityCharacterPolynomial S a χ.character (t + u)‖ ^ 2) ≤
          C * ((N : ℝ) + (Q : ℝ) ^ 2 * T) * ∑ n ∈ S, ‖a n‖ ^ 2 := by
  obtain ⟨C, hC, hb⟩ := gaussian_hybrid_primitive_mean
  refine ⟨C, hC, ?_⟩
  intro N Q hQ T hT S hS a F hF
  let b : ℕ → ℂ := fun n => if n ∈ S then a n else 0
  have hp (χ : PrimitiveComplexCharacter) (t : ℝ) :
      densityCharacterPolynomial (Finset.Icc 1 N) b χ.character t =
        densityCharacterPolynomial S a χ.character t := by
    unfold densityCharacterPolynomial
    convert density_sum_truncate S (Finset.Icc 1 N) hS
      (fun n => a n * χ.character (n : ZMod χ.modulus) * realAdditivePhase (-(Real.log n * t))) using 1
    all_goals try with_reducible_and_instances rfl
    apply Finset.sum_congr rfl
    intro n _
    by_cases hn : n ∈ S <;> simp [b, hn]
  have he : (∑ n ∈ Finset.Icc 1 N, ‖b n‖ ^ 2) = ∑ n ∈ S, ‖a n‖ ^ 2 := by
    convert density_sum_truncate S (Finset.Icc 1 N) hS (fun n => ‖a n‖ ^ 2) using 1
    all_goals try with_reducible_and_instances rfl
    apply Finset.sum_congr rfl
    intro n _
    by_cases hn : n ∈ S <;> simp [b, hn]
  simpa only [hp, he] using hb N Q hQ T hT b F hF

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityFiniteSquareMean
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Mean square of an actual finite piece of the smoothed square -/

namespace Ostmann

open Complex MeasureTheory Set
open scoped BigOperators Classical

 theorem densityFiniteSquare_mean :
    ∃ C : ℝ, 0 < C ∧ ∀ N Q : ℕ, 1 ≤ Q → ∀ T c : ℝ,
      1 ≤ T → 0 < c → c ≤ 1 → ∀ S : Finset ℕ, S ⊆ Finset.Icc 1 N →
      ∀ F : Finset PrimitiveComplexCharacter, (∀ χ ∈ F, χ.modulus ≤ Q) →
      (∑ χ ∈ F, ∫ t in Icc (-T) T,
        ‖∑ n ∈ S, densitySquareIntegralTerm χ (densityVerticalPoint (1 / 2) t) n‖ ^ 2) ≤
          C * (densityKernelCost Q T c) ^ 2 * ((N : ℝ) + (Q : ℝ) ^ 2 * T) *
            ∑ n ∈ S,
              ‖densityVerticalCoeff (fun n : ℕ => (n.divisors.card : ℂ)) (1 / 2 + c) n‖ ^ 2 := by
  obtain ⟨C, hC, hb⟩ := gaussian_hybrid_primitive_subset
  refine ⟨(∫ u : ℝ, densityHalfGaussian u) * C,
    mul_pos densityHalfGaussian_integral_pos hC, ?_⟩
  intro N Q hQ T c hT hc hc1 S hS F hF
  let a := densityVerticalCoeff (fun n : ℕ => (n.divisors.card : ℂ)) (1 / 2 + c)
  let G := ∫ u : ℝ, densityHalfGaussian u
  let K := densityKernelCost Q T c
  have hG : 0 ≤ G := densityHalfGaussian_integral_pos.le
  have hp (χ : PrimitiveComplexCharacter) :
      Integrable (fun t => ∫ u : ℝ, densityHalfGaussian u *
        ‖densityCharacterPolynomial S a χ.character (t + u)‖ ^ 2)
        (volume.restrict (Icc (-T) T)) := by
    let : NeZero χ.modulus := ⟨χ.positive.ne'⟩
    exact (density_gaussian_character_integrable S a χ.character T).integral_prod_left
  have hspos : ∀ n ∈ S, 1 ≤ n := fun n hn => (Finset.mem_Icc.mp (hS hn)).1
  have hpoint (χ : PrimitiveComplexCharacter) (hχ : χ ∈ F) (t : ℝ) (ht : t ∈ Icc (-T) T) :
      ‖∑ n ∈ S, densitySquareIntegralTerm χ (densityVerticalPoint (1 / 2) t) n‖ ^ 2 ≤
        K ^ 2 * G * ∫ u : ℝ, densityHalfGaussian u *
          ‖densityCharacterPolynomial S a χ.character (t + u)‖ ^ 2 := by
    apply (densityFiniteSquare_energy χ S hspos c t hc hc1).trans
    apply mul_le_mul_of_nonneg_right _ (integral_nonneg (fun u => mul_nonneg (densityHalfGaussian_pos u).le (sq_nonneg _)))
    apply mul_le_mul_of_nonneg_right _ hG
    apply pow_le_pow_left₀ (by positivity)
    exact density_kernel_cost_bound Q hQ T c hT hc χ (hF χ hχ) t (abs_le.mpr ht)
  have hm : (∑ χ ∈ F, ∫ t in Icc (-T) T,
      ‖∑ n ∈ S, densitySquareIntegralTerm χ (densityVerticalPoint (1 / 2) t) n‖ ^ 2) ≤
      K ^ 2 * G * (∑ χ ∈ F, ∫ t in Icc (-T) T, ∫ u : ℝ, densityHalfGaussian u *
        ‖densityCharacterPolynomial S a χ.character (t + u)‖ ^ 2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro χ hχ
    rw [← integral_const_mul]
    apply integral_mono_ae
    · exact (((densityFiniteSquare_continuousOn χ S hspos T hT).norm).pow 2).integrableOn_Icc
    · exact (hp χ).const_mul _
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      exact hpoint χ hχ t ht
  apply hm.trans
  have h := mul_le_mul_of_nonneg_left (hb N Q hQ T hT S hS a F hF)
    (mul_nonneg (sq_nonneg K) hG)
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ring

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

 theorem density_divisor_shifted_head (N : ℕ) (c : ℝ) (hc : 0 ≤ c) :
    (∑ n ∈ Finset.Icc 1 N,
      ‖densityVerticalCoeff (fun n : ℕ => (n.divisors.card : ℂ)) (1 / 2 + c) n‖ ^ 2) ≤
        (1 + Real.log N) ^ 4 := by
  apply (Finset.sum_le_sum (fun n hn => ?_)).trans (density_divisor_square_harmonic N)
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
  rw [densityVerticalCoeff_square _ _ n (Finset.mem_Icc.mp hn).1]
  simp only [Complex.norm_natCast]
  apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
  calc
    (n : ℝ) = (n : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
    _ ≤ (n : ℝ) ^ (2 * (1 / 2 + c)) :=
      Real.rpow_le_rpow_of_exponent_le hnR (by linarith)

 theorem density_divisor_shifted_tail (S : Finset ℕ) (M N : ℕ) (hM : 1 ≤ M)
    (hS : S ⊆ Finset.Icc M N) :
    (∑ n ∈ S,
      ‖densityVerticalCoeff (fun n : ℕ => (n.divisors.card : ℂ)) (1 / 2 + (1 : ℝ)) n‖ ^ 2) ≤
        (N : ℝ) * (1 + Real.log N) ^ 3 / (M : ℝ) ^ 3 := by
  have hMp : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  calc
    _ ≤ ∑ n ∈ S, (n.divisors.card : ℝ) ^ 2 / (M : ℝ) ^ 3 := by
      apply Finset.sum_le_sum
      intro n hn
      have hMn := (Finset.mem_Icc.mp (hS hn)).1
      have hnpos : 0 < n := lt_of_lt_of_le (by omega : 0 < M) hMn
      rw [densityVerticalCoeff_square _ _ n hnpos]
      norm_num only [Complex.norm_natCast, show (2 : ℝ) * (1 / 2 + 1) = 3 by norm_num,
        Real.rpow_natCast]
      have hp : (M : ℝ) ^ 3 ≤ (n : ℝ) ^ 3 :=
        pow_le_pow_left₀ hMp.le (by exact_mod_cast hMn) 3
      convert div_le_div_of_nonneg_left (sq_nonneg (n.divisors.card : ℝ)) (pow_pos hMp 3) hp using 1
      all_goals try with_reducible_and_instances rfl
      simp only [Real.rpow_ofNat]
    _ = (∑ n ∈ S, (n.divisors.card : ℝ) ^ 2) / (M : ℝ) ^ 3 := by rw [Finset.sum_div]
    _ ≤ (∑ n ∈ Finset.Icc 1 N, (n.divisors.card : ℝ) ^ 2) / (M : ℝ) ^ 3 := by
      apply div_le_div_of_nonneg_right _ (pow_nonneg hMp.le 3)
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro n hn
        exact Finset.mem_Icc.mpr ⟨hM.trans (Finset.mem_Icc.mp (hS hn)).1,
          (Finset.mem_Icc.mp (hS hn)).2⟩
      · intro n _ _
        positivity
    _ ≤ _ := div_le_div_of_nonneg_right (density_divisor_square_sum N) (pow_nonneg hMp.le 3)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityTailBlock
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original finite square on a distant coefficient block -/

namespace Ostmann

open Complex MeasureTheory Set
open scoped BigOperators Classical

 theorem densityFiniteSquare_tail_mean :
    ∃ C : ℝ, 0 < C ∧ ∀ M N Q : ℕ, 1 ≤ M → 1 ≤ Q → ∀ T : ℝ, 1 ≤ T →
      ∀ S : Finset ℕ, S ⊆ Finset.Icc M N →
      ∀ F : Finset PrimitiveComplexCharacter, (∀ χ ∈ F, χ.modulus ≤ Q) →
      (∑ χ ∈ F, ∫ t in Icc (-T) T,
        ‖∑ n ∈ S, densitySquareIntegralTerm χ (densityVerticalPoint (1 / 2) t) n‖ ^ 2) ≤
          C * (10 * (Q : ℝ) * T) ^ 2 * ((N : ℝ) + (Q : ℝ) ^ 2 * T) *
            ((N : ℝ) * (1 + Real.log N) ^ 3 / (M : ℝ) ^ 3) := by
  obtain ⟨C, hC, hb⟩ := densityFiniteSquare_mean
  refine ⟨C * densityKernelConstant ^ 2, mul_pos hC (sq_pos_of_pos densityKernelConstant_pos), ?_⟩
  intro M N Q hM hQ T hT S hS F hF
  have hSN : S ⊆ Finset.Icc 1 N := fun n hn =>
    Finset.mem_Icc.mpr ⟨hM.trans (Finset.mem_Icc.mp (hS hn)).1, (Finset.mem_Icc.mp (hS hn)).2⟩
  have h := hb N Q hQ T 1 hT (by norm_num) (by norm_num) S hSN F hF
  have he := density_divisor_shifted_tail S M N hM hS
  have hbound := h.trans (mul_le_mul_of_nonneg_left he (by positivity))
  convert hbound using 1
  all_goals try with_reducible_and_instances rfl
  simp only [densityKernelCost, Real.rpow_one, div_one]
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityDyadicArithmetic
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Numerical decay of the distant dyadic coefficient blocks -/

namespace Ostmann

open scoped BigOperators

 theorem density_dyadic_fraction_bound (B V A r L : ℝ)
    (hB : 0 ≤ B) (hBV : B ≤ V) (hV : 0 < V) (hA : 0 ≤ A) (hr : 1 ≤ r) (hL : 0 ≤ L) :
    B ^ 2 * (2 * r * V + A) * ((2 * r * V) * L ^ 3 / (r * V) ^ 3) ≤
      4 * (V + A) * L ^ 3 / r := by
  have hrp : 0 < r := by linarith
  have hsq : B ^ 2 ≤ V ^ 2 := pow_le_pow_left₀ hB hBV 2
  calc
    _ ≤ V ^ 2 * (2 * r * V + A) * ((2 * r * V) * L ^ 3 / (r * V) ^ 3) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_right hsq (by positivity)
    _ = (4 * V / r + 2 * A / r ^ 2) * L ^ 3 := by field_simp; ring
    _ ≤ (4 * (V + A) / r) * L ^ 3 := by
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg hL 3)
      apply (le_div_iff₀ hrp).mpr
      have hdiv : (2 * A / r ^ 2) * r = 2 * A / r := by field_simp
      rw [add_mul, div_mul_cancel₀ _ hrp.ne', hdiv]
      have hb : 2 * A / r ≤ 4 * A := by
        apply (div_le_iff₀ hrp).mpr
        nlinarith
      nlinarith
    _ = _ := by ring

 theorem density_dyadic_log_bound (N j : ℕ) (hN : 1 ≤ N) :
    1 + Real.log ((2 : ℝ) ^ (j + 1) * N) ≤
      (j + 2 : ℝ) * (1 + Real.log N) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hNl : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  rw [Real.log_mul (by positivity) hNp.ne', Real.log_pow]
  have htwo : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  push_cast
  nlinarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityDyadicMean
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Decaying mean squares for the actual distant dyadic blocks -/

namespace Ostmann

open Complex MeasureTheory Set
open scoped BigOperators Classical

 theorem densityFiniteSquare_dyadic_mean :
    ∃ C : ℝ, 0 < C ∧ ∀ N Q : ℕ, 1 ≤ N → 1 ≤ Q → ∀ T : ℝ, 1 ≤ T →
      10 * (Q : ℝ) * T ≤ N → ∀ j : ℕ,
      ∀ F : Finset PrimitiveComplexCharacter, (∀ χ ∈ F, χ.modulus ≤ Q) →
      (∑ χ ∈ F, ∫ t in Icc (-T) T,
        ‖∑ n ∈ Finset.Ioc (2 ^ j * N) (2 ^ (j + 1) * N),
          densitySquareIntegralTerm χ (densityVerticalPoint (1 / 2) t) n‖ ^ 2) ≤
          C * ((N : ℝ) + (Q : ℝ) ^ 2 * T) * (1 + Real.log N) ^ 3 *
            (j + 2 : ℝ) ^ 3 / (2 : ℝ) ^ j := by
  obtain ⟨C, hC, hb⟩ := densityFiniteSquare_tail_mean
  refine ⟨4 * C, by positivity, ?_⟩
  intro N Q hN hQ T hT hscale j F hF
  have hM : 1 ≤ 2 ^ j * N := one_le_mul (by exact_mod_cast (one_le_pow₀ (by norm_num : 1 ≤ (2 : ℕ)) : 1 ≤ (2 : ℕ) ^ j)) hN
  have hS : Finset.Ioc (2 ^ j * N) (2 ^ (j + 1) * N) ⊆
      Finset.Icc (2 ^ j * N) (2 ^ (j + 1) * N) := by
    intro n hn
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Ioc.mp hn).1.le, (Finset.mem_Ioc.mp hn).2⟩
  have h := hb (2 ^ j * N) (2 ^ (j + 1) * N) Q hM hQ T hT
    (Finset.Ioc (2 ^ j * N) (2 ^ (j + 1) * N)) hS F hF
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hr : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
  have hNl : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  have hlog0 : 0 ≤ 1 + Real.log ((2 : ℝ) ^ (j + 1) * N) := by
    apply le_trans (by norm_num : (0 : ℝ) ≤ 1) (le_add_of_nonneg_right _)
    apply Real.log_nonneg
    have hp : (1 : ℝ) ≤ 2 ^ (j + 1) := one_le_pow₀ (by norm_num)
    have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
    nlinarith
  have hlog := pow_le_pow_left₀ hlog0 (density_dyadic_log_bound N j hN) 3
  have hend : (2 : ℝ) ^ (j + 1) * N = 2 * (2 : ℝ) ^ j * N := by rw [pow_succ]; ring
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at h
  calc
    _ ≤ C * ((10 * (Q : ℝ) * T) ^ 2 *
        ((2 : ℝ) ^ (j + 1) * N + (Q : ℝ) ^ 2 * T) *
          (((2 : ℝ) ^ (j + 1) * N) * (1 + Real.log ((2 : ℝ) ^ (j + 1) * N)) ^ 3 /
            ((2 : ℝ) ^ j * N) ^ 3)) := by
      convert h using 1
      all_goals try with_reducible_and_instances rfl
      ring
    _ ≤ C * (4 * ((N : ℝ) + (Q : ℝ) ^ 2 * T) *
        (1 + Real.log ((2 : ℝ) ^ (j + 1) * N)) ^ 3 / (2 : ℝ) ^ j) := by
      apply mul_le_mul_of_nonneg_left _ hC.le
      rw [hend]
      exact density_dyadic_fraction_bound _ _ _ _ _ (by positivity) hscale hNp
        (by positivity) hr (by simpa only [hend] using hlog0)
    _ ≤ C * (4 * ((N : ℝ) + (Q : ℝ) ^ 2 * T) *
        (((j + 2 : ℝ) * (1 + Real.log N)) ^ 3) / (2 : ℝ) ^ j) := by
      apply mul_le_mul_of_nonneg_left _ hC.le
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hlog (by positivity)) (by positivity)
    _ = _ := by ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityBlockWeights
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Summable weights for the actual dyadic-square estimates -/

namespace Ostmann

open scoped BigOperators

 theorem density_block_weight_sum (J : ℕ) :
    (∑ j ∈ Finset.range J, (3 / 4 : ℝ) ^ j) ≤ 4 := by
  have h := (summable_geometric_of_abs_lt_one (by norm_num : |(3 / 4 : ℝ)| < 1)).sum_le_tsum
    (Finset.range J) (fun _ _ => by positivity)
  have he : (∑' j : ℕ, (3 / 4 : ℝ) ^ j) = 4 := by
    rw [tsum_geometric_of_abs_lt_one (by norm_num : |(3 / 4 : ℝ)| < 1)]
    norm_num
  exact h.trans_eq he

 theorem density_block_energy_summable :
    Summable (fun j : ℕ => (j + 2 : ℝ) ^ 3 * (2 / 3 : ℝ) ^ j) := by
  have h3 := summable_pow_mul_geometric_of_norm_lt_one 3 (by norm_num : ‖(2 / 3 : ℝ)‖ < 1)
  have h2 := summable_pow_mul_geometric_of_norm_lt_one 2 (by norm_num : ‖(2 / 3 : ℝ)‖ < 1)
  have h1 := summable_pow_mul_geometric_of_norm_lt_one 1 (by norm_num : ‖(2 / 3 : ℝ)‖ < 1)
  have h0 := summable_geometric_of_abs_lt_one (by norm_num : |(2 / 3 : ℝ)| < 1)
  convert ((h3.add (h2.mul_left 6)).add (h1.mul_left 12)).add (h0.mul_left 8) using 1
  all_goals try with_reducible_and_instances rfl
  funext j
  ring

 theorem densityBlockEnergyConstant_pos : 0 < densityBlockEnergyConstant := by
  unfold densityBlockEnergyConstant
  have h := density_block_energy_summable.le_tsum 0 (fun _ _ => by positivity)
  norm_num at h
  linarith

 theorem density_block_energy_sum (J : ℕ) :
    (∑ j ∈ Finset.range J, ((j + 2 : ℝ) ^ 3 / (2 : ℝ) ^ j) / (3 / 4 : ℝ) ^ j) ≤
      densityBlockEnergyConstant := by
  have he (j : ℕ) : ((j + 2 : ℝ) ^ 3 / (2 : ℝ) ^ j) / (3 / 4 : ℝ) ^ j =
      (j + 2 : ℝ) ^ 3 * (2 / 3 : ℝ) ^ j := by
    rw [div_div, ← mul_pow]
    have hmul : (2 : ℝ) * (3 / 4) = 3 / 2 := by norm_num
    rw [hmul, div_eq_mul_inv, ← inv_pow]
    norm_num
  simp_rw [he]
  exact density_block_energy_summable.sum_le_tsum (Finset.range J) (fun _ _ => by positivity)

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
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityFatou
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Passing a uniform positive mean bound to the actual series limit -/

namespace Ostmann

open Filter MeasureTheory
open scoped Topology

 theorem density_integral_limit_bound (g : ℕ → ℝ → ℝ) (f : ℝ → ℝ)
    (μ : Measure ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hg : ∀ n, Integrable (g n) μ) (hg0 : ∀ n t, 0 ≤ g n t)
    (hf : ∀ t, Tendsto (fun n => g n t) atTop (𝓝 (f t)))
    (hb : ∀ n, ∫ t, g n t ∂μ ≤ B) :
    Integrable f μ ∧ (∫ t, f t ∂μ) ≤ B := by
  have hf0 (t : ℝ) : 0 ≤ f t := ge_of_tendsto (hf t) (Filter.Eventually.of_forall (fun n => hg0 n t))
  have hfn : ∀ᵐ t ∂μ, Tendsto (fun n => g n t) atTop (𝓝 (f t)) := Filter.Eventually.of_forall hf
  have hn (n : ℕ) : (∫⁻ t, ‖g n t‖ₑ ∂μ) = ENNReal.ofReal (∫ t, g n t ∂μ) := by
    simp_rw [Real.enorm_eq_ofReal (hg0 n _)]
    exact (ofReal_integral_eq_lintegral_ofReal (hg n) (Filter.Eventually.of_forall (hg0 n))).symm
  have hlim : Filter.liminf (fun n => ∫⁻ t, ‖g n t‖ₑ ∂μ) atTop ≤ ENNReal.ofReal B := by
    apply liminf_le_of_frequently_le'
    exact Filter.Eventually.frequently (Filter.Eventually.of_forall (fun n => by
      rw [hn n]
      exact ENNReal.ofReal_le_ofReal (hb n)))
  have hint : Integrable f μ := integrable_of_tendsto hfn (fun n => (hg n).aestronglyMeasurable)
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hlim)
  refine ⟨hint, ?_⟩
  have hfat := (lintegral_enorm_le_liminf_of_tendsto hfn
    (fun n => (hg n).aestronglyMeasurable.aemeasurable.enorm)).trans hlim
  simp_rw [Real.enorm_eq_ofReal (hf0 _)] at hfat
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall hf0)] at hfat
  exact (ENNReal.ofReal_le_ofReal_iff hB).mp hfat

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityHeadCutoff
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The logarithmic short contour for the actual finite head -/

namespace Ostmann

open Complex MeasureTheory Set
open scoped BigOperators Classical

 theorem densityKernelCost_log (N Q : ℕ) (hQ : 1 ≤ Q) (T : ℝ) (hT : 1 ≤ T)
    (hN : 1 ≤ Real.log N) (hscale : 10 * (Q : ℝ) * T ≤ N) :
    densityKernelCost Q T (1 / Real.log N) ≤
      densityKernelConstant * Real.exp 1 * Real.log N := by
  have hNp : (0 : ℝ) < N := by
    have hq : (0 : ℝ) < Q := by exact_mod_cast (show 0 < Q by omega)
    have hB : 0 < 10 * (Q : ℝ) * T := by positivity
    exact hB.trans_le hscale
  have hc : 0 < 1 / Real.log N := div_pos zero_lt_one (by linarith)
  have hpow : (N : ℝ) ^ (1 / Real.log N) = Real.exp 1 := by
    rw [Real.rpow_def_of_pos hNp]
    congr 1
    field_simp
  unfold densityKernelCost
  calc
    _ ≤ densityKernelConstant * (N : ℝ) ^ (1 / Real.log N) / (1 / Real.log N) := by
      apply div_le_div_of_nonneg_right _ hc.le
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (by positivity) hscale hc.le) densityKernelConstant_pos.le
    _ = _ := by rw [hpow]; field_simp

 theorem densityFiniteSquare_head_mean :
    ∃ C : ℝ, 0 < C ∧ ∀ N Q : ℕ, 1 ≤ Q → ∀ T : ℝ, 1 ≤ T →
      1 ≤ Real.log N → 10 * (Q : ℝ) * T ≤ N →
      ∀ F : Finset PrimitiveComplexCharacter, (∀ χ ∈ F, χ.modulus ≤ Q) →
      (∑ χ ∈ F, ∫ t in Icc (-T) T,
        ‖∑ n ∈ Finset.Icc 1 N,
          densitySquareIntegralTerm χ (densityVerticalPoint (1 / 2) t) n‖ ^ 2) ≤
          C * ((N : ℝ) + (Q : ℝ) ^ 2 * T) * (Real.log N) ^ 6 := by
  obtain ⟨C, hC, hb⟩ := densityFiniteSquare_mean
  refine ⟨16 * C * (densityKernelConstant * Real.exp 1) ^ 2, by
    have := densityKernelConstant_pos
    positivity, ?_⟩
  intro N Q hQ T hT hN hscale F hF
  let c : ℝ := 1 / Real.log N
  have hc : 0 < c := div_pos zero_lt_one (by linarith)
  have hc1 : c ≤ 1 := by dsimp [c]; exact (div_le_one (by linarith)).mpr hN
  have h := hb N Q hQ T c hT hc hc1 (Finset.Icc 1 N) (fun _ hn => hn) F hF
  have he := density_divisor_shifted_head N c hc.le
  have hk := densityKernelCost_log N Q hQ T hT hN hscale
  have hlog : (1 + Real.log N) ^ 4 ≤ 16 * (Real.log N) ^ 4 := by
    have h := pow_le_pow_left₀ (by linarith : 0 ≤ 1 + Real.log N)
      (by linarith : 1 + Real.log N ≤ 2 * Real.log N) 4
    nlinarith
  calc
    _ ≤ C * (densityKernelCost Q T c) ^ 2 * ((N : ℝ) + (Q : ℝ) ^ 2 * T) *
        (1 + Real.log N) ^ 4 := h.trans (mul_le_mul_of_nonneg_left he (by positivity))
    _ ≤ C * (densityKernelConstant * Real.exp 1 * Real.log N) ^ 2 *
        ((N : ℝ) + (Q : ℝ) ^ 2 * T) * (16 * (Real.log N) ^ 4) := by
      apply mul_le_mul _ hlog (by positivity) (by positivity)
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (densityKernelCost_pos Q hQ T c hT hc).le hk 2) hC.le
    _ = _ := by ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityTailAssembly
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A uniform mean square for every finite dyadic tail -/

namespace Ostmann

open Complex MeasureTheory Set
open scoped BigOperators Classical

 theorem densityFiniteSquare_tail_assembly :
    ∃ C : ℝ, 0 < C ∧ ∀ N Q : ℕ, 1 ≤ N → 1 ≤ Q → ∀ T : ℝ, 1 ≤ T →
      10 * (Q : ℝ) * T ≤ N → ∀ J : ℕ,
      ∀ F : Finset PrimitiveComplexCharacter, (∀ χ ∈ F, χ.modulus ≤ Q) →
      (∑ χ ∈ F, ∫ t in Icc (-T) T,
        ‖∑ j ∈ Finset.range J, ∑ n ∈ Finset.Ioc (2 ^ j * N) (2 ^ (j + 1) * N),
          densitySquareIntegralTerm χ (densityVerticalPoint (1 / 2) t) n‖ ^ 2) ≤
          C * ((N : ℝ) + (Q : ℝ) ^ 2 * T) * (1 + Real.log N) ^ 3 := by
  obtain ⟨C, hC, hb⟩ := densityFiniteSquare_dyadic_mean
  refine ⟨4 * C * densityBlockEnergyConstant, by
    have := densityBlockEnergyConstant_pos
    positivity, ?_⟩
  intro N Q hN hQ T hT hscale J F hF
  let K := ((N : ℝ) + (Q : ℝ) ^ 2 * T) * (1 + Real.log N) ^ 3
  have hK : 0 ≤ K := by
    have hNl := Real.log_nonneg (show (1 : ℝ) ≤ N by exact_mod_cast hN)
    dsimp [K]
    positivity
  let f := fun (χ : PrimitiveComplexCharacter) (j : ℕ) (t : ℝ) =>
    ∑ n ∈ Finset.Ioc (2 ^ j * N) (2 ^ (j + 1) * N),
      densitySquareIntegralTerm χ (densityVerticalPoint (1 / 2) t) n
  have hf (χ : PrimitiveComplexCharacter) (j : ℕ) : ContinuousOn (f χ j) (Icc (-T) T) := by
    apply densityFiniteSquare_continuousOn χ _ _ T hT
    intro n hn
    have hnp : 0 < n := lt_of_le_of_lt (Nat.zero_le _) (Finset.mem_Ioc.mp hn).1
    omega
  have hs : (∑ j ∈ Finset.range J,
      (∑ χ ∈ F, ∫ t in Icc (-T) T, ‖f χ j t‖ ^ 2) / (3 / 4 : ℝ) ^ j) ≤
      C * K * densityBlockEnergyConstant := by
    calc
      _ ≤ ∑ j ∈ Finset.range J,
          (C * K * (j + 2 : ℝ) ^ 3 / (2 : ℝ) ^ j) / (3 / 4 : ℝ) ^ j := by
        apply Finset.sum_le_sum
        intro j _
        have hj : (∑ χ ∈ F, ∫ t in Icc (-T) T, ‖f χ j t‖ ^ 2) ≤
            C * K * (j + 2 : ℝ) ^ 3 / (2 : ℝ) ^ j := by
          simpa only [f, K, mul_assoc] using hb N Q hN hQ T hT hscale j F hF
        exact div_le_div_of_nonneg_right hj (by positivity)
      _ = C * K * ∑ j ∈ Finset.range J,
          ((j + 2 : ℝ) ^ 3 / (2 : ℝ) ^ j) / (3 / 4 : ℝ) ^ j := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (density_block_energy_sum J) (mul_nonneg hC.le hK)
  have h := density_weighted_block_mean F (Finset.range J) f (fun j => (3 / 4 : ℝ) ^ j)
    (fun j _ => by positivity) T (fun χ _ j _ => hf χ j)
  apply h.trans
  calc
    _ ≤ (∑ j ∈ Finset.range J, (3 / 4 : ℝ) ^ j) * (C * K * densityBlockEnergyConstant) :=
      mul_le_mul_of_nonneg_left hs (Finset.sum_nonneg (fun _ _ => by positivity))
    _ ≤ 4 * (C * K * densityBlockEnergyConstant) :=
      mul_le_mul_of_nonneg_right (density_block_weight_sum J)
        (mul_nonneg (mul_nonneg hC.le hK) densityBlockEnergyConstant_pos.le)
    _ = _ := by dsimp [K]; ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityPartialMean
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A uniform sixth-log bound for all growing partial smoothed squares -/

namespace Ostmann

open Complex MeasureTheory Set
open scoped BigOperators Classical

 theorem densityFiniteSquare_partial_mean :
    ∃ C : ℝ, 0 < C ∧ ∀ N Q : ℕ, 1 ≤ N → 1 ≤ Q → ∀ T : ℝ,
      1 ≤ T → 1 ≤ Real.log N → 10 * (Q : ℝ) * T ≤ N → ∀ J : ℕ,
      ∀ F : Finset PrimitiveComplexCharacter, (∀ χ ∈ F, χ.modulus ≤ Q) →
      (∑ χ ∈ F, ∫ t in Icc (-T) T,
        ‖∑ n ∈ Finset.Icc 1 (2 ^ J * N),
          densitySquareIntegralTerm χ (densityVerticalPoint (1 / 2) t) n‖ ^ 2) ≤
          C * ((N : ℝ) + (Q : ℝ) ^ 2 * T) * (Real.log N) ^ 6 := by
  obtain ⟨CH, hCH, hhead⟩ := densityFiniteSquare_head_mean
  obtain ⟨CT, hCT, htail⟩ := densityFiniteSquare_tail_assembly
  refine ⟨2 * CH + 16 * CT, by positivity, ?_⟩
  intro N Q hN hQ T hT hL hscale J F hF
  let H := fun (χ : PrimitiveComplexCharacter) (t : ℝ) =>
    ∑ n ∈ Finset.Icc 1 N, densitySquareIntegralTerm χ (densityVerticalPoint (1 / 2) t) n
  let R := fun (χ : PrimitiveComplexCharacter) (t : ℝ) =>
    ∑ j ∈ Finset.range J, ∑ n ∈ Finset.Ioc (2 ^ j * N) (2 ^ (j + 1) * N),
      densitySquareIntegralTerm χ (densityVerticalPoint (1 / 2) t) n
  have hH (χ : PrimitiveComplexCharacter) : ContinuousOn (H χ) (Icc (-T) T) :=
    densityFiniteSquare_continuousOn χ _ (fun n hn => (Finset.mem_Icc.mp hn).1) T hT
  have hR (χ : PrimitiveComplexCharacter) : ContinuousOn (R χ) (Icc (-T) T) := by
    apply continuousOn_finsetSum
    intro j _
    apply densityFiniteSquare_continuousOn χ _ _ T hT
    intro n hn
    have hn' := (Finset.mem_Ioc.mp hn).1
    omega
  have hpoint (χ : PrimitiveComplexCharacter) (t : ℝ) :
      ‖H χ t + R χ t‖ ^ 2 ≤ 2 * ‖H χ t‖ ^ 2 + 2 * ‖R χ t‖ ^ 2 := by
    have h := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le (H χ t) (R χ t)) 2
    nlinarith [sq_nonneg (‖H χ t‖ - ‖R χ t‖)]
  have hm (χ : PrimitiveComplexCharacter) :
      (∫ t in Icc (-T) T, ‖H χ t + R χ t‖ ^ 2) ≤
        2 * (∫ t in Icc (-T) T, ‖H χ t‖ ^ 2) +
          2 * (∫ t in Icc (-T) T, ‖R χ t‖ ^ 2) := by
    have hh : Integrable (fun t => ‖H χ t‖ ^ 2) (volume.restrict (Icc (-T) T)) :=
      ((hH χ).norm.pow 2).integrableOn_Icc
    have hr : Integrable (fun t => ‖R χ t‖ ^ 2) (volume.restrict (Icc (-T) T)) :=
      ((hR χ).norm.pow 2).integrableOn_Icc
    have hi := (hh.const_mul 2).add (hr.const_mul 2)
    have hb := integral_mono (((hH χ).add (hR χ)).norm.pow 2).integrableOn_Icc hi (hpoint χ)
    simp only [Pi.add_apply, Pi.pow_apply] at hb
    have hadd := integral_add (hh.const_mul 2) (hr.const_mul 2)
    rw [hadd, integral_const_mul, integral_const_mul] at hb
    exact hb
  have hlog : (1 + Real.log N) ^ 3 ≤ 8 * (Real.log N) ^ 6 := by
    have hbase : 1 + Real.log N ≤ 2 * (Real.log N) ^ 2 := by nlinarith
    have h := pow_le_pow_left₀ (by linarith : 0 ≤ 1 + Real.log N) hbase 3
    nlinarith
  calc
    _ = ∑ χ ∈ F, ∫ t in Icc (-T) T, ‖H χ t + R χ t‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro χ _
      apply integral_congr_ae
      filter_upwards with t
      rw [density_dyadic_partition N J hN]
    _ ≤ ∑ χ ∈ F, (2 * (∫ t in Icc (-T) T, ‖H χ t‖ ^ 2) +
        2 * (∫ t in Icc (-T) T, ‖R χ t‖ ^ 2)) := Finset.sum_le_sum (fun χ _ => hm χ)
    _ = 2 * (∑ χ ∈ F, ∫ t in Icc (-T) T, ‖H χ t‖ ^ 2) +
        2 * (∑ χ ∈ F, ∫ t in Icc (-T) T, ‖R χ t‖ ^ 2) := by
      simp only [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ 2 * (CH * ((N : ℝ) + (Q : ℝ) ^ 2 * T) * (Real.log N) ^ 6) +
        2 * (CT * ((N : ℝ) + (Q : ℝ) ^ 2 * T) * (1 + Real.log N) ^ 3) := by
      exact add_le_add (mul_le_mul_of_nonneg_left (hhead N Q hQ T hT hL hscale F hF) (by norm_num))
        (mul_le_mul_of_nonneg_left (htail N Q hN hQ T hT hscale J F hF) (by norm_num))
    _ ≤ _ := by
      have hb := mul_le_mul_of_nonneg_left hlog
        (show 0 ≤ 2 * CT * ((N : ℝ) + (Q : ℝ) ^ 2 * T) by positivity)
      nlinarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensitySquareLimit
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Convergence of the growing original square sums -/

namespace Ostmann

open Complex MeasureTheory Filter
open scoped BigOperators Topology Classical

 theorem densitySquareIntegralTerm_summable (χ : PrimitiveComplexCharacter) (s : ℂ)
    (hs : s.re = 1 / 2) : Summable (densitySquareIntegralTerm χ s) := by
  have h := hasSum_integral_of_summable_integral_norm
    (fun n => densitySquareSeriesTerm_integrable χ s hs n)
    (densitySquareSeriesTerm_integral_summable χ s hs)
  exact h.summable.mul_left (2 * (Real.pi : ℂ))⁻¹

 theorem densitySquare_partial_limit (χ : PrimitiveComplexCharacter) (N : ℕ) (hN : 1 ≤ N)
    (t : ℝ) :
    Tendsto (fun J : ℕ => ∑ n ∈ Finset.Icc 1 (2 ^ J * N),
      densitySquareIntegralTerm χ (densityVerticalPoint (1 / 2) t) n) atTop
        (𝓝 (densitySmoothedSquare χ (densityVerticalPoint (1 / 2) t))) := by
  let s := densityVerticalPoint (1 / 2) t
  have hs : s.re = 1 / 2 := by simp [s, densityVerticalPoint]
  have hc : Tendsto (fun J : ℕ => 2 ^ J * N + 1) atTop atTop := by
    apply tendsto_atTop_mono _ (tendsto_pow_atTop_atTop_of_one_lt (by decide : 1 < (2 : ℕ)))
    intro J
    have h := Nat.le_mul_of_pos_right (2 ^ J) (by omega : 0 < N)
    omega
  have he (K : ℕ) : (∑ n ∈ Finset.Icc 1 K, densitySquareIntegralTerm χ s n) =
      ∑ n ∈ Finset.range (K + 1), densitySquareIntegralTerm χ s n := by
    apply Finset.sum_subset
    · intro n hn
      exact Finset.mem_range.mpr (by have := (Finset.mem_Icc.mp hn).2; omega)
    · intro n hn hnot
      have hn' := Finset.mem_range.mp hn
      have hzero : n = 0 := by
        by_contra hz
        exact hnot (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
      simp [hzero]
  have h := ((densitySquareIntegralTerm_summable χ s hs).hasSum.tendsto_sum_nat).comp hc
  rw [← densitySmoothedSquare_series χ s hs] at h
  change Tendsto (fun J => ∑ n ∈ Finset.range (2 ^ J * N + 1), densitySquareIntegralTerm χ s n)
    atTop (𝓝 (densitySmoothedSquare χ s)) at h
  exact h.congr' (Filter.Eventually.of_forall (fun J => (he (2 ^ J * N)).symm))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensitySmoothedMean
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual smoothed square satisfies the sixth-log mean bound -/

namespace Ostmann

open Complex MeasureTheory Filter Set
open scoped BigOperators Topology Classical

 theorem densitySmoothedSquare_mean_oai :
    ∃ C : ℝ, 0 < C ∧ ∀ N Q : ℕ, 1 ≤ N → 1 ≤ Q → ∀ T : ℝ,
      1 ≤ T → 1 ≤ Real.log N → 10 * (Q : ℝ) * T ≤ N →
      ∀ F : Finset PrimitiveComplexCharacter, (∀ χ ∈ F, χ.modulus ≤ Q) →
      (∀ χ ∈ F, Integrable (fun t =>
        ‖densitySmoothedSquare χ (densityVerticalPoint (1 / 2) t)‖ ^ 2)
          (volume.restrict (Icc (-T) T))) ∧
      (∑ χ ∈ F, ∫ t in Icc (-T) T,
        ‖densitySmoothedSquare χ (densityVerticalPoint (1 / 2) t)‖ ^ 2) ≤
          C * ((N : ℝ) + (Q : ℝ) ^ 2 * T) * (Real.log N) ^ 6 := by
  obtain ⟨C, hC, hb⟩ := densityFiniteSquare_partial_mean
  refine ⟨C, hC, ?_⟩
  intro N Q hN hQ T hT hL hscale F hF
  let p := fun (J : ℕ) (χ : PrimitiveComplexCharacter) (t : ℝ) =>
    ‖∑ n ∈ Finset.Icc 1 (2 ^ J * N),
      densitySquareIntegralTerm χ (densityVerticalPoint (1 / 2) t) n‖ ^ 2
  let f := fun (χ : PrimitiveComplexCharacter) (t : ℝ) =>
    ‖densitySmoothedSquare χ (densityVerticalPoint (1 / 2) t)‖ ^ 2
  have hp (J : ℕ) (χ : PrimitiveComplexCharacter) :
      Integrable (p J χ) (volume.restrict (Icc (-T) T)) :=
    ((densityFiniteSquare_continuousOn χ _ (fun n hn => (Finset.mem_Icc.mp hn).1) T hT).norm.pow 2).integrableOn_Icc
  have ht (χ : PrimitiveComplexCharacter) (t : ℝ) :
      Tendsto (fun J => p J χ t) atTop (𝓝 (f χ t)) :=
    ((densitySquare_partial_limit χ N hN t).norm).pow 2
  have hsum : Integrable (fun t => ∑ χ ∈ F, f χ t) (volume.restrict (Icc (-T) T)) ∧
      (∫ t in Icc (-T) T, ∑ χ ∈ F, f χ t) ≤
        C * ((N : ℝ) + (Q : ℝ) ^ 2 * T) * (Real.log N) ^ 6 := by
    apply density_integral_limit_bound (fun J t => ∑ χ ∈ F, p J χ t)
      (fun t => ∑ χ ∈ F, f χ t) _ _ (by positivity)
    · intro J
      exact integrable_finsetSum F (fun χ _ => hp J χ)
    · intro J t
      exact Finset.sum_nonneg (fun χ _ => sq_nonneg _)
    · intro t
      exact tendsto_finsetSum F (fun χ _ => ht χ t)
    · intro J
      rw [integral_finsetSum F (fun χ _ => hp J χ)]
      exact hb N Q hN hQ T hT hL hscale J F hF
  have hi (χ : PrimitiveComplexCharacter) (hχ : χ ∈ F) :
      Integrable (f χ) (volume.restrict (Icc (-T) T)) := by
    apply hsum.1.mono'
    · exact aestronglyMeasurable_of_tendsto_ae atTop (fun J => (hp J χ).aestronglyMeasurable)
        (Filter.Eventually.of_forall (ht χ))
    · filter_upwards with t
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact Finset.single_le_sum (f := fun ψ => f ψ t) (fun ψ _ => sq_nonneg _) hχ
  refine ⟨hi, ?_⟩
  simpa only [integral_finsetSum F hi] using hsum.2

end Ostmann

end OAI
end

theorem solution : type_of% @OAI.Ostmann.densitySmoothedSquare_mean_oai := @OAI.Ostmann.densitySmoothedSquare_mean_oai
