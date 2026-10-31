-- Prove2me | solution 1 for OAI.Ostmann.sparse_finite_contraction
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T07:19:40.05814+00:00
-- url     : https://prove2.me/submissions/c1614d82-984b-48a7-806a-ca1a8dbe81f6

import Mathlib
import Definitions.Def_OAIQ095D007

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_AdditiveFourier
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
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

/-- Additive Parseval with the manuscript's probability convention. -/
theorem additiveFourier_parseval {p : ℕ} [NeZero p] (f : ZMod p → ℂ) :
    (∑ a : ZMod p, ‖additiveFourier f a‖ ^ 2) =
      (p : ℝ)⁻¹ * ∑ x : ZMod p, ‖f x‖ ^ 2 := by
  rw [additiveFourier_energy f]
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne p
  rw [← mul_assoc, inv_mul_cancel₀ hp, one_mul]

theorem additiveFourier_sub {p : ℕ} [NeZero p]
    (f g : ZMod p → ℂ) (a : ZMod p) :
    additiveFourier (fun x => f x - g x) a = additiveFourier f a - additiveFourier g a := by
  simp only [additiveFourier_apply, sub_mul, Finset.sum_sub_distrib, mul_sub]

theorem additiveFourier_const {p : ℕ} [NeZero p] (c : ℂ) (a : ZMod p) :
    additiveFourier (fun _ : ZMod p => c) a = if a = 0 then c else 0 := by
  classical
  have hp : (p : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne p
  rw [additiveFourier_apply]
  simp only [← mul_neg, ← Finset.mul_sum]
  rw [AddChar.sum_mulShift (-a) (ZMod.isPrimitive_stdAddChar p)]
  simp only [ZMod.card, neg_eq_zero]
  by_cases ha : a = 0
  · simp only [ha, ite_true, if_true]
    field_simp
  · simp only [ha, ite_false, if_false, Nat.cast_zero, mul_zero]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_Autocorrelation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Additive autocorrelation

The probability-normalized Fourier transform of an autocorrelation is
the squared modulus of the original transform. This is the positivity
identity used for the bottom-pair coefficients in Section 6.
-/

namespace Ostmann

open scoped BigOperators ComplexConjugate

theorem additiveFourier_translation_sum {p : ℕ} [NeZero p]
    (g : ZMod p → ℂ) (a y : ZMod p) :
    (∑ x : ZMod p, g (x - y) * ZMod.stdAddChar (-(x * a))) =
      ZMod.stdAddChar (-(y * a)) * ∑ z : ZMod p, g z * ZMod.stdAddChar (-(z * a)) := by
  calc
    _ = ∑ z : ZMod p, g ((z + y) - y) * ZMod.stdAddChar (-((z + y) * a)) :=
      ((Equiv.addRight y).bijective.sum_comp
        (fun x : ZMod p => g (x - y) * ZMod.stdAddChar (-(x * a)))).symm
    _ = _ := by
      simp only [add_sub_cancel_right, add_mul, neg_add, AddChar.map_add_eq_mul]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      ring

theorem additiveFourier_convolution {p : ℕ} [NeZero p]
    (f g : ZMod p → ℂ) (a : ZMod p) :
    additiveFourier (additiveConvolution f g) a =
      additiveFourier f a * additiveFourier g a := by
  simp only [additiveFourier_apply, additiveConvolution]
  calc
    _ = (p : ℂ)⁻¹ * (p : ℂ)⁻¹ *
        ∑ y : ZMod p, f y * ∑ x : ZMod p, g (x - y) * ZMod.stdAddChar (-(x * a)) := by
      simp only [Finset.sum_mul, Finset.mul_sum, mul_assoc]
      rw [Finset.sum_comm]
    _ = _ := by
      simp_rw [additiveFourier_translation_sum]
      simp_rw [← mul_assoc]
      rw [← Finset.sum_mul]
      ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_AffineAction
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Identifying the Fourier matrix of the affine action

The finite matrix from `AffineFourier` is the action of
`F(t) ↦ ∑ c(a,b) F(at+b)` on nonzero additive frequencies.
-/

namespace Ostmann

open scoped BigOperators

theorem additiveFourier_const_mul {p : ℕ} [NeZero p]
    (c : ℂ) (f : ZMod p → ℂ) (a : ZMod p) :
    additiveFourier (fun x => c * f x) a = c * additiveFourier f a := by
  simp only [additiveFourier_apply, mul_assoc]
  rw [← Finset.mul_sum]
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_SymmetricBlockEnergy
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The numerical two-block estimate used in Lemma 5.2 -/

namespace Ostmann

/-- A gap of `1/20` in the second diagonal block means that off-diagonal
size `r` costs only `20*r^2` in the operator bound. -/
theorem symmetric_block_energy (s d r x y : ℝ) (hs : 0 ≤ s) (hd : 0 ≤ d)
    (hgap : d + 1 / 20 ≤ s) :
    (s * x + r * y) ^ 2 + (r * x + d * y) ^ 2 ≤
      (s + 20 * r ^ 2) ^ 2 * (x ^ 2 + y ^ 2) := by
  let M := s + 20 * r ^ 2
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hrow1 : (s * x + r * y) ^ 2 ≤ M * (s * x ^ 2 + y ^ 2 / 20) := by
    have he : M * (s * x ^ 2 + y ^ 2 / 20) - (s * x + r * y) ^ 2 =
        s / 20 * (20 * r * x - y) ^ 2 := by dsimp [M]; ring
    have hn : 0 ≤ s / 20 * (20 * r * x - y) ^ 2 := mul_nonneg (by positivity) (sq_nonneg _)
    linarith
  have hrow2 : (r * x + d * y) ^ 2 ≤
      (d + 1 / 20) * (20 * r ^ 2 * x ^ 2 + d * y ^ 2) := by
    have he : (d + 1 / 20) * (20 * r ^ 2 * x ^ 2 + d * y ^ 2) -
        (r * x + d * y) ^ 2 = d / 20 * (20 * r * x - y) ^ 2 := by ring
    have hn : 0 ≤ d / 20 * (20 * r * x - y) ^ 2 := mul_nonneg (by positivity) (sq_nonneg _)
    linarith
  have hrow2' : (r * x + d * y) ^ 2 ≤ M * (20 * r ^ 2 * x ^ 2 + d * y ^ 2) :=
    hrow2.trans (mul_le_mul_of_nonneg_right (by change d + 1 / 20 ≤ s + 20 * r ^ 2; nlinarith [sq_nonneg r])
      (by positivity))
  have hfinal : M * (s * x ^ 2 + y ^ 2 / 20) +
      M * (20 * r ^ 2 * x ^ 2 + d * y ^ 2) ≤ M ^ 2 * (x ^ 2 + y ^ 2) := by
    have hy := mul_le_mul_of_nonneg_right (hgap.trans (by change s ≤ s + 20 * r ^ 2; nlinarith [sq_nonneg r]))
      (sq_nonneg y)
    have hh := mul_le_mul_of_nonneg_left hy hM
    dsimp [M] at *
    nlinarith only [hh]
  exact (add_le_add hrow1 hrow2').trans hfinal

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_GaussFourier
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Additive Fourier coefficients of multiplicative characters

The Gauss identity already proved in Mathlib gives the exact normalized
squared modulus needed for the two-bad quartet estimate in Section 6.
-/

namespace Ostmann

open scoped BigOperators ComplexConjugate

/-- The Fourier transform exchanges pointwise multiplication and convolution. -/
theorem additiveFourier_pointwise_mul {p : ℕ} [NeZero p]
    (f g : ZMod p → ℂ) (a : ZMod p) :
    additiveFourier (fun x => f x * g x) a =
      ∑ b : ZMod p, additiveFourier f b * additiveFourier g (a - b) := by
  rw [additiveFourier_apply]
  conv_lhs =>
    enter [2, 2, x]
    rw [additiveFourier_inversion f x]
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [additiveFourier_apply g (a - b)]
  simp only [Finset.mul_sum]
  have hphase (x : ZMod p) :
      ZMod.stdAddChar (b * x) * ZMod.stdAddChar (-(x * a)) =
        ZMod.stdAddChar (-(x * (a - b))) := by
    rw [← AddChar.map_add_eq_mul]
    congr 1
    ring
  apply Finset.sum_congr rfl
  intro x _
  calc
    _ = (p : ℂ)⁻¹ * additiveFourier f b * g x *
        (ZMod.stdAddChar (b * x) * ZMod.stdAddChar (-(x * a))) := by ring
    _ = _ := by rw [hphase]; ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_MixedFourier
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Symmetries of the mixed Fourier bound

Conjugation and multiplication of the field argument by a unit preserve
both the energy hypothesis and the mixed character/Fourier bound. These
are the orientation changes used by the bottom pairs.
-/

namespace Ostmann

open scoped BigOperators ComplexConjugate

theorem additiveFourier_conj {p : ℕ} [NeZero p]
    (f : ZMod p → ℂ) (a : ZMod p) :
    additiveFourier (fun x => conj (f x)) a = conj (additiveFourier f (-a)) := by
  simp only [additiveFourier_apply, map_mul, map_inv₀, map_natCast, map_sum,
    stdAddChar_conj, mul_neg, neg_neg]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityFourier
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The normalized Fourier transform of the actual centered density -/

namespace Ostmann

open scoped BigOperators

theorem densityFourier_energy {q : ℕ} [NeZero q] (f : ZMod q → ℂ) :
    (∑ a : ZMod q, ‖densityFourier f a‖ ^ 2) = ∑ x : ZMod q, ‖f x‖ ^ 2 := by
  have hq : (q : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne q
  simp only [densityFourier, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt (Nat.cast_nonneg q)]
  rw [← Finset.mul_sum, additiveFourier_parseval, ← mul_assoc, mul_inv_cancel₀ hq, one_mul]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_NormalizedResidueIndicator
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The manuscript's normalized residue indicators and additive transforms -/

namespace Ostmann

open scoped BigOperators Classical ComplexConjugate

theorem residueVariance_pos {p : ℕ} [NeZero p] (S : Finset (ZMod p))
    (hS : S.Nonempty) (hSp : S.card < p) : 0 < residueVariance S := by
  have hp : (0 : ℝ) < p := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
  have hd : 0 < residueDensity S := div_pos (by exact_mod_cast hS.card_pos) hp
  have hd1 : residueDensity S < 1 := (div_lt_one hp).mpr (by exact_mod_cast hSp)
  exact mul_pos hd (sub_pos.mpr hd1)

theorem centeredDensity_sq_sum {p : ℕ} [NeZero p] (S : Finset (ZMod p)) :
    (∑ x : ZMod p, centeredDensity S x ^ 2) = (p : ℝ) * residueVariance S := by
  let σ := residueDensity S
  have hsq (x : ZMod p) : centeredDensity S x ^ 2 =
      (if x ∈ S then 1 - 2 * σ else 0) + σ ^ 2 := by
    dsimp [centeredDensity, σ, residueDensity]
    split <;> ring
  simp_rw [hsq]
  rw [Finset.sum_add_distrib]
  have hsum : (∑ x : ZMod p, if x ∈ S then (1 - 2 * σ) else 0) = S.card * (1 - 2 * σ) := by simp; ring
  rw [hsum]
  simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne p
  have hσ : (p : ℝ) * σ = S.card := by dsimp [σ, residueDensity]; field_simp
  change _ = (p : ℝ) * (σ * (1 - σ))
  rw [← hσ]
  ring

theorem normalizedResidueIndicator_sum {p : ℕ} [NeZero p] (S : Finset (ZMod p)) :
    (∑ x : ZMod p, normalizedResidueIndicator S x) = 0 := by
  simp only [normalizedResidueIndicator, ← Complex.ofReal_sum, ← Finset.sum_div,
    centeredDensity_sum, zero_div, Complex.ofReal_zero]

theorem normalizedResidueIndicator_energy {p : ℕ} [NeZero p] (S : Finset (ZMod p))
    (hS : S.Nonempty) (hSp : S.card < p) :
    (∑ x : ZMod p, ‖normalizedResidueIndicator S x‖ ^ 2) = p := by
  have hv := residueVariance_pos S hS hSp
  simp only [normalizedResidueIndicator, Complex.norm_real, Real.norm_eq_abs, sq_abs,
    div_pow, ← Finset.sum_div, Real.sq_sqrt hv.le, centeredDensity_sq_sum]
  exact mul_div_cancel_right₀ (p : ℝ) hv.ne'

theorem normalizedResidueTransform_zero {p : ℕ} [NeZero p] (S : Finset (ZMod p)) :
    normalizedResidueTransform S 0 = 0 := by
  simp only [normalizedResidueTransform, densityFourier, additiveFourier_apply,
    mul_zero, neg_zero, AddChar.map_zero_eq_one, mul_one, normalizedResidueIndicator_sum]

theorem normalizedResidueTransform_energy {p : ℕ} [NeZero p] (S : Finset (ZMod p))
    (hS : S.Nonempty) (hSp : S.card < p) :
    (∑ x : ZMod p, ‖normalizedResidueTransform S x‖ ^ 2) = p := by
  rw [normalizedResidueTransform, densityFourier_energy, normalizedResidueIndicator_energy S hS hSp]

theorem normalizedResidueTransform_neg {p : ℕ} [Fact p.Prime] (S : Finset (ZMod p)) (x : ZMod p) :
    normalizedResidueTransform S (-x) = conj (normalizedResidueTransform S x) := by
  have hreal : (fun y => conj (normalizedResidueIndicator S y)) = normalizedResidueIndicator S := by
    funext y
    simp only [normalizedResidueIndicator, Complex.conj_ofReal]
  have hh := additiveFourier_conj (normalizedResidueIndicator S) (-x)
  rw [hreal, neg_neg] at hh
  simp only [normalizedResidueTransform, densityFourier, map_mul, Complex.conj_ofReal]
  rw [hh]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_SparseTransformSpectrum
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Concentration of a small-L1 normalized additive transform

This is the finite argument (5.7), before the contracting kernel in
Proposition 5.1. It requires no analytic input.
-/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

theorem largeTransformSpectrum_zero_not_mem {p : ℕ} [NeZero p]
    (g : ZMod p → ℂ) (hg : g 0 = 0) : 0 ∉ largeTransformSpectrum g := by
  simp [largeTransformSpectrum, hg]

theorem largeTransformSpectrum_neg {p : ℕ} [NeZero p]
    (g : ZMod p → ℂ) (hg : ∀ b, g (-b) = conj (g b)) (b : ZMod p) :
    -b ∈ largeTransformSpectrum g ↔ b ∈ largeTransformSpectrum g := by
  simp only [largeTransformSpectrum, Finset.mem_filter, Finset.mem_univ, true_and,
    hg, Complex.norm_conj]

/-- The large coefficients occupy a small set and retain almost all energy. -/
theorem largeTransformSpectrum_bounds {p : ℕ} [NeZero p]
    (g : ZMod p → ℂ) (δ : ℝ)
    (hL1 : (∑ b, ‖g b‖) ≤ δ * p) (hL2 : (∑ b, ‖g b‖ ^ 2) = p) :
    ((largeTransformSpectrum g).card : ℝ) ≤ δ * p ∧
      (1 - δ) * p ≤ ∑ b ∈ largeTransformSpectrum g, ‖g b‖ ^ 2 := by
  let E := largeTransformSpectrum g
  have hcard : (E.card : ℝ) ≤ ∑ b ∈ E, ‖g b‖ := by
    calc
      _ = ∑ _b ∈ E, (1 : ℝ) := by simp
      _ ≤ _ := Finset.sum_le_sum fun b hb =>
        (Finset.mem_filter.mp hb).2.le
  have hL1E : (∑ b ∈ E, ‖g b‖) ≤ ∑ b, ‖g b‖ :=
    Finset.sum_le_univ_sum_of_nonneg (fun _ => norm_nonneg _)
  refine ⟨hcard.trans (hL1E.trans hL1), ?_⟩
  have hsmall : (∑ b ∈ Finset.univ \ E, ‖g b‖ ^ 2) ≤ δ * p := by
    calc
      _ ≤ ∑ b ∈ Finset.univ \ E, ‖g b‖ := by
        apply Finset.sum_le_sum
        intro b hb
        have hn : ‖g b‖ ≤ 1 := by
          have hnot := (Finset.mem_sdiff.mp hb).2
          simpa only [E, largeTransformSpectrum, Finset.mem_filter, Finset.mem_univ,
            true_and, not_lt] using hnot
        nlinarith [norm_nonneg (g b)]
      _ ≤ ∑ b, ‖g b‖ := Finset.sum_le_univ_sum_of_nonneg (fun _ => norm_nonneg _)
      _ ≤ _ := hL1
  have hsplit : (∑ b ∈ E, ‖g b‖ ^ 2) +
      (∑ b ∈ Finset.univ \ E, ‖g b‖ ^ 2) = p := by
    rw [Finset.sum_sdiff_eq_sub (Finset.subset_univ E), hL2]
    ring
  linarith

/-- The exact normalized residue transform satisfies the sparse-spectrum
conclusions used in Section 5 whenever its probability L1 norm is small. -/
theorem normalizedResidueTransform_sparse {p : ℕ} [Fact p.Prime]
    (S : Finset (ZMod p)) (hS : S.Nonempty) (hSp : S.card < p)
    (ε δ : ℝ) (hδ : δ ≤ ε) (hδsq : δ ≤ ε ^ 2)
    (hL1 : (p : ℝ)⁻¹ * ∑ b, ‖normalizedResidueTransform S b‖ ≤ δ) :
    let E := largeTransformSpectrum (normalizedResidueTransform S)
    0 ∉ E ∧ (∀ b, -b ∈ E ↔ b ∈ E) ∧
      (E.card : ℝ) ≤ ε * p ∧
      (1 - ε ^ 2) * p ≤ ∑ b ∈ E, ‖normalizedResidueTransform S b‖ ^ 2 := by
  intro E
  have hp : (0 : ℝ) < p := Nat.cast_pos.mpr (Fact.out : p.Prime).pos
  have hmass : (∑ b, ‖normalizedResidueTransform S b‖) ≤ δ * p := by
    have hh := mul_le_mul_of_nonneg_left hL1 hp.le
    simpa only [← mul_assoc, mul_inv_cancel₀ hp.ne', one_mul, mul_comm (p : ℝ) δ] using hh
  obtain ⟨hc, he⟩ := largeTransformSpectrum_bounds _ δ hmass
    (normalizedResidueTransform_energy S hS hSp)
  refine ⟨largeTransformSpectrum_zero_not_mem _ (normalizedResidueTransform_zero S),
    largeTransformSpectrum_neg _ (normalizedResidueTransform_neg S),
    hc.trans (mul_le_mul_of_nonneg_right hδ hp.le), ?_⟩
  exact (mul_le_mul_of_nonneg_right (by linarith : 1 - ε ^ 2 ≤ 1 - δ) hp.le).trans he

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityFourierBounds
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The two local Fourier bounds in the large-kernel correlation -/

namespace Ostmann

open scoped BigOperators ComplexConjugate

theorem additiveFourier_twice {q : ℕ} [NeZero q] (f : ZMod q → ℂ) (a : ZMod q) :
    additiveFourier (additiveFourier f) a = (q : ℂ)⁻¹ * f (-a) := by
  rw [additiveFourier_apply]
  congr 1
  have hi := additiveFourier_inversion f (-a)
  simpa only [mul_neg] using hi.symm

/-- Conjugation reverses the Fourier frequency. -/
theorem additiveFourier_conj_density {q : ℕ} [NeZero q] (f : ZMod q → ℂ) (a : ZMod q) :
    additiveFourier (fun x => conj (f x)) a = conj (additiveFourier f (-a)) := by
  simp only [additiveFourier_apply, map_mul, map_sum, map_inv₀, map_natCast,
    stdAddChar_conj, mul_neg, neg_neg]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_PhaseGiantTest
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The Fourier-phase giant and its real physical inverse -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

theorem additiveFourier_reflect {p : ℕ} [NeZero p] (g : ZMod p → ℂ) (x : ZMod p) :
    additiveFourier (fun b => g (-b)) x = additiveFourier g (-x) := by
  simp only [additiveFourier_apply]
  congr 1
  apply Fintype.sum_equiv (Equiv.neg (ZMod p))
  intro b
  simp only [Equiv.neg_apply, neg_neg, neg_mul, mul_neg]

theorem densityFourierInverse_real {p : ℕ} [NeZero p]
    (g : ZMod p → ℂ) (hg : ∀ b, g (-b) = conj (g b)) (x : ZMod p) :
    (densityFourierInverse g x).im = 0 := by
  have hr : (fun b => conj (g b)) = fun b => g (-b) := funext fun b => (hg b).symm
  have he := additiveFourier_conj g x
  rw [hr, additiveFourier_reflect] at he
  have hc : conj (densityFourierInverse g x) = densityFourierInverse g x := by
    unfold densityFourierInverse densityFourier
    rw [map_mul, Complex.conj_ofReal, ← he]
  have hh := congrArg Complex.im hc
  simp only [Complex.conj_im] at hh
  linarith

theorem densityFourierInverse_energy {p : ℕ} [NeZero p] (g : ZMod p → ℂ) :
    (∑ x, ‖densityFourierInverse g x‖ ^ 2) = ∑ b, ‖g b‖ ^ 2 := by
  rw [← densityFourier_energy g]
  exact (Equiv.neg (ZMod p)).bijective.sum_comp (fun x => ‖densityFourier g x‖ ^ 2)

/-- The unitary bilinear identity, with the inverse sign explicit. -/
theorem densityFourier_pairing {p : ℕ} [NeZero p]
    (f g : ZMod p → ℂ) :
    (∑ x, f x * densityFourierInverse g x) =
      ∑ b, densityFourier f (-b) * g b := by
  simp only [densityFourierInverse, densityFourier, additiveFourier_apply,
    Finset.mul_sum, mul_neg, neg_neg, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro x _
  rw [mul_comm b x]
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_PhaseGiantMean
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The positive uniform-support mean of the Fourier-phase giant -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

theorem densityFourier_reflect {p : ℕ} [NeZero p] (g : ZMod p → ℂ) (x : ZMod p) :
    densityFourier (fun b => g (-b)) x = densityFourier g (-x) := by
  simp only [densityFourier, additiveFourier_reflect]

theorem densityFourier_twice {p : ℕ} [NeZero p] (g : ZMod p → ℂ) (x : ZMod p) :
    densityFourier (densityFourier g) x = g (-x) := by
  have hp : (p : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne p
  have hs : (Real.sqrt (p : ℝ) : ℂ) * (Real.sqrt (p : ℝ) : ℂ) = p := by
    exact_mod_cast (by simpa only [pow_two] using Real.sq_sqrt (Nat.cast_nonneg p))
  unfold densityFourier
  rw [additiveFourier_const_mul, additiveFourier_twice]
  calc
    _ = ((Real.sqrt (p : ℝ) : ℂ) * (Real.sqrt (p : ℝ) : ℂ)) * (p : ℂ)⁻¹ * g (-x) := by ring
    _ = _ := by rw [hs, mul_inv_cancel₀ hp, one_mul]

theorem densityFourier_inverse {p : ℕ} [NeZero p] (g : ZMod p → ℂ) (x : ZMod p) :
    densityFourier (densityFourierInverse g) x = g x := by
  change densityFourier (fun b => densityFourier g (-b)) x = g x
  rw [densityFourier_reflect, densityFourier_twice, neg_neg]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Supply_FiniteSpectralProjection
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Concrete finite additive spectral projections for Section 5 -/

namespace Ostmann
open scoped Classical BigOperators

theorem densityFourier_sub {p : ℕ} [NeZero p] (f g : ZMod p → ℂ) (b : ZMod p) :
    densityFourier (fun x => f x - g x) b = densityFourier f b - densityFourier g b := by
  simp only [densityFourier, additiveFourier_sub, mul_sub]

theorem densityFourier_const_mul {p : ℕ} [NeZero p]
    (c : ℂ) (f : ZMod p → ℂ) (b : ZMod p) :
    densityFourier (fun x => c * f x) b = c * densityFourier f b := by
  simp only [densityFourier, additiveFourier_const_mul]
  ring

theorem densityFourierInverse_fourier {p : ℕ} [NeZero p]
    (f : ZMod p → ℂ) (x : ZMod p) :
    densityFourierInverse (densityFourier f) x = f x := by
  change densityFourier (densityFourier f) (-x) = f x
  rw [densityFourier_twice, neg_neg]

theorem finiteSpectralProjection_fourier {p : ℕ} [NeZero p]
    (E : Finset (ZMod p)) (f : ZMod p → ℂ) (b : ZMod p) :
    densityFourier (finiteSpectralProjection E f) b =
      if b ∈ E then densityFourier f b else 0 := densityFourier_inverse _ _

/-- The counting energy of the projection equals the selected Fourier energy. -/
theorem finiteSpectralProjection_energy {p : ℕ} [NeZero p]
    (E : Finset (ZMod p)) (f : ZMod p → ℂ) :
    (∑ x, ‖finiteSpectralProjection E f x‖ ^ 2) =
      ∑ b ∈ E, ‖densityFourier f b‖ ^ 2 := by
  rw [finiteSpectralProjection, densityFourierInverse_energy]
  simp only [apply_ite, norm_zero, ite_pow, zero_pow (by decide : 2 ≠ 0),
    Finset.sum_ite_mem, Finset.univ_inter]

theorem finiteSpectralProjection_energy_le {p : ℕ} [NeZero p]
    (E : Finset (ZMod p)) (f : ZMod p → ℂ) :
    (∑ x, ‖finiteSpectralProjection E f x‖ ^ 2) ≤ ∑ x, ‖f x‖ ^ 2 := by
  rw [finiteSpectralProjection_energy, ← densityFourier_energy f]
  exact Finset.sum_le_univ_sum_of_nonneg (fun _ => sq_nonneg _)

/-- The exact discarded energy, rather than a dimension-dependent bound. -/
theorem finiteSpectralProjection_residual_energy {p : ℕ} [NeZero p]
    (E : Finset (ZMod p)) (f : ZMod p → ℂ) :
    (∑ x, ‖f x - finiteSpectralProjection E f x‖ ^ 2) =
      ∑ b ∈ Finset.univ \ E, ‖densityFourier f b‖ ^ 2 := by
  rw [← densityFourier_energy (fun x => f x - finiteSpectralProjection E f x)]
  simp_rw [densityFourier_sub, finiteSpectralProjection_fourier]
  have hE : Finset.univ \ E = Finset.univ.filter (fun b => b ∉ E) := by
    ext b
    simp
  rw [hE, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro b _
  by_cases hb : b ∈ E <;> simp [hb]

/-- Every spectral projection minus half the identity has operator norm
one half, expressed in the counting energy needed for the block estimate. -/
theorem finiteSpectralProjection_half_energy {p : ℕ} [NeZero p]
    (E : Finset (ZMod p)) (f : ZMod p → ℂ) :
    (∑ x, ‖finiteSpectralProjection E f x - (1 / 2 : ℂ) * f x‖ ^ 2) =
      (1 / 4 : ℝ) * ∑ x, ‖f x‖ ^ 2 := by
  rw [← densityFourier_energy (fun x => finiteSpectralProjection E f x - (1 / 2 : ℂ) * f x),
    ← densityFourier_energy f, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [densityFourier_sub, finiteSpectralProjection_fourier, densityFourier_const_mul]
  by_cases hb : b ∈ E
  · rw [ite_eq_left hb]
    have he : densityFourier f b - (1 / 2 : ℂ) * densityFourier f b =
        (1 / 2 : ℂ) * densityFourier f b := by ring
    rw [he, norm_mul, mul_pow]
    norm_num
  · rw [ite_eq_right hb, zero_sub, norm_neg, norm_mul, mul_pow]
    norm_num

/-- Zero outside the selected frequencies makes the projection idempotent. -/
theorem finiteSpectralProjection_idempotent {p : ℕ} [NeZero p]
    (E : Finset (ZMod p)) (f : ZMod p → ℂ) :
    finiteSpectralProjection E (finiteSpectralProjection E f) = finiteSpectralProjection E f := by
  unfold finiteSpectralProjection
  congr 1
  funext b
  rw [densityFourier_inverse]
  by_cases hb : b ∈ E <;> simp [hb]

theorem finiteSpectralProjection_constant {p : ℕ} [NeZero p]
    (E : Finset (ZMod p)) (hE : 0 ∉ E) (c : ℂ) (x : ZMod p) :
    finiteSpectralProjection E (fun _ => c) x = 0 := by
  have he : (fun b : ZMod p => if b ∈ E then densityFourier (fun _ => c) b else 0) =
      fun _ => 0 := by
    funext b
    simp only [densityFourier, additiveFourier_const]
    by_cases hb : b = 0
    · subst b
      simp only [ite_eq_right hE]
    · simp only [ite_eq_right hb, mul_zero, ite_self]
  rw [finiteSpectralProjection, he]
  simp only [densityFourierInverse, densityFourier, additiveFourier_apply, zero_mul,
    Finset.sum_const_zero, mul_zero]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Supply_CenteredSupportProjection
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The centered support projections in the contracting local kernel -/

namespace Ostmann
open scoped Classical BigOperators

theorem finiteSupportMean_spec {α : Type*} (S : Finset α) (f : α → ℂ) :
    (S.card : ℂ) * finiteSupportMean S f = ∑ x ∈ S, f x := by
  by_cases hs : S.card = 0
  · have he : S = ∅ := Finset.card_eq_zero.mp hs
    simp [he, finiteSupportMean]
  · unfold finiteSupportMean
    rw [← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast hs), one_mul]

theorem centered_support_energy {α : Type*} (S : Finset α) (f : α → ℂ) (c : ℂ)
    (hc : ∑ x ∈ S, f x = (S.card : ℂ) * c) :
    (∑ x ∈ S, ‖f x - c‖ ^ 2) = (∑ x ∈ S, ‖f x‖ ^ 2) - S.card * ‖c‖ ^ 2 := by
  have hr := congrArg Complex.re hc
  have hi := congrArg Complex.im hc
  simp only [Complex.re_sum, Complex.im_sum, Complex.mul_re, Complex.mul_im,
    Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero, add_zero] at hr hi
  have he (x : α) : ‖f x - c‖ ^ 2 = ‖f x‖ ^ 2 -
      2 * (f x).re * c.re - 2 * (f x).im * c.im + ‖c‖ ^ 2 := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
    ring
  simp_rw [he]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  simp only [← Finset.sum_mul, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
  rw [hr, hi, Complex.sq_norm, Complex.normSq_apply]
  ring

theorem centeredSupportProjection_energy {α : Type*} [Fintype α]
    (S : Finset α) (f : α → ℂ) :
    (∑ x, ‖centeredSupportProjection S f x‖ ^ 2) =
      (∑ x ∈ S, ‖f x‖ ^ 2) - S.card * ‖finiteSupportMean S f‖ ^ 2 := by
  calc
    _ = ∑ x ∈ S, ‖f x - finiteSupportMean S f‖ ^ 2 := by
      simp only [centeredSupportProjection, apply_ite, norm_zero, ite_pow,
        zero_pow (by decide : 2 ≠ 0), Finset.sum_ite_mem, Finset.univ_inter]
    _ = _ := centered_support_energy S f _ (finiteSupportMean_spec S f).symm

theorem centeredSupportProjection_energy_le {α : Type*} [Fintype α]
    (S : Finset α) (f : α → ℂ) :
    (∑ x, ‖centeredSupportProjection S f x‖ ^ 2) ≤ ∑ x, ‖f x‖ ^ 2 := by
  rw [centeredSupportProjection_energy]
  exact (sub_le_self _ (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))).trans
    (Finset.sum_le_univ_sum_of_nonneg (fun _ => sq_nonneg _))

theorem centeredSupportProjection_eq_of_eqOn {α : Type*}
    (S : Finset α) (f g : α → ℂ) (h : ∀ x ∈ S, f x = g x) :
    centeredSupportProjection S f = centeredSupportProjection S g := by
  have hm : finiteSupportMean S f = finiteSupportMean S g := by
    unfold finiteSupportMean
    rw [Finset.sum_congr rfl h]
  funext x
  by_cases hx : x ∈ S
  · simp only [centeredSupportProjection, ite_eq_left hx, h x hx, hm]
  · simp only [centeredSupportProjection, ite_eq_right hx]

theorem centeredSupportProjection_disjoint {α : Type*}
    (S T : Finset α) (h : Disjoint S T) (f : α → ℂ) (x : α) (hx : x ∈ S) :
    centeredSupportProjection T f x = 0 := by
  exact ite_eq_right (fun ht => Finset.disjoint_left.mp h hx ht)

/-- The off-diagonal compression has norm at most one half. This uses only
orthogonal support and the exact half-identity spectral bound. -/
theorem centeredSupportProjection_spectral_energy {p : ℕ} [NeZero p]
    (S T E : Finset (ZMod p)) (hST : Disjoint S T) (f : ZMod p → ℂ) :
    (∑ x, ‖centeredSupportProjection S
      (finiteSpectralProjection E (centeredSupportProjection T f)) x‖ ^ 2) ≤
      (1 / 4 : ℝ) * ∑ x, ‖f x‖ ^ 2 := by
  let g := centeredSupportProjection T f
  have he : centeredSupportProjection S (finiteSpectralProjection E g) =
      centeredSupportProjection S (fun x => finiteSpectralProjection E g x - (1 / 2 : ℂ) * g x) := by
    apply centeredSupportProjection_eq_of_eqOn
    intro x hx
    rw [show g x = 0 from centeredSupportProjection_disjoint S T hST f x hx]
    simp
  rw [he]
  calc
    _ ≤ ∑ x, ‖finiteSpectralProjection E g x - (1 / 2 : ℂ) * g x‖ ^ 2 :=
      centeredSupportProjection_energy_le S _
    _ = (1 / 4 : ℝ) * ∑ x, ‖g x‖ ^ 2 := finiteSpectralProjection_half_energy E g
    _ ≤ _ := mul_le_mul_of_nonneg_left (centeredSupportProjection_energy_le T f) (by norm_num)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_SparseResidueProjection
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Sparse projection of the actual normalized residue indicator -/

namespace Ostmann
open scoped Classical BigOperators

/-- The projection chosen in (5.7) kills constants and loses at most epsilon
squared of the normalized residue indicator's energy. -/
theorem sparse_residue_projection {p : ℕ} [Fact p.Prime]
    (S : Finset (ZMod p)) (hS : S.Nonempty) (hSp : S.card < p)
    (ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hL1 : (p : ℝ)⁻¹ * ∑ b, ‖normalizedResidueTransform S b‖ ≤ ε ^ 2) :
    let E := largeTransformSpectrum (normalizedResidueTransform S)
    0 ∉ E ∧ (∀ b, -b ∈ E ↔ b ∈ E) ∧ (E.card : ℝ) ≤ ε * p ∧
      (∀ c x, finiteSpectralProjection E (fun _ => c) x = 0) ∧
      (1 - ε ^ 2) * p ≤ ∑ x, ‖finiteSpectralProjection E (normalizedResidueIndicator S) x‖ ^ 2 ∧
      (∑ x, ‖normalizedResidueIndicator S x -
        finiteSpectralProjection E (normalizedResidueIndicator S) x‖ ^ 2) ≤ ε ^ 2 * p := by
  intro E
  obtain ⟨hz, hn, hc, he⟩ := normalizedResidueTransform_sparse S hS hSp ε (ε ^ 2)
    (by nlinarith) le_rfl hL1
  refine ⟨hz, hn, hc, fun c x => finiteSpectralProjection_constant E hz c x, ?_, ?_⟩
  · simpa only [finiteSpectralProjection_energy, E, normalizedResidueTransform] using he
  · rw [finiteSpectralProjection_residual_energy,
      Finset.sum_sdiff_eq_sub (Finset.subset_univ E)]
    change (∑ b, ‖normalizedResidueTransform S b‖ ^ 2) -
      (∑ b ∈ E, ‖normalizedResidueTransform S b‖ ^ 2) ≤ _
    rw [normalizedResidueTransform_energy S hS hSp]
    linarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_SparseAdditiveKernel
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual additive kernel of the sparse spectral projection -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

theorem sparseAdditiveKernel_formula {p : ℕ} [NeZero p]
    (E : Finset (ZMod p)) (t : ℝ) (x : ZMod p) :
    sparseAdditiveKernel E t x = (t : ℂ) / p * ∑ b ∈ E, ZMod.stdAddChar (b * x) := by
  simp only [sparseAdditiveKernel, additiveFourier_apply, mul_neg, neg_neg,
    ite_mul, one_mul, zero_mul, Finset.sum_ite_mem, Finset.univ_inter, div_eq_mul_inv,
    mul_assoc]

theorem sparseAdditiveKernel_fourier {p : ℕ} [NeZero p]
    (E : Finset (ZMod p)) (t : ℝ) (a : ZMod p) :
    additiveFourier (sparseAdditiveKernel E t) a =
      (t : ℂ) * (p : ℂ)⁻¹ * (if a ∈ E then 1 else 0) := by
  change additiveFourier (fun x => (t : ℂ) *
    additiveFourier (fun b => if b ∈ E then 1 else 0) (-x)) a = _
  rw [additiveFourier_const_mul, additiveFourier_reflect,
    additiveFourier_twice, neg_neg, ← mul_assoc]

theorem sparseAdditiveKernel_real {p : ℕ} [NeZero p]
    (E : Finset (ZMod p)) (hE : ∀ b, -b ∈ E ↔ b ∈ E) (t : ℝ) (x : ZMod p) :
    (sparseAdditiveKernel E t x).im = 0 := by
  have hr : (densityFourierInverse (fun b => if b ∈ E then (1 : ℂ) else 0) x).im = 0 := by
    apply densityFourierInverse_real
    intro b
    by_cases hb : b ∈ E <;> simp [hb, hE b]
  have hp : Real.sqrt (p : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p))).ne'
  change ((Real.sqrt (p : ℝ) : ℂ) *
    additiveFourier (fun b => if b ∈ E then 1 else 0) (-x)).im = 0 at hr
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero] at hr
  have hz := (mul_eq_zero.mp hr).resolve_left hp
  simp only [sparseAdditiveKernel, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, add_zero, hz, mul_zero]

/-- The raw kernel matrix is precisely the scalar multiple of the projection;
no normalization or discarded frequency is hidden in the identification. -/
theorem sparseAdditiveKernel_action {p : ℕ} [NeZero p]
    (E : Finset (ZMod p)) (t : ℝ) (f : ZMod p → ℂ) (x : ZMod p) :
    (∑ y, f y * sparseAdditiveKernel E t (x - y)) =
      (t : ℂ) * finiteSpectralProjection E f x := by
  have hp : (p : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne p
  have hraw : (fun x => ∑ y, f y * sparseAdditiveKernel E t (x - y)) =
      fun x => (p : ℂ) * additiveConvolution f (sparseAdditiveKernel E t) x := by
    funext x
    simp only [additiveConvolution, ← mul_assoc, mul_inv_cancel₀ hp, one_mul]
  have hf : ∀ a, densityFourier (fun x => ∑ y, f y * sparseAdditiveKernel E t (x - y)) a =
      densityFourier (fun x => (t : ℂ) * finiteSpectralProjection E f x) a := by
    intro a
    rw [hraw, densityFourier, additiveFourier_const_mul, additiveFourier_convolution,
      sparseAdditiveKernel_fourier, densityFourier_const_mul, finiteSpectralProjection_fourier]
    by_cases ha : a ∈ E
    · simp only [ite_eq_left ha, mul_one, densityFourier]
      field_simp
    · simp only [ite_eq_right ha, mul_zero]
  have hfun := congrArg (fun g : ZMod p → ℂ => densityFourierInverse g x) (funext hf)
  simpa only [densityFourierInverse_fourier] using hfun

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_SparseKernelEnergy
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Energy bounds for the sparse kernel and its pointwise square -/

namespace Ostmann
open scoped Classical BigOperators

theorem rawAdditiveKernelAction_fourier {p : ℕ} [NeZero p]
    (k f : ZMod p → ℂ) (a : ZMod p) :
    densityFourier (rawAdditiveKernelAction k f) a =
      ((p : ℂ) * additiveFourier k a) * densityFourier f a := by
  have hp : (p : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne p
  have he : rawAdditiveKernelAction k f = fun x => (p : ℂ) * additiveConvolution f k x := by
    funext x
    simp only [rawAdditiveKernelAction, additiveConvolution, ← mul_assoc,
      mul_inv_cancel₀ hp, one_mul]
  rw [he, densityFourier, additiveFourier_const_mul, additiveFourier_convolution]
  unfold densityFourier
  ring

theorem rawAdditiveKernelAction_energy_le {p : ℕ} [NeZero p]
    (k f : ZMod p → ℂ) (B : ℝ)
    (hk : ∀ a, ‖(p : ℂ) * additiveFourier k a‖ ≤ B) :
    (∑ x, ‖rawAdditiveKernelAction k f x‖ ^ 2) ≤ B ^ 2 * ∑ x, ‖f x‖ ^ 2 := by
  rw [← densityFourier_energy, ← densityFourier_energy f, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a _
  rw [rawAdditiveKernelAction_fourier, norm_mul, mul_pow]
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (norm_nonneg _) (hk a) 2) (sq_nonneg _)

theorem sparseAdditiveKernel_square_fourier {p : ℕ} [NeZero p]
    (E : Finset (ZMod p)) (t : ℝ) (a : ZMod p) :
    additiveFourier (fun x => sparseAdditiveKernel E t x * sparseAdditiveKernel E t x) a =
      (t : ℂ) ^ 2 * ((p : ℂ)⁻¹) ^ 2 * ((E.filter fun b => a - b ∈ E).card : ℂ) := by
  rw [additiveFourier_pointwise_mul]
  simp_rw [sparseAdditiveKernel_fourier]
  have he (b : ZMod p) :
      ((t : ℂ) * (p : ℂ)⁻¹ * (if b ∈ E then 1 else 0)) *
        ((t : ℂ) * (p : ℂ)⁻¹ * (if a - b ∈ E then 1 else 0)) =
      ((t : ℂ) ^ 2 * ((p : ℂ)⁻¹) ^ 2) *
        (if b ∈ E ∧ a - b ∈ E then 1 else 0) := by
    split_ifs <;> simp_all
    ring
  simp_rw [he]
  rw [← Finset.mul_sum]
  congr 1
  simp [← Finset.filter_filter]

/-- Equation (5.8): the square kernel has raw operator norm at most
`t^2 epsilon`. The estimate retains the actual convolution multiplicities. -/
theorem sparseAdditiveKernel_square_multiplier_le {p : ℕ} [NeZero p]
    (E : Finset (ZMod p)) (t ε : ℝ) (hE : (E.card : ℝ) ≤ ε * p) (a : ZMod p) :
    ‖(p : ℂ) * additiveFourier
      (fun x => sparseAdditiveKernel E t x * sparseAdditiveKernel E t x) a‖ ≤ t ^ 2 * ε := by
  have hp : (0 : ℝ) < p := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
  have hc : ((E.filter fun b => a - b ∈ E).card : ℝ) ≤ ε * p := by
    have hc' : ((E.filter fun b => a - b ∈ E).card : ℝ) ≤ E.card := by
      exact_mod_cast Finset.card_filter_le E (fun b => a - b ∈ E)
    exact hc'.trans hE
  rw [sparseAdditiveKernel_square_fourier]
  simp only [norm_mul, norm_pow, norm_inv, Complex.norm_natCast, Complex.norm_real,
    Real.norm_eq_abs, sq_abs]
  have he : (p : ℝ) * (t ^ 2 * ((p : ℝ)⁻¹) ^ 2 *
      ((E.filter fun b => a - b ∈ E).card : ℝ)) =
      t ^ 2 * (((E.filter fun b => a - b ∈ E).card : ℝ) / p) := by
    field_simp
  rw [he]
  exact mul_le_mul_of_nonneg_left ((div_le_iff₀ hp).mpr hc) (sq_nonneg _)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Supply_ResidueVectorNorm
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Counting L2 norms for the finite local kernel blocks -/

namespace Ostmann
open WithLp
open scoped Classical BigOperators ComplexConjugate

theorem residueVectorNorm_nonneg {p : ℕ} [NeZero p] (f : ZMod p → ℂ) :
    0 ≤ residueVectorNorm f := norm_nonneg _

theorem residueVectorNorm_sq {p : ℕ} [NeZero p] (f : ZMod p → ℂ) :
    residueVectorNorm f ^ 2 = ∑ x, ‖f x‖ ^ 2 := EuclideanSpace.norm_sq_eq _

theorem residueVectorNorm_add_le {p : ℕ} [NeZero p] (f g : ZMod p → ℂ) :
    residueVectorNorm (fun x => f x + g x) ≤ residueVectorNorm f + residueVectorNorm g := by
  change ‖(toLp 2 f : EuclideanSpace ℂ (ZMod p)) + toLp 2 g‖ ≤ _
  exact norm_add_le _ _

theorem residueVectorNorm_smul {p : ℕ} [NeZero p] (a : ℂ) (f : ZMod p → ℂ) :
    residueVectorNorm (fun x => a * f x) = ‖a‖ * residueVectorNorm f := by
  change ‖a • (toLp 2 f : EuclideanSpace ℂ (ZMod p))‖ = _
  exact norm_smul _ _

theorem residueVectorNorm_le_iff {p : ℕ} [NeZero p] (f : ZMod p → ℂ)
    (B : ℝ) (hB : 0 ≤ B) :
    residueVectorNorm f ≤ B ↔ (∑ x, ‖f x‖ ^ 2) ≤ B ^ 2 := by
  rw [← residueVectorNorm_sq]
  exact (sq_le_sq₀ (residueVectorNorm_nonneg f) hB).symm

theorem residueVectorNorm_inner_le {p : ℕ} [NeZero p] (f g : ZMod p → ℂ) :
    ‖∑ x, conj (f x) * g x‖ ≤ residueVectorNorm f * residueVectorNorm g := by
  calc
    _ ≤ ∑ x, ‖conj (f x) * g x‖ := norm_sum_le _ _
    _ = ∑ x, ‖f x‖ * ‖g x‖ := by simp only [norm_mul, Complex.norm_conj]
    _ ≤ _ := by
      simpa only [residueVectorNorm, EuclideanSpace.norm_eq] using
        Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun x => ‖f x‖) (fun x => ‖g x‖)

theorem residueVectorNorm_raw_le {p : ℕ} [NeZero p]
    (k f : ZMod p → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hk : ∀ a, ‖(p : ℂ) * additiveFourier k a‖ ≤ B) :
    residueVectorNorm (rawAdditiveKernelAction k f) ≤ B * residueVectorNorm f := by
  apply (residueVectorNorm_le_iff _ _ (mul_nonneg hB (residueVectorNorm_nonneg _))).mpr
  rw [mul_pow, residueVectorNorm_sq]
  exact rawAdditiveKernelAction_energy_le k f B hk

theorem residueVectorNorm_centered_le {p : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (f : ZMod p → ℂ) :
    residueVectorNorm (centeredSupportProjection S f) ≤ residueVectorNorm f := by
  apply (residueVectorNorm_le_iff _ _ (residueVectorNorm_nonneg _)).mpr
  rw [residueVectorNorm_sq]
  exact centeredSupportProjection_energy_le S f

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ResidueBlockEnergy
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Two-by-two control of the actual finite residue blocks -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

/-- Cauchy--Schwarz and the vector triangle inequality reduce the finite
kernel block to its scalar matrix of bounds, without a dimension factor. -/
theorem residue_block_energy {p : ℕ} [NeZero p]
    (a : ℂ) (row col : ZMod p → ℂ) (C : (ZMod p → ℂ) → ZMod p → ℂ)
    (s d r : ℝ) (hs : 0 ≤ s) (hd : 0 ≤ d)
    (hgap : d + 1 / 20 ≤ s)
    (ha : ‖a‖ ≤ s) (hrow : residueVectorNorm row ≤ r)
    (hcol : residueVectorNorm col ≤ r)
    (hC : ∀ f, residueVectorNorm (C f) ≤ d * residueVectorNorm f)
    (z : ℂ) (f : ZMod p → ℂ) :
    ‖a * z + ∑ x, conj (row x) * f x‖ ^ 2 +
      residueVectorNorm (fun x => z * col x + C f x) ^ 2 ≤
      (s + 20 * r ^ 2) ^ 2 * (‖z‖ ^ 2 + residueVectorNorm f ^ 2) := by
  have hleft : ‖a * z + ∑ x, conj (row x) * f x‖ ≤
      s * ‖z‖ + r * residueVectorNorm f := by
    apply (norm_add_le _ _).trans
    rw [norm_mul]
    exact add_le_add (mul_le_mul_of_nonneg_right ha (norm_nonneg _))
      ((residueVectorNorm_inner_le row f).trans
        (mul_le_mul_of_nonneg_right hrow (residueVectorNorm_nonneg _)))
  have hright : residueVectorNorm (fun x => z * col x + C f x) ≤
      r * ‖z‖ + d * residueVectorNorm f := by
    apply (residueVectorNorm_add_le _ _).trans
    rw [residueVectorNorm_smul]
    exact add_le_add (by nlinarith only [mul_le_mul_of_nonneg_left hcol (norm_nonneg z)]) (hC f)
  apply (add_le_add (pow_le_pow_left₀ (norm_nonneg _) hleft 2)
    (pow_le_pow_left₀ (residueVectorNorm_nonneg _) hright 2)).trans
  exact symmetric_block_energy s d r ‖z‖ (residueVectorNorm f) hs hd hgap

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Supply_SpectralProjectionPairing
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact pairing of the local spectral projection -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

theorem densityFourier_conj_reflect {p : ℕ} [NeZero p]
    (f : ZMod p → ℂ) (b : ZMod p) :
    densityFourier (fun x => conj (f x)) b = conj (densityFourier f (-b)) := by
  simp only [densityFourier, additiveFourier_conj_density, map_mul, Complex.conj_ofReal]

theorem densityFourier_inner {p : ℕ} [NeZero p] (f g : ZMod p → ℂ) :
    (∑ x, conj (f x) * g x) = ∑ b, conj (densityFourier f b) * densityFourier g b := by
  have he := densityFourier_pairing (fun x => conj (f x)) (densityFourier g)
  simpa only [densityFourierInverse_fourier, densityFourier_conj_reflect, neg_neg] using he

theorem finiteSpectralProjection_pairing {p : ℕ} [NeZero p]
    (E : Finset (ZMod p)) (f g : ZMod p → ℂ) :
    (∑ x, conj (f x) * finiteSpectralProjection E g x) =
      ∑ b ∈ E, conj (densityFourier f b) * densityFourier g b := by
  rw [densityFourier_inner]
  simp only [finiteSpectralProjection_fourier, mul_ite, mul_zero,
    Finset.sum_ite_mem, Finset.univ_inter]

theorem finiteSpectralProjection_selfAdjoint {p : ℕ} [NeZero p]
    (E : Finset (ZMod p)) (f g : ZMod p → ℂ) :
    (∑ x, conj (f x) * finiteSpectralProjection E g x) =
      ∑ x, conj (finiteSpectralProjection E f x) * g x := by
  rw [finiteSpectralProjection_pairing, densityFourier_inner]
  simp only [finiteSpectralProjection_fourier, apply_ite, map_zero, ite_mul,
    zero_mul, Finset.sum_ite_mem, Finset.univ_inter]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Supply_SpectralProjectionAffine
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Affine identities for the constant-killing local projection -/

namespace Ostmann
open scoped Classical BigOperators

theorem densityFourier_affine {p : ℕ} [NeZero p]
    (f : ZMod p → ℂ) (a c : ℂ) (b : ZMod p) :
    densityFourier (fun x => a * f x + c) b =
      a * densityFourier f b + densityFourier (fun _ => c) b := by
  simp only [densityFourier, additiveFourier_apply, add_mul, Finset.sum_add_distrib,
    ← Finset.mul_sum, mul_assoc]
  ring

theorem finiteSpectralProjection_affine {p : ℕ} [NeZero p]
    (E : Finset (ZMod p)) (hE : 0 ∉ E) (f : ZMod p → ℂ) (a c : ℂ) :
    finiteSpectralProjection E (fun x => a * f x + c) =
      fun x => a * finiteSpectralProjection E f x := by
  have he : densityFourier (finiteSpectralProjection E (fun x => a * f x + c)) =
      densityFourier (fun x => a * finiteSpectralProjection E f x) := by
    funext b
    rw [finiteSpectralProjection_fourier, densityFourier_affine,
      densityFourier_const_mul, finiteSpectralProjection_fourier]
    by_cases hb : b ∈ E
    · have hb0 : b ≠ 0 := by intro h; subst b; exact hE hb
      simp only [ite_eq_left hb, densityFourier, additiveFourier_const,
        ite_eq_right hb0, mul_zero, add_zero]
    · simp only [ite_eq_right hb, mul_zero]
  have hh := congrArg (fun g => fun x => densityFourierInverse g x) he
  simpa only [densityFourierInverse_fourier] using hh

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Supply_ResidueProjectionScalar
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The negative scalar block between complementary residue supports -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

theorem uniformResidueVector_affine {p : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (hS : S.Nonempty) (hSp : S.card < p) (x : ZMod p) :
    uniformResidueVector S x =
      ((Real.sqrt (residueVariance S) / S.card : ℝ) : ℂ) * normalizedResidueIndicator S x +
        ((1 / (p : ℝ) : ℝ) : ℂ) := by
  have hs : (S.card : ℝ) ≠ 0 := by exact_mod_cast hS.card_pos.ne'
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne p
  have hv : Real.sqrt (residueVariance S) ≠ 0 :=
    (Real.sqrt_pos.mpr (residueVariance_pos S hS hSp)).ne'
  unfold uniformResidueVector normalizedResidueIndicator centeredDensity
  rw [← Complex.ofReal_mul, ← Complex.ofReal_add]
  apply congrArg Complex.ofReal
  field_simp
  ring

theorem uniformResidueVector_compl_affine {p : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (hS : S.Nonempty) (hSp : S.card < p) (x : ZMod p) :
    uniformResidueVector (Finset.univ \ S) x =
      ((-Real.sqrt (residueVariance S) / ((p : ℝ) - S.card) : ℝ) : ℂ) *
        normalizedResidueIndicator S x + ((1 / (p : ℝ) : ℝ) : ℂ) := by
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne p
  have hd : (p : ℝ) - S.card ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hSp.ne')
  have hv : Real.sqrt (residueVariance S) ≠ 0 :=
    (Real.sqrt_pos.mpr (residueVariance_pos S hS hSp)).ne'
  have hc : ((Finset.univ \ S).card : ℝ) = (p : ℝ) - S.card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ S), Finset.card_univ, ZMod.card,
      Nat.cast_sub hSp.le]
  unfold uniformResidueVector normalizedResidueIndicator centeredDensity
  rw [hc]
  have he : (if x ∈ Finset.univ \ S then (1 : ℝ) else 0) =
      1 - (if x ∈ S then 1 else 0) := by
    by_cases hx : x ∈ S <;> simp [hx]
  rw [he]
  rw [← Complex.ofReal_mul, ← Complex.ofReal_add]
  apply congrArg Complex.ofReal
  field_simp
  ring

theorem finiteSpectralProjection_affine_pairing {p : ℕ} [NeZero p]
    (E : Finset (ZMod p)) (hE : 0 ∉ E) (f : ZMod p → ℂ) (a b c d : ℂ) :
    (∑ x, conj (a * f x + c) *
      finiteSpectralProjection E (fun x => b * f x + d) x) =
      conj a * b * ((∑ x, ‖finiteSpectralProjection E f x‖ ^ 2 : ℝ) : ℂ) := by
  have he := finiteSpectralProjection_selfAdjoint E (fun x => a * f x + c)
    (finiteSpectralProjection E (fun x => b * f x + d))
  rw [finiteSpectralProjection_idempotent] at he
  rw [he, finiteSpectralProjection_affine E hE, finiteSpectralProjection_affine E hE]
  rw [Complex.ofReal_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [map_mul]
  have hn : conj (finiteSpectralProjection E f x) * finiteSpectralProjection E f x =
      ((‖finiteSpectralProjection E f x‖ ^ 2 : ℝ) : ℂ) := by
    rw [mul_comm, Complex.mul_conj', Complex.ofReal_pow]
  calc
    _ = conj a * b * (conj (finiteSpectralProjection E f x) * finiteSpectralProjection E f x) := by ring
    _ = _ := by rw [hn]

/-- The raw projection's scalar block is negative with the exact coefficient
`-1/p^2` appearing in the proof of Lemma 5.2. -/
theorem residueProjection_scalar {p : ℕ} [NeZero p]
    (S E : Finset (ZMod p)) (hS : S.Nonempty) (hSp : S.card < p) (hE : 0 ∉ E) :
    (∑ x, conj (uniformResidueVector S x) *
      finiteSpectralProjection E (uniformResidueVector (Finset.univ \ S)) x) =
      -((p : ℂ) ^ 2)⁻¹ *
        ((∑ x, ‖finiteSpectralProjection E (normalizedResidueIndicator S) x‖ ^ 2 : ℝ) : ℂ) := by
  have hleft : uniformResidueVector S = fun x =>
      ((Real.sqrt (residueVariance S) / S.card : ℝ) : ℂ) * normalizedResidueIndicator S x +
        ((1 / (p : ℝ) : ℝ) : ℂ) := funext (uniformResidueVector_affine S hS hSp)
  have hright : uniformResidueVector (Finset.univ \ S) = fun x =>
      ((-Real.sqrt (residueVariance S) / ((p : ℝ) - S.card) : ℝ) : ℂ) *
        normalizedResidueIndicator S x + ((1 / (p : ℝ) : ℝ) : ℂ) :=
    funext (uniformResidueVector_compl_affine S hS hSp)
  rw [hleft, hright]
  rw [finiteSpectralProjection_affine_pairing E hE]
  congr 1
  rw [Complex.conj_ofReal, ← Complex.ofReal_mul]
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne p
  have hs : (S.card : ℝ) ≠ 0 := by exact_mod_cast hS.card_pos.ne'
  have hd : (p : ℝ) - S.card ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hSp.ne')
  have hv := Real.sq_sqrt (residueVariance_pos S hS hSp).le
  have he : (Real.sqrt (residueVariance S) / S.card) *
      (-Real.sqrt (residueVariance S) / ((p : ℝ) - S.card)) = -((p : ℝ) ^ 2)⁻¹ := by
    rw [div_mul_div_comm, mul_neg, ← pow_two, hv]
    unfold residueVariance residueDensity
    field_simp
  rw [he]
  push_cast
  rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_SparseKernelScalar
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The scalar decrease contributed by the sparse local kernel -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

theorem residueKernelScalar_sparse {p : ℕ} [NeZero p]
    (S E : Finset (ZMod p)) (hS : S.Nonempty) (hSp : S.card < p) (hE : 0 ∉ E)
    (t : ℝ) :
    residueKernelScalar S (sparseAdditiveKernel E t) =
      -(t : ℂ) / (p : ℂ) ^ 2 *
        ((∑ x, ‖finiteSpectralProjection E (normalizedResidueIndicator S) x‖ ^ 2 : ℝ) : ℂ) := by
  unfold residueKernelScalar rawAdditiveKernelAction
  simp_rw [sparseAdditiveKernel_action]
  calc
    _ = (t : ℂ) * (∑ x, conj (uniformResidueVector S x) *
        finiteSpectralProjection E (uniformResidueVector (Finset.univ \ S)) x) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = _ := by rw [residueProjection_scalar S E hS hSp hE]; ring

theorem residueKernelScalar_sparse_re_le {p : ℕ} [NeZero p]
    (S E : Finset (ZMod p)) (hS : S.Nonempty) (hSp : S.card < p) (hE : 0 ∉ E)
    (t ε : ℝ) (ht : 0 ≤ t)
    (henergy : (1 - ε ^ 2) * p ≤
      ∑ x, ‖finiteSpectralProjection E (normalizedResidueIndicator S) x‖ ^ 2) :
    (residueKernelScalar S (sparseAdditiveKernel E t)).re ≤ -(t * (1 - ε ^ 2)) / p := by
  have hp : (0 : ℝ) < p := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
  rw [residueKernelScalar_sparse S E hS hSp hE]
  have hre : (-(t : ℂ) / (p : ℂ) ^ 2 *
      ((∑ x, ‖finiteSpectralProjection E (normalizedResidueIndicator S) x‖ ^ 2 : ℝ) : ℂ)).re =
      -t / (p : ℝ) ^ 2 * ∑ x, ‖finiteSpectralProjection E (normalizedResidueIndicator S) x‖ ^ 2 := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_pow, ← Complex.ofReal_neg,
      ← Complex.ofReal_div, ← Complex.ofReal_mul, Complex.ofReal_re]
  rw [hre]
  calc
    _ ≤ -t / (p : ℝ) ^ 2 * ((1 - ε ^ 2) * p) :=
      mul_le_mul_of_nonpos_left henergy (div_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg _))
    _ = _ := by field_simp

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Supply_CenteredResidueProjection
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Centered support projections annihilate the two values of the residue indicator -/

namespace Ostmann
open scoped Classical BigOperators

theorem centeredSupportProjection_sub {α : Type*}
    (S : Finset α) (f g : α → ℂ) :
    centeredSupportProjection S (fun x => f x - g x) =
      fun x => centeredSupportProjection S f x - centeredSupportProjection S g x := by
  funext x
  unfold centeredSupportProjection finiteSupportMean
  rw [Finset.sum_sub_distrib, mul_sub]
  split_ifs <;> ring

theorem centeredSupportProjection_constant_on {α : Type*}
    (S : Finset α) (f : α → ℂ) (c : ℂ) (hf : ∀ x ∈ S, f x = c) :
    centeredSupportProjection S f = fun _ => 0 := by
  by_cases hs : S.Nonempty
  · have hc : (S.card : ℂ) ≠ 0 := by exact_mod_cast hs.card_pos.ne'
    have hm : finiteSupportMean S f = c := by
      unfold finiteSupportMean
      rw [Finset.sum_congr rfl hf]
      simp only [Finset.sum_const, nsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]
    funext x
    by_cases hx : x ∈ S
    · simp only [centeredSupportProjection, ite_eq_left hx, hf x hx, hm, sub_self]
    · exact ite_eq_right hx
  · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    subst S
    funext x
    simp only [centeredSupportProjection, Finset.notMem_empty, ite_false, if_false]

theorem centeredSupportProjection_residue_zero {p : ℕ}
    (S : Finset (ZMod p)) :
    centeredSupportProjection S (normalizedResidueIndicator S) = fun _ => 0 := by
  apply centeredSupportProjection_constant_on S _
    (((1 - (S.card : ℝ) / p) / Real.sqrt (residueVariance S) : ℝ) : ℂ)
  intro x hx
  simp only [normalizedResidueIndicator, centeredDensity, ite_eq_left hx]

theorem centeredSupportProjection_compl_residue_zero {p : ℕ} [NeZero p]
    (S : Finset (ZMod p)) :
    centeredSupportProjection (Finset.univ \ S) (normalizedResidueIndicator S) = fun _ => 0 := by
  apply centeredSupportProjection_constant_on _ _
    (((-(S.card : ℝ) / p) / Real.sqrt (residueVariance S) : ℝ) : ℂ)
  intro x hx
  have hn := (Finset.mem_sdiff.mp hx).2
  simp only [normalizedResidueIndicator, centeredDensity, ite_eq_right hn, zero_sub, neg_div]

/-- Annihilation of the physical indicator turns the sparse projection error
into the small side block required by Lemma 5.2. -/
theorem centered_residue_projection_energy_le {p : ℕ} [NeZero p]
    (S E T : Finset (ZMod p)) (ε : ℝ)
    (hT : centeredSupportProjection T (normalizedResidueIndicator S) = fun _ => 0)
    (herr : (∑ x, ‖normalizedResidueIndicator S x -
      finiteSpectralProjection E (normalizedResidueIndicator S) x‖ ^ 2) ≤ ε ^ 2 * p) :
    (∑ x, ‖centeredSupportProjection T
      (finiteSpectralProjection E (normalizedResidueIndicator S)) x‖ ^ 2) ≤ ε ^ 2 * p := by
  have he := centeredSupportProjection_sub T
    (finiteSpectralProjection E (normalizedResidueIndicator S)) (normalizedResidueIndicator S)
  rw [hT] at he
  simp only [sub_zero] at he
  change centeredSupportProjection T
    (fun x => finiteSpectralProjection E (normalizedResidueIndicator S) x - normalizedResidueIndicator S x) =
      centeredSupportProjection T (finiteSpectralProjection E (normalizedResidueIndicator S)) at he
  rw [← he]
  apply (centeredSupportProjection_energy_le T _).trans
  simpa only [norm_sub_rev] using herr

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Supply_ResidueProjectionSides
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Quantitative side blocks of the sparse residue projection -/

namespace Ostmann
open scoped Classical BigOperators

theorem centered_spectral_affine_energy {p : ℕ} [NeZero p]
    (E T : Finset (ZMod p)) (hE : 0 ∉ E) (f : ZMod p → ℂ) (a c : ℂ) :
    (∑ x, ‖centeredSupportProjection T
      (finiteSpectralProjection E (fun x => a * f x + c)) x‖ ^ 2) =
      ‖a‖ ^ 2 * ∑ x, ‖centeredSupportProjection T (finiteSpectralProjection E f) x‖ ^ 2 := by
  rw [finiteSpectralProjection_affine E hE, centeredSupportProjection_const_mul]
  simp only [norm_mul, mul_pow, Finset.mul_sum]

theorem residue_uniform_coefficient_sq {p : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (hS : S.Nonempty) (hSp : S.card < p)
    (hlo : (1 / 3 : ℝ) ≤ residueDensity S) :
    (Real.sqrt (residueVariance S) / S.card) ^ 2 ≤ 2 / (p : ℝ) ^ 2 := by
  have hp : (0 : ℝ) < p := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
  have hs : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  have hps : (p : ℝ) ≤ 3 * S.card := by
    rw [residueDensity, le_div_iff₀ hp] at hlo
    linarith
  have hv : residueVariance S = (S.card : ℝ) * (p - S.card) / (p : ℝ) ^ 2 := by
    unfold residueVariance residueDensity
    field_simp
  rw [div_pow, Real.sq_sqrt (residueVariance_pos S hS hSp).le, hv]
  apply (div_le_iff₀ (sq_pos_of_pos hs)).mpr
  rw [div_mul_eq_mul_div]
  apply (div_le_div_iff_of_pos_right (sq_pos_of_pos hp)).mpr
  nlinarith [mul_nonneg hs.le (sub_nonneg.mpr hps)]

theorem residue_compl_coefficient_sq {p : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (hS : S.Nonempty) (hSp : S.card < p)
    (hhi : residueDensity S ≤ 2 / 3) :
    (-Real.sqrt (residueVariance S) / ((p : ℝ) - S.card)) ^ 2 ≤ 2 / (p : ℝ) ^ 2 := by
  have hp : (0 : ℝ) < p := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
  have hs : (0 : ℝ) < (p : ℝ) - S.card := sub_pos.mpr (by exact_mod_cast hSp)
  have hps : 3 * (S.card : ℝ) ≤ 2 * p := by
    rw [residueDensity, div_le_iff₀ hp] at hhi
    linarith
  have hv : residueVariance S = (S.card : ℝ) * (p - S.card) / (p : ℝ) ^ 2 := by
    unfold residueVariance residueDensity
    field_simp
  rw [div_pow, neg_sq, Real.sq_sqrt (residueVariance_pos S hS hSp).le, hv]
  apply (div_le_iff₀ (sq_pos_of_pos hs)).mpr
  rw [div_mul_eq_mul_div]
  apply (div_le_div_iff_of_pos_right (sq_pos_of_pos hp)).mpr
  nlinarith [mul_nonneg hs.le (sub_nonneg.mpr hps)]

/-- Either uniform-support side of the projection is O(epsilon/sqrt(p)),
in the squared-energy form used to bound the local block matrix. -/
theorem residueProjection_side_energy {p : ℕ} [NeZero p]
    (S E : Finset (ZMod p)) (hS : S.Nonempty) (hSp : S.card < p) (hE : 0 ∉ E)
    (hlo : (1 / 3 : ℝ) ≤ residueDensity S) (hhi : residueDensity S ≤ 2 / 3)
    (ε : ℝ)
    (herr : (∑ x, ‖normalizedResidueIndicator S x -
      finiteSpectralProjection E (normalizedResidueIndicator S) x‖ ^ 2) ≤ ε ^ 2 * p) :
    (∑ x, ‖centeredSupportProjection (Finset.univ \ S)
      (finiteSpectralProjection E (uniformResidueVector S)) x‖ ^ 2) ≤ 2 * ε ^ 2 / p ∧
    (∑ x, ‖centeredSupportProjection S
      (finiteSpectralProjection E (uniformResidueVector (Finset.univ \ S))) x‖ ^ 2) ≤ 2 * ε ^ 2 / p := by
  have hp : (0 : ℝ) < p := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
  have hbound (T : Finset (ZMod p)) (a c : ℝ)
      (hT : centeredSupportProjection T (normalizedResidueIndicator S) = fun _ => 0)
      (ha : a ^ 2 ≤ 2 / (p : ℝ) ^ 2) :
      (∑ x, ‖centeredSupportProjection T (finiteSpectralProjection E
        (fun x => (a : ℂ) * normalizedResidueIndicator S x + (c : ℂ))) x‖ ^ 2) ≤
          2 * ε ^ 2 / p := by
    rw [centered_spectral_affine_energy E T hE]
    simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]
    calc
      _ ≤ a ^ 2 * (ε ^ 2 * p) := mul_le_mul_of_nonneg_left
        (centered_residue_projection_energy_le S E T ε hT herr) (sq_nonneg _)
      _ ≤ (2 / (p : ℝ) ^ 2) * (ε ^ 2 * p) :=
        mul_le_mul_of_nonneg_right ha (mul_nonneg (sq_nonneg _) hp.le)
      _ = _ := by field_simp
  constructor
  · have he := funext (uniformResidueVector_affine S hS hSp)
    rw [he]
    exact hbound _ _ _ (centeredSupportProjection_compl_residue_zero S)
      (residue_uniform_coefficient_sq S hS hSp hlo)
  · have he := funext (uniformResidueVector_compl_affine S hS hSp)
    rw [he]
    exact hbound _ _ _ (centeredSupportProjection_residue_zero S)
      (residue_compl_coefficient_sq S hS hSp hhi)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Supply_ResidueKernelNormBounds
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Dimension-free norms of the concrete residue kernel blocks -/

namespace Ostmann
open scoped Classical BigOperators

theorem uniformResidueVector_energy {p : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (hS : S.Nonempty) :
    (∑ x, ‖uniformResidueVector S x‖ ^ 2) = (S.card : ℝ)⁻¹ := by
  have hs : (S.card : ℝ) ≠ 0 := by exact_mod_cast hS.card_pos.ne'
  have he (x : ZMod p) : ‖uniformResidueVector S x‖ ^ 2 =
      if x ∈ S then ((S.card : ℝ)⁻¹) ^ 2 else 0 := by
    by_cases hx : x ∈ S <;> simp [uniformResidueVector, hx]
  simp_rw [he]
  simp only [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
  field_simp

theorem uniformResidueVector_norm_le {p : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (hS : S.Nonempty) (hcard : (p : ℝ) / 3 ≤ S.card) :
    residueVectorNorm (uniformResidueVector S) ≤ 2 / Real.sqrt (p : ℝ) := by
  have hp : (0 : ℝ) < p := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
  have hs : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  apply (residueVectorNorm_le_iff _ _ (by positivity)).mpr
  rw [uniformResidueVector_energy S hS, div_pow, Real.sq_sqrt hp.le]
  norm_num
  rw [inv_eq_one_div]
  apply (div_le_div_iff₀ hs hp).mpr
  linarith

theorem residueVectorNorm_cross_projection_le {p : ℕ} [NeZero p]
    (S T E : Finset (ZMod p)) (hST : Disjoint S T) (f : ZMod p → ℂ) :
    residueVectorNorm (centeredSupportProjection S
      (finiteSpectralProjection E (centeredSupportProjection T f))) ≤
      (1 / 2 : ℝ) * residueVectorNorm f := by
  apply (residueVectorNorm_le_iff _ _ (by positivity [residueVectorNorm_nonneg f])).mpr
  rw [mul_pow, residueVectorNorm_sq]
  convert centeredSupportProjection_spectral_energy S T E hST f using 1
  all_goals try with_reducible_and_instances rfl
  norm_num

theorem residueVectorNorm_cross_kernel_le {p : ℕ} [NeZero p]
    (S T E : Finset (ZMod p)) (hST : Disjoint S T) (t : ℝ) (ht : 0 ≤ t)
    (f : ZMod p → ℂ) :
    residueVectorNorm (centeredSupportProjection S
      (rawAdditiveKernelAction (sparseAdditiveKernel E t) (centeredSupportProjection T f))) ≤
      (t / 2) * residueVectorNorm f := by
  have he : rawAdditiveKernelAction (sparseAdditiveKernel E t) (centeredSupportProjection T f) =
      fun x => (t : ℂ) * finiteSpectralProjection E (centeredSupportProjection T f) x := by
    funext x
    exact sparseAdditiveKernel_action E t _ x
  rw [he, centeredSupportProjection_const_mul, residueVectorNorm_smul]
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht]
  have hh := mul_le_mul_of_nonneg_left (residueVectorNorm_cross_projection_le S T E hST f) ht
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  ring

theorem residueVectorNorm_square_kernel_le {p : ℕ} [NeZero p]
    (S T E : Finset (ZMod p)) (t ε : ℝ) (hε : 0 ≤ ε) (hE : (E.card : ℝ) ≤ ε * p)
    (f : ZMod p → ℂ) :
    residueVectorNorm (centeredSupportProjection S
      (rawAdditiveKernelAction (fun x => sparseAdditiveKernel E t x * sparseAdditiveKernel E t x)
        (centeredSupportProjection T f))) ≤ (t ^ 2 * ε) * residueVectorNorm f := by
  apply (residueVectorNorm_centered_le _ _).trans
  apply (residueVectorNorm_raw_le _ _ _ (mul_nonneg (sq_nonneg _) hε)
    (sparseAdditiveKernel_square_multiplier_le E t ε hE)).trans
  exact mul_le_mul_of_nonneg_left (residueVectorNorm_centered_le T f) (mul_nonneg (sq_nonneg _) hε)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Supply_BalancedKernelBlocks
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bounds for the actual balanced-support local kernel blocks -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

theorem balanced_uniform_norms {p : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (hS : S.Nonempty) (hSp : S.card < p)
    (hlo : (1 / 3 : ℝ) ≤ residueDensity S) (hhi : residueDensity S ≤ 2 / 3) :
    residueVectorNorm (uniformResidueVector S) ≤ 2 / Real.sqrt (p : ℝ) ∧
      residueVectorNorm (uniformResidueVector (Finset.univ \ S)) ≤ 2 / Real.sqrt (p : ℝ) := by
  have hp : (0 : ℝ) < p := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
  have hScard : (p : ℝ) / 3 ≤ S.card := by
    rw [residueDensity, le_div_iff₀ hp] at hlo
    linarith
  have hTcard : ((Finset.univ \ S).card : ℝ) = (p : ℝ) - S.card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ S), Finset.card_univ, ZMod.card,
      Nat.cast_sub hSp.le]
  have hT : (Finset.univ \ S).Nonempty := by
    rw [← Finset.card_pos]
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ S), Finset.card_univ, ZMod.card]
    omega
  refine ⟨uniformResidueVector_norm_le S hS hScard, uniformResidueVector_norm_le _ hT ?_⟩
  rw [hTcard]
  rw [residueDensity, div_le_iff₀ hp] at hhi
  linarith

theorem residue_side_norm_of_energy {p : ℕ} [NeZero p]
    (f : ZMod p → ℂ) (ε : ℝ) (hε : 0 ≤ ε)
    (henergy : (∑ x, ‖f x‖ ^ 2) ≤ 2 * ε ^ 2 / p) :
    residueVectorNorm f ≤ 2 * ε / Real.sqrt (p : ℝ) := by
  have hp : (0 : ℝ) < p := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
  apply (residueVectorNorm_le_iff _ _ (by positivity)).mpr
  apply henergy.trans
  rw [div_pow, Real.sq_sqrt hp.le, mul_pow]
  apply (div_le_div_iff_of_pos_right hp).mpr
  nlinarith [sq_nonneg ε]

theorem residueProjection_side_norms {p : ℕ} [NeZero p]
    (S E : Finset (ZMod p)) (hS : S.Nonempty) (hSp : S.card < p) (hE : 0 ∉ E)
    (hlo : (1 / 3 : ℝ) ≤ residueDensity S) (hhi : residueDensity S ≤ 2 / 3)
    (ε : ℝ) (hε : 0 ≤ ε)
    (herr : (∑ x, ‖normalizedResidueIndicator S x -
      finiteSpectralProjection E (normalizedResidueIndicator S) x‖ ^ 2) ≤ ε ^ 2 * p) :
    residueVectorNorm (centeredSupportProjection (Finset.univ \ S)
      (finiteSpectralProjection E (uniformResidueVector S))) ≤ 2 * ε / Real.sqrt (p : ℝ) ∧
    residueVectorNorm (centeredSupportProjection S
      (finiteSpectralProjection E (uniformResidueVector (Finset.univ \ S)))) ≤
        2 * ε / Real.sqrt (p : ℝ) := by
  obtain ⟨ha, hb⟩ := residueProjection_side_energy S E hS hSp hE hlo hhi ε herr
  exact ⟨residue_side_norm_of_energy _ ε hε ha, residue_side_norm_of_energy _ ε hε hb⟩

/-- The squared kernel's scalar contribution is O(epsilon/p), rather than
O(epsilon). This retains both uniform-support normalization factors. -/
theorem squareKernel_scalar_norm_le {p : ℕ} [NeZero p]
    (S E : Finset (ZMod p)) (hS : S.Nonempty) (hSp : S.card < p)
    (hlo : (1 / 3 : ℝ) ≤ residueDensity S) (hhi : residueDensity S ≤ 2 / 3)
    (t ε : ℝ) (hε : 0 ≤ ε) (hE : (E.card : ℝ) ≤ ε * p) :
    ‖residueKernelScalar S (fun x => sparseAdditiveKernel E t x * sparseAdditiveKernel E t x)‖ ≤
      4 * t ^ 2 * ε / p := by
  have hp : (0 : ℝ) < p := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
  obtain ⟨ha, hb⟩ := balanced_uniform_norms S hS hSp hlo hhi
  unfold residueKernelScalar
  apply (residueVectorNorm_inner_le _ _).trans
  have hraw := residueVectorNorm_raw_le
    (fun x => sparseAdditiveKernel E t x * sparseAdditiveKernel E t x)
    (uniformResidueVector (Finset.univ \ S)) (t ^ 2 * ε) (mul_nonneg (sq_nonneg _) hε)
    (sparseAdditiveKernel_square_multiplier_le E t ε hE)
  calc
    _ ≤ (2 / Real.sqrt (p : ℝ)) * ((t ^ 2 * ε) * (2 / Real.sqrt (p : ℝ))) :=
      mul_le_mul ha (hraw.trans (mul_le_mul_of_nonneg_left hb (by positivity)))
        (residueVectorNorm_nonneg _) (by positivity)
    _ = _ := by
      have hs := Real.sq_sqrt hp.le
      field_simp
      rw [hs]
      ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_FiniteKernelBlocks
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Concrete side and lower blocks of the finite kernel matrix -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

theorem residueKernelSide_sparse_norm {p : ℕ} [NeZero p]
    (S T E : Finset (ZMod p)) (t : ℝ) :
    residueVectorNorm (residueKernelSide S T (sparseAdditiveKernel E t)) =
      |t| * residueVectorNorm (centeredSupportProjection S
        (finiteSpectralProjection E (uniformResidueVector T))) := by
  have he : rawAdditiveKernelAction (sparseAdditiveKernel E t) (uniformResidueVector T) =
      fun x => (t : ℂ) * finiteSpectralProjection E (uniformResidueVector T) x := by
    funext x
    exact sparseAdditiveKernel_action E t _ x
  rw [residueKernelSide, he, centeredSupportProjection_const_mul, residueVectorNorm_smul]
  simp only [Complex.norm_real, Real.norm_eq_abs]

theorem residueKernelSide_square_norm_le {p : ℕ} [NeZero p]
    (S T E : Finset (ZMod p)) (t ε : ℝ) (hε : 0 ≤ ε) (hE : (E.card : ℝ) ≤ ε * p) :
    residueVectorNorm (residueKernelSide S T
      (fun x => sparseAdditiveKernel E t x * sparseAdditiveKernel E t x)) ≤
      (t ^ 2 * ε) * residueVectorNorm (uniformResidueVector T) := by
  apply (residueVectorNorm_centered_le _ _).trans
  exact residueVectorNorm_raw_le _ _ _ (mul_nonneg (sq_nonneg _) hε)
    (sparseAdditiveKernel_square_multiplier_le E t ε hE)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_SparseKernelLocalBlocks
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual local blocks of `(1+b)^2` at the fixed parameter `17/20` -/

namespace Ostmann
open scoped Classical BigOperators

theorem localSparseSide_norm_le {p : ℕ} [NeZero p]
    (S T E : Finset (ZMod p)) (ε : ℝ) (hε : 0 ≤ ε) (hE : (E.card : ℝ) ≤ ε * p)
    (hproj : residueVectorNorm (centeredSupportProjection S
      (finiteSpectralProjection E (uniformResidueVector T))) ≤ 2 * ε / Real.sqrt (p : ℝ))
    (hu : residueVectorNorm (uniformResidueVector T) ≤ 2 / Real.sqrt (p : ℝ)) :
    residueVectorNorm (localSparseSide S T E) ≤ 6 * ε / Real.sqrt (p : ℝ) := by
  apply (residueVectorNorm_add_le _ _).trans
  rw [residueVectorNorm_smul]
  rw [show ‖(2 : ℂ)‖ = (2 : ℝ) by norm_num]
  have h1 := residueKernelSide_sparse_norm S T E (17 / 20)
  norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 17 / 20)] at h1
  have h2 := residueKernelSide_square_norm_le S T E (17 / 20) ε hε hE
  change residueVectorNorm (residueKernelSide S T (localSparseSquare E)) ≤ _ at h2
  have h3 := mul_le_mul_of_nonneg_left hproj (by norm_num : (0 : ℝ) ≤ 17 / 20)
  rw [← h1] at h3
  have h4 := h2.trans (mul_le_mul_of_nonneg_left hu (by positivity))
  have hn : 0 ≤ ε / Real.sqrt (p : ℝ) := by positivity
  dsimp only [localSparseKernel] at *
  calc
    _ ≤ 2 * ((17 / 20) * (2 * ε / Real.sqrt (p : ℝ))) +
        (17 / 20) ^ 2 * ε * (2 / Real.sqrt (p : ℝ)) :=
      add_le_add (mul_le_mul_of_nonneg_left h3 (by norm_num)) h4
    _ = (969 / 200 : ℝ) * (ε / Real.sqrt (p : ℝ)) := by ring
    _ ≤ 6 * (ε / Real.sqrt (p : ℝ)) := mul_le_mul_of_nonneg_right (by norm_num) hn
    _ = _ := by ring

theorem localSparseLower_norm_le {p : ℕ} [NeZero p]
    (S T E : Finset (ZMod p)) (hST : Disjoint S T)
    (ε : ℝ) (hε : 0 ≤ ε) (hεsmall : ε ≤ 1 / 1000000) (hE : (E.card : ℝ) ≤ ε * p)
    (f : ZMod p → ℂ) :
    residueVectorNorm (localSparseLower S T E f) ≤ (9 / 10 : ℝ) * residueVectorNorm f := by
  apply (residueVectorNorm_add_le _ _).trans
  rw [residueVectorNorm_smul]
  rw [show ‖(2 : ℂ)‖ = (2 : ℝ) by norm_num]
  have h1 := residueVectorNorm_cross_kernel_le S T E hST (17 / 20) (by norm_num) f
  have h2 := residueVectorNorm_square_kernel_le S T E (17 / 20) ε hε hE f
  change residueVectorNorm (residueKernelLower S T (localSparseKernel E) f) ≤ _ at h1
  change residueVectorNorm (residueKernelLower S T (localSparseSquare E) f) ≤ _ at h2
  have hcoef : (2 : ℝ) * ((17 / 20) / 2) + (17 / 20) ^ 2 * ε ≤ 9 / 10 := by linarith
  have hh := mul_le_mul_of_nonneg_right hcoef (residueVectorNorm_nonneg f)
  nlinarith only [h1, h2, hh]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_SparseKernelScalarRange
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Real scalar range of the sparse kernel -/

namespace Ostmann
open scoped Classical BigOperators

theorem residueKernelScalar_sparse_real {p : ℕ} [NeZero p]
    (S E : Finset (ZMod p)) (hS : S.Nonempty) (hSp : S.card < p) (hE : 0 ∉ E)
    (t : ℝ) :
    (residueKernelScalar S (sparseAdditiveKernel E t)).im = 0 := by
  rw [residueKernelScalar_sparse S E hS hSp hE]
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_pow, ← Complex.ofReal_neg,
    ← Complex.ofReal_div, ← Complex.ofReal_mul, Complex.ofReal_im]

theorem residueKernelScalar_sparse_lower {p : ℕ} [NeZero p]
    (S E : Finset (ZMod p)) (hS : S.Nonempty) (hSp : S.card < p) (hE : 0 ∉ E)
    (t : ℝ) (ht : 0 ≤ t) :
    -t / p ≤ (residueKernelScalar S (sparseAdditiveKernel E t)).re := by
  have hp : (0 : ℝ) < p := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
  have hen : (∑ x, ‖finiteSpectralProjection E (normalizedResidueIndicator S) x‖ ^ 2) ≤ p := by
    simpa only [normalizedResidueIndicator_energy S hS hSp] using
      finiteSpectralProjection_energy_le E (normalizedResidueIndicator S)
  have he : residueKernelScalar S (sparseAdditiveKernel E t) =
      ((-t / (p : ℝ) ^ 2 *
        ∑ x, ‖finiteSpectralProjection E (normalizedResidueIndicator S) x‖ ^ 2 : ℝ) : ℂ) := by
    rw [residueKernelScalar_sparse S E hS hSp hE]
    push_cast
    rfl
  rw [he, Complex.ofReal_re]
  calc
    _ = -t / (p : ℝ) ^ 2 * p := by field_simp
    _ ≤ _ := mul_le_mul_of_nonpos_left hen (div_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg _))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_SparseKernelMeans
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact nonzero-residue sums for the sparse additive kernel -/

namespace Ostmann
open scoped Classical BigOperators

theorem sum_eq_mul_additiveFourier_zero {p : ℕ} [NeZero p] (f : ZMod p → ℂ) :
    (∑ x, f x) = (p : ℂ) * additiveFourier f 0 := by
  have hp : (p : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne p
  simp only [additiveFourier_apply, mul_zero, neg_zero, AddChar.map_zero_eq_one, mul_one,
    ← mul_assoc, mul_inv_cancel₀ hp, one_mul]

theorem sparseAdditiveKernel_zero {p : ℕ} [NeZero p]
    (E : Finset (ZMod p)) (t : ℝ) :
    sparseAdditiveKernel E t 0 = (t : ℂ) * E.card / p := by
  rw [sparseAdditiveKernel_formula]
  simp only [mul_zero, AddChar.map_zero_eq_one, Finset.sum_const, nsmul_eq_mul, mul_one]
  ring

theorem sparseAdditiveKernel_sum {p : ℕ} [NeZero p]
    (E : Finset (ZMod p)) (hE : 0 ∉ E) (t : ℝ) :
    (∑ x, sparseAdditiveKernel E t x) = 0 := by
  rw [sum_eq_mul_additiveFourier_zero, sparseAdditiveKernel_fourier,
    ite_eq_right hE, mul_zero, mul_zero]

theorem sparseAdditiveKernel_sum_nonzero {p : ℕ} [NeZero p]
    (E : Finset (ZMod p)) (hE : 0 ∉ E) (t : ℝ) :
    (∑ x ∈ Finset.univ.erase 0, sparseAdditiveKernel E t x) = -(t : ℂ) * E.card / p := by
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ _), sparseAdditiveKernel_sum E hE,
    sparseAdditiveKernel_zero]
  ring

theorem sparseAdditiveKernel_square_sum {p : ℕ} [NeZero p]
    (E : Finset (ZMod p)) (hE : ∀ b, -b ∈ E ↔ b ∈ E) (t : ℝ) :
    (∑ x, sparseAdditiveKernel E t x * sparseAdditiveKernel E t x) =
      (t : ℂ) ^ 2 * E.card / p := by
  have hp : (p : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne p
  have he : E.filter (fun b => (0 : ZMod p) - b ∈ E) = E := by
    ext b
    simp only [Finset.mem_filter, zero_sub, hE b, and_self]
  rw [sum_eq_mul_additiveFourier_zero, sparseAdditiveKernel_square_fourier, he]
  field_simp

theorem sparseAdditiveKernel_square_sum_nonzero {p : ℕ} [NeZero p]
    (E : Finset (ZMod p)) (hE : ∀ b, -b ∈ E ↔ b ∈ E) (t : ℝ) :
    (∑ x ∈ Finset.univ.erase 0, sparseAdditiveKernel E t x * sparseAdditiveKernel E t x) =
      (t : ℂ) ^ 2 * ((E.card : ℂ) / p - ((E.card : ℂ) / p) ^ 2) := by
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ _), sparseAdditiveKernel_square_sum E hE,
    sparseAdditiveKernel_zero]
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_SparseKernelUnitFactor
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The unit-residue normalizing factor at the fixed kernel parameter -/

namespace Ostmann
open scoped Classical BigOperators

theorem sparseKernelUnitFactor_lower (p e ε : ℝ) (hp : 2 ≤ p)
    (he : 0 ≤ e) (heε : e ≤ ε) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    1 - 4 * ε / p ≤ sparseKernelUnitFactor p e := by
  have hp0 : 0 < p := by linarith
  have hp1 : 0 < p - 1 := by linarith
  have hn : -2 * ε ≤ ((17 / 20 : ℝ) ^ 2) * (e - e ^ 2) - (17 / 10) * e := by
    have he1 : e ≤ 1 := heε.trans hε1
    nlinarith
  have hfrac : -4 * ε / p ≤ -2 * ε / (p - 1) := by
    apply (div_le_div_iff₀ hp0 hp1).mpr
    nlinarith [mul_nonneg hε0 (sub_nonneg.mpr hp)]
  unfold sparseKernelUnitFactor
  calc
    1 - 4 * ε / p = 1 + (-4 * ε / p) := by ring
    _ ≤ 1 + (-2 * ε / (p - 1)) := add_le_add le_rfl hfrac
    _ ≤ _ := add_le_add le_rfl ((div_le_div_iff_of_pos_right hp1).mpr hn)

theorem sparseKernelUnitFactor_positive (p e ε : ℝ) (hp : 100 ≤ p)
    (he : 0 ≤ e) (heε : e ≤ ε) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 1000000) :
    0 < sparseKernelUnitFactor p e := by
  have hp0 : 0 < p := by linarith
  have hh := sparseKernelUnitFactor_lower p e ε (by linarith) he heε hε0 (by linarith)
  have heps : 4 * ε / p < 1 := (div_lt_one hp0).mpr (by linarith)
  linarith

/-- The closed expression is the actual mean of `(1+b)^2` on nonzero
residues, with `b` the manuscript's fixed `17/20` kernel. -/
theorem sparseKernelUnitFactor_mean {p : ℕ} [NeZero p]
    (E : Finset (ZMod p)) (hE : 0 ∉ E) (hsym : ∀ b, -b ∈ E ↔ b ∈ E)
    (hp : 1 < p) :
    ((sparseKernelUnitFactor p ((E.card : ℝ) / p) : ℝ) : ℂ) =
      ((p : ℂ) - 1)⁻¹ * ∑ x ∈ Finset.univ.erase 0,
        (1 + sparseAdditiveKernel E (17 / 20) x) ^ 2 := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne p
  have hp1 : (p : ℂ) - 1 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hp.ne')
  have hc : ((Finset.univ.erase (0 : ZMod p)).card : ℂ) = (p : ℂ) - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ZMod.card,
      Nat.cast_sub (by omega : 1 ≤ p), Nat.cast_one]
  have he (x : ZMod p) : (1 + sparseAdditiveKernel E (17 / 20) x) ^ 2 =
      1 + 2 * sparseAdditiveKernel E (17 / 20) x +
        sparseAdditiveKernel E (17 / 20) x * sparseAdditiveKernel E (17 / 20) x := by ring
  simp_rw [he]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    sparseAdditiveKernel_sum_nonzero E hE, sparseAdditiveKernel_square_sum_nonzero E hsym]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, hc]
  unfold sparseKernelUnitFactor
  push_cast
  field_simp
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_SparseKernelNumerics
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Fixed numerical margins in the local contraction -/

namespace Ostmann

/-- The scalar decrease survives both the square kernel and the cost of the
side blocks. The fixed epsilon here is deliberately smaller than necessary. -/
theorem sparse_kernel_numeric_margin (p ε s U : ℝ) (hp : 100 ≤ p)
    (hε : 0 ≤ ε) (hεsmall : ε ≤ 1 / 1000000)
    (hs : s ≤ 1 - (17 / 10) * (1 - ε ^ 2) / p + (289 / 100) * ε / p)
    (hU : 1 - 4 * ε / p ≤ U) :
    s + 20 * (6 * ε / Real.sqrt p) ^ 2 ≤ U * (1 - (8 / 5) / p) := by
  have hp0 : 0 < p := by linarith
  have hsq : ε ^ 2 ≤ ε := by nlinarith
  have hbudget : (17 / 10 + 720) * ε ^ 2 + (289 / 100) * ε ≤ (1 / 100 : ℝ) := by
    nlinarith
  have hscale : 20 * (6 * ε / Real.sqrt p) ^ 2 = 720 * ε ^ 2 / p := by
    rw [div_pow, Real.sq_sqrt hp0.le]
    ring
  have hleft : s + 720 * ε ^ 2 / p ≤ 1 - (169 / 100) / p := by
    have hm := mul_le_mul_of_nonneg_right hs hp0.le
    simp only [add_mul, sub_mul, one_mul, div_mul_cancel₀ _ hp0.ne'] at hm
    apply (mul_le_mul_iff_of_pos_right hp0).mp
    simp only [add_mul, sub_mul, one_mul, div_mul_cancel₀ _ hp0.ne']
    nlinarith
  have hf : 0 ≤ 1 - (8 / 5) / p := by
    have hh : (8 / 5 : ℝ) / p ≤ 1 := (div_le_one hp0).mpr (by linarith)
    linarith
  rw [hscale]
  apply hleft.trans
  apply le_trans _ (mul_le_mul_of_nonneg_right hU hf)
  have hsmall : 4 * ε ≤ (1 / 100 : ℝ) := by linarith
  have hmain : 1 - (169 / 100) / p ≤ 1 - ((8 / 5) + 4 * ε) / p := by
    have hn : (8 / 5) + 4 * ε ≤ (169 / 100 : ℝ) := by linarith
    exact sub_le_sub_left ((div_le_div_iff_of_pos_right hp0).mpr hn) 1
  apply hmain.trans
  have hpos : 0 ≤ (4 * ε / p) * ((8 / 5) / p) := by positivity
  calc
    _ = (1 - 4 * ε / p) * (1 - (8 / 5) / p) -
        (4 * ε / p) * ((8 / 5) / p) := by rw [add_div]; ring
    _ ≤ _ := sub_le_self _ hpos

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_SparseScalarNorm
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The scalar block stays positive while retaining its decrease -/

namespace Ostmann

theorem sparse_scalar_norm_bounds (p ε a : ℝ) (b : ℂ) (hp : 100 ≤ p)
    (hε : 0 ≤ ε) (hεsmall : ε ≤ 1 / 1000000)
    (ha0 : -(17 / 20) / p ≤ a)
    (ha1 : a ≤ -(17 / 20) * (1 - ε ^ 2) / p)
    (hb : ‖b‖ ≤ (289 / 100) * ε / p) :
    (19 / 20 : ℝ) ≤ ‖((1 + 2 * a : ℝ) : ℂ) + b‖ ∧
      ‖((1 + 2 * a : ℝ) : ℂ) + b‖ ≤
        1 - (17 / 10) * (1 - ε ^ 2) / p + (289 / 100) * ε / p := by
  have hp0 : 0 < p := by linarith
  have hsmall : ((17 / 10) + (289 / 100) * ε) / p ≤ (1 / 20 : ℝ) := by
    apply (div_le_iff₀ hp0).mpr
    linarith
  have hbase : 0 ≤ 1 + 2 * a := by
    have he : 2 * (-(17 / 20) / p) = -(17 / 10) / p := by ring
    have hdiv : (17 / 10) / p ≤ (1 / 20 : ℝ) := by
      apply le_trans _ hsmall
      apply (div_le_div_iff_of_pos_right hp0).mpr
      linarith
    have hh := mul_le_mul_of_nonneg_left ha0 (by norm_num : (0 : ℝ) ≤ 2)
    rw [he] at hh
    simp only [neg_div] at hh
    linarith
  have hnorm : ‖((1 + 2 * a : ℝ) : ℂ)‖ = 1 + 2 * a := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hbase]
  constructor
  · have hh := norm_add_le (((1 + 2 * a : ℝ) : ℂ) + b) (-b)
    simp only [add_neg_cancel_right, norm_neg, hnorm] at hh
    have he : 2 * (-(17 / 20) / p) = -(17 / 10) / p := by ring
    have hx := mul_le_mul_of_nonneg_left ha0 (by norm_num : (0 : ℝ) ≤ 2)
    rw [he] at hx
    simp only [neg_div] at hx
    rw [add_div] at hsmall
    linarith
  · have hh := norm_add_le (((1 + 2 * a : ℝ) : ℂ)) b
    rw [hnorm] at hh
    have he : 2 * (-(17 / 20) * (1 - ε ^ 2) / p) =
        -(17 / 10) * (1 - ε ^ 2) / p := by ring
    have hx := mul_le_mul_of_nonneg_left ha1 (by norm_num : (0 : ℝ) ≤ 2)
    rw [he] at hx
    simp only [neg_mul, neg_div] at hx
    linarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Supply_LocalSparseKernelContraction
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The contracting local sparse block at `(u,v)=(1,1)` -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

/-- The finite local contraction in Lemma 5.2, with the actual sparse spectrum,
actual residue vectors, and the exact nonzero-residue normalizing factor. -/
theorem local_sparse_kernel_contraction {p : ℕ} [Fact p.Prime]
    (S : Finset (ZMod p)) (hS : S.Nonempty) (hSp : S.card < p)
    (hp : (100 : ℝ) ≤ p)
    (hlo : (1 / 3 : ℝ) ≤ residueDensity S) (hhi : residueDensity S ≤ 2 / 3)
    (ε : ℝ) (hε : 0 ≤ ε) (hεsmall : ε ≤ 1 / 1000000)
    (hL1 : (p : ℝ)⁻¹ * ∑ b, ‖normalizedResidueTransform S b‖ ≤ ε ^ 2) :
    let E := largeTransformSpectrum (normalizedResidueTransform S)
    let T := Finset.univ \ S
    let U := sparseKernelUnitFactor p ((E.card : ℝ) / p)
    0 < U ∧
      ((U : ℝ) : ℂ) = ((p : ℂ) - 1)⁻¹ * ∑ x ∈ Finset.univ.erase 0,
        (1 + localSparseKernel E x) ^ 2 ∧
      ∀ (z : ℂ) (f : ZMod p → ℂ),
        ‖localSparseScalar S E * z + ∑ x, conj (localSparseSide T S E x) * f x‖ ^ 2 +
          residueVectorNorm (fun x => z * localSparseSide S T E x + localSparseLower S T E f x) ^ 2 ≤
            (U * (1 - (8 / 5) / p)) ^ 2 * (‖z‖ ^ 2 + residueVectorNorm f ^ 2) := by
  intro E T U
  have hp0 : (0 : ℝ) < p := by linarith
  have hpNat : 1 < p := by
    have hh : (1 : ℝ) < p := lt_of_lt_of_le (by norm_num) hp
    exact_mod_cast hh
  obtain ⟨hz, hn, hc, _hconst, he, herr⟩ := sparse_residue_projection S hS hSp ε hε (by linarith) hL1
  have hratio : (E.card : ℝ) / p ≤ ε := (div_le_iff₀ hp0).mpr hc
  have hratio0 : 0 ≤ (E.card : ℝ) / p := by positivity
  have hU := sparseKernelUnitFactor_lower p ((E.card : ℝ) / p) ε (by linarith)
    hratio0 hratio hε (by linarith)
  refine ⟨sparseKernelUnitFactor_positive p _ ε hp hratio0 hratio hε hεsmall, ?_, ?_⟩
  · exact sparseKernelUnitFactor_mean E hz hn hpNat
  · intro z f
    let a₁ := residueKernelScalar S (localSparseKernel E)
    let a₂ := residueKernelScalar S (localSparseSquare E)
    have ha0 := residueKernelScalar_sparse_lower S E hS hSp hz (17 / 20) (by norm_num)
    have ha1 := residueKernelScalar_sparse_re_le S E hS hSp hz (17 / 20) ε (by norm_num) he
    change a₁.re ≤ -(17 / 20 * (1 - ε ^ 2)) / p at ha1
    have ha2 := squareKernel_scalar_norm_le S E hS hSp hlo hhi (17 / 20) ε hε hc
    change ‖a₂‖ ≤ _ at ha2
    norm_num at ha2
    have har : a₁ = (a₁.re : ℂ) := by
      apply Complex.ext
      · rfl
      · simpa only [Complex.ofReal_im, a₁, localSparseKernel] using residueKernelScalar_sparse_real S E hS hSp hz (17 / 20)
    have haeq : localSparseScalar S E = ((1 + 2 * a₁.re : ℝ) : ℂ) + a₂ := by
      change 1 + 2 * a₁ + a₂ = _
      rw [har]
      push_cast
      rfl
    have has := sparse_scalar_norm_bounds p ε a₁.re a₂ hp hε hεsmall ha0 (by
      convert ha1 using 1
      all_goals try with_reducible_and_instances rfl
      ring) ha2
    rw [← haeq] at has
    obtain ⟨hproj₁, hproj₂⟩ := residueProjection_side_norms S E hS hSp hz hlo hhi ε hε herr
    obtain ⟨hu₁, hu₂⟩ := balanced_uniform_norms S hS hSp hlo hhi
    have hrow := localSparseSide_norm_le T S E ε hε hc hproj₁ hu₁
    have hcol := localSparseSide_norm_le S T E ε hε hc hproj₂ hu₂
    have hST : Disjoint S T := by
      apply Finset.disjoint_left.mpr
      intro x hx hxT
      exact (Finset.mem_sdiff.mp hxT).2 hx
    have hC := localSparseLower_norm_le S T E hST ε hε hεsmall hc
    have hblock := residue_block_energy (localSparseScalar S E)
      (localSparseSide T S E) (localSparseSide S T E) (localSparseLower S T E)
      ‖localSparseScalar S E‖ (9 / 10) (6 * ε / Real.sqrt (p : ℝ))
      (norm_nonneg _) (by norm_num) (by linarith [has.1]) le_rfl hrow hcol hC z f
    have hM := sparse_kernel_numeric_margin p ε ‖localSparseScalar S E‖ U hp hε hεsmall has.2 hU
    apply hblock.trans
    apply mul_le_mul_of_nonneg_right _ (add_nonneg (sq_nonneg _) (sq_nonneg _))
    exact pow_le_pow_left₀ (by positivity) hM 2

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_SparsePolydiscScalar
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Scalar control on the polydisc used for kernel truncation -/

namespace Ostmann
open scoped Classical BigOperators

theorem residueKernelScalar_sparse_norm_le {p : ℕ} [NeZero p]
    (S E : Finset (ZMod p)) (hS : S.Nonempty) (hSp : S.card < p) (hE : 0 ∉ E)
    (t : ℝ) (ht : 0 ≤ t) :
    ‖residueKernelScalar S (sparseAdditiveKernel E t)‖ ≤ t / p := by
  let a := residueKernelScalar S (sparseAdditiveKernel E t)
  have hreal : a = (a.re : ℂ) := by
    apply Complex.ext
    · rfl
    · simpa only [Complex.ofReal_im, a] using residueKernelScalar_sparse_real S E hS hSp hE t
  have hlo := residueKernelScalar_sparse_lower S E hS hSp hE t ht
  have hhi := residueKernelScalar_sparse_re_le S E hS hSp hE t 1 ht (by norm_num; positivity)
  have hhi' : a.re ≤ 0 := by simpa only [one_pow, sub_self, mul_zero, neg_zero, zero_div] using hhi
  change ‖a‖ ≤ _
  rw [hreal, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos hhi']
  change -t / p ≤ a.re at hlo
  simpa only [neg_div, neg_neg] using neg_le_neg hlo

theorem polydisc_scalar_error_bound (p ε : ℝ) (a b c d : ℂ) (hp : 0 < p)
    (hε : 0 ≤ ε) (hεsmall : ε ≤ 1 / 1000000)
    (ha : ‖a‖ ≤ (17 / 20) / p) (hb : ‖b‖ ≤ (289 / 100) * ε / p)
    (hc : ‖c‖ ≤ 103 / 50) (hd : ‖d‖ ≤ 10609 / 10000) :
    ‖c * a + d * b‖ ≤ 2 / p := by
  apply (norm_add_le _ _).trans
  rw [norm_mul, norm_mul]
  apply (add_le_add (mul_le_mul hc ha (norm_nonneg _) (by norm_num))
    (mul_le_mul hd hb (norm_nonneg _) (by norm_num))).trans
  apply (le_div_iff₀ hp).mpr
  have he : ((103 / 50) * ((17 / 20) / p) +
      (10609 / 10000) * ((289 / 100) * ε / p)) * p =
      (103 / 50) * (17 / 20) + (10609 / 10000) * ((289 / 100) * ε) := by
    field_simp
  rw [he]
  linarith

theorem polydisc_scalar_norm_bounds (p ε : ℝ) (a b c d : ℂ) (hp : 100 ≤ p)
    (hε : 0 ≤ ε) (hεsmall : ε ≤ 1 / 1000000)
    (ha : ‖a‖ ≤ (17 / 20) / p) (hb : ‖b‖ ≤ (289 / 100) * ε / p)
    (hc : ‖c‖ ≤ 103 / 50) (hd : ‖d‖ ≤ 10609 / 10000) :
    (19 / 20 : ℝ) ≤ ‖1 + c * a + d * b‖ ∧ ‖1 + c * a + d * b‖ ≤ 1 + 2 / p := by
  have hp0 : 0 < p := by linarith
  have he := polydisc_scalar_error_bound p ε a b c d hp0 hε hεsmall ha hb hc hd
  have hrewrite : 1 + c * a + d * b = 1 + (c * a + d * b) := by ring
  rw [hrewrite]
  constructor
  · have hh := norm_add_le (1 + (c * a + d * b)) (-(c * a + d * b))
    simp only [add_neg_cancel_right, norm_one, norm_neg] at hh
    have hpbound : 2 / p ≤ (1 / 20 : ℝ) := (div_le_iff₀ hp0).mpr (by linarith)
    linarith
  · exact (norm_add_le _ _).trans (by simpa only [norm_one] using add_le_add le_rfl he)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_SparsePolydiscBlocks
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform side and lower bounds on the complex parameter polydisc -/

namespace Ostmann
open scoped Classical BigOperators

theorem polydiscSparseSide_norm_le {p : ℕ} [NeZero p]
    (S T E : Finset (ZMod p)) (ε : ℝ) (hε : 0 ≤ ε) (hE : (E.card : ℝ) ≤ ε * p)
    (c d : ℂ) (hc : ‖c‖ ≤ 103 / 50) (hd : ‖d‖ ≤ 10609 / 10000)
    (hproj : residueVectorNorm (centeredSupportProjection S
      (finiteSpectralProjection E (uniformResidueVector T))) ≤ 2 * ε / Real.sqrt (p : ℝ))
    (hu : residueVectorNorm (uniformResidueVector T) ≤ 2 / Real.sqrt (p : ℝ)) :
    residueVectorNorm (polydiscSparseSide S T E c d) ≤ 6 * ε / Real.sqrt (p : ℝ) := by
  apply (residueVectorNorm_add_le _ _).trans
  rw [residueVectorNorm_smul, residueVectorNorm_smul]
  let q := ε / Real.sqrt (p : ℝ)
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have h1 : residueVectorNorm (residueKernelSide S T (localSparseKernel E)) ≤ (17 / 10) * q := by
    rw [localSparseKernel, residueKernelSide_sparse_norm]
    norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 17 / 20)]
    apply (mul_le_mul_of_nonneg_left hproj (by norm_num : (0 : ℝ) ≤ 17 / 20)).trans_eq
    dsimp [q]
    ring
  have h2 : residueVectorNorm (residueKernelSide S T (localSparseSquare E)) ≤ (289 / 200) * q := by
    apply (residueKernelSide_square_norm_le S T E (17 / 20) ε hε hE).trans
    apply (mul_le_mul_of_nonneg_left hu (by positivity : (0 : ℝ) ≤ (17 / 20) ^ 2 * ε)).trans_eq
    dsimp [q]
    ring
  have hh := add_le_add (mul_le_mul hc h1 (residueVectorNorm_nonneg _) (by norm_num))
    (mul_le_mul hd h2 (residueVectorNorm_nonneg _) (by norm_num))
  have hlast : (103 / 50) * ((17 / 10) * q) +
      (10609 / 10000) * ((289 / 200) * q) ≤ 6 * ε / Real.sqrt (p : ℝ) := by
    have he : 6 * ε / Real.sqrt (p : ℝ) = 6 * q := by dsimp [q]; ring
    rw [he]
    nlinarith only [hq]
  exact hh.trans hlast

theorem polydiscSparseLower_norm_le {p : ℕ} [NeZero p]
    (S T E : Finset (ZMod p)) (hST : Disjoint S T)
    (ε : ℝ) (hε : 0 ≤ ε) (hεsmall : ε ≤ 1 / 1000000) (hE : (E.card : ℝ) ≤ ε * p)
    (c d : ℂ) (hc : ‖c‖ ≤ 103 / 50) (hd : ‖d‖ ≤ 10609 / 10000)
    (f : ZMod p → ℂ) :
    residueVectorNorm (polydiscSparseLower S T E c d f) ≤ (9 / 10 : ℝ) * residueVectorNorm f := by
  apply (residueVectorNorm_add_le _ _).trans
  rw [residueVectorNorm_smul, residueVectorNorm_smul]
  have h1 := residueVectorNorm_cross_kernel_le S T E hST (17 / 20) (by norm_num) f
  have h2 := residueVectorNorm_square_kernel_le S T E (17 / 20) ε hε hE f
  have hh := add_le_add (mul_le_mul hc h1 (residueVectorNorm_nonneg _) (by norm_num))
    (mul_le_mul hd h2 (residueVectorNorm_nonneg _) (by norm_num))
  have hcoef : (103 / 50) * ((17 / 20) / 2) +
      (10609 / 10000) * ((17 / 20) ^ 2 * ε) ≤ (9 / 10 : ℝ) := by linarith
  apply hh.trans
  have he : (103 / 50) * ((17 / 20 / 2) * residueVectorNorm f) +
      (10609 / 10000) * ((17 / 20) ^ 2 * ε * residueVectorNorm f) =
      ((103 / 50) * ((17 / 20) / 2) + (10609 / 10000) * ((17 / 20) ^ 2 * ε)) *
        residueVectorNorm f := by ring
  rw [he]
  exact mul_le_mul_of_nonneg_right hcoef (residueVectorNorm_nonneg f)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_FiniteKernelLinearMaps
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Linear maps for the concrete finite kernel blocks -/

namespace Ostmann
open scoped Classical BigOperators

theorem polydiscLowerLinearMap_apply {p : ℕ} [NeZero p]
    (S T E : Finset (ZMod p)) (c d : ℂ) (f : ZMod p → ℂ) :
    polydiscLowerLinearMap S T E c d f = polydiscSparseLower S T E c d f := rfl

theorem residuePointVector_expansion {p : ℕ} [NeZero p] (f : ZMod p → ℂ) :
    f = ∑ y, f y • residuePointVector y := by
  funext x
  simp [residuePointVector, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

theorem finiteLinearMap_point_expansion {p : ℕ} [NeZero p]
    (L : (ZMod p → ℂ) →ₗ[ℂ] (ZMod p → ℂ)) (f : ZMod p → ℂ) (x : ZMod p) :
    L f x = ∑ y, L (residuePointVector y) x * f y := by
  have he := congrArg (fun g : ZMod p → ℂ => L g x) (residuePointVector_expansion f)
  rw [map_sum] at he
  simpa only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm] using he

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_TensorKernelEnergy
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Tensoring finite kernel energy bounds without a dimension factor -/

namespace Ostmann
open scoped Classical BigOperators

/-- Slice first in one coordinate and then in the other. The two operator
bounds multiply; the cardinalities of the coordinate spaces never enter. -/
theorem tensorKernel_energy_le {α β γ δ : Type*}
    [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (M : α → β → ℂ) (N : γ → δ → ℂ) (A B : ℝ)
    (hM : ∀ f : β → ℂ, (∑ x, ‖∑ y, M x y * f y‖ ^ 2) ≤ A ^ 2 * ∑ y, ‖f y‖ ^ 2)
    (hN : ∀ f : δ → ℂ, (∑ x, ‖∑ y, N x y * f y‖ ^ 2) ≤ B ^ 2 * ∑ y, ‖f y‖ ^ 2)
    (f : β × δ → ℂ) :
    (∑ x, ‖∑ y, tensorKernel M N x y * f y‖ ^ 2) ≤
      (A * B) ^ 2 * ∑ y, ‖f y‖ ^ 2 := by
  have he (x : α) (z : γ) : (∑ y, tensorKernel M N (x, z) y * f y) =
      ∑ y, M x y * ∑ w, N z w * f (y, w) := by
    rw [Fintype.sum_prod_type]
    simp only [tensorKernel, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    apply Finset.sum_congr rfl
    intro w _
    ring
  rw [Fintype.sum_prod_type]
  simp_rw [he]
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ z, A ^ 2 * ∑ y, ‖∑ w, N z w * f (y, w)‖ ^ 2 :=
      Finset.sum_le_sum fun z _ => hM (fun y => ∑ w, N z w * f (y, w))
    _ = A ^ 2 * ∑ y, ∑ z, ‖∑ w, N z w * f (y, w)‖ ^ 2 := by
      rw [← Finset.mul_sum, Finset.sum_comm]
    _ ≤ A ^ 2 * ∑ y, B ^ 2 * ∑ w, ‖f (y, w)‖ ^ 2 :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun y _ => hN (fun w => f (y, w))) (sq_nonneg _)
    _ = _ := by rw [← Finset.mul_sum, Fintype.sum_prod_type, mul_pow]; ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Supply_FiniteTensorKernel
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite products of the local residue matrices -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

universe u v

theorem kernel_energy_reindex {α β γ δ : Type*}
    [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (M : α → β → ℂ) (A : ℝ)
    (hM : ∀ f : β → ℂ, (∑ x, ‖∑ y, M x y * f y‖ ^ 2) ≤ A ^ 2 * ∑ y, ‖f y‖ ^ 2)
    (e : γ ≃ α) (d : δ ≃ β) (f : δ → ℂ) :
    (∑ x, ‖∑ y, M (e x) (d y) * f y‖ ^ 2) ≤ A ^ 2 * ∑ y, ‖f y‖ ^ 2 := by
  have hi (x : γ) : (∑ y, M (e x) (d y) * f y) =
      ∑ y, M (e x) y * f (d.symm y) := by
    exact Fintype.sum_equiv d _ _ (by intro y; simp)
  simp_rw [hi]
  rw [e.sum_comp (fun x => ‖∑ y, M x y * f (d.symm y)‖ ^ 2)]
  convert hM (fun y => f (d.symm y)) using 1
  all_goals try with_reducible_and_instances rfl
  rw [d.symm.sum_comp (fun y => ‖f y‖ ^ 2)]

/-- Iterating the two-factor bound never introduces the sizes of the residue fields. -/
theorem finiteTensorKernel_energy_le {n : ℕ}
    (α : Fin n → Type u) (β : Fin n → Type v)
    [∀ i, Fintype (α i)] [∀ i, Fintype (β i)]
    (M : ∀ i, α i → β i → ℂ) (A : Fin n → ℝ)
    (hM : ∀ i (f : β i → ℂ), (∑ x, ‖∑ y, M i x y * f y‖ ^ 2) ≤ A i ^ 2 * ∑ y, ‖f y‖ ^ 2)
    (f : (∀ i, β i) → ℂ) :
    (∑ x, ‖∑ y, finiteTensorKernel M x y * f y‖ ^ 2) ≤
      (∏ i, A i) ^ 2 * ∑ y, ‖f y‖ ^ 2 := by
  induction n with
  | zero => simp [finiteTensorKernel]
  | succ n ih =>
    have ht := tensorKernel_energy_le (M 0)
      (finiteTensorKernel (fun i : Fin n => M i.succ)) (A 0) (∏ i : Fin n, A i.succ)
      (hM 0) (ih (fun i => α i.succ) (fun i => β i.succ)
        (fun i => M i.succ) (fun i => A i.succ) (fun i => hM i.succ))
    have hr := kernel_energy_reindex _ _ ht (Fin.consEquiv α).symm
      (Fin.consEquiv β).symm f
    simpa only [finiteTensorKernel, Fin.prod_univ_succ, tensorKernel,
      Fin.consEquiv_symm_apply, Fin.tail] using hr

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_FiniteKernelOperator
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The counting-energy matrix as a continuous operator -/

namespace Ostmann
open WithLp
open scoped Classical BigOperators

theorem finiteKernelOperator_norm_le {α β : Type*} [Fintype α] [Fintype β]
    (M : α → β → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hM : ∀ f : β → ℂ, (∑ x, ‖∑ y, M x y * f y‖ ^ 2) ≤ B ^ 2 * ∑ y, ‖f y‖ ^ 2) :
    ‖finiteKernelOperator M‖ ≤ B := by
  apply ContinuousLinearMap.opNorm_le_bound _ hB
  intro f
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hB (norm_nonneg f))).mp
  rw [mul_pow, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  simpa only [finiteKernelOperator_apply] using hM (fun y => f y)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_FiniteCauchyEstimate
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Coefficient bounds by finite Fourier inversion on a circle

For a finite polynomial, a sufficiently large root-of-unity grid recovers every
coefficient exactly. This supplies the Cauchy estimate used in Section 5.3,
including for finite-dimensional operator spaces, without a dimension factor.
-/

namespace Ostmann
open scoped Classical BigOperators

theorem cyclicPolynomial_eq_invDFT {N : ℕ} [NeZero N]
    {E : Type*} [AddCommGroup E] [Module ℂ E] (c : ZMod N → E) (r : ℝ) :
    cyclicPolynomial c r = (N : ℂ) •
      ZMod.dft.symm (fun j => ((r ^ j.val : ℝ) : ℂ) • c j) := by
  funext z
  simp only [Pi.smul_apply, ZMod.invDFT_apply, smul_smul, mul_inv_cancel₀ (NeZero.ne (N : ℂ)),
    one_smul, cyclicPolynomial]

theorem cyclicPolynomial_coefficient {N : ℕ} [NeZero N]
    {E : Type*} [AddCommGroup E] [Module ℂ E] (c : ZMod N → E) (r : ℝ) (j : ZMod N) :
    (N : ℂ)⁻¹ • ZMod.dft (cyclicPolynomial c r) j = ((r ^ j.val : ℝ) : ℂ) • c j := by
  rw [cyclicPolynomial_eq_invDFT, map_smul]
  simp only [LinearEquiv.apply_symm_apply, Pi.smul_apply, smul_smul,
    ← mul_assoc, inv_mul_cancel₀ (NeZero.ne (N : ℂ)), one_mul]

theorem normalized_dft_norm_le {N : ℕ} [NeZero N]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : ZMod N → E) (M : ℝ) (hM : ∀ z, ‖f z‖ ≤ M) (j : ZMod N) :
    ‖(N : ℂ)⁻¹ • ZMod.dft f j‖ ≤ M := by
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hd : ‖ZMod.dft f j‖ ≤ N * M := by
    rw [ZMod.dft_apply]
    calc
      _ ≤ ∑ z, ‖ZMod.stdAddChar (-(z * j)) • f z‖ := norm_sum_le _ _
      _ = ∑ z, ‖f z‖ := by simp only [norm_smul, ZMod.stdAddChar_apply, Circle.norm_coe, one_mul]
      _ ≤ ∑ _z : ZMod N, M := Finset.sum_le_sum (fun z _ => hM z)
      _ = _ := by simp
  rw [norm_smul, norm_inv, Complex.norm_natCast]
  calc
    _ ≤ (N : ℝ)⁻¹ * (N * M) := mul_le_mul_of_nonneg_left hd (by positivity)
    _ = M := by rw [← mul_assoc, inv_mul_cancel₀ hN, one_mul]

theorem cyclicPolynomial_coefficient_norm_le {N : ℕ} [NeZero N]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (c : ZMod N → E) (r M : ℝ) (hr : 0 < r)
    (hM : ∀ z, ‖cyclicPolynomial c r z‖ ≤ M) (j : ZMod N) :
    ‖c j‖ ≤ M / r ^ j.val := by
  have hh := normalized_dft_norm_le (cyclicPolynomial c r) M hM j
  rw [cyclicPolynomial_coefficient, norm_smul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (pow_pos hr _)] at hh
  exact (le_div_iff₀ (pow_pos hr _)).mpr (by simpa only [mul_comm] using hh)

theorem cyclicPolynomial_two_coefficient_norm_le {N : ℕ} [NeZero N]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (c : ZMod N → ZMod N → E) (r M : ℝ) (hr : 0 < r)
    (hM : ∀ z w, ‖cyclicPolynomial (fun i => cyclicPolynomial (c i) r w) r z‖ ≤ M)
    (i j : ZMod N) : ‖c i j‖ ≤ M / r ^ i.val / r ^ j.val := by
  apply cyclicPolynomial_coefficient_norm_le (c i) r (M / r ^ i.val) hr
  intro w
  exact cyclicPolynomial_coefficient_norm_le
    (fun i => cyclicPolynomial (c i) r w) r M hr (fun z => hM z w) i

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_FinitePolynomialTail
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Rectangular polynomial truncation with a geometric error -/

namespace Ostmann
open scoped Classical BigOperators

theorem finite_geometric_tail_le (q : ℝ) (hq : 0 ≤ q) (hq1 : q < 1) (N K : ℕ) :
    (∑ i ∈ Finset.range N, if K < i then q ^ i else 0) ≤ q ^ (K + 1) / (1 - q) := by
  rw [← Finset.sum_filter]
  have he : {i ∈ Finset.range N | K < i} = Finset.Ico (K + 1) N := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [he]
  exact geom_sum_Ico_le_of_lt_one hq hq1

theorem finite_geometric_sum_le (q : ℝ) (hq : 0 ≤ q) (hq1 : q < 1) (N : ℕ) :
    (∑ i ∈ Finset.range N, q ^ i) ≤ 1 / (1 - q) := by
  simpa only [Nat.Ico_zero_eq_range, pow_zero] using
    (geom_sum_Ico_le_of_lt_one (m := 0) (n := N) hq hq1)

theorem rectangularPolynomialSum_error {E : Type*} [NormedAddCommGroup E]
    (c : ℕ → ℕ → E) (N K : ℕ) (M q : ℝ) (hM : 0 ≤ M)
    (hq : 0 ≤ q) (hq1 : q < 1)
    (hc : ∀ i < N, ∀ j < N, ‖c i j‖ ≤ M * q ^ i * q ^ j) :
    ‖(∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, c i j) -
      rectangularPolynomialSum c N K‖ ≤
        2 * M * q ^ (K + 1) / (1 - q) ^ 2 := by
  have he : (∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, c i j) -
      rectangularPolynomialSum c N K =
      ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
        if i ≤ K ∧ j ≤ K then 0 else c i j := by
    unfold rectangularPolynomialSum
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> simp
  rw [he]
  let Q := ∑ i ∈ Finset.range N, q ^ i
  let T := ∑ i ∈ Finset.range N, if K < i then q ^ i else 0
  have hQ : Q ≤ 1 / (1 - q) := finite_geometric_sum_le q hq hq1 N
  have hT : T ≤ q ^ (K + 1) / (1 - q) := finite_geometric_tail_le q hq hq1 N K
  have hQ0 : 0 ≤ Q := Finset.sum_nonneg (fun i _ => pow_nonneg hq i)
  calc
    _ ≤ ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
        ‖if i ≤ K ∧ j ≤ K then (0 : E) else c i j‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => norm_sum_le _ _)
    _ ≤ ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
        (M * (if K < i then q ^ i else 0) * q ^ j +
          M * q ^ i * (if K < j then q ^ j else 0)) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      have hh := hc i (Finset.mem_range.mp hi) j (Finset.mem_range.mp hj)
      by_cases hiK : i ≤ K <;> by_cases hjK : j ≤ K
      · simp [hiK, hjK, Nat.not_lt.mpr hiK, Nat.not_lt.mpr hjK]
      · simpa [hiK, hjK, Nat.not_lt.mpr hiK, Nat.lt_of_not_ge hjK] using hh
      · simpa [hiK, hjK, Nat.lt_of_not_ge hiK, Nat.not_lt.mpr hjK] using hh
      · simp only [hiK, hjK, false_and, ite_false, if_false, Nat.lt_of_not_ge hiK,
          Nat.lt_of_not_ge hjK, ite_true, if_true]
        exact hh.trans (le_add_of_nonneg_right (by positivity))
    _ = 2 * M * T * Q := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, Q, T]
      ring
    _ ≤ 2 * M * (q ^ (K + 1) / (1 - q)) * (1 / (1 - q)) := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left hT (by positivity)) hQ hQ0 (by positivity)
    _ = _ := by field_simp

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_PolynomialCircleEstimate
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Cauchy and truncation estimates for ordinary finite polynomials -/

namespace Ostmann
open scoped Classical BigOperators

theorem sum_zmod_val {N : ℕ} [NeZero N] {E : Type*} [AddCommMonoid E]
    (f : ℕ → E) : (∑ j : ZMod N, f j.val) = ∑ j ∈ Finset.range N, f j := by
  cases N with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n => exact Fin.sum_univ_eq_sum_range f (n + 1)

theorem cyclicPolynomial_eq_finitePolynomial {N : ℕ} [NeZero N]
    {E : Type*} [AddCommGroup E] [Module ℂ E] (c : ℕ → E) (r : ℝ) (z : ZMod N) :
    cyclicPolynomial (fun i : ZMod N => c i.val) r z =
      finitePolynomial c N ((r : ℂ) * ZMod.stdAddChar z) := by
  have hc (i : ZMod N) : ZMod.stdAddChar (i * z) = ZMod.stdAddChar z ^ i.val := by
    calc
      _ = ZMod.stdAddChar ((i.val : ZMod N) * z) := by rw [ZMod.natCast_zmod_val]
      _ = _ := by rw [← nsmul_eq_mul, AddChar.map_nsmul_eq_pow]
  unfold cyclicPolynomial finitePolynomial
  calc
    _ = ∑ i : ZMod N, (((r : ℂ) * ZMod.stdAddChar z) ^ i.val) • c i.val := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hc, smul_smul, mul_pow, Complex.ofReal_pow, mul_comm]
    _ = _ := sum_zmod_val (N := N) (fun i => (((r : ℂ) * ZMod.stdAddChar z) ^ i) • c i)

theorem finitePolynomial₂_coefficient_norm_le {N : ℕ} [NeZero N]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (c : ℕ → ℕ → E) (r M : ℝ) (hr : 0 < r)
    (hM : ∀ u v : ℂ, ‖u‖ = r → ‖v‖ = r → ‖finitePolynomial₂ c N u v‖ ≤ M)
    (i j : ℕ) (hi : i < N) (hj : j < N) :
    ‖c i j‖ ≤ M / r ^ i / r ^ j := by
  have hn (z : ZMod N) : ‖(r : ℂ) * ZMod.stdAddChar z‖ = r := by
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr,
      ZMod.stdAddChar_apply, Circle.norm_coe, mul_one]
  have hgrid (z w : ZMod N) :
      ‖cyclicPolynomial (fun i : ZMod N =>
        cyclicPolynomial (fun j : ZMod N => c i.val j.val) r w) r z‖ ≤ M := by
    simp_rw [cyclicPolynomial_eq_finitePolynomial]
    rw [cyclicPolynomial_eq_finitePolynomial
      (fun i => finitePolynomial (c i) N ((r : ℂ) * ZMod.stdAddChar w)) r z]
    exact hM _ _ (hn z) (hn w)
  have hh := cyclicPolynomial_two_coefficient_norm_le
    (fun i j : ZMod N => c i.val j.val) r M hr hgrid (i : ZMod N) (j : ZMod N)
  simpa only [ZMod.val_natCast_of_lt hi, ZMod.val_natCast_of_lt hj] using hh

theorem finitePolynomial₂_truncation_error {N : ℕ} [NeZero N]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (c : ℕ → ℕ → E) (r M : ℝ) (hr : 1 < r) (hM0 : 0 ≤ M)
    (hM : ∀ u v : ℂ, ‖u‖ = r → ‖v‖ = r → ‖finitePolynomial₂ c N u v‖ ≤ M)
    (K : ℕ) :
    ‖finitePolynomial₂ c N 1 1 - rectangularPolynomialSum c N K‖ ≤
      2 * M * r⁻¹ ^ (K + 1) / (1 - r⁻¹) ^ 2 := by
  have hr0 : 0 < r := lt_trans zero_lt_one hr
  have hc (i : ℕ) (hi : i < N) (j : ℕ) (hj : j < N) :
      ‖c i j‖ ≤ M * r⁻¹ ^ i * r⁻¹ ^ j := by
    simpa only [div_eq_mul_inv, inv_pow] using
      finitePolynomial₂_coefficient_norm_le c r M hr0 hM i j hi hj
  simpa only [finitePolynomial₂, finitePolynomial, one_pow, one_smul] using
    rectangularPolynomialSum_error c N K M r⁻¹ hM0 (inv_nonneg.mpr hr0.le)
      ((inv_lt_one₀ hr0).mpr hr) hc

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Supply_LocalSparsePolydisc
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform complex-parameter bound for the local sparse block -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

theorem local_sparse_polydisc {p : ℕ} [Fact p.Prime]
    (S : Finset (ZMod p)) (hS : S.Nonempty) (hSp : S.card < p)
    (hp : (100 : ℝ) ≤ p)
    (hlo : (1 / 3 : ℝ) ≤ residueDensity S) (hhi : residueDensity S ≤ 2 / 3)
    (ε : ℝ) (hε : 0 ≤ ε) (hεsmall : ε ≤ 1 / 1000000)
    (hL1 : (p : ℝ)⁻¹ * ∑ b, ‖normalizedResidueTransform S b‖ ≤ ε ^ 2) :
    let E := largeTransformSpectrum (normalizedResidueTransform S)
    let T := Finset.univ \ S
    ∀ u v : ℂ, ‖u‖ ≤ 103 / 100 → ‖v‖ ≤ 103 / 100 →
      ∀ (z : ℂ) (f : ZMod p → ℂ),
        ‖polydiscSparseScalar S E (u + v) (u * v) * z +
          ∑ x, conj (polydiscSparseSide T S E (conj (u + v)) (conj (u * v)) x) * f x‖ ^ 2 +
        residueVectorNorm (fun x => z * polydiscSparseSide S T E (u + v) (u * v) x +
          polydiscSparseLower S T E (u + v) (u * v) f x) ^ 2 ≤
        (1 + 3 / (p : ℝ)) ^ 2 * (‖z‖ ^ 2 + residueVectorNorm f ^ 2) := by
  intro E T u v hu hv z f
  have hp0 : (0 : ℝ) < p := by linarith
  have hc : ‖u + v‖ ≤ (103 / 50 : ℝ) := by linarith [norm_add_le u v]
  have hd : ‖u * v‖ ≤ (10609 / 10000 : ℝ) := by
    rw [norm_mul]
    have hh := mul_le_mul hu hv (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 103 / 100)
    norm_num at hh ⊢
    exact hh
  obtain ⟨hz, _hn, hcard, _hconst, he, herr⟩ :=
    sparse_residue_projection S hS hSp ε hε (by linarith) hL1
  have ha := residueKernelScalar_sparse_norm_le S E hS hSp hz (17 / 20) (by norm_num)
  have hb := squareKernel_scalar_norm_le S E hS hSp hlo hhi (17 / 20) ε hε hcard
  norm_num at hb
  have hs := polydisc_scalar_norm_bounds p ε
    (residueKernelScalar S (localSparseKernel E)) (residueKernelScalar S (localSparseSquare E))
    (u + v) (u * v) hp hε hεsmall ha hb hc hd
  change (19 / 20 : ℝ) ≤ ‖polydiscSparseScalar S E (u + v) (u * v)‖ ∧
    ‖polydiscSparseScalar S E (u + v) (u * v)‖ ≤ 1 + 2 / (p : ℝ) at hs
  obtain ⟨hproj₁, hproj₂⟩ := residueProjection_side_norms S E hS hSp hz hlo hhi ε hε herr
  obtain ⟨hu₁, hu₂⟩ := balanced_uniform_norms S hS hSp hlo hhi
  have hrow := polydiscSparseSide_norm_le T S E ε hε hcard (conj (u + v)) (conj (u * v))
    (by simpa only [Complex.norm_conj] using hc) (by simpa only [Complex.norm_conj] using hd) hproj₁ hu₁
  have hcol := polydiscSparseSide_norm_le S T E ε hε hcard (u + v) (u * v) hc hd hproj₂ hu₂
  have hST : Disjoint S T := by
    apply Finset.disjoint_left.mpr
    intro x hx hxT
    exact (Finset.mem_sdiff.mp hxT).2 hx
  have hC := polydiscSparseLower_norm_le S T E hST ε hε hεsmall hcard (u + v) (u * v) hc hd
  have hblock := residue_block_energy (polydiscSparseScalar S E (u + v) (u * v))
    (polydiscSparseSide T S E (conj (u + v)) (conj (u * v)))
    (polydiscSparseSide S T E (u + v) (u * v)) (polydiscSparseLower S T E (u + v) (u * v))
    ‖polydiscSparseScalar S E (u + v) (u * v)‖ (9 / 10) (6 * ε / Real.sqrt (p : ℝ))
    (norm_nonneg _) (by norm_num) (by linarith [hs.1]) le_rfl hrow hcol hC z f
  have hside : 20 * (6 * ε / Real.sqrt (p : ℝ)) ^ 2 ≤ 1 / (p : ℝ) := by
    rw [div_pow, Real.sq_sqrt hp0.le]
    have heq : 20 * ((6 * ε) ^ 2 / (p : ℝ)) = (720 * ε ^ 2) / p := by ring
    rw [heq]
    apply (div_le_div_iff_of_pos_right hp0).mpr
    have hsq : ε ^ 2 ≤ ε := by nlinarith
    nlinarith
  have hM : ‖polydiscSparseScalar S E (u + v) (u * v)‖ +
      20 * (6 * ε / Real.sqrt (p : ℝ)) ^ 2 ≤ 1 + 3 / (p : ℝ) := by
    have heq : 2 / (p : ℝ) + 1 / p = 3 / p := by ring
    linarith [hs.2]
  apply hblock.trans
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hM 2)
    (add_nonneg (sq_nonneg _) (sq_nonneg _))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_FiniteBlockMatrix
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite matrices for the scalar plus centered-residue blocks -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

theorem finiteBlockMatrix_apply_none {p : ℕ} [NeZero p]
    (a : ℂ) (row col : ZMod p → ℂ) (L : (ZMod p → ℂ) →ₗ[ℂ] (ZMod p → ℂ))
    (f : Option (ZMod p) → ℂ) :
    (∑ y, finiteBlockMatrix a row col L none y * f y) =
      a * f none + ∑ y, conj (row y) * f (some y) := by
  rw [Fintype.sum_option]
  rfl

theorem finiteBlockMatrix_apply_some {p : ℕ} [NeZero p]
    (a : ℂ) (row col : ZMod p → ℂ) (L : (ZMod p → ℂ) →ₗ[ℂ] (ZMod p → ℂ))
    (f : Option (ZMod p) → ℂ) (x : ZMod p) :
    (∑ y, finiteBlockMatrix a row col L (some x) y * f y) =
      f none * col x + L (fun y => f (some y)) x := by
  rw [Fintype.sum_option, finiteLinearMap_point_expansion]
  simp only [finiteBlockMatrix]
  ring

theorem finiteBlockMatrix_energy {p : ℕ} [NeZero p]
    (a : ℂ) (row col : ZMod p → ℂ) (L : (ZMod p → ℂ) →ₗ[ℂ] (ZMod p → ℂ))
    (f : Option (ZMod p) → ℂ) :
    (∑ x, ‖∑ y, finiteBlockMatrix a row col L x y * f y‖ ^ 2) =
      ‖a * f none + ∑ y, conj (row y) * f (some y)‖ ^ 2 +
        residueVectorNorm (fun x => f none * col x + L (fun y => f (some y)) x) ^ 2 := by
  rw [Fintype.sum_option, finiteBlockMatrix_apply_none, residueVectorNorm_sq]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  rw [finiteBlockMatrix_apply_some]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_SparseResidueMatrix
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Matrix form of the concrete local sparse kernel -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

theorem sparseResidueMatrix_energy_le {p : ℕ} [Fact p.Prime]
    (S : Finset (ZMod p)) (hS : S.Nonempty) (hSp : S.card < p) (hp : (100 : ℝ) ≤ p)
    (hlo : (1 / 3 : ℝ) ≤ residueDensity S) (hhi : residueDensity S ≤ 2 / 3)
    (ε : ℝ) (hε : 0 ≤ ε) (hεsmall : ε ≤ 1 / 1000000)
    (hL1 : (p : ℝ)⁻¹ * ∑ b, ‖normalizedResidueTransform S b‖ ≤ ε ^ 2)
    (u v : ℂ) (hu : ‖u‖ ≤ 103 / 100) (hv : ‖v‖ ≤ 103 / 100)
    (f : Option (ZMod p) → ℂ) :
    let E := largeTransformSpectrum (normalizedResidueTransform S)
    (∑ x, ‖∑ y, sparseResidueMatrix S E u v x y * f y‖ ^ 2) ≤
      (1 + 3 / (p : ℝ)) ^ 2 * ∑ y, ‖f y‖ ^ 2 := by
  intro E
  rw [sparseResidueMatrix, finiteBlockMatrix_energy]
  simp only [polydiscLowerLinearMap_apply]
  have hh := local_sparse_polydisc S hS hSp hp hlo hhi ε hε hεsmall hL1 u v hu hv
    (f none) (fun y => f (some y))
  simpa only [Fintype.sum_option, ← residueVectorNorm_sq] using hh

/-- The sharper local estimate at `(1,1)` in the same finite matrix coordinates. -/
theorem sparseResidueMatrix_contraction {p : ℕ} [Fact p.Prime]
    (S : Finset (ZMod p)) (hS : S.Nonempty) (hSp : S.card < p) (hp : (100 : ℝ) ≤ p)
    (hlo : (1 / 3 : ℝ) ≤ residueDensity S) (hhi : residueDensity S ≤ 2 / 3)
    (ε : ℝ) (hε : 0 ≤ ε) (hεsmall : ε ≤ 1 / 1000000)
    (hL1 : (p : ℝ)⁻¹ * ∑ b, ‖normalizedResidueTransform S b‖ ≤ ε ^ 2)
    (f : Option (ZMod p) → ℂ) :
    let E := largeTransformSpectrum (normalizedResidueTransform S)
    let U := sparseKernelUnitFactor p ((E.card : ℝ) / p)
    (∑ x, ‖∑ y, sparseResidueMatrix S E 1 1 x y * f y‖ ^ 2) ≤
      (U * (1 - (8 / 5) / p)) ^ 2 * ∑ y, ‖f y‖ ^ 2 := by
  intro E U
  rw [sparseResidueMatrix, finiteBlockMatrix_energy]
  simp only [polydiscLowerLinearMap_apply]
  have hh := (local_sparse_kernel_contraction S hS hSp hp hlo hhi ε hε hεsmall hL1).2.2
    (f none) (fun y => f (some y))
  simpa only [polydiscSparseScalar, polydiscSparseSide, polydiscSparseLower,
    one_add_one_eq_two, one_mul, map_ofNat, map_one, localSparseScalar, localSparseSide,
    localSparseLower, Fintype.sum_option, ← residueVectorNorm_sq] using hh

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_SparseMatrixPolynomial
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The bilinear polynomial of a local sparse residue matrix -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

/-- Four evaluations recover the four bilinear coefficients exactly. -/
theorem sparseResidueMatrix_polynomial {p : ℕ} [NeZero p]
    (S E : Finset (ZMod p)) (u v : ℂ) (x y : Option (ZMod p)) :
    sparseResidueMatrix S E u v x y =
      sparseResidueMatrix S E 0 0 x y +
      u * (sparseResidueMatrix S E 1 0 x y - sparseResidueMatrix S E 0 0 x y) +
      v * (sparseResidueMatrix S E 0 1 x y - sparseResidueMatrix S E 0 0 x y) +
      u * v * (sparseResidueMatrix S E 1 1 x y - sparseResidueMatrix S E 1 0 x y -
        sparseResidueMatrix S E 0 1 x y + sparseResidueMatrix S E 0 0 x y) := by
  cases x <;> cases y <;>
    simp only [sparseResidueMatrix, finiteBlockMatrix, polydiscLowerLinearMap_apply,
      polydiscSparseScalar, polydiscSparseSide, polydiscSparseLower, map_add, map_mul,
      starRingEnd_apply, star_star, map_one, map_zero] <;> ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_SparseUnitPolydisc
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform control of the scalar unit mean on the parameter polydisc -/

namespace Ostmann
open scoped Classical BigOperators

theorem small_unit_ratio (p x ε : ℝ) (hp : 2 ≤ p) (hx : x ≤ ε) (hε : 0 ≤ ε) :
    x / (p - 1) ≤ 2 * ε / p := by
  have hp0 : 0 < p := by linarith
  have hp1 : 0 < p - 1 := by linarith
  apply (div_le_div_iff₀ hp1 hp0).mpr
  have hh := mul_le_mul_of_nonneg_right hx hp0.le
  nlinarith [mul_nonneg hε (sub_nonneg.mpr hp)]

theorem sparseUnitPolynomial_norm_le (p e ε : ℝ) (c d : ℂ)
    (hp : 2 ≤ p) (he : 0 ≤ e) (heε : e ≤ ε) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hc : ‖c‖ ≤ 103 / 50) (hd : ‖d‖ ≤ 10609 / 10000) :
    ‖sparseUnitPolynomial p e c d‖ ≤ 1 + 6 / p := by
  have hp0 : 0 < p := by linarith
  have hp1 : 0 < p - 1 := by linarith
  have he1 : e ≤ 1 := heε.trans hε1
  have hv : 0 ≤ e - e ^ 2 := by nlinarith
  have hve : e - e ^ 2 ≤ ε := by nlinarith [sq_nonneg e]
  have hr1 := small_unit_ratio p e ε hp heε hε
  have hr2 := small_unit_ratio p (e - e ^ 2) ε hp hve hε
  have h1 : ‖((-(17 / 20) * e / (p - 1) : ℝ) : ℂ)‖ ≤ (17 / 10) * ε / p := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_mul, abs_of_nonneg he,
      abs_of_pos hp1]
    norm_num
    have hh := mul_le_mul_of_nonneg_left hr1 (by norm_num : (0 : ℝ) ≤ 17 / 20)
    first | (convert hh using 1 <;> ring) | exact (le_of_eq (by ring)).trans (hh.trans (le_of_eq (by ring)))
  have h2 : ‖(((17 / 20) ^ 2 * (e - e ^ 2) / (p - 1) : ℝ) : ℂ)‖ ≤ (289 / 200) * ε / p := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hh := mul_le_mul_of_nonneg_left hr2 (by norm_num : (0 : ℝ) ≤ (17 / 20) ^ 2)
    first | (convert hh using 1 <;> ring) | exact (le_of_eq (by ring)).trans (hh.trans (le_of_eq (by ring)))
  unfold sparseUnitPolynomial
  apply (norm_add_le _ _).trans
  apply (add_le_add (norm_add_le _ _) le_rfl).trans
  rw [norm_one, norm_mul, norm_mul]
  have hh := add_le_add (mul_le_mul hc h1 (norm_nonneg _) (by norm_num))
    (mul_le_mul hd h2 (norm_nonneg _) (by norm_num))
  have hfrac : ((103 / 50) * ((17 / 10) * ε / p) +
      (10609 / 10000) * ((289 / 200) * ε / p)) ≤ 6 / p := by
    apply (le_div_iff₀ hp0).mpr
    have heq : ((103 / 50) * ((17 / 10) * ε / p) +
        (10609 / 10000) * ((289 / 200) * ε / p)) * p =
        ((103 / 50) * (17 / 10) + (10609 / 10000) * (289 / 200)) * ε := by
      field_simp
    rw [heq]
    linarith
  linarith

/-- Exact unit mean for both complex polynomial coefficients. -/
theorem sparseUnitPolynomial_mean {p : ℕ} [NeZero p]
    (E : Finset (ZMod p)) (hE : 0 ∉ E) (hsym : ∀ b, -b ∈ E ↔ b ∈ E)
    (hp : 1 < p) (c d : ℂ) :
    sparseUnitPolynomial p ((E.card : ℝ) / p) c d =
      ((p : ℂ) - 1)⁻¹ * ∑ x ∈ Finset.univ.erase 0,
        (1 + c * localSparseKernel E x + d * localSparseSquare E x) := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne p
  have hp1 : (p : ℂ) - 1 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hp.ne')
  have hc : ((Finset.univ.erase (0 : ZMod p)).card : ℂ) = (p : ℂ) - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ZMod.card,
      Nat.cast_sub (by omega : 1 ≤ p), Nat.cast_one]
  simp only [localSparseKernel, localSparseSquare]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    sparseAdditiveKernel_sum_nonzero E hE, sparseAdditiveKernel_square_sum_nonzero E hsym]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, hc]
  unfold sparseUnitPolynomial
  push_cast
  field_simp

/-- The scalar mean on the same polydisc as the operator has a uniform
`1+6/p` bound, independent of the dimension of the residue space. -/
theorem sparse_unit_polydisc_bound {p : ℕ} [Fact p.Prime]
    (E : Finset (ZMod p)) (hE : 0 ∉ E) (hsym : ∀ b, -b ∈ E ↔ b ∈ E)
    (ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hcard : (E.card : ℝ) ≤ ε * p)
    (u v : ℂ) (hu : ‖u‖ ≤ 103 / 100) (hv : ‖v‖ ≤ 103 / 100) :
    ‖((p : ℂ) - 1)⁻¹ * ∑ x ∈ Finset.univ.erase 0,
      (1 + u * localSparseKernel E x) * (1 + v * localSparseKernel E x)‖ ≤
      1 + 6 / (p : ℝ) := by
  have hpNat : 1 < p := (Fact.out : p.Prime).one_lt
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have he (x : ZMod p) : (1 + u * localSparseKernel E x) * (1 + v * localSparseKernel E x) =
      1 + (u + v) * localSparseKernel E x + (u * v) * localSparseSquare E x := by
    unfold localSparseSquare
    ring
  simp_rw [he]
  rw [← sparseUnitPolynomial_mean E hE hsym hpNat]
  apply sparseUnitPolynomial_norm_le p ((E.card : ℝ) / p) ε (u + v) (u * v)
    (by exact_mod_cast (Fact.out : p.Prime).two_le) (by positivity)
    ((div_le_iff₀ hp0).mpr hcard) hε hε1
  · linarith [norm_add_le u v]
  · rw [norm_mul]
    have hh := mul_le_mul hu hv (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 103 / 100)
    norm_num at hh ⊢
    exact hh

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_SparseTensorKernel
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual sparse tensor kernel of Section 5.3 -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

theorem product_one_add_le_exp_sum {ι : Type*} [Fintype ι] (a : ι → ℝ)
    (ha : ∀ i, 0 ≤ 1 + a i) :
    (∏ i, (1 + a i)) ≤ Real.exp (∑ i, a i) := by
  calc
    _ ≤ ∏ i, Real.exp (a i) := Finset.prod_le_prod (by intro i _; exact ha i)
      (by intro i _; linarith [Real.add_one_le_exp (a i)])
    _ = _ := (Real.exp_sum _ _).symm

theorem sparseTensorKernel_energy_le {n : ℕ} (p : Fin n → ℕ) [∀ i, Fact (p i).Prime]
    (S : ∀ i, Finset (ZMod (p i)))
    (hS : ∀ i, (S i).Nonempty) (hSp : ∀ i, (S i).card < p i)
    (hp : ∀ i, (100 : ℝ) ≤ p i)
    (hlo : ∀ i, (1 / 3 : ℝ) ≤ residueDensity (S i))
    (hhi : ∀ i, residueDensity (S i) ≤ 2 / 3)
    (ε : ℝ) (hε : 0 ≤ ε) (hεsmall : ε ≤ 1 / 1000000)
    (hL1 : ∀ i, (p i : ℝ)⁻¹ * ∑ b, ‖normalizedResidueTransform (S i) b‖ ≤ ε ^ 2)
    (u v : ℂ) (hu : ‖u‖ ≤ 103 / 100) (hv : ‖v‖ ≤ 103 / 100)
    (f : (∀ i, Option (ZMod (p i))) → ℂ) :
    (∑ x, ‖∑ y, sparseTensorKernel p S u v x y * f y‖ ^ 2) ≤
      Real.exp (3 * ∑ i, (p i : ℝ)⁻¹) ^ 2 * ∑ y, ‖f y‖ ^ 2 := by
  have hlocal := fun i => sparseResidueMatrix_energy_le (S i) (hS i) (hSp i) (hp i)
    (hlo i) (hhi i) ε hε hεsmall (hL1 i) u v hu hv
  have ht := finiteTensorKernel_energy_le (fun i => Option (ZMod (p i)))
    (fun i => Option (ZMod (p i))) _ (fun i => 1 + 3 / (p i : ℝ)) hlocal f
  apply ht.trans
  apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg (by intro y _; positivity))
  have hprod := product_one_add_le_exp_sum (fun i => 3 / (p i : ℝ))
    (by intro i; positivity)
  rw [show (∑ i, 3 / (p i : ℝ)) = 3 * ∑ i, (p i : ℝ)⁻¹ by
    simp only [div_eq_mul_inv, Finset.mul_sum]] at hprod
  exact pow_le_pow_left₀ (Finset.prod_nonneg (by intro i _; positivity)) hprod 2

/-- The full (untruncated) product has the manuscript's strict exponential contraction. -/
theorem sparseTensorKernel_contraction {n : ℕ} (p : Fin n → ℕ) [∀ i, Fact (p i).Prime]
    (S : ∀ i, Finset (ZMod (p i)))
    (hS : ∀ i, (S i).Nonempty) (hSp : ∀ i, (S i).card < p i)
    (hp : ∀ i, (100 : ℝ) ≤ p i)
    (hlo : ∀ i, (1 / 3 : ℝ) ≤ residueDensity (S i))
    (hhi : ∀ i, residueDensity (S i) ≤ 2 / 3)
    (ε : ℝ) (hε : 0 ≤ ε) (hεsmall : ε ≤ 1 / 1000000)
    (hL1 : ∀ i, (p i : ℝ)⁻¹ * ∑ b, ‖normalizedResidueTransform (S i) b‖ ≤ ε ^ 2)
    (f : (∀ i, Option (ZMod (p i))) → ℂ) :
    let U := ∏ i, sparseKernelUnitFactor (p i)
      (((largeTransformSpectrum (normalizedResidueTransform (S i))).card : ℝ) / p i)
    (∑ x, ‖∑ y, sparseTensorKernel p S 1 1 x y * f y‖ ^ 2) ≤
      (U * Real.exp (-(8 / 5) * ∑ i, (p i : ℝ)⁻¹)) ^ 2 * ∑ y, ‖f y‖ ^ 2 := by
  intro U
  let a : Fin n → ℝ := fun i => sparseKernelUnitFactor (p i)
    (((largeTransformSpectrum (normalizedResidueTransform (S i))).card : ℝ) / p i)
  have ha (i) : 0 < a i :=
    (local_sparse_kernel_contraction (S i) (hS i) (hSp i) (hp i) (hlo i) (hhi i)
      ε hε hεsmall (hL1 i)).1
  have hd (i) : 0 ≤ 1 - (8 / 5) / (p i : ℝ) := by
    have hpos : (0 : ℝ) < p i := lt_of_lt_of_le (by norm_num) (hp i)
    have hh : (8 / 5 : ℝ) / p i ≤ 1 := (div_le_one hpos).mpr (by linarith [hp i])
    linarith
  have ht := finiteTensorKernel_energy_le (fun i => Option (ZMod (p i)))
    (fun i => Option (ZMod (p i))) _ (fun i => a i * (1 - (8 / 5) / (p i : ℝ)))
    (fun i => sparseResidueMatrix_contraction (S i) (hS i) (hSp i) (hp i)
      (hlo i) (hhi i) ε hε hεsmall (hL1 i)) f
  apply ht.trans
  apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg (by intro y _; positivity))
  apply pow_le_pow_left₀ (Finset.prod_nonneg (by intro i _; exact mul_nonneg (ha i).le (hd i)))
  rw [Finset.prod_mul_distrib]
  apply mul_le_mul_of_nonneg_left _ (Finset.prod_nonneg (by intro i _; exact (ha i).le))
  have he := product_one_add_le_exp_sum (fun i => -(8 / 5) / (p i : ℝ))
    (by intro i; simpa only [neg_div, sub_eq_add_neg] using hd i)
  simpa only [neg_div, ← sub_eq_add_neg, div_eq_mul_inv, neg_mul,
    Finset.sum_neg_distrib, ← Finset.mul_sum] using he

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Supply_BilinearCube
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Coefficients of a finite product of bilinear factors -/

namespace Ostmann
open scoped Classical BigOperators

theorem cubeDegree_le {n : ℕ} (t : BilinearCube n) (b : Bool) : cubeDegree t b ≤ n := by
  calc
    _ ≤ ∑ _i : Fin n, 1 := Finset.sum_le_sum (by intro i _; split_ifs <;> omega)
    _ = n := by simp

theorem cubeCoefficient_polynomial {n : ℕ} {E : Type*} [AddCommMonoid E] [Module ℂ E]
    (A : BilinearCube n → E) (u v : ℂ) :
    finitePolynomial₂ (cubeCoefficient A) (n + 1) u v =
      ∑ t : BilinearCube n, (u ^ cubeDegree t false * v ^ cubeDegree t true) • A t := by
  unfold finitePolynomial₂ finitePolynomial cubeCoefficient
  simp_rw [Finset.smul_sum, smul_smul]
  calc
    _ = ∑ d ∈ Finset.range (n + 1) ×ˢ Finset.range (n + 1),
        ∑ t ∈ Finset.univ.filter (fun t => (cubeDegree t false, cubeDegree t true) = d),
          (u ^ cubeDegree t false * v ^ cubeDegree t true) • A t := by
      rw [Finset.sum_product]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro t ht
      have he := (Finset.mem_filter.mp ht).2
      have h₁ : cubeDegree t false = i := congrArg Prod.fst he
      have h₂ : cubeDegree t true = j := congrArg Prod.snd he
      rw [h₁, h₂]
    _ = _ := by
      apply Finset.sum_fiberwise_of_maps_to
      intro t _
      exact Finset.mem_product.mpr
        ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (cubeDegree_le t false)),
          Finset.mem_range.mpr (Nat.lt_succ_of_le (cubeDegree_le t true))⟩

theorem cube_power_product {n : ℕ} (t : BilinearCube n) (b : Bool) (u : ℂ) :
    (∏ i, if (if b then (t i).2 else (t i).1) then u else 1) = u ^ cubeDegree t b := by
  unfold cubeDegree
  rw [← Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_congr rfl
  intro i _
  split_ifs <;> simp

theorem bilinear_product_expansion {n : ℕ}
    (W : Fin n → Bool × Bool → ℂ) (u v : ℂ) :
    (∏ i, (W i (false, false) + u * W i (true, false) +
      v * W i (false, true) + u * v * W i (true, true))) =
      finitePolynomial₂ (cubeCoefficient (fun t => ∏ i, W i (t i))) (n + 1) u v := by
  rw [cubeCoefficient_polynomial]
  have hl (i : Fin n) : (W i (false, false) + u * W i (true, false) +
      v * W i (false, true) + u * v * W i (true, true)) =
      ∑ b : Bool × Bool, (if b.1 then u else 1) * (if b.2 then v else 1) * W i b := by
    rw [Fintype.sum_prod_type]
    simp only [Fintype.sum_bool, Bool.false_eq_true, ite_false, if_false, ite_true, if_true]
    ring
  simp_rw [hl]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro t _
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  have h₁ : (∏ i, if (t i).1 then u else 1) = u ^ cubeDegree t false := by
    simpa only [Bool.false_eq_true, ite_false, if_false] using cube_power_product t false u
  have h₂ : (∏ i, if (t i).2 then v else 1) = v ^ cubeDegree t true := by
    simpa only [ite_true, if_true] using cube_power_product t true v
  rw [h₁, h₂]
  rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_SparseTensorPolynomial
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Concrete coefficients of the sparse tensor polynomial -/

namespace Ostmann
open scoped Classical BigOperators

theorem sparseTensorKernel_polynomial {n : ℕ} (p : Fin n → ℕ) [∀ i, NeZero (p i)]
    (S : ∀ i, Finset (ZMod (p i))) (u v : ℂ) :
    sparseTensorKernel p S u v = finitePolynomial₂ (sparseTensorCoefficient p S) (n + 1) u v := by
  funext x y
  have he := bilinear_product_expansion
    (fun i b => localSparseCoefficient (S i)
      (largeTransformSpectrum (normalizedResidueTransform (S i))) b (x i) (y i)) u v
  change (∏ i, sparseResidueMatrix (S i)
    (largeTransformSpectrum (normalizedResidueTransform (S i))) u v (x i) (y i)) = _
  have hl (i : Fin n) : sparseResidueMatrix (S i)
      (largeTransformSpectrum (normalizedResidueTransform (S i))) u v (x i) (y i) =
      localSparseCoefficient (S i) _ (false, false) (x i) (y i) +
      u * localSparseCoefficient (S i) _ (true, false) (x i) (y i) +
      v * localSparseCoefficient (S i) _ (false, true) (x i) (y i) +
      u * v * localSparseCoefficient (S i) _ (true, true) (x i) (y i) :=
    sparseResidueMatrix_polynomial (S i)
      (largeTransformSpectrum (normalizedResidueTransform (S i))) u v (x i) (y i)
  calc
    _ = _ := Finset.prod_congr rfl (fun i _ => hl i)
    _ = _ := by
      simpa only [sparseTensorCoefficient, finitePolynomial₂, finitePolynomial,
        cubeCoefficient, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using he

theorem finiteKernelOperator_polynomial {α β : Type*} [Fintype α] [Fintype β]
    (c : ℕ → ℕ → α → β → ℂ) (N : ℕ) (u v : ℂ) :
    finiteKernelOperator (finitePolynomial₂ c N u v) =
      finitePolynomial₂ (fun i j => finiteKernelOperator (c i j)) N u v := by
  let L := (finiteKernelOperatorLinearMap :
    (α → β → ℂ) →ₗ[ℂ] (EuclideanSpace ℂ β →L[ℂ] EuclideanSpace ℂ α))
  change L (finitePolynomial₂ c N u v) = _
  simp only [finitePolynomial₂, finitePolynomial, map_sum, map_smul]
  rfl

theorem sparseTensorOperator_polynomial {n : ℕ} (p : Fin n → ℕ) [∀ i, NeZero (p i)]
    (S : ∀ i, Finset (ZMod (p i))) (u v : ℂ) :
    finiteKernelOperator (sparseTensorKernel p S u v) =
      finitePolynomial₂ (fun i j => finiteKernelOperator (sparseTensorCoefficient p S i j))
        (n + 1) u v := by
  rw [sparseTensorKernel_polynomial, finiteKernelOperator_polynomial]

/-- The actual coefficient truncation of the tensor has exponentially small error
in the cutoff, with the exact radius `1.03` from the local estimate. -/
theorem sparseTensorOperator_truncation_error {n : ℕ}
    (p : Fin n → ℕ) [∀ i, Fact (p i).Prime]
    (S : ∀ i, Finset (ZMod (p i)))
    (hS : ∀ i, (S i).Nonempty) (hSp : ∀ i, (S i).card < p i)
    (hp : ∀ i, (100 : ℝ) ≤ p i)
    (hlo : ∀ i, (1 / 3 : ℝ) ≤ residueDensity (S i))
    (hhi : ∀ i, residueDensity (S i) ≤ 2 / 3)
    (ε : ℝ) (hε : 0 ≤ ε) (hεsmall : ε ≤ 1 / 1000000)
    (hL1 : ∀ i, (p i : ℝ)⁻¹ * ∑ b, ‖normalizedResidueTransform (S i) b‖ ≤ ε ^ 2)
    (K : ℕ) :
    ‖finiteKernelOperator (sparseTensorKernel p S 1 1) -
      rectangularPolynomialSum (fun i j => finiteKernelOperator (sparseTensorCoefficient p S i j))
        (n + 1) K‖ ≤
      2 * Real.exp (3 * ∑ i, (p i : ℝ)⁻¹) * (100 / 103 : ℝ) ^ (K + 1) /
        (1 - 100 / 103) ^ 2 := by
  rw [sparseTensorOperator_polynomial]
  have hbound (u v : ℂ) (hu : ‖u‖ = 103 / 100) (hv : ‖v‖ = 103 / 100) :
      ‖finitePolynomial₂ (fun i j => finiteKernelOperator (sparseTensorCoefficient p S i j))
        (n + 1) u v‖ ≤ Real.exp (3 * ∑ i, (p i : ℝ)⁻¹) := by
    rw [← sparseTensorOperator_polynomial]
    apply finiteKernelOperator_norm_le _ _ (Real.exp_pos _).le
    exact sparseTensorKernel_energy_le p S hS hSp hp hlo hhi ε hε hεsmall hL1 u v hu.le hv.le
  have ht := finitePolynomial₂_truncation_error
    (fun i j => finiteKernelOperator (sparseTensorCoefficient p S i j))
    (103 / 100) _ (by norm_num) (Real.exp_pos _).le hbound K
  simpa only [show (103 / 100 : ℝ)⁻¹ = 100 / 103 by norm_num] using ht

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_SparseTruncatedOperator
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The norm bound for the actual truncated tensor -/

namespace Ostmann
open scoped Classical BigOperators

theorem finiteKernelOperator_rectangular {α β : Type*} [Fintype α] [Fintype β]
    (c : ℕ → ℕ → α → β → ℂ) (N K : ℕ) :
    finiteKernelOperator (rectangularPolynomialSum c N K) =
      rectangularPolynomialSum (fun i j => finiteKernelOperator (c i j)) N K := by
  let L := (finiteKernelOperatorLinearMap :
    (α → β → ℂ) →ₗ[ℂ] (EuclideanSpace ℂ β →L[ℂ] EuclideanSpace ℂ α))
  change L (rectangularPolynomialSum c N K) = _
  unfold rectangularPolynomialSum
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> simp only [map_zero]
  rfl

theorem truncatedSparseTensorKernel_norm_le {n : ℕ}
    (p : Fin n → ℕ) [∀ i, Fact (p i).Prime]
    (S : ∀ i, Finset (ZMod (p i)))
    (hS : ∀ i, (S i).Nonempty) (hSp : ∀ i, (S i).card < p i)
    (hp : ∀ i, (100 : ℝ) ≤ p i)
    (hlo : ∀ i, (1 / 3 : ℝ) ≤ residueDensity (S i))
    (hhi : ∀ i, residueDensity (S i) ≤ 2 / 3)
    (ε : ℝ) (hε : 0 ≤ ε) (hεsmall : ε ≤ 1 / 1000000)
    (hL1 : ∀ i, (p i : ℝ)⁻¹ * ∑ b, ‖normalizedResidueTransform (S i) b‖ ≤ ε ^ 2)
    (K : ℕ) :
    let U := ∏ i, sparseKernelUnitFactor (p i)
      (((largeTransformSpectrum (normalizedResidueTransform (S i))).card : ℝ) / p i)
    let H := ∑ i, (p i : ℝ)⁻¹
    ‖finiteKernelOperator (truncatedSparseTensorKernel p S K)‖ ≤
      U * Real.exp (-(8 / 5) * H) +
        2 * Real.exp (3 * H) * (100 / 103 : ℝ) ^ (K + 1) / (1 - 100 / 103) ^ 2 := by
  intro U H
  have hU : 0 < U := Finset.prod_pos (fun i _ =>
    (local_sparse_kernel_contraction (S i) (hS i) (hSp i) (hp i) (hlo i) (hhi i)
      ε hε hεsmall (hL1 i)).1)
  have hf : ‖finiteKernelOperator (sparseTensorKernel p S 1 1)‖ ≤
      U * Real.exp (-(8 / 5) * H) := by
    apply finiteKernelOperator_norm_le _ _ (mul_nonneg hU.le (Real.exp_pos _).le)
    exact sparseTensorKernel_contraction p S hS hSp hp hlo hhi ε hε hεsmall hL1
  have he := sparseTensorOperator_truncation_error p S hS hSp hp hlo hhi ε hε hεsmall hL1 K
  rw [← finiteKernelOperator_rectangular] at he
  change ‖finiteKernelOperator (sparseTensorKernel p S 1 1) -
    finiteKernelOperator (truncatedSparseTensorKernel p S K)‖ ≤ _ at he
  calc
    _ ≤ ‖finiteKernelOperator (sparseTensorKernel p S 1 1)‖ +
        ‖finiteKernelOperator (sparseTensorKernel p S 1 1) -
          finiteKernelOperator (truncatedSparseTensorKernel p S K)‖ :=
      norm_le_insert _ _
    _ ≤ _ := add_le_add hf he

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_SparseTruncationRate
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A concrete linear truncation cutoff for the sparse weight -/

namespace Ostmann

theorem sparse_grid_ratio_le_exp : (100 / 103 : ℝ) ≤ Real.exp (-1 / 40) := by
  have hh := Real.add_one_le_exp (-1 / 40 : ℝ)
  linarith

theorem sparse_truncation_constant_le_exp :
    (2 / (1 - 100 / 103) ^ 2 : ℝ) ≤ Real.exp 14 := by
  have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 11 / 4)
    (show (11 / 4 : ℝ) ≤ Real.exp (7 / 4) by linarith [Real.add_one_le_exp (7 / 4 : ℝ)]) 8
  rw [← Real.exp_nat_mul] at hh
  norm_num at hh ⊢
  linarith

/-- The fixed choice `K >= 1000 L` controls both the scalar and operator tails.
Only the harmonic-mass bound `H <= L` remains to be supplied by the prime band. -/
theorem sparse_truncation_error_rate (L H : ℝ) (K : ℕ)
    (hL : 1 ≤ L) (hH : H ≤ L) (hK : 1000 * L ≤ K) :
    2 * Real.exp (6 * H) * (100 / 103 : ℝ) ^ (K + 1) / (1 - 100 / 103) ^ 2 ≤
      Real.exp (-5 * L) := by
  have hq := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 100 / 103) sparse_grid_ratio_le_exp (K + 1)
  rw [← Real.exp_nat_mul] at hq
  have hc := sparse_truncation_constant_le_exp
  calc
    _ = (2 / (1 - 100 / 103) ^ 2 : ℝ) * Real.exp (6 * H) * (100 / 103 : ℝ) ^ (K + 1) := by ring
    _ ≤ Real.exp 14 * Real.exp (6 * H) * Real.exp ((K + 1 : ℕ) * (-1 / 40 : ℝ)) := by
      exact mul_le_mul (mul_le_mul_of_nonneg_right hc (Real.exp_pos _).le) hq (by positivity) (by positivity)
    _ = Real.exp (14 + 6 * H + (K + 1 : ℕ) * (-1 / 40 : ℝ)) := by rw [Real.exp_add, Real.exp_add]
    _ ≤ Real.exp (-5 * L) := Real.exp_le_exp.mpr (by push_cast; linarith)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_SparseUnitMassBounds
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Lower and upper bounds for the full unit normalizer -/

namespace Ostmann
open scoped Classical BigOperators

theorem exp_neg_two_le_one_sub (x : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    Real.exp (-2 * x) ≤ 1 - x := by
  have hp : 0 < 1 - x := by linarith
  have hi : (1 - x)⁻¹ ≤ 1 + 2 * x := by
    rw [← one_div]
    apply (div_le_iff₀ hp).mpr
    nlinarith [mul_nonneg hx (show 0 ≤ 1 - 2 * x by linarith)]
  have hl := Real.one_sub_inv_le_log_of_pos hp
  rw [← Real.exp_log hp]
  exact Real.exp_le_exp.mpr (by linarith)

theorem sparseKernelUnitFactor_upper (p e : ℝ) (hp : 1 < p) (he : 0 ≤ e) :
    sparseKernelUnitFactor p e ≤ 1 := by
  unfold sparseKernelUnitFactor
  have hn : (17 / 20 : ℝ) ^ 2 * (e - e ^ 2) - (17 / 10) * e ≤ 0 := by
    nlinarith [sq_nonneg e]
  have hh := div_nonpos_of_nonpos_of_nonneg hn (show 0 ≤ p - 1 by linarith)
  linarith

theorem sparseKernelUnitFactor_exp_lower (p e ε : ℝ) (hp : 100 ≤ p)
    (he : 0 ≤ e) (heε : e ≤ ε) (hε : 0 ≤ ε) (hεsmall : ε ≤ 1 / 1000000) :
    Real.exp (-8 * ε / p) ≤ sparseKernelUnitFactor p e := by
  have hp0 : 0 < p := by linarith
  have hx0 : 0 ≤ 4 * ε / p := by positivity
  have hx1 : 4 * ε / p ≤ 1 / 2 := (div_le_iff₀ hp0).mpr (by linarith)
  have hh := exp_neg_two_le_one_sub (4 * ε / p) hx0 hx1
  have hl := sparseKernelUnitFactor_lower p e ε (by linarith) he heε hε (by linarith)
  apply le_trans _ hl
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  ring

theorem sparse_unit_mass_range {n : ℕ} (p : Fin n → ℕ) [∀ i, NeZero (p i)]
    (E : ∀ i, Finset (ZMod (p i))) (hp : ∀ i, (100 : ℝ) ≤ p i)
    (ε : ℝ) (hε : 0 ≤ ε) (hεsmall : ε ≤ 1 / 1000000)
    (hc : ∀ i, ((E i).card : ℝ) ≤ ε * p i) :
    let U := ∏ i, sparseKernelUnitFactor (p i) (((E i).card : ℝ) / p i)
    Real.exp (-8 * ε * ∑ i, (p i : ℝ)⁻¹) ≤ U ∧ U ≤ 1 := by
  intro U
  have hratio (i : Fin n) : ((E i).card : ℝ) / p i ≤ ε :=
    (div_le_iff₀ (show (0 : ℝ) < p i by linarith [hp i])).mpr (hc i)
  constructor
  · have hh := Finset.prod_le_prod (s := Finset.univ)
      (fun (i : Fin n) _ => (Real.exp_pos (-8 * ε / p i)).le)
      (fun (i : Fin n) _ => sparseKernelUnitFactor_exp_lower (p i) _ ε (hp i)
        (by positivity) (hratio i) hε hεsmall)
    rw [← Real.exp_sum] at hh
    simpa only [U, div_eq_mul_inv, ← Finset.mul_sum] using hh
  · apply Finset.prod_le_one
    · intro i _
      exact (sparseKernelUnitFactor_positive (p i) _ ε (hp i) (by positivity)
        (hratio i) hε hεsmall).le
    · intro i _
      exact sparseKernelUnitFactor_upper _ _ (by linarith [hp i]) (by positivity)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_TensorUnitMean
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The independent unit-residue mean of the sparse polynomial -/

namespace Ostmann
open scoped Classical BigOperators

theorem tensorUnitMean_product {n : ℕ} (p : Fin n → ℕ) [∀ i, NeZero (p i)]
    (f : ∀ i, ZMod (p i) → ℂ) :
    tensorUnitMean p (fun x => ∏ i, f i (x i)) =
      ∏ i, ((p i : ℂ) - 1)⁻¹ * ∑ x ∈ Finset.univ.erase 0, f i x := by
  unfold tensorUnitMean
  change (∏ i, ((p i : ℂ) - 1)⁻¹) *
    (∑ x : (∀ i, NonzeroResidue (p i)), ∏ i, f i (x i)) = _
  rw [← Fintype.prod_sum (fun i (x : NonzeroResidue (p i)) => f i x)]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  rw [Finset.sum_coe_sort]

theorem tensorUnitMean_polydisc {n : ℕ} (p : Fin n → ℕ) [∀ i, Fact (p i).Prime]
    (E : ∀ i, Finset (ZMod (p i)))
    (hE : ∀ i, 0 ∉ E i) (hsym : ∀ i b, -b ∈ E i ↔ b ∈ E i)
    (ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hc : ∀ i, ((E i).card : ℝ) ≤ ε * p i)
    (u v : ℂ) (hu : ‖u‖ ≤ 103 / 100) (hv : ‖v‖ ≤ 103 / 100) :
    ‖tensorUnitMean p (fun x => ∏ i,
      (1 + u * localSparseKernel (E i) (x i)) * (1 + v * localSparseKernel (E i) (x i)))‖ ≤
        Real.exp (6 * ∑ i, (p i : ℝ)⁻¹) := by
  rw [tensorUnitMean_product p
    (fun i x => (1 + u * localSparseKernel (E i) x) * (1 + v * localSparseKernel (E i) x)), norm_prod]
  calc
    _ ≤ ∏ i, (1 + 6 / (p i : ℝ)) := Finset.prod_le_prod
      (fun i _ => norm_nonneg _)
      (fun i _ => sparse_unit_polydisc_bound (E i) (hE i) (hsym i) ε hε hε1 (hc i) u v hu hv)
    _ ≤ _ := by
      have hh := product_one_add_le_exp_sum (fun i => 6 / (p i : ℝ)) (by intro i; positivity)
      simpa only [div_eq_mul_inv, ← Finset.mul_sum] using hh

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Supply_ElementaryPolynomial
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The subset polynomial used in the nonnegative sparse weight -/

namespace Ostmann
open scoped Classical BigOperators

theorem elementaryCoefficient_polynomial {n : ℕ} (b : Fin n → ℂ) (u : ℂ) :
    finitePolynomial (elementaryCoefficient b) (n + 1) u = ∏ i, (1 + u * b i) := by
  unfold finitePolynomial elementaryCoefficient
  simp_rw [smul_eq_mul, Finset.mul_sum]
  calc
    _ = ∑ j ∈ Finset.range (n + 1),
        ∑ I ∈ Finset.univ.powerset.filter (fun I : Finset (Fin n) => I.card = j),
          u ^ I.card * ∏ i ∈ I, b i := by
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro I hI
      rw [(Finset.mem_filter.mp hI).2]
    _ = ∑ I ∈ (Finset.univ : Finset (Fin n)).powerset, u ^ I.card * ∏ i ∈ I, b i := by
      apply Finset.sum_fiberwise_of_maps_to
      intro I hI
      apply Finset.mem_range.mpr
      have hh := Finset.card_le_card (Finset.mem_powerset.mp hI)
      simpa only [Finset.card_univ, Fintype.card_fin] using Nat.lt_succ_of_le hh
    _ = _ := by
      rw [Finset.prod_one_add]
      apply Finset.sum_congr rfl
      intro I _
      rw [Finset.prod_mul_distrib, Finset.prod_const]

theorem elementaryCoefficient_product {n : ℕ} (b : Fin n → ℂ) (u v : ℂ) :
    finitePolynomial₂ (fun i j => elementaryCoefficient b i * elementaryCoefficient b j)
      (n + 1) u v = (∏ i, (1 + u * b i)) * ∏ i, (1 + v * b i) := by
  rw [← elementaryCoefficient_polynomial b u, ← elementaryCoefficient_polynomial b v]
  unfold finitePolynomial₂ finitePolynomial
  simp only [smul_eq_mul]
  rw [Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem elementaryTruncation_eq {n : ℕ} (b : Fin n → ℂ) (K : ℕ) :
    (∑ i ∈ Finset.range (n + 1), if i ≤ K then elementaryCoefficient b i else 0) =
      elementaryTruncation b K := by
  rw [← Finset.sum_filter]
  unfold elementaryCoefficient elementaryTruncation
  rw [Finset.sum_fiberwise_eq_sum_filter]
  apply Finset.sum_congr
  · ext I
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_range]
    constructor
    · rintro ⟨hI, _, hK⟩
      exact ⟨hI, hK⟩
    · rintro ⟨hI, hK⟩
      have hh : I.card ≤ n := by simpa using Finset.card_le_card hI
      exact ⟨hI, Nat.lt_succ_of_le hh, hK⟩
  · intro I _
    rfl

theorem elementaryTruncation_square {n : ℕ} (b : Fin n → ℂ) (K : ℕ) :
    rectangularPolynomialSum (fun i j => elementaryCoefficient b i * elementaryCoefficient b j)
      (n + 1) K = elementaryTruncation b K ^ 2 := by
  rw [pow_two, ← elementaryTruncation_eq b K]
  unfold rectangularPolynomialSum
  rw [Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases hi : i ≤ K <;> by_cases hj : j ≤ K <;> simp [hi, hj]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_TensorUnitPolynomial
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Truncating the independent unit-residue mean -/

namespace Ostmann
open scoped Classical BigOperators

theorem tensorUnitCoefficient_polynomial {n : ℕ} (p : Fin n → ℕ) [∀ i, NeZero (p i)]
    (E : ∀ i, Finset (ZMod (p i))) (u v : ℂ) :
    finitePolynomial₂ (tensorUnitCoefficient p E) (n + 1) u v =
      tensorUnitMean p (fun x => ∏ i,
        (1 + u * localSparseKernel (E i) (x i)) * (1 + v * localSparseKernel (E i) (x i))) := by
  let C : ℕ → ℕ → (∀ i, ZMod (p i)) → ℂ := fun j k x =>
    elementaryCoefficient (fun i => localSparseKernel (E i) (x i)) j *
      elementaryCoefficient (fun i => localSparseKernel (E i) (x i)) k
  have hm : tensorUnitMeanLinearMap p (finitePolynomial₂ C (n + 1) u v) =
      finitePolynomial₂ (tensorUnitCoefficient p E) (n + 1) u v := by
    simp only [finitePolynomial₂, finitePolynomial, map_sum, map_smul]
    rfl
  rw [← hm]
  change tensorUnitMean p (finitePolynomial₂ C (n + 1) u v) = _
  apply congrArg (tensorUnitMean p)
  funext x
  have he := elementaryCoefficient_product (fun i => localSparseKernel (E i) (x i)) u v
  simpa only [finitePolynomial₂, finitePolynomial, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, C, Finset.prod_mul_distrib] using he

theorem tensorUnitCoefficient_truncation {n : ℕ} (p : Fin n → ℕ) [∀ i, NeZero (p i)]
    (E : ∀ i, Finset (ZMod (p i))) (K : ℕ) :
    rectangularPolynomialSum (tensorUnitCoefficient p E) (n + 1) K =
      tensorUnitMean p (fun x => elementaryTruncation
        (fun i => localSparseKernel (E i) (x i)) K ^ 2) := by
  let C : ℕ → ℕ → (∀ i, ZMod (p i)) → ℂ := fun j k x =>
    elementaryCoefficient (fun i => localSparseKernel (E i) (x i)) j *
      elementaryCoefficient (fun i => localSparseKernel (E i) (x i)) k
  have hm : tensorUnitMeanLinearMap p (rectangularPolynomialSum C (n + 1) K) =
      rectangularPolynomialSum (tensorUnitCoefficient p E) (n + 1) K := by
    unfold rectangularPolynomialSum
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro k _
    split_ifs
    · rfl
    · exact map_zero _
  rw [← hm]
  change tensorUnitMean p (rectangularPolynomialSum C (n + 1) K) = _
  apply congrArg (tensorUnitMean p)
  funext x
  have he := elementaryTruncation_square (fun i => localSparseKernel (E i) (x i)) K
  simpa only [rectangularPolynomialSum, Finset.sum_apply, ite_apply, Pi.zero_apply, C] using he

theorem tensorUnitMean_truncation_error {n : ℕ} (p : Fin n → ℕ) [∀ i, Fact (p i).Prime]
    (E : ∀ i, Finset (ZMod (p i)))
    (hE : ∀ i, 0 ∉ E i) (hsym : ∀ i b, -b ∈ E i ↔ b ∈ E i)
    (ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hc : ∀ i, ((E i).card : ℝ) ≤ ε * p i)
    (K : ℕ) :
    ‖tensorUnitMean p (fun x => ∏ i, (1 + localSparseKernel (E i) (x i)) ^ 2) -
      tensorUnitMean p (fun x => elementaryTruncation
        (fun i => localSparseKernel (E i) (x i)) K ^ 2)‖ ≤
        2 * Real.exp (6 * ∑ i, (p i : ℝ)⁻¹) * (100 / 103 : ℝ) ^ (K + 1) /
          (1 - 100 / 103) ^ 2 := by
  have hb (u v : ℂ) (hu : ‖u‖ = 103 / 100) (hv : ‖v‖ = 103 / 100) :
      ‖finitePolynomial₂ (tensorUnitCoefficient p E) (n + 1) u v‖ ≤
        Real.exp (6 * ∑ i, (p i : ℝ)⁻¹) := by
    rw [tensorUnitCoefficient_polynomial]
    exact tensorUnitMean_polydisc p E hE hsym ε hε hε1 hc u v hu.le hv.le
  have ht := finitePolynomial₂_truncation_error (tensorUnitCoefficient p E)
    (103 / 100) _ (by norm_num) (Real.exp_pos _).le hb K
  rw [tensorUnitCoefficient_polynomial, tensorUnitCoefficient_truncation] at ht
  simpa only [one_mul, ← pow_two, show (103 / 100 : ℝ)⁻¹ = 100 / 103 by norm_num] using ht

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_TensorUnitFullMean
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact full unit mean and the truncated unit mass -/

namespace Ostmann
open scoped Classical BigOperators

theorem tensorUnitMean_full_square {n : ℕ} (p : Fin n → ℕ) [∀ i, Fact (p i).Prime]
    (E : ∀ i, Finset (ZMod (p i)))
    (hE : ∀ i, 0 ∉ E i) (hsym : ∀ i b, -b ∈ E i ↔ b ∈ E i) :
    tensorUnitMean p (fun x => ∏ i, (1 + localSparseKernel (E i) (x i)) ^ 2) =
      ((∏ i, sparseKernelUnitFactor (p i) (((E i).card : ℝ) / p i) : ℝ) : ℂ) := by
  rw [tensorUnitMean_product p (fun i x => (1 + localSparseKernel (E i) x) ^ 2)]
  push_cast
  apply Finset.prod_congr rfl
  intro i _
  exact (sparseKernelUnitFactor_mean (E i) (hE i) (hsym i) (Fact.out : (p i).Prime).one_lt).symm

theorem tensorUnitMean_truncated_close {n : ℕ} (p : Fin n → ℕ) [∀ i, Fact (p i).Prime]
    (E : ∀ i, Finset (ZMod (p i)))
    (hE : ∀ i, 0 ∉ E i) (hsym : ∀ i b, -b ∈ E i ↔ b ∈ E i)
    (ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hc : ∀ i, ((E i).card : ℝ) ≤ ε * p i)
    (K : ℕ) :
    ‖tensorUnitMean p (fun x => elementaryTruncation
        (fun i => localSparseKernel (E i) (x i)) K ^ 2) -
      ((∏ i, sparseKernelUnitFactor (p i) (((E i).card : ℝ) / p i) : ℝ) : ℂ)‖ ≤
        2 * Real.exp (6 * ∑ i, (p i : ℝ)⁻¹) * (100 / 103 : ℝ) ^ (K + 1) /
          (1 - 100 / 103) ^ 2 := by
  rw [norm_sub_rev]
  rw [← tensorUnitMean_full_square p E hE hsym]
  exact tensorUnitMean_truncation_error p E hE hsym ε hε hε1 hc K

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Supply_NonnegativeSparseWeight
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The real nonnegative weight represented by the truncated tensor -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

theorem elementaryTruncation_conj {n : ℕ} (b : Fin n → ℂ)
    (hb : ∀ i, conj (b i) = b i) (K : ℕ) :
    conj (elementaryTruncation b K) = elementaryTruncation b K := by
  simp only [elementaryTruncation, map_sum, map_prod, hb]

theorem localSparseKernel_spectrum_real {p : ℕ} [Fact p.Prime]
    (S : Finset (ZMod p)) (x : ZMod p) :
    (localSparseKernel (largeTransformSpectrum (normalizedResidueTransform S)) x).im = 0 := by
  exact sparseAdditiveKernel_real _
    (largeTransformSpectrum_neg _ (normalizedResidueTransform_neg S)) (17 / 20) x

theorem sparseSubsetWeight_complex {n : ℕ} (p : Fin n → ℕ) [∀ i, Fact (p i).Prime]
    (S : ∀ i, Finset (ZMod (p i))) (K : ℕ) (x : ∀ i, ZMod (p i)) :
    (sparseSubsetWeight p S K x : ℂ) =
      elementaryTruncation (fun i => localSparseKernel
        (largeTransformSpectrum (normalizedResidueTransform (S i))) (x i)) K ^ 2 := by
  let b := fun i => localSparseKernel (largeTransformSpectrum (normalizedResidueTransform (S i))) (x i)
  have hb (i) : conj (b i) = b i := by
    have hi : (b i).im = 0 := localSparseKernel_spectrum_real (S i) (x i)
    apply Complex.ext <;> simp [hi]
  have he := elementaryTruncation_conj b hb K
  have hh := Complex.mul_conj' (elementaryTruncation b K)
  rw [he, ← pow_two] at hh
  simpa only [sparseSubsetWeight, Complex.ofReal_pow, b] using hh.symm

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_SparseWeightUnitMean
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact real unit mean of the nonnegative sparse weight -/

namespace Ostmann
open scoped Classical BigOperators

theorem tensorUnitMean_ofReal {n : ℕ} (p : Fin n → ℕ) [∀ i, NeZero (p i)]
    (f : (∀ i, ZMod (p i)) → ℝ) :
    tensorUnitMean p (fun x => (f x : ℂ)) = (tensorRealUnitMean p f : ℂ) := by
  unfold tensorUnitMean tensorRealUnitMean
  push_cast
  rfl

theorem sparseWeightUnitMean_close {n : ℕ} (p : Fin n → ℕ) [∀ i, Fact (p i).Prime]
    (S : ∀ i, Finset (ZMod (p i)))
    (hS : ∀ i, (S i).Nonempty) (hSp : ∀ i, (S i).card < p i)
    (ε : ℝ) (hε : 0 ≤ ε) (hεsmall : ε ≤ 1 / 1000000)
    (hL1 : ∀ i, (p i : ℝ)⁻¹ * ∑ b, ‖normalizedResidueTransform (S i) b‖ ≤ ε ^ 2)
    (L : ℝ) (hL : 1 ≤ L) (hH : (∑ i, (p i : ℝ)⁻¹) ≤ L)
    (K : ℕ) (hK : 1000 * L ≤ K) :
    let U := ∏ i, sparseKernelUnitFactor (p i)
      (((largeTransformSpectrum (normalizedResidueTransform (S i))).card : ℝ) / p i)
    |tensorRealUnitMean p (sparseSubsetWeight p S K) - U| ≤ Real.exp (-5 * L) := by
  intro U
  let E := fun i => largeTransformSpectrum (normalizedResidueTransform (S i))
  have hs (i : Fin n) := normalizedResidueTransform_sparse (S i) (hS i) (hSp i)
    ε (ε ^ 2) (by nlinarith) le_rfl (hL1 i)
  have he := tensorUnitMean_truncated_close p E (fun i => (hs i).1)
    (fun i => (hs i).2.1) ε hε (by linarith) (fun i => (hs i).2.2.1) K
  have hf : (fun x => elementaryTruncation (fun i => localSparseKernel (E i) (x i)) K ^ 2) =
      (fun x => (sparseSubsetWeight p S K x : ℂ)) := by
    funext x
    exact (sparseSubsetWeight_complex p S K x).symm
  rw [hf, tensorUnitMean_ofReal, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at he
  exact he.trans (sparse_truncation_error_rate L _ K hL hH hK)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_SparseFiniteContraction
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Completed finite contraction and unit-mass estimates -/

namespace Ostmann
open scoped Classical BigOperators

theorem sparse_normalizer_error_bounds (L H ε U : ℝ)
    (hL : 1 ≤ L) (hH0 : 0 ≤ H) (hH : H ≤ L)
    (hεsmall : ε ≤ 1 / 1000000)
    (hU : Real.exp (-8 * ε * H) ≤ U) :
    0 < U ∧ Real.exp (-5 * L) ≤ U / 2 ∧
      Real.exp (-5 * L) ≤ U * Real.exp (-(8 / 5) * H) := by
  have hcoarse : Real.exp (-L) ≤ U := by
    apply le_trans _ hU
    apply Real.exp_le_exp.mpr
    have hh : 8 * ε * H ≤ H := by
      have he : 8 * ε ≤ 1 := by linarith
      simpa only [one_mul] using mul_le_mul_of_nonneg_right he hH0
    linarith
  have hhalf : Real.exp (-(4 * L)) ≤ 1 / 2 := by
    have he : (2 : ℝ) ≤ Real.exp (4 * L) := by
      linarith [Real.add_one_le_exp (4 * L)]
    rw [Real.exp_neg, ← one_div]
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) he
  refine ⟨(Real.exp_pos _).trans_le hcoarse, ?_, ?_⟩
  · calc
      Real.exp (-5 * L) = Real.exp (-L) * Real.exp (-(4 * L)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ U * (1 / 2) := mul_le_mul hcoarse hhalf (Real.exp_pos _).le
        ((Real.exp_pos _).trans_le hcoarse).le
      _ = U / 2 := by ring
  · calc
      Real.exp (-5 * L) ≤ Real.exp (-L - (8 / 5) * H) := Real.exp_le_exp.mpr (by linarith)
      _ = Real.exp (-L) * Real.exp (-(8 / 5) * H) := by rw [sub_eq_add_neg, Real.exp_add, neg_mul]
      _ ≤ U * Real.exp (-(8 / 5) * H) :=
        mul_le_mul_of_nonneg_right hcoarse (Real.exp_pos _).le

/-- The concrete finite output used by Proposition 5.1: the nonnegative
weight keeps a positive unit mean while its pair kernel contracts. -/
theorem sparse_finite_contraction_oai {n : ℕ}
    (p : Fin n → ℕ) [∀ i, Fact (p i).Prime]
    (S : ∀ i, Finset (ZMod (p i)))
    (hS : ∀ i, (S i).Nonempty) (hSp : ∀ i, (S i).card < p i)
    (hp : ∀ i, (100 : ℝ) ≤ p i)
    (hlo : ∀ i, (1 / 3 : ℝ) ≤ residueDensity (S i))
    (hhi : ∀ i, residueDensity (S i) ≤ 2 / 3)
    (ε : ℝ) (hε : 0 ≤ ε) (hεsmall : ε ≤ 1 / 1000000)
    (hL1 : ∀ i, (p i : ℝ)⁻¹ * ∑ b, ‖normalizedResidueTransform (S i) b‖ ≤ ε ^ 2)
    (L : ℝ) (hL : 1 ≤ L) (hH : (∑ i, (p i : ℝ)⁻¹) ≤ L)
    (K : ℕ) (hK : 1000 * L ≤ K) :
    let U := ∏ i, sparseKernelUnitFactor (p i)
      (((largeTransformSpectrum (normalizedResidueTransform (S i))).card : ℝ) / p i)
    0 < U ∧ U / 2 ≤ tensorRealUnitMean p (sparseSubsetWeight p S K) ∧
      ‖finiteKernelOperator (truncatedSparseTensorKernel p S K)‖ ≤
        2 * U * Real.exp (-(8 / 5) * ∑ i, (p i : ℝ)⁻¹) := by
  intro U
  let H := ∑ i, (p i : ℝ)⁻¹
  let E := fun i => largeTransformSpectrum (normalizedResidueTransform (S i))
  have hs (i : Fin n) := normalizedResidueTransform_sparse (S i) (hS i) (hSp i)
    ε (ε ^ 2) (by nlinarith) le_rfl (hL1 i)
  have hU := (sparse_unit_mass_range p E hp ε hε hεsmall (fun i => (hs i).2.2.1)).1
  have hH0 : 0 ≤ H := Finset.sum_nonneg (fun i _ => by positivity)
  obtain ⟨hpos, hehalf, heratio⟩ := sparse_normalizer_error_bounds L H ε U hL hH0 hH hεsmall hU
  refine ⟨hpos, ?_, ?_⟩
  · have hm := sparseWeightUnitMean_close p S hS hSp ε hε hεsmall hL1 L hL hH K hK
    have hh := (abs_le.mp hm).1
    linarith
  · have ht := truncatedSparseTensorKernel_norm_le p S hS hSp hp hlo hhi ε hε hεsmall hL1 K
    have he := sparse_truncation_error_rate L (H / 2) K hL (by dsimp [H]; linarith) hK
    rw [show 6 * (H / 2) = 3 * H by ring] at he
    have herr := he.trans heratio
    change ‖finiteKernelOperator (truncatedSparseTensorKernel p S K)‖ ≤
      U * Real.exp (-(8 / 5) * H) +
        2 * Real.exp (3 * H) * (100 / 103 : ℝ) ^ (K + 1) / (1 - 100 / 103) ^ 2 at ht
    linarith

end Ostmann

end OAI
end

theorem solution : type_of% @OAI.Ostmann.sparse_finite_contraction_oai := @OAI.Ostmann.sparse_finite_contraction_oai
