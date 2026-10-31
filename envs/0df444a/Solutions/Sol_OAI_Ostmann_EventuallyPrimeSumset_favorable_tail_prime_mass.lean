-- Prove2me | solution 1 for OAI.Ostmann.EventuallyPrimeSumset.favorable_tail_prime_mass
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T06:56:35.864198+00:00
-- url     : https://prove2.me/submissions/d6e8fe06-afa1-432a-b01d-ee6a5501749f

import Mathlib
import Definitions.Def_OstmannComplete
import Definitions.Def_OAIQ095D007
import Theorems.Thm_OAI_Ostmann_EventuallyPrimeSumset_sparse_tail_coverage
import Theorems.Thm_OAI_Ostmann_sparse_finite_contraction

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
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_Collision
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Elementary collision estimates

These are the finite probability and support-size inequalities used in §2
and in the final collision argument of §3. No analytic estimate is assumed.
-/

namespace Ostmann

open scoped BigOperators

/-- Exact squared distance from uniform probability on a finite support. -/
theorem collision_sub_uniform {α : Type*} (s : Finset α) (μ : α → ℝ)
    (hs : s.Nonempty) (hmass : ∑ x ∈ s, μ x = 1) :
    ∑ x ∈ s, (μ x - 1 / (s.card : ℝ)) ^ 2 =
      (∑ x ∈ s, μ x ^ 2) - 1 / (s.card : ℝ) := by
  have hc : (s.card : ℝ) ≠ 0 := by exact_mod_cast hs.card_ne_zero
  calc
    ∑ x ∈ s, (μ x - 1 / (s.card : ℝ)) ^ 2 =
        ∑ x ∈ s, (μ x ^ 2 - (2 / (s.card : ℝ)) * μ x +
          (1 / (s.card : ℝ)) ^ 2) := by
      apply Finset.sum_congr rfl
      intro x hx
      ring
    _ = (∑ x ∈ s, μ x ^ 2) -
          2 * (∑ x ∈ s, μ x) / (s.card : ℝ) +
          (s.card : ℝ) * (1 / (s.card : ℝ)) ^ 2 := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring
    _ = _ := by rw [hmass]; field_simp; ring

/-- Disjoint nonempty supports occupying at most `p` residues have combined
collision probability at least `4 / p`. -/
theorem four_div_le_inverse_add_inverse {a b p : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hab : a + b ≤ p) :
    4 / p ≤ 1 / a + 1 / b := by
  have hp : 0 < p := lt_of_lt_of_le (add_pos ha hb) hab
  have habpos : 0 < a * b := mul_pos ha hb
  have hnum : 4 * (a * b) ≤ p * (a + b) := by
    nlinarith [sq_nonneg (a - b), mul_nonneg (le_of_lt (add_pos ha hb)) (sub_nonneg.mpr hab)]
  apply (div_le_iff₀ hp).mpr
  have hratio : 4 ≤ (p * (a + b)) / (a * b) := (le_div_iff₀ habpos).mpr hnum
  calc
    4 ≤ p * (a + b) / (a * b) := hratio
    _ = (1 / a + 1 / b) * p := by field_simp; ring

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
-- module Solutions.OAIQ095_OS.Ostmann_Characters_NormalizedResidueIndicator
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The manuscript's normalized residue indicators and additive transforms -/

namespace Ostmann

open scoped BigOperators Classical ComplexConjugate

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
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
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

theorem largeTransformSpectrum_neg {p : ℕ} [NeZero p]
    (g : ZMod p → ℂ) (hg : ∀ b, g (-b) = conj (g b)) (b : ZMod p) :
    -b ∈ largeTransformSpectrum g ↔ b ∈ largeTransformSpectrum g := by
  simp only [largeTransformSpectrum, Finset.mem_filter, Finset.mem_univ, true_and,
    hg, Complex.norm_conj]

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

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Supply_FiniteSpectralProjection
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Concrete finite additive spectral projections for Section 5 -/

namespace Ostmann
open scoped Classical BigOperators

theorem densityFourierInverse_fourier {p : ℕ} [NeZero p]
    (f : ZMod p → ℂ) (x : ZMod p) :
    densityFourierInverse (densityFourier f) x = f x := by
  change densityFourier (densityFourier f) (-x) = f x
  rw [densityFourier_twice, neg_neg]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Supply_CenteredSupportProjection
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
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

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_SparseAdditiveKernel
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual additive kernel of the sparse spectral projection -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

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

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_SparseKernelEnergy
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
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

/-- Tensor coordinates evaluate as the product of the local kernel pairings. -/
theorem finiteTensorKernel_pairing {ι : Type*} [Fintype ι]
    {α : ι → Type u} {β : ι → Type v}
    [∀ i, Fintype (α i)] [∀ i, Fintype (β i)]
    (M : ∀ i, α i → β i → ℂ) (a : ∀ i, α i → ℂ) (b : ∀ i, β i → ℂ) :
    (∑ x, conj (∏ i, a i (x i)) * ∑ y, finiteTensorKernel M x y * ∏ i, b i (y i)) =
      ∏ i, ∑ x, conj (a i x) * ∑ y, M i x y * b i y := by
  have hi (x : ∀ i, α i) :
      (∑ y, finiteTensorKernel M x y * ∏ i, b i (y i)) =
        ∏ i, ∑ y, M i (x i) y * b i y := by
    simp only [finiteTensorKernel, ← Finset.prod_mul_distrib]
    exact (Fintype.prod_sum (fun i y => M i (x i) y * b i y)).symm
  simp only [hi, map_prod, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i x => conj (a i x) * ∑ y, M i x y * b i y)).symm

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

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Supply_CenteredProjectionPairing
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Self-adjointness of the finite centered and kernel blocks -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

theorem centeredSupportProjection_pairing {α : Type*} [Fintype α]
    (S : Finset α) (f g : α → ℂ) :
    (∑ x, conj (f x) * centeredSupportProjection S g x) =
      ∑ x, conj (centeredSupportProjection S f x) * g x := by
  have hm : (∑ x ∈ S, conj (f x)) * finiteSupportMean S g =
      conj (finiteSupportMean S f) * ∑ x ∈ S, g x := by
    simp only [finiteSupportMean, map_mul, map_inv₀, map_natCast, map_sum]
    ring
  simp only [centeredSupportProjection, mul_zero, apply_ite, map_zero,
    ite_mul, zero_mul, Finset.sum_ite_mem, Finset.univ_inter]
  simp only [mul_sub, map_sub, sub_mul, Finset.sum_sub_distrib, ← Finset.sum_mul,
    ← Finset.mul_sum]
  rw [hm]

theorem rawAdditiveKernelAction_selfAdjoint {p : ℕ} [NeZero p]
    (k : ZMod p → ℂ) (hk : ∀ a, conj ((p : ℂ) * additiveFourier k a) =
      (p : ℂ) * additiveFourier k a) (f g : ZMod p → ℂ) :
    (∑ x, conj (f x) * rawAdditiveKernelAction k g x) =
      ∑ x, conj (rawAdditiveKernelAction k f x) * g x := by
  rw [densityFourier_inner f (rawAdditiveKernelAction k g),
    densityFourier_inner (rawAdditiveKernelAction k f) g]
  simp_rw [rawAdditiveKernelAction_fourier]
  apply Finset.sum_congr rfl
  intro a _
  rw [map_mul, hk]
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_FiniteKernelBlocks
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Concrete side and lower blocks of the finite kernel matrix -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

theorem residueKernel_row_pairing {p : ℕ} [NeZero p]
    (S T : Finset (ZMod p)) (k : ZMod p → ℂ)
    (hk : ∀ a, conj ((p : ℂ) * additiveFourier k a) = (p : ℂ) * additiveFourier k a)
    (f : ZMod p → ℂ) :
    (∑ x, conj (uniformResidueVector S x) *
      rawAdditiveKernelAction k (centeredSupportProjection T f) x) =
      ∑ x, conj (residueKernelSide T S k x) * f x := by
  rw [rawAdditiveKernelAction_selfAdjoint k hk,
    centeredSupportProjection_pairing T]
  rfl

theorem sparseAdditiveKernel_multiplier_real {p : ℕ} [NeZero p]
    (E : Finset (ZMod p)) (t : ℝ) (a : ZMod p) :
    conj ((p : ℂ) * additiveFourier (sparseAdditiveKernel E t) a) =
      (p : ℂ) * additiveFourier (sparseAdditiveKernel E t) a := by
  rw [sparseAdditiveKernel_fourier]
  simp only [map_mul, map_natCast, map_inv₀, Complex.conj_ofReal]
  by_cases ha : a ∈ E <;> simp [ha]

theorem sparseAdditiveKernel_square_multiplier_real {p : ℕ} [NeZero p]
    (E : Finset (ZMod p)) (t : ℝ) (a : ZMod p) :
    conj ((p : ℂ) * additiveFourier
      (fun x => sparseAdditiveKernel E t x * sparseAdditiveKernel E t x) a) =
      (p : ℂ) * additiveFourier
        (fun x => sparseAdditiveKernel E t x * sparseAdditiveKernel E t x) a := by
  rw [sparseAdditiveKernel_square_fourier]
  simp only [map_mul, map_natCast, map_pow, map_inv₀, Complex.conj_ofReal]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_FiniteKernelCoordinates
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Literal residue-point coordinates of the local kernel matrix -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

theorem centeredSupportProjection_sum {α : Type*}
    (S : Finset α) (f : α → ℂ) :
    (∑ x ∈ S, centeredSupportProjection S f x) = 0 := by
  have he : (∑ x ∈ S, centeredSupportProjection S f x) =
      (∑ x ∈ S, f x) - (S.card : ℂ) * finiteSupportMean S f := by
    simp only [centeredSupportProjection]
    rw [Finset.sum_congr rfl (fun x hx => ite_eq_left hx), Finset.sum_sub_distrib]
    simp only [Finset.sum_const, nsmul_eq_mul]
  rw [he, finiteSupportMean_spec, sub_self]

theorem centeredSupportProjection_idempotent {α : Type*}
    (S : Finset α) (f : α → ℂ) :
    centeredSupportProjection S (centeredSupportProjection S f) = centeredSupportProjection S f := by
  have hm : finiteSupportMean S (centeredSupportProjection S f) = 0 := by
    rw [finiteSupportMean, centeredSupportProjection_sum, mul_zero]
  funext x
  by_cases hx : x ∈ S
  · simp only [centeredSupportProjection, ite_eq_left hx, hm, sub_zero]
  · simp only [centeredSupportProjection, ite_eq_right hx]

theorem uniformResidueVector_ite {p : ℕ} (S : Finset (ZMod p)) (x : ZMod p) :
    uniformResidueVector S x = if x ∈ S then (S.card : ℂ)⁻¹ else 0 := by
  by_cases hx : x ∈ S <;> simp [uniformResidueVector, hx]

theorem residuePointVector_decomposition {p : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (a : ZMod p) (ha : a ∈ S) :
    residuePointVector a = fun x => uniformResidueVector S x +
      centeredSupportProjection S (residuePointVector a) x := by
  have hm : finiteSupportMean S (residuePointVector a) = (S.card : ℂ)⁻¹ := by
    simp [finiteSupportMean, residuePointVector, ha]
  funext x
  by_cases hx : x ∈ S
  · simp only [uniformResidueVector_ite, centeredSupportProjection, ite_eq_left hx, hm]
    ring
  · have hxa : x ≠ a := by intro h; subst x; exact hx ha
    simp only [residuePointVector, ite_eq_right hxa, uniformResidueVector_ite,
      ite_eq_right hx, centeredSupportProjection, add_zero]

theorem residuePointVector_kernel {p : ℕ} [NeZero p]
    (k : ZMod p → ℂ) (a b : ZMod p) :
    (∑ x, conj (residuePointVector a x) * rawAdditiveKernelAction k (residuePointVector b) x) =
      k (a - b) := by
  simp [residuePointVector, rawAdditiveKernelAction]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_KernelCoordinateIdentity
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact identification of the centered-coordinate kernel matrix -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

theorem rawKernel_pairing_add {p : ℕ} [NeZero p]
    (k f₁ f₂ g₁ g₂ : ZMod p → ℂ) :
    (∑ x, conj (f₁ x + f₂ x) * rawAdditiveKernelAction k (fun x => g₁ x + g₂ x) x) =
      (∑ x, conj (f₁ x) * rawAdditiveKernelAction k g₁ x) +
      (∑ x, conj (f₁ x) * rawAdditiveKernelAction k g₂ x) +
      (∑ x, conj (f₂ x) * rawAdditiveKernelAction k g₁ x) +
      (∑ x, conj (f₂ x) * rawAdditiveKernelAction k g₂ x) := by
  rw [rawAdditiveKernelAction_add_input]
  simp only [map_add, add_mul, mul_add, Finset.sum_add_distrib]
  ring

theorem centeredSupportProjection_pairing_range {p : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (f g : ZMod p → ℂ) :
    (∑ x, conj (centeredSupportProjection S f x) * centeredSupportProjection S g x) =
      ∑ x, conj (centeredSupportProjection S f x) * g x := by
  rw [centeredSupportProjection_pairing, centeredSupportProjection_idempotent]

/-- The four blocks really represent `k(a-b)` on the centered coordinates of
the two residue points. This is the identity used before tensoring. -/
theorem kernel_centered_coordinate_identity {p : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (k : ZMod p → ℂ)
    (hk : ∀ c, conj ((p : ℂ) * additiveFourier k c) = (p : ℂ) * additiveFourier k c)
    (a b : ZMod p) (ha : a ∈ S) (hb : b ∈ Finset.univ \ S) :
    k (a - b) = residueKernelScalar S k +
      (∑ x, conj (residueKernelSide (Finset.univ \ S) S k x) *
        centeredSupportProjection (Finset.univ \ S) (residuePointVector b) x) +
      (∑ x, conj (centeredSupportProjection S (residuePointVector a) x) *
        residueKernelSide S (Finset.univ \ S) k x) +
      (∑ x, conj (centeredSupportProjection S (residuePointVector a) x) *
        residueKernelLower S (Finset.univ \ S) k
          (centeredSupportProjection (Finset.univ \ S) (residuePointVector b)) x) := by
  let T := Finset.univ \ S
  let A := centeredSupportProjection S (residuePointVector a)
  let B := centeredSupportProjection T (residuePointVector b)
  have harg := congrArg₂ (fun f g : ZMod p → ℂ =>
    ∑ x, conj (f x) * rawAdditiveKernelAction k g x)
    (residuePointVector_decomposition S a ha)
    (residuePointVector_decomposition T b hb)
  have hexpand := rawKernel_pairing_add k (uniformResidueVector S) A (uniformResidueVector T) B
  rw [residuePointVector_kernel] at harg
  have hrow := residueKernel_row_pairing S T k hk B
  have hB : centeredSupportProjection T B = B := centeredSupportProjection_idempotent T _
  rw [hB] at hrow
  have hcol := centeredSupportProjection_pairing_range S (residuePointVector a)
    (rawAdditiveKernelAction k (uniformResidueVector T))
  have hlower := centeredSupportProjection_pairing_range S (residuePointVector a)
    (rawAdditiveKernelAction k B)
  have hlow : residueKernelLower S T k B = centeredSupportProjection S (rawAdditiveKernelAction k B) := by
    unfold residueKernelLower
    rw [hB]
  change k (a - b) = _
  change k (a - b) =
    (∑ x, conj (uniformResidueVector S x) * rawAdditiveKernelAction k (uniformResidueVector T) x) +
      (∑ x, conj (residueKernelSide T S k x) * B x) +
      (∑ x, conj (A x) * centeredSupportProjection S (rawAdditiveKernelAction k (uniformResidueVector T)) x) +
      (∑ x, conj (A x) * residueKernelLower S T k B x)
  rw [hlow, hcol, hlower, ← hrow]
  exact harg.trans hexpand

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_PolynomialKernelCoordinates
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact polynomial kernel entries in centered residue coordinates -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

private theorem localPairing_left {p : ℕ} [NeZero p]
    (f g h : ZMod p → ℂ) (c d : ℂ) :
    localPairing (fun x => c * f x + d * g x) h =
      conj c * localPairing f h + conj d * localPairing g h := by
  unfold localPairing
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  simp only [map_add, map_mul]
  ring

private theorem localPairing_right {p : ℕ} [NeZero p]
    (f g h : ZMod p → ℂ) (c d : ℂ) :
    localPairing f (fun x => c * g x + d * h x) =
      c * localPairing f g + d * localPairing f h := by
  unfold localPairing
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  ring

/-- The matrix bounded on the polydisc has precisely the desired entries
`(1+u*b(a-b))*(1+v*b(a-b))`, including its constant mode. -/
theorem polynomial_kernel_coordinate_identity {p : ℕ} [NeZero p]
    (S E : Finset (ZMod p)) (a b : ZMod p) (ha : a ∈ S) (hb : b ∈ Finset.univ \ S)
    (u v : ℂ) :
    (1 + u * localSparseKernel E (a - b)) * (1 + v * localSparseKernel E (a - b)) =
      polydiscSparseScalar S E (u + v) (u * v) +
      (∑ x, conj (polydiscSparseSide (Finset.univ \ S) S E (conj (u + v)) (conj (u * v)) x) *
        centeredSupportProjection (Finset.univ \ S) (residuePointVector b) x) +
      (∑ x, conj (centeredSupportProjection S (residuePointVector a) x) *
        polydiscSparseSide S (Finset.univ \ S) E (u + v) (u * v) x) +
      (∑ x, conj (centeredSupportProjection S (residuePointVector a) x) *
        polydiscSparseLower S (Finset.univ \ S) E (u + v) (u * v)
          (centeredSupportProjection (Finset.univ \ S) (residuePointVector b)) x) := by
  let T := Finset.univ \ S
  let A := centeredSupportProjection S (residuePointVector a)
  let B := centeredSupportProjection T (residuePointVector b)
  let k := localSparseKernel E
  let k₂ := localSparseSquare E
  have h₁ := kernel_centered_coordinate_identity S k
    (sparseAdditiveKernel_multiplier_real E (17 / 20)) a b ha hb
  have h₂ := kernel_centered_coordinate_identity S k₂
    (sparseAdditiveKernel_square_multiplier_real E (17 / 20)) a b ha hb
  change k (a - b) = residueKernelScalar S k + localPairing (residueKernelSide T S k) B +
    localPairing A (residueKernelSide S T k) + localPairing A (residueKernelLower S T k B) at h₁
  change k (a - b) * k (a - b) = residueKernelScalar S k₂ + localPairing (residueKernelSide T S k₂) B +
    localPairing A (residueKernelSide S T k₂) + localPairing A (residueKernelLower S T k₂ B) at h₂
  change (1 + u * k (a - b)) * (1 + v * k (a - b)) =
    1 + (u + v) * residueKernelScalar S k + (u * v) * residueKernelScalar S k₂ +
    localPairing (fun x => conj (u + v) * residueKernelSide T S k x +
      conj (u * v) * residueKernelSide T S k₂ x) B +
    localPairing A (fun x => (u + v) * residueKernelSide S T k x +
      (u * v) * residueKernelSide S T k₂ x) +
    localPairing A (fun x => (u + v) * residueKernelLower S T k B x +
      (u * v) * residueKernelLower S T k₂ B x)
  rw [localPairing_left, localPairing_right, localPairing_right]
  simp only [starRingEnd_apply, star_star]
  linear_combination (u + v) * h₁ + (u * v) * h₂

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

theorem sparseResidueMatrix_point_identity {p : ℕ} [NeZero p]
    (S E : Finset (ZMod p)) (a b : ZMod p) (ha : a ∈ S) (hb : b ∈ Finset.univ \ S)
    (u v : ℂ) :
    (∑ x, conj (residuePointCoordinates S a x) *
      ∑ y, sparseResidueMatrix S E u v x y * residuePointCoordinates (Finset.univ \ S) b y) =
      (1 + u * localSparseKernel E (a - b)) * (1 + v * localSparseKernel E (a - b)) := by
  rw [sparseResidueMatrix, Fintype.sum_option, finiteBlockMatrix_apply_none]
  simp only [residuePointCoordinates, map_one, one_mul, mul_one]
  simp_rw [finiteBlockMatrix_apply_some, polydiscLowerLinearMap_apply]
  simp only [one_mul, mul_add, Finset.sum_add_distrib]
  linear_combination (polynomial_kernel_coordinate_identity S E a b ha hb u v).symm

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

theorem sparseTensorKernel_point_identity {n : ℕ} (p : Fin n → ℕ) [∀ i, NeZero (p i)]
    (S : ∀ i, Finset (ZMod (p i))) (a b : ∀ i, ZMod (p i))
    (ha : ∀ i, a i ∈ S i) (hb : ∀ i, b i ∈ Finset.univ \ S i) (u v : ℂ) :
    (∑ x, conj (∏ i, residuePointCoordinates (S i) (a i) (x i)) *
      ∑ y, sparseTensorKernel p S u v x y *
        ∏ i, residuePointCoordinates (Finset.univ \ S i) (b i) (y i)) =
      ∏ i, (1 + u * localSparseKernel
        (largeTransformSpectrum (normalizedResidueTransform (S i))) (a i - b i)) *
        (1 + v * localSparseKernel
          (largeTransformSpectrum (normalizedResidueTransform (S i))) (a i - b i)) := by
  have he := @finiteTensorKernel_pairing (Fin n) inferInstance
    (fun i => Option (ZMod (p i))) (fun i => Option (ZMod (p i))) inferInstance inferInstance
    (fun (i : Fin n) => sparseResidueMatrix (S i)
      (largeTransformSpectrum (normalizedResidueTransform (S i))) u v)
    (fun (i : Fin n) => residuePointCoordinates (S i) (a i))
    (fun (i : Fin n) => residuePointCoordinates (Finset.univ \ S i) (b i))
  unfold sparseTensorKernel
  have hp := Finset.prod_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
    (fun (i : Fin n) _ => sparseResidueMatrix_point_identity (S i)
      (largeTransformSpectrum (normalizedResidueTransform (S i)))
      (a i) (b i) (ha i) (hb i) u v)
  convert he.trans hp using 1
  all_goals try with_reducible_and_instances rfl
  apply Finset.sum_congr
  · ext x
    simp
  · intro x _
    congr 1
    apply Finset.sum_congr
    · ext y
      simp
    · intro y _
      rfl

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

theorem finitePolynomial₂_coefficient_unique {N : ℕ} [NeZero N]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (c d : ℕ → ℕ → E)
    (h : ∀ u v, finitePolynomial₂ c N u v = finitePolynomial₂ d N u v)
    (i j : ℕ) (hi : i < N) (hj : j < N) : c i j = d i j := by
  have hz (u v : ℂ) : finitePolynomial₂ (fun i j => c i j - d i j) N u v = 0 := by
    simp only [finitePolynomial₂, finitePolynomial, smul_sub, Finset.sum_sub_distrib]
    exact sub_eq_zero.mpr (h u v)
  have hc := finitePolynomial₂_coefficient_norm_le (fun i j => c i j - d i j)
    1 0 (by norm_num) (by intro u v _ _; rw [hz]; simp) i j hi hj
  have he : c i j - d i j = 0 := norm_le_zero_iff.mp (by simpa using hc)
  exact sub_eq_zero.mp he

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

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Supply_BilinearCubeSupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Degree bounds the number of centered coordinates -/

namespace Ostmann
open scoped Classical BigOperators

theorem cubeSupport_card_le {n : ℕ} (t : BilinearCube n) :
    (cubeSupport t).card ≤ cubeDegree t false + cubeDegree t true := by
  simp only [cubeSupport, Finset.card_eq_sum_ones, Finset.sum_filter, cubeDegree,
    Bool.false_eq_true, ite_false, if_false, ite_true, if_true, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  cases (t i).1 <;> cases (t i).2 <;> simp

theorem cubeProduct_eq_zero_of_many_coordinates {n : ℕ}
    (W : Fin n → Bool × Bool → ℂ) (Q : Finset (Fin n))
    (hW : ∀ i ∈ Q, W i (false, false) = 0) (t : BilinearCube n)
    (hQ : cubeDegree t false + cubeDegree t true < Q.card) :
    (∏ i, W i (t i)) = 0 := by
  have hnot : ¬ Q ⊆ cubeSupport t := by
    intro hsub
    exact (not_lt_of_ge ((Finset.card_le_card hsub).trans (cubeSupport_card_le t))) hQ
  obtain ⟨i, hi, hti⟩ := Finset.not_subset.mp hnot
  have ht : t i = (false, false) := by
    rcases hh : t i with ⟨a, b⟩
    cases a <;> cases b <;> simp_all [cubeSupport]
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  rw [ht]
  exact hW i hi

theorem cubeCoefficient_eq_zero_of_many_coordinates {n : ℕ}
    (W : Fin n → Bool × Bool → ℂ) (Q : Finset (Fin n))
    (hW : ∀ i ∈ Q, W i (false, false) = 0) (j k : ℕ) (hQ : j + k < Q.card) :
    cubeCoefficient (fun t => ∏ i, W i (t i)) j k = 0 := by
  unfold cubeCoefficient
  apply Finset.sum_eq_zero
  intro t ht
  have hd := (Finset.mem_filter.mp ht).2
  have h₁ : cubeDegree t false = j := congrArg Prod.fst hd
  have h₂ : cubeDegree t true = k := congrArg Prod.snd hd
  apply cubeProduct_eq_zero_of_many_coordinates W Q hW t
  simpa only [h₁, h₂] using hQ

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_SparseTensorModes
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Only low centered modes survive the rectangular truncation -/

namespace Ostmann
open scoped Classical BigOperators

theorem localSparseCoefficient_constant {p : ℕ} [NeZero p]
    (S E : Finset (ZMod p)) (x y : Option (ZMod p)) :
    localSparseCoefficient S E (false, false) x y =
      if x = none ∧ y = none then 1 else 0 := by
  cases x <;> cases y <;>
    simp [localSparseCoefficient, sparseResidueMatrix, finiteBlockMatrix,
      polydiscSparseScalar, polydiscSparseSide, polydiscLowerLinearMap,
      residueLowerLinearMap]

/-- A coefficient of bidegree `(j,k)` vanishes on every output or input
coordinate with more than `j+k` centered factors. -/
theorem sparseTensorCoefficient_mode_support {n : ℕ}
    (p : Fin n → ℕ) [∀ i, NeZero (p i)]
    (S : ∀ i, Finset (ZMod (p i))) (j k : ℕ)
    (x y : ∀ i, Option (ZMod (p i)))
    (h : j + k < (centeredCoordinateSupport x).card ∨
      j + k < (centeredCoordinateSupport y).card) :
    sparseTensorCoefficient p S j k x y = 0 := by
  simp only [sparseTensorCoefficient, cubeCoefficient, Finset.sum_apply]
  change cubeCoefficient (fun t => ∏ i, localSparseCoefficient (S i)
    (largeTransformSpectrum (normalizedResidueTransform (S i))) (t i) (x i) (y i)) j k = 0
  rcases h with h | h
  · apply cubeCoefficient_eq_zero_of_many_coordinates
      (fun i b => localSparseCoefficient (S i)
        (largeTransformSpectrum (normalizedResidueTransform (S i))) b (x i) (y i))
      (centeredCoordinateSupport x) _ j k h
    intro i hi
    have hx : x i ≠ none := (Finset.mem_filter.mp hi).2
    rw [localSparseCoefficient_constant]
    simp [hx]
  · apply cubeCoefficient_eq_zero_of_many_coordinates
      (fun i b => localSparseCoefficient (S i)
        (largeTransformSpectrum (normalizedResidueTransform (S i))) b (x i) (y i))
      (centeredCoordinateSupport y) _ j k h
    intro i hi
    have hy : y i ≠ none := (Finset.mem_filter.mp hi).2
    rw [localSparseCoefficient_constant]
    simp [hy]

theorem truncatedSparseTensorKernel_mode_support {n : ℕ}
    (p : Fin n → ℕ) [∀ i, NeZero (p i)]
    (S : ∀ i, Finset (ZMod (p i))) (K : ℕ)
    (x y : ∀ i, Option (ZMod (p i)))
    (h : 2 * K < (centeredCoordinateSupport x).card ∨
      2 * K < (centeredCoordinateSupport y).card) :
    truncatedSparseTensorKernel p S K x y = 0 := by
  simp only [truncatedSparseTensorKernel, rectangularPolynomialSum, Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro j _
  apply Finset.sum_eq_zero
  intro k _
  by_cases hjk : j ≤ K ∧ k ≤ K
  · simp only [hjk]
    apply sparseTensorCoefficient_mode_support p S j k x y
    rcases h with h | h
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  · simp only [hjk, ite_false, if_false, Pi.zero_apply]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Tree_TruncatedModePairing
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Pairing the truncated kernel against only its active centered modes -/

namespace Ostmann
open WithLp
open scoped Classical BigOperators ComplexConjugate

theorem countingVectorNorm_sq {α : Type*} [Fintype α] (f : α → ℂ) :
    countingVectorNorm f ^ 2 = ∑ x, ‖f x‖ ^ 2 := EuclideanSpace.norm_sq_eq _

theorem finiteKernelOperator_pairing_le {α β : Type*} [Fintype α] [Fintype β]
    (M : α → β → ℂ) (f : α → ℂ) (g : β → ℂ) :
    ‖∑ x, conj (f x) * ∑ y, M x y * g y‖ ≤
      ‖finiteKernelOperator M‖ * countingVectorNorm f * countingVectorNorm g := by
  have he : (∑ x, conj (f x) * ∑ y, M x y * g y) =
      inner ℂ (toLp 2 f : EuclideanSpace ℂ α)
        (finiteKernelOperator M (toLp 2 g)) := by
    simp only [PiLp.inner_apply, RCLike.inner_apply', finiteKernelOperator_apply]
  rw [he]
  calc
    _ ≤ countingVectorNorm f * ‖finiteKernelOperator M (toLp 2 g)‖ := norm_inner_le_norm _ _
    _ ≤ countingVectorNorm f * (‖finiteKernelOperator M‖ * countingVectorNorm g) :=
      mul_le_mul_of_nonneg_left ((finiteKernelOperator M).le_opNorm _) (norm_nonneg _)
    _ = _ := by ring

theorem truncatedSparseTensorKernel_pairing {n : ℕ}
    (p : Fin n → ℕ) [∀ i, NeZero (p i)]
    (S : ∀ i, Finset (ZMod (p i))) (K : ℕ)
    (f g : (∀ i, Option (ZMod (p i))) → ℂ) :
    (∑ x, conj (f x) * ∑ y, truncatedSparseTensorKernel p S K x y * g y) =
      ∑ x, conj (lowModeVector (2 * K) f x) *
        ∑ y, truncatedSparseTensorKernel p S K x y * lowModeVector (2 * K) g y := by
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  by_cases hx : (centeredCoordinateSupport x).card ≤ 2 * K
  · by_cases hy : (centeredCoordinateSupport y).card ≤ 2 * K
    · simp only [lowModeVector, hx, hy, ite_true, if_true]
    · have hz := truncatedSparseTensorKernel_mode_support p S K x y (Or.inr (by omega))
      simp only [hz, mul_zero, zero_mul]
  · have hz := truncatedSparseTensorKernel_mode_support p S K x y (Or.inl (by omega))
    simp only [hz, mul_zero, zero_mul]

theorem truncatedSparseTensorKernel_pairing_le {n : ℕ}
    (p : Fin n → ℕ) [∀ i, NeZero (p i)]
    (S : ∀ i, Finset (ZMod (p i))) (K : ℕ)
    (f g : (∀ i, Option (ZMod (p i))) → ℂ) :
    ‖∑ x, conj (f x) * ∑ y, truncatedSparseTensorKernel p S K x y * g y‖ ≤
      ‖finiteKernelOperator (truncatedSparseTensorKernel p S K)‖ *
        countingVectorNorm (lowModeVector (2 * K) f) *
        countingVectorNorm (lowModeVector (2 * K) g) := by
  rw [truncatedSparseTensorKernel_pairing]
  exact finiteKernelOperator_pairing_le _ _ _

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_FiniteKernelPairing
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Linear evaluation of the finite kernel against two fixed vectors -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

theorem kernelPairing_polynomial {α β : Type*} [Fintype α] [Fintype β]
    (f : α → ℂ) (g : β → ℂ) (c : ℕ → ℕ → α → β → ℂ) (N : ℕ) (u v : ℂ) :
    kernelPairingLinearMap f g (finitePolynomial₂ c N u v) =
      finitePolynomial₂ (fun i j => kernelPairingLinearMap f g (c i j)) N u v := by
  simp only [finitePolynomial₂, finitePolynomial, map_sum, map_smul]

theorem kernelPairing_rectangular {α β : Type*} [Fintype α] [Fintype β]
    (f : α → ℂ) (g : β → ℂ) (c : ℕ → ℕ → α → β → ℂ) (N K : ℕ) :
    kernelPairingLinearMap f g (rectangularPolynomialSum c N K) =
      rectangularPolynomialSum (fun i j => kernelPairingLinearMap f g (c i j)) N K := by
  unfold rectangularPolynomialSum
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> simp only [map_zero]

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
-- module Solutions.OAIQ095_OS.Ostmann_Characters_SparseTruncatedWeight
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The truncated tensor is the squared subset weight -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

theorem sparseTensorCoefficient_point_pairing {n : ℕ}
    (p : Fin n → ℕ) [∀ i, NeZero (p i)] (S : ∀ i, Finset (ZMod (p i)))
    (a b : ∀ i, ZMod (p i)) (ha : ∀ i, a i ∈ S i)
    (hb : ∀ i, b i ∈ Finset.univ \ S i)
    (j k : ℕ) (hj : j < n + 1) (hk : k < n + 1) :
    kernelPairingLinearMap (tensorPointCoordinates p S a)
      (tensorPointCoordinates p (fun i => Finset.univ \ S i) b)
      (sparseTensorCoefficient p S j k) =
        elementaryCoefficient (fun i => localSparseKernel
          (largeTransformSpectrum (normalizedResidueTransform (S i))) (a i - b i)) j *
        elementaryCoefficient (fun i => localSparseKernel
          (largeTransformSpectrum (normalizedResidueTransform (S i))) (a i - b i)) k := by
  apply finitePolynomial₂_coefficient_unique (N := n + 1) _ _ _ j k hj hk
  intro u v
  rw [← kernelPairing_polynomial, ← sparseTensorKernel_polynomial,
    elementaryCoefficient_product]
  change (∑ x, conj (∏ i, residuePointCoordinates (S i) (a i) (x i)) *
    ∑ y, sparseTensorKernel p S u v x y *
      ∏ i, residuePointCoordinates (Finset.univ \ S i) (b i) (y i)) = _
  rw [sparseTensorKernel_point_identity p S a b ha hb u v, Finset.prod_mul_distrib]

theorem truncatedSparseTensorKernel_point_pairing {n : ℕ}
    (p : Fin n → ℕ) [∀ i, NeZero (p i)] (S : ∀ i, Finset (ZMod (p i)))
    (a b : ∀ i, ZMod (p i)) (ha : ∀ i, a i ∈ S i)
    (hb : ∀ i, b i ∈ Finset.univ \ S i) (K : ℕ) :
    kernelPairingLinearMap (tensorPointCoordinates p S a)
      (tensorPointCoordinates p (fun i => Finset.univ \ S i) b)
      (truncatedSparseTensorKernel p S K) =
        elementaryTruncation (fun i => localSparseKernel
          (largeTransformSpectrum (normalizedResidueTransform (S i))) (a i - b i)) K ^ 2 := by
  unfold truncatedSparseTensorKernel
  rw [kernelPairing_rectangular]
  rw [← elementaryTruncation_square]
  unfold rectangularPolynomialSum
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  by_cases h : j ≤ K ∧ k ≤ K
  · simp only [h]
    exact sparseTensorCoefficient_point_pairing p S a b ha hb j k
      (Finset.mem_range.mp hj) (Finset.mem_range.mp hk)
  · simp only [h, ite_false, if_false]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Supply_NonnegativeSparseWeight
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
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

theorem sparseSubsetWeight_nonneg {n : ℕ} (p : Fin n → ℕ) [∀ i, NeZero (p i)]
    (S : ∀ i, Finset (ZMod (p i))) (K : ℕ) (x : ∀ i, ZMod (p i)) :
    0 ≤ sparseSubsetWeight p S K x := sq_nonneg _

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

theorem sparseSubsetWeight_point_pairing {n : ℕ} (p : Fin n → ℕ) [∀ i, Fact (p i).Prime]
    (S : ∀ i, Finset (ZMod (p i))) (K : ℕ)
    (a b : ∀ i, ZMod (p i)) (ha : ∀ i, a i ∈ S i)
    (hb : ∀ i, b i ∈ Finset.univ \ S i) :
    kernelPairingLinearMap (tensorPointCoordinates p S a)
      (tensorPointCoordinates p (fun i => Finset.univ \ S i) b)
      (truncatedSparseTensorKernel p S K) =
        (sparseSubsetWeight p S K (fun i => a i - b i) : ℂ) := by
  rw [sparseSubsetWeight_complex]
  exact truncatedSparseTensorKernel_point_pairing p S a b ha hb K

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Supply_AveragedKernelPairing
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Averaging the actual tensor coordinates over summand elements -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

theorem kernelPairing_sum_left {ι α β : Type*} [Fintype α] [Fintype β]
    (A : Finset ι) (V : ι → α → ℂ) (g : β → ℂ) (M : α → β → ℂ) :
    kernelPairingLinearMap (fun x => ∑ a ∈ A, V a x) g M =
      ∑ a ∈ A, kernelPairingLinearMap (V a) g M := by
  change (∑ x, conj (∑ a ∈ A, V a x) * ∑ y, M x y * g y) = _
  simp only [map_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  rfl

theorem kernelPairing_sum_right {ι α β : Type*} [Fintype α] [Fintype β]
    (A : Finset ι) (f : α → ℂ) (V : ι → β → ℂ) (M : α → β → ℂ) :
    kernelPairingLinearMap f (fun y => ∑ a ∈ A, V a y) M =
      ∑ a ∈ A, kernelPairingLinearMap f (V a) M := by
  change (∑ x, conj (f x) * ∑ y, M x y * ∑ a ∈ A, V a y) = _
  simp only [Finset.mul_sum]
  simp_rw [Finset.sum_comm (s := Finset.univ) (t := A)]
  change _ = ∑ a ∈ A, ∑ x, conj (f x) * ∑ y, M x y * V a y
  simp only [Finset.mul_sum]

theorem kernelPairing_const_mul {α β : Type*} [Fintype α] [Fintype β]
    (f : α → ℂ) (g : β → ℂ) (M : α → β → ℂ) (c d : ℂ) :
    kernelPairingLinearMap (fun x => c * f x) (fun y => d * g y) M =
      conj c * d * kernelPairingLinearMap f g M := by
  change (∑ x, conj (c * f x) * ∑ y, M x y * (d * g y)) =
    conj c * d * ∑ x, conj (f x) * ∑ y, M x y * g y
  simp only [map_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  ring

theorem kernelPairing_averages {ι κ α β : Type*} [Fintype α] [Fintype β]
    (A : Finset ι) (B : Finset κ) (V : ι → α → ℂ) (W : κ → β → ℂ)
    (M : α → β → ℂ) :
    kernelPairingLinearMap (averagedCoordinates A V) (averagedCoordinates B W) M =
      (A.card : ℂ)⁻¹ * (B.card : ℂ)⁻¹ *
        ∑ a ∈ A, ∑ b ∈ B, kernelPairingLinearMap (V a) (W b) M := by
  change kernelPairingLinearMap (fun x => (A.card : ℂ)⁻¹ * ∑ a ∈ A, V a x)
    (fun y => (B.card : ℂ)⁻¹ * ∑ b ∈ B, W b y) M = _
  rw [kernelPairing_const_mul]
  simp only [map_inv₀, map_natCast, kernelPairing_sum_left, kernelPairing_sum_right]
  rw [Finset.sum_comm]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Supply_CenteredRamanujanKernel
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The local Ramanujan identity for the centered-coordinate budget -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

theorem centeredPoint_pairing {p : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (a b : ZMod p) (ha : a ∈ S) (hb : b ∈ S) :
    (∑ x, conj (centeredSupportProjection S (residuePointVector a) x) *
      centeredSupportProjection S (residuePointVector b) x) =
        (if a = b then 1 else 0) - (S.card : ℂ)⁻¹ := by
  rw [centeredSupportProjection_pairing_range]
  simp [centeredSupportProjection, residuePointVector, finiteSupportMean, ha, hb, eq_comm]

theorem nonzero_character_difference_sum {p : ℕ} [NeZero p] (a b : ZMod p) :
    (∑ h ∈ Finset.univ.erase 0, ZMod.stdAddChar (h * (a - b))) =
      (if a = b then (p : ℂ) else 0) - 1 := by
  have he := Finset.sum_erase_add Finset.univ (fun h => ZMod.stdAddChar (h * (a - b)))
    (Finset.mem_univ (0 : ZMod p))
  rw [AddChar.sum_mulShift (a - b) (ZMod.isPrimitive_stdAddChar p)] at he
  simp only [zero_mul, AddChar.map_zero_eq_one, ZMod.card, sub_eq_zero] at he
  by_cases hab : a = b <;> simpa only [hab, ite_true, if_true, ite_false, if_false, Nat.cast_zero] using
    eq_sub_of_add_eq he

theorem centeredRamanujanKernel {p : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (a b : ZMod p) (ha : a ∈ S) (hb : b ∈ S) :
    (∑ h ∈ Finset.univ.erase 0, ZMod.stdAddChar (h * (a - b))) =
      ((p : ℂ) / S.card - 1) + p *
        ∑ x, conj (centeredSupportProjection S (residuePointVector a) x) *
          centeredSupportProjection S (residuePointVector b) x := by
  rw [nonzero_character_difference_sum, centeredPoint_pairing S a b ha hb]
  split_ifs <;> ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Supply_FiniteCoordinateEnergy
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The energy of averaged finite tensor coordinates -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

theorem kernelPairing_identity {α : Type*} [Fintype α] (f g : α → ℂ) :
    kernelPairingLinearMap f g (fun x y => if y = x then 1 else 0) =
      ∑ x, conj (f x) * g x := by
  change (∑ x, conj (f x) * ∑ y, (if y = x then 1 else 0) * g y) = _
  simp

theorem averagedCoordinates_inner {ι κ α : Type*} [Fintype α]
    (A : Finset ι) (B : Finset κ) (V : ι → α → ℂ) (W : κ → α → ℂ) :
    (∑ x, conj (averagedCoordinates A V x) * averagedCoordinates B W x) =
      (A.card : ℂ)⁻¹ * (B.card : ℂ)⁻¹ *
        ∑ a ∈ A, ∑ b ∈ B, ∑ x, conj (V a x) * W b x := by
  have hh := kernelPairing_averages A B V W (fun x y => if y = x then 1 else 0)
  simpa only [kernelPairing_identity] using hh

theorem countingVectorNorm_sq_complex {α : Type*} [Fintype α] (f : α → ℂ) :
    ((countingVectorNorm f ^ 2 : ℝ) : ℂ) = ∑ x, conj (f x) * f x := by
  rw [countingVectorNorm_sq, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro x _
  simpa only [Complex.ofReal_pow, mul_comm] using (Complex.mul_conj' (f x)).symm

theorem productVector_inner {ι : Type*} [Fintype ι] {α : ι → Type*}
    [∀ i, Fintype (α i)] (f g : ∀ i, α i → ℂ) :
    (∑ x : (∀ i, α i), conj (∏ i, f i (x i)) * ∏ i, g i (x i)) =
      ∏ i, ∑ x, conj (f i x) * g i x := by
  simp only [map_prod, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i x => conj (f i x) * g i x)).symm

theorem centeredSubsetEnergy_formula {n : ℕ} (p : Fin n → ℕ) [∀ i, NeZero (p i)]
    (S : ∀ i, Finset (ZMod (p i))) (T : Finset (Fin n)) {ι : Type*}
    (A : Finset ι) (a : ι → ∀ i, ZMod (p i)) :
    (centeredSubsetEnergy p S T A a : ℂ) =
      (A.card : ℂ)⁻¹ * (A.card : ℂ)⁻¹ * ∑ x ∈ A, ∑ y ∈ A,
        ∏ i ∈ T, ∑ z, conj (centeredSupportProjection (S i) (residuePointVector (a x i)) z) *
          centeredSupportProjection (S i) (residuePointVector (a y i)) z := by
  rw [centeredSubsetEnergy, countingVectorNorm_sq_complex, averagedCoordinates_inner]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  have hh := productVector_inner (ι := T) (α := fun i : T => ZMod (p i))
    (fun i z => centeredSupportProjection (S i) (residuePointVector (a x i)) z)
    (fun i z => centeredSupportProjection (S i) (residuePointVector (a y i)) z)
  unfold centeredSubsetVector
  have hp := Finset.prod_coe_sort T (fun i : Fin n => ∑ z : ZMod (p i),
    conj (centeredSupportProjection (S i) (residuePointVector (a x i)) z) *
      centeredSupportProjection (S i) (residuePointVector (a y i)) z)
  convert hh.trans hp using 1
  all_goals try with_reducible_and_instances rfl
  apply Finset.sum_congr
  · ext z
    simp
  · intro z _
    rfl

theorem centeredSubsetEnergy_nonneg {n : ℕ} (p : Fin n → ℕ) [∀ i, NeZero (p i)]
    (S : ∀ i, Finset (ZMod (p i))) (T : Finset (Fin n)) {ι : Type*}
    (A : Finset ι) (a : ι → ∀ i, ZMod (p i)) :
    0 ≤ centeredSubsetEnergy p S T A a := sq_nonneg _

theorem centeredSubsetEnergy_empty {n : ℕ} (p : Fin n → ℕ) [∀ i, NeZero (p i)]
    (S : ∀ i, Finset (ZMod (p i))) {ι : Type*}
    (A : Finset ι) (hA : A.Nonempty) (a : ι → ∀ i, ZMod (p i)) :
    centeredSubsetEnergy p S ∅ A a = 1 := by
  have hAc : (A.card : ℂ) ≠ 0 := by exact_mod_cast (Finset.card_pos.mpr hA).ne'
  rw [centeredSubsetEnergy, countingVectorNorm_sq]
  simp [averagedCoordinates, centeredSubsetVector, hAc]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_TensorRamanujanExpansion
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Expansion of the reduced-frequency kernel by centered subset modes -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

theorem tensorRamanujan_expansion {n : ℕ} (p : Fin n → ℕ) [∀ i, NeZero (p i)]
    (S : ∀ i, Finset (ZMod (p i))) (R : Finset (Fin n))
    (a b : ∀ i, ZMod (p i)) (ha : ∀ i ∈ R, a i ∈ S i) (hb : ∀ i ∈ R, b i ∈ S i) :
    (∏ i ∈ R, ∑ h ∈ Finset.univ.erase (0 : ZMod (p i)), ZMod.stdAddChar (h * (a i - b i))) =
      ∑ T ∈ R.powerset,
        (∏ i ∈ T, (p i : ℂ)) * (∏ i ∈ R \ T, ((p i : ℂ) / (S i).card - 1)) *
          ∏ i ∈ T, centeredResidueGram (S i) (a i) (b i) := by
  calc
    _ = ∏ i ∈ R, ((p i : ℂ) * centeredResidueGram (S i) (a i) (b i) +
        ((p i : ℂ) / (S i).card - 1)) := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [centeredRamanujanKernel (S i) (a i) (b i) (ha i hi) (hb i hi)]
      unfold centeredResidueGram
      ring
    _ = _ := by
      rw [Finset.prod_add]
      apply Finset.sum_congr rfl
      intro T _
      rw [Finset.prod_mul_distrib]
      ring

theorem tensorRamanujan_energy_expansion {n : ℕ} (p : Fin n → ℕ) [∀ i, NeZero (p i)]
    (S : ∀ i, Finset (ZMod (p i))) (R : Finset (Fin n)) {ι : Type*}
    (A : Finset ι) (a : ι → ∀ i, ZMod (p i)) (ha : ∀ x ∈ A, ∀ i ∈ R, a x i ∈ S i) :
    (A.card : ℂ)⁻¹ * (A.card : ℂ)⁻¹ * ∑ x ∈ A, ∑ y ∈ A,
      (∏ i ∈ R, ∑ h ∈ Finset.univ.erase (0 : ZMod (p i)), ZMod.stdAddChar (h * (a x i - a y i))) =
        ∑ T ∈ R.powerset, (∏ i ∈ T, (p i : ℂ)) *
          (∏ i ∈ R \ T, ((p i : ℂ) / (S i).card - 1)) *
            (centeredSubsetEnergy p S T A a : ℂ) := by
  have he (x) (hx : x ∈ A) (y) (hy : y ∈ A) :=
    tensorRamanujan_expansion p S R (a x) (a y) (ha x hx) (ha y hy)
  calc
    _ = (A.card : ℂ)⁻¹ * (A.card : ℂ)⁻¹ * ∑ x ∈ A, ∑ y ∈ A,
        ∑ T ∈ R.powerset, (∏ i ∈ T, (p i : ℂ)) *
          (∏ i ∈ R \ T, ((p i : ℂ) / (S i).card - 1)) *
            ∏ i ∈ T, centeredResidueGram (S i) (a x i) (a y i) := by
      congr 1
      apply Finset.sum_congr rfl
      intro x hx
      exact Finset.sum_congr rfl (fun y hy => he x hx y hy)
    _ = _ := by
      simp_rw [Finset.sum_comm (s := A) (t := R.powerset)]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro T _
      rw [centeredSubsetEnergy_formula]
      simp only [centeredResidueGram, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y _
      ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_TupleCRTFourier
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact cofactor arguments for the Fourier transform of a prime tuple -/

namespace Ostmann

open scoped BigOperators Classical

private theorem stdAddChar_factor {a b M : ℕ} [NeZero a] [NeZero b] [NeZero M]
    (hM : a * b = M) (n : ℕ) :
    ZMod.stdAddChar ((b * n : ℕ) : ZMod M) =
      ZMod.stdAddChar (n : ZMod a) := by
  have hl : ((b * n : ℕ) : ZMod M) = ((b * n : ℕ) : ℤ) := by simp
  have hr : (n : ZMod a) = (n : ℤ) := by simp
  rw [hl, hr, ZMod.stdAddChar_coe, ZMod.stdAddChar_coe]
  congr 1
  push_cast
  rw [← hM, Nat.cast_mul]
  have hb : (b : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne b
  field_simp

theorem tuple_stdAddChar {I : Type*} [Fintype I] (p : I → ℕ)
    [∀ i, NeZero (p i)] [NeZero (∏ i, p i)]
    (hc : Pairwise (fun i j => (p i).Coprime (p j))) (x : ZMod (∏ i, p i)) :
    ZMod.stdAddChar x = ∏ i, ZMod.stdAddChar
      ((tupleCofactor p i : ZMod (p i))⁻¹ * ZMod.prodEquivPi p hc x i) := by
  let a (i : I) : ZMod (p i) :=
    (tupleCofactor p i : ZMod (p i))⁻¹ * ZMod.prodEquivPi p hc x i
  have hx : x = ∑ i, (tupleCofactor p i : ZMod (∏ i, p i)) * (a i).val := by
    apply (ZMod.prodEquivPi p hc).injective
    ext j
    simp only [map_sum, map_mul, map_natCast, Finset.sum_apply, Pi.mul_apply, Pi.natCast_apply]
    rw [Finset.sum_eq_single j]
    · have hu := (ZMod.isUnit_iff_coprime (tupleCofactor p j) (p j)).mpr
        (tupleCofactor_coprime p hc j)
      simp only [ZMod.natCast_zmod_val, a]
      rw [← mul_assoc, ZMod.mul_inv_of_unit _ hu, one_mul]
    · intro i _ hij
      have hd : p j ∣ tupleCofactor p i :=
        Finset.dvd_prod_of_mem p (Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩)
      have hz : (tupleCofactor p i : ZMod (p j)) = 0 :=
        (ZMod.natCast_eq_zero_iff _ _).mpr hd
      simp only [hz, zero_mul]
    · simp
  have hsum (s : Finset I) :
      ZMod.stdAddChar (∑ i ∈ s, (tupleCofactor p i : ZMod (∏ i, p i)) * ((a i).val : ZMod (∏ i, p i))) =
        ∏ i ∈ s, ZMod.stdAddChar ((tupleCofactor p i : ZMod (∏ i, p i)) * ((a i).val : ZMod (∏ i, p i))) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.prod_insert hi, AddChar.map_add_eq_mul, ih]
  conv_lhs => rw [hx, hsum]
  apply Finset.prod_congr rfl
  intro i _
  have hpos : 0 < tupleCofactor p i :=
    Finset.prod_pos (fun j _ => NeZero.pos (p j))
  let : NeZero (tupleCofactor p i) := ⟨hpos.ne'⟩
  simpa only [Nat.cast_mul, ZMod.natCast_zmod_val] using
    (stdAddChar_factor (tupleCofactor_mul p i) (a i).val)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_UnitRamanujanProduct
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The reduced-frequency kernel factors over the actual CRT moduli -/

namespace Ostmann
open scoped Classical BigOperators

theorem unitRamanujanKernel_int_congr {q r : ℕ} [NeZero q] [NeZero r]
    (h : q = r) (z : ℤ) :
    unitRamanujanKernel q (z : ZMod q) = unitRamanujanKernel r (z : ZMod r) := by
  subst r
  rfl

theorem unitRamanujanKernel_scale (q : ℕ) [NeZero q] (c : (ZMod q)ˣ) (z : ZMod q) :
    (∑ u : (ZMod q)ˣ, ZMod.stdAddChar ((c : ZMod q) * (u : ZMod q) * z)) =
      unitRamanujanKernel q z := by
  exact (Equiv.mulLeft c).bijective.sum_comp (fun u : (ZMod q)ˣ =>
    ZMod.stdAddChar ((u : ZMod q) * z))

theorem unitRamanujanKernel_prime {p : ℕ} [Fact p.Prime] (z : ZMod p) :
    unitRamanujanKernel p z =
      ∑ h ∈ Finset.univ.erase (0 : ZMod p), ZMod.stdAddChar (h * z) := by
  apply Finset.sum_bij (fun (u : (ZMod p)ˣ) _ => (u : ZMod p))
  · intro u _
    exact Finset.mem_erase.mpr ⟨Units.ne_zero u, Finset.mem_univ _⟩
  · intro u _ v _ huv
    exact Units.val_injective huv
  · intro x hx
    exact ⟨Units.mk0 x (Finset.mem_erase.mp hx).1, Finset.mem_univ _, rfl⟩
  · intro _ _
    rfl

theorem unitRamanujanKernel_product {I : Type*} [Fintype I]
    (p : I → ℕ) [∀ i, NeZero (p i)] [NeZero (∏ i, p i)]
    (hc : Pairwise (fun i j => (p i).Coprime (p j))) (n : ℤ) :
    unitRamanujanKernel (∏ i, p i) (n : ZMod (∏ i, p i)) =
      ∏ i, unitRamanujanKernel (p i) (n : ZMod (p i)) := by
  have he (u : (ZMod (∏ i, p i))ˣ) :
      ZMod.stdAddChar ((u : ZMod (∏ i, p i)) * (n : ZMod (∏ i, p i))) =
        ∏ i, ZMod.stdAddChar ((tupleCofactor p i : ZMod (p i))⁻¹ *
          (crtUnitEquiv p hc u i : ZMod (p i)) * (n : ZMod (p i))) := by
    rw [tuple_stdAddChar p hc]
    apply Finset.prod_congr rfl
    intro i _
    simp only [map_mul, map_intCast, Pi.mul_apply, Pi.intCast_apply]
    change ZMod.stdAddChar ((tupleCofactor p i : ZMod (p i))⁻¹ *
      ((crtUnitEquiv p hc u i : ZMod (p i)) * (n : ZMod (p i)))) = _
    congr 1
    ring
  unfold unitRamanujanKernel
  simp_rw [he]
  have hh := (crtUnitEquiv p hc).toEquiv.sum_comp (fun u : ∀ i, (ZMod (p i))ˣ =>
    ∏ i, ZMod.stdAddChar ((tupleCofactor p i : ZMod (p i))⁻¹ *
      (u i : ZMod (p i)) * (n : ZMod (p i))))
  calc
    _ = ∑ u : (∀ i, (ZMod (p i))ˣ), ∏ i,
        ZMod.stdAddChar ((tupleCofactor p i : ZMod (p i))⁻¹ *
          (u i : ZMod (p i)) * (n : ZMod (p i))) := hh
    _ = ∏ i, ∑ u : (ZMod (p i))ˣ,
        ZMod.stdAddChar ((tupleCofactor p i : ZMod (p i))⁻¹ *
          (u : ZMod (p i)) * (n : ZMod (p i))) := (Fintype.prod_sum (fun i (u : (ZMod (p i))ˣ) =>
            ZMod.stdAddChar ((tupleCofactor p i : ZMod (p i))⁻¹ *
              (u : ZMod (p i)) * (n : ZMod (p i))))).symm
    _ = _ := by
      apply Finset.prod_congr rfl
      intro i _
      let c := ZMod.unitOfCoprime (tupleCofactor p i) (tupleCofactor_coprime p hc i)
      have hcval : ((c⁻¹ : (ZMod (p i))ˣ) : ZMod (p i)) =
          (tupleCofactor p i : ZMod (p i))⁻¹ := by
        rw [← ZMod.inv_coe_unit]
        simp only [c, ZMod.coe_unitOfCoprime]
      rw [← hcval]
      exact unitRamanujanKernel_scale (p i) c⁻¹ (n : ZMod (p i))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_PrimeDivisors
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Prime-divisor budget in the collision argument

A distinct pair of integers at distance at most `X` contributes at most
`log X` to the sum of `log p` over primes at which it collides. This is the
elementary counting step behind the larger-sieve use in §§2–3.
-/

namespace Ostmann

open scoped BigOperators

/-- The off-diagonal prime-collision budget, in the ordered-pair convention. -/
theorem sum_log_congruent_primes_le_of_sub_le (P : Finset ℕ) {x y X : ℕ}
    (hxy : x < y) (hdiff : y - x ≤ X) (hprime : ∀ p ∈ P, p.Prime) :
    ∑ p ∈ P.filter (fun p => x ≡ y [MOD p]), Real.log (p : ℝ) ≤
      Real.log (X : ℝ) := by
  have hpos : 0 < y - x := Nat.sub_pos_of_lt hxy
  have hbudget := sum_log_prime_divisors_le (P.filter (fun p => x ≡ y [MOD p])) hpos
    (fun p hp => hprime p (Finset.mem_filter.mp hp).1)
    (fun p hp => (Finset.mem_filter.mp hp).2.dvd')
  exact hbudget.trans (Real.log_le_log (by exact_mod_cast hpos)
    (by exact_mod_cast hdiff))

/-- The collision budget for a pair in the initial interval `[0,X]`. -/
theorem sum_log_congruent_primes_le (P : Finset ℕ) {x y X : ℕ}
    (hxy : x < y) (hy : y ≤ X) (hprime : ∀ p ∈ P, p.Prime) :
    ∑ p ∈ P.filter (fun p => x ≡ y [MOD p]), Real.log (p : ℝ) ≤
      Real.log (X : ℝ) :=
  sum_log_congruent_primes_le_of_sub_le P hxy ((Nat.sub_le y x).trans hy) hprime

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

theorem intervalSetReducedEnergy_nonneg {M : ℕ} (A : Finset (Fin M))
    (J : ℤ) (q : ℕ) : 0 ≤ intervalSetReducedEnergy A J q := by
  exact Finset.sum_nonneg (fun h _ => sq_nonneg _)

/-- No density or distribution assumption on the interval subset is needed. -/
theorem additiveSieve_probability_bound (ls : PublishedAdditiveLargeSieve)
    {M Q : ℕ} (hM : 1 ≤ M) (hQ : 1 ≤ Q) (A : Finset (Fin M))
    (hA : A.Nonempty) (J : ℤ) :
    (∑ q ∈ Finset.Icc 1 Q, intervalSetReducedEnergy A J q) ≤
      ((M : ℝ) + (Q : ℝ) ^ 2) / A.card := by
  let c : Fin M → ℂ := fun n => if n ∈ A then 1 else 0
  have hc (q h : ℕ) : additiveSieveSum c J q h = intervalSetExponentialSum A J q h := by
    simp [additiveSieveSum, intervalSetExponentialSum, c]
  have hn : (∑ n, ‖c n‖ ^ 2) = (A.card : ℝ) := by
    have he (n : Fin M) : ‖c n‖ ^ 2 = if n ∈ A then (1 : ℝ) else 0 := by
      by_cases h : n ∈ A <;> simp [c, h]
    simp [he]
  have hh := ls M Q hM hQ J c
  simp only [hc, hn] at hh
  have hcard : (A.card : ℝ) ≠ 0 := by exact_mod_cast (Finset.card_pos.mpr hA).ne'
  calc
    _ = ((A.card : ℝ)⁻¹) ^ 2 *
        ∑ q ∈ Finset.Icc 1 Q, ∑ h ∈ reducedNumerators q,
          ‖intervalSetExponentialSum A J q h‖ ^ 2 := by
      simp only [intervalSetReducedEnergy, norm_mul, norm_inv, Complex.norm_natCast,
        mul_pow, Finset.mul_sum]
    _ ≤ ((A.card : ℝ)⁻¹) ^ 2 * (((M : ℝ) + (Q : ℝ) ^ 2) * A.card) :=
      mul_le_mul_of_nonneg_left hh (sq_nonneg _)
    _ = _ := by field_simp

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
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reduced-frequency energy of a uniform set and its Ramanujan kernel -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

theorem unitFrequencyEnergy_kernel {q : ℕ} [NeZero q] {ι : Type*}
    (A : Finset ι) (a : ι → ZMod q) :
    (unitFrequencyEnergy A a : ℂ) =
      (A.card : ℂ)⁻¹ * (A.card : ℂ)⁻¹ *
        ∑ x ∈ A, ∑ y ∈ A, unitRamanujanKernel q (a x - a y) := by
  have hp (u : (ZMod q)ˣ) :
      ((‖(A.card : ℂ)⁻¹ * ∑ x ∈ A, ZMod.stdAddChar ((u : ZMod q) * a x)‖ ^ 2 : ℝ) : ℂ) =
        (A.card : ℂ)⁻¹ * (A.card : ℂ)⁻¹ * ∑ x ∈ A, ∑ y ∈ A,
          ZMod.stdAddChar ((u : ZMod q) * (a x - a y)) := by
    rw [Complex.ofReal_pow, ← Complex.mul_conj']
    simp only [map_mul, map_inv₀, map_natCast, map_sum, stdAddChar_conj]
    simp only [Finset.mul_sum, Finset.sum_mul]
    conv_lhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    rw [show (u : ZMod q) * (a x - a y) =
      (u : ZMod q) * a x + -((u : ZMod q) * a y) by ring,
      AddChar.map_add_eq_mul]
    ring
  rw [unitFrequencyEnergy, Complex.ofReal_sum]
  simp_rw [hp]
  rw [← Finset.mul_sum]
  congr 1
  simp_rw [Finset.sum_comm (s := Finset.univ) (t := A)]
  rfl

theorem sum_reducedNumerators_eq_units {q : ℕ} [NeZero q]
    {R : Type*} [AddCommMonoid R] (f : ℕ → R) :
    (∑ h ∈ reducedNumerators q, f h) = ∑ u : (ZMod q)ˣ, f (u : ZMod q).val := by
  change (∑ h ∈ reducedResidues q, f h) = _
  rw [← Finset.sum_coe_sort]
  exact ((unitReducedResidueEquiv q).sum_comp (fun a => f a.val)).symm

theorem intervalSetReducedEnergy_eq_unitFrequencyEnergy {M q : ℕ} [NeZero q]
    (A : Finset (Fin M)) (J : ℤ) :
    intervalSetReducedEnergy A J q =
      unitFrequencyEnergy A (fun n => ((J + (n.val : ℤ) : ℤ) : ZMod q)) := by
  unfold intervalSetReducedEnergy unitFrequencyEnergy
  rw [sum_reducedNumerators_eq_units]
  apply Finset.sum_congr rfl
  intro u _
  simp only [intervalSetExponentialSum, sieveAdditivePhase_eq_stdAddChar,
    ZMod.natCast_zmod_val]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Basic
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Sets in Ostmann's inverse Goldbach problem

We use `ℕ` for the manuscript's nonnegative integers. The threshold convention
uses `N ≤ n`; changing finitely many initial values does not affect it.
-/

namespace Ostmann

open scoped symmDiff

/-- Each sufficiently large sum of elements of the summands is prime. -/
theorem EventuallyPrimeSumset.prime_add {A B : Set ℕ}
    (h : EventuallyPrimeSumset A B) :
    ∃ N, ∀ a ∈ A, ∀ b ∈ B, N ≤ a + b → (a + b).Prime := by
  obtain ⟨N, hN⟩ := h
  exact ⟨N, fun a ha b hb hab => (hN (a + b) hab).mp ⟨a, ha, b, hb, rfl⟩⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_Residues
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Complementary residue supports

The elementary reduction in §2 of the manuscript. Only the exclusion of
composite sums is used to separate the tail supports at a prime.
-/

namespace Ostmann

/-- Large sums in an eventual prime decomposition have no smaller prime divisor. -/
theorem EventuallyPrimeSumset.prime_not_dvd_large_sum {A B : Set ℕ}
    (h : EventuallyPrimeSumset A B) :
    ∃ N, ∀ p, p.Prime → ∀ a ∈ A, ∀ b ∈ B,
      N ≤ a + b → p < a + b → ¬ p ∣ a + b := by
  obtain ⟨N, hN⟩ := h
  refine ⟨N, ?_⟩
  intro p hp a ha b hb hn hlt hdvd
  have hab : (a + b).Prime := (hN _ hn).mp ⟨a, ha, b, hb, rfl⟩
  have heq : a + b = p := (hab.dvd_iff_eq (ne_of_gt hp.one_lt)).mp hdvd
  omega

/-- The two tails have disjoint images modulo every prime (§2). -/
theorem EventuallyPrimeSumset.disjoint_tail_residues {A B : Set ℕ}
    (h : EventuallyPrimeSumset A B) :
    ∃ N, ∀ p, p.Prime → Disjoint (tailResidues A N p) (negTailResidues B N p) := by
  obtain ⟨N, hN⟩ := h.prime_not_dvd_large_sum
  refine ⟨N, ?_⟩
  intro p hp
  apply Set.disjoint_left.mpr
  rintro z ⟨a, ⟨ha, hna⟩, rfl⟩ ⟨b, ⟨hb, hnb⟩, hz⟩
  apply hN p hp a ha b hb (by omega) (by omega)
  apply (ZMod.natCast_eq_zero_iff (a + b) p).mp
  change -(b : ZMod p) = (a : ZMod p) at hz
  rw [Nat.cast_add, ← hz]
  simp

/-- The residue-support reduction requires only unboundedness of a summand. -/
theorem tailResidues_nonempty {A : Set ℕ} (hA : A.Infinite) (N p : ℕ) :
    (tailResidues A N p).Nonempty := by
  have hnot : ¬ BddAbove A := fun h => hA (Set.finite_iff_bddAbove.mpr h)
  obtain ⟨a, ha, hlarge⟩ := (not_bddAbove_iff.mp hnot) (N + p)
  exact ⟨(a : ZMod p), a, ⟨ha, hlarge⟩, rfl⟩

theorem negTailResidues_nonempty {B : Set ℕ} (hB : B.Infinite) (N p : ℕ) :
    (negTailResidues B N p).Nonempty := by
  have hnot : ¬ BddAbove B := fun h => hB (Set.finite_iff_bddAbove.mpr h)
  obtain ⟨b, hb, hlarge⟩ := (not_bddAbove_iff.mp hnot) (N + p)
  exact ⟨-(b : ZMod p), b, ⟨hb, hlarge⟩, rfl⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_WeightedCollision
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Weighted prime collisions

The elementary weighted pair count used in Lemma 2.5 (collision stability).
The diagonal is paid for by the largest atom; unequal pairs are paid for by
one logarithm of the interval length.
-/

namespace Ostmann

open scoped BigOperators

theorem primeCollisionWeight_self (P : Finset ℕ) (a : ℕ) :
    primeCollisionWeight P a a = ∑ p ∈ P, Real.log (p : ℝ) := by
  simp [primeCollisionWeight, Nat.ModEq.refl]

theorem primeCollisionWeight_symm (P : Finset ℕ) (a b : ℕ) :
    primeCollisionWeight P a b = primeCollisionWeight P b a := by
  unfold primeCollisionWeight
  congr 1
  ext p
  simp only [Finset.mem_filter]
  exact and_congr_right (fun _ => ⟨fun h => h.symm, fun h => h.symm⟩)

theorem primeCollisionWeight_le_log {P : Finset ℕ} {a b X : ℕ}
    (hab : a ≠ b) (ha : a ≤ X) (hb : b ≤ X) (hP : ∀ p ∈ P, p.Prime) :
    primeCollisionWeight P a b ≤ Real.log (X : ℝ) := by
  rcases lt_or_gt_of_ne hab with hab | hba
  · exact sum_log_congruent_primes_le P hab hb hP
  · rw [primeCollisionWeight_symm]
    exact sum_log_congruent_primes_le P hba ha hP

/-- The weighted pair count from an off-diagonal logarithmic budget. -/
theorem weighted_prime_collision_bound_of_budget (P S : Finset ℕ) (μ : ℕ → ℝ) (L m : ℝ)
    (hL : 0 ≤ L) (hP : ∀ p ∈ P, p.Prime) (hμ : ∀ a ∈ S, 0 ≤ μ a)
    (hmass : ∑ a ∈ S, μ a = 1) (hatom : ∀ a ∈ S, μ a ≤ m)
    (hbudget : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → primeCollisionWeight P a b ≤ L) :
    (∑ a ∈ S, ∑ b ∈ S, μ a * μ b * primeCollisionWeight P a b) ≤
      L + m * ∑ p ∈ P, Real.log (p : ℝ) := by
  classical
  let W : ℝ := ∑ p ∈ P, Real.log (p : ℝ)
  have hW : 0 ≤ W := Finset.sum_nonneg (fun p hp => Real.log_nonneg (by exact_mod_cast (hP p hp).one_le))
  have hpair : ∀ a ∈ S, ∀ b ∈ S,
      primeCollisionWeight P a b ≤ L + if a = b then W else 0 := by
    intro a ha b hb
    by_cases hab : a = b
    · subst b
      simp only [primeCollisionWeight_self, ite_true, if_true]
      dsimp [W] at *
      linarith
    · simpa [hab] using hbudget a ha b hb hab
  have hsquares : (∑ a ∈ S, μ a ^ 2) ≤ m := by
    calc
      (∑ a ∈ S, μ a ^ 2) ≤ ∑ a ∈ S, m * μ a := by
        apply Finset.sum_le_sum
        intro a ha
        nlinarith [hμ a ha, hatom a ha]
      _ = m := by rw [← Finset.mul_sum, hmass, mul_one]
  calc
    _ ≤ ∑ a ∈ S, ∑ b ∈ S, μ a * μ b * (L + if a = b then W else 0) := by
      apply Finset.sum_le_sum
      intro a ha
      apply Finset.sum_le_sum
      intro b hb
      exact mul_le_mul_of_nonneg_left (hpair a ha b hb) (mul_nonneg (hμ a ha) (hμ b hb))
    _ = L + W * ∑ a ∈ S, μ a ^ 2 := by
      simp_rw [mul_add, Finset.sum_add_distrib]
      have hconstant : (∑ a ∈ S, ∑ b ∈ S, μ a * μ b * L) = L := by
        calc
          _ = ∑ a ∈ S, μ a * (∑ b ∈ S, μ b) * L := by
            apply Finset.sum_congr rfl
            intro a _
            rw [← Finset.sum_mul, ← Finset.mul_sum]
          _ = L := by
            rw [hmass]
            simp only [mul_one]
            rw [← Finset.sum_mul, hmass, one_mul]
      rw [hconstant]
      congr 1
      simp only [mul_ite, mul_zero, Finset.sum_ite_eq]
      calc
        (∑ a ∈ S, if a ∈ S then μ a * μ a * W else 0) =
            ∑ a ∈ S, W * μ a ^ 2 := by
          apply Finset.sum_congr rfl
          intro a ha
          simp only [ha, ite_true, if_true]
          ring
        _ = W * ∑ a ∈ S, μ a ^ 2 := (Finset.mul_sum _ _ _).symm
    _ ≤ L + W * m := add_le_add_right (mul_le_mul_of_nonneg_left hsquares hW) L
    _ = _ := by dsimp [W]; ring

/-- Weighted larger-sieve pair bound on the interval `[0,X]`. -/
theorem weighted_prime_collision_bound (P S : Finset ℕ) (μ : ℕ → ℝ) (X : ℕ) (m : ℝ)
    (hX : 1 ≤ X) (hP : ∀ p ∈ P, p.Prime)
    (hS : ∀ a ∈ S, a ≤ X) (hμ : ∀ a ∈ S, 0 ≤ μ a)
    (hmass : ∑ a ∈ S, μ a = 1) (hatom : ∀ a ∈ S, μ a ≤ m) :
    (∑ a ∈ S, ∑ b ∈ S, μ a * μ b * primeCollisionWeight P a b) ≤
      Real.log (X : ℝ) + m * ∑ p ∈ P, Real.log (p : ℝ) :=
  weighted_prime_collision_bound_of_budget P S μ (Real.log X) m
    (Real.log_nonneg (by exact_mod_cast hX)) hP hμ hmass hatom
    (fun a ha b hb hab => primeCollisionWeight_le_log hab (hS a ha) (hS b hb) hP)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_Projection
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Residue projection of finite probability measures

These identities connect the pair count in `WeightedCollision` with the
collision norm of a projected measure, as used in Lemma 2.5 of the paper.
-/

namespace Ostmann

open scoped BigOperators

theorem sum_fiberMass_mul {α β : Type*} [DecidableEq β]
    (s : Finset α) (t : Finset β) (μ : α → ℝ) (f : α → β) (F : β → ℝ)
    (hf : ∀ a ∈ s, f a ∈ t) :
    ∑ y ∈ t, fiberMass s μ f y * F y = ∑ a ∈ s, μ a * F (f a) := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to hf (fun a => μ a * F (f a))]
  apply Finset.sum_congr rfl
  intro y _
  unfold fiberMass
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  rw [(Finset.mem_filter.mp ha).2]

theorem sum_fiberMass {α β : Type*} [DecidableEq β]
    (s : Finset α) (t : Finset β) (μ : α → ℝ) (f : α → β)
    (hf : ∀ a ∈ s, f a ∈ t) :
    ∑ y ∈ t, fiberMass s μ f y = ∑ a ∈ s, μ a := by
  simpa only [mul_one] using sum_fiberMass_mul s t μ f (fun _ => 1) hf

theorem sum_fiberMass_sq {α β : Type*} [DecidableEq β]
    (s : Finset α) (t : Finset β) (μ : α → ℝ) (f : α → β)
    (hf : ∀ a ∈ s, f a ∈ t) :
    ∑ y ∈ t, (fiberMass s μ f y) ^ 2 =
      ∑ a ∈ s, ∑ b ∈ s, if f a = f b then μ a * μ b else 0 := by
  classical
  simp only [pow_two]
  rw [sum_fiberMass_mul s t μ f (fiberMass s μ f) hf]
  apply Finset.sum_congr rfl
  intro a _
  simp only [fiberMass, Finset.sum_filter, Finset.mul_sum, mul_ite, mul_zero]
  apply Finset.sum_congr rfl
  intro b _
  simp only [eq_comm]

theorem residueMass_sq (s : Finset ℕ) (μ : ℕ → ℝ) {p : ℕ}
    (hp : 0 < p) :
    ∑ r ∈ Finset.range p, (residueMass s μ p r) ^ 2 =
      ∑ a ∈ s, ∑ b ∈ s, if a ≡ b [MOD p] then μ a * μ b else 0 :=
  sum_fiberMass_sq s (Finset.range p) μ (fun a => a % p)
    (fun a _ => Finset.mem_range.mpr (Nat.mod_lt a hp))

/-- Reorder the weighted residue collisions as a sum over integer pairs. -/
theorem weighted_residueMass_sq (P s : Finset ℕ) (μ : ℕ → ℝ)
    (hP : ∀ p ∈ P, p.Prime) :
    (∑ p ∈ P, Real.log (p : ℝ) *
      ∑ r ∈ Finset.range p, (residueMass s μ p r) ^ 2) =
    ∑ a ∈ s, ∑ b ∈ s, μ a * μ b * primeCollisionWeight P a b := by
  classical
  calc
    _ = ∑ p ∈ P, ∑ a ∈ s, ∑ b ∈ s,
        Real.log (p : ℝ) * (if a ≡ b [MOD p] then μ a * μ b else 0) := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [residueMass_sq s μ (hP p hp).pos]
      simp only [Finset.mul_sum]
    _ = ∑ a ∈ s, ∑ b ∈ s, ∑ p ∈ P,
        Real.log (p : ℝ) * (if a ≡ b [MOD p] then μ a * μ b else 0) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      simp only [primeCollisionWeight, Finset.sum_filter, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      split_ifs <;> ring

/-- The quantitative weighted collision bound for projected probabilities. -/
theorem residue_collision_bound (P s : Finset ℕ) (μ : ℕ → ℝ) (X : ℕ) (m : ℝ)
    (hX : 1 ≤ X) (hP : ∀ p ∈ P, p.Prime)
    (hs : ∀ a ∈ s, a ≤ X) (hμ : ∀ a ∈ s, 0 ≤ μ a)
    (hmass : ∑ a ∈ s, μ a = 1) (hatom : ∀ a ∈ s, μ a ≤ m) :
    (∑ p ∈ P, Real.log (p : ℝ) *
      ∑ r ∈ Finset.range p, (residueMass s μ p r) ^ 2) ≤
      Real.log (X : ℝ) + m * ∑ p ∈ P, Real.log (p : ℝ) := by
  rw [weighted_residueMass_sq P s μ hP]
  exact weighted_prime_collision_bound P s μ X m hX hP hs hμ hmass hatom

/-- Residue labels may be changed (in particular, negated) without changing
the collision norm, provided they identify exactly the congruent pairs. -/
theorem fiberMass_sq_eq_residueMass_sq (s t : Finset ℕ) (μ : ℕ → ℝ)
    (f : ℕ → ℕ) {p : ℕ} (hp : 0 < p)
    (hf : ∀ a ∈ s, f a ∈ t)
    (hcongr : ∀ a ∈ s, ∀ b ∈ s, f a = f b ↔ a ≡ b [MOD p]) :
    (∑ r ∈ t, (fiberMass s μ f r) ^ 2) =
      ∑ r ∈ Finset.range p, (residueMass s μ p r) ^ 2 := by
  rw [sum_fiberMass_sq s t μ f hf, residueMass_sq s μ hp]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  simp only [hcongr a ha b hb]

/-- The weighted pair bound applies on any chosen residue support, including
the negative residue support of the second summand. -/
theorem fiber_collision_bound (P s : Finset ℕ) (μ : ℕ → ℝ)
    (t : ℕ → Finset ℕ) (f : ℕ → ℕ → ℕ) (X : ℕ) (m : ℝ)
    (hX : 1 ≤ X) (hP : ∀ p ∈ P, p.Prime)
    (hs : ∀ a ∈ s, a ≤ X) (hμ : ∀ a ∈ s, 0 ≤ μ a)
    (hmass : ∑ a ∈ s, μ a = 1) (hatom : ∀ a ∈ s, μ a ≤ m)
    (hf : ∀ p ∈ P, ∀ a ∈ s, f p a ∈ t p)
    (hcongr : ∀ p ∈ P, ∀ a ∈ s, ∀ b ∈ s, f p a = f p b ↔ a ≡ b [MOD p]) :
    (∑ p ∈ P, Real.log (p : ℝ) *
      ∑ r ∈ t p, (fiberMass s μ (f p) r) ^ 2) ≤
      Real.log (X : ℝ) + m * ∑ p ∈ P, Real.log (p : ℝ) := by
  convert residue_collision_bound P s μ X m hX hP hs hμ hmass hatom using 1
  all_goals try with_reducible_and_instances rfl
  apply Finset.sum_congr rfl
  intro p hp
  rw [fiberMass_sq_eq_residueMass_sq s (t p) μ (f p) (hP p hp).pos
    (hf p hp) (hcongr p hp)]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_Stability
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The finite collision-stability inequality

This is the finite quantitative calculation in Lemma 2.5 of the manuscript.
The final theorem takes the exact numerical consequences of Chebyshev's
bound and Mertens' first theorem at the chosen cutoff as explicit hypotheses.
No main theorem of the manuscript is assumed here.
-/

namespace Ostmann

open scoped BigOperators

theorem collisionDefect_nonneg {p : ℕ} (s t : Finset ℕ) (μ ν : ℕ → ℝ)
    (hs : s.Nonempty) (ht : t.Nonempty) (hcard : s.card + t.card ≤ p) :
    0 ≤ collisionDefect p s t μ ν := by
  have hspos : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
  have htpos : (0 : ℝ) < t.card := by exact_mod_cast ht.card_pos
  have hcard' : (s.card : ℝ) + t.card ≤ p := by exact_mod_cast hcard
  have hgap := four_div_le_inverse_add_inverse hspos htpos hcard'
  have hμ : 0 ≤ ∑ r ∈ s, (μ r - 1 / (s.card : ℝ)) ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hν : 0 ≤ ∑ r ∈ t, (ν r - 1 / (t.card : ℝ)) ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  unfold collisionDefect
  linarith

theorem collisionDefect_eq (p : ℕ) (s t : Finset ℕ) (μ ν : ℕ → ℝ)
    (hs : s.Nonempty) (ht : t.Nonempty)
    (hμ : ∑ r ∈ s, μ r = 1) (hν : ∑ r ∈ t, ν r = 1) :
    collisionDefect p s t μ ν =
      (∑ r ∈ s, μ r ^ 2) + (∑ r ∈ t, ν r ^ 2) - 4 / (p : ℝ) := by
  unfold collisionDefect
  rw [collision_sub_uniform s μ hs hμ, collision_sub_uniform t ν ht hν]
  ring

/-- The sum of stability defects is the sum of the collision energies minus
the universal baseline `4 ∑ log p / p`. -/
theorem weighted_collisionDefect_eq (P : Finset ℕ) (s t : ℕ → Finset ℕ)
    (μ ν : ℕ → ℕ → ℝ)
    (hs : ∀ p ∈ P, (s p).Nonempty) (ht : ∀ p ∈ P, (t p).Nonempty)
    (hμ : ∀ p ∈ P, ∑ r ∈ s p, μ p r = 1)
    (hν : ∀ p ∈ P, ∑ r ∈ t p, ν p r = 1) :
    (∑ p ∈ P, Real.log (p : ℝ) * collisionDefect p (s p) (t p) (μ p) (ν p)) =
      (∑ p ∈ P, Real.log (p : ℝ) * ∑ r ∈ s p, μ p r ^ 2) +
      (∑ p ∈ P, Real.log (p : ℝ) * ∑ r ∈ t p, ν p r ^ 2) -
      4 * ∑ p ∈ P, Real.log (p : ℝ) / (p : ℝ) := by
  calc
    _ = ∑ p ∈ P,
        ((Real.log (p : ℝ) * ∑ r ∈ s p, μ p r ^ 2) +
        (Real.log (p : ℝ) * ∑ r ∈ t p, ν p r ^ 2) -
        4 * (Real.log (p : ℝ) / (p : ℝ))) := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [collisionDefect_eq p (s p) (t p) (μ p) (ν p)
        (hs p hp) (ht p hp) (hμ p hp) (hν p hp)]
      ring
    _ = _ := by
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]

/-- A finite, explicit form of collision stability. The two energy bounds
come from `residue_collision_bound`; the last two hypotheses are exactly
the prime-sum estimates needed at the cutoff, rather than full asymptotic
theories. Mertens' first theorem (1874) supplies the lower prime sum. -/
theorem collision_stability_of_prime_sums (P : Finset ℕ)
    (s t : ℕ → Finset ℕ) (μ ν : ℕ → ℕ → ℝ)
    (X Q : ℕ) (m K C : ℝ)
    (hs : ∀ p ∈ P, (s p).Nonempty) (ht : ∀ p ∈ P, (t p).Nonempty)
    (hμ : ∀ p ∈ P, ∑ r ∈ s p, μ p r = 1)
    (hν : ∀ p ∈ P, ∑ r ∈ t p, ν p r = 1)
    (hm : 0 ≤ m)
    (henergyμ : (∑ p ∈ P, Real.log (p : ℝ) * ∑ r ∈ s p, μ p r ^ 2) ≤
      Real.log (X : ℝ) + m * ∑ p ∈ P, Real.log (p : ℝ))
    (henergyν : (∑ p ∈ P, Real.log (p : ℝ) * ∑ r ∈ t p, ν p r ^ 2) ≤
      Real.log (X : ℝ) + m * ∑ p ∈ P, Real.log (p : ℝ))
    (hchebyshev : (∑ p ∈ P, Real.log (p : ℝ)) ≤ K * Q)
    (hmertens : Real.log (Q : ℝ) - C ≤
      ∑ p ∈ P, Real.log (p : ℝ) / (p : ℝ)) :
    (∑ p ∈ P, Real.log (p : ℝ) * collisionDefect p (s p) (t p) (μ p) (ν p)) ≤
      2 * Real.log (X : ℝ) - 4 * Real.log (Q : ℝ) + 4 * C + 2 * m * K * Q := by
  rw [weighted_collisionDefect_eq P s t μ ν hs ht hμ hν]
  have hweight := mul_le_mul_of_nonneg_left hchebyshev hm
  nlinarith

/-- Apply the stability inequality to two actual finite measures on integers.
The maps `f` and `g` label their residue classes; allowing a relabeling is
needed for the negative second summand. The prime-sum hypotheses are the
finite specializations of the published inputs used here. -/
theorem finite_measure_collision_stability (P A B : Finset ℕ)
    (μ ν : ℕ → ℝ) (s t : ℕ → Finset ℕ) (f g : ℕ → ℕ → ℕ)
    (X Q : ℕ) (m K C : ℝ)
    (hX : 1 ≤ X) (hP : ∀ p ∈ P, p.Prime)
    (hA : ∀ a ∈ A, a ≤ X) (hB : ∀ b ∈ B, b ≤ X)
    (hμ : ∀ a ∈ A, 0 ≤ μ a) (hν : ∀ b ∈ B, 0 ≤ ν b)
    (hmassμ : ∑ a ∈ A, μ a = 1) (hmassν : ∑ b ∈ B, ν b = 1)
    (hatomμ : ∀ a ∈ A, μ a ≤ m) (hatomν : ∀ b ∈ B, ν b ≤ m)
    (hs : ∀ p ∈ P, (s p).Nonempty) (ht : ∀ p ∈ P, (t p).Nonempty)
    (hf : ∀ p ∈ P, ∀ a ∈ A, f p a ∈ s p)
    (hg : ∀ p ∈ P, ∀ b ∈ B, g p b ∈ t p)
    (hcongrf : ∀ p ∈ P, ∀ a ∈ A, ∀ b ∈ A, f p a = f p b ↔ a ≡ b [MOD p])
    (hcongrg : ∀ p ∈ P, ∀ a ∈ B, ∀ b ∈ B, g p a = g p b ↔ a ≡ b [MOD p])
    (hm : 0 ≤ m)
    (hchebyshev : (∑ p ∈ P, Real.log (p : ℝ)) ≤ K * Q)
    (hmertens : Real.log (Q : ℝ) - C ≤
      ∑ p ∈ P, Real.log (p : ℝ) / (p : ℝ)) :
    (∑ p ∈ P, Real.log (p : ℝ) *
      collisionDefect p (s p) (t p) (fiberMass A μ (f p)) (fiberMass B ν (g p))) ≤
      2 * Real.log (X : ℝ) - 4 * Real.log (Q : ℝ) + 4 * C + 2 * m * K * Q := by
  apply collision_stability_of_prime_sums P s t
    (fun p => fiberMass A μ (f p)) (fun p => fiberMass B ν (g p))
    X Q m K C hs ht
  · intro p hp
    rw [sum_fiberMass A (s p) μ (f p) (hf p hp)]
    exact hmassμ
  · intro p hp
    rw [sum_fiberMass B (t p) ν (g p) (hg p hp)]
    exact hmassν
  · exact hm
  · exact fiber_collision_bound P A μ s f X m hX hP hA hμ hmassμ hatomμ hf hcongrf
  · exact fiber_collision_bound P B ν t g X m hX hP hB hν hmassν hatomν hg hcongrg
  · exact hchebyshev
  · exact hmertens

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_TailStability
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Collision stability on the two summand tails

This specializes the finite collision bound to the complementary supports
forced by an eventual prime decomposition. Prime-sum estimates remain
explicit hypotheses; no statement about the existence of a decomposition
is assumed as an analytic input.
-/

namespace Ostmann

open scoped BigOperators

theorem negativeResidue_eq_iff {p a b : ℕ} (hp : 0 < p) :
    negativeResidue p a = negativeResidue p b ↔ a ≡ b [MOD p] := by
  let : NeZero p := ⟨Nat.ne_of_gt hp⟩
  unfold negativeResidue
  rw [(ZMod.val_injective p).eq_iff, neg_inj, ZMod.natCast_eq_natCast_iff]

theorem tailSupport_subset (A : Set ℕ) (N p : ℕ) :
    tailSupport A N p ⊆ Finset.range p := by
  classical
  exact Finset.filter_subset _ _

theorem mod_mem_tailSupport {A : Set ℕ} {N p a : ℕ} (hp : 0 < p)
    (ha : a ∈ A) (hlarge : N + p < a) : a % p ∈ tailSupport A N p := by
  classical
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_range.mpr (Nat.mod_lt a hp), ?_⟩
  have heq : ((a % p : ℕ) : ZMod p) = (a : ZMod p) := by simp
  rw [heq]
  exact ⟨a, ⟨ha, hlarge⟩, rfl⟩

theorem tailSupport_nonempty {A : Set ℕ} (hA : A.Infinite) (N p : ℕ)
    (hp : 0 < p) : (tailSupport A N p).Nonempty := by
  obtain ⟨_, a, ⟨ha, hlarge⟩, rfl⟩ := tailResidues_nonempty hA N p
  exact ⟨a % p, mod_mem_tailSupport hp ha hlarge⟩

theorem negativeResidue_mem_complement {A B : Set ℕ} {N p b : ℕ}
    (hp : 0 < p) (hdisjoint : Disjoint (tailResidues A N p) (negTailResidues B N p))
    (hb : b ∈ B) (hlarge : N + p < b) :
    negativeResidue p b ∈ Finset.range p \ tailSupport A N p := by
  classical
  let : NeZero p := ⟨Nat.ne_of_gt hp⟩
  apply Finset.mem_sdiff.mpr
  refine ⟨Finset.mem_range.mpr (ZMod.val_lt _), ?_⟩
  intro hmem
  have ha := (Finset.mem_filter.mp hmem).2
  change ((-(b : ZMod p)).val : ZMod p) ∈ tailResidues A N p at ha
  rw [ZMod.natCast_zmod_val] at ha
  exact Set.disjoint_left.mp hdisjoint ha ⟨b, ⟨hb, hlarge⟩, rfl⟩

theorem tailSupport_complement_nonempty {A B : Set ℕ} (hB : B.Infinite)
    {N p : ℕ} (hp : 0 < p)
    (hdisjoint : Disjoint (tailResidues A N p) (negTailResidues B N p)) :
    (Finset.range p \ tailSupport A N p).Nonempty := by
  obtain ⟨_, b, ⟨hb, hlarge⟩, rfl⟩ := negTailResidues_nonempty hB N p
  exact ⟨negativeResidue p b, negativeResidue_mem_complement hp hdisjoint hb hlarge⟩

theorem tailSupport_card_add_complement (A : Set ℕ) (N p : ℕ) :
    (tailSupport A N p).card + (Finset.range p \ tailSupport A N p).card = p := by
  rw [Nat.add_comm, Finset.card_sdiff_add_card_eq_card (tailSupport_subset A N p)]
  exact Finset.card_range p

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_PrimeSumInputs
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Ostmann

open scoped BigOperators

theorem prime_log_weight_le (Q : ℕ) :
    (∑ p ∈ Nat.primesLE Q, Real.log (p : ℝ)) ≤ Real.log 4 * Q := by
  rw [← Chebyshev.theta_eq_sum_primesLE_log]
  exact Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg Q)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_MertensPrimeBands
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact published Mertens input for logarithmic prime bands

F. Mertens, J. reine angew. Math. 78 (1874), 46–62, first theorem,
DOI 10.1515/crll.1874.78.46. Both sides of the bounded-error estimate
are needed to subtract the lower cutoff; the collision argument uses
only its previously recorded lower-bound consequence.
-/

namespace Ostmann

open scoped BigOperators Classical

theorem MertensEstimate.lower {C : ℝ} (h : MertensEstimate C) : MertensLowerBound C := by
  intro Q hQ
  have hh := (abs_le.mp (h Q hQ)).1
  linarith

theorem MertensEstimate.upper {C : ℝ} (h : MertensEstimate C) (Q : ℕ) (hQ : 1 ≤ Q) :
    (∑ p ∈ Nat.primesLE Q, Real.log (p : ℝ) / p) ≤ Real.log Q + C := by
  have hh := (abs_le.mp (h Q hQ)).2
  linarith

theorem floor_exp_log_bounds (T : ℝ) (hT : 1 ≤ T) :
    1 ≤ ⌊Real.exp T⌋₊ ∧ T - Real.log 2 ≤ Real.log (⌊Real.exp T⌋₊ : ℝ) ∧
      Real.log (⌊Real.exp T⌋₊ : ℝ) ≤ T := by
  have he : 2 ≤ Real.exp T := by linarith [Real.add_one_le_exp T]
  have hfloor : (1 : ℕ) ≤ ⌊Real.exp T⌋₊ :=
    (Nat.one_le_floor_iff _).mpr (by linarith)
  have hfp : (0 : ℝ) < ⌊Real.exp T⌋₊ := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 1) hfloor)
  have hhalf : Real.exp T / 2 ≤ (⌊Real.exp T⌋₊ : ℝ) := by
    have := Nat.sub_one_lt_floor (Real.exp T)
    linarith
  have hlo := Real.log_le_log (show 0 < Real.exp T / 2 by positivity) hhalf
  rw [Real.log_div (Real.exp_ne_zero _) (by norm_num), Real.log_exp] at hlo
  have hhi := Real.log_le_log hfp (Nat.floor_le (Real.exp_nonneg T))
  rw [Real.log_exp] at hhi
  exact ⟨hfloor, hlo, hhi⟩

theorem logPrimeBand_mem {T : ℝ} {p : ℕ} (hp : p ∈ logPrimeBand T) :
    p.Prime ∧ T < Real.log (p : ℝ) ∧ Real.log (p : ℝ) ≤ 2 * T := by
  obtain ⟨hhi, hlo⟩ := Finset.mem_sdiff.mp hp
  have hprime := Nat.prime_of_mem_primesLE hhi
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hprime.pos
  have hlo' : ⌊Real.exp T⌋₊ < p := by
    by_contra hn
    exact hlo (Nat.mem_primesLE.mpr ⟨Nat.le_of_not_gt hn, hprime⟩)
  have hloR : Real.exp T < (p : ℝ) := (Nat.floor_lt (Real.exp_nonneg _)).mp hlo'
  have hhiR : (p : ℝ) ≤ Real.exp (2 * T) :=
    (by exact_mod_cast Nat.le_of_mem_primesLE hhi : (p : ℝ) ≤ ⌊Real.exp (2 * T)⌋₊).trans
      (Nat.floor_le (Real.exp_nonneg _))
  exact ⟨hprime, (Real.lt_log_iff_exp_lt hp0).mpr hloR,
    (Real.log_le_iff_le_exp hp0).mpr hhiR⟩

theorem logPrimeBand_weight_bounds (T C : ℝ) (hT : 1 ≤ T) (hM : MertensEstimate C) :
    T - Real.log 2 - 2 * C ≤ (∑ p ∈ logPrimeBand T, Real.log (p : ℝ) / p) ∧
      (∑ p ∈ logPrimeBand T, Real.log (p : ℝ) / p) ≤ T + Real.log 2 + 2 * C := by
  have hT0 : 0 ≤ T := by linarith
  have hlo := floor_exp_log_bounds T hT
  have hhi := floor_exp_log_bounds (2 * T) (by linarith)
  have hsub : Nat.primesLE ⌊Real.exp T⌋₊ ⊆ Nat.primesLE ⌊Real.exp (2 * T)⌋₊ := by
    intro p hp
    exact Nat.mem_primesLE.mpr ⟨(Nat.le_of_mem_primesLE hp).trans
      (Nat.floor_mono (Real.exp_le_exp.mpr (by linarith))), Nat.prime_of_mem_primesLE hp⟩
  rw [logPrimeBand, Finset.sum_sdiff_eq_sub hsub]
  constructor
  · have h1 := hM.lower _ hhi.1
    have h2 := hM.upper _ hlo.1
    linarith [hhi.2.1, hlo.2.2]
  · have h1 := hM.upper _ hhi.1
    have h2 := hM.lower _ hlo.1
    linarith [hhi.2.2, hlo.2.1]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_MertensHarmonicBands
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Mertens' second theorem on the iterated-logarithm band

F. Mertens, *Ein Beitrag zur analytischen Zahlentheorie*, J. reine angew.
Math. 78 (1874), 46–62, second theorem. We only require its weaker bounded
error consequence `sum_{p≤Q} 1/p = log log Q + O(1)`. The pinned PNT library
states this specialization as `Mertens.sum_prime_div_eq_log_log`.
-/

namespace Ostmann
open Filter
open scoped Classical BigOperators

private theorem floor_exp_loglog_bounds (s : ℝ) (hs : 2 ≤ s) :
    2 ≤ ⌊Real.exp (Real.exp s)⌋₊ ∧
      s - Real.log 2 ≤ Real.log (Real.log (⌊Real.exp (Real.exp s)⌋₊ : ℝ)) ∧
      Real.log (Real.log (⌊Real.exp (Real.exp s)⌋₊ : ℝ)) ≤ s := by
  have he : 2 ≤ Real.exp s := by linarith [Real.add_one_le_exp s]
  have hf := floor_exp_log_bounds (Real.exp s) (by linarith)
  have hQ : 2 ≤ ⌊Real.exp (Real.exp s)⌋₊ := by
    apply Nat.le_floor
    norm_num only [Nat.cast_ofNat]
    linarith [Real.add_one_le_exp (Real.exp s)]
  have hlogQ : 0 < Real.log (⌊Real.exp (Real.exp s)⌋₊ : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < ⌊Real.exp (Real.exp s)⌋₊ by omega))
  have h2 : Real.log 2 ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    linarith
  have hh : Real.exp s / 2 ≤ Real.log (⌊Real.exp (Real.exp s)⌋₊ : ℝ) := by
    linarith [hf.2.1]
  refine ⟨hQ, ?_, ?_⟩
  · have hl := Real.log_le_log (show 0 < Real.exp s / 2 by positivity) hh
    rw [Real.log_div (Real.exp_ne_zero _) (by norm_num), Real.log_exp] at hl
    exact hl
  · have hu := Real.log_le_log hlogQ hf.2.2
    simpa only [Real.log_exp] using hu

theorem logLogPrimeBand_mem {L : ℝ} {p : ℕ} (hp : p ∈ logLogPrimeBand L) :
    p.Prime ∧ Real.exp ((1 / 20 : ℝ) * L) < Real.log (p : ℝ) ∧
      Real.log (p : ℝ) ≤ Real.exp ((9 / 10 : ℝ) * L) := by
  obtain ⟨hhi, hlo⟩ := Finset.mem_sdiff.mp hp
  have hprime := Nat.prime_of_mem_primesLE hhi
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hprime.pos
  have hlo' : ⌊Real.exp (Real.exp ((1 / 20 : ℝ) * L))⌋₊ < p := by
    by_contra hn
    exact hlo (Nat.mem_primesLE.mpr ⟨Nat.le_of_not_gt hn, hprime⟩)
  have hloR : Real.exp (Real.exp ((1 / 20 : ℝ) * L)) < (p : ℝ) :=
    (Nat.floor_lt (Real.exp_nonneg _)).mp hlo'
  have hhiR : (p : ℝ) ≤ Real.exp (Real.exp ((9 / 10 : ℝ) * L)) :=
    (Nat.cast_le.mpr (Nat.le_of_mem_primesLE hhi)).trans (Nat.floor_le (Real.exp_nonneg _))
  exact ⟨hprime, (Real.lt_log_iff_exp_lt hp0).mpr hloR,
    (Real.log_le_iff_le_exp hp0).mpr hhiR⟩

theorem logLogPrimeBand_harmonic_lower {C : ℝ} (hM : MertensHarmonicEstimate C)
    (L : ℝ) (hL : 40 ≤ L) :
    (17 / 20 : ℝ) * L - Real.log 2 - 2 * C ≤
      ∑ p ∈ logLogPrimeBand L, (p : ℝ)⁻¹ := by
  have hlo := floor_exp_loglog_bounds ((1 / 20 : ℝ) * L) (by linarith)
  have hhi := floor_exp_loglog_bounds ((9 / 10 : ℝ) * L) (by linarith)
  have hsub : Nat.primesLE ⌊Real.exp (Real.exp ((1 / 20 : ℝ) * L))⌋₊ ⊆
      Nat.primesLE ⌊Real.exp (Real.exp ((9 / 10 : ℝ) * L))⌋₊ := by
    intro p hp
    refine Nat.mem_primesLE.mpr ⟨(Nat.le_of_mem_primesLE hp).trans ?_, Nat.prime_of_mem_primesLE hp⟩
    apply Nat.floor_mono
    apply Real.exp_le_exp.mpr
    apply Real.exp_le_exp.mpr
    linarith
  rw [logLogPrimeBand, Finset.sum_sdiff_eq_sub hsub]
  have hlow := (abs_le.mp (hM _ hhi.1)).1
  have hupp := (abs_le.mp (hM _ hlo.1)).2
  linarith [hhi.2.1, hlo.2.2]

theorem logLogPrimeBand_harmonic_upper {C : ℝ} (hM : MertensHarmonicEstimate C)
    (L : ℝ) (hL : 40 ≤ L) :
    (∑ p ∈ logLogPrimeBand L, (p : ℝ)⁻¹) ≤
      (17 / 20 : ℝ) * L + Real.log 2 + 2 * C := by
  have hlo := floor_exp_loglog_bounds ((1 / 20 : ℝ) * L) (by linarith)
  have hhi := floor_exp_loglog_bounds ((9 / 10 : ℝ) * L) (by linarith)
  have hsub : Nat.primesLE ⌊Real.exp (Real.exp ((1 / 20 : ℝ) * L))⌋₊ ⊆
      Nat.primesLE ⌊Real.exp (Real.exp ((9 / 10 : ℝ) * L))⌋₊ := by
    intro p hp
    refine Nat.mem_primesLE.mpr ⟨(Nat.le_of_mem_primesLE hp).trans ?_, Nat.prime_of_mem_primesLE hp⟩
    apply Nat.floor_mono
    apply Real.exp_le_exp.mpr
    apply Real.exp_le_exp.mpr
    linarith
  rw [logLogPrimeBand, Finset.sum_sdiff_eq_sub hsub]
  have hlow := (abs_le.mp (hM _ hlo.1)).1
  have hupp := (abs_le.mp (hM _ hhi.1)).2
  linarith [hlo.2.1, hhi.2.2]

theorem eventual_logLogPrimeBand_harmonic_le {C : ℝ} (hM : MertensHarmonicEstimate C) :
    ∀ᶠ L : ℝ in Filter.atTop, (∑ p ∈ logLogPrimeBand L, (p : ℝ)⁻¹) ≤ L := by
  filter_upwards [Filter.eventually_ge_atTop (max 40 ((20 / 3 : ℝ) * (Real.log 2 + 2 * C)))]
    with L hL
  have hh := logLogPrimeBand_harmonic_upper hM L ((le_max_left _ _).trans hL)
  have hnum := (le_max_right 40 ((20 / 3 : ℝ) * (Real.log 2 + 2 * C))).trans hL
  linarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityDefectSelection
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Small collision defect forces balanced supports and accurate tests -/

namespace Ostmann

open scoped BigOperators Classical

theorem reciprocal_gap_forces_thirds (a b p : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hsum : a + b = p) (hgap : p * (1 / a + 1 / b - 4 / p) ≤ 1 / 4) :
    p / 3 ≤ a ∧ a ≤ 2 * p / 3 := by
  have hp : 0 < p := by linarith
  have hab : 0 < a * b := mul_pos ha hb
  have hid : p * (1 / a + 1 / b - 4 / p) = (a - b) ^ 2 / (a * b) := by
    field_simp
    rw [← hsum]
    ring
  have hsq : (a - b) ^ 2 ≤ (1 / 4 : ℝ) * (a * b) := by
    apply (div_le_iff₀ hab).mp
    rwa [← hid]
  constructor
  · by_contra! h
    have hba : 0 ≤ b - 2 * a := by linarith
    have hab' : 0 ≤ 2 * b - a := by linarith
    nlinarith [mul_nonneg hba hab']
  · by_contra! h
    have hab' : 0 ≤ a - 2 * b := by linarith
    have hba : 0 ≤ 2 * a - b := by linarith
    nlinarith [mul_nonneg hab' hba]

theorem small_defect_balances_supports (p : ℕ) (S T : Finset ℕ) (μ ν : ℕ → ℝ)
    (hS : S.Nonempty) (hT : T.Nonempty) (hcard : S.card + T.card = p)
    (hsmall : (p : ℝ) * collisionDefect p S T μ ν ≤ 1 / 4) :
    (p : ℝ) / 3 ≤ S.card ∧ (S.card : ℝ) ≤ 2 * p / 3 := by
  apply reciprocal_gap_forces_thirds (S.card : ℝ) T.card p
    (by exact_mod_cast hS.card_pos) (by exact_mod_cast hT.card_pos) (by exact_mod_cast hcard)
  have henergy : 0 ≤ (∑ r ∈ S, (μ r - 1 / (S.card : ℝ)) ^ 2) +
      ∑ r ∈ T, (ν r - 1 / (T.card : ℝ)) ^ 2 := by positivity
  have hm := mul_nonneg (Nat.cast_nonneg (α := ℝ) p) henergy
  unfold collisionDefect at hsmall
  nlinarith only [hsmall, hm]

/-- Weighted Markov bound, used with cost `p * collisionDefect`. -/
theorem weighted_cost_exception_bound (P : Finset ℕ) (w cost : ℕ → ℝ) (δ : ℝ)
    (hw : ∀ p ∈ P, 0 ≤ w p) (hcost : ∀ p ∈ P, 0 ≤ cost p) :
    δ * (∑ p ∈ P.filter (fun p => δ < cost p), w p) ≤ ∑ p ∈ P, w p * cost p := by
  rw [Finset.mul_sum]
  calc
    _ ≤ ∑ p ∈ P.filter (fun p => δ < cost p), w p * cost p := by
      apply Finset.sum_le_sum
      intro p hp
      have hp' := Finset.mem_filter.mp hp
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left hp'.2.le (hw p hp'.1)
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun p hp _ => mul_nonneg (hw p hp) (hcost p hp))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Supply_CollisionPrimeCellBudget
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Good cells from the proved collision-stability budget -/

namespace Ostmann
open scoped Classical BigOperators

theorem collisionExceptionalPrimes_log_mass (P : Finset ℕ)
    (S T : ℕ → Finset ℕ) (μ ν : ℕ → ℕ → ℝ) (E : ℝ)
    (hprime : ∀ p ∈ P, p.Prime)
    (hS : ∀ p ∈ P, (S p).Nonempty) (hT : ∀ p ∈ P, (T p).Nonempty)
    (hcard : ∀ p ∈ P, (S p).card + (T p).card ≤ p)
    (hbudget : (∑ p ∈ P, Real.log (p : ℝ) *
      collisionDefect p (S p) (T p) (μ p) (ν p)) ≤ E) :
    (∑ p ∈ collisionExceptionalPrimes P S T μ ν, Real.log (p : ℝ) / p) ≤ 4 * E := by
  have h := weighted_cost_exception_bound P (fun p => Real.log (p : ℝ) / p)
    (fun p => (p : ℝ) * collisionDefect p (S p) (T p) (μ p) (ν p)) (1 / 4)
    (fun p hp => div_nonneg (Real.log_nonneg (by exact_mod_cast (hprime p hp).one_le))
      (Nat.cast_nonneg _))
    (fun p hp => mul_nonneg (Nat.cast_nonneg _)
      (collisionDefect_nonneg _ _ _ _ (hS p hp) (hT p hp) (hcard p hp)))
  have heq : (∑ p ∈ P, Real.log (p : ℝ) / p *
      ((p : ℝ) * collisionDefect p (S p) (T p) (μ p) (ν p))) =
      ∑ p ∈ P, Real.log (p : ℝ) * collisionDefect p (S p) (T p) (μ p) (ν p) := by
    apply Finset.sum_congr rfl
    intro p hp
    have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (hprime p hp).ne_zero
    field_simp
  rw [heq] at h
  change (1 / 4 : ℝ) * (∑ p ∈ collisionExceptionalPrimes P S T μ ν,
    Real.log (p : ℝ) / p) ≤ _ at h
  linarith

theorem collision_retained_prime_balanced (P : Finset ℕ)
    (S T : ℕ → Finset ℕ) (μ ν : ℕ → ℕ → ℝ)
    (hS : ∀ p ∈ P, (S p).Nonempty) (hT : ∀ p ∈ P, (T p).Nonempty)
    (hcard : ∀ p ∈ P, (S p).card + (T p).card = p)
    (p : ℕ) (hp : p ∈ P \ collisionExceptionalPrimes P S T μ ν) :
    (p : ℝ) / 3 ≤ (S p).card ∧ ((S p).card : ℝ) ≤ 2 * p / 3 := by
  obtain ⟨hpP, hpnot⟩ := Finset.mem_sdiff.mp hp
  have hsmall : (p : ℝ) * collisionDefect p (S p) (T p) (μ p) (ν p) ≤ 1 / 4 := by
    by_contra! hh
    exact hpnot (Finset.mem_filter.mpr ⟨hpP, hh⟩)
  exact small_defect_balances_supports p (S p) (T p) (μ p) (ν p)
    (hS p hpP) (hT p hpP) (hcard p hpP) hsmall

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Supply_FavorableMassAlternative
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Failure of favorable mass forces a large sparse balanced prime set -/

namespace Ostmann
open scoped Classical BigOperators

theorem sparse_transform_mass_lower (P : Finset ℕ) (S T : ℕ → Finset ℕ)
    (μ ν : ℕ → ℕ → ℝ) (γ : ℕ → ℝ) (δ G D : ℝ) (hG : 0 < G)
    (hprime : ∀ p ∈ P, p.Prime) (hlog : ∀ p ∈ P, G ≤ Real.log (p : ℝ))
    (hS : ∀ p ∈ P, (S p).Nonempty) (hT : ∀ p ∈ P, (T p).Nonempty)
    (hcard : ∀ p ∈ P, (S p).card + (T p).card = p)
    (hbudget : (∑ p ∈ P, Real.log (p : ℝ) * collisionDefect p (S p) (T p) (μ p) (ν p)) ≤ D) :
    (∑ p ∈ P, (p : ℝ)⁻¹) - 4 * D / G -
        (∑ p ∈ favorableTransformPrimes P S γ δ, (p : ℝ)⁻¹) ≤
      ∑ p ∈ sparseTransformPrimes P S γ δ, (p : ℝ)⁻¹ := by
  let E := collisionExceptionalPrimes P S T μ ν
  let F := favorableTransformPrimes P S γ δ
  let R := P \ (E ∪ F)
  have hE : E ⊆ P := Finset.filter_subset _ _
  have hF : F ⊆ P := Finset.filter_subset _ _
  have hbad := collisionExceptionalPrimes_log_mass P S T μ ν D hprime hS hT
    (fun p hp => (hcard p hp).le) hbudget
  have hbadmass : (∑ p ∈ E, (p : ℝ)⁻¹) ≤ 4 * D / G := by
    apply (le_div_iff₀ hG).mpr
    calc
      _ = ∑ p ∈ E, G * (p : ℝ)⁻¹ := by rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intros; ring
      _ ≤ ∑ p ∈ E, Real.log (p : ℝ) / p := by
        apply Finset.sum_le_sum
        intro p hp
        simpa only [div_eq_mul_inv] using
          mul_le_mul_of_nonneg_right (hlog p (hE hp)) (by positivity : 0 ≤ (p : ℝ)⁻¹)
      _ ≤ _ := hbad
  have hR : R ⊆ sparseTransformPrimes P S γ δ := by
    intro p hp
    obtain ⟨hpP, hpnot⟩ := Finset.mem_sdiff.mp hp
    have hpE : p ∉ E := fun he => hpnot (Finset.mem_union_left _ he)
    have hpF : p ∉ F := fun hf => hpnot (Finset.mem_union_right _ hf)
    have hb := collision_retained_prime_balanced P S T μ ν hS hT hcard p
      (Finset.mem_sdiff.mpr ⟨hpP, hpE⟩)
    apply Finset.mem_filter.mpr
    refine ⟨hpP, hb.1, hb.2, ?_⟩
    by_contra h
    exact hpF (Finset.mem_filter.mpr ⟨hpP, hb.1, hb.2, le_of_not_gt h⟩)
  have hremove : (∑ p ∈ R, (p : ℝ)⁻¹) =
      (∑ p ∈ P, (p : ℝ)⁻¹) - ∑ p ∈ E ∪ F, (p : ℝ)⁻¹ :=
    Finset.sum_sdiff_eq_sub (Finset.union_subset hE hF)
  have hunion := Finset.sum_union_inter (s₁ := E) (s₂ := F) (f := fun p => (p : ℝ)⁻¹)
  have hinter : 0 ≤ ∑ p ∈ E ∩ F, (p : ℝ)⁻¹ := Finset.sum_nonneg (fun _ _ => by positivity)
  have hremaining : (∑ p ∈ P, (p : ℝ)⁻¹) - (∑ p ∈ E, (p : ℝ)⁻¹) -
      (∑ p ∈ F, (p : ℝ)⁻¹) ≤ ∑ p ∈ R, (p : ℝ)⁻¹ := by linarith
  have hmass : (∑ p ∈ R, (p : ℝ)⁻¹) ≤ ∑ p ∈ sparseTransformPrimes P S γ δ, (p : ℝ)⁻¹ :=
    Finset.sum_le_sum_of_subset_of_nonneg hR (fun _ _ _ => by positivity)
  change _ - 4 * D / G - (∑ p ∈ F, (p : ℝ)⁻¹) ≤ _
  linarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_SummandTails
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual finite tails of the two summands -/

namespace Ostmann

open scoped Classical

theorem summandPrefix_card_split (A : Set ℕ) (lo hi : ℕ) (hle : lo ≤ hi) :
    (summandPrefix A hi).card = (summandPrefix A lo).card + (summandTail A lo hi).card := by
  have hlo : (summandPrefix A hi).filter (fun n => n ≤ lo) = summandPrefix A lo := by
    ext n
    simp only [Finset.mem_filter, mem_summandPrefix]
    constructor
    · rintro ⟨⟨ha, _⟩, hn⟩; exact ⟨ha, hn⟩
    · rintro ⟨ha, hn⟩; exact ⟨⟨ha, hn.trans hle⟩, hn⟩
  have hhi : (summandPrefix A hi).filter (fun n => ¬ n ≤ lo) = summandTail A lo hi := by
    ext n
    simp only [Finset.mem_filter, mem_summandPrefix, mem_summandTail]
    constructor
    · rintro ⟨⟨ha, hh⟩, hn⟩; exact ⟨ha, Nat.lt_of_not_ge hn, hh⟩
    · rintro ⟨ha, hn, hh⟩; exact ⟨⟨ha, hh⟩, Nat.not_le_of_lt hn⟩
  have hh := Finset.card_filter_add_card_filter_not (s := summandPrefix A hi) (fun n => n ≤ lo)
  rw [hlo, hhi] at hh
  exact hh.symm

theorem positiveSummandTail_bounds (A : Set ℕ) (lo hi : ℕ) {x : ℤ}
    (hx : x ∈ positiveSummandTail A lo hi) : (lo : ℤ) < x ∧ x ≤ hi := by
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨_, hnlo, hnhi⟩ := (mem_summandTail A lo hi n).mp hn
  exact ⟨by exact_mod_cast hnlo, by exact_mod_cast hnhi⟩

theorem negativeSummandTail_bounds (B : Set ℕ) (lo hi : ℕ) {x : ℤ}
    (hx : x ∈ negativeSummandTail B lo hi) : -(hi : ℤ) ≤ x ∧ x < -(lo : ℤ) := by
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨_, hnlo, hnhi⟩ := (mem_summandTail B lo hi n).mp hn
  constructor <;> omega

theorem EventuallyPrimeSumset.tail_prime_differences {A B : Set ℕ}
    (h : EventuallyPrimeSumset A B) :
    ∃ N : ℕ, ∀ lo hi : ℕ, N ≤ lo →
      ∀ x ∈ positiveSummandTail A lo hi, ∀ y ∈ negativeSummandTail B lo hi,
        (x - y).natAbs.Prime ∧ (lo : ℤ) < x - y := by
  obtain ⟨N, hN⟩ := h.prime_add
  refine ⟨N, ?_⟩
  intro lo hi hNlo x hx y hy
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
  obtain ⟨haA, halo, _⟩ := (mem_summandTail A lo hi a).mp ha
  obtain ⟨hbB, _, _⟩ := (mem_summandTail B lo hi b).mp hb
  have hab : (a : ℤ) - -(b : ℤ) = ((a + b : ℕ) : ℤ) := by push_cast; ring
  rw [hab, Int.natAbs_natCast]
  exact ⟨hN a haA b hbB (by omega), by exact_mod_cast (by omega : lo < a + b)⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_TailCountingBudget
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing the short initial segment preserves the square-root lower bound -/

namespace Ostmann

open Filter

theorem eventual_tail_counting_budget (a C : ℝ) (ha : 0 < a) (hC : 0 ≤ C) :
    ∀ᶠ L : ℝ in atTop, ∀ (A : Set ℕ) (lo hi : ℕ), lo ≤ hi → 1 ≤ lo →
      (lo : ℝ) ≤ Real.exp (9 * L / 10) →
      a * Real.exp (L / 2) / L ^ 3 ≤ (summandPrefix A hi).card →
      (summandPrefix A lo).card ≤ C * Real.sqrt (lo : ℝ) * Real.log (lo : ℝ) ^ 2 →
      (a / 2) * Real.exp (L / 2) / L ^ 3 ≤ (summandTail A lo hi).card := by
  have hp := ((isLittleO_pow_exp_pos_mul_atTop 5 (show (0 : ℝ) < 1 / 20 by norm_num)).const_mul_left
    (2 * C / a)).bound (show (0 : ℝ) < 1 by norm_num)
  filter_upwards [hp, eventually_ge_atTop (1 : ℝ)] with L hpoly hL A lo hi hlo h1 hupper hsize hsmall
  have hLp : 0 < L := by linarith
  have hloR : (1 : ℝ) ≤ lo := by exact_mod_cast h1
  have hloPos : (0 : ℝ) < lo := by linarith
  have hlog0 : 0 ≤ Real.log (lo : ℝ) := Real.log_nonneg hloR
  have hlog : Real.log (lo : ℝ) ≤ L := by
    have hh := Real.log_le_log hloPos hupper
    rw [Real.log_exp] at hh
    linarith
  have hsqrt : Real.sqrt (lo : ℝ) ≤ Real.exp (9 * L / 20) := by
    have hh := Real.sqrt_le_sqrt hupper
    have he : Real.exp (9 * L / 10) = (Real.exp (9 * L / 20)) ^ 2 := by
      rw [← Real.exp_nat_mul]; congr 1; norm_num; ring
    rwa [he, Real.sqrt_sq (Real.exp_nonneg _)] at hh
  have hsmall' : (summandPrefix A lo).card ≤ C * Real.exp (9 * L / 20) * L ^ 2 := by
    apply hsmall.trans
    exact mul_le_mul (mul_le_mul_of_nonneg_left hsqrt hC)
      (pow_le_pow_left₀ hlog0 hlog 2) (sq_nonneg _) (by positivity)
  have hpoly' : (2 * C / a) * L ^ 5 ≤ Real.exp (L / 20) := by
    have he : Real.exp ((1 / 20 : ℝ) * L) = Real.exp (L / 20) := by congr 1; ring
    rw [he] at hpoly
    simpa only [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (2 * C / a) * L ^ 5),
      abs_of_pos (Real.exp_pos _), one_mul] using hpoly
  have hdiscard : C * Real.exp (9 * L / 20) * L ^ 2 ≤ (a / 2) * Real.exp (L / 2) / L ^ 3 := by
    apply (le_div_iff₀ (pow_pos hLp 3)).mpr
    have hh : C * L ^ 5 ≤ (a / 2) * Real.exp (L / 20) := by
      have hm := mul_le_mul_of_nonneg_right hpoly' (show 0 ≤ a / 2 by positivity)
      have hcancel : (2 * C / a) * L ^ 5 * (a / 2) = C * L ^ 5 := by
        calc
          _ = (C * L ^ 5) * (a * a⁻¹) := by ring
          _ = _ := by rw [mul_inv_cancel₀ ha.ne', mul_one]
      rw [hcancel] at hm
      linarith only [hm]
    have hm := mul_le_mul_of_nonneg_left hh (Real.exp_nonneg (9 * L / 20))
    have he : Real.exp (9 * L / 20) * Real.exp (L / 20) = Real.exp (L / 2) := by
      rw [← Real.exp_add]; congr 1; ring
    calc
      _ = Real.exp (9 * L / 20) * (C * L ^ 5) := by ring
      _ ≤ Real.exp (9 * L / 20) * ((a / 2) * Real.exp (L / 20)) := hm
      _ = _ := by rw [mul_left_comm, he]
  have hsplit : (summandPrefix A hi).card =
      (summandPrefix A lo).card + (summandTail A lo hi).card := summandPrefix_card_split A lo hi hlo
  have hsplitR : ((summandPrefix A hi).card : ℝ) =
      (summandPrefix A lo).card + (summandTail A lo hi).card := by exact_mod_cast hsplit
  have hh := hsmall'.trans hdiscard
  ring_nf at hh hsize ⊢
  linarith only [hh, hsize, hsplitR]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_LargeSummandTails
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Large actual tails from the published summand counting bounds -/

namespace Ostmann

open Filter
open scoped Classical

theorem exists_large_summand_tails (hsize : PublishedSummandSizeBound)
    {A B : Set ℕ} (hA : A.Infinite) (hB : B.Infinite) (h : EventuallyPrimeSumset A B) :
    ∃ a : ℝ, 0 < a ∧ ∀ᶠ L : ℝ in atTop, ∀ N : ℕ, (N : ℝ) = Real.exp L →
      a * Real.exp (L / 2) / L ^ 3 ≤ (positiveSummandTail A (summandTailCutoff L) N).card ∧
      a * Real.exp (L / 2) / L ^ 3 ≤ (negativeSummandTail B (summandTailCutoff L) N).card ∧
      (∀ x ∈ positiveSummandTail A (summandTailCutoff L) N,
        0 ≤ (x : ℝ) ∧ (x : ℝ) ≤ N) ∧
      (∀ y ∈ negativeSummandTail B (summandTailCutoff L) N,
        -(N : ℝ) ≤ (y : ℝ) ∧ (y : ℝ) ≤ 0) ∧
      (∀ x ∈ positiveSummandTail A (summandTailCutoff L) N,
        ∀ y ∈ negativeSummandTail B (summandTailCutoff L) N,
        (x - y).natAbs.Prime ∧ Real.exp (9 * L / 10) < ((x - y).natAbs : ℝ)) := by
  obtain ⟨a, C, ha, hC, N₀, hcounts⟩ := hsize A B hA hB h
  obtain ⟨N₁, hprime⟩ := h.tail_prime_differences
  let K := max N₀ (max N₁ 2)
  refine ⟨a / 2, by positivity, ?_⟩
  filter_upwards [eventual_tail_counting_budget a C ha hC.le,
    eventually_ge_atTop (2 * ((K : ℝ) + 2))] with L hbudget hL N hN
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg _
  have hLpos : 0 < L := by linarith
  have hL0 : 0 ≤ L := hLpos.le
  have hKexp : (K : ℝ) ≤ Real.exp (9 * L / 10) := by
    have he := Real.add_one_le_exp (9 * L / 10)
    have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg _
    linarith
  have hKcut : K ≤ summandTailCutoff L := Nat.le_floor hKexp
  have hcutupper : (summandTailCutoff L : ℝ) ≤ Real.exp (9 * L / 10) :=
    Nat.floor_le (Real.exp_nonneg _)
  have hcutN : summandTailCutoff L ≤ N := by
    have he : Real.exp (9 * L / 10) ≤ Real.exp L := Real.exp_le_exp.mpr (by linarith)
    have hh := hcutupper.trans he
    rw [← hN] at hh
    exact_mod_cast hh
  have hN₀cut : N₀ ≤ summandTailCutoff L := (le_max_left _ _).trans hKcut
  have hN₁cut : N₁ ≤ summandTailCutoff L :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hKcut)
  have h2cut : 2 ≤ summandTailCutoff L :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hKcut)
  have hcntN := hcounts N (hN₀cut.trans hcutN) (h2cut.trans hcutN)
  have hcntCut := hcounts (summandTailCutoff L) hN₀cut h2cut
  have hsqrt : Real.sqrt (N : ℝ) = Real.exp (L / 2) := by
    rw [hN]
    have he : Real.exp L = (Real.exp (L / 2)) ^ 2 := by
      rw [← Real.exp_nat_mul]; congr 1; norm_num; ring
    rw [he, Real.sqrt_sq (Real.exp_nonneg _)]
  have hlog : Real.log (N : ℝ) = L := by rw [hN, Real.log_exp]
  have hsa : a * Real.exp (L / 2) / L ^ 3 ≤ (summandPrefix A N).card := by
    simpa only [hsqrt, hlog] using hcntN.1
  have hsb : a * Real.exp (L / 2) / L ^ 3 ≤ (summandPrefix B N).card := by
    simpa only [hsqrt, hlog] using hcntN.2.2.1
  have htailA := hbudget A (summandTailCutoff L) N hcutN (by omega) hcutupper hsa hcntCut.2.1
  have htailB := hbudget B (summandTailCutoff L) N hcutN (by omega) hcutupper hsb hcntCut.2.2.2
  refine ⟨by simpa only [positiveSummandTail_card] using htailA,
    by simpa only [negativeSummandTail_card] using htailB, ?_, ?_, ?_⟩
  · intro x hx
    have hb := positiveSummandTail_bounds A _ _ hx
    have hx0 : (0 : ℤ) ≤ x := by omega
    exact ⟨by exact_mod_cast hx0, by exact_mod_cast hb.2⟩
  · intro y hy
    have hb := negativeSummandTail_bounds B _ _ hy
    have hy0 : y ≤ (0 : ℤ) := by omega
    exact ⟨by exact_mod_cast hb.1, by exact_mod_cast hy0⟩
  · intro x hx y hy
    have hp := hprime (summandTailCutoff L) N hN₁cut x hx y hy
    refine ⟨hp.1, ?_⟩
    have hd : 0 ≤ x - y := by omega
    have he : ((x - y).natAbs : ℤ) = x - y := by rw [Int.natCast_natAbs, abs_of_nonneg hd]
    have hn : summandTailCutoff L < (x - y).natAbs := by omega
    exact (Nat.floor_lt (Real.exp_nonneg _)).mp hn

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_TailCollisionCutoff
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The square-root prime cutoff and its logarithmic collision budget -/

namespace Ostmann

open Filter
open scoped BigOperators Classical

theorem tailCollisionCutoff_bounds (L : ℝ) (hL : 1 ≤ L)
    (hr : 2 ≤ Real.exp (L / 2) / L ^ 5) :
    1 ≤ tailCollisionCutoff L ∧
    (tailCollisionCutoff L : ℝ) ≤ Real.exp (L / 2) / L ^ 5 ∧
    L / 2 - 5 * Real.log L - Real.log 2 ≤ Real.log (tailCollisionCutoff L : ℝ) := by
  have hLp : 0 < L := by linarith
  have hrp : 0 < Real.exp (L / 2) / L ^ 5 := by positivity
  have hQ : 1 ≤ tailCollisionCutoff L := (Nat.one_le_floor_iff _).mpr (show (1 : ℝ) ≤ _ by linarith)
  have hhalf : (Real.exp (L / 2) / L ^ 5) / 2 ≤ (tailCollisionCutoff L : ℝ) := by
    have hh := Nat.sub_one_lt_floor (Real.exp (L / 2) / L ^ 5)
    change Real.exp (L / 2) / L ^ 5 - 1 < (tailCollisionCutoff L : ℝ) at hh
    linarith
  refine ⟨hQ, Nat.floor_le hrp.le, ?_⟩
  have hh := Real.log_le_log (show 0 < (Real.exp (L / 2) / L ^ 5) / 2 by positivity) hhalf
  rw [Real.log_div (ne_of_gt hrp) (by norm_num),
    Real.log_div (Real.exp_ne_zero _) (pow_ne_zero 5 hLp.ne'),
    Real.log_exp, Real.log_pow] at hh
  exact hh

theorem eventual_tailCollisionCutoff (N : ℕ) :
    ∀ᶠ L : ℝ in atTop, 1 ≤ L ∧ 2 ≤ Real.exp (L / 2) / L ^ 5 ∧
      N + tailCollisionCutoff L ≤ summandTailCutoff L := by
  have hb := ((isLittleO_pow_exp_pos_mul_atTop 5 (show (0 : ℝ) < 1 / 2 by norm_num)).const_mul_left 2).bound
    (show (0 : ℝ) < 1 by norm_num)
  filter_upwards [hb, eventually_ge_atTop (3 * ((N : ℝ) + 3))] with L hb hL
  have hL1 : 1 ≤ L := by have := Nat.cast_nonneg (α := ℝ) N; linarith
  have hLp : 0 < L := by linarith
  have hpoly : 2 * L ^ 5 ≤ Real.exp (L / 2) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (2 : ℝ) * L ^ 5),
      abs_of_pos (Real.exp_pos _), one_mul, one_div_mul_eq_div] using hb
  have hr : 2 ≤ Real.exp (L / 2) / L ^ 5 := (le_div_iff₀ (pow_pos hLp 5)).mpr hpoly
  have hQ := (tailCollisionCutoff_bounds L hL1 hr).2.1
  have hQ' : (tailCollisionCutoff L : ℝ) ≤ Real.exp (L / 2) := hQ.trans
    (div_le_self (Real.exp_nonneg _) (one_le_pow₀ hL1))
  have he : (1 : ℝ) ≤ Real.exp (L / 2) := Real.one_le_exp (by positivity)
  have hN : (N : ℝ) + 3 ≤ Real.exp (2 * L / 5) := by
    have := Real.add_one_le_exp (2 * L / 5)
    linarith
  have hmul := mul_le_mul_of_nonneg_left hN (Real.exp_nonneg (L / 2))
  have hexp : Real.exp (L / 2) * Real.exp (2 * L / 5) = Real.exp (9 * L / 10) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [hexp] at hmul
  have hN0 : 0 ≤ (N : ℝ) + 2 := by positivity
  have hprod := mul_nonneg (sub_nonneg.mpr he) hN0
  have hfloor := Nat.sub_one_lt_floor (Real.exp (9 * L / 10))
  change Real.exp (9 * L / 10) - 1 < (summandTailCutoff L : ℝ) at hfloor
  have hfinal : (N : ℝ) + tailCollisionCutoff L ≤ (summandTailCutoff L : ℝ) := by
    nlinarith only [hmul, hprod, hfloor, hQ']
  exact ⟨hL1, hr, by exact_mod_cast hfinal⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_RootCollisions
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Collisions of uniform root populations

The root populations at the end of §3 occupy translated intervals. Their
collision upper bound depends on the diameter and their cardinality.
-/

namespace Ostmann

open scoped BigOperators

theorem sum_uniform_mass (s : Finset ℕ) (hs : s.Nonempty) :
    (∑ _a ∈ s, (1 / (s.card : ℝ))) = 1 := by
  have hc : (s.card : ℝ) ≠ 0 := by exact_mod_cast hs.card_ne_zero
  simp only [Finset.sum_const, nsmul_eq_mul]
  exact mul_one_div_cancel hc

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_UniformTailStability
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A logarithmic collision defect bound for the actual uniform tails -/

namespace Ostmann

open scoped BigOperators Classical

private theorem uniform_atom_bound (s : Finset ℕ) (a L : ℝ) (ha : 0 < a) (hL : 0 < L)
    (hsize : a * Real.exp (L / 2) / L ^ 3 ≤ (s.card : ℝ)) :
    s.Nonempty ∧ 1 / (s.card : ℝ) ≤ L ^ 3 / (a * Real.exp (L / 2)) := by
  have hp : 0 < a * Real.exp (L / 2) / L ^ 3 := by positivity
  have hc : (0 : ℝ) < s.card := hp.trans_le hsize
  refine ⟨Finset.card_pos.mp (by exact_mod_cast hc), ?_⟩
  calc
    1 / (s.card : ℝ) ≤ 1 / (a * Real.exp (L / 2) / L ^ 3) := one_div_le_one_div_of_le hp hsize
    _ = _ := by field_simp

theorem uniform_tail_collision_bound {A B : Set ℕ} (hA : A.Infinite) (hB : B.Infinite)
    (N lo hi : ℕ) (a L C : ℝ) (ha : 0 < a) (hL : 1 ≤ L)
    (hr : 2 ≤ Real.exp (L / 2) / L ^ 5) (hhi : (hi : ℝ) = Real.exp L)
    (hlo : N + tailCollisionCutoff L ≤ lo)
    (hdis : ∀ p ∈ Nat.primesLE (tailCollisionCutoff L),
      Disjoint (tailResidues A N p) (negTailResidues B N p))
    (hsizeA : a * Real.exp (L / 2) / L ^ 3 ≤ (summandTail A lo hi).card)
    (hsizeB : a * Real.exp (L / 2) / L ^ 3 ≤ (summandTail B lo hi).card)
    (hM : MertensLowerBound C) :
    (∑ p ∈ Nat.primesLE (tailCollisionCutoff L), Real.log (p : ℝ) *
      tailCollisionDefect A N p (summandTail A lo hi) (summandTail B lo hi)
        (fun _ => 1 / ((summandTail A lo hi).card : ℝ))
        (fun _ => 1 / ((summandTail B lo hi).card : ℝ))) ≤
      20 * Real.log L + 4 * C + 4 * Real.log 2 + 2 * Real.log 4 / a := by
  let Q := tailCollisionCutoff L
  let P := Nat.primesLE Q
  let s := summandTail A lo hi
  let t := summandTail B lo hi
  let m := L ^ 3 / (a * Real.exp (L / 2))
  have hLp : 0 < L := by linarith
  have hs := uniform_atom_bound s a L ha hLp hsizeA
  have ht := uniform_atom_bound t a L ha hLp hsizeB
  have hQ := tailCollisionCutoff_bounds L hL hr
  have hp (p : ℕ) (hp : p ∈ P) : p.Prime := Nat.prime_of_mem_primesLE hp
  have hps (p : ℕ) (hp : p ∈ P) : p ≤ Q := Nat.le_of_mem_primesLE hp
  have hmapA (p : ℕ) (hpP : p ∈ P) (x : ℕ) (hx : x ∈ s) : x % p ∈ tailSupport A N p := by
    obtain ⟨hxA, hxlo, _⟩ := (mem_summandTail A lo hi x).mp hx
    apply mod_mem_tailSupport (hp p hpP).pos hxA
    have := hps p hpP
    omega
  have hmapB (p : ℕ) (hpP : p ∈ P) (x : ℕ) (hx : x ∈ t) :
      negativeResidue p x ∈ Finset.range p \ tailSupport A N p := by
    obtain ⟨hxB, hxlo, _⟩ := (mem_summandTail B lo hi x).mp hx
    apply negativeResidue_mem_complement (hp p hpP).pos (hdis p hpP) hxB
    have := hps p hpP
    omega
  have hX : 1 ≤ hi := by
    have he := Real.one_le_exp hLp.le
    rw [← hhi] at he
    exact_mod_cast he
  have hraw := finite_measure_collision_stability P s t
    (fun _ => 1 / (s.card : ℝ)) (fun _ => 1 / (t.card : ℝ))
    (tailSupport A N) (fun p => Finset.range p \ tailSupport A N p)
    (fun p x => x % p) negativeResidue hi Q m (Real.log 4) C hX hp
    (fun x hx => ((mem_summandTail A lo hi x).mp hx).2.2)
    (fun x hx => ((mem_summandTail B lo hi x).mp hx).2.2)
    (fun _ _ => by positivity) (fun _ _ => by positivity)
    (sum_uniform_mass s hs.1) (sum_uniform_mass t ht.1)
    (fun _ _ => hs.2) (fun _ _ => ht.2)
    (fun p hpP => tailSupport_nonempty hA N p (hp p hpP).pos)
    (fun p hpP => tailSupport_complement_nonempty hB (hp p hpP).pos (hdis p hpP))
    hmapA hmapB (fun _ _ _ _ _ _ => Iff.rfl)
    (fun p hpP _ _ _ _ => negativeResidue_eq_iff (hp p hpP).pos)
    (by positivity) (prime_log_weight_le Q) (hM Q hQ.1)
  change (∑ p ∈ P, Real.log (p : ℝ) * tailCollisionDefect A N p s t
    (fun _ => 1 / (s.card : ℝ)) (fun _ => 1 / (t.card : ℝ))) ≤ _ at hraw
  rw [hhi, Real.log_exp] at hraw
  have hmQ : m * Q ≤ 1 / a := by
    calc
      m * Q ≤ m * (Real.exp (L / 2) / L ^ 5) :=
        mul_le_mul_of_nonneg_left hQ.2.1 (by positivity)
      _ = 1 / (a * L ^ 2) := by dsimp [m]; field_simp
      _ ≤ 1 / a := one_div_le_one_div_of_le ha
        (le_mul_of_one_le_right ha.le (one_le_pow₀ hL))
  have herr := mul_le_mul_of_nonneg_left hmQ (show 0 ≤ 2 * Real.log 4 by positivity)
  dsimp only [Q] at herr
  have herr' : 2 * m * Real.log 4 * (tailCollisionCutoff L : ℝ) ≤ 2 * Real.log 4 / a := by
    first | (convert herr using 1 <;> ring) | exact (le_of_eq (by ring)).trans (herr.trans (le_of_eq (by ring)))
  have hlogQ := hQ.2.2
  dsimp only [P, Q, s, t] at hraw
  linarith only [hraw, herr', hlogQ]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_TailDensityMask
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual residue masks for the positive endpoint tail -/

namespace Ostmann

open scoped Classical

theorem tailDensityMask_card (A : Set ℕ) (N p : ℕ) :
    (tailDensityMask A N p).card = (tailSupport A N p).card := by
  apply Finset.card_image_of_injOn
  intro r hr s hs he
  have hrp := Finset.mem_range.mp (tailSupport_subset A N p hr)
  have hsp := Finset.mem_range.mp (tailSupport_subset A N p hs)
  have hmod := (ZMod.natCast_eq_natCast_iff' r s p).mp he
  simpa only [Nat.mod_eq_of_lt hrp, Nat.mod_eq_of_lt hsp] using hmod

theorem positiveSummandTail_mem_mask (A : Set ℕ) (N lo hi p : ℕ) (hp : 0 < p)
    (hlo : N + p ≤ lo) {x : ℤ} (hx : x ∈ positiveSummandTail A lo hi) :
    (x : ZMod p) ∈ tailDensityMask A N p := by
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨haA, halo, _⟩ := (mem_summandTail A lo hi a).mp ha
  apply Finset.mem_image.mpr
  refine ⟨a % p, mod_mem_tailSupport hp haA (lt_of_le_of_lt hlo halo), ?_⟩
  simp

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_TailBudgetNegligible
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The discarded collision weight is negligible in both prime bands -/

namespace Ostmann

open Filter

theorem eventual_affine_log_le_rpow (A B d κ : ℝ) (hA : 0 ≤ A) (hd : 0 < d) (hκ : 0 < κ) :
    ∀ᶠ T : ℝ in atTop, A * Real.log T + B ≤ d * T ^ κ := by
  have hl := ((isLittleO_log_rpow_atTop hκ).const_mul_left A).bound (show 0 < d / 2 by positivity)
  have hp := (tendsto_rpow_atTop hκ).eventually_ge_atTop (2 * max B 0 / d)
  filter_upwards [hl, hp, eventually_ge_atTop (1 : ℝ)] with T hl hp hT
  have hlog : A * Real.log T ≤ d / 2 * T ^ κ := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hA (Real.log_nonneg hT)),
      abs_of_nonneg (Real.rpow_nonneg (by linarith : 0 ≤ T) κ)] using hl
  have hb : B ≤ d / 2 * T ^ κ := by
    have hh := (div_le_iff₀ hd).mp hp
    linarith [le_max_left B 0]
  linarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_PrimeReciprocalLogBudget
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A uniform reciprocal-log prime budget from the recorded Mertens input -/

namespace Ostmann
open scoped Classical BigOperators

theorem primeReciprocalLogBand_le {C : ℝ} (hM : MertensEstimate C)
    (T : ℝ) (hT : 1 ≤ T) :
    (∑ p ∈ logPrimeBand T, 1 / ((p : ℝ) * Real.log p)) ≤
      (1 + Real.log 2 + 2 * max C 0) / T := by
  have hT0 : 0 < T := by linarith
  have hpoint (p) (hp : p ∈ logPrimeBand T) :
      1 / ((p : ℝ) * Real.log p) ≤ (Real.log p / p) / T ^ 2 := by
    obtain ⟨hprime, hlo, _⟩ := logPrimeBand_mem hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hprime.pos
    have hl0 : 0 < Real.log (p : ℝ) := hT0.trans hlo
    calc
      _ = (Real.log p / p) / (Real.log p) ^ 2 := by field_simp
      _ ≤ _ := div_le_div_of_nonneg_left (div_nonneg hl0.le hp0.le)
        (sq_pos_of_pos hT0) ((sq_le_sq₀ hT0.le hl0.le).mpr hlo.le)
  have hweight := (logPrimeBand_weight_bounds T C hT hM).2
  have hD : 0 ≤ Real.log 2 + 2 * max C 0 := by
    positivity
  calc
    _ ≤ ∑ p ∈ logPrimeBand T, (Real.log p / p) / T ^ 2 :=
      Finset.sum_le_sum hpoint
    _ = (∑ p ∈ logPrimeBand T, Real.log p / p) / T ^ 2 := (Finset.sum_div ..).symm
    _ ≤ (T + Real.log 2 + 2 * max C 0) / T ^ 2 := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      linarith [le_max_left C 0]
    _ ≤ _ := by
      apply (div_le_div_iff₀ (sq_pos_of_pos hT0) hT0).mpr
      have hh := mul_le_mul_of_nonneg_left hT hD
      nlinarith

theorem primeReciprocalLogSum_mono : Monotone primeReciprocalLogSum := by
  intro Q R hQR
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    exact Nat.mem_primesLE.mpr ⟨(Nat.le_of_mem_primesLE hp).trans hQR,
      Nat.prime_of_mem_primesLE hp⟩
  · intro p _ _
    exact one_div_nonneg.mpr (mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _))

theorem primeReciprocalLogSum_power_budget {C : ℝ} (hM : MertensEstimate C) (N : ℕ) :
    primeReciprocalLogSum ⌊Real.exp ((2 : ℝ) ^ N)⌋₊ ≤
      primeReciprocalLogSum ⌊Real.exp 1⌋₊ +
        (1 + Real.log 2 + 2 * max C 0) * ∑ j ∈ Finset.range N, (1 / 2 : ℝ) ^ j := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hT : (1 : ℝ) ≤ 2 ^ N := one_le_pow₀ (by norm_num)
    have hnest : Nat.primesLE ⌊Real.exp ((2 : ℝ) ^ N)⌋₊ ⊆
        Nat.primesLE ⌊Real.exp (2 * (2 : ℝ) ^ N)⌋₊ := by
      intro p hp
      refine Nat.mem_primesLE.mpr ⟨(Nat.le_of_mem_primesLE hp).trans ?_, Nat.prime_of_mem_primesLE hp⟩
      apply Nat.floor_mono
      apply Real.exp_le_exp.mpr
      nlinarith [pow_nonneg (show (0 : ℝ) ≤ 2 by norm_num) N]
    have hb := primeReciprocalLogBand_le hM ((2 : ℝ) ^ N) hT
    rw [logPrimeBand, Finset.sum_sdiff_eq_sub hnest] at hb
    change primeReciprocalLogSum ⌊Real.exp (2 * (2 : ℝ) ^ N)⌋₊ -
      primeReciprocalLogSum ⌊Real.exp ((2 : ℝ) ^ N)⌋₊ ≤ _ at hb
    have he : (1 + Real.log 2 + 2 * max C 0) / (2 : ℝ) ^ N =
        (1 + Real.log 2 + 2 * max C 0) * (1 / 2 : ℝ) ^ N := by
      rw [one_div_pow, div_eq_mul_inv, one_div]
    rw [he] at hb
    rw [Finset.sum_range_succ, pow_succ]
    rw [mul_comm ((2 : ℝ) ^ N) 2]
    nlinarith

theorem primeReciprocalLogSum_uniform {C : ℝ} (hM : MertensEstimate C) (Q : ℕ) :
    primeReciprocalLogSum Q ≤ primeReciprocalLogConstant C := by
  have hQ : Q ≤ ⌊Real.exp ((2 : ℝ) ^ Q)⌋₊ := by
    apply Nat.le_floor
    have hn : Q ≤ 2 ^ Q := (Nat.lt_two_pow_self (n := Q)).le
    have hr : (Q : ℝ) ≤ (2 : ℝ) ^ Q := by exact_mod_cast hn
    linarith [Real.add_one_le_exp ((2 : ℝ) ^ Q)]
  have hgeom : (∑ j ∈ Finset.range Q, (1 / 2 : ℝ) ^ j) ≤ 2 := by
    have hh := geom_sum_mul_neg (1 / 2 : ℝ) Q
    nlinarith [pow_nonneg (show (0 : ℝ) ≤ 1 / 2 by norm_num) Q]
  have hA : 0 ≤ 1 + Real.log 2 + 2 * max C 0 := by positivity
  exact (primeReciprocalLogSum_mono hQ).trans
    ((primeReciprocalLogSum_power_budget hM Q).trans (by
      unfold primeReciprocalLogConstant
      nlinarith))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Supply_LogImbalanceVariance
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Logarithmic imbalance from the collision variance -/

namespace Ostmann
open scoped BigOperators

private theorem log_sq_le_four_variance_of_one_le (t : ℝ) (ht : 1 ≤ t) :
    (Real.log t) ^ 2 ≤ 4 * (t + t⁻¹ - 2) := by
  have ht0 : 0 < t := by linarith
  let s := Real.sqrt t
  have hs : 1 ≤ s := Real.one_le_sqrt.mpr ht
  have hs0 : 0 < s := by linarith
  have hs2 : s ^ 2 = t := Real.sq_sqrt ht0.le
  have hlog0 : 0 ≤ Real.log t := Real.log_nonneg ht
  have hlog : Real.log t ≤ 2 * (s - 1) := by
    have hh := Real.log_le_sub_one_of_pos hs0
    have he := Real.log_sqrt ht0.le
    change Real.log s = Real.log t / 2 at he
    linarith
  have hsq : (Real.log t) ^ 2 ≤ 4 * (s - 1) ^ 2 := by nlinarith
  have hid : t * (t + t⁻¹ - 2 - (s - 1) ^ 2) = (s - 1) ^ 2 * (2 * s + 1) := by
    calc
      _ = s ^ 2 * (s ^ 2 + (s ^ 2)⁻¹ - 2 - (s - 1) ^ 2) := by rw [hs2]
      _ = _ := by field_simp; ring
  have hvar : (s - 1) ^ 2 ≤ t + t⁻¹ - 2 := by
    have hp : 0 ≤ t * (t + t⁻¹ - 2 - (s - 1) ^ 2) := by
      rw [hid]
      exact mul_nonneg (sq_nonneg _) (by linarith)
    have hd := nonneg_of_mul_nonneg_right hp ht0
    linarith
  linarith

theorem log_sq_le_four_variance (t : ℝ) (ht : 0 < t) :
    (Real.log t) ^ 2 ≤ 4 * (t + t⁻¹ - 2) := by
  by_cases h : 1 ≤ t
  · exact log_sq_le_four_variance_of_one_le t h
  · have hinv : 1 ≤ t⁻¹ := by
      simpa only [one_div, inv_one] using
        div_le_div_of_nonneg_left (show (0 : ℝ) ≤ 1 by norm_num) ht (le_of_not_ge h)
    have hh := log_sq_le_four_variance_of_one_le t⁻¹ hinv
    simpa only [Real.log_inv, neg_sq, inv_inv, add_comm] using hh

/-- A finite Cauchy--Schwarz form ready for the actual prime collision budget.
A harmless absolute factor four avoids any additional analytic theorem. -/
theorem logarithmic_imbalance_budget (P : Finset ℕ) (κ : ℕ → ℝ)
    (hP : ∀ p ∈ P, 1 < p) (hκ : ∀ p ∈ P, 0 < κ p) :
    (∑ p ∈ P, |Real.log (κ p)| / p) ^ 2 ≤
      (4 * ∑ p ∈ P, (κ p + (κ p)⁻¹ - 2) * Real.log p / p) *
        ∑ p ∈ P, 1 / ((p : ℝ) * Real.log p) := by
  rw [Finset.mul_sum P (fun p => (κ p + (κ p)⁻¹ - 2) * Real.log p / p) 4]
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul P
  · intro p hp
    have hv : 0 ≤ κ p + (κ p)⁻¹ - 2 := by
      nlinarith [log_sq_le_four_variance (κ p) (hκ p hp), sq_nonneg (Real.log (κ p))]
    have hlog : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hP p hp)
    positivity
  · intro p hp
    have hlog : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hP p hp)
    positivity
  · intro p hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (lt_trans Nat.zero_lt_one (hP p hp))
    have hlog : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hP p hp)
    have hh := log_sq_le_four_variance (κ p) (hκ p hp)
    rw [div_pow, sq_abs]
    apply (div_le_iff₀ (sq_pos_of_pos hp0)).mpr
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    field_simp

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Supply_CollisionLogImbalance
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual complementary-support imbalance is controlled by collisions -/

namespace Ostmann
open scoped Classical BigOperators

theorem supportRatio_variance_le_defect (p : ℕ) (S T : Finset ℕ)
    (μ ν : ℕ → ℝ) (hS : S.Nonempty) (hT : T.Nonempty)
    (hcard : S.card + T.card = p) :
    ((T.card : ℝ) / S.card) + ((T.card : ℝ) / S.card)⁻¹ - 2 ≤
      (p : ℝ) * collisionDefect p S T μ ν := by
  have hSc : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  have hTc : (0 : ℝ) < T.card := by exact_mod_cast hT.card_pos
  have hcr : (S.card : ℝ) + T.card = p := by exact_mod_cast hcard
  have hp : (0 : ℝ) < p := by linarith
  have he : ((T.card : ℝ) / S.card) + ((T.card : ℝ) / S.card)⁻¹ - 2 =
      (p : ℝ) * (1 / (S.card : ℝ) + 1 / (T.card : ℝ) - 4 / (p : ℝ)) := by
    rw [inv_div]
    field_simp
    nlinarith
  rw [he]
  apply mul_le_mul_of_nonneg_left _ hp.le
  unfold collisionDefect
  have h1 : 0 ≤ ∑ r ∈ S, (μ r - 1 / (S.card : ℝ)) ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have h2 : 0 ≤ ∑ r ∈ T, (ν r - 1 / (T.card : ℝ)) ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  linarith

theorem collision_logarithmic_imbalance {C : ℝ} (hM : MertensEstimate C)
    (Q : ℕ) (P : Finset ℕ) (hP : P ⊆ Nat.primesLE Q)
    (S T : ℕ → Finset ℕ) (μ ν : ℕ → ℕ → ℝ)
    (hS : ∀ p ∈ P, (S p).Nonempty) (hT : ∀ p ∈ P, (T p).Nonempty)
    (hcard : ∀ p ∈ P, (S p).card + (T p).card = p)
    (D : ℝ) (hD : (∑ p ∈ P, Real.log (p : ℝ) *
      collisionDefect p (S p) (T p) (μ p) (ν p)) ≤ D) :
    (∑ p ∈ P, |Real.log ((T p).card / ((S p).card : ℝ))| / p) ^ 2 ≤
      4 * D * primeReciprocalLogConstant C := by
  let κ := fun p => ((T p).card : ℝ) / (S p).card
  have hprime (p) (hp : p ∈ P) := Nat.prime_of_mem_primesLE (hP hp)
  have hκ (p) (hp : p ∈ P) : 0 < κ p := by
    exact div_pos (by exact_mod_cast (hT p hp).card_pos)
      (by exact_mod_cast (hS p hp).card_pos)
  let V := ∑ p ∈ P, (κ p + (κ p)⁻¹ - 2) * Real.log p / p
  let J := ∑ p ∈ P, 1 / ((p : ℝ) * Real.log p)
  have hV0 : 0 ≤ V := by
    apply Finset.sum_nonneg
    intro p hp
    have hv : 0 ≤ κ p + (κ p)⁻¹ - 2 := by
      nlinarith [log_sq_le_four_variance (κ p) (hκ p hp), sq_nonneg (Real.log (κ p))]
    positivity
  have hV : V ≤ D := by
    apply le_trans _ hD
    apply Finset.sum_le_sum
    intro p hp
    have hpp : (0 : ℝ) < p := by exact_mod_cast (hprime p hp).pos
    have hl : 0 ≤ Real.log (p : ℝ) := Real.log_natCast_nonneg p
    have hh := supportRatio_variance_le_defect p (S p) (T p) (μ p) (ν p)
      (hS p hp) (hT p hp) (hcard p hp)
    have hm := mul_le_mul_of_nonneg_right hh (div_nonneg hl hpp.le)
    dsimp [κ]
    convert hm using 1 <;> first | (with_reducible_and_instances rfl) | (field_simp)
  have hJ0 : 0 ≤ J := by
    apply Finset.sum_nonneg
    intro p _
    exact one_div_nonneg.mpr (mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _))
  have hJ : J ≤ primeReciprocalLogConstant C := by
    apply le_trans _ (primeReciprocalLogSum_uniform hM Q)
    exact Finset.sum_le_sum_of_subset_of_nonneg hP (fun p _ _ =>
      one_div_nonneg.mpr (mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _)))
  have hh := logarithmic_imbalance_budget P κ (fun p hp => (hprime p hp).one_lt) hκ
  apply hh.trans
  exact mul_le_mul (mul_le_mul_of_nonneg_left hV (by norm_num)) hJ hJ0
    (mul_nonneg (by norm_num) (hV0.trans hV))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Supply_SieveBudgetParameters
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Numerical specialization of the subset-sieve budgets -/

namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem rpow_three_quarters_sq {L : ℝ} (hL : 0 < L) :
    (L ^ (3 / 4 : ℝ)) ^ 2 = L * Real.sqrt L := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hL.le]
  norm_num only [Nat.cast_ofNat, mul_div_cancel_right₀]
  rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
    Real.rpow_add hL, Real.rpow_one, ← Real.sqrt_eq_rpow]

theorem eventual_square_budget_le_three_quarters (K : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ W : ℝ, W ^ 2 ≤ K * L →
      W ≤ L ^ (3 / 4 : ℝ) / 16 := by
  have hlarge := (tendsto_rpow_atTop (show (0 : ℝ) < 1 / 2 by norm_num)).eventually_ge_atTop
    (256 * max K 0)
  filter_upwards [hlarge, eventually_ge_atTop (1 : ℝ)] with L hlarge hL W hW
  have hLp : 0 < L := by linarith
  rw [← Real.sqrt_eq_rpow] at hlarge
  have hs : K * L ≤ (L ^ (3 / 4 : ℝ) / 16) ^ 2 := by
    rw [div_pow, rpow_three_quarters_sq hLp]
    norm_num only [show (16 : ℝ) ^ 2 = 256 by norm_num]
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 256)).mpr
    nlinarith [mul_le_mul_of_nonneg_right hlarge hLp.le, le_max_left K 0]
  exact le_of_sq_le_sq (hW.trans hs) (by positivity)

theorem finite_prime_reciprocal_mass_le (P : Finset ℕ) (L a : ℝ)
    (hP : ∀ p ∈ P, 0 < p ∧ a * L ≤ Real.log (p : ℝ)) :
    (∑ p ∈ P, (p : ℝ)⁻¹) ≤ (P.card : ℝ) * Real.exp (-a * L) := by
  calc
    _ ≤ ∑ _p ∈ P, Real.exp (-a * L) := by
      apply Finset.sum_le_sum
      intro p hp
      have hp0 : (0 : ℝ) < p := by exact_mod_cast (hP p hp).1
      have he : (p : ℝ)⁻¹ = Real.exp (-Real.log (p : ℝ)) := by
        rw [Real.exp_neg, Real.exp_log hp0]
      rw [he]
      apply Real.exp_le_exp.mpr
      linarith [(hP p hp).2]
    _ = _ := by simp

theorem eventual_small_subset_reciprocal (a c : ℝ) (ha : 0 < a) (hc : 0 ≤ c) :
    ∀ᶠ L : ℝ in atTop, ∀ P : Finset ℕ,
      (P.card : ℝ) ≤ c * L →
      (∀ p ∈ P, 0 < p ∧ a * L ≤ Real.log (p : ℝ)) →
      (∑ p ∈ P, (p : ℝ)⁻¹) ≤ 1 / 16 := by
  have hsmall := ((isLittleO_pow_exp_pos_mul_atTop 1 ha).const_mul_left c).bound
    (show (0 : ℝ) < 1 / 16 by norm_num)
  filter_upwards [hsmall, eventually_ge_atTop (1 : ℝ)] with L hsmall hL P hcard hP
  have hLp : 0 < L := by linarith
  have hbound : c * L ≤ (1 / 16 : ℝ) * Real.exp (a * L) := by
    simpa only [pow_one, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hc hLp.le),
      abs_of_pos (Real.exp_pos _)] using hsmall
  calc
    _ ≤ (P.card : ℝ) * Real.exp (-a * L) := finite_prime_reciprocal_mass_le P L a hP
    _ ≤ (c * L) * Real.exp (-a * L) :=
      mul_le_mul_of_nonneg_right hcard (Real.exp_pos _).le
    _ ≤ ((1 / 16 : ℝ) * Real.exp (a * L)) * Real.exp (-a * L) :=
      mul_le_mul_of_nonneg_right hbound (Real.exp_pos _).le
    _ = 1 / 16 := by
      rw [mul_assoc, ← Real.exp_add]
      simp

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_SparseBandMass
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The large sparse set forced by failure of favorable-prime mass -/

namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem logLog_sparse_mass_lower {C : ℝ} (hM : MertensHarmonicEstimate C)
    (L : ℝ) (hL : 40 ≤ L) (S T : ℕ → Finset ℕ)
    (μ ν : ℕ → ℕ → ℝ) (γ : ℕ → ℝ) (δ D : ℝ)
    (hS : ∀ p ∈ logLogPrimeBand L, (S p).Nonempty)
    (hT : ∀ p ∈ logLogPrimeBand L, (T p).Nonempty)
    (hcard : ∀ p ∈ logLogPrimeBand L, (S p).card + (T p).card = p)
    (hbudget : (∑ p ∈ logLogPrimeBand L, Real.log (p : ℝ) *
      collisionDefect p (S p) (T p) (μ p) (ν p)) ≤ D)
    (hfail : (∑ p ∈ favorableTransformPrimes (logLogPrimeBand L) S γ δ, (p : ℝ)⁻¹) ≤
      (3 / 20 : ℝ) * L) :
    (7 / 10 : ℝ) * L - Real.log 2 - 2 * C - 4 * D / Real.exp ((1 / 20 : ℝ) * L) ≤
      ∑ p ∈ sparseTransformPrimes (logLogPrimeBand L) S γ δ, (p : ℝ)⁻¹ := by
  have hh := sparse_transform_mass_lower (logLogPrimeBand L) S T μ ν γ δ
    (Real.exp ((1 / 20 : ℝ) * L)) D (Real.exp_pos _)
    (fun p hp => (logLogPrimeBand_mem hp).1)
    (fun p hp => (logLogPrimeBand_mem hp).2.1.le) hS hT hcard hbudget
  have hm := logLogPrimeBand_harmonic_lower hM L hL
  linarith

theorem eventual_sparse_mass_error (C d e : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ D : ℝ, D ≤ d * L + e →
      (69 / 100 : ℝ) * L ≤
        (7 / 10 : ℝ) * L - Real.log 2 - 2 * C - 4 * D / Real.exp ((1 / 20 : ℝ) * L) := by
  have hlin := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 (1 / 20 : ℝ) (by norm_num)
  have hcon := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 (1 / 20 : ℝ) (by norm_num)
  simp only [Real.rpow_one] at hlin
  simp only [Real.rpow_zero, one_mul] at hcon
  have hz : Tendsto (fun L : ℝ => 4 * (d * L + e) / Real.exp ((1 / 20 : ℝ) * L))
      atTop (nhds 0) := by
    have hh := (hlin.const_mul (4 * d)).add (hcon.const_mul (4 * e))
    simp only [mul_zero, add_zero] at hh
    apply hh.congr
    intro L
    simp only [div_eq_mul_inv, neg_mul, Real.exp_neg]
    ring
  filter_upwards [hz.eventually_lt_const (show (0 : ℝ) < 1 by norm_num),
    eventually_ge_atTop (100 * (Real.log 2 + 2 * C + 1))] with L herr hL D hD
  have hd : 4 * D / Real.exp ((1 / 20 : ℝ) * L) ≤ 1 := by
    apply le_trans _ herr.le
    exact div_le_div_of_nonneg_right (by linarith) (Real.exp_pos _).le
  linarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_SparseCoverageContradiction
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The numerical contradiction between coverage and contraction -/
namespace Ostmann

 theorem coverage_energy_size_bound (S c U X α T r D m : ℝ)
    (_hS : 0 ≤ S) (hc : 0 ≤ c) (hU : 0 ≤ U) (hX : 0 ≤ X) (_hα : 0 ≤ α)
    (hT : 0 ≤ T) (hr : 0 ≤ r) (_hD : 0 ≤ D)
    (hcover : c * U * X ≤ T * S)
    (henergy : α ^ 2 * S ^ 2 ≤ r ^ 2 * D ^ 2 * m)
    (hsize : α ^ 2 * m ≤ D ^ 2) :
    c * U * X * α ^ 2 ≤ T * r * D ^ 2 := by
  apply (sq_le_sq₀ (by positivity) (by positivity)).mp
  calc
    (c * U * X * α ^ 2) ^ 2 ≤ (T * S * α ^ 2) ^ 2 :=
      pow_le_pow_left₀ (by positivity)
        (mul_le_mul_of_nonneg_right hcover (sq_nonneg _)) 2
    _ = T ^ 2 * α ^ 2 * (α ^ 2 * S ^ 2) := by ring
    _ ≤ T ^ 2 * α ^ 2 * (r ^ 2 * D ^ 2 * m) :=
      mul_le_mul_of_nonneg_left henergy (by positivity)
    _ = T ^ 2 * r ^ 2 * D ^ 2 * (α ^ 2 * m) := by ring
    _ ≤ T ^ 2 * r ^ 2 * D ^ 2 * D ^ 2 :=
      mul_le_mul_of_nonneg_left hsize (by positivity)
    _ = (T * r * D ^ 2) ^ 2 := by ring

open Filter

theorem eventual_sparse_coverage_margin (c : ℝ) (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop,
      18432 * Real.exp (L - (8 / 5 : ℝ) * ((17 / 25 : ℝ) * L) +
        2 * L ^ (3 / 4 : ℝ)) < c := by
  have hs := (tendsto_rpow_neg_atTop (show (0 : ℝ) < 1 / 4 by norm_num)).eventually_le_const
    (show (0 : ℝ) < 11 / 500 by norm_num)
  have he := (Real.tendsto_exp_neg_atTop_nhds_zero.comp
    (tendsto_id.const_mul_atTop (show (0 : ℝ) < 11 / 250 by norm_num))).eventually_lt_const
      (show 0 < c / 18432 by positivity)
  filter_upwards [hs, he, eventually_ge_atTop (1 : ℝ)] with L hsmall hexp hL
  have hLp : 0 < L := by linarith
  have hpow : L ^ (3 / 4 : ℝ) = L * L ^ (-(1 / 4 : ℝ)) := by
    nth_rw 2 [← Real.rpow_one L]
    rw [← Real.rpow_add hLp]
    norm_num
  have hm := mul_le_mul_of_nonneg_left hsmall hLp.le
  have hbound : L - (8 / 5 : ℝ) * ((17 / 25 : ℝ) * L) + 2 * L ^ (3 / 4 : ℝ) ≤
      -(11 / 250 : ℝ) * L := by
    rw [hpow]
    linarith
  calc
    _ ≤ 18432 * Real.exp (-(11 / 250 : ℝ) * L) := by
      gcongr
    _ < c := by
      have hh := mul_lt_mul_of_pos_left hexp (show (0 : ℝ) < 18432 by norm_num)
      simpa only [Function.comp_apply, id_eq, neg_mul, mul_div_cancel₀ _ (by norm_num : (18432 : ℝ) ≠ 0)] using hh

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_SparseNumericalContradiction
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The sharp numerical specialization of the sparse contradiction -/
namespace Ostmann

 theorem sparse_sieve_numerical_bound (c U X Q D H L R : ℝ)
    (hc : 0 ≤ c) (hU : 0 < U) (hX : 0 < X) (hD : 0 ≤ D)
    (hQ : X / 4 ≤ Q ^ 2) (hDX : D ≤ 3 * X)
    (hb : c * U * X * (Q / 16 * Real.exp (-R)) ^ 2 ≤
      Real.exp L * (2 * U * Real.exp (-(8 / 5) * H)) * D ^ 2) :
    c ≤ 18432 * Real.exp (L - (8 / 5) * H + 2 * R) := by
  have hα : X / 1024 * Real.exp (-(2 * R)) ≤ (Q / 16 * Real.exp (-R)) ^ 2 := by
    have he : Real.exp (-(2 * R)) = Real.exp (-R) ^ 2 := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    rw [he]
    have hh := mul_le_mul_of_nonneg_right hQ (sq_nonneg (Real.exp (-R)))
    nlinarith only [hh]
  have hD2 : D ^ 2 ≤ 9 * X ^ 2 := by nlinarith only [hD, hDX, hX]
  have hleft := (mul_le_mul_of_nonneg_left hα (mul_nonneg (mul_nonneg hc hU.le) hX.le)).trans hb
  have hright := mul_le_mul_of_nonneg_left hD2
    (show 0 ≤ Real.exp L * (2 * U * Real.exp (-(8 / 5) * H)) by positivity)
  have hh := hleft.trans hright
  have heq : Real.exp (L - (8 / 5) * H + 2 * R) * Real.exp (-(2 * R)) =
      Real.exp L * Real.exp (-(8 / 5) * H) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  apply (mul_le_mul_iff_left₀ (show 0 < U * X ^ 2 * Real.exp (-(2 * R)) by positivity)).mp
  calc
    _ = 1024 * (c * U * X * (X / 1024 * Real.exp (-(2 * R)))) := by ring
    _ ≤ 1024 * (Real.exp L * (2 * U * Real.exp (-(8 / 5) * H)) * (9 * X ^ 2)) := by
      exact mul_le_mul_of_nonneg_left hh (by norm_num)
    _ = 18432 * U * X ^ 2 * (Real.exp L * Real.exp (-(8 / 5) * H)) := by ring
    _ = 18432 * U * X ^ 2 *
        (Real.exp (L - (8 / 5) * H + 2 * R) * Real.exp (-(2 * R))) := by rw [heq]
    _ = _ := by ring

 theorem sparse_sieve_numerical_impossible (c U X Q D H L : ℝ)
    (hc : 0 < c) (hU : 0 < U) (hX : 0 < X) (hD : 0 ≤ D)
    (hQ : X / 4 ≤ Q ^ 2) (hDX : D ≤ 3 * X) (hH : (17 / 25) * L ≤ H)
    (hmargin : 18432 * Real.exp (L - (8 / 5) * ((17 / 25) * L) +
      2 * L ^ (3 / 4 : ℝ)) < c)
    (hb : c * U * X * (Q / 16 * Real.exp (-(L ^ (3 / 4 : ℝ)))) ^ 2 ≤
      Real.exp L * (2 * U * Real.exp (-(8 / 5) * H)) * D ^ 2) : False := by
  have hh := sparse_sieve_numerical_bound c U X Q D H L (L ^ (3 / 4 : ℝ))
    hc.le hU hX hD hQ hDX hb
  have he : Real.exp (L - (8 / 5) * H + 2 * L ^ (3 / 4 : ℝ)) ≤
      Real.exp (L - (8 / 5) * ((17 / 25) * L) + 2 * L ^ (3 / 4 : ℝ)) :=
    Real.exp_le_exp.mpr (by linarith)
  linarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_SparseWeightPairAverage
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The sparse weight average over two actual finite summand sets -/

namespace Ostmann
open scoped Classical BigOperators

theorem sparseWeightPairAverage_nonneg {n : ℕ} (p : Fin n → ℕ) [∀ i, NeZero (p i)]
    (S : ∀ i, Finset (ZMod (p i))) (K : ℕ) {ι κ : Type*}
    (A : Finset ι) (B : Finset κ) (a : ι → ∀ i, ZMod (p i)) (b : κ → ∀ i, ZMod (p i)) :
    0 ≤ sparseWeightPairAverage p S K A B a b := by
  apply mul_nonneg (by positivity)
  exact Finset.sum_nonneg (fun x _ => Finset.sum_nonneg
    (fun y _ => sparseSubsetWeight_nonneg p S K _))

theorem sparseWeightPairAverage_identity {n : ℕ} (p : Fin n → ℕ) [∀ i, Fact (p i).Prime]
    (S : ∀ i, Finset (ZMod (p i))) (K : ℕ) {ι κ : Type*}
    (A : Finset ι) (B : Finset κ) (a : ι → ∀ i, ZMod (p i)) (b : κ → ∀ i, ZMod (p i))
    (ha : ∀ x ∈ A, ∀ i, a x i ∈ S i) (hb : ∀ y ∈ B, ∀ i, b y i ∈ Finset.univ \ S i) :
    kernelPairingLinearMap
      (averagedCoordinates A (fun x => tensorPointCoordinates p S (a x)))
      (averagedCoordinates B (fun y => tensorPointCoordinates p (fun i => Finset.univ \ S i) (b y)))
      (truncatedSparseTensorKernel p S K) =
        (sparseWeightPairAverage p S K A B a b : ℂ) := by
  rw [kernelPairing_averages]
  unfold sparseWeightPairAverage
  push_cast
  congr 1
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  exact sparseSubsetWeight_point_pairing p S K (a x) (b y) (ha x hx) (hb y hy)

theorem sparseWeightPairAverage_le {n : ℕ} (p : Fin n → ℕ) [∀ i, Fact (p i).Prime]
    (S : ∀ i, Finset (ZMod (p i))) (K : ℕ) {ι κ : Type*}
    (A : Finset ι) (B : Finset κ) (a : ι → ∀ i, ZMod (p i)) (b : κ → ∀ i, ZMod (p i))
    (ha : ∀ x ∈ A, ∀ i, a x i ∈ S i) (hb : ∀ y ∈ B, ∀ i, b y i ∈ Finset.univ \ S i) :
    sparseWeightPairAverage p S K A B a b ≤
      ‖finiteKernelOperator (truncatedSparseTensorKernel p S K)‖ *
        countingVectorNorm (lowModeVector (2 * K)
          (averagedCoordinates A (fun x => tensorPointCoordinates p S (a x)))) *
        countingVectorNorm (lowModeVector (2 * K)
          (averagedCoordinates B (fun y => tensorPointCoordinates p (fun i => Finset.univ \ S i) (b y)))) := by
  have he := sparseWeightPairAverage_identity p S K A B a b ha hb
  have hh := truncatedSparseTensorKernel_pairing_le p S K
    (averagedCoordinates A (fun x => tensorPointCoordinates p S (a x)))
    (averagedCoordinates B (fun y => tensorPointCoordinates p (fun i => Finset.univ \ S i) (b y)))
  change ‖kernelPairingLinearMap _ _ _‖ ≤ _ at hh
  rw [he, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (sparseWeightPairAverage_nonneg p S K A B a b)] at hh
  exact hh

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Supply_CenteredCoordinateSupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Decomposing the actual tensor coordinates by their centered support -/

namespace Ostmann
open scoped Classical BigOperators

theorem tensorPointCoordinates_supported {n : ℕ} (p : Fin n → ℕ)
    [∀ i, NeZero (p i)] (S : ∀ i, Finset (ZMod (p i)))
    (T : Finset (Fin n)) (z : ∀ i : T, ZMod (p i)) (a : ∀ i, ZMod (p i)) :
    tensorPointCoordinates p S a (supportedCoordinates p T z) =
      centeredSubsetVector p S T a z := by
  unfold tensorPointCoordinates centeredSubsetVector
  calc
    _ = ∏ i ∈ T, residuePointCoordinates (S i) (a i)
        (supportedCoordinates p T z i) := by
      symm
      apply Finset.prod_subset (Finset.subset_univ T)
      intro i _ hi
      simp [supportedCoordinates, hi, residuePointCoordinates]
    _ = ∏ i : T, residuePointCoordinates (S i) (a i)
        (supportedCoordinates p T z i) := (Finset.prod_coe_sort T _).symm
    _ = _ := by
      apply Finset.prod_congr rfl
      intro i _
      simp [supportedCoordinates, i.property, residuePointCoordinates]

/-- The low-mode norm appearing in the actual truncated-kernel pairing is the
sum of the centered subset energies, without a dimension-dependent loss. -/
theorem lowMode_tensor_energy {n : ℕ} (p : Fin n → ℕ) [∀ i, NeZero (p i)]
    (S : ∀ i, Finset (ZMod (p i))) {ι : Type*} (A : Finset ι)
    (a : ι → ∀ i, ZMod (p i)) (K : ℕ) :
    countingVectorNorm (lowModeVector K
      (averagedCoordinates A (fun x => tensorPointCoordinates p S (a x)))) ^ 2 =
      ∑ T : Finset (Fin n), if T.card ≤ K then centeredSubsetEnergy p S T A a else 0 := by
  rw [countingVectorNorm_sq, ← (centeredSupportEquiv p).symm.sum_comp]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro T _
  change (∑ z : (∀ i : T, ZMod (p i)),
    ‖lowModeVector K (averagedCoordinates A (fun x => tensorPointCoordinates p S (a x)))
      (supportedCoordinates p T z)‖ ^ 2) = _
  simp only [lowModeVector, supportedCoordinates_support]
  by_cases hT : T.card ≤ K
  · simp only [hT, ite_true, if_true]
    rw [centeredSubsetEnergy, countingVectorNorm_sq]
    apply Finset.sum_congr rfl
    intro z _
    simp only [averagedCoordinates, tensorPointCoordinates_supported]
  · simp [hT]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Supply_SubsetReducedEnergy
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact positive subset expansion of the classical reduced energy -/

namespace Ostmann
open scoped Classical BigOperators

theorem unitRamanujanKernel_subset {n : ℕ} (p : Fin n → ℕ)
    [∀ i, Fact (p i).Prime] (R : Finset (Fin n)) [NeZero (∏ i ∈ R, p i)]
    (hc : Pairwise (fun i j => (p i).Coprime (p j))) (z : ℤ) :
    unitRamanujanKernel (∏ i ∈ R, p i) (z : ZMod (∏ i ∈ R, p i)) =
      ∏ i ∈ R, ∑ h ∈ Finset.univ.erase (0 : ZMod (p i)),
        ZMod.stdAddChar (h * (z : ZMod (p i))) := by
  let : NeZero (∏ i : R, p i) := ⟨by
    rw [Finset.prod_coe_sort]
    exact NeZero.ne _⟩
  have hcR : Pairwise (fun i j : R => (p i).Coprime (p j)) := by
    intro i j hij
    exact hc (fun he => hij (Subtype.ext he))
  have hh := unitRamanujanKernel_product (fun i : R => p i) hcR z
  simp_rw [unitRamanujanKernel_prime] at hh
  have hq := Finset.prod_coe_sort R p
  have hr := Finset.prod_coe_sort R (fun i =>
    ∑ h ∈ Finset.univ.erase (0 : ZMod (p i)), ZMod.stdAddChar (h * (z : ZMod (p i))))
  rw [unitRamanujanKernel_int_congr hq z, hr] at hh
  exact hh

theorem subsetSieveCoefficient_nonneg {n : ℕ} (p : Fin n → ℕ)
    [∀ i, NeZero (p i)]
    (S : ∀ i, Finset (ZMod (p i))) (R T : Finset (Fin n))
    (hS : ∀ i ∈ R, (S i).Nonempty) :
    0 ≤ subsetSieveCoefficient p S R T := by
  apply mul_nonneg
  · exact Finset.prod_nonneg (fun i _ => Nat.cast_nonneg _)
  · apply Finset.prod_nonneg
    intro i hi
    have hcard : (0 : ℝ) < (S i).card := by
      exact_mod_cast Finset.card_pos.mpr (hS i (Finset.mem_sdiff.mp hi).1)
    have hle : ((S i).card : ℝ) ≤ p i := by
      exact_mod_cast (Finset.card_le_univ (S i)).trans_eq (ZMod.card (p i))
    exact sub_nonneg.mpr ((le_div_iff₀ hcard).mpr (by simpa using hle))

theorem subset_reduced_energy_expansion {n : ℕ} (p : Fin n → ℕ)
    [∀ i, Fact (p i).Prime] (S : ∀ i, Finset (ZMod (p i)))
    (R : Finset (Fin n)) [NeZero (∏ i ∈ R, p i)]
    (hc : Pairwise (fun i j => (p i).Coprime (p j))) {ι : Type*}
    (A : Finset ι) (a : ι → ℤ)
    (ha : ∀ x ∈ A, ∀ i ∈ R, (a x : ZMod (p i)) ∈ S i) :
    unitFrequencyEnergy A (fun x => (a x : ZMod (∏ i ∈ R, p i))) =
      ∑ T ∈ R.powerset, subsetSieveCoefficient p S R T *
        centeredSubsetEnergy p S T A (fun x i => (a x : ZMod (p i))) := by
  apply Complex.ofReal_injective
  rw [unitFrequencyEnergy_kernel]
  have hk (x y : ι) :
      unitRamanujanKernel (∏ i ∈ R, p i)
          ((a x : ZMod (∏ i ∈ R, p i)) - (a y : ZMod (∏ i ∈ R, p i))) =
        ∏ i ∈ R, ∑ h ∈ Finset.univ.erase (0 : ZMod (p i)),
          ZMod.stdAddChar (h * ((a x : ZMod (p i)) - (a y : ZMod (p i)))) := by
    simpa only [Int.cast_sub] using unitRamanujanKernel_subset p R hc (a x - a y)
  simp_rw [hk]
  rw [tensorRamanujan_energy_expansion p S R A (fun x i => (a x : ZMod (p i))) ha]
  simp only [subsetSieveCoefficient, Complex.ofReal_sum, Complex.ofReal_mul,
    Complex.ofReal_prod, Complex.ofReal_sub, Complex.ofReal_div, Complex.ofReal_natCast,
    Complex.ofReal_one, mul_assoc]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Supply_PrimeSubsetSieve
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Summing the positive subset expansion inside the additive large sieve -/

namespace Ostmann
open scoped Classical BigOperators

theorem prime_subset_product_dvd_iff {n : ℕ} (p : Fin n → ℕ)
    [∀ i, Fact (p i).Prime] (hc : Pairwise (fun i j => (p i).Coprime (p j)))
    (R : Finset (Fin n)) (i : Fin n) : (p i ∣ ∏ j ∈ R, p j) ↔ i ∈ R := by
  rw [(Fact.out : (p i).Prime).prime.dvd_finsetProd_iff]
  constructor
  · rintro ⟨j, hj, hd⟩
    by_cases hij : i = j
    · simpa only [hij] using hj
    · exact ((Fact.out : (p i).Prime).coprime_iff_not_dvd.mp (hc hij) hd).elim
  · intro hi
    exact ⟨i, hi, dvd_rfl⟩

theorem prime_subset_product_injective {n : ℕ} (p : Fin n → ℕ)
    [∀ i, Fact (p i).Prime] (hc : Pairwise (fun i j => (p i).Coprime (p j))) :
    Function.Injective (fun R : Finset (Fin n) => ∏ i ∈ R, p i) := by
  intro R T h
  ext i
  rw [← prime_subset_product_dvd_iff p hc R i,
    ← prime_subset_product_dvd_iff p hc T i]
  exact Iff.of_eq (congrArg (fun q => p i ∣ q) h)

/-- The complete double sum is bounded by the classical additive large sieve.
No centered-coordinate energy estimate is postulated in this step. -/
theorem prime_subset_sieve_bound (ls : PublishedAdditiveLargeSieve)
    {n M Q : ℕ} (p : Fin n → ℕ) [∀ i, Fact (p i).Prime]
    (hc : Pairwise (fun i j => (p i).Coprime (p j)))
    (S : ∀ i, Finset (ZMod (p i))) (G : Finset (Finset (Fin n)))
    (hQ : 1 ≤ Q) (hM : 1 ≤ M) (A : Finset (Fin M)) (hA : A.Nonempty) (J : ℤ)
    (hprod : ∀ R ∈ G, (∏ i ∈ R, p i) ≤ Q)
    (ha : ∀ R ∈ G, ∀ x ∈ A, ∀ i ∈ R, ((J + (x.val : ℤ) : ℤ) : ZMod (p i)) ∈ S i) :
    (∑ R ∈ G, ∑ T ∈ R.powerset, subsetSieveCoefficient p S R T *
      centeredSubsetEnergy p S T A (fun x i => ((J + (x.val : ℤ) : ℤ) : ZMod (p i)))) ≤
      ((M : ℝ) + (Q : ℝ) ^ 2) / A.card := by
  have hpos (R : Finset (Fin n)) : 0 < ∏ i ∈ R, p i :=
    Finset.prod_pos (fun i _ => (Fact.out : (p i).Prime).pos)
  have he (R) (hR : R ∈ G) :
      (∑ T ∈ R.powerset, subsetSieveCoefficient p S R T *
        centeredSubsetEnergy p S T A (fun x i => ((J + (x.val : ℤ) : ℤ) : ZMod (p i)))) =
      intervalSetReducedEnergy A J (∏ i ∈ R, p i) := by
    let : NeZero (∏ i ∈ R, p i) := ⟨(hpos R).ne'⟩
    rw [intervalSetReducedEnergy_eq_unitFrequencyEnergy]
    exact (subset_reduced_energy_expansion p S R hc A
      (fun x => J + (x.val : ℤ)) (ha R hR)).symm
  calc
    _ = ∑ R ∈ G, intervalSetReducedEnergy A J (∏ i ∈ R, p i) :=
      Finset.sum_congr rfl he
    _ = ∑ q ∈ G.image (fun R => ∏ i ∈ R, p i), intervalSetReducedEnergy A J q := by
      rw [Finset.sum_image]
      exact fun _ _ _ _ h => prime_subset_product_injective p hc h
    _ ≤ ∑ q ∈ Finset.Icc 1 Q, intervalSetReducedEnergy A J q := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro q hq
        obtain ⟨R, hR, rfl⟩ := Finset.mem_image.mp hq
        exact Finset.mem_Icc.mpr ⟨hpos R, hprod R hR⟩
      · intro q _ _
        exact intervalSetReducedEnergy_nonneg A J q
    _ ≤ _ := additiveSieve_probability_bound ls hM hQ A hA J

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Supply_SquarefreeMultiplierCount
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # An elementary positive-density supply of squarefree multipliers -/

namespace Ostmann
open scoped Classical BigOperators

private theorem reciprocal_square_step (x : ℝ) (hx : 0 < x) :
    (x + 1)⁻¹ ^ 2 ≤ x⁻¹ - (x + 1)⁻¹ := by
  have hx1 : 0 < x + 1 := by linarith
  have h : (x + 1)⁻¹ ^ 2 ≤ (x * (x + 1))⁻¹ := by
    rw [inv_pow, inv_le_inv₀ (sq_pos_of_pos hx1) (mul_pos hx hx1)]
    nlinarith
  calc
    _ ≤ (x * (x + 1))⁻¹ := h
    _ = x⁻¹ - (x + 1)⁻¹ := by field_simp; ring

theorem sum_reciprocal_squares_le_three_quarters (N : ℕ) :
    (∑ d ∈ Finset.Icc 2 N, (d : ℝ)⁻¹ ^ 2) ≤ 3 / 4 := by
  by_cases hN : 2 ≤ N
  · have hh : ∀ N : ℕ, N ≥ 2 → (∑ d ∈ Finset.Icc 2 N, (d : ℝ)⁻¹ ^ 2) ≤
        3 / 4 - (N : ℝ)⁻¹ := by
      intro N hN
      induction N, hN using Nat.le_induction with
      | base => norm_num
      | succ N hN ih =>
        rw [Finset.sum_Icc_succ_top (by omega)]
        have hp : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
        have hs := reciprocal_square_step (N : ℝ) hp
        push_cast
        linarith
    exact (hh N hN).trans (sub_le_self _ (by positivity))
  · have he : Finset.Icc 2 N = ∅ := Finset.Icc_eq_empty_of_lt (by omega)
    norm_num [he]

theorem nonSquarefreeMultipliers_subset (U : ℕ) :
    nonSquarefreeMultipliers U ⊆ (Finset.Icc 2 U).biUnion
      (fun d => positiveMultiplesUpTo U (d * d)) := by
  intro u hu
  obtain ⟨huU, hu0, hsq⟩ := Finset.mem_filter.mp hu
  have hex : ∃ p, Nat.Prime p ∧ p * p ∣ u := by
    by_contra h
    apply hsq
    apply Nat.squarefree_iff_prime_squarefree.mpr
    intro p hp hd
    exact h ⟨p, hp, hd⟩
  obtain ⟨p, hp, hd⟩ := hex
  have hpu : p ≤ u := Nat.le_of_dvd (Nat.pos_of_ne_zero hu0)
    (dvd_trans (dvd_mul_right p p) hd)
  refine Finset.mem_biUnion.mpr ⟨p, Finset.mem_Icc.mpr ⟨hp.two_le, ?_⟩, ?_⟩
  · have := Finset.mem_range.mp huU
    omega
  · exact Finset.mem_filter.mpr ⟨huU, hu0, hd⟩

theorem nonSquarefreeMultipliers_card_le (U : ℕ) :
    (nonSquarefreeMultipliers U).card ≤ ∑ d ∈ Finset.Icc 2 U, U / (d * d) := by
  apply (Finset.card_le_card (nonSquarefreeMultipliers_subset U)).trans
  apply Finset.card_biUnion_le.trans
  apply Finset.sum_le_sum
  intro d _
  exact (Nat.card_multiples' U (d * d)).le

theorem nonSquarefreeMultipliers_real_card_le (U : ℕ) :
    ((nonSquarefreeMultipliers U).card : ℝ) ≤ (3 / 4) * U := by
  calc
    _ ≤ ((∑ d ∈ Finset.Icc 2 U, U / (d * d) : ℕ) : ℝ) := by
      exact_mod_cast nonSquarefreeMultipliers_card_le U
    _ ≤ ∑ d ∈ Finset.Icc 2 U, (U : ℝ) * (d : ℝ)⁻¹ ^ 2 := by
      rw [Nat.cast_sum]
      apply Finset.sum_le_sum
      intro d _
      simpa only [Nat.cast_mul, mul_inv_rev, div_eq_mul_inv, pow_two] using
        (Nat.cast_div_le (m := U) (n := d * d) (α := ℝ))
    _ = (U : ℝ) * ∑ d ∈ Finset.Icc 2 U, (d : ℝ)⁻¹ ^ 2 := (Finset.mul_sum ..).symm
    _ ≤ (U : ℝ) * (3 / 4) := mul_le_mul_of_nonneg_left
      (sum_reciprocal_squares_le_three_quarters U) (Nat.cast_nonneg U)
    _ = _ := mul_comm _ _

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

theorem multiplierPrimeWeight_nonneg (P : Finset ℕ) (w : ℕ → ℝ)
    (hw : ∀ p ∈ P, 0 ≤ w p) (u : ℕ) : 0 ≤ multiplierPrimeWeight P w u := by
  apply Finset.sum_nonneg
  intro p hp
  split_ifs
  · exact hw p hp
  · exact le_rfl

theorem multiplierPrimeWeight_total_le (U : ℕ) (P : Finset ℕ) (w : ℕ → ℝ)
    (hw : ∀ p ∈ P, 0 ≤ w p) :
    (∑ u ∈ positiveMultipliers U, multiplierPrimeWeight P w u) ≤
      (U : ℝ) * ∑ p ∈ P, w p / p := by
  unfold multiplierPrimeWeight
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  calc
    (∑ u ∈ positiveMultipliers U, if p ∣ u then w p else 0) =
        ∑ _u ∈ (positiveMultipliers U).filter (fun u => p ∣ u), w p := by
      rw [Finset.sum_filter]
    _ = ((U / p : ℕ) : ℝ) * w p := by simp [positiveMultipliers_dvd_card]
    _ ≤ ((U : ℝ) / p) * w p := mul_le_mul_of_nonneg_right Nat.cast_div_le (hw p hp)
    _ = (U : ℝ) * (w p / p) := by ring

theorem badDivisorMultipliers_card_le (U : ℕ) (P : Finset ℕ) :
    ((badDivisorMultipliers U P).card : ℝ) ≤ (U : ℝ) * ∑ p ∈ P, (p : ℝ)⁻¹ := by
  have hs : badDivisorMultipliers U P ⊆ P.biUnion
      (fun p => (positiveMultipliers U).filter (fun u => p ∣ u)) := by
    intro u hu
    obtain ⟨hu, p, hp, hpu⟩ := Finset.mem_filter.mp hu
    exact Finset.mem_biUnion.mpr ⟨p, hp, Finset.mem_filter.mpr ⟨hu, hpu⟩⟩
  have hc := (Finset.card_le_card hs).trans (Finset.card_biUnion_le)
  calc
    _ ≤ ((∑ p ∈ P, ((positiveMultipliers U).filter (fun u => p ∣ u)).card : ℕ) : ℝ) := by
      exact_mod_cast hc
    _ = ∑ p ∈ P, ((U / p : ℕ) : ℝ) := by simp [positiveMultipliers_dvd_card]
    _ ≤ ∑ p ∈ P, (U : ℝ) / p := Finset.sum_le_sum (fun _ _ => Nat.cast_div_le)
    _ = _ := by simp only [div_eq_mul_inv, Finset.mul_sum]

theorem largeWeightMultipliers_card_budget (U : ℕ) (P : Finset ℕ) (w : ℕ → ℝ)
    (hw : ∀ p ∈ P, 0 ≤ w p) (B : ℝ) :
    B * (largeWeightMultipliers U P w B).card ≤ (U : ℝ) * ∑ p ∈ P, w p / p := by
  calc
    _ = ∑ _u ∈ largeWeightMultipliers U P w B, B := by simp [mul_comm]
    _ ≤ ∑ u ∈ largeWeightMultipliers U P w B, multiplierPrimeWeight P w u := by
      apply Finset.sum_le_sum
      intro u hu
      exact (Finset.mem_filter.mp hu).2.le
    _ ≤ ∑ u ∈ positiveMultipliers U, multiplierPrimeWeight P w u := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro u _ _
      exact multiplierPrimeWeight_nonneg P w hw u
    _ ≤ _ := multiplierPrimeWeight_total_le U P w hw

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Supply_GoodSieveMultipliers
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Simultaneously squarefree, coprime and low-weight sieve multipliers -/

namespace Ostmann
open scoped Classical BigOperators

/-- An explicit positive proportion.  The hypotheses will be furnished by
prime reciprocal and logarithmic-imbalance estimates in the application. -/
theorem goodSieveMultipliers_card_lower (U : ℕ) (T P : Finset ℕ) (w : ℕ → ℝ)
    (hw : ∀ p ∈ P, 0 ≤ w p) (B : ℝ) (hB : 0 < B)
    (hT : (∑ p ∈ T, (p : ℝ)⁻¹) ≤ 1 / 16)
    (hP : (∑ p ∈ P, w p / p) ≤ B / 16) :
    (U : ℝ) / 8 ≤ (goodSieveMultipliers U T P w B).card := by
  have hsubset : positiveMultipliers U ⊆
      ((goodSieveMultipliers U T P w B ∪ nonSquarefreeMultipliers U) ∪
        badDivisorMultipliers U T) ∪ largeWeightMultipliers U P w B := by
    intro u hu
    by_cases hs : Squarefree u
    · by_cases hd : ∃ p ∈ T, p ∣ u
      · exact Finset.mem_union_left _ (Finset.mem_union_right _
          (Finset.mem_filter.mpr ⟨hu, hd⟩))
      · by_cases hl : multiplierPrimeWeight P w u ≤ B
        · exact Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hu, hs, hd, hl⟩)))
        · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hu, lt_of_not_ge hl⟩)
    · apply Finset.mem_union_left
      apply Finset.mem_union_left
      apply Finset.mem_union_right
      obtain ⟨hu0, huU⟩ := Finset.mem_Icc.mp hu
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), by omega, hs⟩
  have hc : U ≤ (goodSieveMultipliers U T P w B).card +
      (nonSquarefreeMultipliers U).card + (badDivisorMultipliers U T).card +
        (largeWeightMultipliers U P w B).card := by
    have hh := Finset.card_le_card hsubset
    rw [positiveMultipliers_card] at hh
    have h1 := Finset.card_union_le (goodSieveMultipliers U T P w B) (nonSquarefreeMultipliers U)
    have h2 := Finset.card_union_le
      (goodSieveMultipliers U T P w B ∪ nonSquarefreeMultipliers U) (badDivisorMultipliers U T)
    have h3 := Finset.card_union_le
      ((goodSieveMultipliers U T P w B ∪ nonSquarefreeMultipliers U) ∪ badDivisorMultipliers U T)
      (largeWeightMultipliers U P w B)
    omega
  have hcr : (U : ℝ) ≤ (goodSieveMultipliers U T P w B).card +
      (nonSquarefreeMultipliers U).card + (badDivisorMultipliers U T).card +
        (largeWeightMultipliers U P w B).card := by exact_mod_cast hc
  have hd : ((badDivisorMultipliers U T).card : ℝ) ≤ (U : ℝ) / 16 := by
    calc
      _ ≤ (U : ℝ) * ∑ p ∈ T, (p : ℝ)⁻¹ := badDivisorMultipliers_card_le U T
      _ ≤ (U : ℝ) * (1 / 16) := mul_le_mul_of_nonneg_left hT (Nat.cast_nonneg U)
      _ = _ := by ring
  have hl : ((largeWeightMultipliers U P w B).card : ℝ) ≤ (U : ℝ) / 16 := by
    apply (mul_le_mul_iff_right₀ hB).mp
    calc
      _ ≤ (U : ℝ) * ∑ p ∈ P, w p / p := largeWeightMultipliers_card_budget U P w hw B
      _ ≤ (U : ℝ) * (B / 16) := mul_le_mul_of_nonneg_left hP (Nat.cast_nonneg U)
      _ = _ := by ring
  linarith [nonSquarefreeMultipliers_real_card_le U]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Supply_MultiplierRatioProduct
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Both imbalance products on the retained squarefree multipliers -/

namespace Ostmann
open scoped Classical BigOperators

theorem multiplierRatioProduct_exp_sum (P : Finset ℕ) (κ : ℕ → ℝ)
    (hκ : ∀ p ∈ P, 0 < κ p) (u : ℕ) :
    multiplierRatioProduct P κ u =
      Real.exp (∑ p ∈ P, if p ∣ u then Real.log (κ p) else 0) := by
  rw [Real.exp_sum]
  apply Finset.prod_congr rfl
  intro p hp
  by_cases h : p ∣ u
  · simp [h, Real.exp_log (hκ p hp)]
  · simp [h]

theorem multiplierRatioProduct_bounds (P : Finset ℕ) (κ : ℕ → ℝ)
    (hκ : ∀ p ∈ P, 0 < κ p) (u : ℕ) (B : ℝ)
    (hB : multiplierPrimeWeight P (fun p => |Real.log (κ p)|) u ≤ B) :
    Real.exp (-B) ≤ multiplierRatioProduct P κ u ∧
      multiplierRatioProduct P κ u ≤ Real.exp B := by
  have hsum : |∑ p ∈ P, if p ∣ u then Real.log (κ p) else 0| ≤ B := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    have he : (∑ p ∈ P, |if p ∣ u then Real.log (κ p) else 0|) =
        multiplierPrimeWeight P (fun p => |Real.log (κ p)|) u := by
      unfold multiplierPrimeWeight
      apply Finset.sum_congr rfl
      intro p _
      by_cases hp : p ∣ u <;> simp [hp]
    exact he.trans_le hB
  rw [multiplierRatioProduct_exp_sum P κ hκ u]
  exact ⟨Real.exp_le_exp.mpr (abs_le.mp hsum).1,
    Real.exp_le_exp.mpr (abs_le.mp hsum).2⟩

theorem goodSieveMultipliers_ratio_products (U : ℕ) (T P : Finset ℕ) (κ : ℕ → ℝ)
    (hκ : ∀ p ∈ P, 0 < κ p) (B : ℝ) {u : ℕ}
    (hu : u ∈ goodSieveMultipliers U T P (fun p => |Real.log (κ p)|) B) :
    Real.exp (-B) ≤ multiplierRatioProduct P κ u ∧
      Real.exp (-B) ≤ multiplierRatioProduct P (fun p => (κ p)⁻¹) u := by
  have hB := (Finset.mem_filter.mp hu).2.2.2
  refine ⟨(multiplierRatioProduct_bounds P κ hκ u B hB).1, ?_⟩
  apply (multiplierRatioProduct_bounds P (fun p => (κ p)⁻¹)
    (fun p hp => inv_pos.mpr (hκ p hp)) u B ?_).1
  simpa only [Real.log_inv, abs_neg] using hB

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Supply_WeightedMultiplierSupply
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The weighted positive-density supply used in the sieve amplification -/

namespace Ostmann
open scoped Classical BigOperators

theorem goodSieveMultipliers_coprime (U : ℕ) (T P : Finset ℕ) (w : ℕ → ℝ)
    (B : ℝ) (hT : ∀ p ∈ T, Nat.Prime p) {u : ℕ}
    (hu : u ∈ goodSieveMultipliers U T P w B) : u.Coprime (∏ p ∈ T, p) := by
  apply Nat.coprime_prod_right_iff.mpr
  intro p hp
  apply Nat.Coprime.symm
  apply (hT p hp).coprime_iff_not_dvd.mpr
  intro hd
  exact (Finset.mem_filter.mp hu).2.2.1 ⟨p, hp, hd⟩

theorem weighted_multiplier_supply (U : ℕ) (T P : Finset ℕ) (κ : ℕ → ℝ)
    (hκ : ∀ p ∈ P, 0 < κ p) (hTprime : ∀ p ∈ T, Nat.Prime p)
    (B : ℝ) (hB : 0 < B)
    (hT : (∑ p ∈ T, (p : ℝ)⁻¹) ≤ 1 / 16)
    (hP : (∑ p ∈ P, |Real.log (κ p)| / p) ≤ B / 16) :
    (U : ℝ) / 8 * Real.exp (-B) ≤
      ∑ u ∈ (positiveMultipliers U).filter
        (fun u => Squarefree u ∧ u.Coprime (∏ p ∈ T, p)), multiplierRatioProduct P κ u := by
  let G := goodSieveMultipliers U T P (fun p => |Real.log (κ p)|) B
  have hcard := goodSieveMultipliers_card_lower U T P (fun p => |Real.log (κ p)|)
    (fun _ _ => abs_nonneg _) B hB hT hP
  have hsubset : G ⊆ (positiveMultipliers U).filter
      (fun u => Squarefree u ∧ u.Coprime (∏ p ∈ T, p)) := by
    intro u hu
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hu).1,
      (Finset.mem_filter.mp hu).2.1, goodSieveMultipliers_coprime U T P _ B hTprime hu⟩
  calc
    _ ≤ (G.card : ℝ) * Real.exp (-B) :=
      mul_le_mul_of_nonneg_right hcard (Real.exp_pos _).le
    _ = ∑ _u ∈ G, Real.exp (-B) := by simp
    _ ≤ ∑ u ∈ G, multiplierRatioProduct P κ u := by
      apply Finset.sum_le_sum
      intro u hu
      exact (goodSieveMultipliers_ratio_products U T P κ hκ B hu).1
    _ ≤ _ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
      intro u _ _
      unfold multiplierRatioProduct
      apply Finset.prod_nonneg
      intro p hp
      split_ifs
      · exact (hκ p hp).le
      · exact zero_le_one

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_PrimeDivisorIndices
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Recovering squarefree integer multipliers as actual prime-index subsets -/

namespace Ostmann
open scoped Classical BigOperators

theorem coprime_prime_family_injective {n : ℕ} (p : Fin n → ℕ)
    [∀ i, Fact (p i).Prime] (hc : Pairwise (fun i j => (p i).Coprime (p j))) :
    Function.Injective p := by
  intro i j he
  by_contra hij
  exact ((Fact.out : (p i).Prime).coprime_iff_not_dvd.mp (hc hij)) (dvd_of_eq he)

theorem primeDivisorIndices_image {n : ℕ} (p : Fin n → ℕ)
    [∀ i, Fact (p i).Prime] {u : ℕ} (hu : u ≠ 0)
    (hcover : ∀ q ∈ u.primeFactors, ∃ i, p i = q) :
    (primeDivisorIndices p u).image p = u.primeFactors := by
  ext q
  constructor
  · intro hq
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hq
    exact Nat.mem_primeFactors.mpr ⟨Fact.out, (Finset.mem_filter.mp hi).2, hu⟩
  · intro hq
    obtain ⟨i, rfl⟩ := hcover q hq
    exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, (Nat.mem_primeFactors.mp hq).2.1⟩, rfl⟩

theorem primeDivisorIndices_product {n : ℕ} (p : Fin n → ℕ)
    [∀ i, Fact (p i).Prime] (hc : Pairwise (fun i j => (p i).Coprime (p j)))
    {u : ℕ} (hu : Squarefree u) (hcover : ∀ q ∈ u.primeFactors, ∃ i, p i = q) :
    (∏ i ∈ primeDivisorIndices p u, p i) = u := by
  have he := Finset.prod_image (f := id) (s := primeDivisorIndices p u)
    (fun _ _ _ _ h => coprime_prime_family_injective p hc h)
  change (∏ q ∈ (primeDivisorIndices p u).image p, q) =
    (∏ i ∈ primeDivisorIndices p u, p i) at he
  rw [← he, primeDivisorIndices_image p hu.ne_zero hcover]
  exact Nat.prod_primeFactors_of_squarefree hu

theorem primeDivisorIndices_disjoint {n : ℕ} (p : Fin n → ℕ)
    (T : Finset (Fin n)) {u : ℕ} (hu : u.Coprime (∏ i ∈ T, p i))
    (hp : ∀ i, Nat.Prime (p i)) : Disjoint T (primeDivisorIndices p u) := by
  apply Finset.disjoint_left.mpr
  intro i hi hiu
  have hd : p i ∣ u := (Finset.mem_filter.mp hiu).2
  have he : p i ∣ ∏ j ∈ T, p j := Finset.dvd_prod_of_mem p hi
  exact (hp i).ne_one (Nat.eq_one_of_dvd_coprimes hu hd he)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Supply_SubsetEnergyAmplification
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Amplifying the positive centered-energy expansion by extensions -/

namespace Ostmann
open scoped Classical BigOperators

theorem subset_energy_amplification {n : ℕ} (p : Fin n → ℕ) [∀ i, NeZero (p i)]
    (S : ∀ i, Finset (ZMod (p i))) (hS : ∀ i, (S i).Nonempty)
    (F G : Finset (Finset (Fin n))) (E : Finset (Fin n) → ℝ)
    (hE : ∀ T, 0 ≤ E T) (α C : ℝ)
    (hweight : ∀ T ∈ F, α ≤ ∑ R ∈ G,
      if T ⊆ R then subsetSieveCoefficient p S R T else 0)
    (hsieve : (∑ R ∈ G, ∑ T ∈ R.powerset, subsetSieveCoefficient p S R T * E T) ≤ C) :
    α * (∑ T ∈ F, E T) ≤ C := by
  have hsmall (R : Finset (Fin n)) :
      (∑ T ∈ F, if T ⊆ R then subsetSieveCoefficient p S R T * E T else 0) ≤
        ∑ T ∈ R.powerset, subsetSieveCoefficient p S R T * E T := by
    rw [← Finset.sum_filter]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro T hT
      exact Finset.mem_powerset.mpr (Finset.mem_filter.mp hT).2
    · intro T _ _
      exact mul_nonneg (subsetSieveCoefficient_nonneg p S R T (fun i _ => hS i)) (hE T)
  calc
    _ = ∑ T ∈ F, α * E T := Finset.mul_sum ..
    _ ≤ ∑ T ∈ F, (∑ R ∈ G,
        if T ⊆ R then subsetSieveCoefficient p S R T else 0) * E T := by
      apply Finset.sum_le_sum
      intro T hT
      exact mul_le_mul_of_nonneg_right (hweight T hT) (hE T)
    _ = ∑ R ∈ G, ∑ T ∈ F,
        if T ⊆ R then subsetSieveCoefficient p S R T * E T else 0 := by
      simp only [Finset.sum_mul, ite_mul, zero_mul]
      exact Finset.sum_comm
    _ ≤ ∑ R ∈ G, ∑ T ∈ R.powerset, subsetSieveCoefficient p S R T * E T :=
      Finset.sum_le_sum (fun R _ => hsmall R)
    _ ≤ C := hsieve

/-- Once the concrete extension weights are supplied, the actual centered
subset energies inherit the classical additive-sieve budget. -/
theorem prime_subset_energy_budget (ls : PublishedAdditiveLargeSieve)
    {n M Q : ℕ} (p : Fin n → ℕ) [∀ i, Fact (p i).Prime]
    (hc : Pairwise (fun i j => (p i).Coprime (p j)))
    (S : ∀ i, Finset (ZMod (p i))) (hS : ∀ i, (S i).Nonempty)
    (F G : Finset (Finset (Fin n)))
    (hQ : 1 ≤ Q) (hM : 1 ≤ M) (A : Finset (Fin M)) (hA : A.Nonempty) (J : ℤ)
    (hprod : ∀ R ∈ G, (∏ i ∈ R, p i) ≤ Q)
    (ha : ∀ R ∈ G, ∀ x ∈ A, ∀ i ∈ R, ((J + (x.val : ℤ) : ℤ) : ZMod (p i)) ∈ S i)
    (α : ℝ) (hweight : ∀ T ∈ F, α ≤ ∑ R ∈ G,
      if T ⊆ R then subsetSieveCoefficient p S R T else 0) :
    α * (∑ T ∈ F, centeredSubsetEnergy p S T A
      (fun x i => ((J + (x.val : ℤ) : ℤ) : ZMod (p i)))) ≤
        ((M : ℝ) + (Q : ℝ) ^ 2) / A.card := by
  exact subset_energy_amplification p S hS F G _
    (fun T => centeredSubsetEnergy_nonneg p S T A _) α _ hweight
      (prime_subset_sieve_bound ls p hc S G hQ hM A hA J hprod ha)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Supply_IndexedMultiplierWeights
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Identifying the integer multiplier weights with sieve extensions -/

namespace Ostmann
open scoped Classical BigOperators

theorem multiplierRatioProduct_indices {n : ℕ} (p : Fin n → ℕ)
    [∀ i, Fact (p i).Prime] (hc : Pairwise (fun i j => (p i).Coprime (p j)))
    (κ : ℕ → ℝ) (u : ℕ) :
    multiplierRatioProduct (Finset.univ.image p) κ u =
      ∏ i ∈ primeDivisorIndices p u, κ (p i) := by
  unfold multiplierRatioProduct primeDivisorIndices
  rw [Finset.prod_image]
  · rw [Finset.prod_filter]
  · exact fun _ _ _ _ h => coprime_prime_family_injective p hc h

theorem subsetSieveCoefficient_extension {n : ℕ} (p : Fin n → ℕ)
    (S : ∀ i, Finset (ZMod (p i))) (T I : Finset (Fin n)) (hTI : Disjoint T I) :
    subsetSieveCoefficient p S (T ∪ I) T =
      (∏ i ∈ T, (p i : ℝ)) * ∏ i ∈ I, ((p i : ℝ) / (S i).card - 1) := by
  have he : (T ∪ I) \ T = I := by
    ext i
    have hd : i ∈ T → i ∉ I := fun hi hiI => (Finset.disjoint_left.mp hTI) hi hiI
    simp only [Finset.mem_sdiff, Finset.mem_union]
    tauto
  simp only [subsetSieveCoefficient, he]

theorem primeIndexExtension_product {n : ℕ} (p : Fin n → ℕ)
    [∀ i, Fact (p i).Prime] (hc : Pairwise (fun i j => (p i).Coprime (p j)))
    (T : Finset (Fin n)) {u : ℕ} (hu : Squarefree u)
    (hcover : ∀ q ∈ u.primeFactors, ∃ i, p i = q)
    (hcop : u.Coprime (∏ i ∈ T, p i)) :
    (∏ i ∈ T ∪ primeDivisorIndices p u, p i) = (∏ i ∈ T, p i) * u := by
  rw [Finset.prod_union (primeDivisorIndices_disjoint p T hcop (fun _ => Fact.out)),
    primeDivisorIndices_product p hc hu hcover]

theorem primeIndexExtension_injective {n : ℕ} (p : Fin n → ℕ)
    [∀ i, Fact (p i).Prime] (hc : Pairwise (fun i j => (p i).Coprime (p j)))
    (T : Finset (Fin n)) (D : Finset ℕ)
    (hsq : ∀ u ∈ D, Squarefree u)
    (hcover : ∀ u ∈ D, ∀ q ∈ u.primeFactors, ∃ i, p i = q)
    (hcop : ∀ u ∈ D, u.Coprime (∏ i ∈ T, p i)) :
    Set.InjOn (fun u => T ∪ primeDivisorIndices p u) D := by
  intro u hu v hv huv
  have he := congrArg (fun R : Finset (Fin n) => ∏ i ∈ R, p i) huv
  rw [primeIndexExtension_product p hc T (hsq u hu) (hcover u hu) (hcop u hu),
    primeIndexExtension_product p hc T (hsq v hv) (hcover v hv) (hcop v hv)] at he
  exact Nat.eq_of_mul_eq_mul_left
    (Finset.prod_pos (fun i _ => (Fact.out : (p i).Prime).pos)) he

theorem primeIndexExtension_coefficient {n : ℕ} (p : Fin n → ℕ)
    [∀ i, Fact (p i).Prime] (hc : Pairwise (fun i j => (p i).Coprime (p j)))
    (S : ∀ i, Finset (ZMod (p i))) (κ : ℕ → ℝ)
    (hκ : ∀ i, κ (p i) = (p i : ℝ) / (S i).card - 1)
    (T : Finset (Fin n)) {u : ℕ} (hcop : u.Coprime (∏ i ∈ T, p i)) :
    subsetSieveCoefficient p S (T ∪ primeDivisorIndices p u) T =
      (∏ i ∈ T, (p i : ℝ)) * multiplierRatioProduct (Finset.univ.image p) κ u := by
  rw [subsetSieveCoefficient_extension p S T _
    (primeDivisorIndices_disjoint p T hcop (fun _ => Fact.out)),
    multiplierRatioProduct_indices p hc]
  simp only [hκ]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Supply_ConcreteExtensionWeights
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integer multipliers supply the actual subset extension weights -/

namespace Ostmann
open scoped Classical BigOperators

theorem concrete_extension_weight_lower {n : ℕ} (p : Fin n → ℕ)
    [∀ i, Fact (p i).Prime] (hc : Pairwise (fun i j => (p i).Coprime (p j)))
    (S : ∀ i, Finset (ZMod (p i))) (hS : ∀ i, (S i).Nonempty)
    (κ : ℕ → ℝ) (hκ : ∀ q ∈ Finset.univ.image p, 0 < κ q)
    (hκS : ∀ i, κ (p i) = (p i : ℝ) / (S i).card - 1)
    (Q : ℕ) (T : Finset (Fin n))
    (hcover : ∀ q, Nat.Prime q → q ≤ Q → ∃ i, p i = q)
    (B : ℝ) (hB : 0 < B)
    (hT : (∑ q ∈ T.image p, (q : ℝ)⁻¹) ≤ 1 / 16)
    (hP : (∑ q ∈ Finset.univ.image p, |Real.log (κ q)| / q) ≤ B / 16) :
    ((∏ i ∈ T, p i : ℕ) : ℝ) * ((Q / (∏ i ∈ T, p i) : ℕ) : ℝ) / 8 * Real.exp (-B) ≤
      ∑ R ∈ primeProductSubsets p Q,
        if T ⊆ R then subsetSieveCoefficient p S R T else 0 := by
  let t := ∏ i ∈ T, p i
  let U := Q / t
  let P := Finset.univ.image p
  let D := (positiveMultipliers U).filter (fun u => Squarefree u ∧ u.Coprime t)
  have hTprod : (∏ q ∈ T.image p, q) = t := by
    rw [Finset.prod_image]
    exact fun _ _ _ _ h => coprime_prime_family_injective p hc h
  have hTprime : ∀ q ∈ T.image p, Nat.Prime q := by
    intro q hq
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hq
    exact Fact.out
  have hweighted := weighted_multiplier_supply U (T.image p) P κ hκ hTprime B hB hT hP
  rw [hTprod] at hweighted
  change (U : ℝ) / 8 * Real.exp (-B) ≤ ∑ u ∈ D, multiplierRatioProduct P κ u at hweighted
  have hsq (u) (hu : u ∈ D) : Squarefree u := (Finset.mem_filter.mp hu).2.1
  have hcop (u) (hu : u ∈ D) : u.Coprime t := (Finset.mem_filter.mp hu).2.2
  have hcov (u) (hu : u ∈ D) (q) (hq : q ∈ u.primeFactors) : ∃ i, p i = q := by
    apply hcover q (Nat.mem_primeFactors.mp hq).1
    have hqu : q ≤ u := Nat.le_of_dvd (Nat.pos_of_ne_zero (hsq u hu).ne_zero)
      (Nat.mem_primeFactors.mp hq).2.1
    have huU : u ≤ U := (Finset.mem_Icc.mp (Finset.mem_filter.mp hu).1).2
    exact hqu.trans (huU.trans (Nat.div_le_self Q t))
  have hinj := primeIndexExtension_injective p hc T D hsq hcov hcop
  have himage : D.image (fun u => T ∪ primeDivisorIndices p u) ⊆ primeProductSubsets p Q := by
    intro R hR
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hR
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [primeIndexExtension_product p hc T (hsq u hu) (hcov u hu) (hcop u hu)]
    have huU : u ≤ U := (Finset.mem_Icc.mp (Finset.mem_filter.mp hu).1).2
    exact (Nat.mul_le_mul_left t huU).trans (by simpa [Nat.mul_comm] using Nat.div_mul_le_self Q t)
  calc
    _ = (t : ℝ) * ((U : ℝ) / 8 * Real.exp (-B)) := by dsimp [t, U]; ring
    _ ≤ (t : ℝ) * ∑ u ∈ D, multiplierRatioProduct P κ u :=
      mul_le_mul_of_nonneg_left hweighted (Nat.cast_nonneg t)
    _ = ∑ R ∈ D.image (fun u => T ∪ primeDivisorIndices p u),
        if T ⊆ R then subsetSieveCoefficient p S R T else 0 := by
      rw [Finset.sum_image hinj]
      simp only [Finset.subset_union_left, ite_true, if_true]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u hu
      rw [primeIndexExtension_coefficient p hc S κ hκS T (hcop u hu), Nat.cast_prod]
    _ ≤ _ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg himage
      intro R _ _
      split_ifs
      · exact subsetSieveCoefficient_nonneg p S R T (fun i _ => hS i)
      · exact le_rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Supply_ConcreteSubsetEnergyBudget
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The centered-subset budget with all extension weights discharged -/

namespace Ostmann
open scoped Classical BigOperators

theorem floor_product_half_bound {Q t : ℕ} (ht : 0 < t) (htQ : t ≤ Q) :
    (Q : ℝ) / 2 ≤ (t : ℝ) * (Q / t : ℕ) := by
  have hU : 1 ≤ Q / t := (Nat.le_div_iff_mul_le ht).mpr (by simpa using htQ)
  have hmod := Nat.mod_lt Q ht
  have hid := Nat.mod_add_div Q t
  have htU := Nat.mul_le_mul_left t hU
  have hQ : Q ≤ 2 * (t * (Q / t)) := by nlinarith
  have hQr : (Q : ℝ) ≤ 2 * ((t : ℝ) * (Q / t : ℕ)) := by exact_mod_cast hQ
  linarith

/-- The finite form of (5.4), before specializing the logarithmic budget.
Its multiplier lower bound is proved from squarefreeness, divisibility counts
and Markov's inequality; it is not an additional analytic assumption. -/
theorem concrete_subset_energy_budget (ls : PublishedAdditiveLargeSieve)
    {n M Q : ℕ} (p : Fin n → ℕ) [∀ i, Fact (p i).Prime]
    (hc : Pairwise (fun i j => (p i).Coprime (p j)))
    (S : ∀ i, Finset (ZMod (p i))) (hS : ∀ i, (S i).Nonempty)
    (κ : ℕ → ℝ) (hκ : ∀ q ∈ Finset.univ.image p, 0 < κ q)
    (hκS : ∀ i, κ (p i) = (p i : ℝ) / (S i).card - 1)
    (hQ : 1 ≤ Q) (hM : 1 ≤ M)
    (hcover : ∀ q, Nat.Prime q → q ≤ Q → ∃ i, p i = q)
    (A : Finset (Fin M)) (hA : A.Nonempty) (J : ℤ)
    (ha : ∀ x ∈ A, ∀ i, ((J + (x.val : ℤ) : ℤ) : ZMod (p i)) ∈ S i)
    (F : Finset (Finset (Fin n)))
    (hprod : ∀ T ∈ F, (∏ i ∈ T, p i) ≤ Q)
    (hsmall : ∀ T ∈ F, (∑ q ∈ T.image p, (q : ℝ)⁻¹) ≤ 1 / 16)
    (B : ℝ) (hB : 0 < B)
    (hP : (∑ q ∈ Finset.univ.image p, |Real.log (κ q)| / q) ≤ B / 16) :
    ((Q : ℝ) / 16 * Real.exp (-B)) *
      (∑ T ∈ F, centeredSubsetEnergy p S T A
        (fun x i => ((J + (x.val : ℤ) : ℤ) : ZMod (p i)))) ≤
      ((M : ℝ) + (Q : ℝ) ^ 2) / A.card := by
  apply prime_subset_energy_budget ls p hc S hS F (primeProductSubsets p Q)
    hQ hM A hA J
  · intro R hR
    exact (Finset.mem_filter.mp hR).2
  · intro R _ x hx i _
    exact ha x hx i
  · intro T hT
    have ht : 0 < ∏ i ∈ T, p i :=
      Finset.prod_pos (fun i _ => (Fact.out : (p i).Prime).pos)
    have hhalf := floor_product_half_bound ht (hprod T hT)
    have hw := concrete_extension_weight_lower p hc S hS κ hκ hκS Q T hcover B hB
      (hsmall T hT) hP
    apply le_trans _ hw
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    linarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Supply_RestrictedSubsetEnergy
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Restricting the centered-energy budget to the selected sparse primes -/

namespace Ostmann
open scoped Classical BigOperators

theorem centeredSubsetEnergy_embedding {n m : ℕ} (p : Fin n → ℕ)
    [∀ i, NeZero (p i)] (S : ∀ i, Finset (ZMod (p i)))
    (e : Fin m ↪ Fin n) (T : Finset (Fin m)) {ι : Type*}
    (A : Finset ι) (a : ι → ∀ i, ZMod (p i)) :
    centeredSubsetEnergy (fun i => p (e i)) (fun i => S (e i)) T A
      (fun x i => a x (e i)) = centeredSubsetEnergy p S (T.image e) A a := by
  apply Complex.ofReal_injective
  rw [centeredSubsetEnergy_formula, centeredSubsetEnergy_formula]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  symm
  exact Finset.prod_image (fun i _ j _ hij => e.injective hij)

theorem lowMode_energy_embedding {n m : ℕ} (p : Fin n → ℕ)
    [∀ i, NeZero (p i)] (S : ∀ i, Finset (ZMod (p i)))
    (e : Fin m ↪ Fin n) {ι : Type*} (A : Finset ι)
    (a : ι → ∀ i, ZMod (p i)) (K : ℕ) :
    countingVectorNorm (lowModeVector K (averagedCoordinates A
      (fun x => tensorPointCoordinates (fun i => p (e i)) (fun i => S (e i))
        (fun i => a x (e i))))) ^ 2 =
      ∑ T ∈ (Finset.univ.filter (fun T : Finset (Fin m) => T.card ≤ K)).image
        (fun T => T.image e), centeredSubsetEnergy p S T A a := by
  rw [lowMode_tensor_energy, Finset.sum_image]
  · rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro T _
    split_ifs
    · exact centeredSubsetEnergy_embedding p S e T A a
    · rfl
  · intro T _ U _ h
    exact Finset.image_injective e.injective h

/-- The sparse tensor uses only its selected prime coordinates. Its low-mode
energy is bounded by the sieve on the full prime family, with no factor for
the number of unused coordinates. -/
theorem restricted_lowMode_energy_budget (ls : PublishedAdditiveLargeSieve)
    {n m M Q : ℕ} (p : Fin n → ℕ) [∀ i, Fact (p i).Prime]
    (hc : Pairwise (fun i j => (p i).Coprime (p j)))
    (S : ∀ i, Finset (ZMod (p i))) (hS : ∀ i, (S i).Nonempty)
    (κ : ℕ → ℝ) (hκ : ∀ q ∈ Finset.univ.image p, 0 < κ q)
    (hκS : ∀ i, κ (p i) = (p i : ℝ) / (S i).card - 1)
    (hQ : 1 ≤ Q) (hM : 1 ≤ M)
    (hcover : ∀ q, Nat.Prime q → q ≤ Q → ∃ i, p i = q)
    (A : Finset (Fin M)) (hA : A.Nonempty) (J : ℤ)
    (ha : ∀ x ∈ A, ∀ i, ((J + (x.val : ℤ) : ℤ) : ZMod (p i)) ∈ S i)
    (e : Fin m ↪ Fin n) (K : ℕ)
    (hprod : ∀ T : Finset (Fin m), T.card ≤ K → (∏ i ∈ T, p (e i)) ≤ Q)
    (hsmall : ∀ T : Finset (Fin m), T.card ≤ K →
      (∑ q ∈ T.image (fun i => p (e i)), (q : ℝ)⁻¹) ≤ 1 / 16)
    (B : ℝ) (hB : 0 < B)
    (hP : (∑ q ∈ Finset.univ.image p, |Real.log (κ q)| / q) ≤ B / 16) :
    ((Q : ℝ) / 16 * Real.exp (-B)) *
      countingVectorNorm (lowModeVector K (averagedCoordinates A
        (fun x => tensorPointCoordinates (fun i => p (e i)) (fun i => S (e i))
          (fun i => ((J + (x.val : ℤ) : ℤ) : ZMod (p (e i))))))) ^ 2 ≤
      ((M : ℝ) + (Q : ℝ) ^ 2) / A.card := by
  rw [lowMode_energy_embedding p S e A (fun x i => ((J + (x.val : ℤ) : ℤ) : ZMod (p i))) K]
  apply concrete_subset_energy_budget ls p hc S hS κ hκ hκS hQ hM hcover A hA J ha
  · intro U hU
    obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hU
    rw [Finset.prod_image (fun i _ j _ hij => e.injective hij)]
    exact hprod T (Finset.mem_filter.mp hT).2
  · intro U hU
    obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hU
    rw [Finset.image_image]
    exact hsmall T (Finset.mem_filter.mp hT).2
  · exact hB
  · exact hP

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_SparsePairEnergyBudget
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Combining the actual sparse pair kernel with its two energy budgets -/

namespace Ostmann
open scoped Classical BigOperators

theorem complementary_field_card_ratio {p : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (hS : S.Nonempty) (hSp : S.card < p) :
    ((p : ℝ) / S.card - 1)⁻¹ = (p : ℝ) / (Finset.univ \ S).card - 1 := by
  have hs : (0 : ℝ) < S.card := by exact_mod_cast Finset.card_pos.mpr hS
  have htNat : (Finset.univ \ S).card = p - S.card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ S), Finset.card_univ, ZMod.card]
  have ht : (0 : ℝ) < (Finset.univ \ S).card := by
    rw [htNat]
    exact_mod_cast Nat.sub_pos_of_lt hSp
  have hsum : ((S.card : ℕ) : ℝ) + (Finset.univ \ S).card = p := by
    rw [htNat]
    exact_mod_cast Nat.add_sub_of_le hSp.le
  have he : (p : ℝ) / S.card - 1 = ((Finset.univ \ S).card : ℝ) / S.card := by
    apply (eq_div_iff hs.ne').mpr
    field_simp
    linarith
  rw [he, inv_div]
  apply (eq_sub_iff_add_eq).mpr
  apply (div_add_one ht.ne').trans
  congr 1

theorem weighted_pair_square_bound (w α O a b E F : ℝ)
    (hw : 0 ≤ w) (hα : 0 ≤ α) (hO : 0 ≤ O) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hEF : 0 ≤ E)
    (hp : w ≤ O * a * b) (hA : α * a ^ 2 ≤ E) (hB : α * b ^ 2 ≤ F) :
    α ^ 2 * w ^ 2 ≤ O ^ 2 * E * F := by
  have hs := (sq_le_sq₀ hw (mul_nonneg (mul_nonneg hO ha) hb)).mpr hp
  have he := mul_le_mul hA hB (mul_nonneg hα (sq_nonneg b)) hEF
  calc
    _ ≤ α ^ 2 * (O * a * b) ^ 2 := mul_le_mul_of_nonneg_left hs (sq_nonneg α)
    _ = O ^ 2 * ((α * a ^ 2) * (α * b ^ 2)) := by ring
    _ ≤ O ^ 2 * (E * F) := mul_le_mul_of_nonneg_left he (sq_nonneg O)
    _ = _ := by ring

/-- A single finite bound for the concrete sparse weight. The two energy
bounds here are the quantities proved by `restricted_lowMode_energy_budget`.
No norm of an untruncated tensor and no dimension factor appears. -/
theorem sparse_pair_average_energy_budget {n : ℕ}
    (p : Fin n → ℕ) [∀ i, Fact (p i).Prime]
    (S : ∀ i, Finset (ZMod (p i)))
    (hS : ∀ i, (S i).Nonempty) (hSp : ∀ i, (S i).card < p i)
    (hp : ∀ i, (100 : ℝ) ≤ p i)
    (hlo : ∀ i, (1 / 3 : ℝ) ≤ residueDensity (S i))
    (hhi : ∀ i, residueDensity (S i) ≤ 2 / 3)
    (ε : ℝ) (hε : 0 ≤ ε) (hεsmall : ε ≤ 1 / 1000000)
    (hL1 : ∀ i, (p i : ℝ)⁻¹ * ∑ b, ‖normalizedResidueTransform (S i) b‖ ≤ ε ^ 2)
    (L : ℝ) (hL : 1 ≤ L) (hH : (∑ i, (p i : ℝ)⁻¹) ≤ L)
    (K : ℕ) (hK : 1000 * L ≤ K)
    {ι κ : Type*} (A : Finset ι) (B : Finset κ)
    (a : ι → ∀ i, ZMod (p i)) (b : κ → ∀ i, ZMod (p i))
    (ha : ∀ x ∈ A, ∀ i, a x i ∈ S i)
    (hb : ∀ y ∈ B, ∀ i, b y i ∈ Finset.univ \ S i)
    (α E F : ℝ) (hα : 0 ≤ α) (hE : 0 ≤ E)
    (hEA : α * countingVectorNorm (lowModeVector (2 * K)
      (averagedCoordinates A (fun x => tensorPointCoordinates p S (a x)))) ^ 2 ≤ E)
    (hEB : α * countingVectorNorm (lowModeVector (2 * K)
      (averagedCoordinates B (fun y => tensorPointCoordinates p
        (fun i => Finset.univ \ S i) (b y)))) ^ 2 ≤ F) :
    let U := ∏ i, sparseKernelUnitFactor (p i)
      (((largeTransformSpectrum (normalizedResidueTransform (S i))).card : ℝ) / p i)
    0 < U ∧ U / 2 ≤ tensorRealUnitMean p (sparseSubsetWeight p S K) ∧
      α ^ 2 * (sparseWeightPairAverage p S K A B a b) ^ 2 ≤
        (2 * U * Real.exp (-(8 / 5) * ∑ i, (p i : ℝ)⁻¹)) ^ 2 * E * F := by
  intro U
  obtain ⟨hU, hmean, hop⟩ := sparse_finite_contraction p S hS hSp hp hlo hhi
    ε hε hεsmall hL1 L hL hH K hK
  refine ⟨hU, hmean, ?_⟩
  apply weighted_pair_square_bound _ _ _ _ _ E F
    (sparseWeightPairAverage_nonneg p S K A B a b) hα (by positivity)
    (by unfold countingVectorNorm; positivity) (by unfold countingVectorNorm; positivity) hE
    ?_ hEA hEB
  exact (sparseWeightPairAverage_le p S K A B a b ha hb).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hop (by unfold countingVectorNorm; positivity))
      (by unfold countingVectorNorm; positivity))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Supply_ConstantModeBudget
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The constant mode bounds the size of a sieved interval subset -/
namespace Ostmann
open scoped Classical BigOperators

 theorem lowMode_tensor_energy_one_le {n : ℕ} (p : Fin n → ℕ) [∀ i, NeZero (p i)]
    (S : ∀ i, Finset (ZMod (p i))) {ι : Type*} (A : Finset ι) (hA : A.Nonempty)
    (a : ι → ∀ i, ZMod (p i)) (K : ℕ) :
    1 ≤ countingVectorNorm (lowModeVector K
      (averagedCoordinates A (fun x => tensorPointCoordinates p S (a x)))) ^ 2 := by
  rw [lowMode_tensor_energy]
  have he : (if (∅ : Finset (Fin n)).card ≤ K then centeredSubsetEnergy p S ∅ A a else 0) = 1 := by
    simp [centeredSubsetEnergy_empty p S A hA a]
  have hh := Finset.single_le_sum (s := Finset.univ)
    (f := fun T : Finset (Fin n) => if T.card ≤ K then centeredSubsetEnergy p S T A a else 0)
    (by intro T _; split_ifs; exact centeredSubsetEnergy_nonneg p S T A a; exact le_rfl)
    (Finset.mem_univ (∅ : Finset (Fin n)))
  simpa only [he] using hh

 theorem constant_mode_card_bound (α E m v : ℝ) (hα : 0 ≤ α) (hm : 0 < m)
    (hv : 1 ≤ v) (hbudget : α * v ≤ E / m) : α * m ≤ E := by
  have h := (mul_le_mul_of_nonneg_left hv hα).trans hbudget
  rw [mul_one] at h
  exact (le_div_iff₀ hm).mp h

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_SparsePairSizeBound
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing the normalizations in the sparse pair bound -/
namespace Ostmann
open scoped Classical BigOperators

theorem normalized_pair_energy_bound (s w α r D a b : ℝ)
    (ha : 0 < a) (hb : 0 < b)
    (hw : w = a⁻¹ * b⁻¹ * s)
    (henergy : α ^ 2 * w ^ 2 ≤ r ^ 2 * (D / a) * (D / b)) :
    α ^ 2 * s ^ 2 ≤ r ^ 2 * D ^ 2 * (a * b) := by
  have hh := mul_le_mul_of_nonneg_right henergy (sq_nonneg (a * b))
  rw [hw] at hh
  convert hh using 1 <;> first | (with_reducible_and_instances rfl) | (field_simp)

theorem sparse_pair_coverage_size_bound {n : ℕ}
    (p : Fin n → ℕ) [∀ i, Fact (p i).Prime]
    (S : ∀ i, Finset (ZMod (p i)))
    (hS : ∀ i, (S i).Nonempty) (hSp : ∀ i, (S i).card < p i)
    (hp : ∀ i, (100 : ℝ) ≤ p i)
    (hlo : ∀ i, (1 / 3 : ℝ) ≤ residueDensity (S i))
    (hhi : ∀ i, residueDensity (S i) ≤ 2 / 3)
    (ε : ℝ) (hε : 0 ≤ ε) (hεsmall : ε ≤ 1 / 1000000)
    (hL1 : ∀ i, (p i : ℝ)⁻¹ * ∑ b, ‖normalizedResidueTransform (S i) b‖ ≤ ε ^ 2)
    (L : ℝ) (hL : 1 ≤ L) (hH : (∑ i, (p i : ℝ)⁻¹) ≤ L)
    (K : ℕ) (hK : 1000 * L ≤ K)
    {ι κ : Type*} (A : Finset ι) (B : Finset κ) (hA : A.Nonempty) (hB : B.Nonempty)
    (a : ι → ∀ i, ZMod (p i)) (b : κ → ∀ i, ZMod (p i))
    (ha : ∀ x ∈ A, ∀ i, a x i ∈ S i)
    (hb : ∀ y ∈ B, ∀ i, b y i ∈ Finset.univ \ S i)
    (α D c X T : ℝ) (hα : 0 ≤ α) (hD : 0 ≤ D) (hc : 0 ≤ c)
    (hX : 0 ≤ X) (hT : 0 ≤ T)
    (hEA : α * countingVectorNorm (lowModeVector (2 * K)
      (averagedCoordinates A (fun x => tensorPointCoordinates p S (a x)))) ^ 2 ≤ D / A.card)
    (hEB : α * countingVectorNorm (lowModeVector (2 * K)
      (averagedCoordinates B (fun y => tensorPointCoordinates p
        (fun i => Finset.univ \ S i) (b y)))) ^ 2 ≤ D / B.card)
    (hcover : c * (∏ i, sparseKernelUnitFactor (p i)
        (((largeTransformSpectrum (normalizedResidueTransform (S i))).card : ℝ) / p i)) * X ≤
      T * ∑ x ∈ A, ∑ y ∈ B, sparseSubsetWeight p S K (fun i => a x i - b y i)) :
    let U := ∏ i, sparseKernelUnitFactor (p i)
      (((largeTransformSpectrum (normalizedResidueTransform (S i))).card : ℝ) / p i)
    c * U * X * α ^ 2 ≤
      T * (2 * U * Real.exp (-(8 / 5) * ∑ i, (p i : ℝ)⁻¹)) * D ^ 2 := by
  intro U
  have hmA : 0 < (A.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hA
  have hmB : 0 < (B.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hB
  obtain ⟨hU, _, he⟩ := sparse_pair_average_energy_budget p S hS hSp hp hlo hhi
    ε hε hεsmall hL1 L hL hH K hK A B a b ha hb α (D / A.card) (D / B.card)
      hα (div_nonneg hD hmA.le) hEA hEB
  have hAsize := constant_mode_card_bound α D A.card _ hα hmA
    (lowMode_tensor_energy_one_le p S A hA a (2 * K)) hEA
  have hBsize := constant_mode_card_bound α D B.card _ hα hmB
    (lowMode_tensor_energy_one_le p (fun i => Finset.univ \ S i) B hB b (2 * K)) hEB
  have hsize : α ^ 2 * ((A.card : ℝ) * B.card) ≤ D ^ 2 := by
    have hh := mul_le_mul hAsize hBsize (mul_nonneg hα hmB.le) hD
    nlinarith only [hh]
  apply coverage_energy_size_bound _ c U X α T _ D ((A.card : ℝ) * B.card)
    (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sparseSubsetWeight_nonneg p S K _)
    hc hU.le hX hα hT (by positivity) hD hcover _ hsize
  exact normalized_pair_energy_bound _ _ _ _ _ _ _ hmA hmB rfl he

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_SparsePrimeFamilyCard
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Cardinality bound for the distinct selected primes -/
namespace Ostmann
open scoped Classical BigOperators

 theorem prime_family_injective {n : ℕ} (p : Fin n → ℕ) [∀ i, Fact (p i).Prime]
    (hc : Pairwise (fun i j => (p i).Coprime (p j))) : Function.Injective p := by
  intro i j he
  by_contra hij
  have hh := hc hij
  change (p i).Coprime (p j) at hh
  rw [he, Nat.coprime_self] at hh
  exact (Fact.out : (p j).Prime).ne_one hh

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_TailLogImbalance
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Logarithmic imbalance for the actual large summand tails -/

namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem EventuallyPrimeSumset.tail_logarithmic_imbalance_with_disjoint
    (hsize : PublishedSummandSizeBound) {A B : Set ℕ}
    (h : EventuallyPrimeSumset A B) (hA : A.Infinite) (hB : B.Infinite)
    (C : ℝ) (hM : MertensEstimate C) :
    ∃ N : ℕ, (∀ p, p.Prime → Disjoint (tailResidues A N p) (negTailResidues B N p)) ∧
      ∃ a : ℝ, 0 < a ∧ ∀ᶠ L : ℝ in atTop,
      ∀ hi : ℕ, (hi : ℝ) = Real.exp L →
      ∀ P : Finset ℕ, P ⊆ Nat.primesLE (tailCollisionCutoff L) →
      (∑ p ∈ P, |Real.log
        (((Finset.range p \ tailSupport A N p).card : ℝ) / (tailSupport A N p).card)| / p) ^ 2 ≤
          4 * tailDefectBudget a C L * primeReciprocalLogConstant C := by
  obtain ⟨N, hN⟩ := h.disjoint_tail_residues
  obtain ⟨a, ha, hlarge⟩ := exists_large_summand_tails hsize hA hB h
  refine ⟨N, hN, a, ha, ?_⟩
  filter_upwards [hlarge, eventual_tailCollisionCutoff N] with L hlarge hcut
  intro hi hhi P hP
  obtain ⟨hsa, hsb, _, _, _⟩ := hlarge hi hhi
  let Q := tailCollisionCutoff L
  let S := tailSupport A N
  let T := fun p => Finset.range p \ tailSupport A N p
  let μ := fun p => residueMass (summandTail A (summandTailCutoff L) hi)
    (fun _ => 1 / ((summandTail A (summandTailCutoff L) hi).card : ℝ)) p
  let ν := fun p => fiberMass (summandTail B (summandTailCutoff L) hi)
    (fun _ => 1 / ((summandTail B (summandTailCutoff L) hi).card : ℝ)) (negativeResidue p)
  have hprime (p) (hp : p ∈ Nat.primesLE Q) := Nat.prime_of_mem_primesLE hp
  have hS (p) (hp : p ∈ Nat.primesLE Q) : (S p).Nonempty :=
    tailSupport_nonempty hA N p (hprime p hp).pos
  have hT (p) (hp : p ∈ Nat.primesLE Q) : (T p).Nonempty :=
    tailSupport_complement_nonempty hB (hprime p hp).pos (hN p (hprime p hp))
  have hcard (p) : (S p).card + (T p).card = p := tailSupport_card_add_complement A N p
  have hb : (∑ p ∈ Nat.primesLE Q, Real.log (p : ℝ) *
      collisionDefect p (S p) (T p) (μ p) (ν p)) ≤ tailDefectBudget a C L := by
    apply uniform_tail_collision_bound hA hB N (summandTailCutoff L) hi a L C
      ha hcut.1 hcut.2.1 hhi hcut.2.2
      (fun p hp => hN p (hprime p hp))
    · simpa only [positiveSummandTail_card] using hsa
    · simpa only [negativeSummandTail_card] using hsb
    · exact hM.lower
  have hbP : (∑ p ∈ P, Real.log (p : ℝ) *
      collisionDefect p (S p) (T p) (μ p) (ν p)) ≤ tailDefectBudget a C L := by
    apply le_trans _ hb
    apply Finset.sum_le_sum_of_subset_of_nonneg hP
    intro p hp _
    exact mul_nonneg (Real.log_natCast_nonneg p)
      (collisionDefect_nonneg _ _ _ _ (hS p hp) (hT p hp) (hcard p).le)
  exact collision_logarithmic_imbalance hM Q P hP S T μ ν
    (fun p hp => hS p (hP hp)) (fun p hp => hT p (hP hp))
    (fun p _ => hcard p) (tailDefectBudget a C L) hbP

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Supply_TailSieveParameters
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual tail budget at the square-root sieve scale

The auxiliary collision estimate may be applied at `Y = X²`: its supports
are the same fixed infinite-tail residue sets. This choice keeps the endpoint
integral when `X` is integral and covers every prime up to `sqrt X`.
-/

namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem tailDefectBudget_doubled_exp (a C L : ℝ) :
    tailDefectBudget a C (2 * Real.exp L) =
      20 * L + (24 * Real.log 2 + 4 * C + 2 * Real.log 4 / a) := by
  unfold tailDefectBudget
  rw [Real.log_mul (by norm_num) (Real.exp_ne_zero _), Real.log_exp]
  ring

theorem eventual_sqrt_cutoff_le_tail :
    ∀ᶠ L : ℝ in atTop,
      ⌊Real.exp (Real.exp L / 2)⌋₊ ≤ tailCollisionCutoff (2 * Real.exp L) := by
  have hsmall := eventual_affine_log_le_rpow 5 (Real.log 2) (1 / 6) 1
    (by norm_num) (by norm_num) (by norm_num)
  simp only [Real.rpow_one] at hsmall
  have hlim : Tendsto (fun L : ℝ => 2 * Real.exp L) atTop atTop :=
    Real.tendsto_exp_atTop.const_mul_atTop (by norm_num)
  filter_upwards [hlim.eventually (eventual_tailCollisionCutoff 0),
    hlim.eventually hsmall] with L hcut hsmall
  have hb := tailCollisionCutoff_bounds (2 * Real.exp L) hcut.1 hcut.2.1
  have hQ : (0 : ℝ) < tailCollisionCutoff (2 * Real.exp L) := by
    exact_mod_cast hb.1
  have hlog : Real.exp L / 2 ≤ Real.log (tailCollisionCutoff (2 * Real.exp L) : ℝ) := by
    linarith [hb.2.2, Real.exp_pos L]
  have he := (Real.exp_le_exp.mpr hlog)
  rw [Real.exp_log hQ] at he
  exact (Nat.floor_le_floor he).trans_eq (Nat.floor_natCast _)

theorem logLogPrimeBand_subset_sqrt_cutoff (L : ℝ) (hL : 10 ≤ L) :
    logLogPrimeBand L ⊆ Nat.primesLE ⌊Real.exp (Real.exp L / 2)⌋₊ := by
  intro p hp
  obtain ⟨hpp, _, hlog⟩ := logLogPrimeBand_mem hp
  have hhalf : Real.exp ((9 / 10 : ℝ) * L) ≤ Real.exp L / 2 := by
    have htwo : (2 : ℝ) ≤ Real.exp ((1 / 10 : ℝ) * L) := by
      linarith [Real.add_one_le_exp ((1 / 10 : ℝ) * L)]
    have hm := mul_le_mul_of_nonneg_left htwo (Real.exp_nonneg ((9 / 10 : ℝ) * L))
    rw [← Real.exp_add] at hm
    have hid : (9 / 10 : ℝ) * L + (1 / 10 : ℝ) * L = L := by ring
    rw [hid] at hm
    linarith
  refine Nat.mem_primesLE.mpr ⟨Nat.le_floor ?_, hpp⟩
  exact (Real.log_le_iff_le_exp (by exact_mod_cast hpp.pos)).mp (hlog.trans hhalf)

theorem EventuallyPrimeSumset.sqrt_scale_logarithmic_imbalance_with_disjoint
    (hsize : PublishedSummandSizeBound) {A B : Set ℕ}
    (h : EventuallyPrimeSumset A B) (hA : A.Infinite) (hB : B.Infinite)
    (C : ℝ) (hM : MertensEstimate C) :
    ∃ N : ℕ, (∀ p, p.Prime → Disjoint (tailResidues A N p) (negTailResidues B N p)) ∧
      ∃ a : ℝ, 0 < a ∧ ∀ᶠ L : ℝ in atTop,
      ∀ X : ℕ, (X : ℝ) = Real.exp (Real.exp L) →
      ∀ P : Finset ℕ, P ⊆ Nat.primesLE ⌊Real.exp (Real.exp L / 2)⌋₊ →
      (∑ p ∈ P, |Real.log
        (((Finset.range p \ tailSupport A N p).card : ℝ) / (tailSupport A N p).card)| / p) ^ 2 ≤
        4 * (20 * L + (24 * Real.log 2 + 4 * C + 2 * Real.log 4 / a)) *
          primeReciprocalLogConstant C := by
  obtain ⟨N, hN, a, ha, hbudget⟩ := h.tail_logarithmic_imbalance_with_disjoint hsize hA hB C hM
  refine ⟨N, hN, a, ha, ?_⟩
  have hlim : Tendsto (fun L : ℝ => 2 * Real.exp L) atTop atTop :=
    Real.tendsto_exp_atTop.const_mul_atTop (by norm_num)
  filter_upwards [hlim.eventually hbudget, eventual_sqrt_cutoff_le_tail] with L hb hcut
  intro X hX P hP
  have hXsq : ((X ^ 2 : ℕ) : ℝ) = Real.exp (2 * Real.exp L) := by
    rw [Nat.cast_pow, hX, ← Real.exp_nat_mul]
    norm_num
  have hsub : P ⊆ Nat.primesLE (tailCollisionCutoff (2 * Real.exp L)) := by
    intro p hp
    exact Nat.mem_primesLE.mpr ⟨(Nat.le_of_mem_primesLE (hP hp)).trans hcut,
      Nat.prime_of_mem_primesLE (hP hp)⟩
  simpa only [tailDefectBudget_doubled_exp] using hb (X ^ 2) hXsq P hsub

theorem eventual_affine_square_budget (d e : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ W : ℝ, W ^ 2 ≤ d * L + e →
      W ≤ L ^ (3 / 4 : ℝ) / 16 := by
  filter_upwards [eventual_square_budget_le_three_quarters (|d| + |e|),
    eventually_ge_atTop (1 : ℝ)] with L hnum hL W hW
  apply hnum W
  have hd := mul_le_mul_of_nonneg_right (le_abs_self d) (by linarith : 0 ≤ L)
  have he := mul_le_mul_of_nonneg_left hL (abs_nonneg e)
  linarith [le_abs_self e]

/-- The exact `L^(3/4)/16` budget for the multiplier count
on the infinite-tail residue supports. -/
theorem EventuallyPrimeSumset.sqrt_scale_sieve_log_budget_with_disjoint
    (hsize : PublishedSummandSizeBound) {A B : Set ℕ}
    (h : EventuallyPrimeSumset A B) (hA : A.Infinite) (hB : B.Infinite)
    (C : ℝ) (hM : MertensEstimate C) :
    ∃ N : ℕ, (∀ p, p.Prime → Disjoint (tailResidues A N p) (negTailResidues B N p)) ∧
      ∀ᶠ L : ℝ in atTop,
      ∀ X : ℕ, (X : ℝ) = Real.exp (Real.exp L) →
      ∀ P : Finset ℕ, P ⊆ Nat.primesLE ⌊Real.exp (Real.exp L / 2)⌋₊ →
      (∑ p ∈ P, |Real.log
        (((Finset.range p \ tailSupport A N p).card : ℝ) / (tailSupport A N p).card)| / p) ≤
          L ^ (3 / 4 : ℝ) / 16 := by
  obtain ⟨N, hN, a, _, hb⟩ := h.sqrt_scale_logarithmic_imbalance_with_disjoint hsize hA hB C hM
  let d := 80 * primeReciprocalLogConstant C
  let e := 4 * (24 * Real.log 2 + 4 * C + 2 * Real.log 4 / a) *
    primeReciprocalLogConstant C
  refine ⟨N, hN, ?_⟩
  filter_upwards [hb, eventual_affine_square_budget d e] with L hb hnum X hX P hP
  apply hnum
  convert hb X hX P hP using 1
  all_goals try with_reducible_and_instances rfl
  dsimp [d, e]
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_SparseSubsetParameters
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform product and reciprocal bounds for small sparse-prime subsets -/

namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem primeProduct_le_exp_sum_log {ι : Type*} (T : Finset ι) (p : ι → ℕ)
    (hp : ∀ i ∈ T, 0 < p i) :
    ((∏ i ∈ T, p i : ℕ) : ℝ) = Real.exp (∑ i ∈ T, Real.log (p i)) := by
  rw [Nat.cast_prod, Real.exp_sum]
  apply Finset.prod_congr rfl
  intro i hi
  exact (Real.exp_log (by exact_mod_cast hp i hi)).symm

theorem eventual_sparse_subset_parameters (c : ℝ) (hc : 0 ≤ c) :
    ∀ᶠ L : ℝ in atTop, ∀ (n : ℕ) (p : Fin n → ℕ),
      (∀ i, p i ∈ logLogPrimeBand L) →
      ∀ T : Finset (Fin n), (T.card : ℝ) ≤ c * L →
      (∏ i ∈ T, p i) ≤ ⌊Real.exp (Real.exp L / 2)⌋₊ ∧
      (∑ q ∈ T.image p, (q : ℝ)⁻¹) ≤ 1 / 16 := by
  have hsmall := eventual_small_subset_reciprocal (1 / 20) c (by norm_num) hc
  have hgrowth := ((isLittleO_pow_exp_pos_mul_atTop 1
    (show (0 : ℝ) < 1 / 10 by norm_num)).const_mul_left c).bound
    (show (0 : ℝ) < 1 / 2 by norm_num)
  filter_upwards [hsmall, hgrowth, eventually_ge_atTop (1 : ℝ)] with L hsmall hgrowth hL
  intro n p hp T hT
  have hLp : 0 < L := by linarith
  have hlin : c * L ≤ (1 / 2 : ℝ) * Real.exp ((1 / 10 : ℝ) * L) := by
    simpa only [pow_one, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hc hLp.le),
      abs_of_pos (Real.exp_pos _)] using hgrowth
  have hsum : (∑ i ∈ T, Real.log (p i)) ≤ Real.exp L / 2 := by
    calc
      _ ≤ (T.card : ℝ) * Real.exp ((9 / 10 : ℝ) * L) := by
        have hh := Finset.sum_le_sum (s := T) (fun i _ => (logLogPrimeBand_mem (hp i)).2.2)
        simpa only [Finset.sum_const, nsmul_eq_mul] using hh
      _ ≤ (c * L) * Real.exp ((9 / 10 : ℝ) * L) :=
        mul_le_mul_of_nonneg_right hT (Real.exp_nonneg _)
      _ ≤ ((1 / 2 : ℝ) * Real.exp ((1 / 10 : ℝ) * L)) *
          Real.exp ((9 / 10 : ℝ) * L) :=
        mul_le_mul_of_nonneg_right hlin (Real.exp_nonneg _)
      _ = _ := by
        rw [mul_assoc, ← Real.exp_add]
        rw [show (1 / 10 : ℝ) * L + (9 / 10 : ℝ) * L = L by ring]
        ring
  refine ⟨Nat.le_floor ?_, ?_⟩
  · rw [primeProduct_le_exp_sum_log T p (fun i _ => (logLogPrimeBand_mem (hp i)).1.pos)]
    exact Real.exp_le_exp.mpr hsum
  · apply hsmall (T.image p)
    · have hcard : ((T.image p).card : ℝ) ≤ T.card := by
        exact_mod_cast Finset.card_image_le (s := T) (f := p)
      exact hcard.trans hT
    · intro q hq
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hq
      have hprime := (logLogPrimeBand_mem (hp i)).1
      refine ⟨hprime.pos, ?_⟩
      have he := Real.add_one_le_exp ((1 / 20 : ℝ) * L)
      linarith [(logLogPrimeBand_mem (hp i)).2.1]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SmoothPrimeMeanTest
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A fixed smooth test for the prime mean of the sparse weight -/

namespace Ostmann
open MeasureTheory
open scoped BigOperators

theorem primeMeanTest_compactSupport : HasCompactSupport primeMeanTest :=
  HasCompactSupport.intro isCompact_Icc primeMeanTest_zero_outside

theorem primeMeanTest_center : primeMeanTest (3 / 4) = 1 := by
  norm_num [primeMeanTest, logCellProfile, Real.smoothTransition.zero,
    Real.smoothTransition.one]

theorem primeMeanTest_integral_pos : 0 < ∫ t : ℝ, primeMeanTest t := by
  apply (primeMeanTest_contDiff (n := 0)).continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
    (x := (3 / 4 : ℝ)) primeMeanTest_compactSupport primeMeanTest_nonneg
  rw [primeMeanTest_center]
  norm_num

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_PrimeFamilyEnumeration
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The indexed prime coordinates of a finite selected set -/
namespace Ostmann
open scoped Classical BigOperators

 theorem primeFamilyEnumeration_mem (P : Finset ℕ) (i : Fin P.card) :
    primeFamilyEnumeration P i ∈ P := ((P.equivFin).symm i).property

 theorem primeFamilyEnumeration_injective (P : Finset ℕ) :
    Function.Injective (primeFamilyEnumeration P) := by
  intro i j hij
  apply (P.equivFin.symm).injective
  exact Subtype.ext hij

 theorem primeFamilyEnumeration_surjective (P : Finset ℕ) (q : ℕ) (hq : q ∈ P) :
    ∃ i, primeFamilyEnumeration P i = q := by
  refine ⟨P.equivFin ⟨q, hq⟩, ?_⟩
  simp [primeFamilyEnumeration]

 theorem primeFamilyEnumeration_image (P : Finset ℕ) :
    Finset.univ.image (primeFamilyEnumeration P) = P := by
  ext q
  constructor
  · rintro hq
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hq
    exact primeFamilyEnumeration_mem P i
  · intro hq
    obtain ⟨i, hi⟩ := primeFamilyEnumeration_surjective P q hq
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi⟩

 theorem primeFamilyEnumeration_sum (P : Finset ℕ) (f : ℕ → ℝ) :
    (∑ i, f (primeFamilyEnumeration P i)) = ∑ q ∈ P, f q := by
  calc
    _ = ∑ q ∈ Finset.univ.image (primeFamilyEnumeration P), f q := by
      rw [Finset.sum_image]
      exact fun i _ j _ hij => primeFamilyEnumeration_injective P hij
    _ = _ := by rw [primeFamilyEnumeration_image P]

theorem primeFamilyEnumeration_prod (P : Finset ℕ) :
    (∏ i, primeFamilyEnumeration P i) = ∏ q ∈ P, q := by
  calc
    _ = ∏ q ∈ Finset.univ.image (primeFamilyEnumeration P), q := by
      rw [Finset.prod_image]
      exact fun i _ j _ hij => primeFamilyEnumeration_injective P hij
    _ = _ := by rw [primeFamilyEnumeration_image P]

 theorem primeFamilyEnumeration_coprime (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    Pairwise (fun i j => (primeFamilyEnumeration P i).Coprime (primeFamilyEnumeration P j)) := by
  intro i j hij
  exact (Nat.coprime_primes (hP _ (primeFamilyEnumeration_mem P i))
    (hP _ (primeFamilyEnumeration_mem P j))).mpr
      (fun h => hij (primeFamilyEnumeration_injective P h))

theorem primeFamilyEnumeration_embedding {m : ℕ} (P : Finset ℕ)
    (p : Fin m → ℕ) (hinj : Function.Injective p) (hmem : ∀ i, p i ∈ P) (i : Fin m) :
    primeFamilyEnumeration P (finitePrimeFamilyEmbedding P p hinj hmem i) = p i := by
  change ((P.equivFin).symm (P.equivFin ⟨p i, hmem i⟩)).val = p i
  simp

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_TailSieveMasks
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The two complementary residue masks used by the integer-tail sieve -/
namespace Ostmann
open scoped Classical

theorem tailDensityMask_nonempty {A : Set ℕ} (hA : A.Infinite) (N p : ℕ) (hp : 0 < p) :
    (tailDensityMask A N p).Nonempty :=
  (tailSupport_nonempty hA N p hp).image _

theorem tailDensityMask_eq_tailResidues (A : Set ℕ) (N p : ℕ) [NeZero p] (_hp : 0 < p) :
    (tailDensityMask A N p : Set (ZMod p)) = tailResidues A N p := by
  ext x
  constructor
  · intro hx
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hx
    exact (Finset.mem_filter.mp hr).2
  · intro hx
    apply Finset.mem_image.mpr
    exact ⟨x.val, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (ZMod.val_lt x), by simpa⟩,
      ZMod.natCast_zmod_val x⟩

theorem negativeSummandTail_mem_mask_complement {A B : Set ℕ} (N lo hi p : ℕ) [NeZero p]
    (hp : 0 < p) (hdis : Disjoint (tailResidues A N p) (negTailResidues B N p))
    (hlo : N + p ≤ lo) {x : ℤ} (hx : x ∈ negativeSummandTail B lo hi) :
    (x : ZMod p) ∈ Finset.univ \ tailDensityMask A N p := by
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨hbB, hblo, _⟩ := (mem_summandTail B lo hi b).mp hb
  apply Finset.mem_sdiff.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  intro hm
  have hh : (-(b : ZMod p)) ∈ tailResidues A N p := by
    have he := tailDensityMask_eq_tailResidues A N p hp
    simp only [Int.cast_neg, Int.cast_natCast] at hm
    exact he ▸ hm
  exact Set.disjoint_left.mp hdis hh ⟨b, ⟨hbB, by omega⟩, rfl⟩

theorem tailDensityMask_complement_nonempty {A B : Set ℕ} (hB : B.Infinite)
    (N p : ℕ) [NeZero p] (hp : 0 < p)
    (hdis : Disjoint (tailResidues A N p) (negTailResidues B N p)) :
    (Finset.univ \ tailDensityMask A N p).Nonempty := by
  obtain ⟨x, hx, hlarge⟩ := hB.exists_gt (N + p)
  refine ⟨-(x : ZMod p), Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩⟩
  intro hm
  have hh : -(x : ZMod p) ∈ tailResidues A N p :=
    (tailDensityMask_eq_tailResidues A N p hp) ▸ hm
  exact Set.disjoint_left.mp hdis hh ⟨x, ⟨hx, hlarge⟩, rfl⟩

theorem tailDensityMask_card_lt {A B : Set ℕ} (hB : B.Infinite)
    (N p : ℕ) [NeZero p] (hp : 0 < p)
    (hdis : Disjoint (tailResidues A N p) (negTailResidues B N p)) :
    (tailDensityMask A N p).card < p := by
  have ht := Finset.card_pos.mpr (tailDensityMask_complement_nonempty hB N p hp hdis)
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, ZMod.card] at ht
  omega

theorem tailDensityMask_ratio {A : Set ℕ} (hA : A.Infinite) (N p : ℕ) (hp : 0 < p) :
    (p : ℝ) / (tailDensityMask A N p).card - 1 =
      ((Finset.range p \ tailSupport A N p).card : ℝ) / (tailSupport A N p).card := by
  rw [tailDensityMask_card]
  have hs : (tailSupport A N p).card ≠ 0 :=
    (Finset.card_pos.mpr (tailSupport_nonempty hA N p hp)).ne'
  have hsum := tailSupport_card_add_complement A N p
  have hsum' : ((tailSupport A N p).card : ℝ) +
      (Finset.range p \ tailSupport A N p).card = p := by exact_mod_cast hsum
  apply (eq_div_iff (by exact_mod_cast hs)).mpr
  field_simp
  linarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_IntegerIntervalCoordinates
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Identifying actual integer sets with the interval coordinates of the sieve -/
namespace Ostmann
open scoped Classical BigOperators

 theorem integerIntervalPoint_injective (J : ℤ) (M : ℕ) :
    Function.Injective (integerIntervalPoint J (M := M)) := by
  intro i j h
  apply Fin.ext
  dsimp [integerIntervalPoint] at h
  omega

 theorem integerIntervalIndices_image (A : Finset ℤ) (J : ℤ) (M : ℕ)
    (hA : ∀ a ∈ A, J ≤ a ∧ a < J + M) :
    (integerIntervalIndices A J M).image (integerIntervalPoint J) = A := by
  ext a
  constructor
  · rintro ha
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
    exact (Finset.mem_filter.mp hi).2
  · intro ha
    obtain ⟨hlo, hhi⟩ := hA a ha
    have hsub : 0 ≤ a - J := by omega
    have hcast : ((a - J).toNat : ℤ) = a - J := Int.toNat_of_nonneg hsub
    let i : Fin M := ⟨(a - J).toNat, by omega⟩
    have hi : integerIntervalPoint J i = a := by dsimp [integerIntervalPoint, i]; omega
    refine Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, hi⟩
    change integerIntervalPoint J i ∈ A
    rwa [hi]

 theorem integerIntervalIndices_card (A : Finset ℤ) (J : ℤ) (M : ℕ)
    (hA : ∀ a ∈ A, J ≤ a ∧ a < J + M) :
    (integerIntervalIndices A J M).card = A.card := by
  have hh := congrArg Finset.card (integerIntervalIndices_image A J M hA)
  rw [Finset.card_image_of_injective _ (integerIntervalPoint_injective J M)] at hh
  exact hh

 theorem integerIntervalIndices_average (A : Finset ℤ) (J : ℤ) (M : ℕ)
    (hA : ∀ a ∈ A, J ≤ a ∧ a < J + M) {α : Type*} (V : ℤ → α → ℂ) :
    averagedCoordinates A V = averagedCoordinates (integerIntervalIndices A J M)
      (fun i => V (J + (i.val : ℤ))) := by
  funext x
  unfold averagedCoordinates
  rw [integerIntervalIndices_card A J M hA]
  congr 1
  symm
  apply Finset.sum_bij (fun i _ => integerIntervalPoint J i)
  · intro i hi
    exact (Finset.mem_filter.mp hi).2
  · intro i hi j hj hij
    exact integerIntervalPoint_injective J M hij
  · intro a ha
    have ha' : a ∈ (integerIntervalIndices A J M).image (integerIntervalPoint J) := by
      rwa [integerIntervalIndices_image A J M hA]
    obtain ⟨i, hi, he⟩ := Finset.mem_image.mp ha'
    exact ⟨i, hi, he⟩
  · intro i hi
    rfl

 theorem restricted_integer_energy_budget (ls : PublishedAdditiveLargeSieve)
    {n m M Q : ℕ} (p : Fin n → ℕ) [∀ i, Fact (p i).Prime]
    (hc : Pairwise (fun i j => (p i).Coprime (p j)))
    (S : ∀ i, Finset (ZMod (p i))) (hS : ∀ i, (S i).Nonempty)
    (κ : ℕ → ℝ) (hκ : ∀ q ∈ Finset.univ.image p, 0 < κ q)
    (hκS : ∀ i, κ (p i) = (p i : ℝ) / (S i).card - 1)
    (hQ : 1 ≤ Q) (hM : 1 ≤ M) (hcover : ∀ q, q.Prime → q ≤ Q → ∃ i, p i = q)
    (A : Finset ℤ) (hA : A.Nonempty) (J : ℤ)
    (hArange : ∀ a ∈ A, J ≤ a ∧ a < J + M)
    (ha : ∀ x ∈ A, ∀ i, (x : ZMod (p i)) ∈ S i)
    (e : Fin m ↪ Fin n) (K : ℕ)
    (hprod : ∀ T : Finset (Fin m), T.card ≤ K → (∏ i ∈ T, p (e i)) ≤ Q)
    (hsmall : ∀ T : Finset (Fin m), T.card ≤ K →
      (∑ q ∈ T.image (fun i => p (e i)), (q : ℝ)⁻¹) ≤ 1 / 16)
    (B : ℝ) (hB : 0 < B)
    (hP : (∑ q ∈ Finset.univ.image p, |Real.log (κ q)| / q) ≤ B / 16) :
    ((Q : ℝ) / 16 * Real.exp (-B)) *
      countingVectorNorm (lowModeVector K (averagedCoordinates A
        (fun x => tensorPointCoordinates (fun i => p (e i)) (fun i => S (e i))
          (fun i => (x : ZMod (p (e i))))))) ^ 2 ≤
      ((M : ℝ) + (Q : ℝ) ^ 2) / A.card := by
  let I := integerIntervalIndices A J M
  have hcard : I.card = A.card := integerIntervalIndices_card A J M hArange
  have hI : I.Nonempty := Finset.card_pos.mp (by rw [hcard]; exact Finset.card_pos.mpr hA)
  have hh := restricted_lowMode_energy_budget ls p hc S hS κ hκ hκS hQ hM hcover I hI J
    (fun x hx i => ha _ (Finset.mem_filter.mp hx).2 i) e K hprod hsmall B hB hP
  rw [hcard] at hh
  have havg := integerIntervalIndices_average A J M hArange
    (fun x => tensorPointCoordinates (fun i => p (e i)) (fun i => S (e i))
      (fun i => (x : ZMod (p (e i)))))
  rw [← havg] at hh
  exact hh

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Supply_IntegerSparseSieve
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Applying both sides of the sparse contraction to integer intervals -/
namespace Ostmann
open scoped Classical BigOperators

theorem integer_complementary_energy_budgets (ls : PublishedAdditiveLargeSieve)
    {n m M Q : ℕ} (p : Fin n → ℕ) [∀ i, Fact (p i).Prime]
    (hc : Pairwise (fun i j => (p i).Coprime (p j)))
    (S : ∀ i, Finset (ZMod (p i))) (hS : ∀ i, (S i).Nonempty)
    (hSp : ∀ i, (S i).card < p i)
    (κ : ℕ → ℝ) (hκ : ∀ q ∈ Finset.univ.image p, 0 < κ q)
    (hκS : ∀ i, κ (p i) = (p i : ℝ) / (S i).card - 1)
    (hQ : 1 ≤ Q) (hM : 1 ≤ M) (hcover : ∀ q, q.Prime → q ≤ Q → ∃ i, p i = q)
    (A B : Finset ℤ) (hA : A.Nonempty) (hB : B.Nonempty) (J J' : ℤ)
    (hArange : ∀ a ∈ A, J ≤ a ∧ a < J + M)
    (hBrange : ∀ b ∈ B, J' ≤ b ∧ b < J' + M)
    (ha : ∀ x ∈ A, ∀ i, (x : ZMod (p i)) ∈ S i)
    (hb : ∀ y ∈ B, ∀ i, (y : ZMod (p i)) ∈ Finset.univ \ S i)
    (e : Fin m ↪ Fin n) (K : ℕ)
    (hprod : ∀ T : Finset (Fin m), T.card ≤ K → (∏ i ∈ T, p (e i)) ≤ Q)
    (hsmall : ∀ T : Finset (Fin m), T.card ≤ K →
      (∑ q ∈ T.image (fun i => p (e i)), (q : ℝ)⁻¹) ≤ 1 / 16)
    (R : ℝ) (hR : 0 < R)
    (hP : (∑ q ∈ Finset.univ.image p, |Real.log (κ q)| / q) ≤ R / 16) :
    let α := (Q : ℝ) / 16 * Real.exp (-R)
    let D := (M : ℝ) + (Q : ℝ) ^ 2
    (α * countingVectorNorm (lowModeVector K (averagedCoordinates A
        (fun x => tensorPointCoordinates (fun i => p (e i)) (fun i => S (e i))
          (fun i => (x : ZMod (p (e i))))))) ^ 2 ≤ D / A.card) ∧
    (α * countingVectorNorm (lowModeVector K (averagedCoordinates B
        (fun x => tensorPointCoordinates (fun i => p (e i))
          (fun i => Finset.univ \ S (e i))
          (fun i => (x : ZMod (p (e i))))))) ^ 2 ≤ D / B.card) := by
  constructor
  · exact restricted_integer_energy_budget ls p hc S hS κ hκ hκS hQ hM hcover
      A hA J hArange ha e K hprod hsmall R hR hP
  · have hSc (i : Fin n) : (Finset.univ \ S i).Nonempty := by
      apply Finset.card_pos.mp
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, ZMod.card]
      exact Nat.sub_pos_of_lt (hSp i)
    have hκSc (i : Fin n) : (κ (p i))⁻¹ = (p i : ℝ) / (Finset.univ \ S i).card - 1 := by
      rw [hκS]
      exact complementary_field_card_ratio (S i) (hS i) (hSp i)
    have hPinv : (∑ q ∈ Finset.univ.image p, |Real.log (κ q)⁻¹| / q) ≤ R / 16 := by
      simpa only [Real.log_inv, abs_neg] using hP
    exact restricted_integer_energy_budget ls p hc (fun i => Finset.univ \ S i)
      hSc (fun q => (κ q)⁻¹) (fun q hq => inv_pos.mpr (hκ q hq))
      hκSc hQ hM hcover B hB J' hBrange hb e K hprod hsmall R hR hPinv

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Supply_TailSieveEnergy
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The sieve budget on the two actual summand tails -/
namespace Ostmann
open scoped Classical BigOperators

theorem tail_sieve_energy_budgets (ls : PublishedAdditiveLargeSieve)
    {A B : Set ℕ} (hA : A.Infinite) (hB : B.Infinite) (N lo X Q : ℕ)
    (hdis : ∀ q, q.Prime → Disjoint (tailResidues A N q) (negTailResidues B N q))
    (hlo : N + Q ≤ lo) (hQ : 1 ≤ Q)
    (hAt : (positiveSummandTail A lo X).Nonempty)
    (hBt : (negativeSummandTail B lo X).Nonempty)
    {n m : ℕ} (p : Fin n → ℕ) [∀ i, Fact (p i).Prime]
    (hc : Pairwise (fun i j => (p i).Coprime (p j))) (hpQ : ∀ i, p i ≤ Q)
    (hcover : ∀ q, q.Prime → q ≤ Q → ∃ i, p i = q)
    (e : Fin m ↪ Fin n) (K : ℕ)
    (hprod : ∀ T : Finset (Fin m), T.card ≤ K → (∏ i ∈ T, p (e i)) ≤ Q)
    (hsmall : ∀ T : Finset (Fin m), T.card ≤ K →
      (∑ q ∈ T.image (fun i => p (e i)), (q : ℝ)⁻¹) ≤ 1 / 16)
    (R : ℝ) (hR : 0 < R)
    (hP : (∑ q ∈ Finset.univ.image p,
      |Real.log (((Finset.range q \ tailSupport A N q).card : ℝ) /
        (tailSupport A N q).card)| / q) ≤ R / 16) :
    let S := fun i => tailDensityMask A N (p (e i))
    let α := (Q : ℝ) / 16 * Real.exp (-R)
    let D := (X + 1 : ℝ) + (Q : ℝ) ^ 2
    (α * countingVectorNorm (lowModeVector K
      (averagedCoordinates (positiveSummandTail A lo X)
        (fun x => tensorPointCoordinates (fun i => p (e i)) S
          (fun i => (x : ZMod (p (e i))))))) ^ 2 ≤ D / (summandTail A lo X).card) ∧
    (α * countingVectorNorm (lowModeVector K
      (averagedCoordinates (negativeSummandTail B lo X)
        (fun x => tensorPointCoordinates (fun i => p (e i)) (fun i => Finset.univ \ S i)
          (fun i => (x : ZMod (p (e i))))))) ^ 2 ≤ D / (summandTail B lo X).card) := by
  have hp (i : Fin n) : (p i).Prime := Fact.out
  have hk : ∀ q ∈ Finset.univ.image p,
      0 < ((Finset.range q \ tailSupport A N q).card : ℝ) / (tailSupport A N q).card := by
    intro q hq
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hq
    have ht := Finset.card_pos.mpr
      (tailSupport_complement_nonempty hB (hp i).pos (hdis _ (hp i)))
    have hs := Finset.card_pos.mpr (tailSupport_nonempty hA N _ (hp i).pos)
    exact div_pos (by exact_mod_cast ht) (by exact_mod_cast hs)
  have hb := integer_complementary_energy_budgets ls p hc
    (fun i => tailDensityMask A N (p i))
    (fun i => tailDensityMask_nonempty hA N _ (hp i).pos)
    (fun i => tailDensityMask_card_lt hB N _ (hp i).pos (hdis _ (hp i)))
    (fun q => ((Finset.range q \ tailSupport A N q).card : ℝ) / (tailSupport A N q).card)
    hk (fun i => (tailDensityMask_ratio hA N _ (hp i).pos).symm)
    hQ (show 1 ≤ X + 1 by omega) hcover
    (positiveSummandTail A lo X) (negativeSummandTail B lo X) hAt hBt 0 (-(X : ℤ))
    (fun a ha => ?_) (fun b hb => ?_)
    (fun a ha i => positiveSummandTail_mem_mask A N lo X _ (hp i).pos (by have := hpQ i; omega) ha)
    (fun b hb i => negativeSummandTail_mem_mask_complement N lo X _ (hp i).pos
      (hdis _ (hp i)) (by have := hpQ i; omega) hb)
    e K hprod hsmall R hR hP
  · simpa only [positiveSummandTail_card, negativeSummandTail_card, Nat.cast_add,
      Nat.cast_one] using hb
  · have hh := positiveSummandTail_bounds A lo X ha
    push_cast
    omega
  · have hh := negativeSummandTail_bounds B lo X hb
    push_cast
    omega

theorem summandTail_pair_sum (A B : Set ℕ) (lo X : ℕ) (W : ℤ → ℝ) :
    (∑ a ∈ positiveSummandTail A lo X, ∑ b ∈ negativeSummandTail B lo X, W (a - b)) =
      ∑ a ∈ summandTail A lo X, ∑ b ∈ summandTail B lo X, W ((a + b : ℕ) : ℤ) := by
  unfold positiveSummandTail negativeSummandTail
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro a ha
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro b hb
      congr 1
      push_cast
      ring
    · intro a ha b hb hab
      exact_mod_cast neg_injective hab
  · intro a ha b hb hab
    change (a : ℤ) = (b : ℤ) at hab
    exact_mod_cast hab

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_TailCoordinateTransport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Equality transport for dependent prime-coordinate energies -/
namespace Ostmann
open scoped Classical

theorem tail_low_energy_congr {n : ℕ} (p q : Fin n → ℕ)
    [∀ i, NeZero (p i)] [∀ i, NeZero (q i)] (hpq : p = q)
    (A : Set ℕ) (N K : ℕ) (E : Finset ℤ) :
    countingVectorNorm (lowModeVector K (averagedCoordinates E
      (fun x => tensorPointCoordinates p (fun i => tailDensityMask A N (p i))
        (fun i => (x : ZMod (p i)))))) ^ 2 =
    countingVectorNorm (lowModeVector K (averagedCoordinates E
      (fun x => tensorPointCoordinates q (fun i => tailDensityMask A N (q i))
        (fun i => (x : ZMod (q i)))))) ^ 2 := by
  cases hpq
  rfl

theorem tail_complement_low_energy_congr {n : ℕ} (p q : Fin n → ℕ)
    [∀ i, NeZero (p i)] [∀ i, NeZero (q i)] (hpq : p = q)
    (A : Set ℕ) (N K : ℕ) (E : Finset ℤ) :
    countingVectorNorm (lowModeVector K (averagedCoordinates E
      (fun x => tensorPointCoordinates p (fun i => Finset.univ \ tailDensityMask A N (p i))
        (fun i => (x : ZMod (p i)))))) ^ 2 =
    countingVectorNorm (lowModeVector K (averagedCoordinates E
      (fun x => tensorPointCoordinates q (fun i => Finset.univ \ tailDensityMask A N (q i))
        (fun i => (x : ZMod (q i)))))) ^ 2 := by
  cases hpq
  rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Supply_EnumeratedTailSieveEnergy
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Restrict the full-prime sieve to any indexed sparse prime family -/
namespace Ostmann
open scoped Classical BigOperators

theorem enumerated_tail_sieve_energy_budgets (ls : PublishedAdditiveLargeSieve)
    {A B : Set ℕ} (hA : A.Infinite) (hB : B.Infinite) (N lo X Q : ℕ)
    (hdis : ∀ q, q.Prime → Disjoint (tailResidues A N q) (negTailResidues B N q))
    (hcut : N + Q ≤ lo) (hQ : 1 ≤ Q)
    (hAt : (positiveSummandTail A lo X).Nonempty)
    (hBt : (negativeSummandTail B lo X).Nonempty)
    {n : ℕ} (p : Fin n → ℕ) [∀ i, Fact (p i).Prime]
    (hc : Pairwise (fun i j => (p i).Coprime (p j))) (hpQ : ∀ i, p i ≤ Q)
    (K : ℕ)
    (hprod : ∀ T : Finset (Fin n), T.card ≤ K → (∏ i ∈ T, p i) ≤ Q)
    (hsmall : ∀ T : Finset (Fin n), T.card ≤ K →
      (∑ q ∈ T.image p, (q : ℝ)⁻¹) ≤ 1 / 16)
    (R : ℝ) (hR : 0 < R)
    (hP : (∑ q ∈ Nat.primesLE Q,
      |Real.log (((Finset.range q \ tailSupport A N q).card : ℝ) /
        (tailSupport A N q).card)| / q) ≤ R / 16) :
    let S := fun i => tailDensityMask A N (p i)
    let α := (Q : ℝ) / 16 * Real.exp (-R)
    let D := (X + 1 : ℝ) + (Q : ℝ) ^ 2
    let vA := averagedCoordinates (positiveSummandTail A lo X)
      (fun x => tensorPointCoordinates p S (fun i => (x : ZMod (p i))))
    let vB := averagedCoordinates (negativeSummandTail B lo X)
      (fun x => tensorPointCoordinates p (fun i => Finset.univ \ S i)
        (fun i => (x : ZMod (p i))))
    (α * countingVectorNorm (lowModeVector K vA) ^ 2 ≤ D / (summandTail A lo X).card) ∧
    (α * countingVectorNorm (lowModeVector K vB) ^ 2 ≤ D / (summandTail B lo X).card) := by
  let P := Nat.primesLE Q
  let q := primeFamilyEnumeration P
  have hqprime (i : Fin P.card) : (q i).Prime :=
    Nat.prime_of_mem_primesLE (primeFamilyEnumeration_mem P i)
  let (i : Fin P.card) : Fact (q i).Prime := ⟨hqprime i⟩
  have hpmem (i : Fin n) : p i ∈ P := Nat.mem_primesLE.mpr ⟨hpQ i, Fact.out⟩
  let e := finitePrimeFamilyEmbedding P p (prime_family_injective p hc) hpmem
  have he (i : Fin n) : q (e i) = p i :=
    primeFamilyEnumeration_embedding P p (prime_family_injective p hc) hpmem i
  have heprod (T : Finset (Fin n)) (hT : T.card ≤ K) : (∏ i ∈ T, q (e i)) ≤ Q := by
    simpa only [he] using hprod T hT
  have hesmall (T : Finset (Fin n)) (hT : T.card ≤ K) :
      (∑ r ∈ T.image (fun i => q (e i)), (r : ℝ)⁻¹) ≤ 1 / 16 := by
    simpa only [he] using hsmall T hT
  have hPq : (∑ r ∈ Finset.univ.image q,
      |Real.log (((Finset.range r \ tailSupport A N r).card : ℝ) /
        (tailSupport A N r).card)| / r) ≤ R / 16 := by
    simpa only [q, primeFamilyEnumeration_image] using hP
  have hb := tail_sieve_energy_budgets ls hA hB N lo X Q hdis hcut hQ hAt hBt q
    (primeFamilyEnumeration_coprime P (fun r hr => Nat.prime_of_mem_primesLE hr))
    (fun i => Nat.le_of_mem_primesLE (primeFamilyEnumeration_mem P i))
    (fun r hr hle => primeFamilyEnumeration_surjective P r (Nat.mem_primesLE.mpr ⟨hle, hr⟩))
    e K heprod hesmall R hR hPq
  have hpe : (fun i => q (e i)) = p := funext he
  have hea := tail_low_energy_congr (fun i => q (e i)) p hpe A N K (positiveSummandTail A lo X)
  have heb := tail_complement_low_energy_congr (fun i => q (e i)) p hpe A N K (negativeSummandTail B lo X)
  dsimp only at hb
  rw [hea, heb] at hb
  exact hb

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Supply_TailSparsePairSum
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The natural-sum and reflected-integer forms of the same sparse weight -/
namespace Ostmann
open scoped Classical BigOperators

theorem summandTail_sparse_pair_sum {n : ℕ} (p : Fin n → ℕ) [∀ i, NeZero (p i)]
    (S : ∀ i, Finset (ZMod (p i))) (K : ℕ) (A B : Set ℕ) (lo X : ℕ) :
    (∑ a ∈ positiveSummandTail A lo X, ∑ b ∈ negativeSummandTail B lo X,
      sparseSubsetWeight p S K (fun i => (a : ZMod (p i)) - (b : ZMod (p i)))) =
    ∑ a ∈ summandTail A lo X, ∑ b ∈ summandTail B lo X,
      sparseSubsetWeight p S K (fun i => ((a + b : ℕ) : ZMod (p i))) := by
  have hh := summandTail_pair_sum A B lo X
    (fun z => sparseSubsetWeight p S K (fun i => (z : ZMod (p i))))
  simpa only [Int.cast_sub, Int.cast_natCast] using hh

theorem summandTail_sparse_coverage {n : ℕ} (p : Fin n → ℕ) [∀ i, NeZero (p i)]
    (S : ∀ i, Finset (ZMod (p i))) (K : ℕ) (A B : Set ℕ) (lo X : ℕ) (c L : ℝ)
    (hlog : Real.log (X : ℝ) = L)
    (hc : c ≤ Real.log X * ∑ a ∈ summandTail A lo X, ∑ b ∈ summandTail B lo X,
      sparseSubsetWeight p S K (fun i => ((a + b : ℕ) : ZMod (p i)))) :
    c ≤ L * ∑ a ∈ positiveSummandTail A lo X, ∑ b ∈ negativeSummandTail B lo X,
      sparseSubsetWeight p S K (fun i => (a : ZMod (p i)) - (b : ZMod (p i))) := by
  have he := congrArg (fun x : ℝ => L * x) (summandTail_sparse_pair_sum p S K A B lo X)
  rw [hlog] at hc
  exact hc.trans_eq he.symm

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_SparseTailSieveContradiction
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The concrete sparse contradiction on the original summand tails -/
namespace Ostmann
open scoped Classical BigOperators

theorem sparse_tail_sieve_contradiction (ls : PublishedAdditiveLargeSieve)
    {A B : Set ℕ} (hA : A.Infinite) (hB : B.Infinite) (N lo X Q : ℕ)
    (hdis : ∀ q, q.Prime → Disjoint (tailResidues A N q) (negTailResidues B N q))
    (hcut : N + Q ≤ lo) (hQ : 1 ≤ Q)
    (hAt : (positiveSummandTail A lo X).Nonempty)
    (hBt : (negativeSummandTail B lo X).Nonempty)
    {n : ℕ} (p : Fin n → ℕ) [∀ i, Fact (p i).Prime]
    (hc : Pairwise (fun i j => (p i).Coprime (p j))) (hpQ : ∀ i, p i ≤ Q)
    (hp100 : ∀ i, (100 : ℝ) ≤ p i)
    (hlo : ∀ i, (1 / 3 : ℝ) ≤ residueDensity (tailDensityMask A N (p i)))
    (hhi : ∀ i, residueDensity (tailDensityMask A N (p i)) ≤ 2 / 3)
    (ε : ℝ) (hε : 0 ≤ ε) (hεsmall : ε ≤ 1 / 1000000)
    (hL1 : ∀ i, (p i : ℝ)⁻¹ * ∑ b,
      ‖normalizedResidueTransform (tailDensityMask A N (p i)) b‖ ≤ ε ^ 2)
    (L : ℝ) (hL : 1 ≤ L) (hH : (∑ i, (p i : ℝ)⁻¹) ≤ L)
    (hHlow : (17 / 25) * L ≤ ∑ i, (p i : ℝ)⁻¹)
    (K : ℕ) (hK : 1000 * L ≤ K)
    (hprod : ∀ T : Finset (Fin n), T.card ≤ 2 * K → (∏ i ∈ T, p i) ≤ Q)
    (hsmall : ∀ T : Finset (Fin n), T.card ≤ 2 * K →
      (∑ q ∈ T.image p, (q : ℝ)⁻¹) ≤ 1 / 16)
    (hP : (∑ q ∈ Nat.primesLE Q,
      |Real.log (((Finset.range q \ tailSupport A N q).card : ℝ) /
        (tailSupport A N q).card)| / q) ≤ L ^ (3 / 4 : ℝ) / 16)
    (c : ℝ) (hcpos : 0 < c)
    (hcover : c * (∏ i, sparseKernelUnitFactor (p i)
        (((largeTransformSpectrum (normalizedResidueTransform (tailDensityMask A N (p i)))).card : ℝ) / p i)) * X ≤
      Real.log X * ∑ a ∈ summandTail A lo X, ∑ b ∈ summandTail B lo X,
        sparseSubsetWeight p (fun i => tailDensityMask A N (p i)) K
          (fun i => ((a + b : ℕ) : ZMod (p i))))
    (hlogX : Real.log (X : ℝ) = Real.exp L) (hX : 0 < (X : ℝ))
    (hQsize : (X : ℝ) / 4 ≤ (Q : ℝ) ^ 2)
    (hDsize : ((X : ℝ) + 1) + (Q : ℝ) ^ 2 ≤ 3 * X)
    (hmargin : 18432 * Real.exp (L - (8 / 5) * ((17 / 25) * L) +
      2 * L ^ (3 / 4 : ℝ)) < c) : False := by
  have hb := enumerated_tail_sieve_energy_budgets ls hA hB N lo X Q hdis hcut hQ
    hAt hBt p hc hpQ (2 * K) hprod hsmall (L ^ (3 / 4 : ℝ))
    (Real.rpow_pos_of_pos (by linarith) _) hP
  let S := fun i => tailDensityMask A N (p i)
  have hS (i : Fin n) : (S i).Nonempty := tailDensityMask_nonempty hA N _ (Fact.out : (p i).Prime).pos
  have hSp (i : Fin n) : (S i).card < p i :=
    tailDensityMask_card_lt hB N _ (Fact.out : (p i).Prime).pos (hdis _ Fact.out)
  have hcover' := summandTail_sparse_coverage p S K A B lo X _ (Real.exp L) hlogX hcover
  have hfinal := sparse_pair_coverage_size_bound p S hS hSp hp100 hlo hhi ε hε hεsmall hL1
    L hL hH K hK (positiveSummandTail A lo X) (negativeSummandTail B lo X) hAt hBt
    (fun x i => (x : ZMod (p i))) (fun x i => (x : ZMod (p i)))
    (fun x hx i => positiveSummandTail_mem_mask A N lo X _ (Fact.out : (p i).Prime).pos
      (by have := hpQ i; omega) hx)
    (fun x hx i => negativeSummandTail_mem_mask_complement N lo X _ (Fact.out : (p i).Prime).pos
      (hdis _ Fact.out) (by have := hpQ i; omega) hx)
    ((Q : ℝ) / 16 * Real.exp (-(L ^ (3 / 4 : ℝ))))
    (((X : ℝ) + 1) + (Q : ℝ) ^ 2) c X (Real.exp L)
    (by positivity) (by positivity) hcpos.le hX.le (Real.exp_nonneg _) ?_ ?_ hcover'
  · apply sparse_sieve_numerical_impossible c _ X Q (((X : ℝ) + 1) + (Q : ℝ) ^ 2)
      (∑ i, (p i : ℝ)⁻¹) L hcpos ?_ hX (by positivity) hQsize hDsize hHlow hmargin hfinal
    exact (sparse_finite_contraction p S hS hSp hp100 hlo hhi ε hε hεsmall hL1 L hL hH K hK).1
  · simpa only [positiveSummandTail_card, S] using hb.1
  · simpa only [negativeSummandTail_card, S] using hb.2

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_SqrtSieveGeometry
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Size and endpoint bounds at the rounded square-root cutoff -/
namespace Ostmann
open Filter

theorem sqrt_sieve_geometry (N : ℕ) (T : ℝ) (hT : 3 * ((N : ℝ) + 3) ≤ T) :
    let Q := ⌊Real.exp (T / 2)⌋₊
    1 ≤ Q ∧ Real.exp T / 4 ≤ (Q : ℝ) ^ 2 ∧
      (Real.exp T + 1) + (Q : ℝ) ^ 2 ≤ 3 * Real.exp T ∧
      N + Q ≤ summandTailCutoff T := by
  intro Q
  have hN0 : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
  have hT0 : 0 ≤ T := by linarith
  have hs : 2 ≤ Real.exp (T / 2) := by linarith [Real.add_one_le_exp (T / 2)]
  have hQ : 1 ≤ Q := (Nat.one_le_floor_iff _).mpr (by linarith)
  have hQu : (Q : ℝ) ≤ Real.exp (T / 2) := Nat.floor_le (Real.exp_nonneg _)
  have hQl : Real.exp (T / 2) / 2 ≤ (Q : ℝ) := by
    have hh := Nat.sub_one_lt_floor (Real.exp (T / 2))
    change Real.exp (T / 2) - 1 < (Q : ℝ) at hh
    linarith
  have heq : Real.exp (T / 2) ^ 2 = Real.exp T := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hQpos : 0 ≤ (Q : ℝ) := Nat.cast_nonneg Q
  have hepos := Real.exp_nonneg (T / 2)
  have hsqU : (Q : ℝ) ^ 2 ≤ Real.exp T := by nlinarith only [hQu, hQpos, hepos, heq]
  have hsqL : Real.exp T / 4 ≤ (Q : ℝ) ^ 2 := by nlinarith only [hQl, hQpos, hepos, heq]
  refine ⟨hQ, hsqL, ?_, ?_⟩
  · linarith [Real.one_le_exp hT0]
  · have hN : (N : ℝ) + 3 ≤ Real.exp (2 * T / 5) := by
      linarith [Real.add_one_le_exp (2 * T / 5)]
    have hm := mul_le_mul_of_nonneg_left hN (Real.exp_nonneg (T / 2))
    have hid : Real.exp (T / 2) * Real.exp (2 * T / 5) = Real.exp (9 * T / 10) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hid] at hm
    have hh := mul_nonneg (sub_nonneg.mpr (hs.trans' (by norm_num : (1 : ℝ) ≤ 2)))
      (show 0 ≤ (N : ℝ) + 2 by positivity)
    have hf := Nat.sub_one_lt_floor (Real.exp (9 * T / 10))
    change Real.exp (9 * T / 10) - 1 < (summandTailCutoff T : ℝ) at hf
    have hfinal : (N : ℝ) + Q ≤ (summandTailCutoff T : ℝ) := by
      nlinarith only [hm, hh, hf, hQu]
    exact_mod_cast hfinal

theorem eventual_sqrt_sieve_geometry (N : ℕ) :
    ∀ᶠ L : ℝ in atTop,
      let Q := ⌊Real.exp (Real.exp L / 2)⌋₊
      1 ≤ Q ∧ Real.exp (Real.exp L) / 4 ≤ (Q : ℝ) ^ 2 ∧
        (Real.exp (Real.exp L) + 1) + (Q : ℝ) ^ 2 ≤ 3 * Real.exp (Real.exp L) ∧
        N + Q ≤ summandTailCutoff (Real.exp L) := by
  filter_upwards [Real.tendsto_exp_atTop.eventually_ge_atTop (3 * ((N : ℝ) + 3))] with L hL
  exact sqrt_sieve_geometry N (Real.exp L) hL

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_SparseTailMassBound
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Sparse balanced tail spectra have small harmonic mass

This is the contradiction step of Proposition 5.1, using the original
nonnegative sparse weight and the actual positive and reflected summand tails.
-/
namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem EventuallyPrimeSumset.sparse_tail_mass_bound
    (ls : PublishedAdditiveLargeSieve) (hsize : PublishedSummandSizeBound)
    {A B : Set ℕ} (h : EventuallyPrimeSumset A B) (hA : A.Infinite) (hB : B.Infinite)
    (CM : ℝ) (hM : MertensEstimate CM)
    (Z : ∀ χ, ComplexZeroEnumeration χ) (hD : PublishedComplexZeroDensity Z)
    (hR : PublishedComplexZeroRegion Z) (P : PublishedSmoothExplicitFormula Z)
    (hPNT : PublishedSmoothPrincipalPNT) :
    ∃ N : ℕ, (∀ q, q.Prime → Disjoint (tailResidues A N q) (negTailResidues B N q)) ∧
      ∀ᶠ L : ℝ in atTop, ∃ exception : Option PrimitiveComplexCharacter,
        ∀ X : ℕ, (X : ℝ) = Real.exp (Real.exp L) →
        ∀ (n : ℕ) (p : Fin n → ℕ) [∀ i, Fact (p i).Prime] [NeZero (∏ i, p i)],
          Pairwise (fun i j => (p i).Coprime (p j)) →
          (∀ i, p i ∈ logLogPrimeBand L) →
          (∀ i, (1 / 3 : ℝ) ≤ residueDensity (tailDensityMask A N (p i))) →
          (∀ i, residueDensity (tailDensityMask A N (p i)) ≤ 2 / 3) →
          ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 / 1000000 →
          (∀ i, (p i : ℝ)⁻¹ * ∑ b,
            ‖normalizedResidueTransform (tailDensityMask A N (p i)) b‖ ≤ ε ^ 2) →
          (∑ i, (p i : ℝ)⁻¹) ≤ L →
          (∀ ρ, exception = some ρ → ¬ ρ.modulus ∣ ∏ i, p i) →
          (∑ i, (p i : ℝ)⁻¹) < (17 / 25 : ℝ) * L := by
  obtain ⟨N, hN, hsieve⟩ := h.sqrt_scale_sieve_log_budget_with_disjoint hsize hA hB CM hM
  obtain ⟨a, ha, hlarge⟩ := exists_large_summand_tails hsize hA hB h
  refine ⟨N, hN, ?_⟩
  filter_upwards [hsieve, eventual_sqrt_sieve_geometry N,
    eventual_sparse_subset_parameters 2002 (by norm_num),
    Real.tendsto_exp_atTop.eventually hlarge,
    h.sparse_tail_coverage hsize hA hB Z hD hR P hPNT 1000 (by norm_num),
    eventual_sparse_coverage_margin ((∫ t : ℝ, primeMeanTest t) / 8)
      (div_pos primeMeanTest_integral_pos (by norm_num)),
    eventually_ge_atTop (10000 : ℝ)] with L hsieve hgeom hsub hlarge hcoverage hmargin hL
  obtain ⟨exception, he⟩ := hcoverage
  refine ⟨exception, ?_⟩
  intro X hX n p hp hnprod hc hpband hlo hhi ε hε hεsmall hL1 hH havoid
  by_contra hmass
  have hmass' : (17 / 25 : ℝ) * L ≤ ∑ i, (p i : ℝ)⁻¹ := le_of_not_gt hmass
  have hp100 (i : Fin n) : (100 : ℝ) ≤ p i := by
    have hh := (logLogPrimeBand_mem (hpband i)).2.1
    have he := Real.add_one_le_exp ((1 / 20 : ℝ) * L)
    have hl := Real.log_le_self (Nat.cast_nonneg (p i))
    linarith
  have hSp (i : Fin n) : (tailDensityMask A N (p i)).card < p i :=
    tailDensityMask_card_lt hB N _ (Fact.out : (p i).Prime).pos (hN _ Fact.out)
  have hS (i : Fin n) : (tailDensityMask A N (p i)).Nonempty :=
    tailDensityMask_nonempty hA N _ (Fact.out : (p i).Prime).pos
  obtain ⟨_, hcov⟩ := he X hX n p (fun i => tailDensityMask A N (p i)) hc hS hSp
    hp100 hlo hhi ε hε hεsmall hL1 hH
    (fun i => (logLogPrimeBand_mem (hpband i)).2.2) havoid
  obtain ⟨hsa, hsb, _, _, _⟩ := hlarge X hX
  have hpositive : 0 < a * Real.exp (Real.exp L / 2) / Real.exp L ^ 3 := by positivity
  have hAt : (positiveSummandTail A (summandTailCutoff (Real.exp L)) X).Nonempty :=
    Finset.card_pos.mp (by exact_mod_cast lt_of_lt_of_le hpositive hsa)
  have hBt : (negativeSummandTail B (summandTailCutoff (Real.exp L)) X).Nonempty :=
    Finset.card_pos.mp (by exact_mod_cast lt_of_lt_of_le hpositive hsb)
  let K := sparseTruncationDegree 1000 L
  have hK : 1000 * L ≤ (K : ℝ) := Nat.le_ceil _
  have hKu : (K : ℝ) ≤ 1000 * L + 1 :=
    (Nat.ceil_lt_add_one (by positivity : 0 ≤ (1000 : ℝ) * L)).le
  have hsub' (T : Finset (Fin n)) (hT : T.card ≤ 2 * K) :
      (∏ i ∈ T, p i) ≤ ⌊Real.exp (Real.exp L / 2)⌋₊ ∧
      (∑ q ∈ T.image p, (q : ℝ)⁻¹) ≤ 1 / 16 := by
    apply hsub n p hpband T
    have ht : (T.card : ℝ) ≤ 2 * (K : ℝ) := by exact_mod_cast hT
    linarith
  apply sparse_tail_sieve_contradiction ls hA hB N (summandTailCutoff (Real.exp L)) X
    ⌊Real.exp (Real.exp L / 2)⌋₊ hN hgeom.2.2.2 hgeom.1 hAt hBt p hc
    (fun i => Nat.le_of_mem_primesLE
      (logLogPrimeBand_subset_sqrt_cutoff L (by linarith) (hpband i)))
    hp100 hlo hhi ε hε hεsmall hL1 L (by linarith) hH hmass' K hK
    (fun T hT => (hsub' T hT).1) (fun T hT => (hsub' T hT).2)
    (hsieve X hX _ (Finset.Subset.refl _)) ((∫ t : ℝ, primeMeanTest t) / 8)
    (div_pos primeMeanTest_integral_pos (by norm_num)) hcov
    (by rw [hX, Real.log_exp]) (by rw [hX]; positivity)
    (by simpa only [hX] using hgeom.2.1)
    (by simpa only [hX] using hgeom.2.2.1) hmargin

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_TailBandCollision
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The collision budget on the band used in Proposition 5.1 -/
namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem eventual_logLogPrimeBand_subset_collision_cutoff :
    ∀ᶠ L : ℝ in atTop,
      logLogPrimeBand L ⊆ Nat.primesLE (tailCollisionCutoff (Real.exp L)) := by
  have hsmall := eventual_affine_log_le_rpow 5 (Real.log 2) (1 / 4) 1
    (by norm_num) (by norm_num) (by norm_num)
  simp only [Real.rpow_one] at hsmall
  filter_upwards [Real.tendsto_exp_atTop.eventually hsmall,
    Real.tendsto_exp_atTop.eventually (eventual_tailCollisionCutoff 0),
    eventually_ge_atTop (30 : ℝ)] with L hsmall hcut hL
  intro p hp
  obtain ⟨hpp, _, hpu⟩ := logLogPrimeBand_mem hp
  have hfour : 4 ≤ Real.exp ((1 / 10 : ℝ) * L) := by
    linarith [Real.add_one_le_exp ((1 / 10 : ℝ) * L)]
  have hprod := mul_le_mul_of_nonneg_left hfour (Real.exp_nonneg ((9 / 10 : ℝ) * L))
  rw [← Real.exp_add] at hprod
  have hex : (9 / 10 : ℝ) * L + (1 / 10 : ℝ) * L = L := by ring
  rw [hex] at hprod
  have hQ := tailCollisionCutoff_bounds (Real.exp L) hcut.1 hcut.2.1
  have hlog : Real.log p ≤ Real.log (tailCollisionCutoff (Real.exp L) : ℝ) := by
    linarith [hQ.2.2]
  have hQpos : (0 : ℝ) < tailCollisionCutoff (Real.exp L) := by exact_mod_cast hQ.1
  have hpQ : (p : ℝ) ≤ tailCollisionCutoff (Real.exp L) :=
    (Real.log_le_log_iff (by exact_mod_cast hpp.pos) hQpos).mp hlog
  exact Nat.mem_primesLE.mpr ⟨by exact_mod_cast hpQ, hpp⟩

theorem EventuallyPrimeSumset.tail_band_collision_budget
    (hsize : PublishedSummandSizeBound) {A B : Set ℕ}
    (h : EventuallyPrimeSumset A B) (hA : A.Infinite) (hB : B.Infinite)
    (N : ℕ) (hN : ∀ p, p.Prime → Disjoint (tailResidues A N p) (negTailResidues B N p))
    (C : ℝ) (hM : MertensLowerBound C) :
    ∃ a : ℝ, 0 < a ∧ ∀ᶠ L : ℝ in atTop,
      ∀ X : ℕ, (X : ℝ) = Real.exp (Real.exp L) →
      (∑ p ∈ logLogPrimeBand L, Real.log p * tailCollisionDefect A N p
        (summandTail A (summandTailCutoff (Real.exp L)) X)
        (summandTail B (summandTailCutoff (Real.exp L)) X)
        (fun _ => 1 / ((summandTail A (summandTailCutoff (Real.exp L)) X).card : ℝ))
        (fun _ => 1 / ((summandTail B (summandTailCutoff (Real.exp L)) X).card : ℝ))) ≤
        20 * L + (4 * C + 4 * Real.log 2 + 2 * Real.log 4 / a) := by
  obtain ⟨a, ha, hlarge⟩ := exists_large_summand_tails hsize hA hB h
  refine ⟨a, ha, ?_⟩
  filter_upwards [Real.tendsto_exp_atTop.eventually hlarge,
    Real.tendsto_exp_atTop.eventually (eventual_tailCollisionCutoff N),
    eventual_logLogPrimeBand_subset_collision_cutoff] with L hlarge hcut hsub
  intro X hX
  obtain ⟨hsa, hsb, _, _, _⟩ := hlarge X hX
  have hb := uniform_tail_collision_bound hA hB N (summandTailCutoff (Real.exp L)) X
    a (Real.exp L) C ha hcut.1 hcut.2.1 hX hcut.2.2
    (fun p hp => hN p (Nat.prime_of_mem_primesLE hp))
    (by simpa only [positiveSummandTail_card] using hsa)
    (by simpa only [negativeSummandTail_card] using hsb) hM
  rw [Real.log_exp] at hb
  apply le_trans _ (hb.trans_eq (by ring))
  apply Finset.sum_le_sum_of_subset_of_nonneg hsub
  intro p hp _
  apply mul_nonneg (Real.log_natCast_nonneg p)
  apply collisionDefect_nonneg
  · exact tailSupport_nonempty hA N p (Nat.prime_of_mem_primesLE hp).pos
  · exact tailSupport_complement_nonempty hB (Nat.prime_of_mem_primesLE hp).pos
      (hN p (Nat.prime_of_mem_primesLE hp))
  · exact (tailSupport_card_add_complement A N p).le

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_TailFourierMass
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One total Fourier-mass function for the actual tail masks -/
namespace Ostmann
open scoped Classical BigOperators

theorem tailFourierMass_eq (A : Set ℕ) (N p : ℕ) [NeZero p] :
    tailFourierMass A N p =
      (p : ℝ)⁻¹ * ∑ b, ‖normalizedResidueTransform (tailDensityMask A N p) b‖ := by
  simp only [tailFourierMass, dite_eq_right (NeZero.ne p)]

theorem tailDensityMask_balanced_iff (A : Set ℕ) (N p : ℕ) (hp : 0 < p) :
    ((1 / 3 : ℝ) ≤ residueDensity (tailDensityMask A N p) ∧
      residueDensity (tailDensityMask A N p) ≤ 2 / 3) ↔
    ((p : ℝ) / 3 ≤ (tailSupport A N p).card ∧
      ((tailSupport A N p).card : ℝ) ≤ 2 * p / 3) := by
  unfold residueDensity
  rw [tailDensityMask_card]
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  constructor
  · rintro ⟨hl, hu⟩
    rw [le_div_iff₀ hp'] at hl
    rw [div_le_iff₀ hp'] at hu
    constructor <;> linarith
  · rintro ⟨hl, hu⟩
    constructor
    · apply (le_div_iff₀ hp').mpr
      linarith
    · apply (div_le_iff₀ hp').mpr
      linarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_ExceptionalPrimeDeletion
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing at most one prime excludes the exceptional conductor -/
namespace Ostmann
open scoped Classical BigOperators

theorem PrimitiveComplexCharacter.modulus_one_lt (χ : PrimitiveComplexCharacter) :
    1 < χ.modulus := by
  have : NeZero χ.modulus := ⟨χ.positive.ne'⟩
  have hc : χ.character.conductor ≠ 1 := by
    intro h
    exact χ.nontrivial (DirichletCharacter.eq_one_iff_conductor_eq_one.mpr h)
  have hh := χ.primitive
  change χ.character.conductor = χ.modulus at hh
  have hp := χ.positive
  omega

theorem prime_mem_of_dvd_prime_product (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (q : ℕ) (hq : q.Prime) (hd : q ∣ ∏ p ∈ P, p) : q ∈ P := by
  induction P using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty] at hd
    exact (hq.ne_one (Nat.dvd_one.mp hd)).elim
  | @insert p P hp ih =>
    rw [Finset.prod_insert hp] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have he : q = p := ((Nat.dvd_prime (hP p (Finset.mem_insert_self _ _))).mp hd).resolve_left hq.ne_one
      simp [he]
    · exact Finset.mem_insert_of_mem (ih (fun r hr => hP r (Finset.mem_insert_of_mem hr)) hd)

theorem exists_prime_deletion_avoiding (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (d : ℕ) (hd : 1 < d) :
    ∃ Q : Finset ℕ, Q ⊆ P ∧ P.card ≤ Q.card + 1 ∧ ¬ d ∣ ∏ p ∈ Q, p := by
  by_cases hdiv : d ∣ ∏ p ∈ P, p
  · obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd (show d ≠ 1 by omega)
    have hqP := prime_mem_of_dvd_prime_product P hP q hq (hqd.trans hdiv)
    refine ⟨P.erase q, Finset.erase_subset _ _, ?_, ?_⟩
    · have hh := Finset.card_erase_add_one hqP
      omega
    · intro hh
      have hmem := prime_mem_of_dvd_prime_product (P.erase q)
        (fun p hp => hP p (Finset.mem_erase.mp hp).2) q hq (hqd.trans hh)
      exact (Finset.mem_erase.mp hmem).1 rfl
  · exact ⟨P, Finset.Subset.refl _, by omega, hdiv⟩

theorem exists_exceptional_prime_deletion (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (exception : Option PrimitiveComplexCharacter) :
    ∃ Q : Finset ℕ, Q ⊆ P ∧ P.card ≤ Q.card + 1 ∧
      ∀ ρ, exception = some ρ → ¬ ρ.modulus ∣ ∏ p ∈ Q, p := by
  cases exception with
  | none => exact ⟨P, Finset.Subset.refl _, by omega, by intro ρ h; contradiction⟩
  | some ρ =>
    obtain ⟨Q, hQP, hcard, hd⟩ := exists_prime_deletion_avoiding P hP ρ.modulus ρ.modulus_one_lt
    exact ⟨Q, hQP, hcard, by intro σ h; cases Option.some.inj h; exact hd⟩

theorem prime_deletion_harmonic_loss (P Q : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hQP : Q ⊆ P) (hcard : P.card ≤ Q.card + 1) :
    (∑ p ∈ P, (p : ℝ)⁻¹) ≤ (∑ p ∈ Q, (p : ℝ)⁻¹) + 1 / 2 := by
  have hc : (P \ Q).card ≤ 1 := by
    have hh := Finset.card_sdiff_of_subset hQP
    have hle := Finset.card_le_card hQP
    omega
  have hs : (∑ p ∈ P \ Q, (p : ℝ)⁻¹) ≤ 1 / 2 := by
    calc
      _ ≤ ∑ _p ∈ P \ Q, (1 / 2 : ℝ) := by
        apply Finset.sum_le_sum
        intro p hp
        have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hP p (Finset.mem_sdiff.mp hp).1).two_le
        simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hp2
      _ ≤ 1 / 2 := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        have hc' : ((P \ Q).card : ℝ) ≤ 1 := by exact_mod_cast hc
        linarith
  have hsum : (∑ p ∈ P \ Q, (p : ℝ)⁻¹) + (∑ p ∈ Q, (p : ℝ)⁻¹) =
      (∑ p ∈ P, (p : ℝ)⁻¹) := Finset.sum_sdiff hQP
  linarith

theorem exists_exceptional_prime_deletion_mass (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (exception : Option PrimitiveComplexCharacter) (L : ℝ) (hL : 50 ≤ L)
    (hmass : (69 / 100 : ℝ) * L ≤ ∑ p ∈ P, (p : ℝ)⁻¹) :
    ∃ Q : Finset ℕ, Q ⊆ P ∧
      (17 / 25 : ℝ) * L ≤ (∑ p ∈ Q, (p : ℝ)⁻¹) ∧
      ∀ ρ, exception = some ρ → ¬ ρ.modulus ∣ ∏ p ∈ Q, p := by
  obtain ⟨Q, hQP, hcard, havoid⟩ := exists_exceptional_prime_deletion P hP exception
  refine ⟨Q, hQP, ?_, havoid⟩
  have hh := prime_deletion_harmonic_loss P Q hP hQP hcard
  linarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Supply_FavorableTailPrimeMass
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Proposition 5.1: favorable primes for the actual infinite summand tails -/
namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem EventuallyPrimeSumset.favorable_tail_prime_mass_oai
    (ls : PublishedAdditiveLargeSieve) (hsize : PublishedSummandSizeBound)
    {A B : Set ℕ} (h : EventuallyPrimeSumset A B) (hA : A.Infinite) (hB : B.Infinite)
    (CM CH : ℝ) (hM : MertensEstimate CM) (hMH : MertensHarmonicEstimate CH)
    (Z : ∀ χ, ComplexZeroEnumeration χ) (hD : PublishedComplexZeroDensity Z)
    (hR : PublishedComplexZeroRegion Z) (P : PublishedSmoothExplicitFormula Z)
    (hPNT : PublishedSmoothPrincipalPNT) :
    ∃ N : ℕ, (∀ q, q.Prime → Disjoint (tailResidues A N q) (negTailResidues B N q)) ∧
      ∀ᶠ L : ℝ in atTop, ∀ X : ℕ, (X : ℝ) = Real.exp (Real.exp L) →
        (3 / 20 : ℝ) * L <
          ∑ p ∈ favorableTransformPrimes (logLogPrimeBand L) (tailSupport A N)
            (tailFourierMass A N) ((1 / 1000000 : ℝ) ^ 2), (p : ℝ)⁻¹ := by
  obtain ⟨N, hN, hsmall⟩ := h.sparse_tail_mass_bound ls hsize hA hB CM hM Z hD hR P hPNT
  obtain ⟨a, _, hcollision⟩ := h.tail_band_collision_budget hsize hA hB N hN CM hM.lower
  refine ⟨N, hN, ?_⟩
  filter_upwards [hsmall, hcollision, eventual_logLogPrimeBand_harmonic_le hMH,
    eventual_sparse_mass_error CH 20 (4 * CM + 4 * Real.log 2 + 2 * Real.log 4 / a),
    eventually_ge_atTop (50 : ℝ)] with L hsmall hcollision hbandmass herr hL
  obtain ⟨exception, hsmall⟩ := hsmall
  intro X hX
  by_contra hfail
  have hfail' : (∑ p ∈ favorableTransformPrimes (logLogPrimeBand L) (tailSupport A N)
      (tailFourierMass A N) ((1 / 1000000 : ℝ) ^ 2), (p : ℝ)⁻¹) ≤ (3 / 20 : ℝ) * L :=
    le_of_not_gt hfail
  let R := sparseTransformPrimes (logLogPrimeBand L) (tailSupport A N)
    (tailFourierMass A N) ((1 / 1000000 : ℝ) ^ 2)
  have hRsub : R ⊆ logLogPrimeBand L := Finset.filter_subset _ _
  have hRprime (p : ℕ) (hp : p ∈ R) : p.Prime := (logLogPrimeBand_mem (hRsub hp)).1
  have hmass : (69 / 100 : ℝ) * L ≤ ∑ p ∈ R, (p : ℝ)⁻¹ := by
    have hh := logLog_sparse_mass_lower hMH L (by linarith) (tailSupport A N)
      (fun p => Finset.range p \ tailSupport A N p)
      (fun p => residueMass (summandTail A (summandTailCutoff (Real.exp L)) X)
        (fun _ => 1 / ((summandTail A (summandTailCutoff (Real.exp L)) X).card : ℝ)) p)
      (fun p => fiberMass (summandTail B (summandTailCutoff (Real.exp L)) X)
        (fun _ => 1 / ((summandTail B (summandTailCutoff (Real.exp L)) X).card : ℝ))
        (negativeResidue p))
      (tailFourierMass A N) ((1 / 1000000 : ℝ) ^ 2)
      (20 * L + (4 * CM + 4 * Real.log 2 + 2 * Real.log 4 / a))
      (fun p hp => tailSupport_nonempty hA N p (logLogPrimeBand_mem hp).1.pos)
      (fun p hp => tailSupport_complement_nonempty hB (logLogPrimeBand_mem hp).1.pos
        (hN p (logLogPrimeBand_mem hp).1))
      (fun p _ => tailSupport_card_add_complement A N p)
      (hcollision X hX) hfail'
    exact (herr _ le_rfl).trans hh
  obtain ⟨Q, hQR, hQmass, havoid⟩ := exists_exceptional_prime_deletion_mass R hRprime
    exception L hL hmass
  let p := primeFamilyEnumeration Q
  have hp (i : Fin Q.card) : (p i).Prime :=
    hRprime _ (hQR (primeFamilyEnumeration_mem Q i))
  let (i : Fin Q.card) : Fact (p i).Prime := ⟨hp i⟩
  let : NeZero (∏ i, p i) := ⟨(Finset.prod_pos (fun i _ => (hp i).pos)).ne'⟩
  have hpR (i : Fin Q.card) : p i ∈ R := hQR (primeFamilyEnumeration_mem Q i)
  have hpband (i : Fin Q.card) : p i ∈ logLogPrimeBand L := hRsub (hpR i)
  have hbal (i : Fin Q.card) :
      (1 / 3 : ℝ) ≤ residueDensity (tailDensityMask A N (p i)) ∧
        residueDensity (tailDensityMask A N (p i)) ≤ 2 / 3 := by
    apply (tailDensityMask_balanced_iff A N _ (hp i).pos).mpr
    exact ⟨(Finset.mem_filter.mp (hpR i)).2.1, (Finset.mem_filter.mp (hpR i)).2.2.1⟩
  have hL1 (i : Fin Q.card) : (p i : ℝ)⁻¹ * ∑ b,
      ‖normalizedResidueTransform (tailDensityMask A N (p i)) b‖ ≤ (1 / 1000000 : ℝ) ^ 2 := by
    rw [← tailFourierMass_eq]
    exact (Finset.mem_filter.mp (hpR i)).2.2.2.le
  have hsum : (∑ i, (p i : ℝ)⁻¹) = ∑ q ∈ Q, (q : ℝ)⁻¹ :=
    primeFamilyEnumeration_sum Q (fun q => (q : ℝ)⁻¹)
  have hmassQ : (∑ i, (p i : ℝ)⁻¹) ≤ L := by
    rw [hsum]
    apply le_trans _ hbandmass
    exact Finset.sum_le_sum_of_subset_of_nonneg (hQR.trans hRsub) (fun _ _ _ => by positivity)
  have hbad := hsmall X hX Q.card p
    (primeFamilyEnumeration_coprime Q (fun q hq => hRprime q (hQR hq))) hpband
    (fun i => (hbal i).1) (fun i => (hbal i).2)
    (1 / 1000000) (by norm_num) (by norm_num) hL1 hmassQ
    (by simpa only [p, primeFamilyEnumeration_prod] using havoid)
  rw [hsum] at hbad
  linarith

end Ostmann

end OAI
end

theorem solution : type_of% @OAI.Ostmann.EventuallyPrimeSumset.favorable_tail_prime_mass_oai := @OAI.Ostmann.EventuallyPrimeSumset.favorable_tail_prime_mass_oai
