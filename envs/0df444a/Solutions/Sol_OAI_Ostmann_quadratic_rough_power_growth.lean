-- Prove2me | solution 1 for OAI.Ostmann.quadratic_rough_power_growth
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T06:51:44.084222+00:00
-- url     : https://prove2.me/submissions/6ef0c8b2-f33e-482e-989a-d51266ae208c

import Mathlib
import Definitions.Def_OAIQ095D003
import Definitions.Def_OAIQ095D005
import Theorems.Thm_OAI_Ostmann_quadratic_gcd_corrections_power_bound
import Theorems.Thm_OAI_Ostmann_quadratic_gcd_main_growth

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_AdditiveFourier
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
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
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
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
-- module Solutions.OAIQ095_OS.Ostmann_Characters_FinitePoissonTransform
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Poisson summation with a concrete finite periodic weight -/

namespace Ostmann

open scoped BigOperators FourierTransform SchwartzMap
open Asymptotics Filter

theorem schwartz_int_norm_summable (f : 𝓢(ℝ, ℂ)) :
    Summable (fun n : ℤ => ‖f (n : ℝ)‖) := by
  have hb := (f.isBigO_cocompact_rpow (-2)).comp_tendsto Int.tendsto_coe_cofinite
  exact summable_of_isBigO (Real.summable_abs_int_rpow (by norm_num : (1 : ℝ) < 2)) hb.norm_left

private theorem fourier_residue {N : ℕ} [NeZero N] (n : ℤ) (a : ZMod N) :
    fourier n (ZMod.toAddCircle a) = ZMod.stdAddChar ((n : ZMod N) * a) := by
  simp only [fourier_apply, ZMod.stdAddChar_apply, ZMod.toCircle,
    AddChar.compAddMonoidHom_apply]
  rw [← map_zsmul]
  congr 2
  simp only [zsmul_eq_mul]
  rfl

private theorem schwartz_fourier_residue_summable {N : ℕ} [NeZero N]
    (f : 𝓢(ℝ, ℂ)) (a : ZMod N) :
    Summable (fun n : ℤ => 𝓕 f (n : ℝ) * ZMod.stdAddChar ((n : ZMod N) * a)) := by
  apply Summable.of_norm_bounded (schwartz_int_norm_summable (𝓕 f))
  intro n
  simp only [Complex.norm_mul, ZMod.stdAddChar_apply, Circle.norm_coe, mul_one, le_refl]

/-- The lattice spacing has been absorbed into the Schwartz function.
This exact identity retains the finite Fourier coefficient and all signs. -/
theorem finite_poisson_transform {N : ℕ} [NeZero N] (f : 𝓢(ℝ, ℂ)) (F : ZMod N → ℂ) :
    (∑ a : ZMod N, F a * ∑' n : ℤ, f ((a.val : ℝ) / N + n)) =
      (N : ℂ) * ∑' n : ℤ, 𝓕 f (n : ℝ) * additiveFourier F (-(n : ZMod N)) := by
  have hp (a : ZMod N) : (∑' n : ℤ, f ((a.val : ℝ) / N + n)) =
      ∑' n : ℤ, 𝓕 f (n : ℝ) * ZMod.stdAddChar ((n : ZMod N) * a) := by
    rw [f.tsum_eq_tsum_fourier]
    simp_rw [← ZMod.toAddCircle_apply, fourier_residue]
  simp_rw [hp, ← tsum_mul_left]
  have hsum (a : ZMod N) : Summable (fun n : ℤ =>
      F a * (𝓕 f (n : ℝ) * ZMod.stdAddChar ((n : ZMod N) * a))) :=
    (schwartz_fourier_residue_summable f a).mul_left _
  rw [← Summable.tsum_finsetSum (fun a _ => hsum a)]
  apply tsum_congr
  intro n
  rw [additiveFourier_apply]
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hc (z : ℂ) : (N : ℂ) * ((N : ℂ)⁻¹ * z) = z := by
    rw [← mul_assoc, mul_inv_cancel₀ hN, one_mul]
  rw [mul_left_comm (N : ℂ) (𝓕 f (n : ℝ)), hc]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  have ha' : -(a * -(n : ZMod N)) = (n : ZMod N) * a := by ring
  rw [ha']
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_IntegerPoissonTransform
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integer-lattice form of finite periodic Poisson summation -/

namespace Ostmann

open scoped BigOperators FourierTransform SchwartzMap

private theorem integerResidueEquiv_symm_apply (N : ℕ) [NeZero N] (a : ZMod N) (k : ℤ) :
    (integerResidueEquiv N).symm (a, k) = k * N + a.val := by
  cases N with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ N => rfl

theorem schwartz_translate_int_norm_summable (f : 𝓢(ℝ, ℂ)) (a : ℝ) :
    Summable (fun n : ℤ => ‖f (a + n)‖) := by
  simpa only [SchwartzMap.compSubConstCLM_apply, sub_neg_eq_add, add_comm] using
    schwartz_int_norm_summable (f.compSubConstCLM ℂ (-a))

theorem integer_lattice_residue_sum {N : ℕ} [NeZero N]
    (f : 𝓢(ℝ, ℂ)) (F : ZMod N → ℂ) :
    (∑' n : ℤ, F (n : ZMod N) * f ((n : ℝ) / N)) =
      ∑ a : ZMod N, F a * ∑' k : ℤ, f ((a.val : ℝ) / N + k) := by
  let H : ZMod N × ℤ → ℂ := fun z => F z.1 * f ((z.1.val : ℝ) / N + z.2)
  have hrow (a : ZMod N) : Summable (fun k : ℤ =>
      ‖F a‖ * ‖f ((a.val : ℝ) / N + k)‖) :=
    (schwartz_translate_int_norm_summable f ((a.val : ℝ) / N)).mul_left ‖F a‖
  have houter : Summable (fun a : ZMod N =>
      ∑' k : ℤ, ‖F a‖ * ‖f ((a.val : ℝ) / N + k)‖) := (hasSum_fintype _).summable
  have hnorm : Summable (fun z : ZMod N × ℤ =>
      ‖F z.1‖ * ‖f ((z.1.val : ℝ) / N + z.2)‖) :=
    (summable_prod_of_nonneg (fun z : ZMod N × ℤ =>
      mul_nonneg (norm_nonneg (F z.1)) (norm_nonneg (f ((z.1.val : ℝ) / N + z.2))))).2
        ⟨hrow, houter⟩
  have hH : Summable H := by
    apply Summable.of_norm
    simpa only [H, Complex.norm_mul] using hnorm
  have he (a : ZMod N) (k : ℤ) :
      F (((integerResidueEquiv N).symm (a, k) : ℤ) : ZMod N) *
        f (((integerResidueEquiv N).symm (a, k) : ℤ) / (N : ℝ)) = H (a, k) := by
    rw [integerResidueEquiv_symm_apply]
    simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self,
      mul_zero, zero_add, ZMod.natCast_zmod_val]
    congr 2
    have hN : (N : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
    dsimp [H]
    field_simp
    ring
  calc
    _ = ∑' z : ZMod N × ℤ, H z := by
      rw [← (integerResidueEquiv N).symm.tsum_eq
        (fun n : ℤ => F (n : ZMod N) * f ((n : ℝ) / N))]
      apply tsum_congr
      rintro ⟨a, k⟩
      exact he a k
    _ = ∑' a : ZMod N, ∑' k : ℤ, H (a, k) := hH.tsum_prod
    _ = _ := by
      rw [tsum_fintype]
      apply Finset.sum_congr rfl
      intro a ha
      change (∑' k : ℤ, F a * f ((a.val : ℝ) / N + k)) = _
      exact tsum_mul_left

theorem integer_poisson_transform {N : ℕ} [NeZero N]
    (f : 𝓢(ℝ, ℂ)) (F : ZMod N → ℂ) :
    (∑' n : ℤ, F (n : ZMod N) * f ((n : ℝ) / N)) =
      (N : ℂ) * ∑' n : ℤ, 𝓕 f (n : ℝ) * additiveFourier F (-(n : ZMod N)) := by
  rw [integer_lattice_residue_sum, finite_poisson_transform]

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
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_PeriodicWeightPoisson
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Poisson summation gives the exact total amplification weight -/

namespace Ostmann

open scoped BigOperators FourierTransform SchwartzMap

theorem scaled_periodic_poisson {N : ℕ} [NeZero N]
    (F : ZMod N → ℂ) (ψ : 𝓢(ℝ, ℂ)) (X : ℝ) (hX : 0 < X) :
    (∑' n : ℤ, F (n : ZMod N) * ψ ((n : ℝ) / X)) =
      (X : ℂ) * ∑' n : ℤ, 𝓕 ψ ((n : ℝ) * X / N) * additiveFourier F (-(n : ZMod N)) := by
  have hN : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  have ha : 0 < (N : ℝ) / X := div_pos hN hX
  have hp := integer_poisson_transform (positiveDilate ψ ((N : ℝ) / X) ha) F
  have harg (n : ℤ) : (N : ℝ) / X * ((n : ℝ) / N) = n / X := by field_simp
  have hfreq (n : ℤ) : (n : ℝ) / ((N : ℝ) / X) = n * X / N := by rw [div_div_eq_mul_div]
  simp_rw [positiveDilate_apply, harg, positiveDilate_fourier, hfreq] at hp
  rw [hp]
  simp_rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  have hNC : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  push_cast
  field_simp

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticSieve_JacobiComplex
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The concrete complex Jacobi character used in the Fourier expansion -/

namespace Ostmann

theorem jacobiComplex_isQuadratic (M : ℕ) [NeZero M] : (jacobiComplex M).IsQuadratic := by
  apply MulChar.IsQuadratic.comp
  intro a
  change jacobiSym (a.val : ℤ) M = 0 ∨ jacobiSym (a.val : ℤ) M = 1 ∨ jacobiSym (a.val : ℤ) M = -1
  rcases jacobiSym.trichotomy (a.val : ℤ) M with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticSieve_PrimeJacobiCharacter
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The prime-level Jacobi character is primitive -/

namespace Ostmann

theorem jacobiCharacterInt_prime (p : ℕ) [Fact p.Prime] :
    jacobiCharacterInt p = quadraticChar (ZMod p) := by
  apply MulChar.ext
  intro a
  have hcast : ((((a : ZMod p).val : ℤ) : ZMod p)) = (a : ZMod p) := by
    simp only [Int.cast_natCast, ZMod.natCast_zmod_val]
  calc
    jacobiCharacterInt p a = jacobiCharacterInt p ((((a : ZMod p).val : ℤ) : ZMod p)) :=
      congrArg (jacobiCharacterInt p) hcast.symm
    _ = jacobiSym ((a : ZMod p).val : ℤ) p := jacobiCharacterInt_intCast p _
    _ = legendreSym p ((a : ZMod p).val : ℤ) := (jacobiSym.legendreSym.to_jacobiSym p _).symm
    _ = quadraticChar (ZMod p) a := by rw [legendreSym, hcast]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticSieve_SquarefreeJacobiCharacter
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The conductor of the Jacobi character at odd squarefree level -/

namespace Ostmann

private theorem jacobi_crt_negative (p M : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (hM : 0 < M) (hcop : p.Coprime M) :
    ∃ n : ℕ, n.Coprime (p * M) ∧ n ≡ 1 [MOD M] ∧ jacobiSym (n : ℤ) (p * M) = -1 := by
  let : Fact p.Prime := ⟨hp⟩
  let : NeZero M := ⟨hM.ne'⟩
  have hc : ringChar (ZMod p) ≠ 2 := by simpa only [ZMod.ringChar_zmod_n] using hp2
  obtain ⟨a, ha⟩ := quadraticChar_exists_neg_one' hc
  let n := Nat.chineseRemainder hcop (a : ZMod p).val 1
  have hnp : (n : ℕ) ≡ (a : ZMod p).val [MOD p] := n.property.1
  have hnM : (n : ℕ) ≡ 1 [MOD M] := n.property.2
  have hpa : ((n : ℕ) : ZMod p) = (a : ZMod p) := by
    have h := (ZMod.natCast_eq_natCast_iff (n : ℕ) (a : ZMod p).val p).mpr hnp
    simpa only [ZMod.natCast_zmod_val] using h
  have hMa : ((n : ℕ) : ZMod M) = 1 := by
    simpa only [Nat.cast_one] using (ZMod.natCast_eq_natCast_iff (n : ℕ) 1 M).mpr hnM
  have hcp : (n : ℕ).Coprime p := by
    apply (ZMod.isUnit_iff_coprime (n : ℕ) p).mp
    rw [hpa]
    exact a.isUnit
  have hcM : (n : ℕ).Coprime M := by
    apply (ZMod.isUnit_iff_coprime (n : ℕ) M).mp
    rw [hMa]
    exact isUnit_one
  have hJp : jacobiSym (n : ℤ) p = -1 := by
    rw [← jacobiCharacterInt_intCast p, Int.cast_natCast, jacobiCharacterInt_prime, hpa, ha]
  have hJM : jacobiSym (n : ℤ) M = 1 := by
    have h := jacobiSym.mod_left' ((ZMod.intCast_eq_intCast_iff' (n : ℤ) 1 M).mp
      (by simpa only [Int.cast_natCast, Int.cast_one] using hMa))
    simpa only [jacobiSym.one_left] using h
  exact ⟨n, hcp.mul_right hcM, hnM, by rw [jacobiSym.mul_right, hJp, hJM, mul_one]⟩

/-- An odd prime factor missing from the conductor is contradicted by a
CRT unit whose Jacobi value is -1 and whose conductor residue is 1. -/
theorem jacobiCharacter_squarefree_primitive (N : ℕ) [NeZero N]
    (hN : Squarefree N) (hodd : Odd N) : (jacobiCharacter N).IsPrimitive := by
  let χ := jacobiCharacter N
  have hcN := χ.conductor_dvd_level
  have hcp (p : ℕ) (hp : p.Prime) (hpN : p ∣ N) : p ∣ χ.conductor := by
    by_contra hpc
    have hp2 : p ≠ 2 := by
      intro heq
      subst p
      exact hodd.not_two_dvd_nat hpN
    have hprod : p * (N / p) = N := Nat.mul_div_cancel' hpN
    have hM : 0 < N / p := by
      have hNpos : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
      nlinarith
    have hcop : p.Coprime (N / p) := Nat.coprime_of_squarefree_mul (hprod.symm ▸ hN)
    obtain ⟨n, hn, hnM, hJn⟩ := jacobi_crt_negative p (N / p) hp hp2 hM hcop
    have hnc : n.Coprime N := hprod ▸ hn
    have hcd : χ.conductor ∣ N / p := by
      apply ((hp.coprime_iff_not_dvd.mpr hpc).symm).dvd_of_dvd_mul_left
      rwa [hprod]
    have hncon : (n : ZMod χ.conductor) = 1 := by
      have h := (ZMod.natCast_eq_natCast_iff n 1 χ.conductor).mpr (hnM.of_dvd hcd)
      simpa only [Nat.cast_one] using h
    have he := χ.primitiveCharacter_apply_of_isCoprime (Nat.isCoprime_iff_coprime.mpr hnc)
    have hv : χ.primitiveCharacter (n : ℤ) = 1 := by
      rw [Int.cast_natCast, hncon, map_one]
    have hv' : χ (n : ℤ) = -1 := by
      change jacobiCharacter N (n : ℤ) = -1
      rw [jacobiCharacter_intCast, ← hprod, hJn]
      norm_num
    rw [hv, hv'] at he
    norm_num at he
  have hNc : (∏ p ∈ N.primeFactors, p) ∣ χ.conductor := by
    apply (Nat.prod_primeFactors_dvd_iff χ.conductor_ne_zero).mpr
    intro p hp
    have hp' := Nat.mem_primeFactors.mp hp
    exact Nat.mem_primeFactors.mpr ⟨hp'.1, hcp p hp'.1 hp'.2.1, χ.conductor_ne_zero⟩
  have hNc' : N ∣ χ.conductor := by
    simpa only [Nat.prod_primeFactors_of_squarefree hN] using hNc
  exact Nat.dvd_antisymm hcN hNc'

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticSieve_ComplexJacobiPrimitive
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Primitivity of the concrete complex Jacobi character -/

namespace Ostmann

/-- Passing from a real character to its complex values cannot decrease
its conductor: the map on values is injective. -/
theorem real_character_primitive_complex {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℝ N) (hχ : χ.IsPrimitive) :
    DirichletCharacter.IsPrimitive (χ.ringHomComp Complex.ofRealHom) := by
  let ψ : DirichletCharacter ℂ N := χ.ringHomComp Complex.ofRealHom
  have hd := ψ.conductor_dvd_level
  have hfactor : χ.FactorsThrough ψ.conductor := by
    apply (DirichletCharacter.factorsThrough_iff_ker_unitsMap hd).mpr
    intro u hu
    have hp := (DirichletCharacter.factorsThrough_iff_ker_unitsMap hd).mp
      ψ.factorsThrough_conductor hu
    rw [MonoidHom.mem_ker, Units.ext_iff, MulChar.coe_toUnitHom, Units.val_one] at hp ⊢
    change (χ (u : ZMod N) : ℂ) = 1 at hp
    exact_mod_cast hp
  have hn : N ∣ ψ.conductor := by
    have hh := χ.conductor_dvd_of_mem_conductorSet hfactor
    rwa [hχ] at hh
  exact Nat.dvd_antisymm hd hn

theorem jacobiComplex_eq_real_comp (N : ℕ) [NeZero N] :
    jacobiComplex N = (jacobiCharacter N).ringHomComp Complex.ofRealHom := by
  ext a
  change ((jacobiCharacterInt N) (a : ZMod N) : ℂ) =
    (((jacobiCharacterInt N) (a : ZMod N) : ℝ) : ℂ)
  simp only [Complex.ofReal_intCast]

theorem jacobiComplex_squarefree_primitive (N : ℕ) [NeZero N]
    (hN : Squarefree N) (hodd : Odd N) : (jacobiComplex N).IsPrimitive := by
  rw [jacobiComplex_eq_real_comp]
  exact real_character_primitive_complex _ (jacobiCharacter_squarefree_primitive N hN hodd)

theorem jacobiComplex_intCast (N : ℕ) [NeZero N] (n : ℤ) :
    jacobiComplex N (n : ZMod N) = (jacobiSym n N : ℂ) := by
  change ((jacobiCharacterInt N) (n : ZMod N) : ℂ) = (jacobiSym n N : ℂ)
  rw [jacobiCharacterInt_intCast]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_NormalizedCharacterPoisson
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact square-root normalization in the quadratic Poisson formula -/

namespace Ostmann

open scoped BigOperators SchwartzMap FourierTransform

theorem jacobiGaussPhase_norm (M : ℕ) [NeZero M]
    (hM : Squarefree M) (hodd : Odd M) : ‖jacobiGaussPhase M‖ = 1 := by
  have hp : (0 : ℝ) < M := by exact_mod_cast NeZero.pos M
  have hh := primitive_gauss_norm_sq (jacobiComplex M)
    (jacobiComplex_squarefree_primitive M hM hodd)
  have hs : ‖gaussSum (jacobiComplex M) ZMod.stdAddChar‖ = Real.sqrt (M : ℝ) := by
    nlinarith [Real.sq_sqrt hp.le, Real.sqrt_nonneg (M : ℝ),
      norm_nonneg (gaussSum (jacobiComplex M) ZMod.stdAddChar)]
  rw [jacobiGaussPhase, norm_div, hs, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), div_self (Real.sqrt_pos.mpr hp).ne']

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticPairKernel
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The primitive kernel of a pair of odd squarefree denominators

Writing `d = gcd n₁ n₂`, the product character has squarefree kernel
`(n₁/d)(n₂/d)` and the remaining factor is precisely the coprimality mask
modulo `d`. This is the arithmetic decomposition in Heath-Brown (1995), §3.
-/

namespace Ostmann

 theorem quadraticPairKernel_factor (n₁ n₂ : ℕ) :
    n₁.gcd n₂ ^ 2 * quadraticPairKernel n₁ n₂ = n₁ * n₂ := by
  unfold quadraticPairKernel
  calc
    _ = (n₁.gcd n₂ * (n₁ / n₁.gcd n₂)) *
        (n₁.gcd n₂ * (n₂ / n₁.gcd n₂)) := by ring
    _ = _ := by rw [Nat.mul_div_cancel' (Nat.gcd_dvd_left n₁ n₂),
      Nat.mul_div_cancel' (Nat.gcd_dvd_right n₁ n₂)]

 theorem quadraticPairKernel_squarefree {n₁ n₂ : ℕ}
    (h₁ : Squarefree n₁) (h₂ : Squarefree n₂) :
    Squarefree (quadraticPairKernel n₁ n₂) := by
  apply (Nat.squarefree_mul (Nat.coprime_div_gcd_div_gcd
    (Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero h₁.ne_zero)))).mpr
  exact ⟨h₁.squarefree_of_dvd (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left n₁ n₂)),
    h₂.squarefree_of_dvd (Nat.div_dvd_of_dvd (Nat.gcd_dvd_right n₁ n₂))⟩

 theorem quadraticPairKernel_odd {n₁ n₂ : ℕ} (h₁ : Odd n₁) (h₂ : Odd n₂) :
    Odd (quadraticPairKernel n₁ n₂) :=
  (h₁.of_dvd_nat (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left n₁ n₂))).mul
    (h₂.of_dvd_nat (Nat.div_dvd_of_dvd (Nat.gcd_dvd_right n₁ n₂)))

 theorem quadraticPairKernel_eq_one_iff {n₁ n₂ : ℕ}
    (h₁ : Squarefree n₁) (_h₂ : Squarefree n₂) :
    quadraticPairKernel n₁ n₂ = 1 ↔ n₁ = n₂ := by
  constructor
  · intro h
    change (n₁ / n₁.gcd n₂) * (n₂ / n₁.gcd n₂) = 1 at h
    have ha : n₁ / n₁.gcd n₂ = 1 := Nat.eq_one_of_dvd_one
      ⟨n₂ / n₁.gcd n₂, h.symm⟩
    have hb : n₂ / n₁.gcd n₂ = 1 := Nat.eq_one_of_dvd_one
      ⟨n₁ / n₁.gcd n₂, by simpa only [mul_comm] using h.symm⟩
    have ha' := Nat.mul_div_cancel' (Nat.gcd_dvd_left n₁ n₂)
    have hb' := Nat.mul_div_cancel' (Nat.gcd_dvd_right n₁ n₂)
    rw [ha, mul_one] at ha'
    rw [hb, mul_one] at hb'
    exact ha'.symm.trans hb'
  · rintro rfl
    simp [quadraticPairKernel, Nat.div_self (Nat.pos_of_ne_zero h₁.ne_zero)]

 theorem jacobi_pair_kernel {n₁ n₂ : ℕ} (h₁ : Squarefree n₁)
    (h₂ : Squarefree n₂) (m : ℤ) :
    jacobiSym m n₁ * jacobiSym m n₂ =
      if m.gcd (n₁.gcd n₂) = 1 then jacobiSym m (quadraticPairKernel n₁ n₂) else 0 := by
  let : NeZero n₁ := ⟨h₁.ne_zero⟩
  let : NeZero n₂ := ⟨h₂.ne_zero⟩
  have hd : n₁.gcd n₂ ≠ 0 := (Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero h₁.ne_zero)).ne'
  have hq : quadraticPairKernel n₁ n₂ ≠ 0 := (quadraticPairKernel_squarefree h₁ h₂).ne_zero
  rw [← jacobiSym.mul_right, ← quadraticPairKernel_factor,
    jacobiSym.mul_right' m (pow_ne_zero _ hd) hq, jacobiSym.pow_right]
  split_ifs with hm
  · rw [jacobiSym.sq_one hm, one_mul]
  · rw [(jacobiSym.eq_zero_iff).mpr ⟨hd, hm⟩, zero_pow (by decide), zero_mul]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticPairPoisson
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact Poisson summation for a pair of quadratic coefficients

The squarefree kernel is primitive. The common-divisor coprimality factor
remains in the Fourier transform as the principal character modulo the gcd.
No prime or squarefree terms are discarded.
-/

namespace Ostmann

open scoped Classical BigOperators FourierTransform SchwartzMap

 theorem principal_character_intCast {d : ℕ} (m : ℤ) :
    (1 : DirichletCharacter ℂ d) (m : ZMod d) =
      if m.gcd d = 1 then 1 else 0 := by
  have hu : IsUnit (m : ZMod d) ↔ m.gcd d = 1 := by
    rw [ZMod.coe_int_isUnit_iff_isCoprime, Int.isCoprime_iff_gcd_eq_one, Int.gcd_comm]
  split_ifs with hm
  · exact MulChar.one_apply (hu.mpr hm)
  · exact (1 : DirichletCharacter ℂ d).map_nonunit (fun h => hm (hu.mp h))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticCoprimeMask
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact Möbius expansion of the common-divisor mask -/

namespace Ostmann

open scoped Classical BigOperators

 theorem quadratic_moebius_divisor_sum (n : ℕ) :
    (∑ d ∈ n.divisors, ArithmeticFunction.moebius d) =
      if n = 1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℤ => f n)
    ArithmeticFunction.moebius_mul_coe_zeta
  simpa only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] using h

 theorem coprime_mask_moebius (q n : ℕ) (hq : q ≠ 0) :
    (if n.Coprime q then (1 : ℤ) else 0) =
      ∑ d ∈ q.divisors, if d ∣ n then ArithmeticFunction.moebius d else 0 := by
  have hg : n.gcd q ≠ 0 := Nat.gcd_ne_zero_right hq
  have hf : q.divisors.filter (fun d => d ∣ n) = (n.gcd q).divisors := by
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hdq, _⟩, hdn⟩
      exact ⟨Nat.dvd_gcd hdn hdq, hg⟩
    · rintro ⟨hd, _⟩
      exact ⟨⟨hd.trans (Nat.gcd_dvd_right n q), hq⟩,
        hd.trans (Nat.gcd_dvd_left n q)⟩
  rw [← Finset.sum_filter, hf, quadratic_moebius_divisor_sum]

 theorem principal_character_moebius {q : ℕ} [NeZero q] (n : ℤ) :
    (1 : DirichletCharacter ℂ q) (n : ZMod q) =
      ∑ d ∈ q.divisors, if (d : ℤ) ∣ n then (ArithmeticFunction.moebius d : ℂ) else 0 := by
  have h := congrArg (Int.cast : ℤ → ℂ) (coprime_mask_moebius q n.natAbs (NeZero.ne q))
  have hp : (1 : DirichletCharacter ℂ q) (n : ZMod q) =
      if n.natAbs.Coprime q then 1 else 0 := by
    rw [principal_character_intCast]
    rfl
  simpa only [hp, Int.cast_ite, Int.cast_one, Int.cast_zero, Int.cast_sum, Int.natCast_dvd] using h

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticGcdExpansion
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact common-divisor expansion of the quadratic second moment -/

namespace Ostmann

open scoped Classical BigOperators ComplexConjugate

 theorem quadraticTranspose_norm_sq_expand (N : ℕ) (b : ℕ → ℂ) (m : ℤ) :
    (‖quadraticTransposeSum N b m‖ ^ 2 : ℂ) =
      ∑ z ∈ (oddSquarefreeRange N).product (oddSquarefreeRange N),
        b z.1 * conj (b z.2) * (jacobiSym m z.1 : ℂ) * (jacobiSym m z.2 : ℂ) := by
  rw [← Complex.mul_conj']
  simp only [quadraticTransposeSum, map_sum, map_mul, map_intCast,
    Finset.sum_mul, Finset.mul_sum]
  symm
  calc
    _ = ∑ n₁ ∈ oddSquarefreeRange N, ∑ n₂ ∈ oddSquarefreeRange N,
        b n₁ * conj (b n₂) * (jacobiSym m n₁ : ℂ) * (jacobiSym m n₂ : ℂ) :=
      Finset.sum_product (oddSquarefreeRange N) (oddSquarefreeRange N) _
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro n₁ _
      apply Finset.sum_congr rfl
      intro n₂ _
      ring

 theorem quadraticTranspose_norm_sq_gcd (N : ℕ) (b : ℕ → ℂ) (m : ℤ) :
    (‖quadraticTransposeSum N b m‖ ^ 2 : ℂ) =
      ∑ d ∈ Finset.Icc 1 N, (if m.gcd d = 1 then (1 : ℂ) else 0) *
        quadraticGcdKernelSum N d b m := by
  rw [quadraticTranspose_norm_sq_expand]
  have hmaps (z : ℕ × ℕ)
      (hz : z ∈ (oddSquarefreeRange N).product (oddSquarefreeRange N)) :
      z.1.gcd z.2 ∈ Finset.Icc 1 N := by
    obtain ⟨h₁, h₂⟩ := Finset.mem_product.mp hz
    obtain ⟨hr₁, _, _⟩ := Finset.mem_filter.mp h₁
    exact Finset.mem_Icc.mpr
      ⟨Nat.gcd_pos_of_pos_left _ (Finset.mem_Icc.mp hr₁).1,
        (Nat.gcd_le_left _ (Finset.mem_Icc.mp hr₁).1).trans (Finset.mem_Icc.mp hr₁).2⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  apply Finset.sum_congr rfl
  intro d _
  rw [quadraticGcdKernelSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z hz
  obtain ⟨hz, he⟩ := Finset.mem_filter.mp hz
  obtain ⟨hz₁, hz₂⟩ := Finset.mem_product.mp hz
  have hs := jacobi_pair_kernel (Finset.mem_filter.mp hz₁).2.2
    (Finset.mem_filter.mp hz₂).2.2 m
  rw [he] at hs
  calc
    _ = b z.1 * conj (b z.2) *
        ((jacobiSym m z.1 * jacobiSym m z.2 : ℤ) : ℂ) := by push_cast; ring
    _ = _ := by rw [hs]; split_ifs <;> simp [mul_assoc]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticSieveFinite
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite quadratic-sieve bounds and their reciprocity symmetry

These are the elementary initial steps of Heath-Brown (1995), sections 2--3.
The bound predicate refers to the actual Jacobi matrix and finite coefficients.
-/

namespace Ostmann

open Matrix
open scoped BigOperators Classical

 theorem oddSquarefreeRange_card_le (N : ℕ) : (oddSquarefreeRange N).card ≤ N := by
  calc
    _ ≤ (Finset.Icc 1 N).card := Finset.card_filter_le _ _
    _ = N := by simp

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticSieveMonotone
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Restriction and monotonicity for the actual quadratic-sieve matrix -/

namespace Ostmann

open scoped BigOperators Classical

 theorem oddSquarefreeRange_mono {N R : ℕ} (h : N ≤ R) :
    oddSquarefreeRange N ⊆ oddSquarefreeRange R := by
  intro n hn
  obtain ⟨hrange, hodd, hsq⟩ := Finset.mem_filter.mp hn
  exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
    ⟨(Finset.mem_Icc.mp hrange).1, (Finset.mem_Icc.mp hrange).2.trans h⟩, hodd, hsq⟩

 theorem quadraticSieveEnergy_restrict {N R : ℕ} (hNR : N ≤ R) (b : ℕ → ℂ) :
    quadraticSieveEnergy R (fun n => if n ∈ oddSquarefreeRange N then b n else 0) =
      quadraticSieveEnergy N b := by
  have hs := Finset.sum_subset (oddSquarefreeRange_mono hNR)
    (f := fun n => ‖(if n ∈ oddSquarefreeRange N then b n else 0)‖ ^ 2)
    (by intro n _ hn; simp [hn])
  simpa only [apply_ite, norm_zero, ite_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, Finset.sum_ite_mem, Finset.inter_self, quadraticSieveEnergy] using hs.symm

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticSieveDivisibility
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing a fixed divisor from the actual quadratic coefficient array -/

namespace Ostmann

open scoped Classical BigOperators

 theorem mem_oddSquarefreeRange_mul {s r N : ℕ} (hs : Squarefree s) (ho : Odd s) :
    s * r ∈ oddSquarefreeRange N ↔
      r ∈ oddSquarefreeRange (N / s) ∧ s.Coprime r := by
  have hs0 : 0 < s := Nat.pos_of_ne_zero hs.ne_zero
  constructor
  · intro h
    obtain ⟨hrange, hodd, hsq⟩ := Finset.mem_filter.mp h
    obtain ⟨hcop, _, hrsq⟩ := Nat.squarefree_mul_iff.mp hsq
    refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.pos_of_ne_zero hrsq.ne_zero,
      (Nat.le_div_iff_mul_le hs0).mpr ?_⟩, hodd.of_dvd_nat (dvd_mul_left r s), hrsq⟩, hcop⟩
    simpa only [Nat.mul_comm] using (Finset.mem_Icc.mp hrange).2
  · rintro ⟨hr, hcop⟩
    obtain ⟨hrange, hodd, hsq⟩ := Finset.mem_filter.mp hr
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
      ⟨Nat.mul_pos hs0 (Finset.mem_Icc.mp hrange).1, ?_⟩,
      ho.mul hodd, (Nat.squarefree_mul hcop).mpr ⟨hs, hsq⟩⟩
    simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le hs0).mp (Finset.mem_Icc.mp hrange).2

 theorem sum_oddSquarefree_multiples {R : Type*} [AddCommMonoid R]
    (s N : ℕ) (hs : Squarefree s) (ho : Odd s) (f : ℕ → R) :
    (∑ n ∈ (oddSquarefreeRange N).filter (fun n => s ∣ n), f n) =
      ∑ r ∈ (oddSquarefreeRange (N / s)).filter (fun r => s.Coprime r), f (s * r) := by
  symm
  apply Finset.sum_bij (fun r _ => s * r)
  · intro r hr
    exact Finset.mem_filter.mpr
      ⟨(mem_oddSquarefreeRange_mul hs ho).mpr (Finset.mem_filter.mp hr), dvd_mul_right s r⟩
  · intro a _ b _ hab
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hs.ne_zero) hab
  · intro n hn
    obtain ⟨hn, hd⟩ := Finset.mem_filter.mp hn
    have he : s * (n / s) = n := Nat.mul_div_cancel' hd
    refine ⟨n / s, ?_, he⟩
    apply Finset.mem_filter.mpr
    exact (mem_oddSquarefreeRange_mul hs ho).mp (he.symm ▸ hn)
  · intro _ _
    rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticCoprimeEnergy
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Möbius expansion of the coprime quadratic bilinear form -/

namespace Ostmann

open scoped Classical BigOperators ComplexConjugate

 theorem coprime_mask_truncated (n₁ n₂ N : ℕ) (hn₂ : 0 < n₂) (hN : n₂ ≤ N) :
    (if n₁.Coprime n₂ then (1 : ℂ) else 0) =
      ∑ d ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius d : ℂ) *
        (if d ∣ n₁ then 1 else 0) * (if d ∣ n₂ then 1 else 0) := by
  have hc := congrArg (Int.cast : ℤ → ℂ) (coprime_mask_moebius n₂ n₁ hn₂.ne')
  simp only [Int.cast_ite, Int.cast_one, Int.cast_zero, Int.cast_sum] at hc
  rw [hc]
  have hsub : n₂.divisors ⊆ Finset.Icc 1 N := by
    intro d hd
    exact Finset.mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hd,
      (Nat.le_of_dvd hn₂ (Nat.dvd_of_mem_divisors hd)).trans hN⟩
  have hh := Finset.sum_subset hsub
    (f := fun d => (ArithmeticFunction.moebius d : ℂ) *
      (if d ∣ n₁ then 1 else 0) * (if d ∣ n₂ then 1 else 0)) (by
        intro d _ hd
        have hd₂ : ¬d ∣ n₂ := fun h => hd (Nat.mem_divisors.mpr ⟨h, hn₂.ne'⟩)
        simp [hd₂])
  rw [← hh]
  apply Finset.sum_congr rfl
  intro d hd
  simp only [Nat.dvd_of_mem_divisors hd, ite_true, if_true, mul_one]
  split_ifs <;> simp

private theorem coprime_kernel_coefficient (N n₁ n₂ : ℕ)
    (h₁ : n₁ ∈ oddSquarefreeRange N) (h₂ : n₂ ∈ oddSquarefreeRange N)
    (b : ℕ → ℂ) (m : ℤ) :
    (if n₁.gcd n₂ = 1 then
      b n₁ * conj (b n₂) * (jacobiSym m (quadraticPairKernel n₁ n₂) : ℂ) else 0) =
      ∑ d ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius d : ℂ) *
        (if d ∣ n₁ then b n₁ else 0) * conj (if d ∣ n₂ then b n₂ else 0) *
        (jacobiSym m n₁ : ℂ) * (jacobiSym m n₂ : ℂ) := by
  obtain ⟨hr₁, _, hs₁⟩ := Finset.mem_filter.mp h₁
  obtain ⟨hr₂, _, hs₂⟩ := Finset.mem_filter.mp h₂
  have hm := coprime_mask_truncated n₁ n₂ N
    (Finset.mem_Icc.mp hr₂).1 (Finset.mem_Icc.mp hr₂).2
  have hj : (if n₁.gcd n₂ = 1 then
      b n₁ * conj (b n₂) * (jacobiSym m (quadraticPairKernel n₁ n₂) : ℂ) else 0) =
      (b n₁ * conj (b n₂) * (jacobiSym m n₁ : ℂ) * (jacobiSym m n₂ : ℂ)) *
        (if n₁.Coprime n₂ then 1 else 0) := by
    by_cases h : n₁.Coprime n₂
    · have hg := h.gcd_eq_one
      rw [ite_eq_left hg, ite_eq_left h, mul_one]
      simp only [quadraticPairKernel, hg, Nat.div_one]
      rw [jacobiSym.mul_right' m hs₁.ne_zero hs₂.ne_zero]
      push_cast
      ring
    · have hg : n₁.gcd n₂ ≠ 1 := h
      rw [ite_eq_right hg, ite_eq_right h, mul_zero]
  rw [hj, hm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d _
  by_cases hd₁ : d ∣ n₁ <;> by_cases hd₂ : d ∣ n₂ <;>
    simp [hd₁, hd₂, mul_assoc, mul_left_comm, mul_comm]

 theorem quadratic_coprime_energy_expansion (N : ℕ) (b : ℕ → ℂ) (m : ℤ) :
    quadraticGcdKernelSum N 1 b m =
      ∑ d ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius d : ℂ) *
        (‖quadraticTransposeSum N (fun n => if d ∣ n then b n else 0) m‖ ^ 2 : ℂ) := by
  unfold quadraticGcdKernelSum quadraticGcdPairs
  rw [Finset.sum_filter]
  calc
    _ = ∑ z ∈ (oddSquarefreeRange N).product (oddSquarefreeRange N),
        ∑ d ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius d : ℂ) *
          (if d ∣ z.1 then b z.1 else 0) * conj (if d ∣ z.2 then b z.2 else 0) *
          (jacobiSym m z.1 : ℂ) * (jacobiSym m z.2 : ℂ) := by
      apply Finset.sum_congr rfl
      intro z hz
      exact coprime_kernel_coefficient N z.1 z.2
        (Finset.mem_product.mp hz).1 (Finset.mem_product.mp hz).2 b m
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro d _
      rw [quadraticTranspose_norm_sq_expand, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticDivisorBound
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The divisor loss in the quadratic-sieve iteration -/

namespace Ostmann

 theorem quadratic_divisor_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, n ≠ 0 → (n.divisors.card : ℝ) ≤ C * (n : ℝ) ^ ε := by
  obtain ⟨k, hk⟩ := exists_nat_gt (1 / ε)
  have hek : 1 < ε * k := by
    have hh := (div_lt_iff₀ hε).mp hk
    simpa only [mul_comm] using hh
  have hk0 : k ≠ 0 := by
    intro hz
    simp only [hz, Nat.cast_zero, mul_zero] at hek
    linarith
  obtain ⟨D, hD, hb⟩ := exists_divisors_power_bound k
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast hD
  refine ⟨D, by positivity, ?_⟩
  intro n hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
  have hnp : 0 < (n : ℝ) := lt_of_lt_of_le zero_lt_one hn1
  have hnb : (n : ℝ) ≤ (n : ℝ) ^ (ε * k) := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hn1 hek.le
  have hDp : (D : ℝ) ≤ (D : ℝ) ^ k := le_self_pow₀ hD1 hk0
  have hh : (n.divisors.card : ℝ) ^ k ≤ ((D : ℝ) * (n : ℝ) ^ ε) ^ k := by
    calc
      _ ≤ (D : ℝ) * n := by exact_mod_cast hb n hn
      _ ≤ (D : ℝ) ^ k * (n : ℝ) ^ (ε * k) :=
        mul_le_mul hDp hnb (by positivity) (by positivity)
      _ = _ := by rw [mul_pow, Real.rpow_mul hnp.le, Real.rpow_natCast]
  exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) hk0).mp hh

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticBilinearBound
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Cauchy bounds for two independently truncated coprime arrays -/

namespace Ostmann

open scoped Classical BigOperators ComplexConjugate

 theorem quadratic_divisibility_partial_energy (D N : ℕ) (b : ℕ → ℂ) :
    (∑ d ∈ Finset.Icc 1 D, quadraticSieveEnergy N (fun n => if d ∣ n then b n else 0)) ≤
      ∑ n ∈ oddSquarefreeRange N, (n.divisors.card : ℝ) * ‖b n‖ ^ 2 := by
  unfold quadraticSieveEnergy
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro n hn
  have hn0 := (Finset.mem_filter.mp hn).2.2.ne_zero
  have hsub : (Finset.Icc 1 D).filter (fun d => d ∣ n) ⊆ n.divisors := by
    intro d hd
    exact Nat.mem_divisors.mpr ⟨(Finset.mem_filter.mp hd).2, hn0⟩
  simp only [apply_ite, norm_zero, ite_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_le_card hsub) (sq_nonneg _)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticCoprimePoisson
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Poisson summation with an exact coprimality condition

The divisor terms are retained individually. They are the terms truncated in
Heath-Brown (1995), Lemma 13, for both small-kernel and dual-kernel sums.
-/

namespace Ostmann

open scoped Classical BigOperators FourierTransform SchwartzMap

 theorem quadratic_scaled_poisson (ψ : 𝓢(ℝ, ℂ)) {X : ℝ} (hX : 0 < X) :
    (∑' n : ℤ, ψ ((n : ℝ) / X)) = (X : ℂ) * ∑' n : ℤ, 𝓕 ψ ((n : ℝ) * X) := by
  have hp := (positiveDilate ψ X⁻¹ (inv_pos.mpr hX)).tsum_eq_tsum_fourier 0
  simpa [positiveDilate_apply, positiveDilate_fourier, inv_mul_eq_div,
    tsum_mul_left] using hp

 theorem quadratic_tsum_multiples {d : ℕ} (hd : d ≠ 0) (f : ℤ → ℂ) :
    (∑' n : ℤ, if (d : ℤ) ∣ n then f n else 0) = ∑' n : ℤ, f (d * n) := by
  have hd' : (d : ℤ) ≠ 0 := by exact_mod_cast hd
  have hi : Function.Injective (fun n : ℤ => (d : ℤ) * n) := mul_right_injective₀ hd'
  have hs : Function.support (fun n : ℤ => if (d : ℤ) ∣ n then f n else 0) ⊆
      Set.range (fun n : ℤ => (d : ℤ) * n) := by
    intro n hn
    by_cases h : (d : ℤ) ∣ n
    · obtain ⟨k, hk⟩ := h
      exact ⟨k, hk.symm⟩
    · simp [h] at hn
  simpa only [dvd_mul_right, ite_true, if_true] using (hi.tsum_eq hs).symm

 theorem quadratic_scaled_summable (ψ : 𝓢(ℝ, ℂ)) {X : ℝ} (hX : 0 < X) :
    Summable (fun n : ℤ => ‖ψ ((n : ℝ) / X)‖) := by
  simpa only [positiveDilate_apply, inv_mul_eq_div] using
    schwartz_int_norm_summable (positiveDilate ψ X⁻¹ (inv_pos.mpr hX))

 theorem quadratic_coprime_poisson {q : ℕ} [NeZero q]
    (ψ : 𝓢(ℝ, ℂ)) {X : ℝ} (hX : 0 < X) :
    (∑' n : ℤ, (1 : DirichletCharacter ℂ q) (n : ZMod q) * ψ ((n : ℝ) / X)) =
      ∑ d ∈ q.divisors, (ArithmeticFunction.moebius d : ℂ) * ((X / d : ℝ) : ℂ) *
        ∑' n : ℤ, 𝓕 ψ ((n : ℝ) * X / d) := by
  have hs (d : ℕ) : Summable (fun n : ℤ => (ArithmeticFunction.moebius d : ℂ) *
      (if (d : ℤ) ∣ n then ψ ((n : ℝ) / X) else 0)) := by
    apply Summable.of_norm_bounded
      ((quadratic_scaled_summable ψ hX).mul_left ‖(ArithmeticFunction.moebius d : ℂ)‖)
    intro n
    split_ifs
    · simp only [norm_mul, le_refl]
    · simp only [mul_zero, norm_zero]
      positivity
  calc
    _ = ∑' n : ℤ, ∑ d ∈ q.divisors, (ArithmeticFunction.moebius d : ℂ) *
        (if (d : ℤ) ∣ n then ψ ((n : ℝ) / X) else 0) := by
      apply tsum_congr
      intro n
      rw [principal_character_moebius, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro d _
      split_ifs <;> simp
    _ = ∑ d ∈ q.divisors, (ArithmeticFunction.moebius d : ℂ) *
        ∑' n : ℤ, if (d : ℤ) ∣ n then ψ ((n : ℝ) / X) else 0 := by
      rw [Summable.tsum_finsetSum (fun d _ => hs d)]
      simp only [tsum_mul_left]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d hd
      have hd0 : d ≠ 0 := (Nat.pos_of_mem_divisors hd).ne'
      have hdR : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero hd0
      rw [quadratic_tsum_multiples hd0]
      have he : (fun n : ℤ => ψ (((d * n : ℤ) : ℝ) / X)) =
          fun n : ℤ => ψ ((n : ℝ) / (X / d)) := by
        funext n
        congr 1
        push_cast
        field_simp
      rw [he, quadratic_scaled_poisson ψ (div_pos hX hdR)]
      simp only [mul_div_assoc, mul_assoc]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticGaussMultiplier
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Total quadratic Gauss multipliers and their elementary reciprocity sign -/

namespace Ostmann

open scoped Classical BigOperators

 theorem quadraticGaussMultiplier_norm {n : ℕ} (hn : Squarefree n) (ho : Odd n) :
    ‖quadraticGaussMultiplier n‖ = 1 := by
  rw [quadraticGaussMultiplier, dite_eq_right hn.ne_zero]
  exact @jacobiGaussPhase_norm n ⟨hn.ne_zero⟩ hn ho

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticPrimitivePoisson
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The first Poisson formula for the actual primitive Jacobi character -/

namespace Ostmann

open scoped BigOperators SchwartzMap FourierTransform

theorem quadratic_primitive_poisson {q : ℕ} [NeZero q]
    (hq : Squarefree q) (ho : Odd q) (ψ : 𝓢(ℝ, ℂ)) {X : ℝ} (hX : 0 < X) :
    (∑' n : ℤ, (jacobiSym n q : ℂ) * ψ ((n : ℝ) / X)) =
      (X : ℂ) / q * gaussSum (jacobiComplex q) ZMod.stdAddChar *
        ∑' h : ℤ, (jacobiSym h q : ℂ) * 𝓕 ψ ((h : ℝ) * X / q) := by
  have hp := scaled_periodic_poisson (jacobiComplex q) ψ X hX
  simp_rw [jacobiComplex_intCast] at hp
  rw [hp]
  simp_rw [primitive_character_fourier _ (jacobiComplex_squarefree_primitive q hq ho),
    (jacobiComplex_isQuadratic q).inv, neg_neg, jacobiComplex_intCast]
  rw [← tsum_mul_left, ← tsum_mul_left]
  apply tsum_congr
  intro h
  ring

theorem quadratic_primitive_poisson_normalized {q : ℕ} [NeZero q]
    (hq : Squarefree q) (ho : Odd q) (ψ : 𝓢(ℝ, ℂ)) {X : ℝ} (hX : 0 < X) :
    (∑' n : ℤ, (jacobiSym n q : ℂ) * ψ ((n : ℝ) / X)) =
      quadraticGaussMultiplier q * ((X / Real.sqrt q : ℝ) : ℂ) *
        ∑' h : ℤ, (jacobiSym h q : ℂ) * 𝓕 ψ ((h : ℝ) * X / q) := by
  rw [quadratic_primitive_poisson hq ho ψ hX]
  congr 1
  rw [quadraticGaussMultiplier, dite_eq_right (NeZero.ne q), jacobiGaussPhase,
    Complex.ofReal_div]
  have hs : (Real.sqrt (q : ℝ) : ℂ) ^ 2 = q := by
    exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg q)
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne q
  have hsC : (Real.sqrt (q : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (show (0 : ℝ) < q by exact_mod_cast NeZero.pos q)).ne'
  field_simp
  linear_combination (X : ℂ) * gaussSum (jacobiComplex q) ZMod.stdAddChar * hs

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticCoprimeJacobiPoisson
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The first transform with every original Mobius divisor retained -/

namespace Ostmann

open scoped Classical BigOperators FourierTransform SchwartzMap

private theorem jacobi_norm_le (n : ℤ) (q : ℕ) : ‖(jacobiSym n q : ℂ)‖ ≤ 1 := by
  rcases jacobiSym.trichotomy n q with h | h | h <;> rw [h] <;> norm_num

theorem quadratic_coprime_jacobi_poisson {D q : ℕ} [NeZero D] [NeZero q]
    (hq : Squarefree q) (ho : Odd q) (ψ : 𝓢(ℝ, ℂ)) {X : ℝ} (hX : 0 < X) :
    (∑' n : ℤ, (1 : DirichletCharacter ℂ D) (n : ZMod D) *
      (jacobiSym n q : ℂ) * ψ ((n : ℝ) / X)) =
    quadraticGaussMultiplier q *
      ∑ e ∈ D.divisors, (ArithmeticFunction.moebius e : ℂ) *
        ((X / ((e : ℝ) * Real.sqrt q) : ℝ) : ℂ) *
        ∑' h : ℤ, (jacobiSym ((e : ℤ) * h) q : ℂ) *
          𝓕 ψ ((h : ℝ) * X / ((e : ℝ) * q)) := by
  have hs (e : ℕ) : Summable (fun n : ℤ => (ArithmeticFunction.moebius e : ℂ) *
      (if (e : ℤ) ∣ n then (jacobiSym n q : ℂ) * ψ ((n : ℝ) / X) else 0)) := by
    apply Summable.of_norm_bounded
      ((quadratic_scaled_summable ψ hX).mul_left ‖(ArithmeticFunction.moebius e : ℂ)‖)
    intro n
    split_ifs
    · simp only [norm_mul]
      exact mul_le_mul_of_nonneg_left
        ((mul_le_mul_of_nonneg_right (jacobi_norm_le n q) (norm_nonneg _)).trans_eq (one_mul _))
        (norm_nonneg _)
    · simp only [mul_zero, norm_zero]
      positivity
  calc
    _ = ∑' n : ℤ, ∑ e ∈ D.divisors, (ArithmeticFunction.moebius e : ℂ) *
        (if (e : ℤ) ∣ n then (jacobiSym n q : ℂ) * ψ ((n : ℝ) / X) else 0) := by
      apply tsum_congr
      intro n
      rw [principal_character_moebius, Finset.sum_mul, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro e _
      split_ifs <;> simp [mul_assoc]
    _ = ∑ e ∈ D.divisors, (ArithmeticFunction.moebius e : ℂ) *
        ∑' n : ℤ, if (e : ℤ) ∣ n then (jacobiSym n q : ℂ) * ψ ((n : ℝ) / X) else 0 := by
      rw [Summable.tsum_finsetSum (fun e _ => hs e)]
      simp only [tsum_mul_left]
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e he
      have he₀ := Nat.pos_of_mem_divisors he
      have heR : (0 : ℝ) < e := by exact_mod_cast he₀
      rw [quadratic_tsum_multiples he₀.ne']
      have hterm (n : ℤ) :
          (jacobiSym ((e : ℤ) * n) q : ℂ) * ψ (((e : ℤ) * n : ℤ) / X) =
            (jacobiSym (e : ℤ) q : ℂ) *
              ((jacobiSym n q : ℂ) * ψ ((n : ℝ) / (X / e))) := by
        rw [jacobiSym.mul_left, Int.cast_mul]
        have ha : (((e : ℤ) * n : ℤ) : ℝ) / X = (n : ℝ) / (X / e) := by
          push_cast
          field_simp
        rw [ha]
        ring
      simp_rw [hterm]
      rw [tsum_mul_left, quadratic_primitive_poisson_normalized hq ho ψ (div_pos hX heR)]
      have hfreq (h : ℤ) : (h : ℝ) * (X / e) / q = (h : ℝ) * X / ((e : ℝ) * q) := by ring
      simp_rw [hfreq]
      have hchars : (∑' h : ℤ, (jacobiSym ((e : ℤ) * h) q : ℂ) *
          𝓕 ψ ((h : ℝ) * X / ((e : ℝ) * q))) =
          (jacobiSym (e : ℤ) q : ℂ) * ∑' h : ℤ, (jacobiSym h q : ℂ) *
            𝓕 ψ ((h : ℝ) * X / ((e : ℝ) * q)) := by
        simp only [jacobiSym.mul_left, Int.cast_mul, mul_assoc, tsum_mul_left]
      rw [hchars, div_div]
      ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticTotientMain
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact totient coefficient of the coprime Poisson main term -/

namespace Ostmann

open scoped Classical BigOperators

 theorem quadratic_totient_moebius (q : ℕ) (hq : q ≠ 0) :
    (∑ d ∈ q.divisors, (ArithmeticFunction.moebius d : ℝ) / d) = (q.totient : ℝ) / q := by
  have hsum (n : ℕ) (_hn : 0 < n) :
      (∑ d ∈ n.divisors, (d.totient : ℝ)) = (n : ℝ) := by
    exact_mod_cast Nat.sum_totient n
  have hm := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq (R := ℝ)).mp hsum
    q (Nat.pos_of_ne_zero hq)
  have hm' := (Nat.sum_divisorsAntidiagonal (n := q)
    (fun d e => (ArithmeticFunction.moebius d : ℝ) * (e : ℝ))).symm.trans hm
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq
  apply (mul_right_cancel₀ hqR)
  rw [div_mul_cancel₀ _ hqR, Finset.sum_mul]
  calc
    _ = ∑ d ∈ q.divisors, (ArithmeticFunction.moebius d : ℝ) * ((q / d : ℕ) : ℝ) := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [Nat.cast_div (Nat.dvd_of_mem_divisors hd)
        (by exact_mod_cast (Nat.pos_of_mem_divisors hd).ne' : (d : ℝ) ≠ 0)]
      ring
    _ = _ := hm'

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticCoprimeMain
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Separating the exact main term in coprime Poisson summation -/

namespace Ostmann

open scoped Classical BigOperators FourierTransform SchwartzMap

 theorem quadratic_coprime_main {q : ℕ} [NeZero q]
    (ψ : 𝓢(ℝ, ℂ)) {X : ℝ} (hX : 0 < X) :
    (∑' n : ℤ, (1 : DirichletCharacter ℂ q) (n : ZMod q) * ψ ((n : ℝ) / X)) =
      ((X : ℂ) * q.totient / q) * 𝓕 ψ 0 + quadraticCoprimeRemainder q ψ X := by
  have hs (d : ℕ) (hd : d ∈ q.divisors) :
      (∑' n : ℤ, 𝓕 ψ ((n : ℝ) * X / d)) = 𝓕 ψ 0 +
        ∑' n : ℤ, if n = 0 then 0 else 𝓕 ψ ((n : ℝ) * X / d) := by
    have hdR : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_mem_divisors hd
    have hnorm := quadratic_scaled_summable (𝓕 ψ) (div_pos hdR hX)
    have hsum : Summable (fun n : ℤ => 𝓕 ψ ((n : ℝ) * X / d)) := by
      apply Summable.of_norm
      simpa only [div_div_eq_mul_div] using hnorm
    simpa only [Int.cast_zero, zero_mul, zero_div] using hsum.tsum_eq_add_tsum_ite 0
  have hcoef : (∑ d ∈ q.divisors,
      (ArithmeticFunction.moebius d : ℂ) * ((X / d : ℝ) : ℂ)) = (X : ℂ) * q.totient / q := by
    have ht := congrArg (fun x : ℝ => (x : ℂ)) (quadratic_totient_moebius q (NeZero.ne q))
    simp only [Complex.ofReal_sum, Complex.ofReal_div, Complex.ofReal_intCast,
      Complex.ofReal_natCast] at ht
    calc
      _ = (X : ℂ) * ∑ d ∈ q.divisors, (ArithmeticFunction.moebius d : ℂ) / d := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro d _
        push_cast
        ring
      _ = _ := by rw [ht]; ring
  rw [quadratic_coprime_poisson ψ hX]
  calc
    _ = ∑ d ∈ q.divisors,
        ((ArithmeticFunction.moebius d : ℂ) * ((X / d : ℝ) : ℂ) * 𝓕 ψ 0 +
        (ArithmeticFunction.moebius d : ℂ) * ((X / d : ℝ) : ℂ) *
          ∑' n : ℤ, if n = 0 then 0 else 𝓕 ψ ((n : ℝ) * X / d)) := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [hs d hd, mul_add]
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, hcoef]
      rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticDivisorFamily
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Summing the two divisor ranges in Heath-Brown's bilinear comparison -/

namespace Ostmann

open scoped Classical BigOperators

 theorem quadraticDivisorWeight_nonneg (N s : ℕ) (a : ℕ → ℂ) :
    0 ≤ quadraticDivisorWeight N s a := by
  apply Finset.sum_nonneg
  intro n _
  positivity

 theorem quadratic_divisor_weight_sum (N : ℕ) (S : Finset ℕ) (a : ℕ → ℂ) :
    (∑ s ∈ S, quadraticDivisorWeight N s a) ≤ quadraticDivisorMoment N a := by
  unfold quadraticDivisorWeight quadraticDivisorMoment
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro n hn
  have hn0 := (Finset.mem_filter.mp hn).2.2.ne_zero
  have hsub : S.filter (fun s => s ∣ n) ⊆ n.divisors := by
    intro s hs
    exact Nat.mem_divisors.mpr ⟨(Finset.mem_filter.mp hs).2, hn0⟩
  have hc : ((S.filter (fun s => s ∣ n)).card : ℝ) ≤ n.divisors.card := by
    exact_mod_cast Finset.card_le_card hsub
  simp only [apply_ite, norm_zero, ite_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, mul_zero, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  calc
    _ ≤ (n.divisors.card : ℝ) * ((n.divisors.card : ℝ) * ‖a n‖ ^ 2) :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    _ = _ := by ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticDivisorMomentBound
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Absorbing the divisor moment by an arbitrarily small power -/

namespace Ostmann

open scoped Classical BigOperators

 theorem quadratic_divisor_moment_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, ∀ a : ℕ → ℂ,
      quadraticDivisorMoment N a ≤ C * (N : ℝ) ^ ε * quadraticSieveEnergy N a := by
  obtain ⟨C, hC, hc⟩ := quadratic_divisor_bound (ε / 2) (by positivity)
  refine ⟨C ^ 2, by positivity, ?_⟩
  intro N a
  unfold quadraticDivisorMoment quadraticSieveEnergy
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  have hn0 := (Finset.mem_filter.mp hn).2.2.ne_zero
  have hnN : (n : ℝ) ≤ N := by
    exact_mod_cast (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).2
  have hdiv : (n.divisors.card : ℝ) ≤ C * (N : ℝ) ^ (ε / 2) :=
    (hc n hn0).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg _) hnN (by positivity)) hC.le)
  have hsq := pow_le_pow_left₀ (Nat.cast_nonneg n.divisors.card) hdiv 2
  have he : (C * (N : ℝ) ^ (ε / 2)) ^ 2 = C ^ 2 * (N : ℝ) ^ ε := by
    rw [mul_pow]
    congr 1
    calc
      _ = ((N : ℝ) ^ (ε / 2)) ^ (2 : ℝ) := (Real.rpow_natCast _ 2).symm
      _ = (N : ℝ) ^ ((ε / 2) * 2) := (Real.rpow_mul (Nat.cast_nonneg N) _ _).symm
      _ = _ := by congr 1; ring
  rw [he] at hsq
  exact mul_le_mul_of_nonneg_right hsq (sq_nonneg _)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticDyadicDivisors
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A disjoint dyadic partition of the actual odd-squarefree divisors -/

namespace Ostmann

open scoped Classical BigOperators

 theorem quadraticDyadicDivisors_bounds {N j s : ℕ}
    (hs : s ∈ quadraticDyadicDivisors N j) : 2 ^ j ≤ s ∧ s < 2 ^ (j + 1) := by
  obtain ⟨hs, hj⟩ := Finset.mem_filter.mp hs
  have hn := (Finset.mem_filter.mp hs).2.2.ne_zero
  have hlo := Nat.pow_log_le_self 2 hn
  have hhi := Nat.lt_pow_succ_log_self (by decide : 1 < 2) s
  rw [hj] at hlo hhi
  exact ⟨hlo, hhi⟩

 theorem quadratic_dyadic_divisors_sum {R : Type*} [AddCommMonoid R]
    (N : ℕ) (f : ℕ → R) :
    (∑ j ∈ Finset.range (Nat.log 2 N + 1), ∑ s ∈ quadraticDyadicDivisors N j, f s) =
      ∑ s ∈ oddSquarefreeRange N, f s := by
  simp only [quadraticDyadicDivisors, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s hs
  have hle : Nat.log 2 s < Nat.log 2 N + 1 := by
    have hh := Nat.log_mono_right (b := 2)
      (Finset.mem_Icc.mp (Finset.mem_filter.mp hs).1).2
    omega
  simp only [Finset.sum_ite_eq, Finset.mem_range, hle, ite_true, if_true]

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

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticSquareCompose
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual square-composed Schwartz test for the second Poisson step -/

namespace Ostmann

open MeasureTheory
open scoped SchwartzMap FourierTransform

 theorem quadraticSquareCompose_apply (ρ : 𝓢(ℝ, ℂ)) (a : ℝ) (ha : 1 ≤ |a|) (x : ℝ) :
    quadraticSquareCompose ρ a ha x = ρ (a * x ^ 2) := rfl

 theorem quadraticSquareCompose_even (ρ : 𝓢(ℝ, ℂ)) (a : ℝ) (ha : 1 ≤ |a|) :
    Function.Even (quadraticSquareCompose ρ a ha) := by
  intro x
  simp only [quadraticSquareCompose_apply, neg_sq]

 theorem quadraticFourierSquare_apply (ρ : 𝓢(ℝ, ℂ)) (a : ℝ) (ha : 1 ≤ |a|) (x : ℝ) :
    quadraticFourierSquare ρ a ha x = 𝓕 ρ (a * x ^ 2) := rfl

 theorem quadraticFourierSquare_even (ρ : 𝓢(ℝ, ℂ)) (a : ℝ) (ha : 1 ≤ |a|) :
    Function.Even (quadraticFourierSquare ρ a ha) :=
  quadraticSquareCompose_even _ _ _

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticDampedFresnel
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Gaussian regularization of the quadratic Fourier integral -/

namespace Ostmann

open MeasureTheory
open scoped SchwartzMap FourierTransform

 theorem quadraticGaussianDamping_integrable {ε : ℝ} (hε : 0 < ε) :
    Integrable (quadraticGaussianDamping ε) :=
  integrable_cexp_neg_mul_sq (by simpa using mul_pos Real.pi_pos hε)

 theorem quadratic_gaussian_phase_identity (ε a t x : ℝ) :
    quadraticGaussianDamping ε x * realAdditivePhase (-(t * (a * x ^ 2))) =
      Complex.exp (-((Real.pi : ℂ) * ((ε : ℂ) + 2 * Complex.I * (a * t : ℝ))) *
        (x : ℂ) ^ 2) := by
  unfold quadraticGaussianDamping realAdditivePhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

 theorem quadratic_damped_fresnel_integrable (ρ : 𝓢(ℝ, ℂ))
    {ε : ℝ} (hε : 0 < ε) (a : ℝ) :
    Integrable (fun p : ℝ × ℝ => quadraticGaussianDamping ε p.1 *
      realAdditivePhase (-(p.2 * (a * p.1 ^ 2))) * ρ p.2) := by
  have hi : Integrable (fun p : ℝ × ℝ => ‖quadraticGaussianDamping ε p.1‖ * ‖ρ p.2‖)
      (volume.prod volume) :=
    (quadraticGaussianDamping_integrable hε).norm.mul_prod ρ.integrable.norm
  apply hi.mono'
  · apply Continuous.aestronglyMeasurable
    unfold quadraticGaussianDamping realAdditivePhase
    fun_prop
  · filter_upwards with p
    simp only [norm_mul, norm_realAdditivePhase, mul_one]
    rfl

 theorem quadratic_damped_fresnel (ρ : 𝓢(ℝ, ℂ)) {ε : ℝ} (hε : 0 < ε) (a : ℝ) :
    (∫ x : ℝ, quadraticGaussianDamping ε x * 𝓕 ρ (a * x ^ 2)) =
      ∫ t : ℝ, ((1 : ℂ) / ((ε : ℂ) + 2 * Complex.I * (a * t : ℝ))) ^ (1 / 2 : ℂ) * ρ t := by
  have hprod := quadratic_damped_fresnel_integrable ρ hε a
  calc
    _ = ∫ x : ℝ, ∫ t : ℝ, quadraticGaussianDamping ε x *
        realAdditivePhase (-(t * (a * x ^ 2))) * ρ t := by
      apply integral_congr_ae
      filter_upwards with x
      rw [quadratic_fourier_phase_integral, ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with t
      ring
    _ = ∫ t : ℝ, ∫ x : ℝ, quadraticGaussianDamping ε x *
        realAdditivePhase (-(t * (a * x ^ 2))) * ρ t := integral_integral_swap hprod
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with t
      simp_rw [quadratic_gaussian_phase_identity]
      rw [integral_mul_const]
      have hp : 0 < (((Real.pi : ℂ) * ((ε : ℂ) + 2 * Complex.I * (a * t : ℝ)))).re := by
        simpa using mul_pos Real.pi_pos hε
      rw [integral_gaussian_complex hp]
      have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      have he : (Real.pi : ℂ) /
          ((Real.pi : ℂ) * ((ε : ℂ) + 2 * Complex.I * (a * t : ℝ))) =
          1 / ((ε : ℂ) + 2 * Complex.I * (a * t : ℝ)) := by
        rw [div_mul_eq_div_div, div_self hpi]
      rw [he]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticDampingLimit
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing the Gaussian damping from the quadratic Fourier side -/

namespace Ostmann

open MeasureTheory Filter
open scoped SchwartzMap FourierTransform Topology

 theorem quadraticGaussianDamping_norm_le {ε : ℝ} (hε : 0 ≤ ε) (x : ℝ) :
    ‖quadraticGaussianDamping ε x‖ ≤ 1 := by
  rw [quadraticGaussianDamping, Complex.norm_exp]
  have he : -((Real.pi * ε : ℝ) : ℂ) * (x : ℂ) ^ 2 =
      ((-(Real.pi * ε * x ^ 2) : ℝ) : ℂ) := by push_cast; ring
  rw [he, Complex.ofReal_re, Real.exp_le_one_iff]
  exact neg_nonpos.mpr (by positivity)

 theorem quadraticGaussianDamping_limit (x : ℝ) :
    Tendsto (fun n : ℕ => quadraticGaussianDamping (1 / ((n : ℝ) + 1)) x)
      atTop (𝓝 1) := by
  have hc : Continuous (fun ε : ℝ => quadraticGaussianDamping ε x) := by
    unfold quadraticGaussianDamping
    fun_prop
  have ht := hc.continuousAt.tendsto.comp
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  simpa [quadraticGaussianDamping, Function.comp_def] using ht

 theorem quadratic_damped_fourier_integral_limit (ρ : 𝓢(ℝ, ℂ))
    (a : ℝ) (ha : 1 ≤ |a|) :
    Tendsto (fun n : ℕ => ∫ x : ℝ,
      quadraticGaussianDamping (1 / ((n : ℝ) + 1)) x * 𝓕 ρ (a * x ^ 2))
      atTop (𝓝 (∫ x : ℝ, 𝓕 ρ (a * x ^ 2))) := by
  apply tendsto_integral_of_dominated_convergence (fun x : ℝ => ‖𝓕 ρ (a * x ^ 2)‖)
  · intro n
    apply Continuous.aestronglyMeasurable
    apply Continuous.mul
    · unfold quadraticGaussianDamping
      fun_prop
    · exact (𝓕 ρ : 𝓢(ℝ, ℂ)).continuous.comp (by fun_prop)
  · exact (quadraticFourierSquare ρ a ha).integrable.norm
  · intro n
    filter_upwards with x
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right
      (quadraticGaussianDamping_norm_le (by positivity) x) (norm_nonneg _)).trans_eq (one_mul _)
  · filter_upwards with x
    simpa only [one_mul] using (quadraticGaussianDamping_limit x).mul_const (𝓕 ρ (a * x ^ 2))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticSquarefreePart
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Unique square-times-squarefree decomposition for the Poisson comparison -/

namespace Ostmann

 theorem quadraticSquarePart_factor (m : ℕ) :
    quadraticSquarePart m ^ 2 * quadraticSquarefreePart m = m :=
  (Classical.choose_spec (Classical.choose_spec (exists_quadratic_factor m))).1

 theorem quadraticSquarefreePart_squarefree (m : ℕ) :
    Squarefree (quadraticSquarefreePart m) :=
  (Classical.choose_spec (Classical.choose_spec (exists_quadratic_factor m))).2

 theorem quadraticSquarePart_pos {m : ℕ} (hm : 0 < m) : 0 < quadraticSquarePart m := by
  have hh := quadraticSquarePart_factor m
  by_contra h
  have hz : quadraticSquarePart m = 0 := by omega
  simp only [hz, zero_pow (by decide : 2 ≠ 0), zero_mul] at hh
  omega

 theorem quadraticSquarefreePart_pos (m : ℕ) : 0 < quadraticSquarefreePart m :=
  Nat.pos_of_ne_zero (quadraticSquarefreePart_squarefree m).ne_zero

 theorem quadratic_squarefree_factor_unique {a b c d : ℕ}
    (ha : a ≠ 0) (hc : c ≠ 0) (hb : Squarefree b) (hd : Squarefree d)
    (he : a ^ 2 * b = c ^ 2 * d) : a = c ∧ b = d := by
  have hbd : b = d := by
    apply Nat.eq_of_factorization_eq hb.ne_zero hd.ne_zero
    intro p
    have hf := congrArg (fun n : ℕ => n.factorization p) he
    rw [Nat.factorization_mul (pow_ne_zero _ ha) hb.ne_zero,
      Nat.factorization_mul (pow_ne_zero _ hc) hd.ne_zero,
      Nat.factorization_pow, Nat.factorization_pow] at hf
    simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul] at hf
    have hb' := hb.natFactorization_le_one p
    have hd' := hd.natFactorization_le_one p
    omega
  subst d
  have hs : a ^ 2 = c ^ 2 := mul_right_cancel₀ hb.ne_zero he
  have hac : a = c := by nlinarith
  exact ⟨hac, rfl⟩

 theorem quadraticSquarefreePart_of_mul_square {a b : ℕ} (ha : a ≠ 0)
    (hb : Squarefree b) : quadraticSquarePart (a ^ 2 * b) = a ∧
      quadraticSquarefreePart (a ^ 2 * b) = b := by
  exact quadratic_squarefree_factor_unique
    (quadraticSquarePart_pos (Nat.pos_of_ne_zero (mul_ne_zero (pow_ne_zero _ ha) hb.ne_zero))).ne'
    ha (quadraticSquarefreePart_squarefree _) hb (quadraticSquarePart_factor _)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticSmallKernels
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact finite reindexing of the small-squarefree-kernel contribution -/

namespace Ostmann

open scoped Classical BigOperators

 theorem quadraticSquarePart_le {m : ℕ} (hm : 0 < m) : quadraticSquarePart m ≤ m := by
  have ha := quadraticSquarePart_pos hm
  have hb := quadraticSquarefreePart_pos m
  have he := quadraticSquarePart_factor m
  nlinarith [Nat.mul_le_mul_left (quadraticSquarePart m ^ 2) hb]

 theorem quadraticSquarefreePart_dvd (m : ℕ) : quadraticSquarefreePart m ∣ m :=
  ⟨quadraticSquarePart m ^ 2, by rw [mul_comm, quadraticSquarePart_factor]⟩

 theorem quadraticSquarePart_dvd (m : ℕ) : quadraticSquarePart m ∣ m :=
  ⟨quadraticSquarePart m * quadraticSquarefreePart m,
    by rw [← mul_assoc, ← pow_two, quadraticSquarePart_factor]⟩

 theorem sum_quadraticSmallKernelRange {R : Type*} [AddCommMonoid R]
    (M K : ℕ) (f : ℕ → R) :
    (∑ m ∈ quadraticSmallKernelRange M K, f m) =
      ∑ z ∈ quadraticSmallKernelPairs M K, f (z.1 ^ 2 * z.2) := by
  symm
  apply Finset.sum_bij (fun z _ => z.1 ^ 2 * z.2)
  · intro z hz
    obtain ⟨hz, ho, hb⟩ := Finset.mem_filter.mp hz
    obtain ⟨ha, hk⟩ := Finset.mem_product.mp hz
    obtain ⟨hkr, hko, hks⟩ := Finset.mem_filter.mp hk
    have ha0 : z.1 ≠ 0 := by have := (Finset.mem_Icc.mp ha).1; omega
    have hf := (quadraticSquarefreePart_of_mul_square ha0 hks).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨?_, hb⟩, ?_, ?_⟩
    · exact Nat.mul_pos (pow_pos (Nat.pos_of_ne_zero ha0) _) (Finset.mem_Icc.mp hkr).1
    · exact ho.pow.mul hko
    · rw [hf]
      exact (Finset.mem_Icc.mp hkr).2
  · intro z hz w hw he
    obtain ⟨hz, _, _⟩ := Finset.mem_filter.mp hz
    obtain ⟨hw, _, _⟩ := Finset.mem_filter.mp hw
    obtain ⟨hza, hzb⟩ := Finset.mem_product.mp hz
    obtain ⟨hwa, hwb⟩ := Finset.mem_product.mp hw
    have ha : z.1 ≠ 0 := by have := (Finset.mem_Icc.mp hza).1; omega
    have hc : w.1 ≠ 0 := by have := (Finset.mem_Icc.mp hwa).1; omega
    have hh := quadratic_squarefree_factor_unique ha hc
      (Finset.mem_filter.mp hzb).2.2 (Finset.mem_filter.mp hwb).2.2 he
    exact Prod.ext hh.1 hh.2
  · intro m hm
    obtain ⟨hr, ho, hk⟩ := Finset.mem_filter.mp hm
    have hm0 : 0 < m := (Finset.mem_Icc.mp hr).1
    refine ⟨(quadraticSquarePart m, quadraticSquarefreePart m), ?_, quadraticSquarePart_factor m⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, ?_, ?_⟩
    · exact Finset.mem_Icc.mpr ⟨quadraticSquarePart_pos hm0,
        (quadraticSquarePart_le hm0).trans (Finset.mem_Icc.mp hr).2⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
        ⟨quadraticSquarefreePart_pos m, hk⟩,
        ho.of_dvd_nat (quadraticSquarefreePart_dvd m), quadraticSquarefreePart_squarefree m⟩
    · exact ho.of_dvd_nat (quadraticSquarePart_dvd m)
    · rw [quadraticSquarePart_factor]
      exact (Finset.mem_Icc.mp hr).2
  · intro _ _
    rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticGcdReduction
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing the actual gcd from the quadratic pair family -/

namespace Ostmann

open scoped Classical BigOperators

 theorem quadratic_gcd_pair_reindex {N D : ℕ} (hD : Squarefree D) (hDo : Odd D)
    (F : ℕ → ℕ → ℂ) :
    (∑ z ∈ quadraticGcdPairs N D, F z.1 z.2) =
      ∑ z ∈ quadraticGcdPairs (N / D) 1,
        if D.Coprime z.1 ∧ D.Coprime z.2 then F (D * z.1) (D * z.2) else 0 := by
  let P := (quadraticGcdPairs (N / D) 1).filter
    (fun z => D.Coprime z.1 ∧ D.Coprime z.2)
  have hsum : (∑ z ∈ P, F (D * z.1) (D * z.2)) =
      ∑ z ∈ quadraticGcdPairs (N / D) 1,
        if D.Coprime z.1 ∧ D.Coprime z.2 then F (D * z.1) (D * z.2) else 0 := by
    exact Finset.sum_filter _ _
  rw [← hsum]
  symm
  apply Finset.sum_bij (fun z _ => (D * z.1, D * z.2))
  · intro z hz
    obtain ⟨hz, hcop⟩ := Finset.mem_filter.mp hz
    obtain ⟨hz, hg⟩ := Finset.mem_filter.mp hz
    obtain ⟨h₁, h₂⟩ := Finset.mem_product.mp hz
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨
      (mem_oddSquarefreeRange_mul hD hDo).mpr ⟨h₁, hcop.1⟩,
      (mem_oddSquarefreeRange_mul hD hDo).mpr ⟨h₂, hcop.2⟩⟩, ?_⟩
    simp only [Nat.gcd_mul_left, hg, mul_one]
  · intro z _ y _ heq
    apply Prod.ext
    · have hh := congrArg Prod.fst heq
      exact mul_left_cancel₀ hD.ne_zero hh
    · have hh := congrArg Prod.snd heq
      exact mul_left_cancel₀ hD.ne_zero hh
  · intro z hz
    obtain ⟨hz, hg⟩ := Finset.mem_filter.mp hz
    obtain ⟨h₁, h₂⟩ := Finset.mem_product.mp hz
    have hd₁ : D ∣ z.1 := hg ▸ Nat.gcd_dvd_left z.1 z.2
    have hd₂ : D ∣ z.2 := hg ▸ Nat.gcd_dvd_right z.1 z.2
    have he₁ : D * (z.1 / D) = z.1 := Nat.mul_div_cancel' hd₁
    have he₂ : D * (z.2 / D) = z.2 := Nat.mul_div_cancel' hd₂
    have hr₁ := (mem_oddSquarefreeRange_mul hD hDo).mp (he₁ ▸ h₁)
    have hr₂ := (mem_oddSquarefreeRange_mul hD hDo).mp (he₂ ▸ h₂)
    refine ⟨(z.1 / D, z.2 / D), ?_, Prod.ext he₁ he₂⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hr₁.1, hr₂.1⟩, ?_⟩,
      hr₁.2, hr₂.2⟩
    have hc := Nat.coprime_div_gcd_div_gcd
      (Nat.gcd_pos_of_pos_left z.2 (Finset.mem_Icc.mp (Finset.mem_filter.mp h₁).1).1)
    rwa [hg] at hc
  · intro _ _
    rfl

 theorem quadraticPairKernel_mul_coprime {D a b : ℕ} (hD : D ≠ 0)
    (hab : a.Coprime b) : quadraticPairKernel (D * a) (D * b) = a * b := by
  have hg : (D * a).gcd (D * b) = D := by simp [Nat.gcd_mul_left, hab.gcd_eq_one]
  rw [quadraticPairKernel, hg]
  simp only [Nat.mul_div_right _ (Nat.pos_of_ne_zero hD)]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticSmallKernelCharacter
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The literal character after the small-kernel reindexing -/

namespace Ostmann

open scoped Classical BigOperators ComplexConjugate

 theorem jacobi_square_mul (a : ℕ) (b : ℤ) {q : ℕ} (hq : q ≠ 0) :
    jacobiSym ((a : ℤ) ^ 2 * b) q =
      if a.Coprime q then jacobiSym b q else 0 := by
  rw [jacobiSym.mul_left, jacobiSym.pow_left]
  split_ifs with h
  · rw [jacobiSym.sq_one (by exact h), one_mul]
  · rw [(jacobiSym.eq_zero_iff).mpr ⟨hq, by exact h⟩,
      zero_pow (by decide : 2 ≠ 0), zero_mul]

 theorem jacobi_pair_square_mul (a b : ℕ) {n₁ n₂ : ℕ}
    (h₁ : Squarefree n₁) (h₂ : Squarefree n₂) :
    (jacobiSym (a ^ 2 * b : ℕ) n₁ : ℂ) * (jacobiSym (a ^ 2 * b : ℕ) n₂ : ℂ) =
      (if a.Coprime (n₁ * n₂) then (1 : ℂ) else 0) *
      (if b.Coprime (n₁.gcd n₂) then (1 : ℂ) else 0) *
      (jacobiSym b (quadraticPairKernel n₁ n₂) : ℂ) := by
  have ht : n₁ * n₂ ≠ 0 := mul_ne_zero h₁.ne_zero h₂.ne_zero
  rw [← Int.cast_mul, ← jacobiSym.mul_right' _ h₁.ne_zero h₂.ne_zero]
  push_cast
  rw [jacobi_square_mul _ _ ht]
  have hb := jacobi_pair_kernel h₁ h₂ (b : ℤ)
  rw [← jacobiSym.mul_right' _ h₁.ne_zero h₂.ne_zero] at hb
  have hb' : jacobiSym (b : ℤ) (n₁ * n₂) =
      if b.Coprime (n₁.gcd n₂) then jacobiSym (b : ℤ) (quadraticPairKernel n₁ n₂) else 0 := hb
  rw [hb']
  split_ifs <;> simp

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticFresnelCoefficient
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform control of the regularized quadratic Gaussian coefficient -/

namespace Ostmann

open MeasureTheory Filter
open scoped Topology

 theorem quadraticFresnelCoefficient_norm_le (ε : ℝ) {a t : ℝ}
    (ha : 1 ≤ |a|) (ht : 1 / 2 ≤ t) : ‖quadraticFresnelCoefficient ε a t‖ ≤ 1 := by
  let z : ℂ := (ε : ℂ) + 2 * Complex.I * (a * t : ℝ)
  have ht₀ : 0 ≤ t := by linarith
  have him : z.im = 2 * a * t := by simp [z]; ring
  have hn : 1 ≤ ‖z‖ := by
    have hh := Complex.abs_im_le_norm z
    rw [him, abs_mul, abs_mul, abs_of_nonneg ht₀] at hh
    norm_num at hh
    nlinarith
  have hi : ‖(1 : ℂ) / z‖ ≤ 1 := by
    rw [norm_div, norm_one]
    exact (div_le_one (by linarith : 0 < ‖z‖)).mpr hn
  change ‖((1 : ℂ) / z) ^ (1 / 2 : ℂ)‖ ≤ 1
  have he : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by norm_num
  rw [he, Complex.norm_cpow_real]
  exact Real.rpow_le_one (norm_nonneg _) hi (by norm_num)

 theorem quadraticFresnelCoefficient_continuousAt_zero {a t : ℝ} (hat : a * t ≠ 0) :
    ContinuousAt (fun ε : ℝ => quadraticFresnelCoefficient ε a t) 0 := by
  let z : ℂ := 2 * Complex.I * (a * t : ℝ)
  have hz : z ≠ 0 := by
    dsimp [z]
    exact mul_ne_zero (mul_ne_zero (by norm_num) Complex.I_ne_zero)
      (Complex.ofReal_ne_zero.mpr hat)
  have him : z.im = 2 * a * t := by simp [z]; ring
  have hi : z⁻¹ ∈ Complex.slitPlane := by
    apply Complex.mem_slitPlane_iff.mpr
    right
    rw [Complex.inv_im]
    apply div_ne_zero
    · rw [him]
      exact neg_ne_zero.mpr (by
        simpa only [mul_assoc] using (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) hat))
    · exact (Complex.normSq_pos.mpr hz).ne'
  have hc : ContinuousAt (fun ε : ℝ => (ε : ℂ) + z) 0 := by fun_prop
  have hc' : ContinuousAt (fun ε : ℝ => ((ε : ℂ) + z)⁻¹) 0 :=
    hc.inv₀ (by simpa using hz)
  have ht : Tendsto (fun ε : ℝ => ((ε : ℂ) + z)⁻¹) (𝓝 0) (𝓝 z⁻¹) := by
    simpa using hc'.tendsto
  have hp := (continuousAt_cpow_const (b := (1 / 2 : ℂ)) hi).tendsto.comp ht
  simpa only [ContinuousAt, Function.comp_def, quadraticFresnelCoefficient, one_div, z, Complex.ofReal_zero, zero_add] using hp

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticFresnelPhase
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The principal square root on the two imaginary half-axes -/

namespace Ostmann

 theorem quadratic_half_negative_imaginary {r : ℝ} (hr : 0 < r) :
    (-(r : ℂ) * Complex.I) ^ (1 / 2 : ℂ) =
      (Real.sqrt (r / 2) : ℂ) * (1 - Complex.I) := by
  have hn : ‖-(r : ℂ) * Complex.I‖ = r := by
    rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr,
      Complex.norm_I, mul_one]
  have hi : (-(r : ℂ) * Complex.I).im < 0 := by simpa using neg_neg_of_pos hr
  rw [one_div (2 : ℂ)]
  apply Complex.ext
  · rw [Complex.cpow_inv_two_re, hn]
    simp
  · rw [Complex.cpow_inv_two_im_eq_neg_sqrt hi, hn]
    simp

 theorem quadratic_half_positive_imaginary {r : ℝ} (hr : 0 < r) :
    ((r : ℂ) * Complex.I) ^ (1 / 2 : ℂ) =
      (Real.sqrt (r / 2) : ℂ) * (1 + Complex.I) := by
  have hn : ‖(r : ℂ) * Complex.I‖ = r := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr,
      Complex.norm_I, mul_one]
  have hi : 0 ≤ ((r : ℂ) * Complex.I).im := by simpa using hr.le
  rw [one_div (2 : ℂ)]
  apply Complex.ext
  · rw [Complex.cpow_inv_two_re, hn]
    simp
  · rw [Complex.cpow_inv_two_im_eq_sqrt hi, hn]
    simp

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticFresnelEvaluation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Evaluating the limiting quadratic Gaussian coefficient -/

namespace Ostmann

private theorem sqrt_quarter_reciprocal {b : ℝ} :
    Real.sqrt ((1 / (2 * b)) / 2) = 1 / (2 * Real.sqrt b) := by
  rw [div_div, show 2 * b * 2 = 4 * b by ring, Real.sqrt_div,
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
  all_goals norm_num

 theorem quadratic_fresnel_coefficient_positive {a t : ℝ} (hat : 0 < a * t) :
    quadraticFresnelCoefficient 0 a t =
      ((1 / (2 * Real.sqrt (a * t)) : ℝ) : ℂ) * (1 - Complex.I) := by
  let b := a * t
  have hb : 0 < b := hat
  have hbC : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
  have he : (1 : ℂ) / (2 * Complex.I * (b : ℂ)) =
      -((1 / (2 * b) : ℝ) : ℂ) * Complex.I := by
    push_cast
    field_simp
    ring_nf
    simp only [Complex.I_sq]
    ring
  unfold quadraticFresnelCoefficient
  rw [Complex.ofReal_zero, zero_add]
  change ((1 : ℂ) / (2 * Complex.I * (b : ℂ))) ^ (1 / 2 : ℂ) = _
  rw [he, quadratic_half_negative_imaginary (by positivity), sqrt_quarter_reciprocal]

 theorem quadratic_fresnel_coefficient_negative {a t : ℝ} (hat : a * t < 0) :
    quadraticFresnelCoefficient 0 a t =
      ((1 / (2 * Real.sqrt (-(a * t))) : ℝ) : ℂ) * (1 + Complex.I) := by
  let b := -(a * t)
  have hb : 0 < b := neg_pos.mpr hat
  have hbC : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
  have he : (1 : ℂ) / (2 * Complex.I * (a * t : ℝ)) =
      ((1 / (2 * b) : ℝ) : ℂ) * Complex.I := by
    have hbt : a * t = -b := by dsimp [b]; ring
    rw [hbt]
    push_cast
    field_simp
    ring_nf
    simp only [Complex.I_sq]
  unfold quadraticFresnelCoefficient
  rw [Complex.ofReal_zero, zero_add, he,
    quadratic_half_positive_imaginary (by positivity), sqrt_quarter_reciprocal]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticFresnelLimit
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing the damping on the physical test-function side -/

namespace Ostmann

open MeasureTheory Filter
open scoped SchwartzMap FourierTransform Topology

private theorem fresnelCoefficient_continuous {ε : ℝ} (hε : 0 < ε) (a : ℝ) :
    Continuous (quadraticFresnelCoefficient ε a) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  let z : ℂ := (ε : ℂ) + 2 * Complex.I * (a * t : ℝ)
  have hz : z ≠ 0 := by
    intro hh
    have hh' := congrArg Complex.re hh
    simp only [z, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im] at hh'
    norm_num at hh'
    linarith
  have hzre : z.re = ε := by simp [z]
  have hi : z⁻¹ ∈ Complex.slitPlane := by
    apply Complex.mem_slitPlane_iff.mpr
    left
    rw [Complex.inv_re, hzre]
    exact div_pos hε (Complex.normSq_pos.mpr hz)
  have hc : ContinuousAt (fun t' : ℝ => (ε : ℂ) + 2 * Complex.I * (a * t' : ℝ)) t := by
    fun_prop
  have ht : Tendsto (fun t' : ℝ => ((ε : ℂ) + 2 * Complex.I * (a * t' : ℝ))⁻¹)
      (𝓝 t) (𝓝 z⁻¹) := (hc.inv₀ hz).tendsto
  have hh := (continuousAt_cpow_const (b := (1 / 2 : ℂ)) hi).tendsto.comp ht
  change Tendsto (fun t' => quadraticFresnelCoefficient ε a t') (𝓝 t)
    (𝓝 (quadraticFresnelCoefficient ε a t))
  simpa only [Function.comp_def, quadraticFresnelCoefficient, one_div, z] using hh

 theorem quadratic_fresnel_coefficient_integral_limit (ρ : 𝓢(ℝ, ℂ))
    (a : ℝ) (ha : 1 ≤ |a|) (hρ : ∀ t < 1 / 2, ρ t = 0) :
    Tendsto (fun n : ℕ => ∫ t : ℝ,
      quadraticFresnelCoefficient (1 / ((n : ℝ) + 1)) a t * ρ t)
      atTop (𝓝 (∫ t : ℝ, quadraticFresnelCoefficient 0 a t * ρ t)) := by
  apply tendsto_integral_of_dominated_convergence (fun t : ℝ => ‖ρ t‖)
  · intro n
    exact ((fresnelCoefficient_continuous (by positivity) a).mul ρ.continuous).aestronglyMeasurable
  · exact ρ.integrable.norm
  · intro n
    filter_upwards with t
    by_cases ht : t < 1 / 2
    · simp [hρ t ht]
    · rw [norm_mul]
      exact (mul_le_mul_of_nonneg_right
        (quadraticFresnelCoefficient_norm_le _ ha (le_of_not_gt ht))
        (norm_nonneg _)).trans_eq (one_mul _)
  · filter_upwards with t
    by_cases ht : t < 1 / 2
    · simp only [hρ t ht, mul_zero]
      exact tendsto_const_nhds
    · have ha₀ : a ≠ 0 := by
        intro hh
        simp only [hh, abs_zero] at ha
        linarith
      have ht₀ : t ≠ 0 := by linarith
      have hc := (quadraticFresnelCoefficient_continuousAt_zero (mul_ne_zero ha₀ ht₀)).tendsto.comp
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      exact hc.mul_const (ρ t)

 theorem quadratic_fresnel_integral (ρ : 𝓢(ℝ, ℂ)) (a : ℝ)
    (ha : 1 ≤ |a|) (hρ : ∀ t < 1 / 2, ρ t = 0) :
    (∫ x : ℝ, 𝓕 ρ (a * x ^ 2)) =
      ∫ t : ℝ, quadraticFresnelCoefficient 0 a t * ρ t := by
  have hleft := quadratic_damped_fourier_integral_limit ρ a ha
  have hright := quadratic_fresnel_coefficient_integral_limit ρ a ha hρ
  have he : (fun n : ℕ => ∫ x : ℝ,
      quadraticGaussianDamping (1 / ((n : ℝ) + 1)) x * 𝓕 ρ (a * x ^ 2)) =
      (fun n : ℕ => ∫ t : ℝ,
        quadraticFresnelCoefficient (1 / ((n : ℝ) + 1)) a t * ρ t) := by
    funext n
    exact quadratic_damped_fresnel ρ (by positivity) a
  rw [he] at hleft
  exact tendsto_nhds_unique hleft hright

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticSqrtIntegral
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The square-root Jacobian in the quadratic Poisson main term -/

namespace Ostmann

open MeasureTheory Set
open scoped SchwartzMap

theorem quadratic_sqrt_integral (ρ : ℝ → ℂ) :
    (∫ t : ℝ, (Real.sqrt t)⁻¹ • ρ t) =
      (2 : ℝ) • ∫ x in Ioi (0 : ℝ), ρ (x ^ 2) := by
  have hsupport : (∫ t in Ioi (0 : ℝ), (Real.sqrt t)⁻¹ • ρ t) =
      ∫ t : ℝ, (Real.sqrt t)⁻¹ • ρ t := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro t ht
    have ht' : t ≤ 0 := le_of_not_gt ht
    simp [Real.sqrt_eq_zero_of_nonpos ht']
  rw [← hsupport, ← integral_comp_rpow_Ioi (fun t : ℝ => (Real.sqrt t)⁻¹ • ρ t)
    (by norm_num : (2 : ℝ) ≠ 0)]
  calc
    _ = ∫ x in Ioi (0 : ℝ), (2 : ℝ) • ρ (x ^ 2) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      have hx₀ : x ≠ 0 := ne_of_gt hx
      simp only [abs_of_pos (by norm_num : (0 : ℝ) < 2),
        show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, Real.rpow_two,
        Real.sqrt_sq (le_of_lt hx), smul_smul]
      congr 1
      field_simp
    _ = _ := integral_smul _ _

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticFresnelMain
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact main term of the second quadratic Poisson transform -/

namespace Ostmann

open MeasureTheory Set
open scoped SchwartzMap FourierTransform

theorem quadratic_fresnel_coefficient_factor {a t : ℝ} (ha : a ≠ 0) (ht : 0 < t) :
    quadraticFresnelCoefficient 0 a t =
      (quadraticFresnelPhase a / (2 * (Real.sqrt |a| : ℂ))) *
        ((Real.sqrt t)⁻¹ : ℝ) := by
  rcases lt_or_gt_of_ne ha with ha | ha
  · have hat : a * t < 0 := mul_neg_of_neg_of_pos ha ht
    rw [quadratic_fresnel_coefficient_negative hat, quadraticFresnelPhase,
      ite_eq_right (not_lt_of_ge ha.le), abs_of_neg ha,
      show -(a * t) = (-a) * t by ring, Real.sqrt_mul (neg_pos.mpr ha).le]
    push_cast
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  · rw [quadratic_fresnel_coefficient_positive (mul_pos ha ht), quadraticFresnelPhase,
      ite_eq_left ha, abs_of_pos ha, Real.sqrt_mul ha.le]
    push_cast
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring

theorem quadratic_fresnel_main (ρ : 𝓢(ℝ, ℂ)) (a : ℝ)
    (ha : 1 ≤ |a|) (hρ : ∀ t < 1 / 2, ρ t = 0) :
    (∫ x : ℝ, 𝓕 ρ (a * x ^ 2)) =
      (quadraticFresnelPhase a / (Real.sqrt |a| : ℂ)) *
        ∫ x in Ioi (0 : ℝ), ρ (x ^ 2) := by
  have ha₀ : a ≠ 0 := by
    intro hz
    simp only [hz, abs_zero] at ha
    linarith
  rw [quadratic_fresnel_integral ρ a ha hρ]
  calc
    _ = ∫ t : ℝ, (quadraticFresnelPhase a / (2 * (Real.sqrt |a| : ℂ))) *
        ((Real.sqrt t)⁻¹ • ρ t) := by
      apply integral_congr_ae
      filter_upwards with t
      by_cases ht : t < 1 / 2
      · simp [hρ t ht]
      · rw [quadratic_fresnel_coefficient_factor ha₀ (by linarith)]
        simp only [Complex.real_smul]
        ring
    _ = (quadraticFresnelPhase a / (2 * (Real.sqrt |a| : ℂ))) *
        ((2 : ℝ) • ∫ x in Ioi (0 : ℝ), ρ (x ^ 2)) := by
      rw [integral_const_mul, quadratic_sqrt_integral]
    _ = _ := by
      simp only [Complex.real_smul, Complex.ofReal_ofNat]
      ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticSchwartzTail
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Quantitative lattice tails for the actual Poisson test function -/

namespace Ostmann

open scoped Classical BigOperators SchwartzMap

private theorem schwartz_lattice_point_bound (ψ : 𝓢(ℝ, ℂ)) (A : ℕ)
    {Y R : ℝ} (hY : 0 < Y) (hR : 0 < R) (n : ℤ) :
    (if R ≤ |(n : ℝ)| then ‖ψ ((n : ℝ) * Y)‖ else 0) ≤
      (SchwartzMap.seminorm ℝ (A + 2) 0 ψ / (Y ^ (A + 2) * R ^ A)) *
        (1 / (n : ℝ) ^ 2) := by
  by_cases hn : R ≤ |(n : ℝ)|
  · rw [ite_eq_left hn]
    have hnabs : 0 < |(n : ℝ)| := hR.trans_le hn
    have hn0 : (n : ℝ) ≠ 0 := abs_pos.mp hnabs
    have hseminorm := SchwartzMap.norm_pow_mul_le_seminorm ℝ ψ (A + 2) ((n : ℝ) * Y)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos hY, mul_pow, pow_add] at hseminorm
    have hh : ‖ψ ((n : ℝ) * Y)‖ * (Y ^ (A + 2) * R ^ A) * (n : ℝ) ^ 2 ≤
        SchwartzMap.seminorm ℝ (A + 2) 0 ψ := by
      calc
        _ ≤ ‖ψ ((n : ℝ) * Y)‖ * (Y ^ (A + 2) * |(n : ℝ)| ^ A) * (n : ℝ) ^ 2 := by
          gcongr
        _ = (|(n : ℝ)| ^ A * |(n : ℝ)| ^ 2) * Y ^ (A + 2) * ‖ψ ((n : ℝ) * Y)‖ := by
          rw [sq_abs]
          ring
        _ ≤ _ := hseminorm
    rw [← div_eq_mul_one_div, le_div_iff₀ (sq_pos_of_ne_zero hn0),
      le_div_iff₀ (mul_pos (pow_pos hY _) (pow_pos hR _))]
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    ring
  · rw [ite_eq_right hn]
    positivity

 theorem quadratic_schwartz_lattice_tail (ψ : 𝓢(ℝ, ℂ)) (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ Y R : ℝ, 0 < Y → 0 < R →
      (∑' n : ℤ, if R ≤ |(n : ℝ)| then ‖ψ ((n : ℝ) * Y)‖ else 0) ≤
        C / (Y ^ (A + 2) * R ^ A) := by
  let Z : ℝ := ∑' n : ℤ, 1 / (n : ℝ) ^ 2
  have hZ : 0 ≤ Z := tsum_nonneg (fun _ => by positivity)
  let P : ℝ := SchwartzMap.seminorm ℝ (A + 2) 0 ψ
  have hP : 0 ≤ P := by positivity
  refine ⟨P * Z, mul_nonneg hP hZ, ?_⟩
  intro Y R hY hR
  have hs : Summable (fun n : ℤ => (P / (Y ^ (A + 2) * R ^ A)) * (1 / (n : ℝ) ^ 2)) :=
    (Real.summable_one_div_int_pow.mpr (by norm_num : 1 < 2)).mul_left _
  have hb := fun n => schwartz_lattice_point_bound ψ A hY hR n
  have hf : Summable (fun n : ℤ => if R ≤ |(n : ℝ)| then ‖ψ ((n : ℝ) * Y)‖ else 0) :=
    Summable.of_nonneg_of_le (fun _ => by split_ifs <;> positivity) hb hs
  have ht := hf.tsum_le_tsum hb hs
  rw [tsum_mul_left] at ht
  convert ht using 1
  all_goals try with_reducible_and_instances rfl
  dsimp only [Z, P]
  ring

 theorem quadratic_schwartz_nonzero_lattice (ψ : 𝓢(ℝ, ℂ)) (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ Y : ℝ, 0 < Y →
      (∑' n : ℤ, if n = 0 then 0 else ‖ψ ((n : ℝ) * Y)‖) ≤ C / Y ^ (A + 2) := by
  obtain ⟨C, hC, hc⟩ := quadratic_schwartz_lattice_tail ψ A
  refine ⟨C, hC, ?_⟩
  intro Y hY
  have hh := hc Y 1 hY zero_lt_one
  have he : (fun n : ℤ => if n = 0 then 0 else ‖ψ ((n : ℝ) * Y)‖) =
      (fun n : ℤ => if 1 ≤ |(n : ℝ)| then ‖ψ ((n : ℝ) * Y)‖ else 0) := by
    funext n
    by_cases hn : n = 0
    · simp [hn]
    · have ha : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast Int.one_le_abs hn
      simp [hn, ha]
  simpa only [he, one_pow, mul_one] using hh

 theorem quadratic_schwartz_frequency_tail (ψ : 𝓢(ℝ, ℂ)) (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ Y : ℝ, 0 < Y → ∀ L : ℕ,
      (∑' n : ℤ, if L < n.natAbs then ‖ψ ((n : ℝ) * Y)‖ else 0) ≤
        C / (Y ^ (A + 2) * ((L : ℝ) + 1) ^ A) := by
  obtain ⟨C, hC, hc⟩ := quadratic_schwartz_lattice_tail ψ A
  refine ⟨C, hC, ?_⟩
  intro Y hY L
  have hh := hc Y (L + 1) hY (by positivity)
  have he : (fun n : ℤ => if L < n.natAbs then ‖ψ ((n : ℝ) * Y)‖ else 0) =
      (fun n : ℤ => if (L : ℝ) + 1 ≤ |(n : ℝ)| then ‖ψ ((n : ℝ) * Y)‖ else 0) := by
    funext n
    have hi : L < n.natAbs ↔ (L : ℝ) + 1 ≤ |(n : ℝ)| := by
      rw [show |(n : ℝ)| = (n.natAbs : ℝ) by simp]
      exact_mod_cast (Nat.lt_iff_add_one_le : L < n.natAbs ↔ L + 1 ≤ n.natAbs)
    simp only [hi]
  simpa only [he] using hh

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticFrequencyCutoff
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A finite frequency window with its actual Schwartz remainder -/

namespace Ostmann

open scoped Classical BigOperators SchwartzMap

 theorem quadratic_schwartz_tail_norm (ψ : 𝓢(ℝ, ℂ)) (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ Y : ℝ, 0 < Y → ∀ L : ℕ,
      ‖∑' n : ℤ, if L < n.natAbs then ψ ((n : ℝ) * Y) else 0‖ ≤
        C / (Y ^ (A + 2) * ((L : ℝ) + 1) ^ A) := by
  obtain ⟨C, hC, hc⟩ := quadratic_schwartz_frequency_tail ψ A
  refine ⟨C, hC, ?_⟩
  intro Y hY L
  have hs : Summable (fun n : ℤ => ‖ψ ((n : ℝ) * Y)‖) := by
    simpa only [div_inv_eq_mul] using quadratic_scaled_summable ψ (inv_pos.mpr hY)
  have ht : Summable (fun n : ℤ => ‖if L < n.natAbs then ψ ((n : ℝ) * Y) else 0‖) := by
    apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ hs
    intro n
    split_ifs <;> simp
  apply (norm_tsum_le_tsum_norm ht).trans
  simpa only [apply_ite, norm_zero] using hc Y hY L

private theorem outside_int_window (n : ℤ) (L : ℕ) :
    n ∉ Finset.Icc (-(L : ℤ)) L ↔ L < n.natAbs := by
  simp only [Finset.mem_Icc, not_and_or]
  omega

 theorem quadratic_frequency_window (ψ : 𝓢(ℝ, ℂ)) {Y : ℝ} (hY : 0 < Y) (L : ℕ) :
    (∑' n : ℤ, if n = 0 then 0 else ψ ((n : ℝ) * Y)) =
      (∑ n ∈ Finset.Icc (-(L : ℤ)) L, if n = 0 then 0 else ψ ((n : ℝ) * Y)) +
      ∑' n : ℤ, if L < n.natAbs then ψ ((n : ℝ) * Y) else 0 := by
  have hs : Summable (fun n : ℤ => ‖ψ ((n : ℝ) * Y)‖) := by
    simpa only [div_inv_eq_mul] using quadratic_scaled_summable ψ (inv_pos.mpr hY)
  have hf : Summable (fun n : ℤ => if n = 0 then 0 else ψ ((n : ℝ) * Y)) := by
    apply Summable.of_norm_bounded hs
    intro n
    split_ifs <;> simp
  have hh := hf.sum_add_tsum_subtype_compl (Finset.Icc (-(L : ℤ)) L)
  have ht := tsum_subtype {n : ℤ | n ∉ Finset.Icc (-(L : ℤ)) L}
    (fun n : ℤ => if n = 0 then 0 else ψ ((n : ℝ) * Y))
  have hh' := (congrArg (fun z : ℂ =>
    (∑ n ∈ Finset.Icc (-(L : ℤ)) L, if n = 0 then 0 else ψ ((n : ℝ) * Y)) + z) ht).symm.trans hh
  simp only [Set.indicator, Set.mem_ofPred_eq] at hh'
  rw [← hh']
  congr 1
  apply tsum_congr
  intro n
  simp only [outside_int_window]
  by_cases hn : n = 0
  · simp [hn]
  · simp [hn]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticHybridPoisson
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact passage between the physical and Fourier lattice tails -/

namespace Ostmann

open scoped Classical BigOperators FourierTransform SchwartzMap

 theorem quadraticLatticeTail_window (ψ : 𝓢(ℝ, ℂ)) {Y : ℝ} (hY : 0 < Y) (L : ℕ) :
    quadraticLatticeTail ψ Y = quadraticLatticeWindow ψ Y L + quadraticLatticeOuter ψ Y L :=
  quadratic_frequency_window ψ hY L

 theorem quadraticLatticeTail_poisson (ψ : 𝓢(ℝ, ℂ)) {X d : ℝ}
    (hX : 0 < X) (hd : 0 < d) :
    ((X / d : ℝ) : ℂ) * quadraticLatticeTail (𝓕 ψ) (X / d) =
      ψ 0 + quadraticLatticeTail ψ (d / X) - ((X / d : ℝ) : ℂ) * 𝓕 ψ 0 := by
  have hsplit (f : 𝓢(ℝ, ℂ)) (Y : ℝ) (hY : 0 < Y) :
      (∑' n : ℤ, f ((n : ℝ) * Y)) = f 0 + quadraticLatticeTail f Y := by
    have hs : Summable (fun n : ℤ => f ((n : ℝ) * Y)) := by
      apply Summable.of_norm
      simpa only [div_inv_eq_mul] using quadratic_scaled_summable f (inv_pos.mpr hY)
    simpa only [Int.cast_zero, zero_mul, quadraticLatticeTail] using hs.tsum_eq_add_tsum_ite 0
  have hp := quadratic_scaled_poisson ψ (div_pos hX hd)
  simp only [div_div_eq_mul_div, mul_div_assoc] at hp
  have hp' : (∑' n : ℤ, ψ ((n : ℝ) * (d / X))) =
      ((X / d : ℝ) : ℂ) * ∑' n : ℤ, 𝓕 ψ ((n : ℝ) * (X / d)) := by
    simpa only [mul_div_assoc] using hp
  rw [hsplit ψ (d / X) (div_pos hd hX), hsplit (𝓕 ψ) (X / d) (div_pos hX hd)] at hp'
  linear_combination -hp'

 theorem quadraticCoprimeRemainder_tail {q : ℕ} (ψ : 𝓢(ℝ, ℂ)) (X : ℝ) :
    quadraticCoprimeRemainder q ψ X =
      ∑ d ∈ q.divisors, (ArithmeticFunction.moebius d : ℂ) * ((X / d : ℝ) : ℂ) *
        quadraticLatticeTail (𝓕 ψ) (X / d) := by
  unfold quadraticCoprimeRemainder quadraticLatticeTail
  simp only [mul_div_assoc]

 theorem quadraticCoprimeRemainder_hybrid {q : ℕ} (ψ : 𝓢(ℝ, ℂ))
    {X U V : ℝ} (hX : 0 < X) (_hUV : U ≤ V) (L : ℕ) :
    quadraticCoprimeRemainder q ψ X =
      ∑ d ∈ q.divisors,
        if (d : ℝ) ≤ U then
          (ArithmeticFunction.moebius d : ℂ) * ((X / d : ℝ) : ℂ) * quadraticLatticeTail (𝓕 ψ) (X / d)
        else if (d : ℝ) ≤ V then
          (ArithmeticFunction.moebius d : ℂ) * ((X / d : ℝ) : ℂ) *
            (quadraticLatticeWindow (𝓕 ψ) (X / d) L + quadraticLatticeOuter (𝓕 ψ) (X / d) L)
        else (ArithmeticFunction.moebius d : ℂ) *
          (ψ 0 + quadraticLatticeTail ψ (d / X) - ((X / d : ℝ) : ℂ) * 𝓕 ψ 0) := by
  rw [quadraticCoprimeRemainder_tail]
  apply Finset.sum_congr rfl
  intro d hd
  have hdR : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_mem_divisors hd
  by_cases hdu : (d : ℝ) ≤ U
  · rw [ite_eq_left hdu]
  · rw [ite_eq_right hdu]
    by_cases hdv : (d : ℝ) ≤ V
    · rw [ite_eq_left hdv, quadraticLatticeTail_window (𝓕 ψ) (div_pos hX hdR) L]
    · rw [ite_eq_right hdv, mul_assoc, quadraticLatticeTail_poisson ψ hX hdR]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticSmallDivisorTail
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniformly summing the small-divisor Fourier tails -/

namespace Ostmann

open scoped Classical BigOperators FourierTransform SchwartzMap

theorem quadratic_low_divisor_card (q : ℕ) {U : ℝ} (hU : 0 ≤ U) :
    (((q.divisors.filter (fun d : ℕ => (d : ℝ) ≤ U)).card : ℝ)) ≤ U := by
  have hc : (q.divisors.filter (fun d : ℕ => (d : ℝ) ≤ U)).card ≤ ⌊U⌋₊ := by
    calc
      _ ≤ (Finset.Icc 1 ⌊U⌋₊).card := by
        apply Finset.card_le_card
        intro d hd
        obtain ⟨hd, hbound⟩ := Finset.mem_filter.mp hd
        exact Finset.mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hd, Nat.le_floor hbound⟩
      _ = _ := by simp
  exact (Nat.cast_le.mpr hc).trans (Nat.floor_le hU)

 theorem quadratic_small_divisor_tail (ψ : 𝓢(ℝ, ℂ)) (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q : ℕ, ∀ X U : ℝ, 0 < X → 0 < U →
      ‖∑ d ∈ q.divisors.filter (fun d : ℕ => (d : ℝ) ≤ U),
        (ArithmeticFunction.moebius d : ℂ) * ((X / d : ℝ) : ℂ) *
          quadraticLatticeTail (𝓕 ψ) (X / d)‖ ≤ C * U * (U / X) ^ (A + 1) := by
  obtain ⟨C, hC, hc⟩ := quadratic_schwartz_nonzero_lattice (𝓕 ψ) A
  refine ⟨C, hC, ?_⟩
  intro q X U hX hU
  have hterm (d : ℕ) (hd : d ∈ q.divisors.filter (fun d : ℕ => (d : ℝ) ≤ U)) :
      ‖(ArithmeticFunction.moebius d : ℂ) * ((X / d : ℝ) : ℂ) *
        quadraticLatticeTail (𝓕 ψ) (X / d)‖ ≤ C * (U / X) ^ (A + 1) := by
    obtain ⟨hd, hdU⟩ := Finset.mem_filter.mp hd
    have hdR : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_mem_divisors hd
    have hxd : 0 < X / d := div_pos hX hdR
    have hs : Summable (fun n : ℤ => ‖(𝓕 ψ) ((n : ℝ) * (X / d))‖) := by
      simpa only [div_inv_eq_mul] using quadratic_scaled_summable (𝓕 ψ) (inv_pos.mpr hxd)
    have hs' : Summable (fun n : ℤ => ‖if n = 0 then 0 else (𝓕 ψ) ((n : ℝ) * (X / d))‖) := by
      apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ hs
      intro n
      split_ifs <;> simp
    have ht : ‖quadraticLatticeTail (𝓕 ψ) (X / d)‖ ≤ C / (X / d) ^ (A + 2) := by
      apply (norm_tsum_le_tsum_norm hs').trans
      simpa only [apply_ite, norm_zero] using hc (X / d) hxd
    have hmu : ‖(ArithmeticFunction.moebius d : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_intCast]
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hxd]
    calc
      _ ≤ 1 * (X / d) * (C / (X / d) ^ (A + 2)) := by gcongr
      _ = C * ((d : ℝ) / X) ^ (A + 1) := by
        rw [div_pow, div_pow]
        simp only [pow_add, pow_one, pow_two]
        field_simp
      _ ≤ C * (U / X) ^ (A + 1) := by gcongr
  calc
    _ ≤ ∑ d ∈ q.divisors.filter (fun d : ℕ => (d : ℝ) ≤ U),
        ‖(ArithmeticFunction.moebius d : ℂ) * ((X / d : ℝ) : ℂ) *
          quadraticLatticeTail (𝓕 ψ) (X / d)‖ := norm_sum_le _ _
    _ ≤ ∑ _d ∈ q.divisors.filter (fun d : ℕ => (d : ℝ) ≤ U), C * (U / X) ^ (A + 1) :=
      Finset.sum_le_sum hterm
    _ = (((q.divisors.filter (fun d : ℕ => (d : ℝ) ≤ U)).card : ℝ)) *
        (C * (U / X) ^ (A + 1)) := by simp
    _ ≤ U * (C * (U / X) ^ (A + 1)) :=
      mul_le_mul_of_nonneg_right (quadratic_low_divisor_card q hU.le) (by positivity)
    _ = _ := by ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticInverseSquareTail
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform finite tails of the inverse-square series -/

namespace Ostmann

open scoped Classical BigOperators

 theorem quadratic_inverse_square_tail (S : Finset ℕ) {V : ℝ} (hV : 0 < V)
    (hS : ∀ d ∈ S, V < (d : ℝ)) :
    (∑ d ∈ S, 1 / (d : ℝ) ^ 2) ≤ 2 / V := by
  by_cases hs : S.Nonempty
  · let M : ℕ := ⌊V⌋₊ + 1
    let B : ℕ := S.sup id
    have hM : 0 < M := by dsimp [M]; omega
    have hMV : V < (M : ℝ) := by simpa only [M, Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one V
    have hMd : ∀ d ∈ S, M ≤ d := by
      intro d hd
      by_contra hn
      have hdF : d ≤ ⌊V⌋₊ := by dsimp [M] at hn; omega
      have hle := (Nat.cast_le.mpr hdF).trans (Nat.floor_le hV.le)
      exact (not_lt_of_ge hle) (hS d hd)
    have hMB : M ≤ B + 1 := by
      obtain ⟨d, hd⟩ := hs
      have hdb : d ≤ B := Finset.le_sup (f := id) hd
      exact (hMd d hd).trans (by omega)
    have hsub : S ⊆ Finset.Ico M (B + 1) := by
      intro d hd
      exact Finset.mem_Ico.mpr ⟨hMd d hd, Nat.lt_succ_of_le (Finset.le_sup (f := id) hd)⟩
    have hpoint (d : ℕ) (hd : d ∈ Finset.Ico M (B + 1)) :
        1 / (d : ℝ) ^ 2 ≤ 2 / (d : ℝ) - 2 / ((d : ℝ) + 1) := by
      have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hM.trans_le (Finset.mem_Ico.mp hd).1
      have hd0 : (0 : ℝ) < d := by linarith
      have hid : 2 / (d : ℝ) - 2 / ((d : ℝ) + 1) = 2 / ((d : ℝ) * (d + 1)) := by
        field_simp
        ring
      rw [hid]
      apply (div_le_div_iff₀ (sq_pos_of_pos hd0) (mul_pos hd0 (by linarith))).mpr
      nlinarith
    calc
      _ ≤ ∑ d ∈ Finset.Ico M (B + 1), 1 / (d : ℝ) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (by intros; positivity)
      _ ≤ ∑ d ∈ Finset.Ico M (B + 1), (2 / (d : ℝ) - 2 / ((d : ℝ) + 1)) :=
        Finset.sum_le_sum hpoint
      _ = 2 / (M : ℝ) - 2 / ((B : ℝ) + 1) := by
        have hh := Finset.sum_Ico_sub (f := fun n : ℕ => -(2 / (n : ℝ))) hMB
        simpa only [Nat.cast_add, Nat.cast_one, sub_neg_eq_add, neg_add_eq_sub] using hh
      _ ≤ 2 / (M : ℝ) := sub_le_self _ (by positivity)
      _ ≤ 2 / V := div_le_div_of_nonneg_left (by norm_num) hV hMV.le
  · simp only [Finset.not_nonempty_iff_eq_empty.mp hs, Finset.sum_empty]
    positivity

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticLargeDivisorTail
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniformly summing the large-divisor physical tails -/

namespace Ostmann

open scoped Classical BigOperators SchwartzMap

 theorem quadratic_large_divisor_tail (ψ : 𝓢(ℝ, ℂ)) (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q : ℕ, ∀ X V : ℝ, 0 < X → 0 < V →
      ‖∑ d ∈ q.divisors.filter (fun d : ℕ => V < (d : ℝ)),
        (ArithmeticFunction.moebius d : ℂ) * quadraticLatticeTail ψ (d / X)‖ ≤
        C * X * (X / V) ^ (A + 1) := by
  obtain ⟨C, hC, hc⟩ := quadratic_schwartz_nonzero_lattice ψ A
  refine ⟨2 * C, mul_nonneg (by norm_num) hC, ?_⟩
  intro q X V hX hV
  have hterm (d : ℕ) (hd : d ∈ q.divisors.filter (fun d : ℕ => V < (d : ℝ))) :
      ‖(ArithmeticFunction.moebius d : ℂ) * quadraticLatticeTail ψ (d / X)‖ ≤
        (C * X ^ (A + 2) / V ^ A) * (1 / (d : ℝ) ^ 2) := by
    obtain ⟨hd, hdV⟩ := Finset.mem_filter.mp hd
    have hdR : (0 : ℝ) < d := hV.trans hdV
    have hdx : 0 < (d : ℝ) / X := div_pos hdR hX
    have hs : Summable (fun n : ℤ => ‖ψ ((n : ℝ) * (d / X))‖) := by
      simpa only [div_inv_eq_mul] using quadratic_scaled_summable ψ (inv_pos.mpr hdx)
    have hs' : Summable (fun n : ℤ => ‖if n = 0 then 0 else ψ ((n : ℝ) * (d / X))‖) := by
      apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ hs
      intro n
      split_ifs <;> simp
    have ht : ‖quadraticLatticeTail ψ (d / X)‖ ≤ C / ((d : ℝ) / X) ^ (A + 2) := by
      apply (norm_tsum_le_tsum_norm hs').trans
      simpa only [apply_ite, norm_zero] using hc (d / X) hdx
    have hmu : ‖(ArithmeticFunction.moebius d : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_intCast]
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)
    rw [norm_mul]
    calc
      _ ≤ 1 * (C / ((d : ℝ) / X) ^ (A + 2)) := by gcongr
      _ = (C * X ^ (A + 2) / (d : ℝ) ^ A) * (1 / (d : ℝ) ^ 2) := by
        rw [div_pow, pow_add]
        field_simp
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact div_le_div_of_nonneg_left (by positivity) (pow_pos hV A)
          (pow_le_pow_left₀ hV.le hdV.le A)
  calc
    _ ≤ ∑ d ∈ q.divisors.filter (fun d : ℕ => V < (d : ℝ)),
        ‖(ArithmeticFunction.moebius d : ℂ) * quadraticLatticeTail ψ (d / X)‖ := norm_sum_le _ _
    _ ≤ ∑ d ∈ q.divisors.filter (fun d : ℕ => V < (d : ℝ)),
        (C * X ^ (A + 2) / V ^ A) * (1 / (d : ℝ) ^ 2) := Finset.sum_le_sum hterm
    _ = (C * X ^ (A + 2) / V ^ A) *
        ∑ d ∈ q.divisors.filter (fun d : ℕ => V < (d : ℝ)), 1 / (d : ℝ) ^ 2 :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ (C * X ^ (A + 2) / V ^ A) * (2 / V) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact quadratic_inverse_square_tail _ hV (fun d hd => (Finset.mem_filter.mp hd).2)
    _ = _ := by
      rw [div_pow]
      simp only [pow_add, pow_one, pow_two]
      field_simp

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticMiddleFrequencyTail
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform truncation of the middle-divisor Fourier frequencies -/

namespace Ostmann

open scoped Classical BigOperators FourierTransform SchwartzMap

 theorem quadratic_middle_frequency_tail (ψ : 𝓢(ℝ, ℂ)) (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q : ℕ, ∀ X U V : ℝ, 0 < X → 0 < V → ∀ L : ℕ,
      ‖∑ d ∈ q.divisors.filter (fun d : ℕ => U < (d : ℝ) ∧ (d : ℝ) ≤ V),
        (ArithmeticFunction.moebius d : ℂ) * ((X / d : ℝ) : ℂ) *
          quadraticLatticeOuter (𝓕 ψ) (X / d) L‖ ≤
        C * V * (V / X) ^ (A + 1) / ((L : ℝ) + 1) ^ A := by
  obtain ⟨C, hC, hc⟩ := quadratic_schwartz_tail_norm (𝓕 ψ) A
  refine ⟨C, hC, ?_⟩
  intro q X U V hX hV L
  let S := q.divisors.filter (fun d : ℕ => U < (d : ℝ) ∧ (d : ℝ) ≤ V)
  have hcard : (S.card : ℝ) ≤ V := by
    apply le_trans _ (quadratic_low_divisor_card q hV.le)
    exact_mod_cast Finset.card_le_card (show S ⊆ q.divisors.filter (fun d : ℕ => (d : ℝ) ≤ V) from by
      intro d hd
      obtain ⟨hd, _, hbound⟩ := Finset.mem_filter.mp hd
      exact Finset.mem_filter.mpr ⟨hd, hbound⟩)
  have hterm (d : ℕ) (hd : d ∈ S) :
      ‖(ArithmeticFunction.moebius d : ℂ) * ((X / d : ℝ) : ℂ) *
        quadraticLatticeOuter (𝓕 ψ) (X / d) L‖ ≤
        C * (V / X) ^ (A + 1) / ((L : ℝ) + 1) ^ A := by
    obtain ⟨hd, _, hdV⟩ := Finset.mem_filter.mp hd
    have hdR : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_mem_divisors hd
    have hxd : 0 < X / d := div_pos hX hdR
    have ht := hc (X / d) hxd L
    have hmu : ‖(ArithmeticFunction.moebius d : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_intCast]
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hxd]
    calc
      _ ≤ 1 * (X / d) * (C / ((X / d) ^ (A + 2) * ((L : ℝ) + 1) ^ A)) := by
        exact mul_le_mul (mul_le_mul_of_nonneg_right hmu hxd.le) ht (norm_nonneg _) (by positivity)
      _ = C * ((d : ℝ) / X) ^ (A + 1) / ((L : ℝ) + 1) ^ A := by
        rw [div_pow, div_pow]
        simp only [pow_add, pow_one, pow_two]
        field_simp
      _ ≤ _ := by gcongr
  calc
    _ ≤ ∑ d ∈ S, ‖(ArithmeticFunction.moebius d : ℂ) * ((X / d : ℝ) : ℂ) *
        quadraticLatticeOuter (𝓕 ψ) (X / d) L‖ := norm_sum_le _ _
    _ ≤ ∑ _d ∈ S, C * (V / X) ^ (A + 1) / ((L : ℝ) + 1) ^ A := Finset.sum_le_sum hterm
    _ = (S.card : ℝ) * (C * (V / X) ^ (A + 1) / ((L : ℝ) + 1) ^ A) := by simp
    _ ≤ V * (C * (V / X) ^ (A + 1) / ((L : ℝ) + 1) ^ A) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticTruncatedPoisson
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The full finite Poisson truncation, with every correction retained -/

namespace Ostmann

open scoped Classical BigOperators FourierTransform SchwartzMap

private theorem moebius_high_low {q : ℕ} (_hq : q ≠ 0) (hq1 : q ≠ 1) (V : ℝ) :
    (∑ d ∈ q.divisors.filter (fun d : ℕ => V < (d : ℝ)), (ArithmeticFunction.moebius d : ℂ)) =
      -(∑ d ∈ q.divisors.filter (fun d : ℕ => (d : ℝ) ≤ V), (ArithmeticFunction.moebius d : ℂ)) := by
  have htotal : (∑ d ∈ q.divisors, (ArithmeticFunction.moebius d : ℂ)) = 0 := by
    have hh := quadratic_moebius_divisor_sum q
    have hh' := congrArg (Int.cast : ℤ → ℂ) hh
    simpa only [hq1, ite_false, if_false, Int.cast_sum, Int.cast_zero] using hh'
  have hsplit :
      (∑ d ∈ q.divisors.filter (fun d : ℕ => (d : ℝ) ≤ V), (ArithmeticFunction.moebius d : ℂ)) +
      (∑ d ∈ q.divisors.filter (fun d : ℕ => V < (d : ℝ)), (ArithmeticFunction.moebius d : ℂ)) = 0 := by
    calc
      _ = ∑ d ∈ q.divisors, (ArithmeticFunction.moebius d : ℂ) := by
        rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro d _
        by_cases hd : (d : ℝ) ≤ V
        · simp [hd, not_lt_of_ge hd]
        · simp [hd, lt_of_not_ge hd]
      _ = 0 := htotal
  exact eq_neg_of_add_eq_zero_right hsplit

 theorem quadratic_truncated_coprime_poisson {q : ℕ} [NeZero q] (hq1 : q ≠ 1)
    (ψ : 𝓢(ℝ, ℂ)) {X U V : ℝ} (hX : 0 < X) (hUV : U ≤ V) (L : ℕ) :
    (∑' n : ℤ, (1 : DirichletCharacter ℂ q) (n : ZMod q) * ψ ((n : ℝ) / X)) =
      quadraticPoissonCore q ψ X U V L + quadraticPoissonError q ψ X U V L := by
  rw [quadratic_coprime_main ψ hX, quadraticCoprimeRemainder_hybrid ψ hX hUV L]
  have hm := moebius_high_low (NeZero.ne q) hq1 V
  unfold quadraticPoissonCore quadraticPoissonError
  have hreplace : -(ψ 0 * (∑ d ∈ q.divisors.filter (fun d : ℕ => (d : ℝ) ≤ V),
      (ArithmeticFunction.moebius d : ℂ))) =
      ψ 0 * (∑ d ∈ q.divisors.filter (fun d : ℕ => V < (d : ℝ)),
        (ArithmeticFunction.moebius d : ℂ)) := by rw [hm, mul_neg]
  rw [sub_eq_add_neg _ (ψ 0 * _), hreplace]
  simp only [Finset.sum_filter, Finset.mul_sum]
  have heq (d : ℕ) :
      (if (d : ℝ) ≤ U then
        (ArithmeticFunction.moebius d : ℂ) * ((X / d : ℝ) : ℂ) * quadraticLatticeTail (𝓕 ψ) (X / d)
      else if (d : ℝ) ≤ V then
        (ArithmeticFunction.moebius d : ℂ) * ((X / d : ℝ) : ℂ) *
          (quadraticLatticeWindow (𝓕 ψ) (X / d) L + quadraticLatticeOuter (𝓕 ψ) (X / d) L)
      else (ArithmeticFunction.moebius d : ℂ) *
        (ψ 0 + quadraticLatticeTail ψ (d / X) - ((X / d : ℝ) : ℂ) * 𝓕 ψ 0)) =
      ψ 0 * (if V < (d : ℝ) then (ArithmeticFunction.moebius d : ℂ) else 0) -
      𝓕 ψ 0 * (if V < (d : ℝ) then
        (ArithmeticFunction.moebius d : ℂ) * ((X / d : ℝ) : ℂ) else 0) +
      (if U < (d : ℝ) ∧ (d : ℝ) ≤ V then
        (ArithmeticFunction.moebius d : ℂ) * ((X / d : ℝ) : ℂ) * quadraticLatticeWindow (𝓕 ψ) (X / d) L else 0) +
      ((if (d : ℝ) ≤ U then
        (ArithmeticFunction.moebius d : ℂ) * ((X / d : ℝ) : ℂ) * quadraticLatticeTail (𝓕 ψ) (X / d) else 0) +
      (if V < (d : ℝ) then
        (ArithmeticFunction.moebius d : ℂ) * quadraticLatticeTail ψ (d / X) else 0) +
      (if U < (d : ℝ) ∧ (d : ℝ) ≤ V then
        (ArithmeticFunction.moebius d : ℂ) * ((X / d : ℝ) : ℂ) * quadraticLatticeOuter (𝓕 ψ) (X / d) L else 0)) := by
    by_cases hdu : (d : ℝ) ≤ U
    · have hdv : (d : ℝ) ≤ V := hdu.trans hUV
      simp [hdu, hdv, not_lt_of_ge hdu, not_lt_of_ge hdv]
    · by_cases hdv : (d : ℝ) ≤ V
      · simp [hdu, hdv, lt_of_not_ge hdu, not_lt_of_ge hdv, mul_add]
      · simp [hdu, hdv, lt_of_not_ge hdu, lt_of_not_ge hdv, mul_add, mul_sub]
        ring
  have hsum := Finset.sum_congr (s₁ := q.divisors) rfl (fun d _ => heq d)
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib] at hsum
  linear_combination hsum

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticPoissonErrorBound
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Quantitative error of the actual truncated coprime Poisson formula -/

namespace Ostmann

open scoped Classical BigOperators SchwartzMap

 theorem quadratic_poisson_error_bound (ψ : 𝓢(ℝ, ℂ)) (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q : ℕ, ∀ X U V : ℝ, 0 < X → 0 < U → 0 < V → ∀ L : ℕ,
      ‖quadraticPoissonError q ψ X U V L‖ ≤
        C * (U * (U / X) ^ (A + 1) + X * (X / V) ^ (A + 1) +
          V * (V / X) ^ (A + 1) / ((L : ℝ) + 1) ^ A) := by
  obtain ⟨C₁, hC₁, hc₁⟩ := quadratic_small_divisor_tail ψ A
  obtain ⟨C₂, hC₂, hc₂⟩ := quadratic_large_divisor_tail ψ A
  obtain ⟨C₃, hC₃, hc₃⟩ := quadratic_middle_frequency_tail ψ A
  refine ⟨C₁ + C₂ + C₃, by positivity, ?_⟩
  intro q X U V hX hU hV L
  have h₁ := hc₁ q X U hX hU
  have h₂ := hc₂ q X V hX hV
  have h₃ := hc₃ q X U V hX hV L
  have hh : ‖quadraticPoissonError q ψ X U V L‖ ≤
      C₁ * U * (U / X) ^ (A + 1) + C₂ * X * (X / V) ^ (A + 1) +
        C₃ * V * (V / X) ^ (A + 1) / ((L : ℝ) + 1) ^ A := by
    unfold quadraticPoissonError
    apply (norm_add_le _ _).trans
    apply add_le_add _ h₃
    exact (norm_add_le _ _).trans (add_le_add h₁ h₂)
  apply hh.trans
  calc
    _ = C₁ * (U * (U / X) ^ (A + 1)) + C₂ * (X * (X / V) ^ (A + 1)) +
        C₃ * (V * (V / X) ^ (A + 1) / ((L : ℝ) + 1) ^ A) := by ring
    _ ≤ (C₁ + C₂ + C₃) * (U * (U / X) ^ (A + 1)) +
        (C₁ + C₂ + C₃) * (X * (X / V) ^ (A + 1)) +
        (C₁ + C₂ + C₃) * (V * (V / X) ^ (A + 1) / ((L : ℝ) + 1) ^ A) := by gcongr <;> linarith
    _ = _ := by ring

 theorem quadratic_truncated_poisson_bound (ψ : 𝓢(ℝ, ℂ)) (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q : ℕ, [NeZero q] → q ≠ 1 →
      ∀ X U V : ℝ, 0 < X → 0 < U → U ≤ V → ∀ L : ℕ,
      ‖(∑' n : ℤ, (1 : DirichletCharacter ℂ q) (n : ZMod q) * ψ ((n : ℝ) / X)) -
        quadraticPoissonCore q ψ X U V L‖ ≤
      C * (U * (U / X) ^ (A + 1) + X * (X / V) ^ (A + 1) +
        V * (V / X) ^ (A + 1) / ((L : ℝ) + 1) ^ A) := by
  obtain ⟨C, hC, hc⟩ := quadratic_poisson_error_bound ψ A
  refine ⟨C, hC, ?_⟩
  intro q _ hq1 X U V hX hU hUV L
  rw [quadratic_truncated_coprime_poisson hq1 ψ hX hUV L, add_sub_cancel_left]
  exact hc q X U V hX hU (hU.trans_le hUV) L

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticPoissonParameters
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The power-saving parameter specialization in coprime Poisson truncation -/

namespace Ostmann

private theorem cutoff_power {t J : ℝ} (ht : 0 ≤ t) (hJ : 1 ≤ J)
    (htJ : t ≤ 1 / J) (a k : ℕ) : t ^ (a + k) ≤ 1 / J ^ a := by
  have hJ0 : 0 < J := lt_of_lt_of_le zero_lt_one hJ
  have ht1 : t ≤ 1 := htJ.trans ((div_le_one hJ0).mpr hJ)
  calc
    _ = t ^ a * t ^ k := pow_add _ _ _
    _ ≤ (1 / J) ^ a * 1 := mul_le_mul (pow_le_pow_left₀ ht htJ a)
      (pow_le_one₀ ht ht1) (pow_nonneg ht _) (by positivity)
    _ = _ := by rw [div_pow, one_pow, mul_one]

 theorem quadratic_poisson_parameter_budget (a L : ℕ) {X U V J : ℝ}
    (hX : 0 < X) (hU : 0 < U) (hV : 0 < V) (hJ : 1 ≤ J)
    (hUJ : U * J ≤ X) (hJV : X * J ≤ V) (hL : (V / X) ^ 2 ≤ (L : ℝ) + 1) :
    U * (U / X) ^ (a + 3) + X * (X / V) ^ (a + 3) +
      V * (V / X) ^ (a + 3) / ((L : ℝ) + 1) ^ (a + 2) ≤ 3 * X / J ^ a := by
  have hJ0 : 0 < J := lt_of_lt_of_le zero_lt_one hJ
  have hsmall : U * (U / X) ^ (a + 3) ≤ X / J ^ a := by
    have hu : U / X ≤ 1 / J := (div_le_div_iff₀ hX hJ0).mpr (by simpa using hUJ)
    have hh := mul_le_mul_of_nonneg_left (cutoff_power (div_nonneg hU.le hX.le) hJ hu a 4) hX.le
    have hp : (U / X) ^ (a + 4) = (U / X) ^ (a + 3) * (U / X) := by
      rw [show a + 4 = (a + 3) + 1 by omega, pow_succ]
    calc
      _ = X * (U / X) ^ (a + 4) := by rw [hp]; field_simp
      _ ≤ X * (1 / J ^ a) := hh
      _ = _ := by ring
  have hlarge : X * (X / V) ^ (a + 3) ≤ X / J ^ a := by
    have hv : X / V ≤ 1 / J := (div_le_div_iff₀ hV hJ0).mpr (by simpa using hJV)
    simpa only [mul_one_div] using mul_le_mul_of_nonneg_left
      (cutoff_power (div_nonneg hX.le hV.le) hJ hv a 3) hX.le
  have hmiddle : V * (V / X) ^ (a + 3) / ((L : ℝ) + 1) ^ (a + 2) ≤ X / J ^ a := by
    have hratio : 0 < V / X := div_pos hV hX
    have hbase : J ≤ V / X := (le_div_iff₀ hX).mpr (by simpa only [mul_comm] using hJV)
    calc
      _ ≤ V * (V / X) ^ (a + 3) / ((V / X) ^ 2) ^ (a + 2) :=
        div_le_div_of_nonneg_left (by positivity) (pow_pos (pow_pos hratio 2) (a + 2))
          (pow_le_pow_left₀ (sq_nonneg _) hL (a + 2))
      _ = X / (V / X) ^ a := by
        rw [← pow_mul]
        have he : 2 * (a + 2) = (a + 3) + a + 1 := by omega
        have hp : (V / X) ^ (2 * (a + 2)) =
            (V / X) ^ (a + 3) * (V / X) ^ a * (V / X) := by
          rw [he, pow_add, pow_add, pow_one]
        rw [hp]
        field_simp
      _ ≤ X / J ^ a := div_le_div_of_nonneg_left hX.le (pow_pos hJ0 a)
        (pow_le_pow_left₀ hJ0.le hbase a)
  calc
    _ ≤ X / J ^ a + X / J ^ a + X / J ^ a := add_le_add (add_le_add hsmall hlarge) hmiddle
    _ = _ := by ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticUniformPoisson
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform power-saving coprime Poisson summation

This proves the concrete Schwartz-function form of Heath-Brown (1995),
Lemma 13, needed in the two quadratic-sieve error estimates.
-/

namespace Ostmann

open scoped Classical BigOperators SchwartzMap

 theorem quadratic_uniform_coprime_poisson (ψ : 𝓢(ℝ, ℂ)) (a : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ q : ℕ, [NeZero q] → q ≠ 1 →
      ∀ X U V J : ℝ, 0 < X → 0 < U → 0 < V → 1 ≤ J →
      U * J ≤ X → X * J ≤ V → ∀ L : ℕ, (V / X) ^ 2 ≤ (L : ℝ) + 1 →
      ‖(∑' n : ℤ, (1 : DirichletCharacter ℂ q) (n : ZMod q) * ψ ((n : ℝ) / X)) -
        quadraticPoissonCore q ψ X U V L‖ ≤ C * X / J ^ a := by
  obtain ⟨C, hC, hc⟩ := quadratic_truncated_poisson_bound ψ (a + 2)
  refine ⟨3 * C + 1, by positivity, ?_⟩
  intro q _ hq1 X U V J hX hU hV hJ hUJ hJV L hL
  have hUX : U ≤ X := (le_mul_of_one_le_right hU.le hJ).trans hUJ
  have hXV : X ≤ V := (le_mul_of_one_le_right hX.le hJ).trans hJV
  have hbound := hc q hq1 X U V hX hU (hUX.trans hXV) L
  have hparam := quadratic_poisson_parameter_budget a L hX hU hV hJ hUJ hJV hL
  have hparam' :
      U * (U / X) ^ (a + 2 + 1) + X * (X / V) ^ (a + 2 + 1) +
      V * (V / X) ^ (a + 2 + 1) / ((L : ℝ) + 1) ^ (a + 2) ≤ 3 * X / J ^ a := by
    simpa only [Nat.add_assoc] using hparam
  calc
    _ ≤ C * (U * (U / X) ^ (a + 2 + 1) + X * (X / V) ^ (a + 2 + 1) +
        V * (V / X) ^ (a + 2 + 1) / ((L : ℝ) + 1) ^ (a + 2)) := hbound
    _ ≤ C * (3 * X / J ^ a) := mul_le_mul_of_nonneg_left hparam' hC
    _ ≤ (3 * C + 1) * X / J ^ a := by
      have hj0 : 0 < J := lt_of_lt_of_le zero_lt_one hJ
      have hxj : 0 ≤ X / J ^ a := div_nonneg hX.le (pow_nonneg hj0.le _)
      calc
        _ = (3 * C) * (X / J ^ a) := by ring
        _ ≤ (3 * C + 1) * (X / J ^ a) := mul_le_mul_of_nonneg_right (by linarith) hxj
        _ = _ := by ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticPositiveCoprime
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Recovering the positive half of an even coprime Poisson sum -/

namespace Ostmann

open scoped Classical BigOperators SchwartzMap

theorem quadratic_coprime_summable {q : ℕ} [NeZero q]
    (ψ : 𝓢(ℝ, ℂ)) {X : ℝ} (hX : 0 < X) :
    Summable (fun n : ℤ => (1 : DirichletCharacter ℂ q) (n : ZMod q) *
      ψ ((n : ℝ) / X)) := by
  apply Summable.of_norm_bounded (quadratic_scaled_summable ψ hX)
  intro n
  rw [principal_character_intCast]
  split_ifs <;> simp

theorem quadratic_coprime_positive_half {q : ℕ} [NeZero q] (hq : q ≠ 1)
    (ψ : 𝓢(ℝ, ℂ)) (heven : Function.Even ψ) {X : ℝ} (hX : 0 < X) :
    (∑' n : ℤ, (1 : DirichletCharacter ℂ q) (n : ZMod q) * ψ ((n : ℝ) / X)) =
      2 * ∑' n : ℕ+, (1 : DirichletCharacter ℂ q) (n : ZMod q) *
        ψ ((n : ℝ) / X) := by
  have hf : Function.Even (fun n : ℤ =>
      (1 : DirichletCharacter ℂ q) (n : ZMod q) * ψ ((n : ℝ) / X)) := by
    intro n
    change (1 : DirichletCharacter ℂ q) ((-n : ℤ) : ZMod q) *
      ψ (((-n : ℤ) : ℝ) / X) =
        (1 : DirichletCharacter ℂ q) (n : ZMod q) * ψ ((n : ℝ) / X)
    rw [principal_character_intCast, principal_character_intCast]
    rw [Int.cast_neg, neg_div, heven ((n : ℝ) / X)]
    congr 2
    simp only [Int.gcd, Int.natAbs_neg]
  have hzero : (1 : DirichletCharacter ℂ q) (0 : ZMod q) = 0 := by
    simpa [hq] using (principal_character_intCast (d := q) (0 : ℤ))
  have hh := tsum_int_eq_zero_add_two_mul_tsum_pnat hf (quadratic_coprime_summable ψ hX)
  simpa [hzero, two_smul, ← two_mul] using hh

theorem quadratic_uniform_positive_poisson (ψ : 𝓢(ℝ, ℂ)) (heven : Function.Even ψ)
    (a : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ q : ℕ, [NeZero q] → q ≠ 1 →
      ∀ X U V J : ℝ, 0 < X → 0 < U → 0 < V → 1 ≤ J →
      U * J ≤ X → X * J ≤ V → ∀ L : ℕ, (V / X) ^ 2 ≤ (L : ℝ) + 1 →
      ‖(∑' n : ℕ+, (1 : DirichletCharacter ℂ q) (n : ZMod q) * ψ ((n : ℝ) / X)) -
        quadraticPoissonCore q ψ X U V L / 2‖ ≤ C * X / J ^ a := by
  obtain ⟨C, hC, hc⟩ := quadratic_uniform_coprime_poisson ψ a
  refine ⟨C, hC, ?_⟩
  intro q _ hq X U V J hX hU hV hJ hUJ hJV L hL
  have hh := hc q hq X U V J hX hU hV hJ hUJ hJV L hL
  rw [quadratic_coprime_positive_half hq ψ heven hX] at hh
  have hid : (∑' n : ℕ+, (1 : DirichletCharacter ℂ q) (n : ZMod q) *
      ψ ((n : ℝ) / X)) - quadraticPoissonCore q ψ X U V L / 2 =
      (2 * (∑' n : ℕ+, (1 : DirichletCharacter ℂ q) (n : ZMod q) *
        ψ ((n : ℝ) / X)) - quadraticPoissonCore q ψ X U V L) / 2 := by ring
  rw [hid, norm_div]
  norm_num only [Complex.norm_ofNat]
  have hp : 0 ≤ C * X / J ^ a := by positivity
  exact (div_le_div_of_nonneg_right hh (by norm_num)).trans (by linarith)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticSecondPoisson
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The second Poisson formula for the actual quadratic Fourier test -/

namespace Ostmann

open MeasureTheory Set
open scoped Classical BigOperators SchwartzMap FourierTransform

theorem quadraticFourierSquare_fourier_zero (ρ : 𝓢(ℝ, ℂ)) (a : ℝ)
    (ha : 1 ≤ |a|) (hρ : ∀ t < 1 / 2, ρ t = 0) :
    𝓕 (quadraticFourierSquare ρ a ha) 0 =
      (quadraticFresnelPhase a / (Real.sqrt |a| : ℂ)) *
        ∫ x in Ioi (0 : ℝ), ρ (x ^ 2) := by
  rw [quadratic_fourier_phase_integral]
  simpa only [mul_zero, neg_zero, realAdditivePhase_zero, one_mul,
    quadraticFourierSquare_apply] using quadratic_fresnel_main ρ a ha hρ

theorem quadraticSecondPoissonCore_eq (q : ℕ) (ρ : 𝓢(ℝ, ℂ))
    (a : ℝ) (ha : 1 ≤ |a|) (hρ : ∀ t < 1 / 2, ρ t = 0)
    (X U V : ℝ) (L : ℕ) :
    quadraticSecondPoissonCore q ρ a ha X U V L =
      quadraticPoissonCore q (quadraticFourierSquare ρ a ha) X U V L / 2 := by
  unfold quadraticSecondPoissonCore quadraticPoissonCore
  rw [quadraticFourierSquare_fourier_zero ρ a ha hρ, quadraticFourierSquare_apply]
  simp only [zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero]

theorem quadratic_second_poisson (ρ : 𝓢(ℝ, ℂ)) (a : ℝ)
    (ha : 1 ≤ |a|) (hρ : ∀ t < 1 / 2, ρ t = 0) (A : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ q : ℕ, [NeZero q] → q ≠ 1 →
      ∀ X U V J : ℝ, 0 < X → 0 < U → 0 < V → 1 ≤ J →
      U * J ≤ X → X * J ≤ V → ∀ L : ℕ, (V / X) ^ 2 ≤ (L : ℝ) + 1 →
      ‖(∑' n : ℕ+, (1 : DirichletCharacter ℂ q) (n : ZMod q) *
        𝓕 ρ (a * ((n : ℝ) / X) ^ 2)) -
          quadraticSecondPoissonCore q ρ a ha X U V L‖ ≤ C * X / J ^ A := by
  obtain ⟨C, hC, hc⟩ := quadratic_uniform_positive_poisson
    (quadraticFourierSquare ρ a ha) (quadraticFourierSquare_even ρ a ha) A
  refine ⟨C, hC, ?_⟩
  intro q _ hq X U V J hX hU hV hJ hUJ hJV L hL
  simpa only [quadraticSecondPoissonCore_eq q ρ a ha hρ X U V L,
    quadraticFourierSquare_apply] using hc q hq X U V J hX hU hV hJ hUJ hJV L hL

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticSecondScale
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual square-root scale in the second Poisson transform -/

namespace Ostmann

theorem quadraticSecondScale_pos {M : ℝ} {e q b : ℕ}
    (hM : 0 < M) (he : 0 < e) (hq : 0 < q) (hb : 0 < b) :
    0 < quadraticSecondScale M e q b := by
  unfold quadraticSecondScale
  exact Real.sqrt_pos.mpr (by positivity)

theorem quadraticSecondScale_argument {M : ℝ} {e q b : ℕ}
    (hM : 0 < M) (he : 0 < e) (hq : 0 < q) (hb : 0 < b) (a c : ℝ) :
    a * (c / quadraticSecondScale M e q b) ^ 2 =
      a * b * c ^ 2 / ((e : ℝ) * q / M) := by
  rw [div_pow, quadraticSecondScale, Real.sq_sqrt (by positivity)]
  field_simp

theorem quadraticSecondScale_dyadic {M B N : ℝ} {e q b : ℕ}
    (hM : 0 < M) (hB : 0 < B) (hN : 0 < N) (he : 0 < e)
    (hb : B ≤ b) (hb' : (b : ℝ) ≤ 2 * B)
    (hq : N ^ 2 ≤ q) (hq' : (q : ℝ) ≤ 4 * N ^ 2) :
    let X₀ := Real.sqrt ((e : ℝ) * N ^ 2 / (M * B))
    X₀ / 2 ≤ quadraticSecondScale M e q b ∧
      quadraticSecondScale M e q b ≤ 2 * X₀ := by
  have hb₀ : 0 < (b : ℝ) := hB.trans_le hb
  have hq₀ : 0 < (q : ℝ) := (sq_pos_of_pos hN).trans_le hq
  have he₀ : 0 < (e : ℝ) := by exact_mod_cast he
  have hlo : (e : ℝ) * N ^ 2 / (M * B) ≤
      2 * ((e : ℝ) * q / (M * b)) := by
    calc
      _ = 2 * ((e : ℝ) * N ^ 2 / (M * (2 * B))) := by ring
      _ ≤ 2 * ((e : ℝ) * q / (M * (2 * B))) := by gcongr
      _ ≤ _ := by gcongr
  have hhi : (e : ℝ) * q / (M * b) ≤
      4 * ((e : ℝ) * N ^ 2 / (M * B)) := by
    calc
      _ ≤ (e : ℝ) * q / (M * B) := by gcongr
      _ ≤ (e : ℝ) * (4 * N ^ 2) / (M * B) := by gcongr
      _ = _ := by ring
  dsimp
  have hs₀ := Real.sq_sqrt (show 0 ≤ (e : ℝ) * N ^ 2 / (M * B) by positivity)
  have hs := Real.sq_sqrt (show 0 ≤ (e : ℝ) * q / (M * b) by positivity)
  have hn₀ := Real.sqrt_nonneg ((e : ℝ) * N ^ 2 / (M * B))
  have hn := Real.sqrt_nonneg ((e : ℝ) * q / (M * b))
  unfold quadraticSecondScale
  constructor <;> nlinarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticSecondCutoffs
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One pair-independent Poisson cutoff on a dyadic block -/

namespace Ostmann

theorem quadratic_second_cutoffs {X₀ X J : ℝ}
    (hX₀ : 0 < X₀) (hJ : 1 ≤ J) (hlo : X₀ / 2 ≤ X) (hhi : X ≤ 2 * X₀) :
    0 < quadraticSecondLower X₀ J ∧ 0 < quadraticSecondUpper X₀ J ∧
      quadraticSecondLower X₀ J * J ≤ X ∧
      X * J ≤ quadraticSecondUpper X₀ J ∧
      (quadraticSecondUpper X₀ J / X) ^ 2 ≤ (quadraticSecondWindow J : ℝ) + 1 := by
  have hJ₀ : 0 < J := lt_of_lt_of_le zero_lt_one hJ
  have hX : 0 < X := (half_pos hX₀).trans_le hlo
  have hlow : quadraticSecondLower X₀ J * J = X₀ / 2 := by
    unfold quadraticSecondLower
    field_simp
  have hratio : quadraticSecondUpper X₀ J / X ≤ 4 * J := by
    rw [div_le_iff₀ hX]
    unfold quadraticSecondUpper
    nlinarith [mul_le_mul_of_nonneg_right hlo hJ₀.le]
  refine ⟨by unfold quadraticSecondLower; positivity,
    by unfold quadraticSecondUpper; positivity, hlow ▸ hlo,
    mul_le_mul_of_nonneg_right hhi hJ₀.le, ?_⟩
  have hs : (quadraticSecondUpper X₀ J / X) ^ 2 ≤ (4 * J) ^ 2 :=
    (sq_le_sq₀ (by unfold quadraticSecondUpper; positivity) (by positivity)).mpr hratio
  have hc : 16 * J ^ 2 ≤ (quadraticSecondWindow J : ℝ) := Nat.le_ceil _
  nlinarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticSmallKernelPoisson
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual small-squarefree-kernel Poisson formula -/

namespace Ostmann

open MeasureTheory Set
open scoped Classical BigOperators SchwartzMap FourierTransform

theorem quadraticSmallSquareTest_apply (ρ : 𝓢(ℝ, ℂ)) (x : ℝ) :
    quadraticSmallSquareTest ρ x = ρ (x ^ 2) := by
  simp only [quadraticSmallSquareTest, quadraticSquareCompose_apply, one_mul]

theorem quadraticSmallSquareTest_even (ρ : 𝓢(ℝ, ℂ)) :
    Function.Even (quadraticSmallSquareTest ρ) :=
  quadraticSquareCompose_even ρ 1 _

theorem quadraticSmallSquareTest_fourier_zero (ρ : 𝓢(ℝ, ℂ)) :
    𝓕 (quadraticSmallSquareTest ρ) 0 = 2 * ∫ x in Ioi (0 : ℝ), ρ (x ^ 2) := by
  let ψ := quadraticSmallSquareTest ρ
  have heq : (∫ x in Iic (0 : ℝ), ψ x) = ∫ x in Ioi (0 : ℝ), ψ x := by
    calc
      _ = ∫ x in Ioi (0 : ℝ), ψ (-x) := by
        simpa only [neg_zero] using (integral_comp_neg_Ioi 0 ψ).symm
      _ = _ := setIntegral_congr_fun measurableSet_Ioi
        (fun x _ => quadraticSmallSquareTest_even ρ x)
  rw [quadratic_fourier_phase_integral]
  simp only [mul_zero, neg_zero, realAdditivePhase_zero, one_mul]
  change (∫ x : ℝ, ψ x) = _
  rw [← integral_add_compl (s := Ioi (0 : ℝ)) measurableSet_Ioi ψ.integrable,
    compl_Ioi, heq]
  simp only [ψ, quadraticSmallSquareTest_apply]
  ring

theorem quadraticSmallPoissonCore_eq (q : ℕ) (ρ : 𝓢(ℝ, ℂ)) (hρ : ρ 0 = 0)
    (X U V : ℝ) (L : ℕ) :
    quadraticSmallPoissonCore q ρ X U V L =
      quadraticPoissonCore q (quadraticSmallSquareTest ρ) X U V L / 2 := by
  have hzero : quadraticSmallSquareTest ρ 0 = 0 := by
    simpa only [quadraticSmallSquareTest_apply, zero_pow (by decide : 2 ≠ 0)] using hρ
  have hsum (F : Finset ℕ) (g : ℕ → ℂ) :
      (∑ d ∈ F, (ArithmeticFunction.moebius d : ℂ) * ((X / d : ℝ) : ℂ) * g d) =
      (X : ℂ) * ∑ d ∈ F, ((ArithmeticFunction.moebius d : ℂ) / d) * g d := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d _
    rw [Complex.ofReal_div, Complex.ofReal_natCast]
    ring
  have hlarge : (∑ d ∈ q.divisors.filter (fun d : ℕ => V < (d : ℝ)),
      (ArithmeticFunction.moebius d : ℂ) * ((X / d : ℝ) : ℂ)) =
      (X : ℂ) * ∑ d ∈ q.divisors.filter (fun d : ℕ => V < (d : ℝ)),
        (ArithmeticFunction.moebius d : ℂ) / d := by
    simpa only [mul_one] using hsum (q.divisors.filter (fun d : ℕ => V < (d : ℝ))) (fun _ => 1)
  unfold quadraticSmallPoissonCore quadraticPoissonCore
  rw [hzero, quadraticSmallSquareTest_fourier_zero, hlarge, hsum]
  ring

theorem quadratic_small_kernel_poisson (ρ : 𝓢(ℝ, ℂ)) (hρ : ρ 0 = 0) (A : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ q : ℕ, [NeZero q] → q ≠ 1 →
      ∀ X U V J : ℝ, 0 < X → 0 < U → 0 < V → 1 ≤ J →
      U * J ≤ X → X * J ≤ V → ∀ L : ℕ, (V / X) ^ 2 ≤ (L : ℝ) + 1 →
      ‖(∑' n : ℕ+, (1 : DirichletCharacter ℂ q) (n : ZMod q) *
        ρ (((n : ℝ) / X) ^ 2)) - quadraticSmallPoissonCore q ρ X U V L‖ ≤
          C * X / J ^ A := by
  obtain ⟨C, hC, hc⟩ := quadratic_uniform_positive_poisson
    (quadraticSmallSquareTest ρ) (quadraticSmallSquareTest_even ρ) A
  refine ⟨C, hC, ?_⟩
  intro q _ hq X U V J hX hU hV hJ hUJ hJV L hL
  simpa only [quadraticSmallPoissonCore_eq q ρ hρ X U V L,
    quadraticSmallSquareTest_apply] using hc q hq X U V J hX hU hV hJ hUJ hJV L hL

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticSmallKernelScale
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Common cutoffs for the original small-squarefree-kernel block -/

namespace Ostmann

open scoped SchwartzMap BigOperators

theorem quadraticSmallScale_pos {M : ℝ} {b : ℕ} (hM : 0 < M) (hb : 0 < b) :
    0 < quadraticSmallScale M b := by unfold quadraticSmallScale; positivity

theorem quadraticSmallScale_argument {M : ℝ} {b : ℕ}
    (hM : 0 < M) (hb : 0 < b) (x : ℝ) :
    (x / quadraticSmallScale M b) ^ 2 = x ^ 2 * b / M := by
  rw [div_pow, quadraticSmallScale, Real.sq_sqrt (by positivity)]
  field_simp

theorem quadraticSmallScale_dyadic {M B : ℝ} {b : ℕ}
    (hM : 0 < M) (hB : 0 < B) (hb : B ≤ b) (hb' : (b : ℝ) ≤ 2 * B) :
    Real.sqrt (M / B) / 2 ≤ quadraticSmallScale M b ∧
      quadraticSmallScale M b ≤ 2 * Real.sqrt (M / B) := by
  have hb₀ : 0 < (b : ℝ) := hB.trans_le hb
  have hlo : M / B ≤ 2 * (M / b) := by
    calc
      _ = 2 * (M / (2 * B)) := by ring
      _ ≤ _ := by gcongr
  have hhi : M / b ≤ M / B := div_le_div_of_nonneg_left hM.le hB hb
  have hs₀ := Real.sq_sqrt (div_nonneg hM.le hB.le)
  have hs := Real.sq_sqrt (div_nonneg hM.le hb₀.le)
  have hn₀ := Real.sqrt_nonneg (M / B)
  have hn := Real.sqrt_nonneg (M / b)
  unfold quadraticSmallScale
  constructor <;> nlinarith

theorem quadratic_small_dyadic (ρ : 𝓢(ℝ, ℂ)) (hρ : ρ 0 = 0) (A : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M B J : ℝ), 0 < M → 0 < B → 1 ≤ J →
      ∀ (q b : ℕ), [NeZero q] → q ≠ 1 → B ≤ b → (b : ℝ) ≤ 2 * B →
      ‖(∑' n : ℕ+, (1 : DirichletCharacter ℂ q) (n : ZMod q) *
        ρ ((n : ℝ) ^ 2 * b / M)) - quadraticSmallDyadicCore ρ M B J q b‖ ≤
          C * quadraticSmallScale M b / J ^ A := by
  obtain ⟨C, hC, hc⟩ := quadratic_small_kernel_poisson ρ hρ A
  refine ⟨C, hC, ?_⟩
  intro M B J hM hB hJ q b _ hq hb hb'
  have hb₀ : 0 < b := by exact_mod_cast (hB.trans_le hb)
  obtain ⟨hlo, hhi⟩ := quadraticSmallScale_dyadic hM hB hb hb'
  obtain ⟨hU, hV, hUX, hXV, hL⟩ := quadratic_second_cutoffs
    (show 0 < Real.sqrt (M / B) by positivity) hJ hlo hhi
  simpa only [quadraticSmallScale_argument hM hb₀, quadraticSmallDyadicCore] using
    hc q hq (quadraticSmallScale M b)
      (quadraticSecondLower (Real.sqrt (M / B)) J)
      (quadraticSecondUpper (Real.sqrt (M / B)) J) J
      (quadraticSmallScale_pos hM hb₀) hU hV hJ hUX hXV (quadraticSecondWindow J) hL

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticSieveWeight
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The fixed nonnegative smoothing weight in Heath-Brown's argument -/

namespace Ostmann

open scoped SchwartzMap BigOperators

theorem quadraticSieveWeight_apply (x : ℝ) :
    quadraticSieveWeight x = (quadraticSieveBump x : ℂ) := rfl

theorem quadraticSieveBump_nonneg (x : ℝ) : 0 ≤ quadraticSieveBump x :=
  quadraticSieveBump.nonneg

theorem quadraticSieveBump_le_one (x : ℝ) : quadraticSieveBump x ≤ 1 :=
  quadraticSieveBump.le_one

theorem quadraticSieveBump_eq_zero {x : ℝ} (hx : x ≤ 1 / 2 ∨ 5 / 2 ≤ x) :
    quadraticSieveBump x = 0 := by
  apply quadraticSieveBump.zero_of_le_dist
  change 1 ≤ |x - 3 / 2|
  rcases hx with hx | hx
  · rw [abs_of_nonpos (by linarith)]
    linarith
  · rw [abs_of_nonneg (by linarith)]
    linarith

theorem quadraticSieveWeight_eq_zero {x : ℝ} (hx : x ≤ 1 / 2 ∨ 5 / 2 ≤ x) :
    quadraticSieveWeight x = 0 := by
  rw [quadraticSieveWeight_apply, quadraticSieveBump_eq_zero hx, Complex.ofReal_zero]

theorem quadraticSieveWeight_zero : quadraticSieveWeight 0 = 0 :=
  quadraticSieveWeight_eq_zero (Or.inl (by norm_num))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticSmoothedSquareSum
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact finite support for the small-kernel Poisson sum -/

namespace Ostmann

open scoped Classical BigOperators

theorem quadratic_pnat_sum_eq_finite (R : ℕ) (f : ℕ → ℂ) (hzero : f 0 = 0)
    (htail : ∀ n, R < n → f n = 0) :
    (∑' n : ℕ+, f n) = ∑ n ∈ Finset.Icc 1 R, f n := by
  rw [tsum_pnat_eq_tsum_of_eq_zero hzero]
  apply tsum_eq_sum
  intro n hn
  by_cases hz : n = 0
  · simpa only [hz] using hzero
  · apply htail
    simp only [Finset.mem_Icc, not_and_or, not_le] at hn
    omega

theorem quadratic_sieve_weight_square_zero {M b n : ℕ}
    (hM : 0 < M) (hb : 0 < b) (hn : 3 * M < n) :
    quadraticSieveWeight ((n : ℝ) ^ 2 * b / M) = 0 := by
  apply quadraticSieveWeight_eq_zero (Or.inr ?_)
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hbR : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hnR : (3 : ℝ) * M < n := by exact_mod_cast hn
  have hn₁ : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hn₂ : (n : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  have hprod : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 * b := by nlinarith [sq_nonneg (n : ℝ)]
  apply (le_div_iff₀ hMR).mpr
  nlinarith

theorem quadratic_small_square_sum_finite {M b : ℕ} (hM : 0 < M) (hb : 0 < b)
    (q : ℕ) :
    (∑' n : ℕ+, (1 : DirichletCharacter ℂ q) (n : ZMod q) *
      quadraticSieveWeight ((n : ℝ) ^ 2 * b / M)) =
    ∑ n ∈ Finset.Icc 1 (3 * M), (1 : DirichletCharacter ℂ q) (n : ZMod q) *
      quadraticSieveWeight ((n : ℝ) ^ 2 * b / M) := by
  apply quadratic_pnat_sum_eq_finite (3 * M)
    (fun n : ℕ => (1 : DirichletCharacter ℂ q) (n : ZMod q) *
      quadraticSieveWeight ((n : ℝ) ^ 2 * b / M))
  · simp only [Nat.cast_zero, zero_pow (by decide : 2 ≠ 0), zero_mul, zero_div,
      quadraticSieveWeight_zero, mul_zero]
  · intro n hn
    rw [quadratic_sieve_weight_square_zero hM hb hn, mul_zero]

theorem quadratic_small_kernel_sum_rectangular (R K : ℕ) (f : ℕ → ℂ)
    (htail : ∀ n, R < n → f n = 0) :
    (∑ m ∈ quadraticSmallKernelRange R K, f m) =
      ∑ b ∈ oddSquarefreeRange K, ∑ c ∈ Finset.Icc 1 R,
        if Odd c then f (c ^ 2 * b) else 0 := by
  rw [sum_quadraticSmallKernelRange]
  unfold quadraticSmallKernelPairs
  rw [Finset.sum_filter, Finset.product_eq_sprod, Finset.sum_product, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  by_cases hc : Odd c
  · by_cases hb : c ^ 2 * b ≤ R
    · simp only [hc, hb, and_self, ite_true, if_true]
    · simp only [hc, hb, and_false, ite_false, if_false, ite_true, if_true,
        htail (c ^ 2 * b) (lt_of_not_ge hb)]
  · simp only [hc, false_and, ite_false, if_false]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticSmallPairTransform
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact small-kernel pair sum as the positive coprime Poisson sum -/

namespace Ostmann

open scoped Classical BigOperators

theorem quadratic_principal_nat (q n : ℕ) :
    (1 : DirichletCharacter ℂ q) (n : ZMod q) =
      if n.Coprime q then 1 else 0 := by
  by_cases hn : n.Coprime q
  · rw [ite_eq_left hn]
    exact MulChar.one_apply ((ZMod.isUnit_iff_coprime n q).mpr hn)
  · rw [ite_eq_right hn]
    exact (1 : DirichletCharacter ℂ q).map_nonunit
      (fun h => hn ((ZMod.isUnit_iff_coprime n q).mp h))

theorem quadratic_odd_coprime_mask (q n : ℕ) :
    (1 : DirichletCharacter ℂ (2 * q)) (n : ZMod (2 * q)) =
      (if Odd n then (1 : ℂ) else 0) * (if n.Coprime q then 1 else 0) := by
  rw [quadratic_principal_nat]
  simp only [Nat.coprime_mul_iff_right, Nat.coprime_two_right]
  split_ifs <;> simp_all

theorem quadratic_sieve_weight_linear_zero {M n : ℕ} (hM : 0 < M) (hn : 3 * M < n) :
    quadraticSieveWeight ((n : ℝ) / M) = 0 := by
  apply quadraticSieveWeight_eq_zero (Or.inr ?_)
  apply (le_div_iff₀ (show (0 : ℝ) < M by exact_mod_cast hM)).mpr
  have hh : (3 : ℝ) * M < n := by exact_mod_cast hn
  nlinarith [show (0 : ℝ) < M by exact_mod_cast hM]

theorem quadratic_small_pair_transform {M : ℕ} (hM : 0 < M) (K : ℕ)
    {n₁ n₂ : ℕ} (h₁ : Squarefree n₁) (h₂ : Squarefree n₂) :
    (∑ m ∈ quadraticSmallKernelRange (3 * M) K,
      quadraticSieveWeight ((m : ℝ) / M) *
        (jacobiSym m n₁ : ℂ) * (jacobiSym m n₂ : ℂ)) =
    ∑ b ∈ oddSquarefreeRange K,
      ((if b.Coprime (n₁.gcd n₂) then (1 : ℂ) else 0) *
        (jacobiSym b (quadraticPairKernel n₁ n₂) : ℂ)) *
      ∑' c : ℕ+, (1 : DirichletCharacter ℂ (2 * (n₁ * n₂)))
        (c : ZMod (2 * (n₁ * n₂))) *
        quadraticSieveWeight ((c : ℝ) ^ 2 * b / M) := by
  rw [quadratic_small_kernel_sum_rectangular (3 * M) K _ (by
    intro m hm
    rw [quadratic_sieve_weight_linear_zero hM hm, zero_mul, zero_mul])]
  apply Finset.sum_congr rfl
  intro b hb
  have hb₀ : 0 < b := (Finset.mem_Icc.mp (Finset.mem_filter.mp hb).1).1
  rw [quadratic_small_square_sum_finite hM hb₀, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  have hj := jacobi_pair_square_mul c b h₁ h₂
  have hmask := quadratic_odd_coprime_mask (n₁ * n₂) c
  rw [hmask]
  simp only [Nat.cast_mul, Nat.cast_pow] at hj ⊢
  by_cases hc : Odd c
  · simp only [hc, ite_true, if_true]
    rw [mul_assoc, hj]
    ring
  · simp only [hc, ite_false, if_false, zero_mul, mul_zero]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticOddWeightPoisson
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The finite odd smoothing sum equals its original first Poisson transform -/

namespace Ostmann

open scoped Classical BigOperators SchwartzMap FourierTransform

theorem quadratic_integer_weight_finite {M : ℕ} (hM : 0 < M) (F : ℤ → ℂ) :
    (∑' m : ℤ, F m * quadraticSieveWeight ((m : ℝ) / M)) =
      ∑ m ∈ Finset.Icc 1 (3 * M), F m * quadraticSieveWeight ((m : ℝ) / M) := by
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  calc
    _ = ∑ m ∈ Finset.Icc (1 : ℤ) (3 * M),
        F m * quadraticSieveWeight ((m : ℝ) / M) := by
      apply tsum_eq_sum
      intro m hm
      have hz : quadraticSieveWeight ((m : ℝ) / M) = 0 := by
        by_cases hlo : m ≤ 0
        · apply quadraticSieveWeight_eq_zero (Or.inl ?_)
          have hmR : (m : ℝ) ≤ 0 := by exact_mod_cast hlo
          exact (div_nonpos_of_nonpos_of_nonneg hmR hMR.le).trans (by norm_num)
        · have hhi : (3 * M : ℤ) < m := by
            simp only [Finset.mem_Icc] at hm
            omega
          apply quadraticSieveWeight_eq_zero (Or.inr ?_)
          apply (le_div_iff₀ hMR).mpr
          have hh : (3 : ℝ) * M < m := by exact_mod_cast hhi
          nlinarith
      rw [hz, mul_zero]
    _ = _ := by
      apply Finset.sum_bij (fun m _ => m.toNat)
      · intro m hm
        have hh := Finset.mem_Icc.mp hm
        apply Finset.mem_Icc.mpr
        constructor
        · omega
        · omega
      · intro m hm n hn he
        have hm₀ : 0 ≤ m := by have := (Finset.mem_Icc.mp hm).1; omega
        have hn₀ : 0 ≤ n := by have := (Finset.mem_Icc.mp hn).1; omega
        omega
      · intro m hm
        refine ⟨(m : ℤ), ?_, by simp⟩
        have hh := Finset.mem_Icc.mp hm
        apply Finset.mem_Icc.mpr
        constructor <;> exact_mod_cast (by omega : _)
      · intro m hm
        have hm₀ : 0 ≤ m := by have := (Finset.mem_Icc.mp hm).1; omega
        have he : (m.toNat : ℤ) = m := Int.toNat_of_nonneg hm₀
        have hr : (m.toNat : ℝ) = (m : ℝ) := by exact_mod_cast he
        rw [he, hr]

theorem quadratic_odd_kernel_poisson {M D q : ℕ} (hM : 0 < M) [NeZero D] [NeZero q]
    (hq : Squarefree q) (ho : Odd q) :
    (∑ m ∈ quadraticOddRange (3 * M), quadraticSieveWeight ((m : ℝ) / M) *
      (if (m : ℤ).gcd D = 1 then (1 : ℂ) else 0) * (jacobiSym m q : ℂ)) =
    quadraticGaussMultiplier q * ∑ e ∈ (2 * D).divisors,
      (ArithmeticFunction.moebius e : ℂ) *
        (((M : ℝ) / ((e : ℝ) * Real.sqrt q) : ℝ) : ℂ) *
        ∑' h : ℤ, (jacobiSym ((e : ℤ) * h) q : ℂ) *
          𝓕 quadraticSieveWeight ((h : ℝ) * M / ((e : ℝ) * q)) := by
  have hD : 2 * D ≠ 0 := mul_ne_zero (by decide) (NeZero.ne D)
  have : NeZero (2 * D) := ⟨hD⟩
  rw [← quadratic_coprime_jacobi_poisson hq ho quadraticSieveWeight
    (show (0 : ℝ) < M by exact_mod_cast hM),
    quadratic_integer_weight_finite hM]
  unfold quadraticOddRange
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro m _
  simp only [Int.cast_natCast]
  rw [quadratic_odd_coprime_mask]
  have hg : ((m : ℤ).gcd D = 1) ↔ m.Coprime D := by
    simp only [Int.gcd, Int.natAbs_natCast]
  simp only [hg]
  by_cases hm : Odd m
  · rw [ite_eq_left hm, ite_eq_left hm]
    ring
  · rw [ite_eq_right hm, ite_eq_right hm]
    ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticSmallMomentTransform
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual small-kernel moment after the first finite rearrangement -/

namespace Ostmann

open scoped Classical BigOperators ComplexConjugate

theorem quadratic_principal_pair_reduction {n₁ n₂ D : ℕ}
    (hg : n₁.gcd n₂ = D) (c : ℕ) :
    (1 : DirichletCharacter ℂ (2 * (n₁ * n₂))) (c : ZMod (2 * (n₁ * n₂))) =
      (1 : DirichletCharacter ℂ (2 * (quadraticPairKernel n₁ n₂ * D)))
        (c : ZMod (2 * (quadraticPairKernel n₁ n₂ * D))) := by
  rw [quadratic_principal_nat, quadratic_principal_nat,
    ← quadraticPairKernel_factor n₁ n₂, hg]
  simp only [Nat.coprime_mul_iff_right, Nat.coprime_pow_right_iff (by decide : 0 < 2)]
  congr 1
  exact propext (by tauto)

theorem quadratic_pair_sum_gcd {R : Type*} [AddCommMonoid R] (N : ℕ) (F : ℕ × ℕ → R) :
    (∑ z ∈ (oddSquarefreeRange N).product (oddSquarefreeRange N), F z) =
      ∑ D ∈ Finset.Icc 1 N, ∑ z ∈ quadraticGcdPairs N D, F z := by
  have hmaps (z : ℕ × ℕ)
      (hz : z ∈ (oddSquarefreeRange N).product (oddSquarefreeRange N)) :
      z.1.gcd z.2 ∈ Finset.Icc 1 N := by
    have hz₁ := (Finset.mem_product.mp hz).1
    have hr := Finset.mem_Icc.mp (Finset.mem_filter.mp hz₁).1
    exact Finset.mem_Icc.mpr ⟨Nat.gcd_pos_of_pos_left _ hr.1,
      (Nat.gcd_le_left _ hr.1).trans hr.2⟩
  exact (Finset.sum_fiberwise_of_maps_to hmaps F).symm

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticGcdRemainder
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Summing uniform pair remainders against the actual coefficients -/

namespace Ostmann

open scoped Classical BigOperators ComplexConjugate

theorem quadratic_pair_coefficient_mass (N : ℕ) (v : ℕ → ℂ) :
    (∑ z ∈ (oddSquarefreeRange N).product (oddSquarefreeRange N),
      ‖v z.1‖ * ‖v z.2‖) ≤ (N : ℝ) * quadraticSieveEnergy N v := by
  have he : (∑ z ∈ (oddSquarefreeRange N).product (oddSquarefreeRange N),
      ‖v z.1‖ * ‖v z.2‖) = (∑ n ∈ oddSquarefreeRange N, ‖v n‖) ^ 2 := by
    rw [Finset.product_eq_sprod, Finset.sum_product]
    simp_rw [← Finset.mul_sum]
    rw [← Finset.sum_mul, pow_two]
  rw [he]
  calc
    _ ≤ ((oddSquarefreeRange N).card : ℝ) * quadraticSieveEnergy N v :=
      sq_sum_le_card_mul_sum_sq
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (by exact_mod_cast oddSquarefreeRange_card_le N)
      (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

theorem quadratic_gcd_remainder_bound (N : ℕ) (v : ℕ → ℂ)
    (E : ℕ → ℕ × ℕ → ℂ) {T : ℝ} (hT : 0 ≤ T)
    (hE : ∀ D ∈ Finset.Icc 1 N, ∀ z ∈ quadraticGcdPairs N D, ‖E D z‖ ≤ T) :
    ‖quadraticGcdRemainder N v E‖ ≤ T * N * quadraticSieveEnergy N v := by
  unfold quadraticGcdRemainder
  calc
    _ ≤ ∑ D ∈ Finset.Icc 1 N, ∑ z ∈ quadraticGcdPairs N D,
        ‖v z.1‖ * ‖v z.2‖ * T := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro D hD
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro z hz
      simp only [norm_mul, Complex.norm_conj]
      exact mul_le_mul_of_nonneg_left (hE D hD z hz) (by positivity)
    _ = T * ∑ z ∈ (oddSquarefreeRange N).product (oddSquarefreeRange N),
        ‖v z.1‖ * ‖v z.2‖ := by
      rw [← quadratic_pair_sum_gcd]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      ring
    _ ≤ T * ((N : ℝ) * quadraticSieveEnergy N v) :=
      mul_le_mul_of_nonneg_left (quadratic_pair_coefficient_mass N v) hT
    _ = _ := by ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticSmallMomentError
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The complete small-kernel moment has a uniformly controlled Poisson error -/

namespace Ostmann

open scoped Classical BigOperators ComplexConjugate

theorem quadratic_small_dyadic_uniform (A : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M J : ℝ), 0 < M → 1 ≤ J →
      ∀ q : ℕ, [NeZero q] → q ≠ 1 → ∀ b : ℕ, 0 < b →
      ‖(∑' c : ℕ+, (1 : DirichletCharacter ℂ q) (c : ZMod q) *
        quadraticSieveWeight ((c : ℝ) ^ 2 * b / M)) -
          quadraticSmallDyadicCore quadraticSieveWeight M b J q b‖ ≤
        C * Real.sqrt M / J ^ A := by
  obtain ⟨C, hC, hc⟩ := quadratic_small_dyadic quadraticSieveWeight quadraticSieveWeight_zero A
  refine ⟨C, hC, ?_⟩
  intro M J hM hJ q _ hq b hb
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hb₁ : (1 : ℝ) ≤ b := by exact_mod_cast hb
  apply (hc M b J hM hbR hJ q b hq le_rfl (by linarith)).trans
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply mul_le_mul_of_nonneg_left _ hC.le
  exact Real.sqrt_le_sqrt (div_le_self hM.le hb₁)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticSmallMomentMain
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The literal small-kernel moment: original main term and two corrections -/

namespace Ostmann

open MeasureTheory Set
open scoped Classical BigOperators ComplexConjugate FourierTransform

theorem quadratic_small_pair_core (M J : ℝ) (q b : ℕ) :
    quadraticSmallDyadicCore quadraticSieveWeight M b J q b =
      (quadraticSmallScale M b : ℂ) * ((q.totient : ℂ) / q) *
        (∫ x in Ioi (0 : ℝ), quadraticSieveWeight (x ^ 2)) +
      quadraticSmallPairCorrection M J q b := by
  unfold quadraticSmallDyadicCore quadraticSmallPoissonCore quadraticSmallPairCorrection
  dsimp only
  simp only [quadraticSmallScale]
  ring_nf

theorem quadraticGcdPairs_empty_of_not_odd (N D : ℕ) (hD : ¬ Odd D) :
    quadraticGcdPairs N D = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro z hz
  obtain ⟨hz, hg⟩ := Finset.mem_filter.mp hz
  have hs := (Finset.mem_product.mp hz).1
  have ho := (Finset.mem_filter.mp hs).2.1
  apply hD
  rw [← hg]
  exact ho.of_dvd_nat (Nat.gcd_dvd_left z.1 z.2)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticOffDiagonalPairSums
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original off-diagonal pairs in the two Poisson transforms -/

namespace Ostmann

open scoped Classical BigOperators ComplexConjugate

theorem quadratic_small_pair_sum_eq {M N D : ℕ} (hM : 0 < M) (K : ℕ)
    {z : ℕ × ℕ} (hz : z ∈ quadraticGcdPairs N D) :
    (∑ m ∈ quadraticSmallKernelRange (3 * M) K,
      quadraticSieveWeight ((m : ℝ) / M) * (jacobiSym m z.1 : ℂ) * (jacobiSym m z.2 : ℂ)) =
        quadraticSmallPairSum M K D (quadraticPairKernel z.1 z.2) := by
  obtain ⟨hz, hg⟩ := Finset.mem_filter.mp hz
  obtain ⟨hs, ht⟩ := Finset.mem_product.mp hz
  rw [quadratic_small_pair_transform hM K (Finset.mem_filter.mp hs).2.2
    (Finset.mem_filter.mp ht).2.2]
  unfold quadraticSmallPairSum
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro b _
  rw [hg]
  have he : (∑' c : ℕ+, (1 : DirichletCharacter ℂ (2 * (z.1 * z.2)))
      (c : ZMod (2 * (z.1 * z.2))) * quadraticSieveWeight ((c : ℝ) ^ 2 * b / M)) =
      ∑' c : ℕ+, (1 : DirichletCharacter ℂ (2 * (quadraticPairKernel z.1 z.2 * D)))
      (c : ZMod (2 * (quadraticPairKernel z.1 z.2 * D))) *
        quadraticSieveWeight ((c : ℝ) ^ 2 * b / M) := by
    apply tsum_congr
    intro c
    rw [quadratic_principal_pair_reduction hg]
  rw [he]
  by_cases hb : D.Coprime b
  · rw [ite_eq_left hb.symm, ite_eq_left hb, one_mul]
  · rw [ite_eq_right (fun h => hb h.symm), ite_eq_right hb, zero_mul, zero_mul]

theorem quadratic_odd_pair_poisson {M N D : ℕ} (hM : 0 < M)
    {z : ℕ × ℕ} (hz : z ∈ quadraticGcdPairs N D) :
    (∑ m ∈ quadraticOddRange (3 * M),
      quadraticSieveWeight ((m : ℝ) / M) * (jacobiSym m z.1 : ℂ) * (jacobiSym m z.2 : ℂ)) =
        quadraticFirstKernelTransform M D (quadraticPairKernel z.1 z.2) := by
  obtain ⟨hz, hg⟩ := Finset.mem_filter.mp hz
  obtain ⟨hs, ht⟩ := Finset.mem_product.mp hz
  have hsf := quadraticPairKernel_squarefree (Finset.mem_filter.mp hs).2.2
    (Finset.mem_filter.mp ht).2.2
  have ho := quadraticPairKernel_odd (Finset.mem_filter.mp hs).2.1 (Finset.mem_filter.mp ht).2.1
  have hD : 0 < D := by
    rw [← hg]
    exact Nat.gcd_pos_of_pos_left _ (Finset.mem_Icc.mp (Finset.mem_filter.mp hs).1).1
  have : NeZero D := ⟨hD.ne'⟩
  have : NeZero (quadraticPairKernel z.1 z.2) := ⟨hsf.ne_zero⟩
  unfold quadraticFirstKernelTransform
  rw [← quadratic_odd_kernel_poisson (D := D) hM hsf ho]
  apply Finset.sum_congr rfl
  intro m _
  have hj := congrArg (fun x : ℤ => (x : ℂ))
    (jacobi_pair_kernel (Finset.mem_filter.mp hs).2.2 (Finset.mem_filter.mp ht).2.2 (m : ℤ))
  rw [hg] at hj
  push_cast at hj
  rw [mul_assoc, hj]
  split_ifs <;> ring

theorem quadratic_rough_pair_transform {M N D : ℕ} (hM : 0 < M) (K : ℕ)
    {z : ℕ × ℕ} (hz : z ∈ quadraticGcdPairs N D) :
    (∑ m ∈ quadraticRoughKernelRange (3 * M) K,
      quadraticSieveWeight ((m : ℝ) / M) * (jacobiSym m z.1 : ℂ) * (jacobiSym m z.2 : ℂ)) =
      quadraticFirstKernelTransform M D (quadraticPairKernel z.1 z.2) -
        quadraticSmallPairSum M K D (quadraticPairKernel z.1 z.2) := by
  have hs : (quadraticOddRange (3 * M)).filter
      (fun m => ¬ K < quadraticSquarefreePart m) = quadraticSmallKernelRange (3 * M) K := by
    ext m
    simp only [quadraticOddRange, quadraticSmallKernelRange, Finset.mem_filter, not_lt]
    tauto
  have he := Finset.sum_filter_add_sum_filter_not (quadraticOddRange (3 * M))
    (fun m => K < quadraticSquarefreePart m)
    (fun m => quadraticSieveWeight ((m : ℝ) / M) *
      (jacobiSym m z.1 : ℂ) * (jacobiSym m z.2 : ℂ))
  rw [hs, quadratic_small_pair_sum_eq hM K hz, quadratic_odd_pair_poisson hM hz] at he
  exact eq_sub_of_add_eq he

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticGcdCoefficientBridge
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual gcd-removal coefficients for all three divisor corrections -/

namespace Ostmann

open scoped Classical BigOperators ComplexConjugate

theorem quadratic_gcd_coefficient_reindex {N D : ℕ} (hD : Squarefree D) (ho : Odd D)
    (v w : ℕ → ℂ) (F : ℕ → ℂ) :
    (∑ z ∈ quadraticGcdPairs N D,
      v z.1 * conj (w z.2) * F (quadraticPairKernel z.1 z.2)) =
    ∑ z ∈ quadraticGcdPairs (N / D) 1,
      quadraticDivisibilityCoeff D v z.1 * conj (quadraticDivisibilityCoeff D w z.2) * F (z.1 * z.2) := by
  rw [quadratic_gcd_pair_reindex (N := N) hD ho
    (fun s t => v s * conj (w t) * F (quadraticPairKernel s t))]
  apply Finset.sum_congr rfl
  intro z hz
  obtain ⟨_, hg⟩ := Finset.mem_filter.mp hz
  rw [quadraticPairKernel_mul_coprime hD.ne_zero hg]
  unfold quadraticDivisibilityCoeff
  by_cases hs : D.Coprime z.1
  · by_cases ht : D.Coprime z.2
    · rw [ite_eq_left ⟨hs, ht⟩, ite_eq_left hs, ite_eq_left ht]
    · rw [ite_eq_right (fun h => ht h.2), ite_eq_left hs, ite_eq_right ht]
      simp
  · rw [ite_eq_right (fun h => hs h.1), ite_eq_right hs]
    simp

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticRoughBound
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Restriction and divisor descent for the actual rough moment -/

namespace Ostmann

open scoped Classical BigOperators ComplexConjugate

theorem QuadraticRoughBound.mono_constant {M N K : ℕ} {T U : ℝ}
    (h : QuadraticRoughBound M N K T) (hTU : T ≤ U) : QuadraticRoughBound M N K U := by
  intro v
  exact (h v).trans (mul_le_mul_of_nonneg_right hTU (Finset.sum_nonneg fun _ _ => sq_nonneg _))

theorem quadraticRoughEnergy_restrict {N R : ℕ} (hNR : N ≤ R)
    (M K : ℕ) (v : ℕ → ℂ) :
    quadraticRoughEnergy M R K (fun n => if n ∈ oddSquarefreeRange N then v n else 0) =
      quadraticRoughEnergy M N K v := by
  unfold quadraticRoughEnergy quadraticTransposeSum
  apply Finset.sum_congr rfl
  intro m _
  congr 2
  simp only [ite_mul, zero_mul]
  rw [← Finset.sum_filter]
  rw [Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr (oddSquarefreeRange_mono hNR)]

theorem QuadraticRoughBound.mono_second {M N R K : ℕ} {T : ℝ}
    (hNR : N ≤ R) (h : QuadraticRoughBound M R K T) : QuadraticRoughBound M N K T := by
  intro v
  have hh := h (fun n => if n ∈ oddSquarefreeRange N then v n else 0)
  rwa [quadraticRoughEnergy_restrict hNR, quadraticSieveEnergy_restrict hNR] at hh

theorem quadratic_gcd_kernel_remove {N D : ℕ} (hD : Squarefree D) (ho : Odd D)
    (v : ℕ → ℂ) (m : ℤ) :
    quadraticGcdKernelSum N D v m =
      quadraticGcdKernelSum (N / D) 1 (quadraticDivisibilityCoeff D v) m := by
  unfold quadraticGcdKernelSum
  rw [quadratic_gcd_coefficient_reindex hD ho v v (fun q => (jacobiSym m q : ℂ))]
  apply Finset.sum_congr rfl
  intro z hz
  have hg := (Finset.mem_filter.mp hz).2
  simp only [quadraticPairKernel, hg, Nat.div_one]

/-- Removing the gcd and then the coprimality condition only introduces actual
rough moments of divisor-restricted coefficients. -/
theorem quadratic_rough_gcd_moment_divisors {M N K D : ℕ}
    (hD : Squarefree D) (ho : Odd D) (v : ℕ → ℂ) :
    ‖quadraticRoughGcdMoment M N K D v‖ ≤
      ∑ d ∈ Finset.Icc 1 (N / D), quadraticRoughEnergy M (N / D) K
        (fun n => if d ∣ n then quadraticDivisibilityCoeff D v n else 0) := by
  unfold quadraticRoughGcdMoment
  simp_rw [quadratic_gcd_kernel_remove hD ho,
    quadratic_coprime_energy_expansion, Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ m ∈ quadraticRoughKernelRange (3 * M) K, ∑ d ∈ Finset.Icc 1 (N / D),
        quadraticSieveBump ((m : ℝ) / M) *
          ‖quadraticTransposeSum (N / D)
            (fun n => if d ∣ n then quadraticDivisibilityCoeff D v n else 0) m‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro m _
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro d _
      have hμ : ‖(ArithmeticFunction.moebius d : ℂ)‖ ≤ 1 := by
        rw [Complex.norm_intCast]
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)
      have hw : ‖quadraticSieveWeight ((m : ℝ) / M)‖ = quadraticSieveBump ((m : ℝ) / M) := by
        rw [quadraticSieveWeight_apply, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (quadraticSieveBump_nonneg _)]
      by_cases hc : (m : ℤ).gcd D = 1
      · simp only [ite_eq_left hc, norm_mul, mul_one, norm_pow,
          Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), hw]
        simpa only [one_mul] using mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hμ (sq_nonneg ‖quadraticTransposeSum (N / D)
            (fun n => if d ∣ n then quadraticDivisibilityCoeff D v n else 0) m‖))
          (quadraticSieveBump_nonneg ((m : ℝ) / M))
      · simp only [ite_eq_right hc, mul_zero, zero_mul, norm_zero]
        exact mul_nonneg (quadraticSieveBump_nonneg _) (sq_nonneg _)
    _ = _ := by rw [Finset.sum_comm]; rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticRoughDyadic
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Disjoint coefficient blocks for the actual rough moment -/

namespace Ostmann

open scoped Classical BigOperators

theorem quadraticDyadicCoeff_below (N j : ℕ) (v : ℕ → ℂ) {n : ℕ}
    (hn : n < 2 ^ j) : quadraticDyadicCoeff N j v n = 0 := by
  apply ite_eq_right
  exact fun h => (not_le_of_gt hn) (quadraticDyadicDivisors_bounds h).1

theorem quadraticDyadicDivisors_subset_double (N j : ℕ) :
    quadraticDyadicDivisors N j ⊆ oddSquarefreeRange (2 * 2 ^ j) := by
  intro n hn
  have hmem := (Finset.mem_filter.mp hn).1
  have hbound := (quadraticDyadicDivisors_bounds hn).2
  rw [pow_succ] at hbound
  obtain ⟨hi, ho, hs⟩ := Finset.mem_filter.mp hmem
  exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
    ⟨(Finset.mem_Icc.mp hi).1, by omega⟩, ho, hs⟩

theorem quadraticTransposeSum_dyadic {N j B : ℕ}
    (hB : quadraticDyadicDivisors N j ⊆ oddSquarefreeRange B)
    (v : ℕ → ℂ) (m : ℤ) :
    quadraticTransposeSum B (quadraticDyadicCoeff N j v) m =
      ∑ n ∈ quadraticDyadicDivisors N j, v n * (jacobiSym m n : ℂ) := by
  unfold quadraticTransposeSum quadraticDyadicCoeff
  simp only [ite_mul, zero_mul, ← Finset.sum_filter]
  rw [Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hB]

theorem quadraticDyadicCoeff_energy {N j B : ℕ}
    (hB : quadraticDyadicDivisors N j ⊆ oddSquarefreeRange B) (v : ℕ → ℂ) :
    quadraticSieveEnergy B (quadraticDyadicCoeff N j v) =
      ∑ n ∈ quadraticDyadicDivisors N j, ‖v n‖ ^ 2 := by
  unfold quadraticSieveEnergy quadraticDyadicCoeff
  simp only [apply_ite, norm_zero, ite_pow, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, ← Finset.sum_filter]
  rw [Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hB]

theorem quadratic_dyadic_coeff_energy_sum (N : ℕ) (v : ℕ → ℂ) :
    (∑ j ∈ Finset.range (Nat.log 2 N + 1),
      quadraticSieveEnergy (2 * 2 ^ j) (quadraticDyadicCoeff N j v)) =
      quadraticSieveEnergy N v := by
  simp_rw [quadraticDyadicCoeff_energy (quadraticDyadicDivisors_subset_double N _)]
  exact quadratic_dyadic_divisors_sum N (fun n => ‖v n‖ ^ 2)

theorem quadratic_rough_energy_dyadic (M N K : ℕ) (v : ℕ → ℂ) :
    quadraticRoughEnergy M N K v ≤ (Nat.log 2 N + 1 : ℕ) *
      ∑ j ∈ Finset.range (Nat.log 2 N + 1),
        quadraticRoughEnergy M (2 * 2 ^ j) K (quadraticDyadicCoeff N j v) := by
  have hsum (m : ℤ) : quadraticTransposeSum N v m =
      ∑ j ∈ Finset.range (Nat.log 2 N + 1),
        quadraticTransposeSum (2 * 2 ^ j) (quadraticDyadicCoeff N j v) m := by
    simp_rw [quadraticTransposeSum_dyadic (quadraticDyadicDivisors_subset_double N _)]
    exact (quadratic_dyadic_divisors_sum N _).symm
  unfold quadraticRoughEnergy
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro m _
  rw [hsum]
  have hn := norm_sum_le (Finset.range (Nat.log 2 N + 1))
    (fun j => quadraticTransposeSum (2 * 2 ^ j) (quadraticDyadicCoeff N j v) m)
  have hc := sq_sum_le_card_mul_sum_sq (s := Finset.range (Nat.log 2 N + 1))
    (f := fun j => ‖quadraticTransposeSum (2 * 2 ^ j) (quadraticDyadicCoeff N j v) m‖)
  simp only [Finset.card_range] at hc
  have hp := (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans hc
  have hw := mul_le_mul_of_nonneg_left hp (quadraticSieveBump_nonneg ((m : ℝ) / M))
  simpa only [Finset.mul_sum, mul_left_comm, mul_assoc] using hw

theorem quadraticTransposeSum_trivial (N : ℕ) (v : ℕ → ℂ) (m : ℤ) :
    ‖quadraticTransposeSum N v m‖ ^ 2 ≤ (N : ℝ) * quadraticSieveEnergy N v := by
  have hn := norm_sum_le (oddSquarefreeRange N)
    (fun n => v n * (jacobiSym m n : ℂ))
  have hc := sq_sum_le_card_mul_sum_sq (s := oddSquarefreeRange N)
    (f := fun n => ‖v n * (jacobiSym m n : ℂ)‖)
  have hs : (∑ n ∈ oddSquarefreeRange N, ‖v n * (jacobiSym m n : ℂ)‖ ^ 2) ≤
      quadraticSieveEnergy N v := by
    apply Finset.sum_le_sum
    intro n _
    rcases jacobiSym.trichotomy m n with h | h | h <;> simp [h]
  exact (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans (hc.trans
    (mul_le_mul (by exact_mod_cast oddSquarefreeRange_card_le N) hs
      (Finset.sum_nonneg fun _ _ => sq_nonneg _) (Nat.cast_nonneg _)))

theorem quadratic_rough_bound_trivial (M N K : ℕ) :
    QuadraticRoughBound M N K (3 * (M : ℝ) * N) := by
  intro v
  have hcard : (quadraticRoughKernelRange (3 * M) K).card ≤ 3 * M := by
    apply le_trans (Finset.card_filter_le _ _)
    apply le_trans (Finset.card_filter_le _ _)
    simp
  calc
    _ ≤ ∑ _m ∈ quadraticRoughKernelRange (3 * M) K,
        (N : ℝ) * quadraticSieveEnergy N v := by
      apply Finset.sum_le_sum
      intro m _
      exact (mul_le_mul (quadraticSieveBump_le_one _) (quadraticTransposeSum_trivial N v m)
        (sq_nonneg _) zero_le_one).trans_eq (one_mul _)
    _ = (quadraticRoughKernelRange (3 * M) K).card *
        ((N : ℝ) * quadraticSieveEnergy N v) := by simp
    _ ≤ (3 * (M : ℝ)) * ((N : ℝ) * quadraticSieveEnergy N v) := by
      apply mul_le_mul_of_nonneg_right _
        (mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg fun _ _ => sq_nonneg _))
      exact_mod_cast hcard
    _ = _ := by ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticDyadicCount
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The explicit dyadic-bin count costs only an arbitrarily small power -/

namespace Ostmann

 theorem quadratic_dyadic_count_bound (ε : ℝ) (hε : 0 < ε) (N : ℕ) (hN : 1 ≤ N) :
    ((Nat.log 2 N + 1 : ℕ) : ℝ) ≤
      (1 + (ε * Real.log 2)⁻¹) * (N : ℝ) ^ ε := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hp : (1 : ℝ) ≤ (N : ℝ) ^ ε :=
    Real.one_le_rpow (by exact_mod_cast hN) hε.le
  have hb := Real.natLog_le_logb N 2
  change (Nat.log 2 N : ℝ) ≤ Real.log (N : ℝ) / Real.log 2 at hb
  calc
    _ = (Nat.log 2 N : ℝ) + 1 := by push_cast; rfl
    _ ≤ Real.log (N : ℝ) / Real.log 2 + 1 := by linarith
    _ ≤ ((N : ℝ) ^ ε / ε) / Real.log 2 + (N : ℝ) ^ ε :=
      add_le_add (div_le_div_of_nonneg_right (Real.log_natCast_le_rpow_div N hε) hl.le) hp
    _ = _ := by field_simp; ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticFrequencyTwist
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Absorbing signed square factors into the original coefficient arrays -/

namespace Ostmann

open scoped Classical BigOperators ComplexConjugate SchwartzMap

 theorem quadratic_frequency_character (a : ℤ) (c : ℕ) (m : ℤ) {n : ℕ} (hn : n ≠ 0) :
    (jacobiSym (a * (c : ℤ) ^ 2 * m) n : ℂ) =
      (if c.Coprime n then (jacobiSym a n : ℂ) else 0) * (jacobiSym m n : ℂ) := by
  rw [show a * (c : ℤ) ^ 2 * m = (c : ℤ) ^ 2 * (a * m) by ring,
    jacobi_square_mul c (a * m) hn]
  by_cases hc : c.Coprime n
  · rw [ite_eq_left hc, ite_eq_left hc, jacobiSym.mul_left, Int.cast_mul]
  · rw [ite_eq_right hc, ite_eq_right hc, Int.cast_zero, zero_mul]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticSignedFrequency
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Signed odd-squarefree coordinates for nonzero Poisson frequencies -/

namespace Ostmann

open scoped Classical BigOperators

 theorem quadratic_squarefree_odd_factor {q : ℕ} (hq : Squarefree q) :
    ∃ d b : ℕ, (d = 1 ∨ d = 2) ∧ Odd b ∧ Squarefree b ∧ q = d * b := by
  rcases Nat.even_or_odd q with he | ho
  · obtain ⟨b, hb⟩ := he
    have heq : q = 2 * b := by omega
    have hs : Squarefree (2 * b) := heq ▸ hq
    have hh := Nat.squarefree_mul_iff.mp hs
    exact ⟨2, b, Or.inr rfl, Nat.coprime_two_left.mp hh.1, hh.2.2, heq⟩
  · exact ⟨1, q, Or.inl rfl, ho, hq, (one_mul q).symm⟩

 theorem quadratic_signed_frequency_coordinates {H : ℕ} {h : ℤ}
    (hh : h ≠ 0) (hH : h.natAbs ≤ H) :
    ∃ a ∈ ({1, -1, 2, -2} : Finset ℤ), ∃ c ∈ Finset.Icc 1 H,
      ∃ b ∈ oddSquarefreeRange H, h = a * (c : ℤ) ^ 2 * (b : ℤ) := by
  have habs : 0 < h.natAbs := Int.natAbs_pos.mpr hh
  obtain ⟨q, c, hq, hc, he, hsf⟩ := Nat.sq_mul_squarefree_of_pos habs
  obtain ⟨d, b, hd, hbo, hbs, hdb⟩ := quadratic_squarefree_odd_factor hsf
  have hdpos : 0 < d := by rcases hd with rfl | rfl <;> norm_num
  have hbpos : 0 < b := Nat.pos_of_ne_zero hbs.ne_zero
  have hcH : c ≤ H := by
    apply le_trans _ hH
    have hmul : c ^ 2 ≤ c ^ 2 * q := Nat.le_mul_of_pos_right _ hq
    rw [he] at hmul
    nlinarith
  have hbH : b ≤ H := by
    apply le_trans _ hH
    calc
      b ≤ d * b := Nat.le_mul_of_pos_left _ hdpos
      _ = q := hdb.symm
      _ ≤ c ^ 2 * q := Nat.le_mul_of_pos_left _ (pow_pos hc _)
      _ = _ := he
  have hcMem : c ∈ Finset.Icc 1 H := Finset.mem_Icc.mpr ⟨hc, hcH⟩
  have hbMem : b ∈ oddSquarefreeRange H :=
    Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hbpos, hbH⟩, hbo, hbs⟩
  have heZ : (d : ℤ) * (c : ℤ) ^ 2 * (b : ℤ) = (h.natAbs : ℤ) := by
    have hn : d * c ^ 2 * b = h.natAbs := by rw [← he, hdb]; ring
    exact_mod_cast hn
  by_cases hs : 0 ≤ h
  · refine ⟨d, ?_, c, hcMem, b, hbMem, ?_⟩
    · rcases hd with rfl | rfl <;> simp
    · rw [heZ, Int.natCast_natAbs, abs_of_nonneg hs]
  · refine ⟨-(d : ℤ), ?_, c, hcMem, b, hbMem, ?_⟩
    · rcases hd with rfl | rfl <;> simp
    · rw [neg_mul, neg_mul, heZ, Int.natCast_natAbs, abs_of_neg (lt_of_not_ge hs), neg_neg]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticSignedFrequencyBijection
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Unique signed squarefree coordinates, with exact finite reindexing -/

namespace Ostmann

open scoped Classical BigOperators

private theorem signed_frequency_abs (a : ℤ) (ha : a ∈ ({1, -1, 2, -2} : Finset ℤ)) :
    a.natAbs = 1 ∨ a.natAbs = 2 := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha
  rcases ha with rfl | rfl | rfl | rfl <;> norm_num

private theorem signed_odd_kernel_squarefree {a : ℤ} {b : ℕ}
    (ha : a ∈ ({1, -1, 2, -2} : Finset ℤ)) (hb : Odd b) (hs : Squarefree b) :
    Squarefree (a.natAbs * b) := by
  rcases signed_frequency_abs a ha with hh | hh
  · simpa only [hh, one_mul] using hs
  · rw [hh]
    exact (Nat.squarefree_mul (Nat.coprime_two_left.mpr hb)).mpr
      ⟨Nat.prime_two.squarefree, hs⟩

theorem quadratic_signed_coordinates_injective {a d : ℤ} {c e b f : ℕ}
    (ha : a ∈ ({1, -1, 2, -2} : Finset ℤ))
    (hd : d ∈ ({1, -1, 2, -2} : Finset ℤ))
    (hc : 0 < c) (he : 0 < e) (hb : Odd b) (hf : Odd f)
    (hsb : Squarefree b) (hsf : Squarefree f)
    (hh : a * (c : ℤ) ^ 2 * b = d * (e : ℤ) ^ 2 * f) :
    a = d ∧ c = e ∧ b = f := by
  have habs := congrArg Int.natAbs hh
  simp only [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast] at habs
  have hfactor : c ^ 2 * (a.natAbs * b) = e ^ 2 * (d.natAbs * f) := by
    calc
      _ = a.natAbs * c ^ 2 * b := by ring
      _ = d.natAbs * e ^ 2 * f := habs
      _ = _ := by ring
  obtain ⟨hce, hkernel⟩ := quadratic_squarefree_factor_unique hc.ne' he.ne'
    (signed_odd_kernel_squarefree ha hb hsb) (signed_odd_kernel_squarefree hd hf hsf) hfactor
  have hbf : b = f := by
    obtain ⟨r, hr⟩ := hb
    obtain ⟨s, hs⟩ := hf
    rcases signed_frequency_abs a ha with ha' | ha' <;>
      rcases signed_frequency_abs d hd with hd' | hd' <;>
      simp only [ha', hd', one_mul] at hkernel <;> omega
  refine ⟨?_, hce, hbf⟩
  rw [hce, hbf] at hh
  have heZ : (e : ℤ) ≠ 0 := by exact_mod_cast he.ne'
  have hfZ : (f : ℤ) ≠ 0 := by exact_mod_cast hsf.ne_zero
  exact mul_right_cancel₀ (pow_ne_zero 2 heZ) (mul_right_cancel₀ hfZ hh)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticSignedInfiniteSum
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact infinite signed-frequency coordinates for the first transform -/

namespace Ostmann

open scoped Classical BigOperators

theorem quadraticFrequencyValue_injective : Function.Injective quadraticFrequencyValue := by
  intro z w h
  obtain ⟨ha, hc, hb⟩ := quadratic_signed_coordinates_injective z.1.property w.1.property
    z.2.2.property w.2.2.property z.2.1.property.1 w.2.1.property.1
    z.2.1.property.2 w.2.1.property.2 h
  apply Prod.ext (Subtype.ext ha)
  apply Prod.ext
  · exact Subtype.ext (Subtype.ext hb)
  · exact Subtype.ext hc

theorem quadraticFrequencyValue_range :
    Set.range quadraticFrequencyValue = {h : ℤ | h ≠ 0} := by
  ext h
  constructor
  · rintro ⟨z, rfl⟩
    have ha : (z.1 : ℤ) ≠ 0 := by
      have hm := z.1.property
      simp only [Finset.mem_insert, Finset.mem_singleton] at hm
      rcases hm with hm | hm | hm | hm <;> rw [hm] <;> norm_num
    have hc : ((z.2.2 : ℕ) : ℤ) ≠ 0 := by exact_mod_cast z.2.2.property.ne'
    have hb : ((z.2.1.val : ℕ) : ℤ) ≠ 0 := by exact_mod_cast z.2.1.val.property.ne'
    exact mul_ne_zero (mul_ne_zero ha (pow_ne_zero 2 hc)) hb
  · intro hh
    obtain ⟨a, ha, c, hc, b, hb, he⟩ := quadratic_signed_frequency_coordinates hh (le_refl h.natAbs)
    have hc₀ : 0 < c := (Finset.mem_Icc.mp hc).1
    obtain ⟨hr, hbo, hbs⟩ := Finset.mem_filter.mp hb
    have hb₀ : 0 < b := (Finset.mem_Icc.mp hr).1
    refine ⟨(⟨a, ha⟩, (⟨⟨b, hb₀⟩, hbo, hbs⟩, ⟨c, hc₀⟩)), ?_⟩
    exact he.symm

theorem quadratic_signed_tsum (F : ℤ → ℂ) (hzero : F 0 = 0) :
    (∑' h : ℤ, F h) = ∑' z : QuadraticFrequencyIndex, F (quadraticFrequencyValue z) := by
  symm
  apply quadraticFrequencyValue_injective.tsum_eq
  intro h hh
  rw [quadraticFrequencyValue_range]
  intro hz
  exact hh (hz ▸ hzero)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticFirstSignedTransform
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual nonzero first frequencies in signed squarefree coordinates -/

namespace Ostmann

open scoped Classical BigOperators FourierTransform SchwartzMap

theorem quadratic_jacobi_frequency_summable (ψ : 𝓢(ℝ, ℂ)) {Y : ℝ} (hY : 0 < Y)
    (e q : ℕ) :
    Summable (fun h : ℤ => (jacobiSym ((e : ℤ) * h) q : ℂ) * ψ ((h : ℝ) * Y)) := by
  have hs := quadratic_scaled_summable ψ (inv_pos.mpr hY)
  simp only [div_inv_eq_mul] at hs
  apply Summable.of_norm_bounded hs
  intro h
  have hJ : ‖(jacobiSym ((e : ℤ) * h) q : ℂ)‖ ≤ 1 := by
    rcases jacobiSym.trichotomy ((e : ℤ) * h) q with he | he | he <;> rw [he] <;> norm_num
  rw [norm_mul]
  exact (mul_le_mul_of_nonneg_right hJ (norm_nonneg _)).trans_eq (one_mul _)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticFirstCoprimeTransform
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact second-Poisson input inside each signed first-transform term -/

namespace Ostmann

open scoped Classical BigOperators FourierTransform SchwartzMap

theorem quadratic_first_square_term {q e : ℕ} (hq : 0 < q)
    {M : ℝ} (hM : 0 < M) (ψ : 𝓢(ℝ, ℂ)) (a : ℤ) (b : ℕ) :
    (∑' c : ℕ+, (jacobiSym ((e : ℤ) * (a * (c : ℕ) ^ 2 * b)) q : ℂ) *
      𝓕 ψ (((a * (c : ℕ) ^ 2 * b : ℤ) : ℝ) * M / ((e : ℝ) * q))) =
    ((jacobiSym ((e : ℤ) * a) q : ℂ) * (jacobiSym b q : ℂ)) *
      ∑' c : ℕ+, (1 : DirichletCharacter ℂ q) (c : ZMod q) *
        𝓕 ψ ((a : ℝ) * b * (c : ℝ) ^ 2 / ((e : ℝ) * q / M)) := by
  rw [← tsum_mul_left]
  apply tsum_congr
  intro c
  have harg : (((a * (c : ℕ) ^ 2 * b : ℤ) : ℝ) * M / ((e : ℝ) * q)) =
      (a : ℝ) * b * (c : ℝ) ^ 2 / ((e : ℝ) * q / M) := by
    push_cast
    field_simp
  rw [harg]
  have hj := quadratic_frequency_character ((e : ℤ) * a) (c : ℕ) b
    hq.ne'
  have heq : (e : ℤ) * (a * (c : ℕ) ^ 2 * b) =
      ((e : ℤ) * a) * (c : ℕ) ^ 2 * b := by ring
  rw [heq, hj, quadratic_principal_nat, jacobiSym.mul_left, Int.cast_mul]
  by_cases hc : (c : ℕ).Coprime q
  · rw [ite_eq_left hc, ite_eq_left hc]
    ring
  · rw [ite_eq_right hc, ite_eq_right hc]
    ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticOddKernelCutoff
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact finite cutoff in the odd-squarefree frequency variable -/

namespace Ostmann

open scoped Classical BigOperators

theorem quadraticOddKernel_val_injective :
    Function.Injective (fun b : QuadraticOddKernel => (b.val : ℕ)) := by
  intro b c h
  exact Subtype.ext (Subtype.ext h)

theorem quadratic_odd_kernel_cutoff (K : ℕ) (F : ℕ → ℂ) :
    (∑' b : QuadraticOddKernel, if (b.val : ℕ) ≤ K then F b.val else 0) =
      ∑ b ∈ oddSquarefreeRange K, F b := by
  let G : ℕ → ℂ := fun n => if n ∈ oddSquarefreeRange K then F n else 0
  have he : (∑' b : QuadraticOddKernel, G b.val) = ∑' n : ℕ, G n := by
    apply quadraticOddKernel_val_injective.tsum_eq
    intro n hn
    have hnS : n ∈ oddSquarefreeRange K := by
      by_contra hs
      exact hn (by simp only [G, hs, ite_false, if_false])
    obtain ⟨hr, ho, hsf⟩ := Finset.mem_filter.mp hnS
    exact ⟨⟨⟨n, (Finset.mem_Icc.mp hr).1⟩, ho, hsf⟩, rfl⟩
  calc
    _ = ∑' b : QuadraticOddKernel, G b.val := by
      apply tsum_congr
      intro b
      have hm : (b.val : ℕ) ∈ oddSquarefreeRange K ↔ (b.val : ℕ) ≤ K := by
        simp only [oddSquarefreeRange, Finset.mem_filter, Finset.mem_Icc]
        exact ⟨fun h => h.1.2, fun h => ⟨⟨b.val.property, h⟩, b.property⟩⟩
      simp only [G, hm]
    _ = ∑' n : ℕ, G n := he
    _ = _ := by
      rw [tsum_eq_sum (s := oddSquarefreeRange K) (by
        intro n hn
        simp only [G, hn, ite_false, if_false])]
      apply Finset.sum_congr rfl
      intro n hn
      simp only [G, hn, ite_true, if_true]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticSignedKernelTail
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The discarded odd kernels are a genuine Schwartz frequency tail -/

namespace Ostmann

open scoped Classical BigOperators SchwartzMap

theorem quadratic_kernel_le_frequency (z : QuadraticFrequencyIndex) :
    (z.2.1.val : ℕ) ≤ (quadraticFrequencyValue z).natAbs := by
  have ha : (z.1 : ℤ) ≠ 0 := by
    have h := z.1.property
    simp only [Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with h | h | h | h <;> rw [h] <;> norm_num
  unfold quadraticFrequencyValue
  simp only [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast]
  calc
    _ ≤ (z.2.2 : ℕ) ^ 2 * (z.2.1.val : ℕ) :=
      Nat.le_mul_of_pos_left _ (pow_pos z.2.2.property 2)
    _ ≤ (z.1 : ℤ).natAbs * ((z.2.2 : ℕ) ^ 2 * (z.2.1.val : ℕ)) :=
      Nat.le_mul_of_pos_left _ (Int.natAbs_pos.mpr ha)
    _ = _ := by ring

theorem quadratic_signed_kernel_tail_bound (F : ℤ → ℂ)
    (hF : Summable (fun h => ‖F h‖)) (K : ℕ) :
    ‖∑' z : QuadraticFrequencyIndex,
      if K < (z.2.1.val : ℕ) then F (quadraticFrequencyValue z) else 0‖ ≤
      ∑' h : ℤ, if K < h.natAbs then ‖F h‖ else 0 := by
  let G : ℤ → ℝ := fun h => if K < h.natAbs then ‖F h‖ else 0
  have hG : Summable G := by
    apply Summable.of_nonneg_of_le (fun _ => by dsimp [G]; split_ifs <;> positivity) _ hF
    intro h
    dsimp [G]
    split_ifs <;> simp
  have hGi := hG.comp_injective quadraticFrequencyValue_injective
  have hp (z : QuadraticFrequencyIndex) :
      ‖if K < (z.2.1.val : ℕ) then F (quadraticFrequencyValue z) else 0‖ ≤
        G (quadraticFrequencyValue z) := by
    by_cases hz : K < (z.2.1.val : ℕ)
    · have hi := hz.trans_le (quadratic_kernel_le_frequency z)
      simp only [hz, G, hi, ite_true, if_true]
      exact le_rfl
    · simp only [hz, ite_false, if_false, norm_zero]
      dsimp [G]
      split_ifs <;> positivity
  have hpi : Summable (fun z : QuadraticFrequencyIndex =>
      ‖if K < (z.2.1.val : ℕ) then F (quadraticFrequencyValue z) else 0‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hp hGi
  apply (norm_tsum_le_tsum_norm hpi).trans
  apply (hpi.tsum_le_tsum hp hGi).trans_eq
  apply quadraticFrequencyValue_injective.tsum_eq
  intro h hh
  rw [quadraticFrequencyValue_range]
  intro hz
  apply hh
  simp only [G, hz, Int.natAbs_zero, not_lt_zero, ite_false, if_false]

theorem quadratic_schwartz_kernel_tail (ψ : 𝓢(ℝ, ℂ)) (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Y : ℝ), 0 < Y → ∀ e q K : ℕ,
      ‖∑' z : QuadraticFrequencyIndex,
        if K < (z.2.1.val : ℕ) then
          (jacobiSym ((e : ℤ) * quadraticFrequencyValue z) q : ℂ) *
            ψ ((quadraticFrequencyValue z : ℤ) * Y) else 0‖ ≤
        C / (Y ^ (A + 2) * ((K : ℝ) + 1) ^ A) := by
  obtain ⟨C, hC, hc⟩ := quadratic_schwartz_frequency_tail ψ A
  refine ⟨C, hC, ?_⟩
  intro Y hY e q K
  let F : ℤ → ℂ := fun h => (jacobiSym ((e : ℤ) * h) q : ℂ) * ψ ((h : ℝ) * Y)
  have hbase : Summable (fun h : ℤ => ‖ψ ((h : ℝ) * Y)‖) := by
    simpa only [div_inv_eq_mul] using quadratic_scaled_summable ψ (inv_pos.mpr hY)
  have hbound (h : ℤ) : ‖F h‖ ≤ ‖ψ ((h : ℝ) * Y)‖ := by
    have hJ : ‖(jacobiSym ((e : ℤ) * h) q : ℂ)‖ ≤ 1 := by
      rcases jacobiSym.trichotomy ((e : ℤ) * h) q with hh | hh | hh <;> rw [hh] <;> norm_num
    change ‖(jacobiSym ((e : ℤ) * h) q : ℂ) * ψ ((h : ℝ) * Y)‖ ≤ _
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right hJ (norm_nonneg _)).trans_eq (one_mul _)
  have hFn : Summable (fun h => ‖F h‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hbound hbase
  have htail : Summable (fun h : ℤ => if K < h.natAbs then ‖ψ ((h : ℝ) * Y)‖ else 0) := by
    apply Summable.of_nonneg_of_le (fun _ => by split_ifs <;> positivity) _ hbase
    intro h
    split_ifs <;> simp
  have hFtail : Summable (fun h : ℤ => if K < h.natAbs then ‖F h‖ else 0) := by
    apply Summable.of_nonneg_of_le (fun _ => by split_ifs <;> positivity) _ hFn
    intro h
    split_ifs <;> simp
  apply (quadratic_signed_kernel_tail_bound F hFn K).trans
  apply le_trans _ (hc Y hY K)
  apply hFtail.tsum_le_tsum _ htail
  intro h
  split_ifs
  · exact hbound h
  · rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticSignedFiniteCutoff
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact finite kernel truncation of the signed frequency expansion -/

namespace Ostmann

open scoped Classical BigOperators

theorem quadratic_signed_low_sum (F : ℤ → ℂ) (hF : Summable (fun h => ‖F h‖)) (K : ℕ) :
    (∑' z : QuadraticFrequencyIndex,
      if (z.2.1.val : ℕ) ≤ K then F (quadraticFrequencyValue z) else 0) =
    ∑ a ∈ ({1, -1, 2, -2} : Finset ℤ), ∑ b ∈ oddSquarefreeRange K,
      ∑' c : ℕ+, F (a * (c : ℕ) ^ 2 * b) := by
  have hindex := hF.comp_injective quadraticFrequencyValue_injective
  have hlow : Summable (fun z : QuadraticFrequencyIndex =>
      if (z.2.1.val : ℕ) ≤ K then F (quadraticFrequencyValue z) else 0) := by
    apply Summable.of_norm_bounded hindex
    intro z
    split_ifs <;> simp
  rw [hlow.tsum_prod]
  have ha (a : ({1, -1, 2, -2} : Finset ℤ)) :
      (∑' bc : QuadraticOddKernel × ℕ+,
        if (bc.1.val : ℕ) ≤ K then F (quadraticFrequencyValue (a, bc)) else 0) =
        ∑ b ∈ oddSquarefreeRange K, ∑' c : ℕ+, F ((a : ℤ) * (c : ℕ) ^ 2 * b) := by
    rw [(hlow.prod_factor a).tsum_prod]
    have hb (b : QuadraticOddKernel) :
        (∑' c : ℕ+, if (b.val : ℕ) ≤ K then F (quadraticFrequencyValue (a, (b, c))) else 0) =
        if (b.val : ℕ) ≤ K then (∑' c : ℕ+, F ((a : ℤ) * (c : ℕ) ^ 2 * (b.val : ℕ))) else 0 := by
      by_cases h : (b.val : ℕ) ≤ K
      · simp only [h, ite_true, if_true, quadraticFrequencyValue]
      · simp only [h, ite_false, if_false, tsum_zero]
    simp_rw [hb]
    exact quadratic_odd_kernel_cutoff K (fun b => ∑' c : ℕ+, F ((a : ℤ) * (c : ℕ) ^ 2 * b))
  simp_rw [ha]
  exact Finset.tsum_subtype ({1, -1, 2, -2} : Finset ℤ)
    (fun a : ℤ => ∑ b ∈ oddSquarefreeRange K, ∑' c : ℕ+, F (a * (c : ℕ) ^ 2 * b))

theorem quadratic_signed_finite_cutoff (F : ℤ → ℂ) (hzero : F 0 = 0)
    (hF : Summable (fun h => ‖F h‖)) (K : ℕ) :
    (∑' h : ℤ, F h) =
      (∑ a ∈ ({1, -1, 2, -2} : Finset ℤ), ∑ b ∈ oddSquarefreeRange K,
        ∑' c : ℕ+, F (a * (c : ℕ) ^ 2 * b)) +
      ∑' z : QuadraticFrequencyIndex,
        if K < (z.2.1.val : ℕ) then F (quadraticFrequencyValue z) else 0 := by
  have hindex := hF.comp_injective quadraticFrequencyValue_injective
  have hlow : Summable (fun z : QuadraticFrequencyIndex =>
      if (z.2.1.val : ℕ) ≤ K then F (quadraticFrequencyValue z) else 0) := by
    apply Summable.of_norm_bounded hindex
    intro z
    split_ifs <;> simp
  have hhigh : Summable (fun z : QuadraticFrequencyIndex =>
      if K < (z.2.1.val : ℕ) then F (quadraticFrequencyValue z) else 0) := by
    apply Summable.of_norm_bounded hindex
    intro z
    split_ifs <;> simp
  rw [quadratic_signed_tsum F hzero, ← quadratic_signed_low_sum F hF K,
    ← hlow.tsum_add hhigh]
  apply tsum_congr
  intro z
  by_cases h : (z.2.1.val : ℕ) ≤ K
  · simp only [h, not_lt.mpr h, ite_true, if_true, ite_false, if_false, add_zero]
  · simp only [h, lt_of_not_ge h, ite_false, if_false, ite_true, if_true, zero_add]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticFirstFrequencyCutoff
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The finite second-Poisson family and its proved first-transform tail -/

namespace Ostmann

open scoped Classical BigOperators SchwartzMap FourierTransform

theorem quadratic_first_frequency_cutoff (ψ : 𝓢(ℝ, ℂ)) (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (M : ℝ), 0 < M → ∀ e q K : ℕ, 0 < e → 1 < q →
      ‖(∑' h : ℤ, (jacobiSym ((e : ℤ) * h) q : ℂ) *
        𝓕 ψ ((h : ℝ) * M / ((e : ℝ) * q))) -
          quadraticFirstFiniteFrequency ψ M e q K‖ ≤
        C / ((M / ((e : ℝ) * q)) ^ (A + 2) * ((K : ℝ) + 1) ^ A) := by
  obtain ⟨C, hC, hc⟩ := quadratic_schwartz_kernel_tail (𝓕 ψ) A
  refine ⟨C, hC, ?_⟩
  intro M hM e q K he hq
  have heR : (0 : ℝ) < e := by exact_mod_cast he
  have hqR : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  let Y := M / ((e : ℝ) * q)
  have hY : 0 < Y := div_pos hM (mul_pos heR hqR)
  let F : ℤ → ℂ := fun h => (jacobiSym ((e : ℤ) * h) q : ℂ) * 𝓕 ψ ((h : ℝ) * Y)
  have hF : Summable (fun h => ‖F h‖) :=
    (quadratic_jacobi_frequency_summable (𝓕 ψ) hY e q).norm
  have hzero : F 0 = 0 := by
    simp only [F, mul_zero, jacobiSym.zero_left hq, Int.cast_zero, zero_mul]
  have hfinite : (∑ a ∈ ({1, -1, 2, -2} : Finset ℤ), ∑ b ∈ oddSquarefreeRange K,
      ∑' c : ℕ+, F (a * (c : ℕ) ^ 2 * b)) = quadraticFirstFiniteFrequency ψ M e q K := by
    unfold quadraticFirstFiniteFrequency
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    dsimp only [F, Y]
    simp only [← mul_div_assoc]
    exact quadratic_first_square_term (by omega) hM ψ a b
  have hs := quadratic_signed_finite_cutoff F hzero hF K
  rw [hfinite] at hs
  simp only [mul_div_assoc]
  change ‖(∑' h : ℤ, F h) - quadraticFirstFiniteFrequency ψ M e q K‖ ≤ _
  rw [hs, add_sub_cancel_left]
  exact hc Y hY e q K

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticFirstTailNormalization
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The first-frequency tail after the original Gauss normalization -/

namespace Ostmann

open scoped Classical BigOperators SchwartzMap FourierTransform

private theorem tail_denominator {Y J C : ℝ} (hY : 0 < Y) (hJ : 1 ≤ J)
    (hC : 0 ≤ C) (K A : ℕ) (hcut : J ≤ Y * ((K : ℝ) + 1)) :
    C / (Y ^ (A + 2) * ((K : ℝ) + 1) ^ A) ≤ C / (Y ^ 2 * J ^ A) := by
  apply div_le_div_of_nonneg_left hC (by positivity)
  have hp := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ J) hcut A
  have he : Y ^ (A + 2) * ((K : ℝ) + 1) ^ A =
      Y ^ 2 * (Y * ((K : ℝ) + 1)) ^ A := by
    rw [pow_add, mul_pow]
    ring
  rw [he]
  exact mul_le_mul_of_nonneg_left hp (by positivity)

theorem quadratic_first_tail_normalized (ψ : 𝓢(ℝ, ℂ)) (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ M J : ℝ, 0 < M → 1 ≤ J →
      ∀ e q K : ℕ, 0 < e → 1 < q →
      J ≤ (M / ((e : ℝ) * q)) * ((K : ℝ) + 1) →
      ‖(((M / ((e : ℝ) * Real.sqrt q) : ℝ) : ℂ) *
        ((∑' h : ℤ, (jacobiSym ((e : ℤ) * h) q : ℂ) *
          𝓕 ψ ((h : ℝ) * M / ((e : ℝ) * q))) -
          quadraticFirstFiniteFrequency ψ M e q K))‖ ≤
        C * ((e : ℝ) * q * Real.sqrt q / M) / J ^ A := by
  obtain ⟨C, hC, hc⟩ := quadratic_first_frequency_cutoff ψ A
  refine ⟨C, hC, ?_⟩
  intro M J hM hJ e q K he hq hcut
  have heR : (0 : ℝ) < e := by exact_mod_cast he
  have hqR : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hs : 0 < Real.sqrt (q : ℝ) := Real.sqrt_pos.mpr hqR
  have hS : 0 < M / ((e : ℝ) * Real.sqrt q) := by positivity
  have hY : 0 < M / ((e : ℝ) * q) := by positivity
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hS]
  calc
    _ ≤ (M / ((e : ℝ) * Real.sqrt q)) *
        (C / ((M / ((e : ℝ) * q)) ^ (A + 2) * ((K : ℝ) + 1) ^ A)) :=
      mul_le_mul_of_nonneg_left (hc M hM e q K he hq) hS.le
    _ ≤ (M / ((e : ℝ) * Real.sqrt q)) *
        (C / ((M / ((e : ℝ) * q)) ^ 2 * J ^ A)) :=
      mul_le_mul_of_nonneg_left (tail_denominator hY hJ hC K A hcut) hS.le
    _ = C * ((e : ℝ) * q * ((q : ℝ) / Real.sqrt q) / M) / J ^ A := by
      field_simp
    _ = _ := by
      have hroot : (q : ℝ) / Real.sqrt q = Real.sqrt q := by
        apply (div_eq_iff hs.ne').mpr
        nlinarith only [Real.sq_sqrt hqR.le]
      rw [hroot]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticPairTailGeometry
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform cutoff geometry for the actual common-divisor pair family -/

namespace Ostmann

open scoped Classical BigOperators

theorem quadratic_pair_product_bound {N D : ℕ} {z : ℕ × ℕ}
    (hz : z ∈ quadraticGcdPairs N D) :
    0 < D ∧ D ≤ N ∧ D ^ 2 * quadraticPairKernel z.1 z.2 ≤ N ^ 2 := by
  obtain ⟨hz, hg⟩ := Finset.mem_filter.mp hz
  obtain ⟨hs, ht⟩ := Finset.mem_product.mp hz
  have hsR := Finset.mem_Icc.mp (Finset.mem_filter.mp hs).1
  have htR := Finset.mem_Icc.mp (Finset.mem_filter.mp ht).1
  refine ⟨hg ▸ Nat.gcd_pos_of_pos_left _ hsR.1,
    hg ▸ (Nat.gcd_le_left _ hsR.1).trans hsR.2, ?_⟩
  rw [← hg, quadraticPairKernel_factor, pow_two]
  exact Nat.mul_le_mul hsR.2 htR.2

theorem quadratic_pair_tail_scales {N D e : ℕ} {z : ℕ × ℕ}
    (hz : z ∈ quadraticGcdPairs N D) (he : e ∈ (2 * D).divisors) :
    0 < e ∧ e * quadraticPairKernel z.1 z.2 ≤ 2 * N ^ 2 ∧
      quadraticPairKernel z.1 z.2 ≤ N ^ 2 := by
  obtain ⟨hD, _, hp⟩ := quadratic_pair_product_bound hz
  have hepos := Nat.pos_of_mem_divisors he
  have heD := Nat.le_of_dvd (show 0 < 2 * D by omega) (Nat.dvd_of_mem_divisors he)
  have hDsq : D ≤ D ^ 2 := by nlinarith
  have hq : quadraticPairKernel z.1 z.2 ≤ D ^ 2 * quadraticPairKernel z.1 z.2 :=
    Nat.le_mul_of_pos_left _ (pow_pos hD 2)
  refine ⟨hepos, ?_, hq.trans hp⟩
  calc
    _ ≤ (2 * D) * quadraticPairKernel z.1 z.2 := Nat.mul_le_mul_right _ heD
    _ ≤ 2 * (D ^ 2 * quadraticPairKernel z.1 z.2) := by nlinarith [Nat.mul_le_mul_right (quadraticPairKernel z.1 z.2) hDsq]
    _ ≤ 2 * N ^ 2 := Nat.mul_le_mul_left 2 hp

theorem quadratic_pair_normalized_tail_scale {N D e : ℕ} {z : ℕ × ℕ}
    (hz : z ∈ quadraticGcdPairs N D) (he : e ∈ (2 * D).divisors) :
    (e : ℝ) * quadraticPairKernel z.1 z.2 * Real.sqrt (quadraticPairKernel z.1 z.2) ≤
      2 * (N : ℝ) ^ 3 := by
  obtain ⟨_, heq, hq⟩ := quadratic_pair_tail_scales hz he
  have heqR : (e : ℝ) * quadraticPairKernel z.1 z.2 ≤ 2 * (N : ℝ) ^ 2 := by exact_mod_cast heq
  have hqR : (quadraticPairKernel z.1 z.2 : ℝ) ≤ (N : ℝ) ^ 2 := by exact_mod_cast hq
  have hs : Real.sqrt (quadraticPairKernel z.1 z.2) ≤ (N : ℝ) := by
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg (quadraticPairKernel z.1 z.2)),
      Real.sqrt_nonneg (quadraticPairKernel z.1 z.2), Nat.cast_nonneg (α := ℝ) N]
  calc
    _ ≤ (2 * (N : ℝ) ^ 2) * N := mul_le_mul heqR hs (Real.sqrt_nonneg _) (by positivity)
    _ = _ := by ring

theorem quadratic_pair_first_cutoff {N D e K : ℕ} {z : ℕ × ℕ}
    (hz : z ∈ quadraticGcdPairs N D) (he : e ∈ (2 * D).divisors)
    {M J : ℝ} (hJ : 0 ≤ J)
    (hcut : 2 * (N : ℝ) ^ 2 * J ≤ M * ((K : ℝ) + 1)) :
    J ≤ (M / ((e : ℝ) * quadraticPairKernel z.1 z.2)) * ((K : ℝ) + 1) := by
  obtain ⟨hepos, heq, _⟩ := quadratic_pair_tail_scales hz he
  have hz' := (Finset.mem_filter.mp hz).1
  obtain ⟨hs, ht⟩ := Finset.mem_product.mp hz'
  have hqpos := Nat.pos_of_ne_zero (quadraticPairKernel_squarefree
    (Finset.mem_filter.mp hs).2.2 (Finset.mem_filter.mp ht).2.2).ne_zero
  have hden : 0 < (e : ℝ) * quadraticPairKernel z.1 z.2 := by positivity
  rw [div_mul_eq_mul_div, le_div_iff₀ hden]
  apply le_trans _ hcut
  have hh : (e : ℝ) * quadraticPairKernel z.1 z.2 ≤ 2 * (N : ℝ) ^ 2 := by exact_mod_cast heq
  nlinarith [mul_le_mul_of_nonneg_left hh hJ]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticFirstKernelError
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The whole first-transform tail, with the actual pair and divisor weights -/

namespace Ostmann

open scoped Classical BigOperators FourierTransform

theorem quadratic_first_kernel_error (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ M N D K : ℕ, 0 < M → ∀ J : ℝ, 1 ≤ J →
      2 * (N : ℝ) ^ 2 * J ≤ (M : ℝ) * ((K : ℝ) + 1) →
      ∀ z ∈ quadraticGcdPairs N D, z.1 ≠ z.2 →
      ‖quadraticFirstKernelTransform M D (quadraticPairKernel z.1 z.2) -
        quadraticFirstKernelFinite M D (quadraticPairKernel z.1 z.2) K‖ ≤
      4 * C * (N : ℝ) ^ 4 / ((M : ℝ) * J ^ A) := by
  obtain ⟨C, hC, hc⟩ := quadratic_first_tail_normalized quadraticSieveWeight A
  refine ⟨C, hC, ?_⟩
  intro M N D K hM J hJ hcut z hz hne
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  obtain ⟨hD, hDN, _⟩ := quadratic_pair_product_bound hz
  obtain ⟨hz', _⟩ := Finset.mem_filter.mp hz
  obtain ⟨hs, ht⟩ := Finset.mem_product.mp hz'
  have hsf := quadraticPairKernel_squarefree (Finset.mem_filter.mp hs).2.2
    (Finset.mem_filter.mp ht).2.2
  have ho := quadraticPairKernel_odd (Finset.mem_filter.mp hs).2.1 (Finset.mem_filter.mp ht).2.1
  have hq : 1 < quadraticPairKernel z.1 z.2 := by
    have hn := mt (quadraticPairKernel_eq_one_iff (Finset.mem_filter.mp hs).2.2
      (Finset.mem_filter.mp ht).2.2).mp hne
    have hp := Nat.pos_of_ne_zero hsf.ne_zero
    omega
  let q := quadraticPairKernel z.1 z.2
  let R (e : ℕ) : ℂ := (((M : ℝ) / ((e : ℝ) * Real.sqrt q) : ℝ) : ℂ) *
    ((∑' h : ℤ, (jacobiSym ((e : ℤ) * h) q : ℂ) *
      𝓕 quadraticSieveWeight ((h : ℝ) * M / ((e : ℝ) * q))) -
        quadraticFirstFiniteFrequency quadraticSieveWeight M e q K)
  have hid : quadraticFirstKernelTransform M D q - quadraticFirstKernelFinite M D q K =
      quadraticGaussMultiplier q * ∑ e ∈ (2 * D).divisors, (ArithmeticFunction.moebius e : ℂ) * R e := by
    unfold quadraticFirstKernelTransform quadraticFirstKernelFinite
    rw [← mul_sub, ← Finset.sum_sub_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro e _
    dsimp [R]
    ring
  have hT : 0 ≤ C * (2 * (N : ℝ) ^ 3 / M) / J ^ A := by positivity
  have hp (e : ℕ) (he : e ∈ (2 * D).divisors) :
      ‖(ArithmeticFunction.moebius e : ℂ) * R e‖ ≤ C * (2 * (N : ℝ) ^ 3 / M) / J ^ A := by
    have hepos := Nat.pos_of_mem_divisors he
    have hcc := quadratic_pair_first_cutoff hz he (by positivity : 0 ≤ J) hcut
    have hh := hc M J hMR hJ e q K hepos hq hcc
    have hn : ‖(ArithmeticFunction.moebius e : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_intCast]
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := e)
    rw [norm_mul]
    apply (mul_le_mul hn hh (norm_nonneg _) zero_le_one).trans
    simp only [one_mul]
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_left _ hC
    apply div_le_div_of_nonneg_right _ hMR.le
    exact quadratic_pair_normalized_tail_scale hz he
  change ‖quadraticFirstKernelTransform M D q - quadraticFirstKernelFinite M D q K‖ ≤ _
  rw [hid, norm_mul, quadraticGaussMultiplier_norm hsf ho, one_mul]
  calc
    _ ≤ ∑ e ∈ (2 * D).divisors, C * (2 * (N : ℝ) ^ 3 / M) / J ^ A :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum hp)
    _ = (((2 * D).divisors.card : ℕ) : ℝ) * (C * (2 * (N : ℝ) ^ 3 / M) / J ^ A) := by simp
    _ ≤ (2 * N : ℝ) * (C * (2 * (N : ℝ) ^ 3 / M) / J ^ A) := by
      apply mul_le_mul_of_nonneg_right _ hT
      exact_mod_cast (Nat.card_divisors_le_self (2 * D)).trans (Nat.mul_le_mul_left 2 hDN)
    _ = _ := by ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticSecondDyadic
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The second Poisson estimate with the literal dyadic square argument -/

namespace Ostmann

open scoped Classical BigOperators SchwartzMap FourierTransform

theorem quadratic_second_dyadic (ρ : 𝓢(ℝ, ℂ)) (a : ℝ)
    (ha : 1 ≤ |a|) (hρ : ∀ t < 1 / 2, ρ t = 0) (A : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ M B N J : ℝ,
      0 < M → 0 < B → 0 < N → 1 ≤ J →
      ∀ e q b : ℕ, 0 < e → q ≠ 1 → B ≤ b → (b : ℝ) ≤ 2 * B →
      N ^ 2 ≤ q → (q : ℝ) ≤ 4 * N ^ 2 →
      ‖(∑' c : ℕ+, (1 : DirichletCharacter ℂ q) (c : ZMod q) *
        𝓕 ρ (a * b * (c : ℝ) ^ 2 / ((e : ℝ) * q / M))) -
          quadraticSecondDyadicCore ρ a ha M B N J e q b‖ ≤
        C * quadraticSecondScale M e q b / J ^ A := by
  obtain ⟨C, hC, hc⟩ := quadratic_second_poisson ρ a ha hρ A
  refine ⟨C, hC, ?_⟩
  intro M B N J hM hB hN hJ e q b he hq1 hb hb' hq hq'
  have hbR : 0 < (b : ℝ) := hB.trans_le hb
  have hqR : 0 < (q : ℝ) := (sq_pos_of_pos hN).trans_le hq
  have hb₀ : 0 < b := by exact_mod_cast hbR
  have hq₀ : 0 < q := by exact_mod_cast hqR
  let : NeZero q := ⟨hq₀.ne'⟩
  let X₀ := Real.sqrt ((e : ℝ) * N ^ 2 / (M * B))
  have hX₀ : 0 < X₀ := Real.sqrt_pos.mpr (by positivity)
  have hX := quadraticSecondScale_pos hM he hq₀ hb₀
  obtain ⟨hlo, hhi⟩ := quadraticSecondScale_dyadic hM hB hN he hb hb' hq hq'
  obtain ⟨hU, hV, hUX, hXV, hL⟩ := quadratic_second_cutoffs hX₀ hJ hlo hhi
  have hh := hc q hq1 (quadraticSecondScale M e q b)
    (quadraticSecondLower X₀ J) (quadraticSecondUpper X₀ J) J
    hX hU hV hJ hUX hXV (quadraticSecondWindow J) hL
  simpa only [quadraticSecondScale_argument hM he hq₀ hb₀,
    quadraticSecondDyadicCore, X₀] using hh

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticSecondMain
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Identifying the first Poisson main term after the square-factor transform -/

namespace Ostmann

open MeasureTheory Set
open scoped Classical BigOperators SchwartzMap

theorem quadratic_second_main_normalizer {M : ℝ} {e q b : ℕ}
    (hM : 0 < M) (he : 0 < e) (hq : 0 < q) (hb : 0 < b) :
    M / ((e : ℝ) * Real.sqrt q) * quadraticSecondScale M e q b =
      Real.sqrt M / (Real.sqrt e * Real.sqrt b) := by
  have heR : 0 < (e : ℝ) := by exact_mod_cast he
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have hbR : 0 < (b : ℝ) := by exact_mod_cast hb
  have hsM := Real.sq_sqrt hM.le
  have hse := Real.sq_sqrt heR.le
  have hsM₀ := (Real.sqrt_pos.mpr hM).ne'
  have hse₀ := (Real.sqrt_pos.mpr heR).ne'
  have hsq₀ := (Real.sqrt_pos.mpr hqR).ne'
  have hsb₀ := (Real.sqrt_pos.mpr hbR).ne'
  unfold quadraticSecondScale
  rw [Real.sqrt_div (by positivity), Real.sqrt_mul heR.le, Real.sqrt_mul hM.le]
  field_simp
  ring_nf
  rw [hsM, hse]
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticSecondError
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The second-transform error after the original Gauss normalization -/

namespace Ostmann

open scoped Classical BigOperators SchwartzMap FourierTransform

theorem quadratic_second_error_normalized (ρ : 𝓢(ℝ, ℂ)) (a : ℝ)
    (ha : 1 ≤ |a|) (hρ : ∀ t < 1 / 2, ρ t = 0) (A : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ M B N J : ℝ,
      0 < M → 0 < B → 0 < N → 1 ≤ J →
      ∀ e q b : ℕ, 0 < e → q ≠ 1 → B ≤ b → (b : ℝ) ≤ 2 * B →
      N ^ 2 ≤ q → (q : ℝ) ≤ 4 * N ^ 2 →
      ‖((M / ((e : ℝ) * Real.sqrt q) : ℝ) : ℂ) *
        quadraticSecondDyadicError ρ a ha M B N J e q b‖ ≤
          C * Real.sqrt M / (Real.sqrt e * Real.sqrt B) / J ^ A := by
  obtain ⟨C, hC, hc⟩ := quadratic_second_dyadic ρ a ha hρ A
  refine ⟨C, hC, ?_⟩
  intro M B N J hM hB hN hJ e q b he hq1 hb hb' hq hq'
  have hqR : 0 < (q : ℝ) := (sq_pos_of_pos hN).trans_le hq
  have hq₀ : 0 < q := by exact_mod_cast hqR
  have hb₀ : 0 < b := by exact_mod_cast (hB.trans_le hb)
  have heR : 0 < (e : ℝ) := by exact_mod_cast he
  have hJ₀ : 0 < J := lt_of_lt_of_le zero_lt_one hJ
  have hm : 0 < M / ((e : ℝ) * Real.sqrt q) := by positivity
  have hh := hc M B N J hM hB hN hJ e q b he hq1 hb hb' hq hq'
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hm]
  calc
    _ ≤ (M / ((e : ℝ) * Real.sqrt q)) *
        (C * quadraticSecondScale M e q b / J ^ A) :=
      mul_le_mul_of_nonneg_left hh hm.le
    _ = C * (M / ((e : ℝ) * Real.sqrt q) * quadraticSecondScale M e q b) / J ^ A := by ring
    _ = C * Real.sqrt M / (Real.sqrt e * Real.sqrt b) / J ^ A := by
      rw [quadratic_second_main_normalizer hM he hq₀ hb₀]
      ring
    _ ≤ _ := by
      gcongr

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticSecondSignedCore
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The full signed second Poisson core, at the original first-transform weights -/

namespace Ostmann

open scoped Classical BigOperators SchwartzMap FourierTransform

theorem quadratic_second_signed_uniform (ρ : 𝓢(ℝ, ℂ))
    (hρ : ∀ t < 1 / 2, ρ t = 0) (A : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ a : quadraticPoissonSigns, ∀ M H J : ℝ,
      0 < M → 0 < H → 1 ≤ J → ∀ e q b : ℕ, 0 < e → q ≠ 1 → 0 < b →
      H ^ 2 ≤ q → (q : ℝ) ≤ 4 * H ^ 2 →
      ‖((M / ((e : ℝ) * Real.sqrt q) : ℝ) : ℂ) *
        quadraticSecondDyadicError ρ (a : ℤ) (quadraticPoissonSigns_abs a.property)
          M b H J e q b‖ ≤ C * Real.sqrt M / J ^ A := by
  have hs (a : quadraticPoissonSigns) :=
    quadratic_second_error_normalized ρ (a : ℤ) (quadraticPoissonSigns_abs a.property) hρ A
  choose c hc hbound using hs
  let C := (∑ a : quadraticPoissonSigns, c a) + 1
  have hC : 0 < C := by
    dsimp [C]
    exact add_pos_of_nonneg_of_pos (Finset.sum_nonneg (fun a _ => (hc a).le)) zero_lt_one
  refine ⟨C, hC, ?_⟩
  intro a M H J hM hH hJ e q b he hq hb hqlo hqhi
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have he₁ : (1 : ℝ) ≤ e := by exact_mod_cast he
  have hb₁ : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hca : c a ≤ C := by
    have hh := Finset.single_le_sum (fun i _ => (hc i).le) (Finset.mem_univ a)
    change c a ≤ (∑ a : quadraticPoissonSigns, c a) + 1
    linarith
  have hd : 1 ≤ Real.sqrt e * Real.sqrt b :=
    one_le_mul_of_one_le_of_one_le (Real.one_le_sqrt.mpr he₁) (Real.one_le_sqrt.mpr hb₁)
  apply (hbound a M b H J hM hbR hH hJ e q b he hq le_rfl (by linarith) hqlo hqhi).trans
  calc
    _ = (c a * (Real.sqrt M / (Real.sqrt e * Real.sqrt b))) / J ^ A := by ring
    _ ≤ c a * Real.sqrt M / J ^ A := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left (div_le_self (Real.sqrt_nonneg _) hd) (hc a).le
    _ ≤ _ := by gcongr

theorem quadratic_signed_second_error (ρ : 𝓢(ℝ, ℂ))
    (hρ : ∀ t < 1 / 2, ρ t = 0) (A : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ M H J : ℝ, 0 < M → 0 < H → 1 ≤ J →
      ∀ e q K : ℕ, 0 < e → q ≠ 1 → H ^ 2 ≤ q → (q : ℝ) ≤ 4 * H ^ 2 →
      ‖((M / ((e : ℝ) * Real.sqrt q) : ℝ) : ℂ) *
        (quadraticFirstFiniteFrequency ρ M e q K - quadraticSignedSecondCore ρ M H J e q K)‖ ≤
          C * Real.sqrt M * K / J ^ A := by
  obtain ⟨C, hC, hc⟩ := quadratic_second_signed_uniform ρ hρ A
  refine ⟨4 * C, by positivity, ?_⟩
  intro M H J hM hH hJ e q K he hq hqlo hqhi
  have hf : quadraticFirstFiniteFrequency ρ M e q K =
      ∑ a : quadraticPoissonSigns, ∑ b ∈ oddSquarefreeRange K,
        ((jacobiSym ((e : ℤ) * a) q : ℂ) * (jacobiSym b q : ℂ)) *
          ∑' c : ℕ+, (1 : DirichletCharacter ℂ q) (c : ZMod q) *
            𝓕 ρ ((a : ℤ) * b * (c : ℝ) ^ 2 / ((e : ℝ) * q / M)) := by
    exact (Finset.sum_coe_sort quadraticPoissonSigns _).symm
  have hid : ((M / ((e : ℝ) * Real.sqrt q) : ℝ) : ℂ) *
      (quadraticFirstFiniteFrequency ρ M e q K - quadraticSignedSecondCore ρ M H J e q K) =
      ∑ a : quadraticPoissonSigns, ∑ b ∈ oddSquarefreeRange K,
        ((jacobiSym ((e : ℤ) * a) q : ℂ) * (jacobiSym b q : ℂ)) *
          (((M / ((e : ℝ) * Real.sqrt q) : ℝ) : ℂ) *
            quadraticSecondDyadicError ρ (a : ℤ) (quadraticPoissonSigns_abs a.property)
              M b H J e q b) := by
    rw [hf]
    unfold quadraticSignedSecondCore
    simp only [← Finset.sum_sub_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b _
    unfold quadraticSecondDyadicError
    ring
  rw [hid]
  have hp (a : quadraticPoissonSigns) (b : ℕ) (hb : b ∈ oddSquarefreeRange K) :
      ‖((jacobiSym ((e : ℤ) * a) q : ℂ) * (jacobiSym b q : ℂ)) *
          (((M / ((e : ℝ) * Real.sqrt q) : ℝ) : ℂ) *
            quadraticSecondDyadicError ρ (a : ℤ) (quadraticPoissonSigns_abs a.property)
              M b H J e q b)‖ ≤ C * Real.sqrt M / J ^ A := by
    have hJac (n : ℤ) : ‖(jacobiSym n q : ℂ)‖ ≤ 1 := by
      rcases jacobiSym.trichotomy n q with h | h | h <;> rw [h] <;> norm_num
    have hj : ‖(jacobiSym ((e : ℤ) * a) q : ℂ) * (jacobiSym b q : ℂ)‖ ≤ 1 := by
      rw [norm_mul]
      exact (mul_le_mul (hJac _) (hJac _) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
    rw [norm_mul]
    exact (mul_le_mul hj (hc a M H J hM hH hJ e q b he hq
      (Finset.mem_Icc.mp (Finset.mem_filter.mp hb).1).1 hqlo hqhi)
        (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
  calc
    _ ≤ ∑ a : quadraticPoissonSigns, ∑ b ∈ oddSquarefreeRange K, C * Real.sqrt M / J ^ A := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro a _
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum (hp a))
    _ = 4 * ((oddSquarefreeRange K).card : ℝ) * (C * Real.sqrt M / J ^ A) := by
      norm_num [quadraticPoissonSigns]
      ring
    _ ≤ 4 * (K : ℝ) * (C * Real.sqrt M / J ^ A) := by
      gcongr
      exact_mod_cast oddSquarefreeRange_card_le K
    _ = _ := by ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticFirstSecondKernel
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original finite first transform after the complete second Poisson step -/

namespace Ostmann

open scoped Classical BigOperators SchwartzMap

theorem quadratic_first_second_kernel_error (A : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ M D q K : ℕ, 0 < M → Squarefree q → Odd q → q ≠ 1 →
      ∀ H J : ℝ, 0 < H → 1 ≤ J → H ^ 2 ≤ q → (q : ℝ) ≤ 4 * H ^ 2 →
      ‖quadraticFirstKernelFinite M D q K - quadraticFirstSecondKernel M D q K H J‖ ≤
        C * Real.sqrt M * D * K / J ^ A := by
  have hw : ∀ t < 1 / 2, quadraticSieveWeight t = 0 :=
    fun t ht => quadraticSieveWeight_eq_zero (Or.inl ht.le)
  obtain ⟨C, hC, hc⟩ := quadratic_signed_second_error quadraticSieveWeight hw A
  refine ⟨2 * C, by positivity, ?_⟩
  intro M D q K hM hsf ho hq H J hH hJ hlo hhi
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hid : quadraticFirstKernelFinite M D q K - quadraticFirstSecondKernel M D q K H J =
      quadraticGaussMultiplier q * ∑ e ∈ (2 * D).divisors,
        (ArithmeticFunction.moebius e : ℂ) *
          ((((M : ℝ) / ((e : ℝ) * Real.sqrt q) : ℝ) : ℂ) *
            (quadraticFirstFiniteFrequency quadraticSieveWeight M e q K -
              quadraticSignedSecondCore quadraticSieveWeight M H J e q K)) := by
    unfold quadraticFirstKernelFinite quadraticFirstSecondKernel
    rw [← mul_sub, ← Finset.sum_sub_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro e _
    ring
  rw [hid, norm_mul, quadraticGaussMultiplier_norm hsf ho, one_mul]
  have hp (e : ℕ) (he : e ∈ (2 * D).divisors) :
      ‖(ArithmeticFunction.moebius e : ℂ) *
          ((((M : ℝ) / ((e : ℝ) * Real.sqrt q) : ℝ) : ℂ) *
            (quadraticFirstFiniteFrequency quadraticSieveWeight M e q K -
              quadraticSignedSecondCore quadraticSieveWeight M H J e q K))‖ ≤
        C * Real.sqrt M * K / J ^ A := by
    have hμ : ‖(ArithmeticFunction.moebius e : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_intCast]
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := e)
    rw [norm_mul]
    exact (mul_le_mul hμ (hc M H J hMR hH hJ e q K
      (Nat.pos_of_mem_divisors he) hq hlo hhi) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
  calc
    _ ≤ ∑ e ∈ (2 * D).divisors, C * Real.sqrt M * K / J ^ A :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum hp)
    _ = (((2 * D).divisors.card : ℕ) : ℝ) * (C * Real.sqrt M * K / J ^ A) := by simp
    _ ≤ (2 * D : ℝ) * (C * Real.sqrt M * K / J ^ A) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast Nat.card_divisors_le_self (2 * D)
    _ = _ := by ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticFirstSecondMain
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The second Poisson core has exactly the original main term and corrections -/

namespace Ostmann

open MeasureTheory Set
open scoped Classical BigOperators SchwartzMap FourierTransform

theorem quadratic_second_core_split (q : ℕ) (ρ : 𝓢(ℝ, ℂ))
    (a : ℝ) (ha : 1 ≤ |a|) (X U V : ℝ) (L : ℕ) :
    quadraticSecondPoissonCore q ρ a ha X U V L =
      ((X : ℂ) * q.totient / q) *
        ((quadraticFresnelPhase a / (Real.sqrt |a| : ℂ)) *
          ∫ x in Ioi (0 : ℝ), ρ (x ^ 2)) / 2 +
      quadraticSecondCorrection q ρ a ha X U V L := by
  unfold quadraticSecondPoissonCore quadraticSecondCorrection
  ring

theorem quadratic_second_dyadic_core_split (ρ : 𝓢(ℝ, ℂ))
    (a : ℝ) (ha : 1 ≤ |a|) (M H J : ℝ) (e q b : ℕ) :
    quadraticSecondDyadicCore ρ a ha M b H J e q b =
      ((quadraticSecondScale M e q b : ℂ) * q.totient / q) *
        ((quadraticFresnelPhase a / (Real.sqrt |a| : ℂ)) *
          ∫ x in Ioi (0 : ℝ), ρ (x ^ 2)) / 2 +
      quadraticSecondDyadicCorrection ρ a ha M H J e q b :=
  quadratic_second_core_split q ρ a ha _ _ _ _

theorem quadratic_first_second_kernel_split (M D q K : ℕ) (H J : ℝ) :
    quadraticFirstSecondKernel M D q K H J =
      quadraticFirstSecondMainKernel M D q K + quadraticFirstSecondCorrections M D q K H J := by
  unfold quadraticFirstSecondKernel quadraticFirstSecondMainKernel quadraticFirstSecondCorrections
    quadraticSignedSecondCore
  simp_rw [quadratic_second_dyadic_core_split, mul_add, Finset.sum_add_distrib]
  simp only [mul_add, Finset.sum_add_distrib]

theorem quadratic_first_second_main_kernel (M D q K : ℕ) :
    quadraticFirstSecondMainKernel M D q K =
      ((∫ x in Ioi (0 : ℝ), quadraticSieveWeight (x ^ 2)) / 2) *
      ((q.totient : ℂ) / q) * ∑ b ∈ oddSquarefreeRange K,
        (jacobiSym b q : ℂ) * quadraticDualMainCoefficient M D q b := by
  have hs (f : ℤ → ℂ) : (∑ a : quadraticPoissonSigns, f a) =
      ∑ a ∈ ({1, -1, 2, -2} : Finset ℤ), f a := Finset.sum_coe_sort quadraticPoissonSigns f
  have hr (F : ℕ → quadraticPoissonSigns → ℕ → ℂ) :
      (∑ e ∈ (2 * D).divisors, ∑ a : quadraticPoissonSigns,
        ∑ b ∈ oddSquarefreeRange K, F e a b) =
      ∑ b ∈ oddSquarefreeRange K, ∑ e ∈ (2 * D).divisors,
        ∑ a : quadraticPoissonSigns, F e a b := by
    calc
      _ = ∑ e ∈ (2 * D).divisors, ∑ b ∈ oddSquarefreeRange K,
          ∑ a : quadraticPoissonSigns, F e a b := by
        apply Finset.sum_congr rfl
        intro e _
        exact Finset.sum_comm
      _ = _ := Finset.sum_comm
  unfold quadraticFirstSecondMainKernel quadraticDualMainCoefficient
  simp_rw [← hs]
  simp only [Finset.mul_sum]
  rw [hr]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro e _
  apply Finset.sum_congr rfl
  intro a _
  push_cast
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticMomentMainComparison
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual two transformed main terms, summed over the original pairs -/

namespace Ostmann

open MeasureTheory Set
open scoped Classical BigOperators ComplexConjugate

theorem quadratic_small_pair_core_main (M D q K : ℕ) (J : ℝ) :
    quadraticSmallPairCore M K D q J = quadraticSmallPairMain M D q K +
      ∑ b ∈ (oddSquarefreeRange K).filter (D.Coprime ·),
        (jacobiSym b q : ℂ) * quadraticSmallPairCorrection M J (2 * (q * D)) b := by
  unfold quadraticSmallPairCore quadraticSmallPairMain
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b _
  rw [quadratic_small_pair_core]
  ring

theorem quadratic_pair_main_difference_sum (M N D K : ℕ) (v : ℕ → ℂ) :
    (∑ z ∈ quadraticGcdPairs N D,
      v z.1 * conj (v z.2) * quadraticPairMainDifference M D (quadraticPairKernel z.1 z.2) K) =
      quadraticTransformedFirstMain M N D K quadraticSieveWeight v -
        quadraticSmallTransformedMain M N D K quadraticSieveWeight v := by
  unfold quadraticPairMainDifference
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  congr 1
  · simp_rw [quadratic_first_second_main_kernel]
    unfold quadraticTransformedFirstMain
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z _
    ring

theorem quadraticGcdPairs_empty_of_not_squarefree (N D : ℕ) (hD : ¬ Squarefree D) :
    quadraticGcdPairs N D = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro z hz
  obtain ⟨hz, hg⟩ := Finset.mem_filter.mp hz
  have hs := (Finset.mem_product.mp hz).1
  have hsf := (Finset.mem_filter.mp hs).2.2
  apply hD
  rw [← hg]
  exact hsf.squarefree_of_dvd (Nat.gcd_dvd_left z.1 z.2)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticRoughGcdDescent
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Large common divisors descend to genuinely shorter rough moments -/

namespace Ostmann

open scoped Classical BigOperators

theorem quadratic_divisor_coefficient_weight {N D : ℕ}
    (hD : Squarefree D) (ho : Odd D) (v : ℕ → ℂ) :
    (∑ n ∈ oddSquarefreeRange (N / D), (n.divisors.card : ℝ) *
      ‖quadraticDivisibilityCoeff D v n‖ ^ 2) ≤ quadraticDivisorWeight N D v := by
  unfold quadraticDivisorWeight quadraticDivisibilityCoeff
  simp only [apply_ite, norm_zero, ite_pow, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, mul_zero, ← Finset.sum_filter]
  rw [sum_oddSquarefree_multiples D N hD ho]
  apply Finset.sum_le_sum
  intro n hn
  have hn₀ : n ≠ 0 := (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).2.2.ne_zero
  have hmul₀ : D * n ≠ 0 := mul_ne_zero hD.ne_zero hn₀
  have hc : (n.divisors.card : ℝ) ≤ (D * n).divisors.card := by
    exact_mod_cast Finset.card_le_card (Nat.divisors_subset_of_dvd hmul₀ (dvd_mul_left n D))
  exact mul_le_mul_of_nonneg_right hc (sq_nonneg _)

theorem quadratic_rough_gcd_shorter {M N K D : ℕ} {T : ℝ}
    (hD : Squarefree D) (ho : Odd D) (hT : 0 ≤ T)
    (h : QuadraticRoughBound M (N / D) K T) (v : ℕ → ℂ) :
    ‖quadraticRoughGcdMoment M N K D v‖ ≤ T * quadraticDivisorWeight N D v := by
  apply (quadratic_rough_gcd_moment_divisors hD ho v).trans
  calc
    _ ≤ ∑ d ∈ Finset.Icc 1 (N / D), T * quadraticSieveEnergy (N / D)
        (fun n => if d ∣ n then quadraticDivisibilityCoeff D v n else 0) :=
      Finset.sum_le_sum (fun d _ => h _)
    _ = T * ∑ d ∈ Finset.Icc 1 (N / D), quadraticSieveEnergy (N / D)
        (fun n => if d ∣ n then quadraticDivisibilityCoeff D v n else 0) :=
      (Finset.mul_sum ..).symm
    _ ≤ T * ∑ n ∈ oddSquarefreeRange (N / D), (n.divisors.card : ℝ) *
        ‖quadraticDivisibilityCoeff D v n‖ ^ 2 :=
      mul_le_mul_of_nonneg_left (quadratic_divisibility_partial_energy _ _ _) hT
    _ ≤ _ := mul_le_mul_of_nonneg_left (quadratic_divisor_coefficient_weight hD ho v) hT

theorem quadratic_rough_energy_gcd (M N K : ℕ) (v : ℕ → ℂ) :
    (quadraticRoughEnergy M N K v : ℂ) =
      ∑ D ∈ Finset.Icc 1 N, quadraticRoughGcdMoment M N K D v := by
  unfold quadraticRoughEnergy quadraticRoughGcdMoment
  push_cast
  simp_rw [quadraticTranspose_norm_sq_gcd, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [quadraticSieveWeight_apply, mul_assoc]

theorem quadratic_rough_gcd_moment_zero {M N K D : ℕ}
    (he : quadraticGcdPairs N D = ∅) (v : ℕ → ℂ) :
    quadraticRoughGcdMoment M N K D v = 0 := by
  simp [quadraticRoughGcdMoment, quadraticGcdKernelSum, he]

/-- Heath-Brown's large-gcd descent, with the original small-gcd moments left
literal. The shorter range is the integer quotient N/D₀. -/
theorem quadratic_rough_gcd_descent {M N K D₀ : ℕ} {T : ℝ}
    (hD₀ : 0 < D₀) (hT : 0 ≤ T) (h : QuadraticRoughBound M (N / D₀) K T)
    (v : ℕ → ℂ) :
    quadraticRoughEnergy M N K v ≤
      (∑ D ∈ (Finset.Icc 1 N).filter (fun D => D ≤ D₀),
        ‖quadraticRoughGcdMoment M N K D v‖) + T * quadraticDivisorMoment N v := by
  have hn : quadraticRoughEnergy M N K v ≤
      ∑ D ∈ Finset.Icc 1 N, ‖quadraticRoughGcdMoment M N K D v‖ := by
    have he := congrArg Complex.re (quadratic_rough_energy_gcd M N K v)
    simp only [Complex.ofReal_re, Complex.re_sum] at he
    rw [he]
    exact Finset.sum_le_sum (fun D _ => Complex.re_le_norm _)
  have hs := Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 N)
    (fun D => D ≤ D₀) (fun D => ‖quadraticRoughGcdMoment M N K D v‖)
  rw [← hs] at hn
  apply hn.trans
  apply add_le_add le_rfl
  calc
    _ ≤ ∑ D ∈ (Finset.Icc 1 N).filter (fun D => ¬ D ≤ D₀),
        T * quadraticDivisorWeight N D v := by
      apply Finset.sum_le_sum
      intro D hmem
      have hle : D₀ ≤ D := le_of_lt (lt_of_not_ge (Finset.mem_filter.mp hmem).2)
      by_cases hsf : Squarefree D
      · by_cases ho : Odd D
        · exact quadratic_rough_gcd_shorter hsf ho hT
            (h.mono_second (Nat.div_le_div_left hle hD₀)) v
        · rw [quadratic_rough_gcd_moment_zero (quadraticGcdPairs_empty_of_not_odd N D ho), norm_zero]
          exact mul_nonneg hT (quadraticDivisorWeight_nonneg N D v)
      · rw [quadratic_rough_gcd_moment_zero (quadraticGcdPairs_empty_of_not_squarefree N D hsf), norm_zero]
        exact mul_nonneg hT (quadraticDivisorWeight_nonneg N D v)
    _ = T * ∑ D ∈ (Finset.Icc 1 N).filter (fun D => ¬ D ≤ D₀), quadraticDivisorWeight N D v :=
      (Finset.mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (quadratic_divisor_weight_sum N _ v) hT

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticOffDiagonalError
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Both actual off-diagonal Poisson errors are uniformly negligible -/

namespace Ostmann

open scoped Classical BigOperators ComplexConjugate

theorem quadratic_small_pair_error (A : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ M K D q : ℕ, 0 < M → 0 < D → 0 < q →
      ∀ J : ℝ, 1 ≤ J →
      ‖quadraticSmallPairSum M K D q - quadraticSmallPairCore M K D q J‖ ≤
        C * Real.sqrt M * K / J ^ A := by
  obtain ⟨C, hC, hc⟩ := quadratic_small_dyadic_uniform A
  refine ⟨C, hC, ?_⟩
  intro M K D q hM hD hq J hJ
  have hmod : 0 < 2 * (q * D) := by positivity
  have : NeZero (2 * (q * D)) := ⟨hmod.ne'⟩
  have hmod₁ : 2 * (q * D) ≠ 1 := by omega
  let T : ℝ := C * Real.sqrt M / J ^ A
  have hT : 0 ≤ T := by dsimp [T]; positivity
  unfold quadraticSmallPairSum quadraticSmallPairCore
  rw [← Finset.sum_sub_distrib]
  have hp (b : ℕ) (hb : b ∈ (oddSquarefreeRange K).filter (D.Coprime ·)) :
      ‖(jacobiSym b q : ℂ) *
          (∑' c : ℕ+, (1 : DirichletCharacter ℂ (2 * (q * D)))
            (c : ZMod (2 * (q * D))) * quadraticSieveWeight ((c : ℝ) ^ 2 * b / M)) -
        (jacobiSym b q : ℂ) * quadraticSmallDyadicCore quadraticSieveWeight M b J (2 * (q * D)) b‖ ≤ T := by
    have hb₀ : 0 < b := (Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hb).1).1).1
    have hh := hc M J (by exact_mod_cast hM) hJ _ hmod₁ b hb₀
    have hJac : ‖(jacobiSym b q : ℂ)‖ ≤ 1 := by
      rcases jacobiSym.trichotomy (b : ℤ) q with h | h | h <;> rw [h] <;> norm_num
    rw [← mul_sub, norm_mul]
    exact (mul_le_mul hJac hh (norm_nonneg _) zero_le_one).trans_eq (one_mul T)
  calc
    _ ≤ ∑ b ∈ (oddSquarefreeRange K).filter (D.Coprime ·), T :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum hp)
    _ = (((oddSquarefreeRange K).filter (D.Coprime ·)).card : ℝ) * T := by simp
    _ ≤ (K : ℝ) * T := by
      apply mul_le_mul_of_nonneg_right _ hT
      exact_mod_cast (Finset.card_filter_le _ _).trans (oddSquarefreeRange_card_le K)
    _ = _ := by dsimp [T]; ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticSecondMomentError
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The full second-Poisson remainder on the original dyadic coefficient block -/

namespace Ostmann

open scoped Classical BigOperators ComplexConjugate

theorem quadratic_gcd_remainder_support_bound (N : ℕ) (v : ℕ → ℂ)
    (E : ℕ → ℕ × ℕ → ℂ) {T : ℝ} (hT : 0 ≤ T)
    (hE : ∀ D ∈ Finset.Icc 1 N, ∀ z ∈ quadraticGcdPairs N D,
      v z.1 ≠ 0 → v z.2 ≠ 0 → ‖E D z‖ ≤ T) :
    ‖quadraticGcdRemainder N v E‖ ≤ T * N * quadraticSieveEnergy N v := by
  let F (D : ℕ) (z : ℕ × ℕ) := if v z.1 = 0 ∨ v z.2 = 0 then 0 else E D z
  have he : quadraticGcdRemainder N v E = quadraticGcdRemainder N v F := by
    unfold quadraticGcdRemainder
    apply Finset.sum_congr rfl
    intro D _
    apply Finset.sum_congr rfl
    intro z _
    dsimp [F]
    by_cases hz : v z.1 = 0 ∨ v z.2 = 0
    · rw [ite_eq_left hz]
      rcases hz with h | h <;> simp [h]
    · rw [ite_eq_right hz]
  rw [he]
  apply quadratic_gcd_remainder_bound N v F hT
  intro D hD z hz
  dsimp [F]
  split_ifs with h
  · simpa only [norm_zero] using hT
  · exact hE D hD z hz (fun hh => h (Or.inl hh)) (fun hh => h (Or.inr hh))

theorem quadratic_pair_dyadic_kernel {R D : ℕ} {z : ℕ × ℕ}
    (hz : z ∈ quadraticGcdPairs (2 * R) D) (h₁ : R ≤ z.1) (h₂ : R ≤ z.2) :
    ((R : ℝ) / D) ^ 2 ≤ quadraticPairKernel z.1 z.2 ∧
      (quadraticPairKernel z.1 z.2 : ℝ) ≤ 4 * ((R : ℝ) / D) ^ 2 := by
  obtain ⟨hD, _, _⟩ := quadratic_pair_product_bound hz
  obtain ⟨hz', hg⟩ := Finset.mem_filter.mp hz
  obtain ⟨hs, ht⟩ := Finset.mem_product.mp hz'
  have hs' := (Finset.mem_Icc.mp (Finset.mem_filter.mp hs).1).2
  have ht' := (Finset.mem_Icc.mp (Finset.mem_filter.mp ht).1).2
  have hp : (D : ℝ) ^ 2 * quadraticPairKernel z.1 z.2 = (z.1 : ℝ) * z.2 := by
    have hh := quadraticPairKernel_factor z.1 z.2
    rw [hg] at hh
    exact_mod_cast hh
  have hlo : (R : ℝ) ^ 2 ≤ (z.1 : ℝ) * z.2 := by
    have hh := Nat.mul_le_mul h₁ h₂
    have hhR : (R : ℝ) * R ≤ (z.1 : ℝ) * z.2 := by exact_mod_cast hh
    nlinarith
  have hhi : (z.1 : ℝ) * z.2 ≤ 4 * (R : ℝ) ^ 2 := by
    have hh := Nat.mul_le_mul hs' ht'
    have hh' : (z.1 : ℝ) * z.2 ≤ (2 * (R : ℝ)) * (2 * R) := by exact_mod_cast hh
    nlinarith
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  constructor
  · rw [div_pow]
    apply (div_le_iff₀ (pow_pos hDR 2)).mpr
    nlinarith
  · rw [div_pow, ← mul_div_assoc]
    apply (le_div_iff₀ (pow_pos hDR 2)).mpr
    nlinarith

theorem quadratic_polynomial_error_power_choice {δ : ℝ} (hδ : 0 < δ) (P Q : ℕ) :
    ∃ A : ℕ, ∀ X : ℝ, 1 ≤ X → X ^ Q / (X ^ δ) ^ A ≤ 1 / X ^ P := by
  obtain ⟨A, hA⟩ := exists_nat_ge (((P : ℝ) + Q) / δ)
  refine ⟨A, ?_⟩
  intro X hX
  have hX₀ : 0 < X := zero_lt_one.trans_le hX
  have hexp : (P : ℝ) + Q ≤ δ * A := by
    have hh := (div_le_iff₀ hδ).mp hA
    nlinarith
  have hp : X ^ (P + Q) ≤ (X ^ δ) ^ A := by
    calc
      _ = X ^ ((P : ℝ) + Q) := by rw [← Real.rpow_natCast, Nat.cast_add]
      _ ≤ X ^ (δ * A) := Real.rpow_le_rpow_of_exponent_le hX hexp
      _ = _ := by rw [Real.rpow_mul hX₀.le, Real.rpow_natCast]
  calc
    _ ≤ X ^ Q / X ^ (P + Q) :=
      div_le_div_of_nonneg_left (by positivity) (pow_pos hX₀ _) hp
    _ = _ := by rw [pow_add]; field_simp

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticSmallGcdTransform
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual small-gcd moment in the Poisson comparison -/

namespace Ostmann

open scoped Classical BigOperators ComplexConjugate

theorem quadratic_rough_gcd_pair_sum (M N K D : ℕ) (v : ℕ → ℂ) :
    quadraticRoughGcdMoment M N K D v =
      ∑ z ∈ quadraticGcdPairs N D, v z.1 * conj (v z.2) *
        ∑ m ∈ quadraticRoughKernelRange (3 * M) K,
          quadraticSieveWeight ((m : ℝ) / M) * (jacobiSym m z.1 : ℂ) * (jacobiSym m z.2 : ℂ) := by
  unfold quadraticRoughGcdMoment quadraticGcdKernelSum
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z hz
  apply Finset.sum_congr rfl
  intro m _
  obtain ⟨hz, hg⟩ := Finset.mem_filter.mp hz
  obtain ⟨hs, ht⟩ := Finset.mem_product.mp hz
  have hj := congrArg (fun x : ℤ => (x : ℂ))
    (jacobi_pair_kernel (Finset.mem_filter.mp hs).2.2 (Finset.mem_filter.mp ht).2.2 (m : ℤ))
  rw [hg] at hj
  push_cast at hj
  calc
    _ = (v z.1 * conj (v z.2)) * quadraticSieveWeight ((m : ℝ) / M) *
        ((jacobiSym m z.1 : ℂ) * (jacobiSym m z.2 : ℂ)) := by
      rw [hj]
      split_ifs <;> ring
    _ = _ := by ring

theorem quadratic_rough_gcd_transform {M : ℕ} (hM : 0 < M)
    (N K D : ℕ) (v : ℕ → ℂ) :
    quadraticRoughGcdMoment M N K D v =
      ∑ z ∈ quadraticGcdPairs N D, v z.1 * conj (v z.2) *
        (quadraticFirstKernelTransform M D (quadraticPairKernel z.1 z.2) -
          quadraticSmallPairSum M K D (quadraticPairKernel z.1 z.2)) := by
  rw [quadratic_rough_gcd_pair_sum]
  apply Finset.sum_congr rfl
  intro z hz
  rw [quadratic_rough_pair_transform hM K hz]

/-- Small gcds cannot contain a diagonal pair in the actual dyadic support. -/
theorem quadratic_small_gcd_ne_diagonal {R D : ℕ} (hDR : D < R)
    (v : ℕ → ℂ) (hsupp : ∀ n ∈ oddSquarefreeRange (2 * R), n < R → v n = 0)
    {z : ℕ × ℕ} (hz : z ∈ quadraticGcdPairs (2 * R) D) (hv : v z.1 ≠ 0) :
    z.1 ≠ z.2 := by
  intro heq
  have hg := (Finset.mem_filter.mp hz).2
  rw [heq, Nat.gcd_self] at hg
  have hs := (Finset.mem_product.mp (Finset.mem_filter.mp hz).1).1
  apply hv
  apply hsupp z.1 hs
  omega

theorem quadratic_small_gcd_moment_decomposition {M : ℕ} (hM : 0 < M)
    (R K D : ℕ) (J : ℝ) (v : ℕ → ℂ) :
    quadraticRoughGcdMoment M (2 * R) K D v =
      (quadraticTransformedFirstMain M (2 * R) D K quadraticSieveWeight v -
        quadraticSmallTransformedMain M (2 * R) D K quadraticSieveWeight v) +
      quadraticGcdMomentCorrections M R K D J v + quadraticGcdMomentError M R K D J v := by
  rw [quadratic_rough_gcd_transform hM,
    ← quadratic_pair_main_difference_sum]
  unfold quadraticGcdMomentCorrections quadraticGcdMomentError
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro z _
  rw [quadratic_first_second_kernel_split, quadratic_small_pair_core_main]
  unfold quadraticPairMainDifference
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticGcdMainGrowth
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The genuine main-term cancellation under the current sieve exponent -/

namespace Ostmann

open scoped Classical BigOperators

/-- Only the fourth power of the common divisor is needed for exponents at
most two; the shortened matrix parameter remains the actual integer K D². -/
theorem quadratic_gcd_main_exponent {ξ : ℝ} (hξ : ξ ≤ 2)
    {K D : ℕ} (hK : 0 < K) (hD : 0 < D) (N : ℝ) (hN : 0 ≤ N) :
    (((K * D ^ 2 : ℕ) : ℝ) ^ ξ + N) ≤
      (D : ℝ) ^ 4 * ((K : ℝ) ^ ξ + N) := by
  have hDR : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hDpow : ((D : ℝ) ^ 2) ^ ξ ≤ (D : ℝ) ^ 4 := by
    calc
      _ ≤ ((D : ℝ) ^ 2) ^ (2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ hDR) hξ
      _ = _ := by rw [Real.rpow_two]; ring
  have hDfour : (1 : ℝ) ≤ (D : ℝ) ^ 4 := one_le_pow₀ hDR
  push_cast
  rw [Real.mul_rpow (Nat.cast_nonneg K) (by positivity)]
  have hp : 0 ≤ (K : ℝ) ^ ξ := by positivity
  have hh := mul_le_mul_of_nonneg_left hDpow hp
  have hn := mul_le_mul_of_nonneg_right hDfour hN
  nlinarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticMainPowerCost
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual main-term normalization and its small-power arithmetic cost -/

namespace Ostmann

theorem quadratic_main_power_cost {η X R D K : ℝ} (hη : 0 ≤ η) (hX : 1 ≤ X)
    (hR : 0 ≤ R) (hD : 0 ≤ D) (hK : 0 ≤ K)
    (hRX : R ≤ X) (hDR : D ≤ R) (hKX : K ≤ X ^ 3) :
    (K * D ^ 2 * (2 * R)) ^ (2 * η) * D ^ η ≤ 2 ^ (3 * η) * X ^ (36 * η) := by
  have hX₀ : 0 ≤ X := by linarith
  let Y := 2 * X ^ 6
  have hY : 0 < Y := by dsimp [Y]; positivity
  have hb : K * D ^ 2 * (2 * R) ≤ Y := by
    calc
      _ ≤ X ^ 3 * X ^ 2 * (2 * X) := by gcongr; exact hDR.trans hRX
      _ = Y := by dsimp [Y]; ring
  have hDY : D ≤ Y := by
    have hh : X ≤ X ^ 6 := by simpa using pow_le_pow_right₀ hX (by norm_num : 1 ≤ (6 : ℕ))
    dsimp [Y]
    nlinarith [hDR.trans hRX, pow_nonneg hX₀ 6]
  calc
    _ ≤ Y ^ (2 * η) * Y ^ η := mul_le_mul
      (Real.rpow_le_rpow (by positivity) hb (by positivity))
      (Real.rpow_le_rpow hD hDY hη) (Real.rpow_nonneg hD η) (Real.rpow_nonneg hY.le _)
    _ = Y ^ (3 * η) := by rw [← Real.rpow_add hY]; congr 1; ring
    _ = 2 ^ (3 * η) * X ^ (18 * η) := by
      dsimp [Y]
      rw [Real.mul_rpow (by norm_num) (pow_nonneg hX₀ 6)]
      congr 1
      rw [← Real.rpow_natCast, ← Real.rpow_mul hX₀]
      congr 1
      norm_num
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hX (by linarith)) (by positivity)

theorem quadratic_main_scale {M R K ξ : ℝ} (hK : 0 < K) :
    Real.sqrt M / Real.sqrt K * (K ^ ξ + 2 * R) =
      Real.sqrt M * K ^ (ξ - 1 / 2) + 2 * (Real.sqrt M * R / Real.sqrt K) := by
  rw [Real.rpow_sub hK, ← Real.sqrt_eq_rpow]
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticSmallGcdError
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The three complete Poisson remainders at each small common divisor -/

namespace Ostmann

open scoped Classical BigOperators ComplexConjugate

theorem quadratic_gcd_pair_support_bound {N D : ℕ}
    (hD : D ∈ Finset.Icc 1 N) (v : ℕ → ℂ) (E : ℕ × ℕ → ℂ)
    {T : ℝ} (hT : 0 ≤ T)
    (hE : ∀ z ∈ quadraticGcdPairs N D, v z.1 ≠ 0 → v z.2 ≠ 0 → ‖E z‖ ≤ T) :
    ‖∑ z ∈ quadraticGcdPairs N D, v z.1 * conj (v z.2) * E z‖ ≤
      T * N * quadraticSieveEnergy N v := by
  let F (d : ℕ) (z : ℕ × ℕ) : ℂ := if d = D then E z else 0
  have he : quadraticGcdRemainder N v F =
      ∑ z ∈ quadraticGcdPairs N D, v z.1 * conj (v z.2) * E z := by
    unfold quadraticGcdRemainder F
    simp only [mul_ite, mul_zero, Finset.sum_ite_irrel, Finset.sum_const_zero]
    simp [hD]
  rw [← he]
  apply quadratic_gcd_remainder_support_bound N v F hT
  intro d _ z hz hv hw
  dsimp [F]
  split_ifs with hd
  · subst d
    exact hE z hz hv hw
  · simpa only [norm_zero] using hT

theorem quadratic_small_gcd_error (A : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ M R K D : ℕ, 1 ≤ M → 1 ≤ R → 0 < D → D < R →
      ∀ J : ℝ, 1 ≤ J →
      2 * (2 * (R : ℝ)) ^ 2 * J ≤ (M : ℝ) * ((K : ℝ) + 1) →
      (K : ℝ) ≤ ((M : ℝ) * R) ^ 3 →
      ∀ v : ℕ → ℂ, (∀ n ∈ oddSquarefreeRange (2 * R), n < R → v n = 0) →
      ‖quadraticGcdMomentError M R K D J v‖ ≤
        C * (((M : ℝ) * R) ^ 6 / J ^ A) * quadraticSieveEnergy (2 * R) v := by
  obtain ⟨C₁, hC₁, hc₁⟩ := quadratic_first_kernel_error A
  obtain ⟨C₂, hC₂, hc₂⟩ := quadratic_first_second_kernel_error A
  obtain ⟨C₃, hC₃, hc₃⟩ := quadratic_small_pair_error A
  let C := 64 * C₁ + C₂ + C₃
  refine ⟨2 * C, by dsimp [C]; positivity, ?_⟩
  intro M R K D hM hR hD hDR J hJ hcut hK v hsupp
  have hMR : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hRR : (1 : ℝ) ≤ R := by exact_mod_cast hR
  have hDRR : (D : ℝ) ≤ R := by exact_mod_cast hDR.le
  have hprod : 1 ≤ (M : ℝ) * R := one_le_mul_of_one_le_of_one_le hMR hRR
  have hMN : (0 : ℝ) < M := zero_lt_one.trans_le hMR
  have hRN : (0 : ℝ) < R := zero_lt_one.trans_le hRR
  have hRprod : (R : ℝ) ≤ (M : ℝ) * R := by nlinarith
  have hMprod : (M : ℝ) ≤ (M : ℝ) * R := by nlinarith
  have hDmem : D ∈ Finset.Icc 1 (2 * R) := Finset.mem_Icc.mpr ⟨hD, by omega⟩
  have hb : ‖quadraticGcdMomentError M R K D J v‖ ≤
      (C * (((M : ℝ) * R) ^ 4 / J ^ A)) * (2 * R) * quadraticSieveEnergy (2 * R) v := by
    unfold quadraticGcdMomentError
    have hcast : (2 * (R : ℝ)) = ((2 * R : ℕ) : ℝ) := by push_cast; rfl
    rw [hcast]
    apply quadratic_gcd_pair_support_bound hDmem v _ (by dsimp [C]; positivity)
    intro z hz hv hw
    have hne := quadratic_small_gcd_ne_diagonal hDR v hsupp hz hv
    obtain ⟨hz', _⟩ := Finset.mem_filter.mp hz
    obtain ⟨hs, ht⟩ := Finset.mem_product.mp hz'
    have hlo : R ≤ z.1 := by by_contra! hh; exact hv (hsupp _ hs hh)
    have hhi : R ≤ z.2 := by by_contra! hh; exact hw (hsupp _ ht hh)
    obtain ⟨hqlo, hqhi⟩ := quadratic_pair_dyadic_kernel hz hlo hhi
    have hsf := quadraticPairKernel_squarefree (Finset.mem_filter.mp hs).2.2 (Finset.mem_filter.mp ht).2.2
    have ho := quadraticPairKernel_odd (Finset.mem_filter.mp hs).2.1 (Finset.mem_filter.mp ht).2.1
    have hqne : quadraticPairKernel z.1 z.2 ≠ 1 :=
      mt (quadraticPairKernel_eq_one_iff (Finset.mem_filter.mp hs).2.2 (Finset.mem_filter.mp ht).2.2).mp hne
    have he₁ := hc₁ M (2 * R) D K (by omega) J hJ
      (by simpa only [Nat.cast_mul, Nat.cast_ofNat] using hcut) z hz hne
    have he₂ := hc₂ M D _ K (by omega) hsf ho hqne ((R : ℝ) / D) J
      (by positivity) hJ hqlo hqhi
    have he₃ := hc₃ M K D _ (by omega) hD (Nat.pos_of_ne_zero hsf.ne_zero) J hJ
    have hcost₁ : 4 * C₁ * ((2 * R : ℕ) : ℝ) ^ 4 / ((M : ℝ) * J ^ A) ≤
        64 * C₁ * (((M : ℝ) * R) ^ 4 / J ^ A) := by
      have hrpow := pow_le_pow_left₀ (Nat.cast_nonneg R) hRprod 4
      have hmdiv : (R : ℝ) ^ 4 / M ≤ ((M : ℝ) * R) ^ 4 :=
        (div_le_self (by positivity) hMR).trans hrpow
      calc
        _ = 64 * C₁ * ((R : ℝ) ^ 4 / M) / J ^ A := by push_cast; ring
        _ ≤ 64 * C₁ * (((M : ℝ) * R) ^ 4) / J ^ A :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hmdiv (by positivity)) (by positivity)
        _ = _ := by ring
    have hcost₂ : C₂ * Real.sqrt M * D * K / J ^ A ≤
        C₂ * (((M : ℝ) * R) ^ 4 / J ^ A) := by
      have hh : Real.sqrt M * D * K ≤ ((M : ℝ) * R) ^ 4 := by
        calc
          _ ≤ (M : ℝ) * R * (((M : ℝ) * R) ^ 3) := by
            gcongr
            exact Real.sqrt_le_self_iff.mpr (Or.inr hMR)
          _ = _ := by ring
      calc
        _ = C₂ * (Real.sqrt M * D * K) / J ^ A := by ring
        _ ≤ C₂ * (((M : ℝ) * R) ^ 4) / J ^ A :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hh hC₂.le) (by positivity)
        _ = _ := by ring
    have hcost₃ : C₃ * Real.sqrt M * K / J ^ A ≤
        C₃ * (((M : ℝ) * R) ^ 4 / J ^ A) := by
      have hh : Real.sqrt M * K ≤ ((M : ℝ) * R) ^ 4 := by
        calc
          _ ≤ ((M : ℝ) * R) * (((M : ℝ) * R) ^ 3) := by
            gcongr
            exact (Real.sqrt_le_self_iff.mpr (Or.inr hMR)).trans hMprod
          _ = _ := by ring
      calc
        _ = C₃ * (Real.sqrt M * K) / J ^ A := by ring
        _ ≤ C₃ * (((M : ℝ) * R) ^ 4) / J ^ A :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hh hC₃.le) (by positivity)
        _ = _ := by ring
    apply ((norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)).trans
    dsimp [C]
    linarith
  apply hb.trans
  have hp : ((M : ℝ) * R) ^ 5 ≤ ((M : ℝ) * R) ^ 6 := pow_le_pow_right₀ hprod (by omega)
  have hn : 0 ≤ quadraticSieveEnergy (2 * R) v := Finset.sum_nonneg fun _ _ => sq_nonneg _
  apply mul_le_mul_of_nonneg_right _ hn
  calc
    _ ≤ (2 * C) * (((M : ℝ) * R) ^ 5 / J ^ A) := by
      have hc : 0 ≤ C := by dsimp [C]; positivity
      have hh := mul_le_mul_of_nonneg_left hRprod (show 0 ≤ 2 * C * (((M : ℝ) * R) ^ 4 / J ^ A) by positivity)
      first | (convert hh using 1 <;> ring) | exact (le_of_eq (by ring)).trans (hh.trans (le_of_eq (by ring)))
    _ ≤ _ := by gcongr

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticSmallGcdPowerSaving
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform arbitrary power saving at every retained small gcd -/

namespace Ostmann

open scoped Classical BigOperators

theorem quadratic_small_gcd_error_arbitrary_power {δ : ℝ} (hδ : 0 < δ) (P : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ M R K D : ℕ, 1 ≤ M → 1 ≤ R → 0 < D → D < R →
      ∀ J : ℝ, ((M : ℝ) * R) ^ δ ≤ J →
      2 * (2 * (R : ℝ)) ^ 2 * J ≤ (M : ℝ) * ((K : ℝ) + 1) →
      (K : ℝ) ≤ ((M : ℝ) * R) ^ 3 →
      ∀ v : ℕ → ℂ, (∀ n ∈ oddSquarefreeRange (2 * R), n < R → v n = 0) →
      ‖quadraticGcdMomentError M R K D J v‖ ≤
        C / (((M : ℝ) * R) ^ P) * quadraticSieveEnergy (2 * R) v := by
  obtain ⟨A, hA⟩ := quadratic_polynomial_error_power_choice hδ P 6
  obtain ⟨C, hC, hc⟩ := quadratic_small_gcd_error A
  refine ⟨C, hC, ?_⟩
  intro M R K D hM hR hD hDR J hJ hcut hK v hsupp
  have hprod : 1 ≤ (M : ℝ) * R := one_le_mul_of_one_le_of_one_le
    (by exact_mod_cast hM) (by exact_mod_cast hR)
  have hJone : 1 ≤ J := (Real.one_le_rpow hprod hδ.le).trans hJ
  have hp := hA ((M : ℝ) * R) hprod
  have he : 0 ≤ quadraticSieveEnergy (2 * R) v := Finset.sum_nonneg fun _ _ => sq_nonneg _
  apply (hc M R K D hM hR hD hDR J hJone hcut hK v hsupp).trans
  calc
    _ ≤ C * (((M : ℝ) * R) ^ 6 / (((M : ℝ) * R) ^ δ) ^ A) *
        quadraticSieveEnergy (2 * R) v := by gcongr
    _ ≤ C * (1 / (((M : ℝ) * R) ^ P)) * quadraticSieveEnergy (2 * R) v := by gcongr
    _ = _ := by ring

/-- The large-gcd loss in the descent is only an arbitrary small power. -/
theorem quadratic_rough_gcd_descent_epsilon (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ M N K D₀ : ℕ, 0 < D₀ → ∀ T : ℝ, 0 ≤ T →
      QuadraticRoughBound M (N / D₀) K T → ∀ v : ℕ → ℂ,
      quadraticRoughEnergy M N K v ≤
        (∑ D ∈ (Finset.Icc 1 N).filter (fun D => D ≤ D₀),
          ‖quadraticRoughGcdMoment M N K D v‖) +
        C * (N : ℝ) ^ ε * T * quadraticSieveEnergy N v := by
  obtain ⟨C, hC, hc⟩ := quadratic_divisor_moment_bound ε hε
  refine ⟨C, hC, ?_⟩
  intro M N K D₀ hD₀ T hT h v
  apply (quadratic_rough_gcd_descent hD₀ hT h v).trans
  apply add_le_add le_rfl
  have hh := mul_le_mul_of_nonneg_left (hc N v) hT
  convert hh using 1 <;> first | rfl | ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticSmallGcdAssembly
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The small-gcd moment with only its literal correction sum left -/

namespace Ostmann

open scoped Classical BigOperators

theorem quadratic_small_gcd_comparison {ξ δ ε : ℝ}
    (h : QuadraticSieveGrowth ξ) (hδ : 0 < δ) (hε : 0 < ε) (P : ℕ) :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
      ∀ M R K D : ℕ, 1 ≤ M → 1 ≤ R → Squarefree D → Odd D → D < R → 0 < K →
      ∀ J : ℝ, ((M : ℝ) * R) ^ δ ≤ J →
      2 * (2 * (R : ℝ)) ^ 2 * J ≤ (M : ℝ) * ((K : ℝ) + 1) →
      (K : ℝ) ≤ ((M : ℝ) * R) ^ 3 →
      ∀ v : ℕ → ℂ, (∀ n ∈ oddSquarefreeRange (2 * R), n < R → v n = 0) →
      ‖quadraticRoughGcdMoment M (2 * R) K D v‖ ≤
        (C₁ * (((K * D ^ 2 : ℕ) : ℝ) * (2 * R)) ^ (2 * ε) * (D : ℝ) ^ ε *
          (Real.sqrt M / Real.sqrt K) * (((K * D ^ 2 : ℕ) : ℝ) ^ ξ + 2 * R) +
          C₂ / (((M : ℝ) * R) ^ P)) * quadraticSieveEnergy (2 * R) v +
          ‖quadraticGcdMomentCorrections M R K D J v‖ := by
  obtain ⟨C₁, hC₁, hc₁⟩ := quadratic_gcd_main_growth h hε
  obtain ⟨C₂, hC₂, hc₂⟩ := quadratic_small_gcd_error_arbitrary_power hδ P
  refine ⟨C₁, C₂, hC₁, hC₂, ?_⟩
  intro M R K D hM hR hD ho hDR hK J hJ hcut hKB v hsupp
  have hm := hc₁ M (2 * R) D K (by omega) (by omega) hD ho hK v
  have he := hc₂ M R K D hM hR (Nat.pos_of_ne_zero hD.ne_zero) hDR J hJ hcut hKB v hsupp
  have hn := norm_add_le
    ((quadraticTransformedFirstMain M (2 * R) D K quadraticSieveWeight v -
      quadraticSmallTransformedMain M (2 * R) D K quadraticSieveWeight v) +
      quadraticGcdMomentCorrections M R K D J v) (quadraticGcdMomentError M R K D J v)
  have hn₂ := norm_add_le
    (quadraticTransformedFirstMain M (2 * R) D K quadraticSieveWeight v -
      quadraticSmallTransformedMain M (2 * R) D K quadraticSieveWeight v)
    (quadraticGcdMomentCorrections M R K D J v)
  rw [quadratic_small_gcd_moment_decomposition (by omega) R K D J v]
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hm ⊢
  nlinarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticSmallGcdGrowth
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The complete small-gcd comparison with a proved small-power error -/

namespace Ostmann

open scoped Classical BigOperators

theorem quadratic_small_gcd_growth {ξ η : ℝ} (h : QuadraticSieveGrowth ξ)
    (hξ : 1 / 2 ≤ ξ) (hξ' : ξ ≤ 2) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ M R D K : ℕ, 0 < M → 0 < R → Squarefree D → Odd D → D < R → 0 < K →
      (K : ℝ) ≤ ((M : ℝ) * R) ^ 3 →
      2 * (2 * (R : ℝ)) ^ 2 * (((M : ℝ) * R) ^ η) ≤ (M : ℝ) * ((K : ℝ) + 1) →
      ∀ v : ℕ → ℂ, (∀ n < R, v n = 0) →
        ‖quadraticRoughGcdMoment M (2 * R) K D v‖ ≤
          C * ((M : ℝ) * R) ^ (36 * η) * (D : ℝ) ^ 4 *
            ((M : ℝ) + R + Real.sqrt M * (K : ℝ) ^ (ξ - 1 / 2) +
              Real.sqrt M * R / Real.sqrt K) * quadraticSieveEnergy (2 * R) v := by
  obtain ⟨C₁, C₂, hC₁, hC₂, hc⟩ := quadratic_small_gcd_comparison h hη hη 1
  obtain ⟨C₃, hC₃, hcorr⟩ := quadratic_gcd_corrections_power_bound h hξ hξ' hη
  let C := 2 * C₁ * 2 ^ (3 * η) + C₂ + C₃
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro M R D K hM hR hD ho hDR hK hKX hcut v hv
  let X := (M : ℝ) * R
  let V := (M : ℝ) + R + Real.sqrt M * (K : ℝ) ^ (ξ - 1 / 2) +
    Real.sqrt M * R / Real.sqrt K
  let F := X ^ (36 * η) * (D : ℝ) ^ 4 * V
  let E := quadraticSieveEnergy (2 * R) v
  have hE : 0 ≤ E := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hM₁ : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hR₁ : (1 : ℝ) ≤ R := by exact_mod_cast hR
  have hD₁ : (1 : ℝ) ≤ D := by exact_mod_cast Nat.pos_of_ne_zero hD.ne_zero
  have hX : 1 ≤ X := one_le_mul_of_one_le_of_one_le hM₁ hR₁
  have hRX : (R : ℝ) ≤ X := by dsimp [X]; nlinarith
  have hV₁ : 1 ≤ V := by
    dsimp [V]
    have : 0 ≤ Real.sqrt M * (K : ℝ) ^ (ξ - 1 / 2) := by positivity
    have : 0 ≤ Real.sqrt M * R / Real.sqrt K := by positivity
    linarith
  have hF₁ : 1 ≤ F := one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le (Real.one_le_rpow hX (by positivity)) (one_le_pow₀ hD₁)) hV₁
  have hb := hc M R K D hM hR hD ho hDR hK (X ^ η) le_rfl hcut hKX v
    (fun n _ hn => hv n hn)
  have hcoef := quadratic_main_power_cost hη.le hX (Nat.cast_nonneg R) (Nat.cast_nonneg D)
    (Nat.cast_nonneg K) hRX (by exact_mod_cast hDR.le) hKX
  have hexp := quadratic_gcd_main_exponent hξ' hK (Nat.pos_of_ne_zero hD.ne_zero)
    (2 * (R : ℝ)) (by positivity)
  have hscale : Real.sqrt M / Real.sqrt K * ((K : ℝ) ^ ξ + 2 * R) ≤ 2 * V := by
    rw [quadratic_main_scale (by exact_mod_cast hK)]
    dsimp [V]
    have : 0 ≤ Real.sqrt M * (K : ℝ) ^ (ξ - 1 / 2) := by positivity
    linarith
  have hmain : C₁ * (((K * D ^ 2 : ℕ) : ℝ) * (2 * R)) ^ (2 * η) * (D : ℝ) ^ η *
      (Real.sqrt M / Real.sqrt K) * (((K * D ^ 2 : ℕ) : ℝ) ^ ξ + 2 * R) ≤
      (2 * C₁ * 2 ^ (3 * η)) * F := by
    calc
      _ = C₁ * ((((K * D ^ 2 : ℕ) : ℝ) * (2 * R)) ^ (2 * η) * (D : ℝ) ^ η) *
          ((Real.sqrt M / Real.sqrt K) * (((K * D ^ 2 : ℕ) : ℝ) ^ ξ + 2 * R)) := by ring
      _ ≤ C₁ * (2 ^ (3 * η) * X ^ (36 * η)) *
          ((Real.sqrt M / Real.sqrt K) * ((D : ℝ) ^ 4 * ((K : ℝ) ^ ξ + 2 * R))) := by
        apply mul_le_mul
        · apply mul_le_mul_of_nonneg_left _ hC₁.le
          simpa only [Nat.cast_mul, Nat.cast_pow] using hcoef
        · exact mul_le_mul_of_nonneg_left hexp (by positivity)
        · positivity
        · positivity
      _ = (C₁ * 2 ^ (3 * η) * X ^ (36 * η) * (D : ℝ) ^ 4) *
          ((Real.sqrt M / Real.sqrt K) * ((K : ℝ) ^ ξ + 2 * R)) := by ring
      _ ≤ (C₁ * 2 ^ (3 * η) * X ^ (36 * η) * (D : ℝ) ^ 4) * (2 * V) := by gcongr
      _ = _ := by dsimp [F]; ring
  have herr : C₂ / X ^ (1 : ℕ) ≤ C₂ * F := by
    rw [pow_one]
    exact (div_le_self hC₂.le hX).trans (le_mul_of_one_le_right hC₂.le hF₁)
  have hco := hcorr M R D K hM hR hD ho hDR.le hK hKX v hv
  have hcor : ‖quadraticGcdMomentCorrections M R K D (X ^ η) v‖ ≤ C₃ * F * E := by
    apply hco.trans
    calc
      _ = C₃ * X ^ (36 * η) * (D : ℝ) ^ 2 *
          ((M : ℝ) + R + Real.sqrt M * (K : ℝ) ^ (ξ - 1 / 2)) * E := by ring
      _ ≤ C₃ * X ^ (36 * η) * (D : ℝ) ^ 4 * V * E := by
        apply mul_le_mul_of_nonneg_right _ hE
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hD₁ (by norm_num : 2 ≤ (4 : ℕ))) (by positivity)
        · change (M : ℝ) + R + Real.sqrt M * (K : ℝ) ^ (ξ - 1 / 2) ≤ V
          dsimp [V]
          exact le_add_of_nonneg_right (by positivity)
        · positivity
        · positivity
      _ = C₃ * F * E := by dsimp [F]; ring
  have hmE := mul_le_mul_of_nonneg_right hmain hE
  have heE := mul_le_mul_of_nonneg_right herr hE
  calc
    _ ≤ (2 * C₁ * 2 ^ (3 * η) + C₂ + C₃) * F * E := by
      change ‖quadraticRoughGcdMoment M (2 * R) K D v‖ ≤
        (_ + C₂ / X ^ (1 : ℕ)) * E + ‖quadraticGcdMomentCorrections M R K D (X ^ η) v‖ at hb
      nlinarith only [hb, hmE, heE, hcor]
    _ = _ := by dsimp [C, F, X, V, E]; ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticSmallGcdSum
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform summation of the bounded common divisors -/

namespace Ostmann

open scoped Classical BigOperators

theorem quadraticDescentScale_nonneg (ξ : ℝ) (M N K : ℕ) :
    0 ≤ quadraticDescentScale ξ M N K := by
  unfold quadraticDescentScale
  positivity

theorem quadraticDescentScale_mono {ξ : ℝ} {M N R K : ℕ} (h : R ≤ N) :
    quadraticDescentScale ξ M R K ≤ quadraticDescentScale ξ M N K := by
  unfold quadraticDescentScale
  gcongr

theorem quadratic_small_gcd_sum_growth {ξ η : ℝ} (h : QuadraticSieveGrowth ξ)
    (hξ : 1 / 2 ≤ ξ) (hξ' : ξ ≤ 2) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ M N R K D₀ : ℕ,
      0 < M → 0 < R → R ≤ N → 0 < D₀ → D₀ < R → 0 < K → K ≤ M →
      2 * (2 * (N : ℝ)) ^ 2 * (((M : ℝ) * N) ^ η) ≤ (M : ℝ) * ((K : ℝ) + 1) →
      ∀ v : ℕ → ℂ, (∀ n < R, v n = 0) →
        (∑ D ∈ (Finset.Icc 1 (2 * R)).filter (fun D => D ≤ D₀),
          ‖quadraticRoughGcdMoment M (2 * R) K D v‖) ≤
          C * ((M : ℝ) * N) ^ (36 * η) * (D₀ : ℝ) ^ 5 *
            quadraticDescentScale ξ M N K * quadraticSieveEnergy (2 * R) v := by
  obtain ⟨C, hC, hc⟩ := quadratic_small_gcd_growth h hξ hξ' hη
  refine ⟨C, hC, ?_⟩
  intro M N R K D₀ hM hR hRN hD₀ hDR hK hKM hcut v hv
  have hMR : 1 ≤ (M : ℝ) * R := one_le_mul_of_one_le_of_one_le
    (by exact_mod_cast hM) (by exact_mod_cast hR)
  have hMX : (M : ℝ) ≤ (M : ℝ) * R := by
    nlinarith [show (1 : ℝ) ≤ R by exact_mod_cast hR]
  have hKX : (K : ℝ) ≤ ((M : ℝ) * R) ^ 3 :=
    (show (K : ℝ) ≤ M by exact_mod_cast hKM).trans
      (hMX.trans (le_self_pow₀ hMR (by norm_num)))
  have hNR : (R : ℝ) ≤ N := by exact_mod_cast hRN
  have hpow : ((M : ℝ) * R) ^ (36 * η) ≤ ((M : ℝ) * N) ^ (36 * η) := by
    apply Real.rpow_le_rpow (by positivity) _ (by positivity)
    exact mul_le_mul_of_nonneg_left hNR (Nat.cast_nonneg M)
  have hcutR : 2 * (2 * (R : ℝ)) ^ 2 * (((M : ℝ) * R) ^ η) ≤
      (M : ℝ) * ((K : ℝ) + 1) := by
    apply le_trans _ hcut
    gcongr
  let A := C * ((M : ℝ) * N) ^ (36 * η) * (D₀ : ℝ) ^ 4 *
    quadraticDescentScale ξ M N K * quadraticSieveEnergy (2 * R) v
  have hA : 0 ≤ A := by
    dsimp [A]
    exact mul_nonneg (mul_nonneg (by positivity) (quadraticDescentScale_nonneg _ _ _ _))
      (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hs : (Finset.Icc 1 (2 * R)).filter (fun D => D ≤ D₀) ⊆ Finset.Icc 1 D₀ := by
    intro D hD
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp (Finset.mem_filter.mp hD).1).1,
      (Finset.mem_filter.mp hD).2⟩
  calc
    _ ≤ ∑ _D ∈ (Finset.Icc 1 (2 * R)).filter (fun D => D ≤ D₀), A := by
      apply Finset.sum_le_sum
      intro D hmem
      have hDle := (Finset.mem_filter.mp hmem).2
      by_cases hD : Squarefree D
      · by_cases ho : Odd D
        · apply (hc M R D K hM hR hD ho (hDle.trans_lt hDR) hK hKX hcutR v hv).trans
          change C * ((M : ℝ) * R) ^ (36 * η) * (D : ℝ) ^ 4 *
            quadraticDescentScale ξ M R K * quadraticSieveEnergy (2 * R) v ≤ A
          dsimp only [A]
          apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
          exact mul_le_mul
            (mul_le_mul (mul_le_mul_of_nonneg_left hpow hC.le)
              (pow_le_pow_left₀ (Nat.cast_nonneg D) (by exact_mod_cast hDle) 4)
              (by positivity) (by positivity))
            (quadraticDescentScale_mono hRN) (quadraticDescentScale_nonneg _ _ _ _)
            (by positivity)
        · rw [quadratic_rough_gcd_moment_zero (quadraticGcdPairs_empty_of_not_odd (2 * R) D ho),
            norm_zero]
          exact hA
      · rw [quadratic_rough_gcd_moment_zero (quadraticGcdPairs_empty_of_not_squarefree (2 * R) D hD),
          norm_zero]
        exact hA
    _ ≤ ∑ _D ∈ Finset.Icc 1 D₀, A :=
      Finset.sum_le_sum_of_subset_of_nonneg hs (fun _ _ _ => hA)
    _ = _ := by simp [A]; ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticRoughDescent
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One complete descent step for the original rough moment -/

namespace Ostmann

open scoped Classical BigOperators

theorem quadratic_rough_descent {ξ η : ℝ} (h : QuadraticSieveGrowth ξ)
    (hξ : 1 / 2 ≤ ξ) (hξ' : ξ ≤ 2) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ M N₀ N K D₀ : ℕ,
      0 < M → 0 < N → N ≤ N₀ → 0 < D₀ → 0 < K → K ≤ M →
      2 * (2 * (N₀ : ℝ)) ^ 2 * (((M : ℝ) * N₀) ^ η) ≤ (M : ℝ) * ((K : ℝ) + 1) →
      ∀ T : ℝ, 0 ≤ T → QuadraticRoughBound M (2 * N / D₀) K T →
        QuadraticRoughBound M N K
          ((Nat.log 2 N + 1 : ℕ) *
            (C * ((M : ℝ) * N₀) ^ (36 * η) * (D₀ : ℝ) ^ 5 *
              quadraticDescentScale ξ M N₀ K + C * (2 * (N₀ : ℝ)) ^ η * T)) := by
  obtain ⟨A, hA, ha⟩ := quadratic_small_gcd_sum_growth h hξ hξ' hη
  obtain ⟨B, hB, hb⟩ := quadratic_rough_gcd_descent_epsilon η hη
  let C := A + B + 6
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro M N₀ N K D₀ hM hN hNN hD₀ hK hKM hcut T hT hshort v
  let F := ((M : ℝ) * N₀) ^ (36 * η) * (D₀ : ℝ) ^ 5 *
    quadraticDescentScale ξ M N₀ K
  let U := C * F + C * (2 * (N₀ : ℝ)) ^ η * T
  have hNN₀ : 0 < N₀ := lt_of_lt_of_le hN hNN
  have hX : 1 ≤ (M : ℝ) * N₀ := one_le_mul_of_one_le_of_one_le
    (by exact_mod_cast hM) (by exact_mod_cast hNN₀)
  have hD₁ : (1 : ℝ) ≤ D₀ := by exact_mod_cast hD₀
  have hFp : 0 ≤ F := mul_nonneg (by positivity) (quadraticDescentScale_nonneg _ _ _ _)
  have hCF : A * F ≤ C * F := mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) hFp
  have hFM : (M : ℝ) * D₀ ≤ F := by
    have hp : 1 ≤ ((M : ℝ) * N₀) ^ (36 * η) := Real.one_le_rpow hX (by positivity)
    have hD : (D₀ : ℝ) ≤ (D₀ : ℝ) ^ 5 := le_self_pow₀ hD₁ (by norm_num)
    have hV : (M : ℝ) ≤ quadraticDescentScale ξ M N₀ K := by
      unfold quadraticDescentScale
      have : 0 ≤ Real.sqrt M * (K : ℝ) ^ (ξ - 1 / 2) := by positivity
      have : 0 ≤ Real.sqrt M * N₀ / Real.sqrt K := by positivity
      linarith [Nat.cast_nonneg (α := ℝ) N₀]
    calc
      _ = 1 * (D₀ : ℝ) * M := by ring
      _ ≤ ((M : ℝ) * N₀) ^ (36 * η) * (D₀ : ℝ) ^ 5 *
          quadraticDescentScale ξ M N₀ K := by gcongr
      _ = F := rfl
  have hblock (j : ℕ) (hj : j ∈ Finset.range (Nat.log 2 N + 1)) :
      quadraticRoughEnergy M (2 * 2 ^ j) K (quadraticDyadicCoeff N j v) ≤
        U * quadraticSieveEnergy (2 * 2 ^ j) (quadraticDyadicCoeff N j v) := by
    let R := 2 ^ j
    let w := quadraticDyadicCoeff N j v
    have hR : 0 < R := by dsimp [R]; positivity
    have hRN : R ≤ N := (Nat.pow_le_pow_right (by norm_num : 0 < 2)
      (by have := Finset.mem_range.mp hj; omega)).trans (Nat.pow_log_le_self 2 (by omega))
    have hRN₀ := hRN.trans hNN
    have hE : 0 ≤ quadraticSieveEnergy (2 * R) w := Finset.sum_nonneg fun _ _ => sq_nonneg _
    by_cases hsmall : R ≤ D₀
    · apply (quadratic_rough_bound_trivial M (2 * R) K w).trans
      apply mul_le_mul_of_nonneg_right _ hE
      simp only [Nat.cast_mul, Nat.cast_ofNat]
      have hRreal : (R : ℝ) ≤ D₀ := by exact_mod_cast hsmall
      have hm : 3 * (M : ℝ) * (2 * R) ≤ 6 * F := by nlinarith [Nat.cast_nonneg (α := ℝ) M]
      have h6 : 6 * F ≤ C * F := mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) hFp
      exact (hm.trans h6).trans (le_add_of_nonneg_right (by dsimp [C]; positivity))
    · have hshortR : QuadraticRoughBound M (2 * R / D₀) K T :=
        hshort.mono_second (Nat.div_le_div_right (Nat.mul_le_mul_left 2 hRN))
      have hsum := ha M N₀ R K D₀ hM hR hRN₀ hD₀ (lt_of_not_ge hsmall) hK hKM
        hcut w (fun n hn => quadraticDyadicCoeff_below N j v hn)
      have hdesc := hb M (2 * R) K D₀ hD₀ T hT hshortR w
      have hpow : (2 * (R : ℝ)) ^ η ≤ (2 * (N₀ : ℝ)) ^ η := by
        apply Real.rpow_le_rpow (by positivity) _ hη.le
        exact mul_le_mul_of_nonneg_left (by exact_mod_cast hRN₀) (by norm_num)
      have htail : B * ((2 * R : ℕ) : ℝ) ^ η * T ≤ C * (2 * (N₀ : ℝ)) ^ η * T := by
        simp only [Nat.cast_mul, Nat.cast_ofNat]
        gcongr
        dsimp [C]
        linarith
      have hsum' : (∑ D ∈ (Finset.Icc 1 (2 * R)).filter (fun D => D ≤ D₀),
          ‖quadraticRoughGcdMoment M (2 * R) K D w‖) ≤
          A * F * quadraticSieveEnergy (2 * R) w := by
        convert hsum using 1
        all_goals try with_reducible_and_instances rfl
        dsimp [F]
        ring
      have hs := mul_le_mul_of_nonneg_right hCF hE
      have ht := mul_le_mul_of_nonneg_right htail hE
      dsimp only [U]
      nlinarith only [hdesc, hsum', hs, ht]
  apply (quadratic_rough_energy_dyadic M N K v).trans
  calc
    _ ≤ (Nat.log 2 N + 1 : ℕ) * ∑ j ∈ Finset.range (Nat.log 2 N + 1),
        U * quadraticSieveEnergy (2 * 2 ^ j) (quadraticDyadicCoeff N j v) := by
      apply mul_le_mul_of_nonneg_left (Finset.sum_le_sum hblock) (Nat.cast_nonneg _)
    _ = (Nat.log 2 N + 1 : ℕ) * U * quadraticSieveEnergy N v := by
      rw [← Finset.mul_sum, quadratic_dyadic_coeff_energy_sum]
      ring
    _ = _ := by dsimp [U, F]; ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticFiniteDescent
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The finite length of the actual coefficient descent -/

namespace Ostmann

open scoped Classical BigOperators

theorem quadraticDescentBudget_nonneg {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (r : ℕ) :
    0 ≤ quadraticDescentBudget A B r := by
  induction r with
  | zero => rfl
  | succ r ih => exact add_nonneg hA (mul_nonneg hB ih)

theorem quadraticDescentBudget_bound {A B : ℝ} (hA : 0 ≤ A) (hB : 1 ≤ B) (r : ℕ) :
    quadraticDescentBudget A B r ≤ (r : ℝ) * B ^ r * A := by
  induction r with
  | zero => simp [quadraticDescentBudget]
  | succ r ih =>
    have hBA : A ≤ B ^ (r + 1) * A := le_mul_of_one_le_left hA (one_le_pow₀ hB)
    calc
      _ ≤ A + B * ((r : ℝ) * B ^ r * A) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left ih (le_trans zero_le_one hB))
      _ ≤ B ^ (r + 1) * A + B * ((r : ℝ) * B ^ r * A) := add_le_add hBA le_rfl
      _ = _ := by rw [pow_succ, Nat.cast_add, Nat.cast_one]; ring

theorem quadratic_rough_zero (M K : ℕ) (T : ℝ) : QuadraticRoughBound M 0 K T := by
  intro v
  simp [quadraticRoughEnergy, quadraticTransposeSum, quadraticSieveEnergy, oddSquarefreeRange]

theorem quadratic_quotient_descent_cutoff {D n r : ℕ} (hD : 0 < D)
    (h : 2 ^ (r + 1) * n < D ^ (r + 1)) :
    2 ^ r * (2 * n / D) < D ^ r := by
  have hdiv : (2 * n / D) * D ≤ 2 * n := Nat.div_mul_le_self _ _
  have hmul := Nat.mul_le_mul_left (2 ^ r) hdiv
  have hstrict : (2 ^ r * (2 * n / D)) * D < D ^ r * D := by
    calc
      _ ≤ 2 ^ r * (2 * n) := by simpa only [mul_assoc] using hmul
      _ < D ^ r * D := by simpa only [pow_succ, mul_assoc] using h
  exact (Nat.mul_lt_mul_right hD).mp hstrict

/-- Iterate the concrete `n ↦ 2*n/D` descent. The power condition proves that
the last coefficient range is empty; no limiting or supremum argument occurs. -/
theorem quadratic_rough_finite_descent {M N₀ K D : ℕ} {A B : ℝ}
    (hD : 2 ≤ D) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hstep : ∀ n : ℕ, 0 < n → n ≤ N₀ → ∀ T : ℝ, 0 ≤ T →
      QuadraticRoughBound M (2 * n / D) K T → QuadraticRoughBound M n K (A + B * T))
    (r n : ℕ) (hn : n ≤ N₀) (hcut : 2 ^ r * n < D ^ r) :
    QuadraticRoughBound M n K (quadraticDescentBudget A B r) := by
  induction r generalizing n with
  | zero =>
    have : n = 0 := by simpa using hcut
    subst n
    exact quadratic_rough_zero M K _
  | succ r ih =>
    by_cases hn₀ : n = 0
    · subst n
      exact quadratic_rough_zero M K _
    have hsmall : 2 * n / D ≤ n := by
      calc
        _ ≤ 2 * n / 2 := Nat.div_le_div_left hD (by norm_num)
        _ = n := by omega
    have hnext := ih (2 * n / D) (hsmall.trans hn) (quadratic_quotient_descent_cutoff (by omega) hcut)
    exact hstep n (Nat.pos_of_ne_zero hn₀) hn _ (quadraticDescentBudget_nonneg hA hB r) hnext

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticRoughIteration
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Iterating the actual rough-moment estimate with uniform constants -/

namespace Ostmann

open scoped Classical BigOperators

theorem quadratic_rough_iteration {ξ η : ℝ} (h : QuadraticSieveGrowth ξ)
    (hξ : 1 / 2 ≤ ξ) (hξ' : ξ ≤ 2) (hη : 0 < η) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ M N K D r : ℕ,
      0 < M → 0 < N → 2 ≤ D → 0 < K → K ≤ M →
      2 ^ r * N < D ^ r →
      2 * (2 * (N : ℝ)) ^ 2 * (((M : ℝ) * N) ^ η) ≤ (M : ℝ) * ((K : ℝ) + 1) →
      QuadraticRoughBound M N K
        ((r : ℝ) * (C * (Nat.log 2 N + 1 : ℕ) * (2 * (N : ℝ)) ^ η) ^ r *
          (C * (Nat.log 2 N + 1 : ℕ) * ((M : ℝ) * N) ^ (36 * η) *
            (D : ℝ) ^ 5 * quadraticDescentScale ξ M N K)) := by
  obtain ⟨C₀, hC₀, hc⟩ := quadratic_rough_descent h hξ hξ' hη
  let C := C₀ + 1
  refine ⟨C, by dsimp [C]; linarith, ?_⟩
  intro M N K D r hM hN hD hK hKM hpow hcut
  let L : ℝ := (Nat.log 2 N + 1 : ℕ)
  let F := ((M : ℝ) * N) ^ (36 * η) * (D : ℝ) ^ 5 * quadraticDescentScale ξ M N K
  let A := C * L * F
  let B := C * L * (2 * (N : ℝ)) ^ η
  have hC : 0 < C := by dsimp [C]; linarith
  have hL : 1 ≤ L := by
    dsimp [L]
    exact_mod_cast Nat.le_add_left 1 (Nat.log 2 N)
  have hF : 0 ≤ F := mul_nonneg (by positivity) (quadraticDescentScale_nonneg _ _ _ _)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 1 ≤ B := by
    apply one_le_mul_of_one_le_of_one_le
    · exact one_le_mul_of_one_le_of_one_le (by dsimp [C]; linarith) hL
    · apply Real.one_le_rpow _ hη.le
      have : (1 : ℝ) ≤ N := by exact_mod_cast hN
      linarith
  have hstep (n : ℕ) (hn : 0 < n) (hnN : n ≤ N) (T : ℝ) (hT : 0 ≤ T)
      (hshort : QuadraticRoughBound M (2 * n / D) K T) :
      QuadraticRoughBound M n K (A + B * T) := by
    apply (hc M N n K D hM hn hnN (by omega) hK hKM hcut T hT hshort).mono_constant
    have hl : ((Nat.log 2 n + 1 : ℕ) : ℝ) ≤ L := by
      dsimp [L]
      exact_mod_cast Nat.add_le_add_right (Nat.log_mono_right (b := 2) hnN) 1
    have hcn : C₀ ≤ C := by dsimp [C]; linarith
    calc
      _ = ((Nat.log 2 n + 1 : ℕ) : ℝ) * (C₀ * F + C₀ * (2 * (N : ℝ)) ^ η * T) := by
        dsimp [F]; ring
      _ ≤ L * (C * F + C * (2 * (N : ℝ)) ^ η * T) := by gcongr
      _ = A + B * T := by dsimp [A, B]; ring
  apply (quadratic_rough_finite_descent hD hA (by linarith : 0 ≤ B)
    hstep r N le_rfl hpow).mono_constant
  convert quadraticDescentBudget_bound hA hB r using 1
  all_goals try with_reducible_and_instances rfl
  dsimp [A, B, F, L]
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticDescentCutoff
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A rounded cutoff that terminates the descent in a fixed number of steps -/

namespace Ostmann

theorem quadratic_descent_root_power {N r : ℕ} (hr : 0 < r) :
    ((N : ℝ) ^ (1 / (r : ℝ))) ^ r = N := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg N)]
  have hr₀ : (r : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hr
  rw [one_div_mul_cancel hr₀, Real.rpow_one]

theorem quadratic_descent_cutoff_bounds {N r : ℕ} (hN : 0 < N) (hr : 0 < r) :
    4 ≤ quadraticDescentCutoff N r ∧
      (quadraticDescentCutoff N r : ℝ) ≤ 5 * (N : ℝ) ^ (1 / (r : ℝ)) ∧
      2 ^ r * N < quadraticDescentCutoff N r ^ r := by
  let Y := (N : ℝ) ^ (1 / (r : ℝ))
  have hN₁ : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hY : 1 ≤ Y := Real.one_le_rpow hN₁ (by positivity)
  have hlo : 4 * Y ≤ (quadraticDescentCutoff N r : ℝ) := Nat.le_ceil _
  have hhi : (quadraticDescentCutoff N r : ℝ) < 4 * Y + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hD : (4 : ℝ) ≤ quadraticDescentCutoff N r := by linarith
  refine ⟨by exact_mod_cast hD, by linarith, ?_⟩
  have hstrict : 2 * Y < (quadraticDescentCutoff N r : ℝ) := by linarith
  have hp := pow_lt_pow_left₀ hstrict (by positivity : (0 : ℝ) ≤ 2 * Y) (Nat.ne_of_gt hr)
  rw [mul_pow, quadratic_descent_root_power hr] at hp
  exact_mod_cast hp

theorem quadratic_descent_cutoff_fifth {N r : ℕ} (hN : 0 < N) (hr : 0 < r) :
    (quadraticDescentCutoff N r : ℝ) ^ 5 ≤ 5 ^ 5 * (N : ℝ) ^ (5 / (r : ℝ)) := by
  have hb := (quadratic_descent_cutoff_bounds hN hr).2.1
  apply (pow_le_pow_left₀ (Nat.cast_nonneg _) hb 5).trans_eq
  rw [mul_pow]
  congr 1
  rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg N)]
  congr 1
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticIterationPowerCost
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The explicit small-power cost of a fixed number of descent steps -/

namespace Ostmann

theorem quadratic_iteration_power_cost {η C : ℝ} (hη : 0 < η) (hC : 0 < C)
    {M N r : ℕ} (hM : 0 < M) (hN : 0 < N) (hr : 0 < r) :
    (r : ℝ) * (C * (Nat.log 2 N + 1 : ℕ) * (2 * (N : ℝ)) ^ η) ^ r *
        (C * (Nat.log 2 N + 1 : ℕ) * ((M : ℝ) * N) ^ (36 * η) *
          (quadraticDescentCutoff N r : ℝ) ^ 5) ≤
      ((r : ℝ) * (C * (1 + (η * Real.log 2)⁻¹) * 2 ^ η) ^ r *
        (C * (1 + (η * Real.log 2)⁻¹) * 5 ^ 5)) *
        ((M : ℝ) * N) ^ ((2 * (r : ℝ) + 37) * η + 5 / (r : ℝ)) := by
  let X := (M : ℝ) * N
  let A := 1 + (η * Real.log 2)⁻¹
  have hX : 0 < X := by dsimp [X]; positivity
  have hA : 0 < A := by dsimp [A]; positivity
  have hNX : (N : ℝ) ≤ X := by
    have : (1 : ℝ) ≤ M := by exact_mod_cast hM
    dsimp [X]
    nlinarith [Nat.cast_nonneg (α := ℝ) N]
  have hp : (N : ℝ) ^ η ≤ X ^ η := Real.rpow_le_rpow (Nat.cast_nonneg _) hNX hη.le
  have hl : ((Nat.log 2 N + 1 : ℕ) : ℝ) ≤ A * X ^ η :=
    (quadratic_dyadic_count_bound η hη N hN).trans (mul_le_mul_of_nonneg_left hp hA.le)
  have htwo : (2 * (N : ℝ)) ^ η ≤ 2 ^ η * X ^ η := by
    rw [Real.mul_rpow (by norm_num) (Nat.cast_nonneg N)]
    exact mul_le_mul_of_nonneg_left hp (by positivity)
  have hroot : (quadraticDescentCutoff N r : ℝ) ^ 5 ≤ 5 ^ 5 * X ^ (5 / (r : ℝ)) :=
    (quadratic_descent_cutoff_fifth hN hr).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg _) hNX (by positivity)) (by positivity))
  have hfirst : C * (Nat.log 2 N + 1 : ℕ) * (2 * (N : ℝ)) ^ η ≤
      (C * A * 2 ^ η) * X ^ (2 * η) := by
    calc
      _ ≤ C * (A * X ^ η) * (2 ^ η * X ^ η) := by gcongr
      _ = _ := by
        rw [show 2 * η = η + η by ring, Real.rpow_add hX]
        ring
  have hsecond : C * (Nat.log 2 N + 1 : ℕ) * X ^ (36 * η) *
      (quadraticDescentCutoff N r : ℝ) ^ 5 ≤
      (C * A * 5 ^ 5) * X ^ (37 * η + 5 / (r : ℝ)) := by
    calc
      _ ≤ C * (A * X ^ η) * X ^ (36 * η) * (5 ^ 5 * X ^ (5 / (r : ℝ))) := by gcongr
      _ = _ := by
        rw [show 37 * η + 5 / (r : ℝ) = (η + 36 * η) + 5 / (r : ℝ) by ring,
          Real.rpow_add hX, Real.rpow_add hX]
        ring
  calc
    _ ≤ (r : ℝ) * ((C * A * 2 ^ η) * X ^ (2 * η)) ^ r *
        ((C * A * 5 ^ 5) * X ^ (37 * η + 5 / (r : ℝ))) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (by positivity) hfirst r) (Nat.cast_nonneg r)
      · exact hsecond
      · positivity
      · positivity
    _ = _ := by
      rw [mul_pow]
      rw [← Real.rpow_natCast (X ^ (2 * η)) r, ← Real.rpow_mul hX.le]
      have he : X ^ ((2 * (r : ℝ) + 37) * η + 5 / (r : ℝ)) =
          X ^ ((2 * η) * r) * X ^ (37 * η + 5 / (r : ℝ)) := by
        rw [← Real.rpow_add hX]
        congr 1
        ring
      change _ = ((r : ℝ) * (C * A * 2 ^ η) ^ r * (C * A * 5 ^ 5)) *
        X ^ ((2 * (r : ℝ) + 37) * η + 5 / (r : ℝ))
      rw [he]
      ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticRoughPowerGrowth
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # An arbitrarily small loss after the complete finite rough-moment descent -/

namespace Ostmann

theorem quadratic_rough_fixed_depth {ξ η : ℝ} (h : QuadraticSieveGrowth ξ)
    (hξ : 1 / 2 ≤ ξ) (hξ' : ξ ≤ 2) (hη : 0 < η) {r : ℕ} (hr : 0 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ M N K : ℕ,
      0 < M → 0 < N → 0 < K → K ≤ M →
      2 * (2 * (N : ℝ)) ^ 2 * (((M : ℝ) * N) ^ η) ≤ (M : ℝ) * ((K : ℝ) + 1) →
      QuadraticRoughBound M N K
        (C * ((M : ℝ) * N) ^ ((2 * (r : ℝ) + 37) * η + 5 / (r : ℝ)) *
          quadraticDescentScale ξ M N K) := by
  obtain ⟨B, hB, hb⟩ := quadratic_rough_iteration h hξ hξ' hη
  let A := 1 + (η * Real.log 2)⁻¹
  let C := (r : ℝ) * (B * A * 2 ^ η) ^ r * (B * A * 5 ^ 5)
  have hA : 0 < A := by dsimp [A]; positivity
  have hB₀ : 0 < B := lt_of_lt_of_le zero_lt_one hB
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro M N K hM hN hK hKM hcut
  obtain ⟨hD, _, hpow⟩ := quadratic_descent_cutoff_bounds hN hr
  apply (hb M N K (quadraticDescentCutoff N r) r hM hN (by omega) hK hKM hpow hcut).mono_constant
  have hp := mul_le_mul_of_nonneg_right (quadratic_iteration_power_cost hη hB₀ hM hN hr)
    (quadraticDescentScale_nonneg ξ M N K)
  convert hp using 1
  all_goals try with_reducible_and_instances rfl
  ring

theorem quadratic_rough_power_growth_oai {ξ : ℝ} (h : QuadraticSieveGrowth ξ)
    (hξ : 1 / 2 ≤ ξ) (hξ' : ξ ≤ 2) (ε : ℝ) (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ η ≤ ε ∧ ∃ C : ℝ, 0 < C ∧ ∀ M N K : ℕ,
      0 < M → 0 < N → 0 < K → K ≤ M →
      2 * (2 * (N : ℝ)) ^ 2 * (((M : ℝ) * N) ^ η) ≤ (M : ℝ) * ((K : ℝ) + 1) →
      QuadraticRoughBound M N K
        (C * ((M : ℝ) * N) ^ ε * quadraticDescentScale ξ M N K) := by
  obtain ⟨r, hr⟩ := exists_nat_gt (10 / ε)
  have hr₀ : (0 : ℝ) < r := lt_trans (by positivity : (0 : ℝ) < 10 / ε) hr
  have hrn : 0 < r := by exact_mod_cast hr₀
  let η := ε / (2 * (2 * (r : ℝ) + 37))
  have hη : 0 < η := by dsimp [η]; positivity
  have hcost : (2 * (r : ℝ) + 37) * η + 5 / (r : ℝ) ≤ ε := by
    have heq : (2 * (r : ℝ) + 37) * η = ε / 2 := by
      dsimp [η]
      field_simp
    have hrε : 10 < (r : ℝ) * ε := (div_lt_iff₀ hε).mp hr
    have hdiv : 5 / (r : ℝ) ≤ ε / 2 := (div_le_iff₀ hr₀).mpr (by nlinarith)
    linarith
  obtain ⟨C, hC, hc⟩ := quadratic_rough_fixed_depth h hξ hξ' hη hrn
  have hηε : η ≤ ε := by
    apply div_le_self hε.le
    nlinarith
  refine ⟨η, hη, hηε, C, hC, ?_⟩
  intro M N K hM hN hK hKM hcut
  apply (hc M N K hM hN hK hKM hcut).mono_constant
  have hX : 1 ≤ (M : ℝ) * N := one_le_mul_of_one_le_of_one_le
    (by exact_mod_cast hM) (by exact_mod_cast hN)
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hX hcost) hC.le)
    (quadraticDescentScale_nonneg ξ M N K)

end Ostmann

end OAI
end

theorem solution : type_of% @OAI.Ostmann.quadratic_rough_power_growth_oai := @OAI.Ostmann.quadratic_rough_power_growth_oai
