-- Prove2me | solution 1 for OAI.Ostmann.eventual_uniform_character_endpoint_contradiction
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T07:16:26.802329+00:00
-- url     : https://prove2.me/submissions/7ceb48af-e59d-4118-9812-31ae99109c44

import Mathlib
import Definitions.Def_OAIQ095D007
import Theorems.Thm_OAI_Ostmann_eventual_character_anchor_decay
import Theorems.Thm_OAI_Ostmann_eventual_character_atom_iteration
import Theorems.Thm_OAI_Ostmann_eventual_character_final_contradiction
import Theorems.Thm_OAI_Ostmann_eventual_selected_nonanchor_product_decay

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_ArithmeticErrorRates
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Absorbing the fixed-depth arithmetic comparison costs

The polynomial and spectator costs in Section 8 are dominated by the
double-exponential savings. The strict numerical gaps in the manuscript
therefore survive the finite history and equality-pattern sums.
-/

namespace Ostmann

open Filter Asymptotics

theorem arithmetic_exponent_absorption (a b d C c : ℝ) (n : ℕ)
    (hb : 0 < b) (hab : a < b) (hdb : d < b) (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop,
      C * L ^ n + C * L * Real.exp (a * L) - c * Real.exp (b * L) ≤
        -Real.exp (d * L) := by
  have hp := (isLittleO_pow_exp_pos_mul_atTop n hb).const_mul_left C
  have hm : (fun L : ℝ => C * (Real.exp (a * L) * L)) =o[atTop]
      (fun L => Real.exp (b * L)) := by
    simpa only [Real.rpow_one] using (isLittleO_exp_mul_rpow_of_lt 1 hab).const_mul_left C
  have he : (fun L : ℝ => Real.exp (d * L)) =o[atTop] (fun L => Real.exp (b * L)) := by
    simpa only [Real.rpow_zero, mul_one] using isLittleO_exp_mul_rpow_of_lt 0 hdb
  have h := ((hp.add hm).add he).bound hc
  filter_upwards [h] with L hL
  simp only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at hL
  have hle := (le_abs_self _).trans hL
  nlinarith

end Ostmann

end OAI
end

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

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_PrimitiveGaussFourier
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
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
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CRTFourier
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Chinese remainder factorization of the finite Fourier transform -/

namespace Ostmann

open scoped BigOperators

/-- Translation contributes its additive character with the negative Fourier sign. -/
theorem additiveFourier_translate {N : ℕ} [NeZero N]
    (f : ZMod N → ℂ) (t u : ZMod N) :
    additiveFourier (fun x => f (x - t)) u =
      ZMod.stdAddChar (-(t * u)) * additiveFourier f u := by
  rw [additiveFourier_apply, additiveFourier_apply]
  have hs := (Equiv.addRight t).bijective.sum_comp
    (fun x : ZMod N => f (x - t) * ZMod.stdAddChar (-(x * u)))
  rw [← hs]
  change (N : ℂ)⁻¹ * (∑ x : ZMod N, f ((x + t) - t) *
    ZMod.stdAddChar (-((x + t) * u))) = _
  simp only [add_sub_cancel_right]
  have he (x : ZMod N) : -((x + t) * u) = -(x * u) + -(t * u) := by ring
  simp_rw [he, AddChar.map_add_eq_mul]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_FinitePoissonTransform
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
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
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
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
-- module Solutions.OAIQ095_OS.Ostmann_Characters_TupleCRTFourier
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
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

theorem tupleCRTFunction_intCast {I : Type*} [Fintype I] (p : I → ℕ)
    (hc : Pairwise (fun i j => (p i).Coprime (p j)))
    (F : ∀ i, ZMod (p i) → ℂ) (n : ℤ) :
    tupleCRTFunction p hc F (n : ZMod (∏ i, p i)) = ∏ i, F i (n : ZMod (p i)) := by
  simp only [tupleCRTFunction, map_intCast, Pi.intCast_apply]

theorem tupleCRTFunction_fourier {I : Type*} [Fintype I] (p : I → ℕ)
    [∀ i, NeZero (p i)] [NeZero (∏ i, p i)]
    (hc : Pairwise (fun i j => (p i).Coprime (p j)))
    (F : ∀ i, ZMod (p i) → ℂ) (u : ZMod (∏ i, p i)) :
    additiveFourier (tupleCRTFunction p hc F) u = ∏ i,
      additiveFourier (F i)
        ((tupleCofactor p i : ZMod (p i))⁻¹ * ZMod.prodEquivPi p hc u i) := by
  have hphase (x : ZMod (∏ i, p i)) : ZMod.stdAddChar (-(x * u)) =
      ∏ i, ZMod.stdAddChar (-(ZMod.prodEquivPi p hc x i *
        ((tupleCofactor p i : ZMod (p i))⁻¹ * ZMod.prodEquivPi p hc u i))) := by
    rw [tuple_stdAddChar p hc]
    apply Finset.prod_congr rfl
    intro i _
    simp only [map_neg, map_mul, Pi.neg_apply, Pi.mul_apply]
    congr 1
    ring
  simp only [additiveFourier_apply, tupleCRTFunction, hphase]
  simp only [← Finset.prod_mul_distrib]
  have hs := (ZMod.prodEquivPi p hc).toEquiv.sum_comp (fun x : ∀ i, ZMod (p i) =>
    ∏ i, F i (x i) * ZMod.stdAddChar (-(x i *
      ((tupleCofactor p i : ZMod (p i))⁻¹ * ZMod.prodEquivPi p hc u i))))
  change (∑ x : ZMod (∏ i, p i), ∏ i, F i (ZMod.prodEquivPi p hc x i) *
    ZMod.stdAddChar (-(ZMod.prodEquivPi p hc x i *
      ((tupleCofactor p i : ZMod (p i))⁻¹ * ZMod.prodEquivPi p hc u i)))) = _ at hs
  rw [hs]
  rw [← Fintype.prod_sum (fun i (x : ZMod (p i)) => F i x *
    ZMod.stdAddChar (-(x * ((tupleCofactor p i : ZMod (p i))⁻¹ *
      ZMod.prodEquivPi p hc u i))))]
  simp only [Nat.cast_prod, Finset.prod_inv_distrib, Finset.prod_mul_distrib]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_TupleCharacterPoisson
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Poisson summation and the initial graph phase of a character tuple -/

namespace Ostmann

open scoped BigOperators FourierTransform SchwartzMap ComplexConjugate Classical

theorem primitiveGaussPhase_norm {p : ℕ} [NeZero p]
    (χ : DirichletCharacter ℂ p) (hχ : χ.IsPrimitive) :
    ‖primitiveGaussPhase χ‖ = 1 := by
  have hp : (0 : ℝ) < p := by exact_mod_cast NeZero.pos p
  have hg := primitive_gauss_norm_sq χ hχ
  have he : ‖gaussSum χ ZMod.stdAddChar‖ = Real.sqrt (p : ℝ) := by
    nlinarith [Real.sq_sqrt hp.le, Real.sqrt_nonneg (p : ℝ),
      norm_nonneg (gaussSum χ ZMod.stdAddChar)]
  rw [primitiveGaussPhase, norm_div, he, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), div_self (Real.sqrt_pos.mpr hp).ne']

theorem inverse_character_inverse_unit {p : ℕ} (χ : DirichletCharacter ℂ p)
    (x : ZMod p) (hx : IsUnit x) : χ⁻¹ x⁻¹ = χ x := by
  obtain ⟨u, rfl⟩ := hx
  have h := MulChar.inv_apply χ⁻¹ (u : ZMod p)
  rw [inv_inv, Ring.inverse_unit] at h
  simpa only [ZMod.inv_coe_unit] using h.symm

/-- Each off-diagonal edge has exponent one at level zero, including the
inverse characters assigned to conjugate slots. -/
theorem tuple_character_fourier {I : Type*} [Fintype I] (p : I → ℕ)
    [∀ i, NeZero (p i)] [NeZero (∏ i, p i)]
    (hc : Pairwise (fun i j => (p i).Coprime (p j)))
    (χ : ∀ i, DirichletCharacter ℂ (p i)) (hχ : ∀ i, (χ i).IsPrimitive)
    (t : ∀ i, ZMod (p i)) (v : ℤ) :
    additiveFourier (tupleCRTFunction p hc (fun i x => χ i (x - t i))) (-(v : ZMod (∏ i, p i))) =
      (Real.sqrt (∏ i, p i : ℕ) : ℂ)⁻¹ * tupleGraphPhase p χ t v := by
  rw [tupleCRTFunction_fourier]
  have hi (i : I) :
      additiveFourier (fun x => χ i (x - t i))
        ((tupleCofactor p i : ZMod (p i))⁻¹ *
          ZMod.prodEquivPi p hc (-(v : ZMod (∏ i, p i))) i) =
      (Real.sqrt (p i : ℝ) : ℂ)⁻¹ *
        (ZMod.stdAddChar (t i * ((tupleCofactor p i : ZMod (p i))⁻¹ * (v : ZMod (p i)))) *
          primitiveGaussPhase (χ i) * (χ i)⁻¹ (v : ZMod (p i)) *
            ∏ j ∈ Finset.univ.erase i, χ i (p j : ZMod (p i))) := by
    simp only [map_neg, map_intCast, Pi.neg_apply, Pi.intCast_apply, mul_neg]
    rw [additiveFourier_translate, primitive_character_fourier (χ i) (hχ i)]
    simp only [neg_neg, mul_neg]
    rw [map_mul ((χ i)⁻¹), inverse_character_inverse_unit (χ i) _
      ((ZMod.isUnit_iff_coprime _ _).mpr (tupleCofactor_coprime p hc i))]
    have he : χ i (tupleCofactor p i : ZMod (p i)) =
        ∏ j ∈ Finset.univ.erase i, χ i (p j : ZMod (p i)) := by
      simp only [tupleCofactor, Nat.cast_prod, map_prod]
    rw [he]
    have hs : (Real.sqrt (p i : ℝ) : ℂ) ^ 2 = p i := by
      exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg (p i))
    have hsp : (Real.sqrt (p i : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.mpr (show (0 : ℝ) < p i by exact_mod_cast NeZero.pos (p i))).ne'
    have hpC : (p i : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne (p i)
    unfold primitiveGaussPhase
    field_simp [hpC]
    rw [hs]
    ring
  simp_rw [hi]
  rw [Finset.prod_mul_distrib]
  have hs : (Real.sqrt (∏ i, p i : ℕ) : ℂ) = ∏ i, (Real.sqrt (p i : ℝ) : ℂ) := by
    rw [Nat.cast_prod, Real.sqrt_prod _ (fun i _ => Nat.cast_nonneg (p i)), Complex.ofReal_prod]
  rw [hs, Finset.prod_inv_distrib]
  rfl

theorem tuple_character_poisson {I : Type*} [Fintype I] (p : I → ℕ)
    [∀ i, NeZero (p i)] [NeZero (∏ i, p i)]
    (hc : Pairwise (fun i j => (p i).Coprime (p j)))
    (χ : ∀ i, DirichletCharacter ℂ (p i)) (hχ : ∀ i, (χ i).IsPrimitive)
    (t : ∀ i, ZMod (p i)) (ψ : 𝓢(ℝ, ℂ)) (X : ℝ) (hX : 0 < X) :
    (∑' n : ℤ, (∏ i, χ i ((n : ZMod (p i)) - t i)) * ψ ((n : ℝ) / X)) =
      ((X : ℂ) / (Real.sqrt (∏ i, p i : ℕ) : ℂ)) *
        ∑' v : ℤ, 𝓕 ψ ((v : ℝ) * X / (∏ i, p i : ℕ)) * tupleGraphPhase p χ t v := by
  have hp := scaled_periodic_poisson (tupleCRTFunction p hc (fun i x => χ i (x - t i))) ψ X hX
  simp_rw [tupleCRTFunction_intCast, tuple_character_fourier p hc χ hχ t] at hp
  rw [hp, ← tsum_mul_left, ← tsum_mul_left]
  apply tsum_congr
  intro v
  ring

theorem tupleGraphPhase_zero {I : Type*} [Fintype I] (p : I → ℕ)
    [∀ i, NeZero (p i)] (χ : ∀ i, DirichletCharacter ℂ (p i))
    (t : ∀ i, ZMod (p i)) (v : ℤ) (i : I) (hi : ¬IsUnit (v : ZMod (p i))) :
    tupleGraphPhase p χ t v = 0 := by
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  rw [((χ i)⁻¹).map_nonunit hi, mul_zero, zero_mul]

theorem tuple_character_poisson_normalized {I : Type*} [Fintype I] (p : I → ℕ)
    [∀ i, NeZero (p i)] [NeZero (∏ i, p i)]
    (hc : Pairwise (fun i j => (p i).Coprime (p j)))
    (χ : ∀ i, DirichletCharacter ℂ (p i)) (hχ : ∀ i, (χ i).IsPrimitive)
    (t : ∀ i, ZMod (p i)) (ψ : 𝓢(ℝ, ℂ)) (X : ℝ) (hX : 0 < X) :
    (∑' n : ℤ, (∏ i, χ i ((n : ZMod (p i)) - t i)) * ψ ((n : ℝ) / X)) /
        (Real.sqrt X : ℂ) =
      ∑' v : ℤ, (Real.sqrt (X / (∏ i, p i : ℕ)) : ℂ) *
        𝓕 ψ ((v : ℝ) * X / (∏ i, p i : ℕ)) * tupleGraphPhase p χ t v := by
  rw [tuple_character_poisson p hc χ hχ t ψ X hX, div_eq_mul_inv, mul_assoc, ← tsum_mul_right,
    ← tsum_mul_left]
  have hM : (0 : ℝ) < (∏ i, p i : ℕ) := by exact_mod_cast NeZero.pos (∏ i, p i)
  have hx : (Real.sqrt X : ℂ) ^ 2 = X := by exact_mod_cast Real.sq_sqrt hX.le
  have hx0 : (Real.sqrt X : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hX).ne'
  have hm0 : (Real.sqrt (∏ i, p i : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hM).ne'
  rw [Real.sqrt_div hX.le]
  push_cast
  apply tsum_congr
  intro v
  field_simp [hx0, hm0]
  rw [hx]
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_TransferArithmetic
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The arithmetic separation of diagonal and transferred terms -/

namespace Ostmann

theorem large_prime_factors_coprime_frequency (H : ℕ) (v : ℤ) (hv : v ≠ 0)
    (hlarge : ∀ q, q.Prime → q ∣ H → v.natAbs < q) : H.Coprime v.natAbs := by
  apply Nat.coprime_of_dvd
  intro q hq hqH hqv
  exact (not_le_of_gt (hlarge q hq hqH))
    (Nat.le_of_dvd (Int.natAbs_pos.mpr hv) hqv)

/-- The zero numerator has only the equal-product, equal-frequency
diagonal when prime factors exceed the frequencies. -/
theorem diagonal_products_equal (HL HR : ℕ) (hHL : 0 < HL) (v w : ℤ)
    (hv : v ≠ 0) (hw : w ≠ 0) (hrel : v * HR = w * HL)
    (hL : ∀ q, q.Prime → q ∣ HL → v.natAbs < q)
    (hR : ∀ q, q.Prime → q ∣ HR → w.natAbs < q) : HL = HR ∧ v = w := by
  have hvH := large_prime_factors_coprime_frequency HL v hv hL
  have hwH := large_prime_factors_coprime_frequency HR w hw hR
  have habs := congrArg Int.natAbs hrel
  simp only [Int.natAbs_mul, Int.natAbs_natCast] at habs
  have hdL : HL ∣ HR := hvH.dvd_of_dvd_mul_left (by
    rw [habs]
    exact dvd_mul_left HL w.natAbs)
  have hdR : HR ∣ HL := hwH.dvd_of_dvd_mul_left (by
    rw [← habs]
    exact dvd_mul_left HR v.natAbs)
  have heq : HL = HR := Nat.dvd_antisymm hdL hdR
  refine ⟨heq, ?_⟩
  rw [← heq] at hrel
  exact mul_right_cancel₀ (by exact_mod_cast (Nat.ne_of_gt hHL) : (HL : ℤ) ≠ 0) hrel

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_DirectedPrimePhase
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A common directed-graph phase for the initial and transferred amplitudes -/

namespace Ostmann

open scoped BigOperators Classical

private theorem initial_row_product {I : Type*} [Fintype I]
    (f : I → ℂ) (i : I) :
    (∏ j, f j ^ initialDirectedGraph i j) = ∏ j ∈ Finset.univ.erase i, f j := by
  have hi : f i ^ initialDirectedGraph i i = 1 := by simp [initialDirectedGraph]
  rw [← Finset.mul_prod_erase Finset.univ (fun j => f j ^ initialDirectedGraph i j)
    (Finset.mem_univ i), hi, one_mul]
  apply Finset.prod_congr rfl
  intro j hj
  simp only [initialDirectedGraph, (Finset.mem_erase.mp hj).1.symm, ite_false, if_false, zpow_one]

/-- The graph phase obtained by Poisson summation is the level-zero
specialization of the phase maintained through the transfers. -/
theorem tupleGraphPhase_eq_directed {I : Type*} [Fintype I] (p : I → ℕ)
    [∀ i, NeZero (p i)] (χ : ∀ i, DirichletCharacter ℂ (p i))
    (t : ∀ i, ZMod (p i)) (v : ℤ) :
    tupleGraphPhase p χ t v = directedPrimePhase p χ t
      (fun i => primitiveGaussPhase (χ i) * (χ i)⁻¹ (v : ZMod (p i))) initialDirectedGraph v := by
  unfold tupleGraphPhase directedPrimePhase
  apply Finset.prod_congr rfl
  intro i _
  rw [initial_row_product]
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_PermutedAdditiveCancellation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Common-center additive phases cancel under the actual matching -/

namespace Ostmann

open scoped BigOperators ComplexConjugate Classical

theorem tupleCofactor_equiv {I J : Type*} [Fintype I] [Fintype J]
    (e : I ≃ J) (p : J → ℕ) (hp : ∀ j, p j ≠ 0) (i : I) :
    tupleCofactor (fun i => p (e i)) i = tupleCofactor p (e i) := by
  apply mul_left_cancel₀ (hp (e i))
  calc
    _ = ∏ j, p (e j) := tupleCofactor_mul _ i
    _ = ∏ j, p j := e.prod_comp p
    _ = _ := (tupleCofactor_mul p (e i)).symm

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_FiniteProductPrior
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite independent priors used for the arithmetic samples -/

namespace Ostmann

open scoped BigOperators

theorem productPrior_nonneg {A : Type*} {n : ℕ}
    (μ : Fin n → A → ℝ) (hμ : ∀ i a, 0 ≤ μ i a) (x : Fin n → A) :
    0 ≤ productPrior μ x := Finset.prod_nonneg fun i _ => hμ i (x i)

theorem productPrior_mass {A : Type*} [Fintype A] {n : ℕ}
    (μ : Fin n → A → ℝ) (hμ : ∀ i, ∑ a, μ i a = 1) :
    (∑ x : Fin n → A, productPrior μ x) = 1 := by
  unfold productPrior
  rw [← Fintype.prod_sum]
  simp only [hμ, Finset.prod_const_one]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_PositiveWordBins
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Positive word means and a common product bin -/

namespace Ostmann

open scoped BigOperators Classical

/-- Every bin coefficient remains bounded by one under the original
probability law; restricting a bin does not renormalize that law. -/
theorem binnedWordAverage_norm_le_one {A B : Type*} [Fintype A] {n : ℕ}
    (μ : Fin n → A → ℝ) (F : Fin n → A → ℂ) (bin : (Fin n → A) → B) (b : B)
    (hμ : ∀ i a, 0 ≤ μ i a) (hmass : ∀ i, ∑ a, μ i a = 1)
    (hF : ∀ i a, ‖F i a‖ ≤ 1) : ‖binnedWordAverage μ F bin b‖ ≤ 1 := by
  unfold binnedWordAverage
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ x, productPrior μ x := by
      apply Finset.sum_le_sum
      intro x _
      have hx := productPrior_nonneg μ hμ x
      split_ifs
      · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx]
        apply mul_le_of_le_one_right hx
        rw [norm_prod]
        exact Finset.prod_le_one (fun i _ => norm_nonneg _) (fun i _ => hF i (x i))
      · simpa using hx
    _ = 1 := productPrior_mass μ hmass

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_HarmonicWordPriors
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Harmonic laws for all word roles on one common prime sample space -/

namespace Ostmann

open scoped BigOperators Classical

theorem primeSubsetPrior_nonneg (P Q : Finset ℕ) (p : P) :
    0 ≤ primeSubsetPrior P Q p := by
  unfold primeSubsetPrior
  split_ifs
  · exact div_nonneg (by positivity) (Finset.sum_nonneg (fun _ _ => by positivity))
  · exact le_rfl

theorem primeSubsetPrior_support (P Q : Finset ℕ) (p : P)
    (hp : primeSubsetPrior P Q p ≠ 0) : (p : ℕ) ∈ Q := by
  by_contra hn
  simp [primeSubsetPrior, hn] at hp

theorem primeSubsetPrior_mass (P Q : Finset ℕ) (hQP : Q ⊆ P)
    (hm : (∑ q ∈ Q, (q : ℝ)⁻¹) ≠ 0) : (∑ p : P, primeSubsetPrior P Q p) = 1 := by
  unfold primeSubsetPrior
  rw [Finset.sum_coe_sort P (fun p => if p ∈ Q then
    (p : ℝ)⁻¹ / (∑ q ∈ Q, (q : ℝ)⁻¹) else 0), ← Finset.sum_filter]
  have hf : P.filter (fun p => p ∈ Q) = Q := by
    ext p
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hQP h, h⟩⟩
  rw [hf, ← Finset.sum_div]
  exact div_self hm

theorem primeSubsetPrior_atom (P Q : Finset ℕ) (p : P) :
    primeSubsetPrior P Q p ≤ (∑ q ∈ Q, (q : ℝ)⁻¹)⁻¹ * (p : ℝ)⁻¹ := by
  unfold primeSubsetPrior
  split_ifs
  · exact le_of_eq (by ring)
  · positivity

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_NormalizedFourierProfile
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bounds for the actual normalized level-zero Fourier profile -/

namespace Ostmann

open scoped SchwartzMap

/-- Normalizing by X exactly recovers the original Fourier factor, before
its separate bounded support cutoff is applied. -/
theorem normalizedFourierProfile_original (ψ : ℝ → ℂ) (X M v : ℝ)
    (hX : X ≠ 0) (hM : M ≠ 0) :
    normalizedFourierProfile ψ v (M / X) = archimedeanLeafFactor X M v 1 ψ := by
  have hi : (M / X)⁻¹ = X / M := by field_simp
  have ha : -v * (M / X)⁻¹ = -v * X / M := by rw [hi]; ring
  have hs : (Real.sqrt (M / X))⁻¹ = Real.sqrt (X / M) := by rw [← Real.sqrt_inv, hi]
  simp only [normalizedFourierProfile, archimedeanLeafFactor, mul_one, hs, ha]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_PivotSquareExpansion
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The grouped square has the actual transfer divisibility condition -/

namespace Ostmann

open scoped BigOperators ComplexConjugate Classical

theorem pivot_zero_numerator_iff (L R : ℕ) (hLpos : 0 < L) (v w : ℤ)
    (hv : v ≠ 0) (hw : w ≠ 0)
    (hL : ∀ q, q.Prime → q ∣ L → v.natAbs < q)
    (hR : ∀ q, q.Prime → q ∣ R → w.natAbs < q) :
    v * R - w * L = 0 ↔ L = R ∧ v = w := by
  constructor
  · intro h
    exact diagonal_products_equal L R hLpos v w hv hw (sub_eq_zero.mp h) hL hR
  · rintro ⟨rfl, rfl⟩
    simp

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_TransferredPivotSubstitution
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Eliminating the extended integer by its exact signed quotient -/

namespace Ostmann

open scoped BigOperators ComplexConjugate Classical

theorem reconstructedPivot_of_eq (N s : ℤ) (hs : s ≠ 0) (M : ℕ)
    (h : N = s * M) : reconstructedPivot N s = M := by
  rw [reconstructedPivot, Int.ediv_eq_of_eq_mul_right hs h, Int.toNat_natCast]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_RecursiveTransferWeight
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The recursive weight with its actual reconstructed integer pivots -/

namespace Ostmann

open scoped BigOperators Classical

theorem ValidTransferNode.historyPivot_eq {State : Type*} {sys : TransferHistorySystem State}
    {σ : State} {s v w : ℤ} {P : ℕ} (h : ValidTransferNode sys σ s v w P) :
    historyPivot sys σ s v w = P :=
  reconstructedPivot_of_eq _ _ h.root_ne_zero P h.relation

/-- No witness choices enter the recursive weight: the integer equation
forces the pivot at every valid node. -/
theorem recursiveTransferWeight_node {State : Type*} (sys : TransferHistorySystem State)
    (leaf : State → ℤ → ℂ) (cutoff : State → ℤ → ℤ → ℤ → ℝ)
    (n : ℕ) (σ : State) (t : FrequencyTree ℤ (n + 1)) (P : ℕ)
    (hP : ValidTransferNode sys σ t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) P) :
    recursiveTransferWeight sys leaf cutoff (n + 1) σ t =
      (cutoff σ t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) : ℂ) *
        recursiveTransferWeight sys leaf cutoff n (sys.leftState σ P) t.2.1 *
        star (recursiveTransferWeight sys leaf cutoff n (sys.rightState σ P) t.2.2) := by
  simp only [recursiveTransferWeight, hP.historyPivot_eq, hP, ite_true, if_true]

theorem recursiveTransferWeight_nonzero_valid {State : Type*} (sys : TransferHistorySystem State)
    (leaf : State → ℤ → ℂ) (cutoff : State → ℤ → ℤ → ℤ → ℝ)
    (n : ℕ) (σ : State) (t : FrequencyTree ℤ n)
    (ht : recursiveTransferWeight sys leaf cutoff n σ t ≠ 0) :
    ValidTransferHistory sys n σ t := by
  induction n generalizing σ with
  | zero => trivial
  | succ n ih =>
    let P := historyPivot sys σ t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2)
    by_cases hP : ValidTransferNode sys σ t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) P
    · rw [recursiveTransferWeight_node sys leaf cutoff n σ t P hP] at ht
      have hl : recursiveTransferWeight sys leaf cutoff n (sys.leftState σ P) t.2.1 ≠ 0 := by
        intro hz
        simp only [hz, mul_zero, zero_mul, ne_eq, not_true_eq_false] at ht
      have hr : recursiveTransferWeight sys leaf cutoff n (sys.rightState σ P) t.2.2 ≠ 0 := by
        intro hz
        simp only [hz, star_zero, mul_zero, ne_eq, not_true_eq_false] at ht
      exact ⟨P, hP, ih _ _ hl, ih _ _ hr⟩
    · exact False.elim (ht (by simp only [recursiveTransferWeight, P, hP, ite_false, if_false]))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_WordTransferFullPeriod
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The full small-frequency modulus, including every node's unit tests -/

namespace Ostmann

open scoped Classical

theorem frequencyRoot_mem_allFrequencyList (n : ℕ) (t : FrequencyTree ℤ n) :
    frequencyRoot n t ∈ allFrequencyList n t := by
  cases n <;> simp [allFrequencyList, frequencyRoot]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_DirectedPhaseReindex
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact reindexing of the directed phase and its cofactors -/

namespace Ostmann

open scoped BigOperators Classical

theorem directedPrimePhase_equiv {I J : Type*} [Fintype I] [Fintype J]
    (e : I ≃ J) (p : J → ℕ) [∀ j, NeZero (p j)]
    (χ : ∀ j, DirichletCharacter ℂ (p j)) (t : ∀ j, ZMod (p j))
    (ν : J → ℂ) (b : J → J → ℤ) (v : ℤ) :
    directedPrimePhase (fun i => p (e i)) (fun i => χ (e i)) (fun i => t (e i))
        (fun i => ν (e i)) (fun i j => b (e i) (e j)) v =
      directedPrimePhase p χ t ν b v := by
  unfold directedPrimePhase
  rw [← e.prod_comp (fun j => ZMod.stdAddChar
    (t j * ((tupleCofactor p j : ZMod (p j))⁻¹ * (v : ZMod (p j)))) *
      ν j * ∏ k, χ j (p k : ZMod (p j)) ^ b j k)]
  apply Finset.prod_congr rfl
  intro i _
  rw [tupleCofactor_equiv e p (fun j => NeZero.ne (p j)) i]
  dsimp only
  rw [e.prod_comp (fun j => χ (e i) (p j : ZMod (p (e i))) ^ b (e i) j)]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduledTemplateBounds
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Word-size bounds for the constructed copied-atom template -/

namespace Ostmann

open scoped Classical

theorem copyScheduleVertex_card {I : Type*} [Fintype I] (n : ℕ) :
    Fintype.card (CopyScheduleVertex I n) = 3 ^ n * Fintype.card I := by
  induction n with
  | zero =>
    simp only [pow_zero, one_mul]
    exact Fintype.card_congr (Equiv.refl I)
  | succ n ih =>
    change Fintype.card ((Bool × CopyScheduleVertex I n) ⊕ CopyScheduleVertex I n) = _
    rw [Fintype.card_sum, Fintype.card_prod, Fintype.card_bool, ih, pow_succ]
    ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ConstituentWords
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact constituent words of the surviving grouped atoms -/

namespace Ostmann

open scoped BigOperators Classical

theorem scheduleConstituentWord_prod {I : Type*} (role : I → CopyScheduleRole)
    (size : I → ℕ) (n : ℕ) (v : CopyScheduleAtoms role n)
    (q : SurvivingConstituent role size n → ℕ) :
    ((scheduleConstituentWord role size n v).map q).prod =
      ∏ k : Fin (size (copyScheduleOrigin n v.val)), q ((survivingConstituentEquiv role size n).symm ⟨v, k⟩) := by
  rw [scheduleConstituentWord, List.map_ofFn, List.prod_ofFn]
  rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_DyadicPrimeRange
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Concrete dyadic covers of the prime ranges used by the prior comparison -/

namespace Ostmann

/-- Even a doubly exponential prime endpoint needs only exponentially
many dyadic blocks. The constant is explicit and independent of the tree. -/
theorem dyadic_prime_range_count (B : ℕ) (C L : ℝ) (hC : 0 ≤ C) (hL : 1 ≤ L)
    (hB : (B : ℝ) ≤ Real.exp (Real.exp (C * L))) :
    ((Nat.log 2 B + 1 : ℕ) : ℝ) ≤
      Real.exp ((C + Real.log ((Real.log 2)⁻¹ + 1)) * L) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogB : Real.log B ≤ Real.exp (C * L) := by
    by_cases hB0 : B = 0
    · subst B
      simp only [Nat.cast_zero, Real.log_zero]
      exact (Real.exp_pos _).le
    · exact (Real.log_le_iff_le_exp (by exact_mod_cast Nat.pos_of_ne_zero hB0)).mpr hB
  have hnat : (Nat.log 2 B : ℝ) ≤ Real.log B / Real.log 2 := by
    simpa only [Real.logb, Nat.cast_ofNat] using Real.natLog_le_logb B 2
  have hexp1 : 1 ≤ Real.exp (C * L) := Real.one_le_exp (mul_nonneg hC (by linarith))
  have hconstant : 1 ≤ (Real.log 2)⁻¹ + 1 := by linarith [inv_pos.mpr hlog2]
  have hconstantpos : 0 < (Real.log 2)⁻¹ + 1 := lt_of_lt_of_le (by norm_num) hconstant
  have hlogconst : 0 ≤ Real.log ((Real.log 2)⁻¹ + 1) := Real.log_nonneg hconstant
  calc
    _ ≤ Real.log B / Real.log 2 + 1 := by push_cast; linarith
    _ ≤ Real.exp (C * L) / Real.log 2 + 1 := by gcongr
    _ ≤ ((Real.log 2)⁻¹ + 1) * Real.exp (C * L) := by
      rw [div_eq_mul_inv]
      nlinarith
    _ = Real.exp (Real.log ((Real.log 2)⁻¹ + 1) + C * L) := by
      rw [Real.exp_add, Real.exp_log hconstantpos]
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      nlinarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_TotalAtomUnits
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual unit condition on every current atom at every frequency -/

namespace Ostmann

open scoped BigOperators Classical

/-- A unit product is exactly the original assertion that every current
atom is a unit. The dummy interval endpoints play no part in this test. -/
theorem totalAtomUnitRanges_iff {I : Type*} [Fintype I] (role : I → CopyScheduleRole)
    (n : ℕ) (x : CopyScheduleAtoms role n → ℕ) (s : ℤ) :
    (∀ r ∈ totalAtomUnitRanges role n, ((r.atoms.map x).prod).Coprime s.natAbs) ↔
      ∀ i, (x i).Coprime s.natAbs := by
  simp only [totalAtomUnitRanges, List.mem_singleton, forall_eq]
  rw [Finset.prod_map_toList]
  exact Nat.coprime_fintype_prod_left_iff

theorem copyScheduleAtoms_card_le {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (n : ℕ) :
    Fintype.card (CopyScheduleAtoms role n) ≤ 3 ^ n * Fintype.card I := by
  rw [← copyScheduleVertex_card n]
  exact Fintype.card_subtype_le _

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SchedulePairwiseReplay
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The reduced support implies every original pairwise-coprimality gate -/

namespace Ostmann

open scoped BigOperators Classical

theorem scheduleAtomUnitsValid_root {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (childBound pivotBound : ℕ → ℕ)
    (n : ℕ) (x : CopyScheduleAtoms role n → ℕ) (t : FrequencyTree ℤ n)
    (hu : scheduleAtomUnitsValid role childBound pivotBound (totalAtomUnitRanges role) n x t) :
    ∀ i, (x i).Coprime (frequencyRoot n t).natAbs := by
  cases n with
  | zero => exact (totalAtomUnitRanges_iff role 0 x t).mp hu
  | succ n => exact (totalAtomUnitRanges_iff role (n + 1) x t.1).mp hu.1

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduleFullCoprime
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Recovering the complete large-coprimality support from the reduced tests -/

namespace Ostmann

open scoped BigOperators Classical

theorem schedule_full_coprime_reduced {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (childBound pivotBound : ℕ → ℕ)
    (n : ℕ) (x : CopyScheduleAtoms role n → ℕ) (t : FrequencyTree ℤ n)
    (h : scheduleAtomFullCoprimeValid role childBound pivotBound n x t) :
    Pairwise (fun i j => (x i).Coprime (x j)) ∧
      scheduleAtomCoprimalitiesValid role childBound pivotBound n x t := by
  induction n with
  | zero => exact ⟨h, trivial⟩
  | succ n ih =>
    exact ⟨h.1, (fun i => (h.2.1 _).symm), (ih _ _ h.2.2.1).2,
      (ih _ _ h.2.2.2).2⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_FullAtomTransferWeight
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The complete grouped weight as a single supported recursive weight -/

namespace Ostmann

open scoped BigOperators Classical ComplexConjugate SchwartzMap FourierTransform

theorem fullAtomWeightGuard_node {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (childBound pivotBound : ℕ → ℕ)
    (ranges : (j : ℕ) → List (ScheduleAtomRange role j)) (n : ℕ)
    (x : CopyScheduleAtoms role (n + 1) → ℕ) (t : FrequencyTree ℤ (n + 1)) (P : ℕ)
    (hP : ValidTransferNode (scheduleAtomSystem role childBound pivotBound) ⟨n + 1, x⟩
      t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) P) :
    fullAtomWeightGuard role childBound pivotBound ranges (n + 1) x t ↔
      fullAtomRootGuard role ranges n x P t.1 ∧
      fullAtomWeightGuard role childBound pivotBound ranges n (reverseCopyLabelMap role n true P x) t.2.1 ∧
      fullAtomWeightGuard role childBound pivotBound ranges n (reverseCopyLabelMap role n false P x) t.2.2 := by
  simp only [fullAtomWeightGuard, scheduleAtomFullCoprimeValid, scheduleAtomUnitsValid,
    scheduleAtomRangesValid, hP.historyPivot_eq, totalAtomUnitRanges_iff, fullAtomRootGuard]
  tauto

private theorem guarded_product (A B C : Prop) [Decidable A] [Decidable B] [Decidable C] (x y : ℂ) :
    (if A ∧ B ∧ C then x * conj y else 0) =
      if A then (if B then x else 0) * conj (if C then y else 0) else 0 := by
  by_cases hA : A <;> by_cases hB : B <;> by_cases hC : C <;> simp [hA, hB, hC]

/-- The full weight has exactly the inherited left/right factors, with all
new top tests in the root guard. There is no loss of boundary or unit tests. -/
theorem fullAtomTransferWeight_node {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (childBound pivotBound : ℕ → ℕ)
    (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (leaf : ScheduleAtomState role → ℤ → ℂ) (n : ℕ)
    (x : CopyScheduleAtoms role (n + 1) → ℕ) (t : FrequencyTree ℤ (n + 1)) (P : ℕ)
    (hP : ValidTransferNode (scheduleAtomSystem role childBound pivotBound) ⟨n + 1, x⟩
      t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) P) :
    fullAtomTransferWeight role childBound pivotBound ranges leaf (n + 1) x t =
      if fullAtomRootGuard role ranges n x P t.1 then
        fullAtomTransferWeight role childBound pivotBound ranges leaf n
          (reverseCopyLabelMap role n true P x) t.2.1 *
        conj (fullAtomTransferWeight role childBound pivotBound ranges leaf n
          (reverseCopyLabelMap role n false P x) t.2.2) else 0 := by
  simp only [fullAtomTransferWeight,
    fullAtomWeightGuard_node role childBound pivotBound ranges n x t P hP,
    recursiveTransferWeight_node _ leaf _ n ⟨n + 1, x⟩ t P hP,
    Complex.ofReal_one, one_mul]
  exact guarded_product _ _ _ _ _

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InsertedAtomAssignment
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Inserting the reconstructed composite pivot in either old branch -/

namespace Ostmann

open scoped Classical

theorem scheduledInsertedAtoms_H {I : Type*} (role : I → CopyScheduleRole)
    (n : ℕ) (P : ℕ) (l : CopyScheduleH role n → ℕ) (u : CopyScheduleY role n → ℕ)
    (h : CopyScheduleH role n) :
    scheduledInsertedAtoms role n P l u ⟨h.val, h.property.1⟩ = l h := by
  change scheduledInsertedAtoms role n P l u (scheduledPartitionEquiv role n (.inr (.inl h))) = _
  simp only [scheduledInsertedAtoms, Equiv.symm_apply_apply]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ConstituentBlockProducts
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact products of all constituents in an H or Y block -/

namespace Ostmann

open scoped BigOperators Classical

theorem constituentH_product {I : Type*} [Fintype I] (role : I → CopyScheduleRole)
    (size : I → ℕ) (n : ℕ)
    (l : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → ℕ) :
    (∏ h : CopyScheduleH role n, ∏ k, l (constituentH role size n h k)) = ∏ h, l h := by
  rw [← Fintype.prod_sigma (fun z : Σ h : CopyScheduleH role n, Fin (size (copyScheduleOrigin n h.val)) =>
    l (constituentH role size n z.1 z.2))]
  exact (constituentHEquiv role size n).prod_comp l

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_FullAtomWeightSupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Support and square-energy bounds for the actual full atom weight -/

namespace Ostmann

open scoped BigOperators Classical

theorem fullAtomTransferWeight_support {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (childBound pivotBound : ℕ → ℕ)
    (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (leaf : ScheduleAtomState role → ℤ → ℂ) (n : ℕ)
    (x : CopyScheduleAtoms role n → ℕ) (t : FrequencyTree ℤ n)
    (h : fullAtomTransferWeight role childBound pivotBound ranges leaf n x t ≠ 0) :
    fullAtomWeightGuard role childBound pivotBound ranges n x t ∧
    ValidTransferHistory (scheduleAtomSystem role childBound pivotBound) n ⟨n, x⟩ t := by
  unfold fullAtomTransferWeight at h
  split_ifs at h with hg
  · exact ⟨hg, recursiveTransferWeight_nonzero_valid _ _ _ _ _ _ h⟩
  · exact False.elim (h rfl)

theorem fullAtomTransferWeight_top_support {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (childBound pivotBound : ℕ → ℕ)
    (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (leaf : ScheduleAtomState role → ℤ → ℂ) (n : ℕ)
    (x : CopyScheduleAtoms role n → ℕ) (t : FrequencyTree ℤ n)
    (h : fullAtomTransferWeight role childBound pivotBound ranges leaf n x t ≠ 0) :
    Pairwise (fun i j => (x i).Coprime (x j)) ∧
      (∀ i, (x i).Coprime (frequencyRoot n t).natAbs) := by
  have hg := (fullAtomTransferWeight_support role childBound pivotBound ranges leaf n x t h).1
  exact ⟨(schedule_full_coprime_reduced role childBound pivotBound n x t hg.1).1,
    scheduleAtomUnitsValid_root role childBound pivotBound n x t hg.2.1⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_FullAtomRangeSupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original pivot interval remains present in full coefficient support -/

namespace Ostmann

open scoped Classical

theorem fullAtomTransferWeight_top_range {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (childBound pivotBound : ℕ → ℕ)
    (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (leaf : ScheduleAtomState role → ℤ → ℂ) (n : ℕ)
    (x : CopyScheduleAtoms role n → ℕ) (t : FrequencyTree ℤ n)
    (hw : fullAtomTransferWeight role childBound pivotBound ranges leaf n x t ≠ 0)
    (r : ScheduleAtomRange role n) (hr : r ∈ ranges n) : r.Holds x := by
  have hg := (fullAtomTransferWeight_support role childBound pivotBound ranges leaf n x t hw).1.2.2
  cases n with
  | zero => exact hg r hr
  | succ n => exact hg.1 r hr

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_AtomIntervalRanges
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Concrete inherited intervals for every original atom role -/

namespace Ostmann

open scoped Classical

theorem atomInterval_holds_iff {I : Type*} (role : I → CopyScheduleRole)
    (lo hi : I → ℕ) (n : ℕ) (v : CopyScheduleAtoms role n) (x : CopyScheduleAtoms role n → ℕ) :
    (atomInterval role lo hi n v).Holds x ↔
      lo (copyScheduleOrigin n v.val) ≤ x v ∧ x v ≤ hi (copyScheduleOrigin n v.val) := by
  simp only [atomInterval, ScheduleAtomRange.Holds, List.map_singleton, List.prod_singleton,
    Set.mem_Icc, Nat.cast_le]

theorem atomIntervalRanges_holds_iff {I : Type*} [Fintype I] (role : I → CopyScheduleRole)
    (lo hi : I → ℕ) (n : ℕ) (x : CopyScheduleAtoms role n → ℕ) :
    (∀ r ∈ atomIntervalRanges role lo hi n, r.Holds x) ↔
      ∀ v, lo (copyScheduleOrigin n v.val) ≤ x v ∧ x v ≤ hi (copyScheduleOrigin n v.val) := by
  constructor
  · intro h v
    apply (atomInterval_holds_iff role lo hi n v x).mp
    apply h
    exact List.mem_map.mpr ⟨v, Finset.mem_toList.mpr (Finset.mem_univ v), rfl⟩
  · intro h r hr
    obtain ⟨v, _, rfl⟩ := List.mem_map.mp hr
    exact (atomInterval_holds_iff role lo hi n v x).mpr (h v)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_AtomIntervalComplexity
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original interval guards have bounded complexity at every finite depth -/
namespace Ostmann
open scoped Classical

theorem atomIntervalRanges_singleton {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (lo hi : I → ℕ) (n : ℕ)
    (r : ScheduleAtomRange role n) (hr : r ∈ atomIntervalRanges role lo hi n) :
    r.atoms.length = 1 := by
  obtain ⟨v, _, rfl⟩ := List.mem_map.mp hr
  rfl

theorem atomIntervalRanges_length_le {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (lo hi : I → ℕ) (k n : ℕ) (hn : n ≤ k) :
    (atomIntervalRanges role lo hi n).length ≤ 3 ^ k * Fintype.card I := by
  have he : (atomIntervalRanges role lo hi n).length = Fintype.card (CopyScheduleAtoms role n) := by
    simp only [atomIntervalRanges, List.length_map, Finset.length_toList, Finset.card_univ]
  rw [he]
  exact (copyScheduleAtoms_card_le role n).trans
    (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega : 1 ≤ 3) hn))

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

/-- A nonprincipal character has zero additive Fourier coefficient at zero. -/
theorem additiveFourier_mulChar_zero {p : ℕ} [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (hχ : χ ≠ 1) : additiveFourier χ 0 = 0 := by
  simp [additiveFourier_apply, χ.sum_eq_zero_of_ne_one hχ]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_RepeatedCharacterCancellation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A singleton prime makes a short-period repeated tuple vanish -/

namespace Ostmann

open scoped BigOperators FourierTransform SchwartzMap Classical

theorem periodic_poisson_complete_mean {N : ℕ} [NeZero N]
    (F : ZMod N → ℂ) (ψ : 𝓢(ℝ, ℂ)) (X H : ℝ) (hX : 0 < X)
    (hH : H < X / N) (hsupp : ∀ x : ℝ, H < |x| → 𝓕 ψ x = 0) :
    (∑' n : ℤ, F (n : ZMod N) * ψ ((n : ℝ) / X)) =
      (X : ℂ) * 𝓕 ψ 0 * additiveFourier F 0 := by
  rw [scaled_periodic_poisson F ψ X hX]
  have hn (n : ℤ) (hne : n ≠ 0) :
      𝓕 ψ ((n : ℝ) * X / N) * additiveFourier F (-(n : ZMod N)) = 0 := by
    have habs : (1 : ℝ) ≤ |(n : ℝ)| := by
      exact_mod_cast (show (1 : ℤ) ≤ |n| by have hh := abs_pos.mpr hne; omega)
    have hN : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
    have hlarge : H < |(n : ℝ) * X / N| := by
      rw [abs_div, abs_mul, abs_of_pos hX, abs_of_pos hN, div_eq_mul_inv, mul_assoc]
      exact hH.trans_le (by
        simpa only [div_eq_mul_inv, one_mul] using
          mul_le_mul_of_nonneg_right habs (mul_nonneg hX.le (inv_nonneg.mpr hN.le)))
    rw [hsupp _ hlarge, zero_mul]
  rw [tsum_eq_single 0 hn]
  simp only [Int.cast_zero, zero_mul, zero_div, neg_zero]
  ring

theorem groupedSlotValue_product {I : Type*} [Fintype I] (P : Finset ℕ)
    (p : I → P) (χ : I → ∀ q : ℕ, DirichletCharacter ℂ q)
    (t : ∀ q : ℕ, ZMod q) (n : ℤ) :
    (∏ q : P, groupedSlotValue P p χ t q (n : ZMod (q : ℕ))) =
      ∏ i, χ i (p i) ((n : ZMod (p i : ℕ)) - t (p i)) := by
  unfold groupedSlotValue
  have he (q : P) :
      (∏ i ∈ Finset.univ.filter (fun i => p i = q), χ i q ((n : ZMod (q : ℕ)) - t q)) =
        ∏ i ∈ Finset.univ.filter (fun i => p i = q),
          χ i (p i) ((n : ZMod (p i : ℕ)) - t (p i)) := by
    apply Finset.prod_congr rfl
    intro i hi
    rw [(Finset.mem_filter.mp hi).2]
  simp_rw [he]
  exact Finset.prod_fiberwise Finset.univ p _

theorem groupedSlotValue_singleton {I : Type*} [Fintype I] (P : Finset ℕ)
    (p : I → P) (χ : I → ∀ q : ℕ, DirichletCharacter ℂ q)
    (t : ∀ q : ℕ, ZMod q) (i : I) (hi : ∀ j, p j = p i → j = i) :
    groupedSlotValue P p χ t (p i) = fun x => χ i (p i) (x - t (p i)) := by
  have hf : Finset.univ.filter (fun j => p j = p i) = {i} := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ⟨hi j, fun h => by rw [h]⟩
  funext x
  simp only [groupedSlotValue, hf, Finset.prod_singleton]

theorem grouped_singleton_fourier_zero {I : Type*} [Fintype I] (P : Finset ℕ)
    (hP : ∀ q ∈ P, q.Prime) (p : I → P)
    (χ : I → ∀ q : ℕ, DirichletCharacter ℂ q) (t : ∀ q : ℕ, ZMod q)
    (i : I) (hi : ∀ j, p j = p i → j = i) (hχ : χ i (p i) ≠ 1) :
    let q : P → ℕ := fun q => q
    let : ∀ q : P, NeZero (q : ℕ) := fun q => ⟨(hP q q.property).ne_zero⟩
    let : NeZero (∏ q : P, (q : ℕ)) := ⟨(Finset.prod_pos (s := Finset.univ) (f := fun q : P => (q : ℕ)) (fun q _ => (hP q q.property).pos)).ne'⟩
    let hc : Pairwise (fun a b : P => (a : ℕ).Coprime (b : ℕ)) :=
      fun a b hab => (Nat.coprime_primes (hP a a.property) (hP b b.property)).mpr
        (fun h => hab (Subtype.ext h))
    additiveFourier (tupleCRTFunction q hc (groupedSlotValue P p χ t)) 0 = 0 := by
  intro q _ _ hc
  rw [tupleCRTFunction_fourier]
  apply Finset.prod_eq_zero (Finset.mem_univ (p i))
  simp only [map_zero, Pi.zero_apply, mul_zero, groupedSlotValue_singleton P p χ t i hi]
  let : Fact (p i : ℕ).Prime := ⟨hP (p i) (p i).property⟩
  rw [additiveFourier_translate, mul_zero, neg_zero, AddChar.map_zero_eq_one, one_mul]
  exact additiveFourier_mulChar_zero (χ i (p i)) hχ

/-- Once the repeated tuple's actual period is below the Fourier cutoff,
one singly occurring nonprincipal character annihilates its entire sum. -/
theorem grouped_singleton_poisson_zero {I : Type*} [Fintype I] (P : Finset ℕ)
    (hP : ∀ q ∈ P, q.Prime) (p : I → P)
    (χ : I → ∀ q : ℕ, DirichletCharacter ℂ q) (t : ∀ q : ℕ, ZMod q)
    (i : I) (hi : ∀ j, p j = p i → j = i) (hχ : χ i (p i) ≠ 1)
    (ψ : 𝓢(ℝ, ℂ)) (X H : ℝ) (hX : 0 < X)
    (hperiod : H < X / (∏ q : P, (q : ℕ)))
    (hsupp : ∀ x : ℝ, H < |x| → 𝓕 ψ x = 0) :
    (∑' n : ℤ, (∏ j, χ j (p j) ((n : ZMod (p j : ℕ)) - t (p j))) *
      ψ ((n : ℝ) / X)) = 0 := by
  let q : P → ℕ := fun q => q
  let : ∀ q : P, NeZero (q : ℕ) := fun q => ⟨(hP q q.property).ne_zero⟩
  let : NeZero (∏ q : P, (q : ℕ)) :=
    ⟨(Finset.prod_pos (s := Finset.univ) (f := fun q : P => (q : ℕ))
      (fun q _ => (hP q q.property).pos)).ne'⟩
  have hc : Pairwise (fun a b : P => (a : ℕ).Coprime (b : ℕ)) :=
    fun a b hab => (Nat.coprime_primes (hP a a.property) (hP b b.property)).mpr
      (fun h => hab (Subtype.ext h))
  have hz : additiveFourier (tupleCRTFunction q hc (groupedSlotValue P p χ t)) 0 = 0 :=
    grouped_singleton_fourier_zero P hP p χ t i hi hχ
  have hs := periodic_poisson_complete_mean (tupleCRTFunction q hc (groupedSlotValue P p χ t))
    ψ X H hX hperiod hsupp
  simp_rw [tupleCRTFunction_intCast, groupedSlotValue_product] at hs
  rw [hs, hz, mul_zero]

theorem bounded_complete_mean_norm {N : ℕ} [NeZero N]
    (F : ZMod N → ℂ) (hF : ∀ x, ‖F x‖ ≤ 1) : ‖additiveFourier F 0‖ ≤ 1 := by
  have hsum : ‖∑ x, F x‖ ≤ (N : ℝ) := by
    apply (norm_sum_le _ _).trans
    calc
      (∑ x : ZMod N, ‖F x‖) ≤ ∑ _x : ZMod N, (1 : ℝ) :=
        Finset.sum_le_sum (fun x _ => hF x)
      _ = N := by simp
  rw [additiveFourier_apply]
  simp only [mul_zero, neg_zero, AddChar.map_zero_eq_one, mul_one, norm_mul,
    norm_inv, Complex.norm_natCast]
  calc
    (N : ℝ)⁻¹ * ‖∑ x, F x‖ ≤ (N : ℝ)⁻¹ * N :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = 1 := inv_mul_cancel₀ (by exact_mod_cast NeZero.ne N)

theorem short_period_character_sum_bound {N : ℕ} [NeZero N]
    (F : ZMod N → ℂ) (hF : ∀ x, ‖F x‖ ≤ 1)
    (ψ : 𝓢(ℝ, ℂ)) (X H : ℝ) (hX : 0 < X)
    (hperiod : H < X / N) (hsupp : ∀ x : ℝ, H < |x| → 𝓕 ψ x = 0) :
    ‖∑' n : ℤ, F (n : ZMod N) * ψ ((n : ℝ) / X)‖ ≤ X * ‖𝓕 ψ 0‖ := by
  rw [periodic_poisson_complete_mean F ψ X H hX hperiod hsupp, norm_mul, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hX]
  exact mul_le_of_le_one_right (by positivity) (bounded_complete_mean_norm F hF)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_RepeatedPrimePeriod
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Formal products and the smaller period of a repeated prime tuple -/

namespace Ostmann

open scoped BigOperators Classical

theorem primeSlotCount_pos {I : Type*} [Fintype I] (p : I → ℕ) {q : ℕ}
    (hq : q ∈ sampledPrimeSet p) : 0 < primeSlotCount p q := by
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hq
  exact Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩

theorem formal_prime_product {I : Type*} [Fintype I] (p : I → ℕ) :
    (∏ i, p i) = ∏ q ∈ sampledPrimeSet p, q ^ primeSlotCount p q := by
  simpa only [primeSlotCount, Finset.prod_const] using
    (Finset.prod_fiberwise_of_maps_to' (s := Finset.univ) (t := sampledPrimeSet p)
      (g := p) (fun i hi => Finset.mem_image.mpr ⟨i, hi, rfl⟩) (fun q => q)).symm

/-- A repeated label removes at least that prime from the formal period.
This is the period saving used before bandlimited Poisson summation. -/
theorem repeated_prime_period_bound {I : Type*} [Fintype I] (p : I → ℕ)
    (hp : ∀ i, 1 ≤ p i) {q : ℕ} (hq : q ∈ sampledPrimeSet p)
    (hm : 2 ≤ primeSlotCount p q) :
    q * (∏ r ∈ sampledPrimeSet p, r) ≤ ∏ i, p i := by
  have hr1 (r : ℕ) (hr : r ∈ sampledPrimeSet p) : 1 ≤ r := by
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hr
    exact hp i
  have hbase (r : ℕ) (hr : r ∈ (sampledPrimeSet p).erase q) :
      r ≤ r ^ primeSlotCount p r := by
    simpa only [pow_one] using Nat.pow_le_pow_right (hr1 r (Finset.mem_of_mem_erase hr))
      (primeSlotCount_pos p (Finset.mem_of_mem_erase hr))
  rw [formal_prime_product, ← Finset.mul_prod_erase (sampledPrimeSet p) (fun r => r) hq,
    ← Finset.mul_prod_erase (sampledPrimeSet p) (fun r => r ^ primeSlotCount p r) hq]
  calc
    q * (q * ∏ r ∈ (sampledPrimeSet p).erase q, r) =
        q ^ 2 * ∏ r ∈ (sampledPrimeSet p).erase q, r := by ring
    _ ≤ q ^ primeSlotCount p q * ∏ r ∈ (sampledPrimeSet p).erase q, r ^ primeSlotCount p r :=
      Nat.mul_le_mul (Nat.pow_le_pow_right (hr1 q hq) hm) (Finset.prod_le_prod' hbase)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_RepeatedTuplePoisson
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original product bounds imply the short-period cancellation -/

namespace Ostmann

open scoped BigOperators FourierTransform SchwartzMap Classical

theorem repeated_tuple_short_period {I : Type*} [Fintype I]
    (p : I → ℕ) (hp : ∀ i, (p i).Prime) (X H R : ℝ) (hR : 0 < R)
    (hsmall : ∀ i, H * R < p i) (hprod : (∏ i, (p i : ℝ)) ≤ X * R)
    (i j : I) (hij : i ≠ j) (heq : p i = p j) :
    H < X / (∏ r ∈ sampledPrimeSet p, r : ℕ) := by
  let P := sampledPrimeSet p
  have hP : ∀ q ∈ P, q.Prime := by
    intro q hq
    obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp hq
    exact hp l
  have hmem (l : I) : p l ∈ P := Finset.mem_image.mpr ⟨l, Finset.mem_univ l, rfl⟩
  have hcount : 2 ≤ primeSlotCount p (p i) := by
    have hh : ({i, j} : Finset I) ⊆ Finset.univ.filter (fun l => p l = p i) := by
      intro l hl
      simp only [Finset.mem_insert, Finset.mem_singleton] at hl
      rcases hl with rfl | rfl
      · simp
      · simp [heq]
    have hc := Finset.card_le_card hh
    simpa only [Finset.card_pair hij, primeSlotCount] using hc
  have hperiod : (p i) * (∏ r ∈ P, r) ≤ ∏ l, p l :=
    repeated_prime_period_bound p (fun l => (hp l).one_lt.le) (hmem i) hcount
  have hpos : (0 : ℝ) < (∏ r ∈ P, r : ℕ) := by
    exact_mod_cast Finset.prod_pos (fun r hr => (hP r hr).pos)
  have hupper : (p i : ℝ) * (∏ r ∈ P, r : ℕ) ≤ X * R := by
    have hh : (p i : ℝ) * (∏ r ∈ P, r : ℕ) ≤ (∏ l, p l : ℕ) := by exact_mod_cast hperiod
    exact hh.trans (by simpa only [Nat.cast_prod] using hprod)
  have hshort : H < X / (∏ r ∈ P, r : ℕ) := by
    rw [lt_div_iff₀ hpos]
    have hh := mul_lt_mul_of_pos_right (hsmall i) hpos
    have hr : (H * (∏ r ∈ P, r : ℕ)) * R < X * R := by nlinarith
    exact (mul_lt_mul_iff_left₀ hR).mp hr
  exact hshort

theorem repeated_tuple_singleton_zero {I : Type*} [Fintype I]
    (p : I → ℕ) (hp : ∀ i, (p i).Prime)
    (χ : I → ∀ q : ℕ, DirichletCharacter ℂ q) (t : ∀ q : ℕ, ZMod q)
    (ψ : 𝓢(ℝ, ℂ)) (X H R : ℝ) (hX : 0 < X) (hR : 0 < R)
    (hsupp : ∀ x : ℝ, H < |x| → 𝓕 ψ x = 0)
    (hsmall : ∀ i, H * R < p i) (hprod : (∏ i, (p i : ℝ)) ≤ X * R)
    (i j : I) (hij : i ≠ j) (heq : p i = p j)
    (k : I) (hk : ∀ l, p l = p k → l = k) (hχ : χ k (p k) ≠ 1) :
    characterTupleSum p χ t ψ X = 0 := by
  let P := sampledPrimeSet p
  have hP : ∀ q ∈ P, q.Prime := by
    intro q hq
    obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp hq
    exact hp l
  have hmem (l : I) : p l ∈ P := Finset.mem_image.mpr ⟨l, Finset.mem_univ l, rfl⟩
  let q : I → P := fun l => ⟨p l, hmem l⟩
  have hshort := repeated_tuple_short_period p hp X H R hR hsmall hprod i j hij heq
  have hshort' : H < X / (∏ r : P, (r : ℕ)) := by
    have he : (∏ r : P, (r : ℕ)) = ∏ r ∈ P, r := Finset.prod_coe_sort P (fun r : ℕ => r)
    rw [he]
    exact hshort
  exact grouped_singleton_poisson_zero P hP q χ t k
    (fun l h => hk l (congrArg Subtype.val h)) hχ ψ X H hX hshort' hsupp

theorem repeated_tuple_sum_bound {I : Type*} [Fintype I]
    (p : I → ℕ) (hp : ∀ i, (p i).Prime)
    (χ : I → ∀ q : ℕ, DirichletCharacter ℂ q) (t : ∀ q : ℕ, ZMod q)
    (ψ : 𝓢(ℝ, ℂ)) (X H R : ℝ) (hX : 0 < X) (hR : 0 < R)
    (hsupp : ∀ x : ℝ, H < |x| → 𝓕 ψ x = 0)
    (hsmall : ∀ i, H * R < p i) (hprod : (∏ i, (p i : ℝ)) ≤ X * R)
    (i j : I) (hij : i ≠ j) (heq : p i = p j) :
    ‖characterTupleSum p χ t ψ X‖ ≤ X * ‖𝓕 ψ 0‖ := by
  let P := sampledPrimeSet p
  have hP : ∀ q ∈ P, q.Prime := by
    intro q hq
    obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp hq
    exact hp l
  have hmem (l : I) : p l ∈ P := Finset.mem_image.mpr ⟨l, Finset.mem_univ l, rfl⟩
  let q : I → P := fun l => ⟨p l, hmem l⟩
  let v : P → ℕ := fun r => r
  let : ∀ r : P, NeZero (r : ℕ) := fun r => ⟨(hP r r.property).ne_zero⟩
  let : NeZero (∏ r : P, (r : ℕ)) :=
    ⟨(Finset.prod_pos (s := Finset.univ) (f := fun r : P => (r : ℕ))
      (fun r _ => (hP r r.property).pos)).ne'⟩
  have hc : Pairwise (fun a b : P => (a : ℕ).Coprime (b : ℕ)) :=
    fun a b hab => (Nat.coprime_primes (hP a a.property) (hP b b.property)).mpr
      (fun h => hab (Subtype.ext h))
  let F := tupleCRTFunction v hc (groupedSlotValue P q χ t)
  have hF (a : ZMod (∏ r : P, (r : ℕ))) : ‖F a‖ ≤ 1 := by
    dsimp [F, tupleCRTFunction, groupedSlotValue]
    rw [norm_prod]
    apply Finset.prod_le_one (fun r _ => norm_nonneg _)
    intro r _
    rw [norm_prod]
    exact Finset.prod_le_one (fun l _ => norm_nonneg _) (fun l _ => (χ l r).norm_le_one _)
  have hshort : H < X / (∏ r : P, (r : ℕ)) := by
    have hs := repeated_tuple_short_period p hp X H R hR hsmall hprod i j hij heq
    have he : (∏ r : P, (r : ℕ)) = ∏ r ∈ P, r := Finset.prod_coe_sort P (fun r : ℕ => r)
    rw [he]
    exact hs
  have hb := short_period_character_sum_bound F hF ψ X H hX hshort hsupp
  simpa only [F, tupleCRTFunction_intCast, groupedSlotValue_product, characterTupleSum] using hb

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_TupleFrequencyCutoff
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual finite frequency support of the initial tuple amplitude -/

namespace Ostmann

open scoped BigOperators FourierTransform SchwartzMap Classical

private theorem tupleGraphPhase_zero_at_zero {I : Type*} [Fintype I] [Nonempty I]
    (p : I → ℕ) [∀ i, NeZero (p i)] (hp : ∀ i, 2 ≤ p i)
    (χ : ∀ i, DirichletCharacter ℂ (p i)) (t : ∀ i, ZMod (p i)) :
    tupleGraphPhase p χ t 0 = 0 := by
  obtain ⟨i⟩ := ‹Nonempty I›
  have hp1 : p i ≠ 1 := by have h := hp i; omega
  let : Nontrivial (ZMod (p i)) := ZMod.nontrivial_iff.mpr hp1
  exact tupleGraphPhase_zero p χ t 0 i (by simp)

private theorem fourier_zero_beyond_tuple_cutoff {I : Type*} [Fintype I]
    (p : I → ℕ) [NeZero (∏ i, p i)] (ψ : 𝓢(ℝ, ℂ))
    (X H : ℝ) (hX : 0 < X) (N : ℕ) (hcut : H * (∏ i, p i : ℕ) ≤ N * X)
    (hsupp : ∀ x : ℝ, H < |x| → 𝓕 ψ x = 0) (v : ℤ)
    (hv : v ∉ Finset.Icc (-(N : ℤ)) (N : ℤ)) :
    𝓕 ψ ((v : ℝ) * X / (∏ i, p i : ℕ)) = 0 := by
  have hn : (N : ℝ) < |(v : ℝ)| := by
    have hi : (N : ℤ) < |v| := by
      simp only [Finset.mem_Icc, not_and_or, not_le] at hv
      rcases hv with hv | hv
      · exact (show (N : ℤ) < -v by omega).trans_le (neg_le_abs v)
      · exact hv.trans_le (le_abs_self v)
    exact_mod_cast hi
  have hM : (0 : ℝ) < (∏ i, p i : ℕ) := by exact_mod_cast NeZero.pos (∏ i, p i)
  apply hsupp
  rw [abs_div, abs_mul, abs_of_pos hX, abs_of_pos hM, lt_div_iff₀ hM]
  exact hcut.trans_lt (mul_lt_mul_of_pos_right hn hX)

private theorem tupleFrequencyTerm_zero {I : Type*} [Fintype I] [Nonempty I]
    (p : I → ℕ) [∀ i, NeZero (p i)] [NeZero (∏ i, p i)]
    (hp : ∀ i, 2 ≤ p i) (χ : ∀ i, DirichletCharacter ℂ (p i))
    (t : ∀ i, ZMod (p i)) (ψ : 𝓢(ℝ, ℂ)) (X H : ℝ) (hX : 0 < X)
    (N : ℕ) (hcut : H * (∏ i, p i : ℕ) ≤ N * X)
    (hsupp : ∀ x : ℝ, H < |x| → 𝓕 ψ x = 0) (v : ℤ)
    (hv : v ∉ tupleFrequencies p N) :
    (Real.sqrt (X / (∏ i, p i : ℕ)) : ℂ) *
      𝓕 ψ ((v : ℝ) * X / (∏ i, p i : ℕ)) * tupleGraphPhase p χ t v = 0 := by
  simp only [tupleFrequencies, Finset.mem_filter] at hv
  by_cases hr : v ∈ Finset.Icc (-(N : ℤ)) (N : ℤ)
  · by_cases hz : v = 0
    · subst v
      rw [tupleGraphPhase_zero_at_zero p hp χ t, mul_zero]
    · have hunit : ¬∀ i, IsUnit (v : ZMod (p i)) := fun hu => hv ⟨hr, hz, hu⟩
      obtain ⟨i, hi⟩ := not_forall.mp hunit
      rw [tupleGraphPhase_zero p χ t v i hi, mul_zero]
  · rw [fourier_zero_beyond_tuple_cutoff p ψ X H hX N hcut hsupp v hr,
      mul_zero, zero_mul]

theorem tuple_character_poisson_finite {I : Type*} [Fintype I] [Nonempty I]
    (p : I → ℕ) [∀ i, NeZero (p i)] [NeZero (∏ i, p i)]
    (hp : ∀ i, 2 ≤ p i) (hc : Pairwise (fun i j => (p i).Coprime (p j)))
    (χ : ∀ i, DirichletCharacter ℂ (p i)) (hχ : ∀ i, (χ i).IsPrimitive)
    (t : ∀ i, ZMod (p i)) (ψ : 𝓢(ℝ, ℂ)) (X H : ℝ) (hX : 0 < X)
    (N : ℕ) (hcut : H * (∏ i, p i : ℕ) ≤ N * X)
    (hsupp : ∀ x : ℝ, H < |x| → 𝓕 ψ x = 0) :
    (∑' n : ℤ, (∏ i, χ i ((n : ZMod (p i)) - t i)) * ψ ((n : ℝ) / X)) /
        (Real.sqrt X : ℂ) =
      ∑ v ∈ tupleFrequencies p N, (Real.sqrt (X / (∏ i, p i : ℕ)) : ℂ) *
        𝓕 ψ ((v : ℝ) * X / (∏ i, p i : ℕ)) * tupleGraphPhase p χ t v := by
  rw [tuple_character_poisson_normalized p hc χ hχ t ψ X hX]
  exact tsum_eq_sum (tupleFrequencyTerm_zero p hp χ t ψ X H hX N hcut hsupp)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_SampledTupleAmplitude
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The finite graph amplitude of an injective prime sample -/

namespace Ostmann

open scoped BigOperators FourierTransform SchwartzMap Classical

theorem prime_character_isPrimitive (p : ℕ) (hp : p.Prime)
    (χ : DirichletCharacter ℂ p) (hχ : χ ≠ 1) : χ.IsPrimitive := by
  let : NeZero p := ⟨hp.ne_zero⟩
  rcases (Nat.dvd_prime hp).mp χ.conductor_dvd_level with h | h
  · exact False.elim (hχ (DirichletCharacter.eq_one_iff_conductor_eq_one.mpr h))
  · exact h

theorem sampledTupleAmplitude_eq {I : Type*} [Fintype I] [Nonempty I]
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (χ : I → ∀ p : ℕ, DirichletCharacter ℂ p)
    (hχ : ∀ i p, p ∈ P → χ i p ≠ 1) (t : ∀ p : ℕ, ZMod p)
    (ψ : 𝓢(ℝ, ℂ)) (X H : ℝ) (hX : 0 < X) (N : ℕ)
    (hsupp : ∀ u : ℝ, H < |u| → 𝓕 ψ u = 0)
    (x : I → P) (hx : Function.Injective x)
    (hcut : H * (∏ i, (x i : ℕ)) ≤ N * X) :
    characterTupleSum (fun i => (x i : ℕ)) χ t ψ X / (Real.sqrt X : ℂ) =
      sampledTupleAmplitude P hP χ t ψ X N x := by
  let : ∀ i, NeZero (x i : ℕ) := fun i => ⟨(hP _ (x i).property).ne_zero⟩
  let : NeZero (∏ i, (x i : ℕ)) := ⟨Finset.prod_ne_zero_iff.mpr
    (fun i _ => (hP _ (x i).property).ne_zero)⟩
  have hc : Pairwise (fun i j => (x i : ℕ).Coprime (x j : ℕ)) := by
    intro i j hij
    apply (hP _ (x i).property).coprime_iff_not_dvd.mpr
    intro hd
    have he : (x i : ℕ) = (x j : ℕ) :=
      ((Nat.dvd_prime (hP _ (x j).property)).mp hd).resolve_left (hP _ (x i).property).ne_one
    exact hij (hx (Subtype.ext he))
  exact tuple_character_poisson_finite (fun i => (x i : ℕ))
    (fun i => (hP _ (x i).property).two_le) hc (fun i => χ i (x i))
    (fun i => prime_character_isPrimitive _ (hP _ (x i).property) _ (hχ i _ (x i).property))
    (fun i => t (x i)) ψ X H hX N hcut hsupp

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_FullWeightFrequencies
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Nonzero frequencies from the actual unit and modulus-window support -/

namespace Ostmann

open scoped BigOperators Classical ComplexConjugate SchwartzMap FourierTransform

theorem fullAtomTransferWeight_all_frequencies_ne_zero {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (childBound pivotBound : ℕ → ℕ)
    (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (leaf : ScheduleAtomState role → ℤ → ℂ)
    (hzero : ∀ x, fullAtomTransferWeight role childBound pivotBound ranges leaf 0 x (0 : ℤ) = 0)
    (n : ℕ) (x : CopyScheduleAtoms role n → ℕ) (t : FrequencyTree ℤ n)
    (hw : fullAtomTransferWeight role childBound pivotBound ranges leaf n x t ≠ 0) :
    ∀ s ∈ allFrequencyList n t, s ≠ 0 := by
  induction n with
  | zero =>
    intro s hs
    have he : s = t := by simpa only [allFrequencyList, List.mem_singleton] using hs
    subst s
    intro ht
    subst t
    exact hw (hzero x)
  | succ n ih =>
    obtain ⟨hg, P, hP, _, _⟩ := fullAtomTransferWeight_support role childBound pivotBound ranges leaf
      (n + 1) x t hw
    have hr := ((fullAtomWeightGuard_node role childBound pivotBound ranges n x t P hP).mp hg).1
    rw [fullAtomTransferWeight_node role childBound pivotBound ranges leaf n x t P hP,
      ite_eq_left hr] at hw
    obtain ⟨hL, hR⟩ := mul_ne_zero_iff.mp hw
    have hR' : fullAtomTransferWeight role childBound pivotBound ranges leaf n
        (reverseCopyLabelMap role n false P x) t.2.2 ≠ 0 := by
      intro hz
      exact hR (by rw [hz, map_zero])
    intro s hs
    rcases List.mem_cons.mp hs with he | hs
    · exact he ▸ hP.root_ne_zero
    · rcases List.mem_append.mp hs with hs | hs
      · exact ih _ t.2.1 hL s hs
      · exact ih _ t.2.2 hR' s hs

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ConstituentFrequencySupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Frequency units for the actual supported arithmetic coefficient -/

namespace Ostmann

open scoped BigOperators Classical

theorem constituentTransferWeight_full_ne_zero {I D : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (size : I → ℕ) (n : ℕ)
    (P : Finset ℕ) (Q : (Σ i, Fin (size i)) → Finset ℕ)
    (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (leaf : ScheduleAtomState role → ℤ → ℂ) (hist : D → FrequencyTree ℤ n)
    (u : CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n → P) (M : ℕ)
    (a : (CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → P) × D)
    (hw : constituentTransferWeight role size n P Q childBound pivotBound ranges leaf hist u M a ≠ 0) :
    fullAtomTransferWeight role childBound pivotBound ranges leaf n
      (scheduledInsertedAtoms role n M
        (fun h => ∏ k, (a.1 (constituentH role size n h k) : ℕ))
        (fun y => ∏ k, (u (constituentY role size n y k) : ℕ))) (hist a.2) ≠ 0 := by
  unfold constituentTransferWeight at hw
  split_ifs at hw
  · exact (mul_ne_zero_iff.mp hw).2
  · exact False.elim (hw rfl)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduledActiveCharacters
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.copyScheduleVertexFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Only original positive roles can occur in the active H block -/

namespace Ostmann

theorem copyScheduleRole_origin_outside {I : Type*} (role : I → CopyScheduleRole)
    (n : ℕ) (v : CopyScheduleVertex I n) (hv : role (copyScheduleOrigin n v) = .outside) :
    copyScheduleRole role n v = .outside := by
  induction n with
  | zero => exact hv
  | succ n ih =>
    rcases v with ⟨b, v⟩ | v
    · change (copyScheduleRole role n v).afterCopy b = .outside
      have h := ih v hv
      rw [h]
      rfl
    · exact ih v hv

theorem copyScheduleH_origin_not_outside {I : Type*} (role : I → CopyScheduleRole)
    (n : ℕ) (h : CopyScheduleH role n) : role (copyScheduleOrigin n h.val) ≠ .outside := by
  intro he
  have hh := h.property.2
  rw [copyScheduleRole_origin_outside role n h.val he] at hh
  cases hh

theorem scheduled_active_characters_invariant {I : Type*}
    (role : I → CopyScheduleRole) (χ : I → ∀ p : ℕ, DirichletCharacter ℂ p)
    (χ₀ : ∀ p : ℕ, DirichletCharacter ℂ p)
    (hχ : ∀ i, role i ≠ .outside → χ i = χ₀)
    (n : ℕ) (e : Equiv.Perm (CopyScheduleH role n)) (h : CopyScheduleH role n) :
    χ (copyScheduleOrigin n (e h).val) = χ (copyScheduleOrigin n h.val) := by
  rw [hχ _ (copyScheduleH_origin_not_outside role n (e h)),
    hχ _ (copyScheduleH_origin_not_outside role n h)]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ActiveNonbulkCount
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Counting only original active nonword slots

Outside slots cannot enter H. In particular the negative copy of the whole
word must not be charged to the nonbulk harmonic normalization.
-/
namespace Ostmann
open scoped Classical

theorem copyScheduleRole_origin_word {I : Type*} (role : I → CopyScheduleRole)
    (n : ℕ) (i : CopyScheduleVertex I n) (hi : role (copyScheduleOrigin n i) = .word) :
    copyScheduleRole role n i = .word := by
  induction n with
  | zero => exact hi
  | succ n ih =>
    rcases i with ⟨b, i⟩ | i
    · change (copyScheduleRole role n i).afterCopy b = .word
      rw [ih i hi]
      rfl
    · exact ih i hi

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_BackwardTargets
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The backwards pivot-target recurrence

For coefficients `c_j = 2^j J + a_j - Delta_j`, the pivot target is `c_j`
plus the sum of all later pivot targets. This constructs the recurrence,
rather than assuming that its simultaneous equations have a solution.
-/

namespace Ostmann

theorem backwardTargets_get (cs : List ℝ) (i : ℕ) (hi : i < cs.length) :
    (backwardTargets cs)[i]'(by rw [backwardTargets_length]; exact hi) =
      cs[i] + ((backwardTargets cs).drop (i + 1)).sum := by
  induction cs generalizing i with
  | nil => simp at hi
  | cons c cs ih =>
    cases i with
    | zero => rfl
    | succ i =>
      simpa only [backwardTargets, List.getElem_cons_succ, List.drop_succ_cons] using
        ih i (by simpa using hi)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_PivotTargetScale
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Positive pivot targets at the required logarithmic scale -/

namespace Ostmann

theorem pivotTargets_recurrence (k : ℕ) (J : ℝ) (a Δ : Fin k → ℝ) (i : Fin k) :
    (pivotTargets k J a Δ)[i.val]'(by
      simpa only [pivotTargets, backwardTargets_length, pivotCoefficients,
        List.length_ofFn] using i.isLt) =
      (2 : ℝ) ^ i.val * J + a i - Δ i +
        ((pivotTargets k J a Δ).drop (i.val + 1)).sum := by
  have hi : i.val < (pivotCoefficients k J a Δ).length := by
    simpa only [pivotCoefficients, List.length_ofFn] using i.isLt
  simpa [pivotTargets, pivotCoefficients] using
    backwardTargets_get (pivotCoefficients k J a Δ) i.val hi

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterDiagonalBudget
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A depth-independent choice of the Section 4 diagonal gap constant -/
namespace Ostmann

/-- Two independently bounded parts of the literal diagonal fit the one-unit
reserve in the amplitude recurrence. -/
theorem character_diagonal_sum_small (a b B m : ℝ) (n : ℕ) (hm : 1 ≤ m)
    (ha : a ≤ Real.exp (-(2 * B + 4) * (2 ^ n : ℕ) * m))
    (hb : b ≤ Real.exp (-(2 * B + 4) * (2 ^ n : ℕ) * m)) :
    a + b ≤ Real.exp (-(2 * B + 3) * (2 ^ n : ℕ) * m) := by
  have hr : (1 : ℝ) ≤ (2 ^ n : ℕ) := by exact_mod_cast Nat.one_le_two_pow
  have hrm : 1 ≤ (2 ^ n : ℕ) * m := by nlinarith
  have htwo : 2 ≤ Real.exp ((2 ^ n : ℕ) * m) :=
    (by linarith : (2 : ℝ) ≤ (2 ^ n : ℕ) * m + 1).trans (Real.add_one_le_exp _)
  calc
    _ ≤ 2 * Real.exp (-(2 * B + 4) * (2 ^ n : ℕ) * m) := by linarith
    _ ≤ Real.exp ((2 ^ n : ℕ) * m) * Real.exp (-(2 * B + 4) * (2 ^ n : ℕ) * m) :=
      mul_le_mul_of_nonneg_right htwo (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_FiniteMatchedPrior
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The counterpart harmonic normalization on the actual finite slot type -/

namespace Ostmann

open scoped BigOperators Classical

theorem finite_enumeration_sum {A M : Type*} [AddCommMonoid M]
    (F G : Fintype A) (f : A → M) :
    Finset.sum (@Finset.univ A F) f = Finset.sum (@Finset.univ A G) f := by
  cases Subsingleton.elim F G
  rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduledInitialPhase
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The initial Poisson phase is the initial phase of the actual schedule -/

namespace Ostmann

open scoped Classical

theorem scheduledPrimePhase_zero {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (χ : I → ∀ p : ℕ, DirichletCharacter ℂ p)
    (g : I → I → ℤ) (pivot : ℕ → I) (initial : I → ℤ → ℕ → ℂ)
    (p : I → ℕ) [∀ i, Fact (p i).Prime] (center : ∀ p : ℕ, ZMod p) (v : ℤ) :
    letI := initialSurvivorPrimeFact role p
    scheduledPrimePhase role χ g pivot initial 0 v (fun i => p i.val) center =
      directedPrimePhase p (fun i => χ i (p i)) (fun i => center (p i))
        (fun i => initial i v (p i)) g v := by
  let := initialSurvivorPrimeFact role p
  unfold scheduledPrimePhase
  have he := directedPrimePhase_equiv (initialSurvivorEquiv role)
    (fun i => p i.val) (fun i => χ (copyScheduleOrigin 0 i.val) (p i.val))
    (fun i => center (p i.val))
    (fun i => copyScheduleUnary χ g pivot initial 0 v i.val (p i.val))
    (fun i j => copyScheduleGraph g pivot 0 i.val j.val) v
  exact he.symm

/-- The Gauss multipliers are only needed at prime arguments; their values at
other natural numbers do not enter the schedule. -/
theorem tupleGraphPhase_eq_regular_directed {I : Type*} [Fintype I]
    (p : I → ℕ) [∀ i, NeZero (p i)] (χ : ∀ i, DirichletCharacter ℂ (p i))
    (t : ∀ i, ZMod (p i)) (v : ℤ) :
    tupleGraphPhase p χ t v = directedPrimePhase p χ t
      (fun i => regularUnary (χ i) (primitiveGaussPhase (χ i)) 1 (v : ZMod (p i)))
      initialCompleteGraph v := by
  rw [tupleGraphPhase_eq_directed]
  have hg : (initialDirectedGraph : I → I → ℤ) = initialCompleteGraph := by
    funext i j
    rfl
  rw [hg]
  congr 1
  funext i
  simp only [regularUnary, zpow_neg_one, MulChar.inv_apply_eq_inv']

/-- The exact level-zero identification used by the initial-amplitude bound. -/
theorem tupleGraphPhase_eq_scheduled {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (χ : I → ∀ p : ℕ, DirichletCharacter ℂ p)
    (κ : I → ℕ → ℂ) (pivot : ℕ → I)
    (p : I → ℕ) [∀ i, Fact (p i).Prime] (center : ∀ p : ℕ, ZMod p)
    (hκ : ∀ i, κ i (p i) = primitiveGaussPhase (χ i (p i))) (v : ℤ) :
    letI := initialSurvivorPrimeFact role p
    tupleGraphPhase p (fun i => χ i (p i)) (fun i => center (p i)) v =
      scheduledPrimePhase role χ initialCompleteGraph pivot (initialRegularUnary χ κ)
        0 v (fun i => p i.val) center := by
  let := initialSurvivorPrimeFact role p
  rw [scheduledPrimePhase_zero, tupleGraphPhase_eq_regular_directed]
  congr 1
  funext i
  simp only [initialRegularUnary, hκ]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ConstituentInitialAmplitude
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual guarded amplitude at depth zero in original prime coordinates -/

namespace Ostmann
open scoped BigOperators Classical

theorem initial_constituent_word_prod {I : Type*} (role : I → CopyScheduleRole)
    (size : I → ℕ) (x : (Σ i, Fin (size i)) → ℕ) (a : CopyScheduleAtoms role 0) :
    ((scheduleConstituentWord role size 0 a).map (fun i => x i.val)).prod =
      ∏ k, x ⟨a.val, k⟩ := by
  rw [scheduleConstituentWord_prod]
  rfl

theorem initial_constituent_pairwise {I : Type*} (role : I → CopyScheduleRole)
    (size : I → ℕ) (x : (Σ i, Fin (size i)) → ℕ) :
    Pairwise (fun i j : SurvivingConstituent role size 0 => (x i.val).Coprime (x j.val)) ↔
      Pairwise (fun i j => (x i).Coprime (x j)) := by
  constructor
  · intro h i j hij
    exact h (show (⟨i, trivial⟩ : SurvivingConstituent role size 0) ≠ ⟨j, trivial⟩ from
      fun he => hij (congrArg Subtype.val he))
  · intro h i j hij
    exact h (fun he => hij (Subtype.ext he))

theorem scheduledSamplePhase_zero {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (χ : I → ∀ p : ℕ, DirichletCharacter ℂ p)
    (κ : I → ℕ → ℂ) (pivot : ℕ → I) (v : ℤ)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (x : I → P)
    (hκ : ∀ i (p : P), κ i p =
      @primitiveGaussPhase p.val ⟨(hP p p.property).ne_zero⟩ (χ i p))
    (center : ∀ p : ℕ, ZMod p) :
    scheduledSamplePhase role χ κ pivot 0 v P hP (fun i => x i.val) center =
      sampledTuplePhase P hP χ center v x := by
  let : ∀ i, Fact (x i : ℕ).Prime := fun i => ⟨hP _ (x i).property⟩
  exact (tupleGraphPhase_eq_scheduled role χ κ pivot (fun i => (x i : ℕ)) center
    (fun i => hκ i (x i)) v).symm

/-- This is the original independent prime law, with the full initial range,
unit and prime support kept inside the integrand. -/
theorem constituentPrimeGuardedAmplitude_zero {I D : Type*} [Fintype I] [Fintype D]
    (role : I → CopyScheduleRole) (size : I → ℕ)
    (χ : (Σ i, Fin (size i)) → ∀ p : ℕ, DirichletCharacter ℂ p)
    (κ : (Σ i, Fin (size i)) → ℕ → ℂ) (pivot : ℕ → (Σ i, Fin (size i)))
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (Q : (Σ i, Fin (size i)) → Finset ℕ)
    (hκ : ∀ i (p : P), κ i p =
      @primitiveGaussPhase p.val ⟨(hP p p.property).ne_zero⟩ (χ i p))
    (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (leaf : ScheduleAtomState role → ℤ → ℂ) (hist : D → ℤ)
    (center : ∀ p : ℕ, ZMod p) :
    constituentPrimeGuardedAmplitude role size χ κ pivot 0 P hP Q
      childBound pivotBound ranges leaf hist center =
    ∑ x : (Σ i, Fin (size i)) → P,
      ((∏ i, primeSubsetPrior P (Q i) (x i) : ℝ) : ℂ) *
      ∑ d, fullAtomTransferWeight role childBound pivotBound ranges leaf 0
        (fun a => ∏ k, (x ⟨a.val, k⟩ : ℕ)) (hist d) *
        (if Pairwise (fun i j => (x i : ℕ).Coprime (x j : ℕ)) then
          sampledTuplePhase P hP χ center (hist d) x else 0) := by
  let ρ := fun i : Σ j, Fin (size j) => role i.1
  let e : ((Σ i, Fin (size i)) → P) ≃ (SurvivingConstituent role size 0 → P) :=
    Equiv.arrowCongr (initialSurvivorEquiv ρ) (Equiv.refl P)
  unfold constituentPrimeGuardedAmplitude
  rw [← e.sum_comp]
  apply Finset.sum_congr rfl
  intro x _
  have hprior : (∏ i : SurvivingConstituent role size 0,
      scheduledRolePrior ρ (fun j => primeSubsetPrior P (Q j)) 0 i (e x i)) =
      ∏ i, primeSubsetPrior P (Q i) (x i) :=
    (initialSurvivorEquiv ρ).prod_comp (fun i : SurvivingConstituent role size 0 =>
      primeSubsetPrior P (Q i.val) (x i.val)) |>.symm
  apply congrArg₂ (fun a b : ℂ => a * b)
  · exact congrArg (fun r : ℝ => (r : ℂ)) hprior
  apply Finset.sum_congr rfl
  intro d _
  have hword : (fun v => ((scheduleConstituentWord role size 0 v).map
      (fun i => (e x i : ℕ))).prod) = (fun a => ∏ k, (x ⟨a.val, k⟩ : ℕ)) := by
    funext a
    exact initial_constituent_word_prod role size (fun i => (x i : ℕ)) a
  rw [hword]
  congr 1
  have hpair := initial_constituent_pairwise role size (fun i => (x i : ℕ))
  change (if Pairwise (fun i j : SurvivingConstituent role size 0 =>
      (x i.val : ℕ).Coprime (x j.val : ℕ)) then _ else 0) = _
  rw [hpair]
  split_ifs
  · exact scheduledSamplePhase_zero ρ χ κ pivot (hist d) P hP x hκ center
  · rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialAtomGuards
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact prime-unit support and Fourier normalization at depth zero -/

namespace Ostmann
open scoped BigOperators Classical SchwartzMap FourierTransform

theorem initial_atom_units_iff {I : Type*} (role : I → CopyScheduleRole)
    (size : I → ℕ) (x : (Σ i, Fin (size i)) → ℕ) (v : ℤ) :
    (∀ a : CopyScheduleAtoms role 0, (∏ k, x ⟨a.val, k⟩).Coprime v.natAbs) ↔
      ∀ i, (x i).Coprime v.natAbs := by
  constructor
  · intro h i
    exact Nat.coprime_fintype_prod_left_iff.mp (h ⟨i.1, trivial⟩) i.2
  · intro h a
    exact Nat.coprime_fintype_prod_left_iff.mpr (fun k => h ⟨a.val, k⟩)

theorem initial_atom_pairwise {I : Type*} (role : I → CopyScheduleRole)
    (size : I → ℕ) (x : (Σ i, Fin (size i)) → ℕ)
    (hx : Pairwise (fun i j => (x i).Coprime (x j))) :
    Pairwise (fun a b : CopyScheduleAtoms role 0 =>
      (∏ k, x ⟨a.val, k⟩).Coprime (∏ k, x ⟨b.val, k⟩)) := by
  intro a b hab
  apply Nat.coprime_fintype_prod_left_iff.mpr
  intro k
  apply Nat.coprime_fintype_prod_right_iff.mpr
  intro l
  apply hx
  intro he
  exact hab (Subtype.ext (congrArg Sigma.fst he))

theorem fullAtomTransferWeight_initial {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (size : I → ℕ)
    (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (leaf : ScheduleAtomState role → ℤ → ℂ) (x : (Σ i, Fin (size i)) → ℕ) (v : ℤ)
    (hx : Pairwise (fun i j => (x i).Coprime (x j)))
    (hrange : ∀ r ∈ ranges 0, r.Holds (fun a => ∏ k, x ⟨a.val, k⟩)) :
    fullAtomTransferWeight role childBound pivotBound ranges leaf 0
      (fun a => ∏ k, x ⟨a.val, k⟩) v =
      if ∀ i, (x i).Coprime v.natAbs then leaf ⟨0, fun a => ∏ k, x ⟨a.val, k⟩⟩ v else 0 := by
  have hpair := initial_atom_pairwise role size x hx
  have hg : fullAtomWeightGuard role childBound pivotBound ranges 0
      (fun a => ∏ k, x ⟨a.val, k⟩) v ↔ ∀ i, (x i).Coprime v.natAbs := by
    constructor
    · intro hg
      exact (initial_atom_units_iff role size x v).mp
        ((totalAtomUnitRanges_iff role 0 _ v).mp hg.2.1)
    · intro hu
      exact ⟨hpair, (totalAtomUnitRanges_iff role 0 _ v).mpr
        ((initial_atom_units_iff role size x v).mpr hu), hrange⟩
  simp only [fullAtomTransferWeight, hg, recursiveTransferWeight]

theorem initial_atom_total {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (size : I → ℕ) (x : (Σ i, Fin (size i)) → ℕ) :
    scheduleAtomTotal role ⟨0, fun a => ∏ k, x ⟨a.val, k⟩⟩ = ∏ i, x i := by
  unfold scheduleAtomTotal
  trans ∏ i : I, ∏ k : Fin (size i), x ⟨i, k⟩
  · exact ((initialSurvivorEquiv role).prod_comp
      (fun a : CopyScheduleAtoms role 0 => ∏ k, x ⟨a.val, k⟩)).symm
  · exact (Fintype.prod_sigma (fun i => x i)).symm

/-- The chosen even cutoff makes the negative recursive Fourier convention
identical to the original positive-frequency Poisson convention. -/
theorem normalizedFourierProfile_even_original (ψ : ℝ → ℂ)
    (heven : ∀ t, ψ (-t) = ψ t) (X M v : ℝ) (hX : X ≠ 0) (hM : M ≠ 0) :
    normalizedFourierProfile ψ v (M / X) =
      (Real.sqrt (X / M) : ℂ) * ψ (v * X / M) := by
  rw [normalizedFourierProfile_original ψ X M v hX hM]
  unfold archimedeanLeafFactor
  rw [mul_one, show -v * X / M = -(v * X / M) by ring, heven]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_PrimeProductMatching
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Equal distinct-prime products give the unique actual slot matching -/

namespace Ostmann

open scoped BigOperators Classical

theorem prime_dvd_prime_product {I : Type*} [Fintype I]
    (p : I → ℕ) (hp : ∀ i, (p i).Prime) (q : ℕ) (hq : q.Prime)
    (hd : q ∣ ∏ i, p i) : ∃ i, q = p i := by
  obtain ⟨i, _, hi⟩ := (hq.prime.dvd_finsetProd_iff p).mp hd
  exact ⟨i, ((Nat.dvd_prime (hp i)).mp hi).resolve_left hq.ne_one⟩

theorem prime_product_matching_exists_unique {I J : Type*} [Fintype I] [Fintype J]
    (p : I → ℕ) (q : J → ℕ) (hp : ∀ i, (p i).Prime) (hq : ∀ j, (q j).Prime)
    (hinjp : Function.Injective p) (hinjq : Function.Injective q)
    (hprod : (∏ i, p i) = ∏ j, q j) : ∃! e : I ≃ J, ∀ i, p i = q (e i) := by
  have hex : ∀ i, ∃ j, p i = q j := by
    intro i
    apply prime_dvd_prime_product q hq (p i) (hp i)
    rw [← hprod]
    exact Finset.dvd_prod_of_mem p (Finset.mem_univ i)
  let f : I → J := fun i => Classical.choose (hex i)
  have hf : ∀ i, p i = q (f i) := fun i => Classical.choose_spec (hex i)
  have hfi : Function.Injective f := by
    intro i i' he
    apply hinjp
    rw [hf i, hf i', he]
  have hfs : Function.Surjective f := by
    intro j
    obtain ⟨i, hi⟩ := prime_dvd_prime_product p hp (q j) (hq j) (by
      rw [hprod]
      exact Finset.dvd_prod_of_mem q (Finset.mem_univ j))
    refine ⟨i, hinjq ?_⟩
    exact (hf i).symm.trans hi.symm
  refine ⟨Equiv.ofBijective f ⟨hfi, hfs⟩, hf, ?_⟩
  intro e he
  apply Equiv.ext
  intro i
  exact hinjq ((he i).symm.trans (hf i))

/-- Replacing the equal-product indicator by the sum over actual matchings
introduces no multiplicity, because all prime slots are distinct. -/
theorem prime_product_matching_sum {I J : Type*} [Fintype I] [Fintype J]
    (p : I → ℕ) (q : J → ℕ) (hp : ∀ i, (p i).Prime) (hq : ∀ j, (q j).Prime)
    (hinjp : Function.Injective p) (hinjq : Function.Injective q) (z : ℂ) :
    (if (∏ i, p i) = ∏ j, q j then z else 0) =
      ∑ e : I ≃ J, if ∀ i, p i = q (e i) then z else 0 := by
  by_cases h : (∏ i, p i) = ∏ j, q j
  · obtain ⟨e, he, hu⟩ := prime_product_matching_exists_unique p q hp hq hinjp hinjq h
    rw [ite_eq_left h, Finset.sum_eq_single e]
    · exact (ite_eq_left he).symm
    · intro e' _ hne
      rw [ite_eq_right (fun he' => hne (hu e' he'))]
    · simp
  · rw [ite_eq_right h]
    symm
    apply Finset.sum_eq_zero
    intro e _
    rw [ite_eq_right]
    intro he
    apply h
    calc
      _ = ∏ i, q (e i) := Finset.prod_congr rfl (fun i _ => he i)
      _ = _ := e.prod_comp q

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_PrimeDiagonalMatching
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The supported arithmetic diagonal is a sum over actual prime permutations -/

namespace Ostmann

open scoped BigOperators Classical ComplexConjugate

theorem pivotDiagonal_fintype_eq {A : Type*} (F G : Fintype A)
    (L : A → ℕ) (v : A → ℤ) (c : A → ℂ) :
    @pivotDiagonal A F L v c = @pivotDiagonal A G L v c := by
  cases Subsingleton.elim F G
  rfl

theorem primePermutationCorrelation_congr {H D : Type*} [Fintype H] [Fintype D]
    (P : Finset ℕ) (v : D → ℤ) (c c' : ((H → P) × D) → ℂ)
    (h : ∀ (e : Equiv.Perm H) l d d', v d = v d' →
      c (l, d) * conj (c (l ∘ e.symm, d')) = c' (l, d) * conj (c' (l ∘ e.symm, d'))) :
    primePermutationCorrelation P v c = primePermutationCorrelation P v c' := by
  unfold primePermutationCorrelation
  apply Finset.sum_congr rfl
  intro e _
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro d _
  apply Finset.sum_congr rfl
  intro d' _
  split_ifs with he
  · exact h e l d d' he
  · rfl

theorem prime_pivotDiagonal_matching {A H : Type*} [Fintype A] [Fintype H]
    (p : A → H → ℕ) (hp : ∀ a h, (p a h).Prime) (v : A → ℤ) (c : A → ℂ)
    (hinj : ∀ a, c a ≠ 0 → Function.Injective (p a))
    (hv : ∀ a, c a ≠ 0 → v a ≠ 0)
    (hsmall : ∀ a, c a ≠ 0 → ∀ h, (v a).natAbs < p a h) :
    pivotDiagonal (fun a => ∏ h, p a h) v c =
      ∑ a, ∑ b, ∑ e : Equiv.Perm H,
        if v a = v b ∧ ∀ h, p a h = p b (e h) then c a * conj (c b) else 0 := by
  unfold pivotDiagonal
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  by_cases ha : c a = 0
  · simp [ha]
  by_cases hb : c b = 0
  · simp [hb]
  have he := pivot_zero_numerator_iff (∏ h, p a h) (∏ h, p b h)
    (Finset.prod_pos (fun h _ => (hp a h).pos)) (v a) (v b) (hv a ha) (hv b hb)
    (fun q hq hd => by
      obtain ⟨h, rfl⟩ := prime_dvd_prime_product (p a) (hp a) q hq hd
      exact hsmall a ha h)
    (fun q hq hd => by
      obtain ⟨h, rfl⟩ := prime_dvd_prime_product (p b) (hp b) q hq hd
      exact hsmall b hb h)
  simp only [he]
  by_cases hab : v a = v b
  · simp only [hab, and_true, true_and]
    exact prime_product_matching_sum (p a) (p b) (hp a) (hp b) (hinj a ha) (hinj b hb) _
  · simp [hab]

theorem prime_pivotDiagonal_permutations {H D : Type*} [Fintype H] [Fintype D]
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (v : D → ℤ)
    (c : ((H → P) × D) → ℂ)
    (hinj : ∀ a, c a ≠ 0 → Function.Injective (fun h => (a.1 h : ℕ)))
    (hv : ∀ a, c a ≠ 0 → v a.2 ≠ 0)
    (hsmall : ∀ a, c a ≠ 0 → ∀ h, (v a.2).natAbs < (a.1 h : ℕ)) :
    pivotDiagonal (fun a => ∏ h, (a.1 h : ℕ)) (fun a => v a.2) c =
      ∑ e : Equiv.Perm H, ∑ l : H → P, ∑ d : D, ∑ d' : D,
        if v d = v d' then c (l, d) * conj (c (l ∘ e.symm, d')) else 0 := by
  rw [prime_pivotDiagonal_matching (fun a h => (a.1 h : ℕ))
    (fun a h => hP _ (a.1 h).property) (fun a => v a.2) c hinj hv hsmall]
  calc
    _ = ∑ e : Equiv.Perm H, ∑ a, ∑ b,
        if v a.2 = v b.2 ∧ ∀ h, (a.1 h : ℕ) = (b.1 (e h) : ℕ)
          then c a * conj (c b) else 0 := by
      calc
        _ = ∑ a, ∑ e : Equiv.Perm H, ∑ b,
            if v a.2 = v b.2 ∧ ∀ h, (a.1 h : ℕ) = (b.1 (e h) : ℕ)
              then c a * conj (c b) else 0 := by
          apply Finset.sum_congr rfl
          intro a _
          rw [Finset.sum_comm]
        _ = _ := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro e _
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro l _
      apply Finset.sum_congr rfl
      intro d _
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro d' _
      rw [Finset.sum_eq_single (l ∘ e.symm)]
      · simp
      · intro r _ hne
        have hn : ¬ ∀ h, (l h : ℕ) = (r (e h) : ℕ) := by
          intro he
          apply hne
          funext h
          apply Subtype.ext
          simpa only [e.apply_symm_apply, Function.comp_apply] using (he (e.symm h)).symm
        simp only [hn, and_false, ite_false, if_false]
      · simp

theorem prime_pivotDiagonal_eq_correlation {H D : Type*} [Fintype H] [Fintype D]
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (v : D → ℤ)
    (c : ((H → P) × D) → ℂ)
    (hinj : ∀ a, c a ≠ 0 → Function.Injective (fun h => (a.1 h : ℕ)))
    (hv : ∀ a, c a ≠ 0 → v a.2 ≠ 0)
    (hsmall : ∀ a, c a ≠ 0 → ∀ h, (v a.2).natAbs < (a.1 h : ℕ)) :
    pivotDiagonal (fun a => ∏ h, (a.1 h : ℕ)) (fun a => v a.2) c =
      primePermutationCorrelation P v c :=
  prime_pivotDiagonal_permutations P hP v c hinj hv hsmall

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ConstituentDiagonalMatching
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Prime matching for the actual original-prior diagonal -/

namespace Ostmann

open scoped BigOperators Classical ComplexConjugate

section

variable {I D : Type*} [Fintype I]
variable (role : I → CopyScheduleRole) (size : I → ℕ)
variable (χ : (Σ i, Fin (size i)) → ∀ p : ℕ, DirichletCharacter ℂ p)
variable (κ : (Σ i, Fin (size i)) → ℕ → ℂ) (pivot : ℕ → (Σ i, Fin (size i)))
variable (n : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
variable (Q : (Σ i, Fin (size i)) → Finset ℕ)
variable (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
variable (leaf : ScheduleAtomState role → ℤ → ℂ) (hist : D → FrequencyTree ℤ n)
variable (center : ∀ p : ℕ, ZMod p)
variable (u : CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n → P) (M : ℕ)

theorem constituentRetainedCoefficient_weight_ne_zero
    (a : (CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → P) × D)
    (ha : constituentRetainedCoefficient role size χ κ pivot n P hP Q
      childBound pivotBound ranges leaf hist center u M a ≠ 0) :
    constituentTransferWeight role size n P Q childBound pivotBound ranges leaf hist u M a ≠ 0 := by
  unfold constituentRetainedCoefficient at ha
  exact (mul_ne_zero_iff.mp ha).1

include hP in
theorem constituentTransferWeight_prime_injective
    (a : (CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → P) × D)
    (ha : constituentTransferWeight role size n P Q childBound pivotBound ranges leaf hist u M a ≠ 0) :
    Function.Injective (fun h => (a.1 h : ℕ)) := by
  unfold constituentTransferWeight at ha
  split_ifs at ha with hg
  · intro h k he
    dsimp only at he
    by_contra hne
    have hc := hg (show Sum.inl h ≠ Sum.inl k from fun hh => hne (Sum.inl.inj hh))
    change (a.1 h : ℕ).Coprime (a.1 k : ℕ) at hc
    rw [he] at hc
    exact (hP _ (a.1 k).property).ne_one (by simpa only [Nat.coprime_self] using hc)
  · exact False.elim (ha rfl)

theorem constituentRetainedCoefficient_prime_injective
    (a : (CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → P) × D)
    (ha : constituentRetainedCoefficient role size χ κ pivot n P hP Q
      childBound pivotBound ranges leaf hist center u M a ≠ 0) :
    Function.Injective (fun h => (a.1 h : ℕ)) := by
  exact constituentTransferWeight_prime_injective role size n P hP Q childBound pivotBound ranges
    leaf hist u M a (constituentRetainedCoefficient_weight_ne_zero role size χ κ pivot n P hP Q
      childBound pivotBound ranges leaf hist center u M a ha)

theorem constituentRetainedCoefficient_root_ne_zero
    (hzero : ∀ x, fullAtomTransferWeight role childBound pivotBound ranges leaf 0 x (0 : ℤ) = 0)
    (a : (CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → P) × D)
    (ha : constituentRetainedCoefficient role size χ κ pivot n P hP Q
      childBound pivotBound ranges leaf hist center u M a ≠ 0) :
    frequencyRoot n (hist a.2) ≠ 0 := by
  have hw := constituentTransferWeight_full_ne_zero role size n P Q childBound pivotBound ranges
    leaf hist u M a (constituentRetainedCoefficient_weight_ne_zero role size χ κ pivot n P hP Q
      childBound pivotBound ranges leaf hist center u M a ha)
  exact fullAtomTransferWeight_all_frequencies_ne_zero role childBound pivotBound ranges leaf hzero
    n _ (hist a.2) hw _ (frequencyRoot_mem_allFrequencyList n (hist a.2))

theorem constituentPivotDiagonal_permutations [Fintype D]
    (hzero : ∀ x, fullAtomTransferWeight role childBound pivotBound ranges leaf 0 x (0 : ℤ) = 0)
    (hsmall : ∀ d p, p ∈ P → (frequencyRoot n (hist d)).natAbs < p) :
    constituentPivotDiagonal role size χ κ pivot n P hP Q childBound pivotBound ranges leaf hist center u M =
      primePermutationCorrelation P (fun d => frequencyRoot n (hist d))
        (constituentRetainedCoefficient role size χ κ pivot n P hP Q
          childBound pivotBound ranges leaf hist center u M) := by
  unfold constituentPivotDiagonal
  have ht := @prime_pivotDiagonal_eq_correlation
    (CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n) D inferInstance inferInstance
    P hP (fun d => frequencyRoot n (hist d))
    (constituentRetainedCoefficient role size χ κ pivot n P hP Q
      childBound pivotBound ranges leaf hist center u M)
    (constituentRetainedCoefficient_prime_injective role size χ κ pivot n P hP Q
      childBound pivotBound ranges leaf hist center u M)
    (constituentRetainedCoefficient_root_ne_zero role size χ κ pivot n P hP Q
      childBound pivotBound ranges leaf hist center u M hzero)
    (fun a _ h => hsmall a.2 _ (a.1 h).property)
  convert ht using 1
  all_goals try with_reducible_and_instances rfl
  with_reducible exact pivotDiagonal_fintype_eq _ _ _ _ _

end

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_RetainedAdditiveMatching
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The common-center additive phase cancels on the matched diagonal -/

namespace Ostmann

open scoped BigOperators Classical ComplexConjugate

section

variable {H Y : Type*} [Fintype H] [Fintype Y]
variable (L : H → ℕ) (U : Y → ℕ)
variable [∀ h, Fact (L h).Prime] [∀ y, Fact (U y).Prime]

theorem retainedAdditiveBranch_equiv (e : Equiv.Perm H)
    (center : ∀ p : ℕ, ZMod p) (M : ℕ) (v : ℤ) :
    retainedAdditiveBranch (fun h => L (e h)) U center M v =
      retainedAdditiveBranch L U center M v := by
  unfold retainedAdditiveBranch
  simp_rw [tupleCofactor_equiv e L (fun h => (Fact.out : (L h).Prime).ne_zero), Equiv.prod_comp e L]
  rw [Equiv.prod_comp e (fun h => (ZMod.stdAddChar
    (center (L h) * ((v : ZMod (L h)) /
      ((M * (tupleCofactor L h * ∏ y, U y) : ℕ) : ZMod (L h)))) : ℂ))]

theorem retainedAdditiveBranch_norm (center : ∀ p : ℕ, ZMod p) (M : ℕ) (v : ℤ) :
    ‖retainedAdditiveBranch L U center M v‖ = 1 := by
  simp only [retainedAdditiveBranch, norm_mul, norm_prod,
    ZMod.stdAddChar_apply, Circle.norm_coe, Finset.prod_const_one, mul_one]

theorem retained_additive_matching_cancel (e : Equiv.Perm H)
    (center : ∀ p : ℕ, ZMod p) (M : ℕ) (v : ℤ) (W W' : ℂ) :
    (retainedAdditiveBranch L U center M v * W) *
      conj (retainedAdditiveBranch (fun h => L (e h)) U center M v * W') = W * conj W' := by
  rw [retainedAdditiveBranch_equiv, map_mul]
  have hn : retainedAdditiveBranch L U center M v *
      conj (retainedAdditiveBranch L U center M v) = 1 := by
    rw [Complex.mul_conj', retainedAdditiveBranch_norm]
    norm_num
  calc
    _ = (retainedAdditiveBranch L U center M v * conj (retainedAdditiveBranch L U center M v)) *
        (W * conj W') := by ring
    _ = _ := by rw [hn, one_mul]

/-- The integer pivot and the common prime centers introduce no residual
additive phase in a matched pair, even when the character rows differ. -/
theorem retainedPrimePhase_matching (e : Equiv.Perm H)
    (center : ∀ p : ℕ, ZMod p)
    (χH χH' : H → ∀ p : ℕ, DirichletCharacter ℂ p)
    (χY χY' : Y → ∀ p : ℕ, DirichletCharacter ℂ p)
    (b b' : Option (H ⊕ Y) → Option (H ⊕ Y) → ℤ)
    (νH νH' : H → ℂ) (νY νY' : Y → ℂ) (M : ℕ) (v : ℤ) (W W' : ℂ) :
    (W * retainedPrimePhase L U center χH χY b νH νY M v) *
      conj (W' * retainedPrimePhase (fun h => L (e h)) U center χH' χY' b' νH' νY' M v) =
    (W * retainedCharacterBranch L U χH χY b νH νY M) *
      conj (W' * retainedCharacterBranch (fun h => L (e h)) U χH' χY' b' νH' νY' M) := by
  unfold retainedPrimePhase
  calc
    _ = (retainedAdditiveBranch L U center M v *
          (W * retainedCharacterBranch L U χH χY b νH νY M)) *
        conj (retainedAdditiveBranch (fun h => L (e h)) U center M v *
          (W' * retainedCharacterBranch (fun h => L (e h)) U χH' χY' b' νH' νY' M)) := by
      simp only [map_mul]
      ring
    _ = _ := retained_additive_matching_cancel L U e center M v _ _

end

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ConstituentCharacterCoefficient
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing the common additive factor from the actual diagonal -/

namespace Ostmann

open scoped BigOperators Classical ComplexConjugate

section

variable {I D : Type*} [Fintype I]
variable (role : I → CopyScheduleRole) (size : I → ℕ)
variable (χ : (Σ i, Fin (size i)) → ∀ p : ℕ, DirichletCharacter ℂ p)
variable (κ : (Σ i, Fin (size i)) → ℕ → ℂ) (pivot : ℕ → (Σ i, Fin (size i)))
variable (n : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
variable (Q : (Σ i, Fin (size i)) → Finset ℕ)
variable (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
variable (leaf : ScheduleAtomState role → ℤ → ℂ) (hist : D → FrequencyTree ℤ n)
variable (center : ∀ p : ℕ, ZMod p)
variable (u : CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n → P) (M : ℕ)

theorem constituentRetainedCoefficient_matching
    (e : Equiv.Perm (CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n))
    (l : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → P) (d d' : D)
    (hv : frequencyRoot n (hist d) = frequencyRoot n (hist d')) :
    constituentRetainedCoefficient role size χ κ pivot n P hP Q
        childBound pivotBound ranges leaf hist center u M (l, d) *
      conj (constituentRetainedCoefficient role size χ κ pivot n P hP Q
        childBound pivotBound ranges leaf hist center u M (l ∘ e.symm, d')) =
    constituentCharacterCoefficient role size χ κ pivot n P hP Q
        childBound pivotBound ranges leaf hist u M (l, d) *
      conj (constituentCharacterCoefficient role size χ κ pivot n P hP Q
        childBound pivotBound ranges leaf hist u M (l ∘ e.symm, d')) := by
  let : ∀ h, Fact (l h : ℕ).Prime := fun h => ⟨hP _ (l h).property⟩
  let : ∀ h, Fact ((l ∘ e.symm) h : ℕ).Prime := fun h => ⟨hP _ ((l ∘ e.symm) h).property⟩
  let : ∀ y, Fact (u y : ℕ).Prime := fun y => ⟨hP _ (u y).property⟩
  unfold constituentRetainedCoefficient constituentCharacterCoefficient
  dsimp only
  rw [← hv]
  exact retainedPrimePhase_matching (fun h => (l h : ℕ)) (fun y => (u y : ℕ))
    e.symm center _ _ _ _ _ _ _ _ _ _ M _ _ _

theorem constituentPivotDiagonal_characters [Fintype D]
    (hzero : ∀ x, fullAtomTransferWeight role childBound pivotBound ranges leaf 0 x (0 : ℤ) = 0)
    (hsmall : ∀ d p, p ∈ P → (frequencyRoot n (hist d)).natAbs < p) :
    constituentPivotDiagonal role size χ κ pivot n P hP Q childBound pivotBound ranges leaf hist center u M =
      primePermutationCorrelation P (fun d => frequencyRoot n (hist d))
        (constituentCharacterCoefficient role size χ κ pivot n P hP Q
          childBound pivotBound ranges leaf hist u M) := by
  apply Eq.trans (constituentPivotDiagonal_permutations role size χ κ pivot n P hP Q
    childBound pivotBound ranges leaf hist center u M hzero hsmall)
  exact primePermutationCorrelation_congr P (fun d => frequencyRoot n (hist d)) _ _
    (constituentRetainedCoefficient_matching role size χ κ pivot n P hP Q
      childBound pivotBound ranges leaf hist center u M)

end

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ConstituentUnweighted
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Separating the original H prior from the supported Fourier weight -/

namespace Ostmann

open scoped BigOperators Classical

theorem constituentTransferWeight_eq_prior_mul {I D : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (size : I → ℕ) (n : ℕ)
    (P : Finset ℕ) (Q : (Σ i, Fin (size i)) → Finset ℕ)
    (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (leaf : ScheduleAtomState role → ℤ → ℂ) (hist : D → FrequencyTree ℤ n)
    (u : CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n → P) (M : ℕ)
    (a : (CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → P) × D) :
    constituentTransferWeight role size n P Q childBound pivotBound ranges leaf hist u M a =
      ((∏ h, primeSubsetPrior P (Q (copyScheduleOrigin n h.val)) (a.1 h) : ℝ) : ℂ) *
        constituentUnweightedTransferWeight role size n P childBound pivotBound ranges leaf hist u M a := by
  unfold constituentTransferWeight constituentCurrentWeight constituentUnweightedTransferWeight
  split_ifs
  · rfl
  · exact (mul_zero _).symm

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ConstituentCharacterCore
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original priors in each matched character correlation -/

namespace Ostmann

open scoped BigOperators Classical ComplexConjugate

section

variable {I D : Type*} [Fintype I]
variable (role : I → CopyScheduleRole) (size : I → ℕ)
variable (χ : (Σ i, Fin (size i)) → ∀ p : ℕ, DirichletCharacter ℂ p)
variable (κ : (Σ i, Fin (size i)) → ℕ → ℂ) (pivot : ℕ → (Σ i, Fin (size i)))
variable (n : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
variable (Q : (Σ i, Fin (size i)) → Finset ℕ)
variable (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
variable (leaf : ScheduleAtomState role → ℤ → ℂ) (hist : D → FrequencyTree ℤ n)
variable (center : ∀ p : ℕ, ZMod p)
variable (u : CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n → P) (M : ℕ)

theorem constituentCharacterCoefficient_factor
    (a : (CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → P) × D) :
    constituentCharacterCoefficient role size χ κ pivot n P hP Q
      childBound pivotBound ranges leaf hist u M a =
    ((∏ h, primeSubsetPrior P (Q (copyScheduleOrigin n h.val)) (a.1 h) : ℝ) : ℂ) *
      constituentCharacterCore role size χ κ pivot n P hP childBound pivotBound ranges leaf hist u M a := by
  unfold constituentCharacterCoefficient constituentCharacterCore
  rw [constituentTransferWeight_eq_prior_mul]
  ring

end

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SignedAtomSchedule
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The positive and conjugate atom copies retain their original characters -/

namespace Ostmann

theorem signedAtomCharacter_active {I : Type*} (role : I → CopyScheduleRole)
    (size : I → ℕ) (χ : ∀ p : ℕ, DirichletCharacter ℂ p)
    (i : Σ j : Bool × I, Fin (size j.2))
    (hi : signedAtomRole role i.1 ≠ .outside) : signedAtomCharacter size χ i = χ := by
  rcases i with ⟨⟨b, i⟩, k⟩
  cases b with
  | false => exact False.elim (hi rfl)
  | true => rfl

/-- Even negative transfer copies keep the character of their original atom.
Every prime-slot matching in H therefore preserves the character assignment. -/
theorem signedAtomCharacter_matching {I : Type*} (role : I → CopyScheduleRole)
    (size : I → ℕ) (χ : ∀ p : ℕ, DirichletCharacter ℂ p) (n : ℕ)
    (e : Equiv.Perm (CopyScheduleH
      (fun i : Σ j : Bool × I, Fin (size j.2) => signedAtomRole role i.1) n))
    (h : CopyScheduleH
      (fun i : Σ j : Bool × I, Fin (size j.2) => signedAtomRole role i.1) n) :
    signedAtomCharacter size χ (copyScheduleOrigin n (e h).val) =
      signedAtomCharacter size χ (copyScheduleOrigin n h.val) :=
  scheduled_active_characters_invariant _ _ χ
    (signedAtomCharacter_active role size χ) n e h

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_PositiveWordStatistic
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The initial nonnegative word statistic -/

namespace Ostmann

open scoped BigOperators SchwartzMap

theorem wordStatisticTerm_nonneg {m : ℕ} (ψ : 𝓢(ℝ, ℂ)) (X : ℝ)
    (G : ℤ → ℂ) (R : Fin m → ℤ → ℂ) (hψ : ∀ x, 0 ≤ (ψ x).re) (a : ℤ) :
    0 ≤ wordStatisticTerm ψ X G R a := by
  unfold wordStatisticTerm
  have hψa := hψ ((a : ℝ) / X)
  positivity

theorem wordStatisticTerm_summable {m : ℕ} (ψ : 𝓢(ℝ, ℂ)) (X : ℝ) (hX : 0 < X)
    (G : ℤ → ℂ) (R : Fin m → ℤ → ℂ) (hψ : ∀ x, 0 ≤ (ψ x).re)
    (hG : ∀ a, ‖G a‖ ≤ 1) (hR : ∀ i a, ‖R i a‖ ≤ 1) :
    Summable (wordStatisticTerm ψ X G R) := by
  have hsum : Summable (fun a : ℤ => ‖ψ ((a : ℝ) / X)‖) := by
    simpa only [positiveDilate_apply, div_eq_mul_inv, mul_comm] using
      schwartz_int_norm_summable (positiveDilate ψ X⁻¹ (inv_pos.mpr hX))
  apply Summable.of_norm_bounded hsum
  intro a
  rw [Real.norm_eq_abs, abs_of_nonneg (wordStatisticTerm_nonneg ψ X G R hψ a)]
  have hg : ‖G a‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg (G a), hG a]
  have hr : (∏ i, ‖R i a‖ ^ 2) ≤ 1 := Finset.prod_le_one
    (fun i _ => sq_nonneg _) (fun i _ => by nlinarith [norm_nonneg (R i a), hR i a])
  calc
    wordStatisticTerm ψ X G R a ≤ (ψ ((a : ℝ) / X)).re := by
      unfold wordStatisticTerm
      exact (mul_le_of_le_one_right (mul_nonneg (hψ _) (sq_nonneg _)) hr).trans
        (mul_le_of_le_one_right (hψ _) hg)
    _ ≤ ‖ψ ((a : ℝ) / X)‖ := Complex.re_le_norm _

/-- The selected endpoints give a lower bound for the full positive
statistic, with all cell multiplicities retained. -/
theorem wordStatistic_lower {m : ℕ} (ψ : 𝓢(ℝ, ℂ)) (X : ℝ) (hX : 0 < X)
    (G : ℤ → ℂ) (R : Fin m → ℤ → ℂ) (S : Finset ℤ)
    (hψ : ∀ x, 0 ≤ (ψ x).re) (hG : ∀ a, ‖G a‖ ≤ 1) (hR : ∀ i a, ‖R i a‖ ≤ 1)
    (c u δ : ℝ) (hu : 0 ≤ u) (hδ : 0 ≤ δ)
    (hcS : ∀ a ∈ S, c ≤ (ψ ((a : ℝ) / X)).re)
    (huS : ∀ a ∈ S, u ≤ ‖G a‖) (hδS : ∀ a ∈ S, ∀ i, δ ≤ ‖R i a‖) :
    S.card * (c * u ^ 2 * δ ^ (2 * m)) ≤ ∑' a : ℤ, wordStatisticTerm ψ X G R a := by
  have hpoint : ∀ a ∈ S, c * u ^ 2 * δ ^ (2 * m) ≤ wordStatisticTerm ψ X G R a := by
    intro a ha
    have hψa := hψ ((a : ℝ) / X)
    have hg : u ^ 2 ≤ ‖G a‖ ^ 2 := pow_le_pow_left₀ hu (huS a ha) _
    have hr : δ ^ (2 * m) ≤ ∏ i, ‖R i a‖ ^ 2 := by
      rw [pow_mul]
      calc
        (δ ^ 2) ^ m = ∏ _i : Fin m, δ ^ 2 := by simp
        _ ≤ _ := Finset.prod_le_prod (fun _ _ => sq_nonneg _)
          (fun i _ => pow_le_pow_left₀ hδ (hδS a ha i) _)
    exact mul_le_mul (mul_le_mul (hcS a ha) hg (sq_nonneg _) (hψ _)) hr
      (by positivity) (by positivity)
  have hfinite := Finset.sum_le_sum hpoint
  simp only [Finset.sum_const, nsmul_eq_mul] at hfinite
  exact hfinite.trans ((wordStatisticTerm_summable ψ X hX G R hψ hG hR).sum_le_tsum S
    (fun a _ => wordStatisticTerm_nonneg ψ X G R hψ a))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_DoubledWordExpansion
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The two independent copies in the original word statistic -/

namespace Ostmann

open scoped BigOperators ComplexConjugate SchwartzMap Classical

theorem weighted_mean_norm_sq {A : Type*} [Fintype A] (w : A → ℝ) (F : A → ℂ) :
    ‖∑ x, (w x : ℂ) * F x‖ ^ 2 =
      ∑ x, ∑ y, w x * w y * (F x * conj (F y)).re := by
  have he : (∑ x, (w x : ℂ) * F x) * conj (∑ x, (w x : ℂ) * F x) =
      ∑ x, ∑ y, ((w x * w y : ℝ) : ℂ) * (F x * conj (F y)) := by
    rw [map_sum, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    simp only [map_mul, Complex.conj_ofReal, Complex.ofReal_mul]
    ring
  rw [Complex.mul_conj'] at he
  have hr := congrArg Complex.re he
  simpa only [← Complex.ofReal_pow, Complex.ofReal_re, Complex.re_sum,
    Complex.mul_re, Complex.ofReal_im, zero_mul, sub_zero] using hr

theorem joint_word_mean {A B : Type*} [Fintype A] {k m : ℕ}
    (μ : Fin k → A → ℝ) (ν : Fin m → A → ℝ)
    (F : Fin k → A → ℂ) (R : Fin m → A → ℂ) (bin : (Fin k → A) → B) (b : B) :
    (∑ z, (jointWordPrior μ ν z : ℂ) * jointWordAmplitude F R bin b z) =
      binnedWordAverage μ F bin b * ∏ i, ∑ x, (ν i x : ℂ) * R i x := by
  classical
  have hcell : (∑ y : Fin m → A, (productPrior ν y : ℂ) * ∏ i, R i (y i)) =
      ∏ i, ∑ x, (ν i x : ℂ) * R i x := by
    simp_rw [productPrior, Complex.ofReal_prod, ← Finset.prod_mul_distrib]
    exact (Fintype.prod_sum (fun (i : Fin m) (x : A) => (ν i x : ℂ) * R i x)).symm
  rw [← hcell, binnedWordAverage, Finset.sum_mul_sum, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  by_cases h : bin x = b
  · simp only [jointWordPrior, jointWordAmplitude, h, ite_true, if_true, Complex.ofReal_mul]
    ring
  · simp [jointWordPrior, jointWordAmplitude, h]

theorem jointWordAmplitude_norm_le_one {A B : Type*} {k m : ℕ}
    (F : Fin k → A → ℂ) (R : Fin m → A → ℂ) (bin : (Fin k → A) → B) (b : B)
    (hF : ∀ i x, ‖F i x‖ ≤ 1) (hR : ∀ i x, ‖R i x‖ ≤ 1)
    (z : (Fin k → A) × (Fin m → A)) :
    ‖jointWordAmplitude F R bin b z‖ ≤ 1 := by
  unfold jointWordAmplitude
  split_ifs
  · rw [norm_mul, norm_prod, norm_prod]
    have hf := Finset.prod_le_one (s := Finset.univ) (fun i _ => norm_nonneg (F i (z.1 i)))
      (fun i _ => hF i (z.1 i))
    have hr := Finset.prod_le_one (s := Finset.univ) (fun i _ => norm_nonneg (R i (z.2 i)))
      (fun i _ => hR i (z.2 i))
    exact (mul_le_mul_of_nonneg_left hr (Finset.prod_nonneg (fun i _ => norm_nonneg _))).trans
      (by simpa only [mul_one] using hf)
  · simp

theorem bounded_schwartz_real_correlation_summable (ψ : 𝓢(ℝ, ℂ)) (X : ℝ)
    (hX : 0 < X) (F G : ℤ → ℂ) (hF : ∀ a, ‖F a‖ ≤ 1) (hG : ∀ a, ‖G a‖ ≤ 1) :
    Summable (fun a : ℤ => (ψ ((a : ℝ) / X)).re * (F a * conj (G a)).re) := by
  have hs : Summable (fun a : ℤ => ‖ψ ((a : ℝ) / X)‖) := by
    simpa only [positiveDilate_apply, div_eq_mul_inv, mul_comm] using
      schwartz_int_norm_summable (positiveDilate ψ X⁻¹ (inv_pos.mpr hX))
  apply Summable.of_norm_bounded hs
  intro a
  rw [Real.norm_eq_abs, abs_mul]
  have hc : |(F a * conj (G a)).re| ≤ 1 := by
    apply (Complex.abs_re_le_norm _).trans
    rw [norm_mul, Complex.norm_conj]
    exact (mul_le_mul_of_nonneg_left (hG a) (norm_nonneg _)).trans
      (by simpa only [mul_one] using hF a)
  exact (mul_le_mul_of_nonneg_left hc (abs_nonneg _)).trans
    (by simpa only [mul_one] using Complex.abs_re_le_norm (ψ ((a : ℝ) / X)))

/-- Each role is sampled twice under its original law. Bin restrictions are
indicators in the amplitude; the prior is never renormalized. -/
theorem word_statistic_double_expansion {A B : Type*} [Fintype A] {k m : ℕ}
    (ψ : 𝓢(ℝ, ℂ)) (X : ℝ) (μ : Fin k → A → ℝ) (ν : Fin m → A → ℝ)
    (F : ℤ → Fin k → A → ℂ) (R : ℤ → Fin m → A → ℂ)
    (bin : (Fin k → A) → B) (b : B) (a : ℤ) :
    wordStatisticTerm ψ X (fun a => binnedWordAverage μ (F a) bin b)
      (fun i a => ∑ x, (ν i x : ℂ) * R a i x) a =
      (ψ ((a : ℝ) / X)).re *
        ∑ z, ∑ z', jointWordPrior μ ν z * jointWordPrior μ ν z' *
          (jointWordAmplitude (F a) (R a) bin b z *
            conj (jointWordAmplitude (F a) (R a) bin b z')).re := by
  calc
    _ = (ψ ((a : ℝ) / X)).re *
        ‖binnedWordAverage μ (F a) bin b * ∏ i, ∑ x, (ν i x : ℂ) * R a i x‖ ^ 2 := by
      simp only [wordStatisticTerm, norm_mul, norm_prod, mul_pow, Finset.prod_pow]
      ring
    _ = (ψ ((a : ℝ) / X)).re *
        ‖∑ z, (jointWordPrior μ ν z : ℂ) * jointWordAmplitude (F a) (R a) bin b z‖ ^ 2 := by
      rw [joint_word_mean]
    _ = _ := congrArg (fun t => (ψ ((a : ℝ) / X)).re * t)
      (weighted_mean_norm_sq (jointWordPrior μ ν) (jointWordAmplitude (F a) (R a) bin b))

/-- The finite original prime averages commute with the physical Schwartz sum.
No conditioning or change of prior occurs in this expansion. -/
theorem word_statistic_tsum_double_expansion {A B : Type*} [Fintype A] {k m : ℕ}
    (ψ : 𝓢(ℝ, ℂ)) (X : ℝ) (hX : 0 < X)
    (μ : Fin k → A → ℝ) (ν : Fin m → A → ℝ)
    (F : ℤ → Fin k → A → ℂ) (R : ℤ → Fin m → A → ℂ)
    (hF : ∀ a i x, ‖F a i x‖ ≤ 1) (hR : ∀ a i x, ‖R a i x‖ ≤ 1)
    (bin : (Fin k → A) → B) (b : B) :
    (∑' a : ℤ, wordStatisticTerm ψ X (fun a => binnedWordAverage μ (F a) bin b)
      (fun i a => ∑ x, (ν i x : ℂ) * R a i x) a) =
      ∑ z, ∑ z', jointWordPrior μ ν z * jointWordPrior μ ν z' *
        ∑' a : ℤ, (ψ ((a : ℝ) / X)).re *
          (jointWordAmplitude (F a) (R a) bin b z *
            conj (jointWordAmplitude (F a) (R a) bin b z')).re := by
  let C (a : ℤ) (z z' : (Fin k → A) × (Fin m → A)) : ℝ :=
    (ψ ((a : ℝ) / X)).re * (jointWordAmplitude (F a) (R a) bin b z *
      conj (jointWordAmplitude (F a) (R a) bin b z')).re
  have hC (z z' : (Fin k → A) × (Fin m → A)) : Summable (fun a => C a z z') :=
    bounded_schwartz_real_correlation_summable ψ X hX _ _
      (fun a => jointWordAmplitude_norm_le_one (F a) (R a) bin b (hF a) (hR a) z)
      (fun a => jointWordAmplitude_norm_le_one (F a) (R a) bin b (hF a) (hR a) z')
  have hs (z z') : Summable (fun a => jointWordPrior μ ν z * jointWordPrior μ ν z' * C a z z') :=
    (hC z z').mul_left _
  have he (a : ℤ) : wordStatisticTerm ψ X (fun a => binnedWordAverage μ (F a) bin b)
      (fun i a => ∑ x, (ν i x : ℂ) * R a i x) a =
      ∑ z, ∑ z', jointWordPrior μ ν z * jointWordPrior μ ν z' * C a z z' := by
    rw [word_statistic_double_expansion]
    simp only [Finset.mul_sum, C]
    apply Finset.sum_congr rfl
    intro z _
    apply Finset.sum_congr rfl
    intro z' _
    ring
  simp_rw [he]
  rw [Summable.tsum_finsetSum (fun z _ => summable_sum (fun z' _ => hs z z'))]
  apply Finset.sum_congr rfl
  intro z _
  rw [Summable.tsum_finsetSum (fun z' _ => hs z z')]
  simp only [tsum_mul_left, C]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_WordCopyCoordinates
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The two copies of every word and cell role as one ordered tuple -/

namespace Ostmann

open scoped BigOperators ComplexConjugate Classical

theorem map_fin_append {A B : Type*} {k m : ℕ} (f : A → B)
    (x : Fin k → A) (y : Fin m → A) :
    Fin.append (f ∘ x) (f ∘ y) = f ∘ Fin.append x y := by
  funext i
  obtain ⟨j, rfl⟩ := (finSumFinEquiv : Fin k ⊕ Fin m ≃ Fin (k + m)).surjective i
  cases j with
  | inl j => simp only [finSumFinEquiv_apply_left, Fin.append_left, Function.comp_apply]
  | inr j => simp only [finSumFinEquiv_apply_right, Fin.append_right, Function.comp_apply]

theorem wordCopyEquiv_map {A B : Type*} {k m : ℕ} (f : A → B)
    (z : ((Fin k → A) × (Fin m → A)) × ((Fin k → A) × (Fin m → A))) :
    wordCopyEquiv B k m ((f ∘ z.1.1, f ∘ z.1.2), (f ∘ z.2.1, f ∘ z.2.2)) =
      f ∘ wordCopyEquiv A k m z := by
  change Fin.append (Fin.append (f ∘ z.1.1) (f ∘ z.1.2))
    (Fin.append (f ∘ z.2.1) (f ∘ z.2.2)) = f ∘ Fin.append (Fin.append z.1.1 z.1.2) (Fin.append z.2.1 z.2.2)
  rw [map_fin_append, map_fin_append, map_fin_append]

theorem productPrior_append {A : Type*} {k m : ℕ}
    (μ : Fin k → A → ℝ) (ν : Fin m → A → ℝ) (x : Fin k → A) (y : Fin m → A) :
    productPrior (Fin.append μ ν) (Fin.append x y) = productPrior μ x * productPrior ν y := by
  simp only [productPrior, Fin.prod_univ_add, Fin.append_left, Fin.append_right]

theorem wordCopyPrior {A : Type*} {k m : ℕ}
    (μ : Fin k → A → ℝ) (ν : Fin m → A → ℝ)
    (z : ((Fin k → A) × (Fin m → A)) × ((Fin k → A) × (Fin m → A))) :
    productPrior (Fin.append (Fin.append μ ν) (Fin.append μ ν)) (wordCopyEquiv A k m z) =
      jointWordPrior μ ν z.1 * jointWordPrior μ ν z.2 := by
  change productPrior (Fin.append (Fin.append μ ν) (Fin.append μ ν))
    (Fin.append (Fin.append z.1.1 z.1.2) (Fin.append z.2.1 z.2.2)) = _
  rw [productPrior_append, productPrior_append, productPrior_append]
  rfl

theorem wordCopyCharacter_product {k m : ℕ}
    (χ : ∀ p : ℕ, DirichletCharacter ℂ p) (t : ∀ p : ℕ, ZMod p) (a : ℤ)
    (z : ((Fin k → ℕ) × (Fin m → ℕ)) × ((Fin k → ℕ) × (Fin m → ℕ))) :
    (∏ i, wordCopyCharacter k m χ i (wordCopyEquiv ℕ k m z i)
      ((a : ZMod (wordCopyEquiv ℕ k m z i)) - t (wordCopyEquiv ℕ k m z i))) =
      ((∏ i, χ (z.1.1 i) ((a : ZMod (z.1.1 i)) - t (z.1.1 i))) *
        (∏ i, χ (z.1.2 i) ((a : ZMod (z.1.2 i)) - t (z.1.2 i)))) *
      conj ((∏ i, χ (z.2.1 i) ((a : ZMod (z.2.1 i)) - t (z.2.1 i))) *
        (∏ i, χ (z.2.2 i) ((a : ZMod (z.2.2 i)) - t (z.2.2 i)))) := by
  let f (p : ℕ) := χ p ((a : ZMod p) - t p)
  let u := wordCopyEquiv ℕ k m z
  have he : (∏ i, wordCopyCharacter k m χ i (u i) ((a : ZMod (u i)) - t (u i))) =
      ∏ i, Fin.append (fun _ : Fin (k + m) => f) (fun _ : Fin (k + m) => conj ∘ f) i (u i) := by
    apply Finset.prod_congr rfl
    intro i _
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [wordCopyCharacter, Fin.append_left]
      rfl
    · simp only [wordCopyCharacter, Fin.append_right]
      exact (MulChar.star_apply' (χ _) _).symm
  rw [he]
  change (∏ i, Fin.append (fun _ : Fin (k + m) => f) (fun _ : Fin (k + m) => conj ∘ f) i
    (Fin.append (Fin.append z.1.1 z.1.2) (Fin.append z.2.1 z.2.2) i)) = _
  rw [Fin.prod_univ_add]
  simp only [Fin.append_left, Fin.append_right]
  rw [Fin.prod_univ_add, Fin.prod_univ_add]
  simp only [Fin.append_left, Fin.append_right, Function.comp_apply, map_mul, map_prod]
  rfl

theorem wordCopyAmplitude_map {A B : Type*} {k m : ℕ} (v : A → ℕ)
    (χ : ∀ p : ℕ, DirichletCharacter ℂ p) (t : ∀ p : ℕ, ZMod p) (a : ℤ)
    (bin : (Fin k → A) → B) (b : B)
    (z : ((Fin k → A) × (Fin m → A)) × ((Fin k → A) × (Fin m → A))) :
    jointWordAmplitude (fun _ p => χ (v p) ((a : ZMod (v p)) - t (v p)))
        (fun _ p => χ (v p) ((a : ZMod (v p)) - t (v p))) bin b z.1 *
      conj (jointWordAmplitude (fun _ p => χ (v p) ((a : ZMod (v p)) - t (v p)))
        (fun _ p => χ (v p) ((a : ZMod (v p)) - t (v p))) bin b z.2) =
      if bin z.1.1 = b ∧ bin z.2.1 = b then
        ∏ i, wordCopyCharacter k m χ i (v (wordCopyEquiv A k m z i))
          ((a : ZMod (v (wordCopyEquiv A k m z i))) - t (v (wordCopyEquiv A k m z i)))
      else 0 := by
  by_cases h₁ : bin z.1.1 = b <;> by_cases h₂ : bin z.2.1 = b
  · simp only [jointWordAmplitude, h₁, h₂, ite_true, if_true, and_self]
    have hh := wordCopyCharacter_product χ t a
      ((v ∘ z.1.1, v ∘ z.1.2), (v ∘ z.2.1, v ∘ z.2.2))
    rw [wordCopyEquiv_map] at hh
    simpa only [Function.comp_apply] using hh.symm
  · simp [jointWordAmplitude, h₁, h₂]
  · simp [jointWordAmplitude, h₁, h₂]
  · simp [jointWordAmplitude, h₁, h₂]

theorem wordCopyCharacter_ne_one {k m : ℕ}
    (χ : ∀ p : ℕ, DirichletCharacter ℂ p) (p : ℕ) (hχ : χ p ≠ 1)
    (i : Fin ((k + m) + (k + m))) : wordCopyCharacter k m χ i p ≠ 1 := by
  obtain ⟨j, rfl⟩ := (finSumFinEquiv : Fin (k + m) ⊕ Fin (k + m) ≃
    Fin ((k + m) + (k + m))).surjective i
  cases j with
  | inl j => simpa only [finSumFinEquiv_apply_left, wordCopyCharacter, Fin.append_left] using hχ
  | inr j => simpa only [finSumFinEquiv_apply_right, wordCopyCharacter, Fin.append_right,
      ne_eq, inv_eq_one] using hχ

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialWordCoordinates
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Explicit original word and cell coordinates for the signed atom schedule -/

namespace Ostmann
open scoped Classical BigOperators

theorem initialWordTupleEquiv_positive {C : Type*} (k m : ℕ) (s : C → ℕ)
    (cell : (Σ c, Fin (s c)) ≃ Fin m)
    (a : Option C) (i : Fin (initialWordSize k s a)) :
    initialWordTupleEquiv k m s cell ⟨⟨true, a⟩, i⟩ =
      (positiveWordTupleEquiv k m s cell ⟨a, i⟩).castAdd (k + m) := rfl

theorem initialWordTupleEquiv_negative {C : Type*} (k m : ℕ) (s : C → ℕ)
    (cell : (Σ c, Fin (s c)) ≃ Fin m)
    (a : Option C) (i : Fin (initialWordSize k s a)) :
    initialWordTupleEquiv k m s cell ⟨⟨false, a⟩, i⟩ =
      (positiveWordTupleEquiv k m s cell ⟨a, i⟩).natAdd (k + m) := rfl

theorem initialWordTupleEquiv_character {C : Type*} (k m : ℕ) (s : C → ℕ)
    (cell : (Σ c, Fin (s c)) ≃ Fin m) (χ : ∀ p : ℕ, DirichletCharacter ℂ p)
    (i : Σ a : Bool × Option C, Fin (initialWordSize k s a.2)) :
    wordCopyCharacter k m χ (initialWordTupleEquiv k m s cell i) =
      signedAtomCharacter (initialWordSize k s) χ i := by
  rcases i with ⟨⟨b, a⟩, i⟩
  cases b with
  | false =>
      rw [initialWordTupleEquiv_negative]
      simp only [wordCopyCharacter, Fin.append_right]
      rfl

  | true =>
      rw [initialWordTupleEquiv_positive]
      simp only [wordCopyCharacter, Fin.append_left]
      rfl

theorem wordCopyEquiv_positive_word {A : Type*} (k m : ℕ)
    (y : Fin ((k + m) + (k + m)) → A) (i : Fin k) :
    ((wordCopyEquiv A k m).symm y).1.1 i = y ((i.castAdd m).castAdd (k + m)) := by
  have h := congrFun ((wordCopyEquiv A k m).apply_symm_apply y)
    ((i.castAdd m).castAdd (k + m))
  change Fin.append (Fin.append _ _) (Fin.append _ _) _ = _ at h
  simp only [Fin.append_left] at h
  exact h

theorem wordCopyEquiv_negative_word {A : Type*} (k m : ℕ)
    (y : Fin ((k + m) + (k + m)) → A) (i : Fin k) :
    ((wordCopyEquiv A k m).symm y).2.1 i = y ((i.castAdd m).natAdd (k + m)) := by
  have h := congrFun ((wordCopyEquiv A k m).apply_symm_apply y)
    ((i.castAdd m).natAdd (k + m))
  change Fin.append (Fin.append _ _) (Fin.append _ _) _ = _ at h
  simp only [Fin.append_left, Fin.append_right] at h
  exact h

theorem initialWordTuple_positive_word {A C : Type*} (k m : ℕ) (s : C → ℕ)
    (cell : (Σ c, Fin (s c)) ≃ Fin m) (y : Fin ((k + m) + (k + m)) → A)
    (i : Fin k) :
    ((wordCopyEquiv A k m).symm y).1.1 i =
      y (initialWordTupleEquiv k m s cell ⟨(true, none), i⟩) :=
  wordCopyEquiv_positive_word k m y i

theorem initialWordTuple_negative_word {A C : Type*} (k m : ℕ) (s : C → ℕ)
    (cell : (Σ c, Fin (s c)) ≃ Fin m) (y : Fin ((k + m) + (k + m)) → A)
    (i : Fin k) :
    ((wordCopyEquiv A k m).symm y).2.1 i =
      y (initialWordTupleEquiv k m s cell ⟨(false, none), i⟩) :=
  wordCopyEquiv_negative_word k m y i

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_TopWordBinScale
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The top prime controls every nonempty bulk-word bin -/

namespace Ostmann

open Filter
open scoped BigOperators

theorem wordLogBin_val {m : ℕ} (τ : ℝ) (ℓ : Fin (m + 1) → ℝ)
    (h : (∑ i, ℓ i) ≤ 4 * τ) :
    (wordLogBin τ ℓ).val = ⌊∑ i, ℓ i⌋₊ := by
  exact Nat.min_eq_left (Nat.floor_mono h)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_AllMultipleTupleWeight
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The harmonic square-root weight of tuples with no singleton -/

namespace Ostmann

open scoped BigOperators Classical

theorem tuple_range_fiber_card_le {A : Type*} [Fintype A] (n : ℕ) (S : Finset A) :
    ((Finset.univ : Finset (Fin n → A)).filter (fun x => Finset.univ.image x = S)).card ≤ n ^ n := by
  let T := (Finset.univ : Finset (Fin n → A)).filter (fun x => Finset.univ.image x = S)
  by_cases ht : T.Nonempty
  · obtain ⟨x, hx⟩ := ht
    have hxS : Finset.univ.image x = S := (Finset.mem_filter.mp hx).2
    have hS : S.card ≤ n := by
      rw [← hxS]
      simpa only [Finset.card_univ, Fintype.card_fin] using
        Finset.card_image_le (s := (Finset.univ : Finset (Fin n))) (f := x)
    let f : T → (Fin n → S) := fun y i => ⟨y.val i, by
      rw [← (Finset.mem_filter.mp y.property).2]
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩
    have hf : Function.Injective f := by
      intro y z h
      apply Subtype.ext
      funext i
      exact congrArg Subtype.val (congrFun h i)
    have hc : T.card ≤ S.card ^ n := by
      simpa only [Fintype.card_coe, Fintype.card_fun, Fintype.card_fin] using
        Fintype.card_le_of_injective f hf
    exact hc.trans (Nat.pow_le_pow_left hS n)
  · have he : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp ht
    change T.card ≤ n ^ n
    rw [he, Finset.card_empty]
    exact Nat.zero_le _

theorem all_multiple_sqrt_weight {A : Type*} [Fintype A] (n : ℕ) (w : A → ℝ)
    (hw0 : ∀ a, 0 ≤ w a) (hw1 : ∀ a, w a ≤ 1) (x : Fin n → A)
    (hm : ∀ a ∈ Finset.univ.image x,
      2 ≤ ((Finset.univ : Finset (Fin n)).filter (fun i => x i = a)).card) :
    (∏ i, Real.sqrt (w (x i))) ≤ ∏ a ∈ Finset.univ.image x, w a := by
  have he := Finset.prod_fiberwise_of_maps_to' (s := (Finset.univ : Finset (Fin n)))
    (t := Finset.univ.image x) (g := x) (fun i hi => Finset.mem_image.mpr ⟨i, hi, rfl⟩)
    (fun a => Real.sqrt (w a))
  rw [← he]
  apply Finset.prod_le_prod (fun a _ => by positivity)
  intro a ha
  simp only [Finset.prod_const]
  calc
    Real.sqrt (w a) ^ ((Finset.univ : Finset (Fin n)).filter (fun i => x i = a)).card ≤
        Real.sqrt (w a) ^ 2 :=
      pow_le_pow_of_le_one (Real.sqrt_nonneg _) (Real.sqrt_le_one.mpr (hw1 a)) (hm a ha)
    _ = w a := Real.sq_sqrt (hw0 a)

theorem exists_singleton_of_not_allMultiple {A : Type*} [Fintype A] {n : ℕ}
    (x : Fin n → A) (hx : x ∉ allMultipleTuples A n) :
    ∃ i, ∀ j, x j = x i → j = i := by
  simp only [allMultipleTuples, Finset.mem_filter, Finset.mem_univ, true_and, not_forall,
    not_le] at hx
  obtain ⟨a, ha⟩ := hx
  have ha' : a ∈ Finset.univ.image x ∧
      ((Finset.univ : Finset (Fin n)).filter (fun i => x i = a)).card < 2 := by
    obtain ⟨ha, hlt⟩ := ha
    exact ⟨ha, hlt⟩
  obtain ⟨j, _, hj⟩ := Finset.mem_image.mp ha'.1
  have hpos : 0 < ((Finset.univ : Finset (Fin n)).filter (fun i => x i = a)).card :=
    Finset.card_pos.mpr ⟨j, by simp [hj]⟩
  have hcard : ((Finset.univ : Finset (Fin n)).filter (fun i => x i = a)).card = 1 := by omega
  obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hcard
  have hxi : x i = a := by
    have hm : i ∈ (Finset.univ : Finset (Fin n)).filter (fun i => x i = a) := by rw [hi]; simp
    exact (Finset.mem_filter.mp hm).2
  refine ⟨i, fun l hl => ?_⟩
  have hm : l ∈ (Finset.univ : Finset (Fin n)).filter (fun i => x i = a) := by simp [hl, hxi]
  rw [hi] at hm
  exact Finset.mem_singleton.mp hm

/-- Grouping by the distinct value set pays at most n^n for the ordered
assignments, while each distinct prime contributes its full harmonic weight. -/
theorem all_multiple_tuple_weight_le {A : Type*} [Fintype A] (n : ℕ) (w : A → ℝ)
    (hw0 : ∀ a, 0 ≤ w a) (hw1 : ∀ a, w a ≤ 1) :
    (∑ x ∈ allMultipleTuples A n, ∏ i, Real.sqrt (w (x i))) ≤
      (n : ℝ) ^ n * ∏ a, (1 + w a) := by
  have hmaps (x : Fin n → A) (_hx : x ∈ allMultipleTuples A n) :
      Finset.univ.image x ∈ (Finset.univ : Finset A).powerset := by simp
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hfiber (S : Finset A) :
      (∑ x ∈ (allMultipleTuples A n).filter (fun x => Finset.univ.image x = S),
        ∏ i, Real.sqrt (w (x i))) ≤ (n : ℝ) ^ n * ∏ a ∈ S, w a := by
    let T := (allMultipleTuples A n).filter (fun x => Finset.univ.image x = S)
    have hT : T.card ≤ n ^ n := by
      apply (Finset.card_le_card (show T ⊆ (Finset.univ : Finset (Fin n → A)).filter
        (fun x => Finset.univ.image x = S) from ?_)).trans (tuple_range_fiber_card_le n S)
      intro x hx
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, (Finset.mem_filter.mp hx).2⟩
    calc
      _ ≤ ∑ _x ∈ T, ∏ a ∈ S, w a := by
        apply Finset.sum_le_sum
        intro x hx
        obtain ⟨hxA, hxS⟩ := Finset.mem_filter.mp hx
        have hm := (Finset.mem_filter.mp hxA).2
        simpa only [hxS] using all_multiple_sqrt_weight n w hw0 hw1 x hm
      _ = (T.card : ℝ) * ∏ a ∈ S, w a := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hT)
        (Finset.prod_nonneg (fun a _ => hw0 a))
  calc
    _ ≤ ∑ S ∈ (Finset.univ : Finset A).powerset, (n : ℝ) ^ n * ∏ a ∈ S, w a :=
      Finset.sum_le_sum (fun S _ => hfiber S)
    _ = (n : ℝ) ^ n * ∏ a, (1 + w a) := by
      rw [← Finset.mul_sum, ← Finset.prod_one_add]

theorem all_multiple_tuple_weight_exp {A : Type*} [Fintype A] (n : ℕ) (w : A → ℝ)
    (hw0 : ∀ a, 0 ≤ w a) (hw1 : ∀ a, w a ≤ 1) :
    (∑ x ∈ allMultipleTuples A n, ∏ i, Real.sqrt (w (x i))) ≤
      (n : ℝ) ^ n * Real.exp (∑ a, w a) := by
  exact (all_multiple_tuple_weight_le n w hw0 hw1).trans
    (mul_le_mul_of_nonneg_left (Real.prod_one_add_le_exp_sum Finset.univ hw0) (by positivity))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_HarmonicRepeatedMass
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Repeated tuples under the original normalized harmonic priors -/

namespace Ostmann

open scoped BigOperators Classical

theorem weighted_all_multiple_mass_le {A : Type*} [Fintype A] (n : ℕ)
    (w : A → ℝ) (hw0 : ∀ a, 0 ≤ w a) (hw1 : ∀ a, w a ≤ 1)
    (c : Fin n → ℝ) (hc : ∀ i, 0 ≤ c i) (μ : Fin n → A → ℝ)
    (hμ : ∀ i a, 0 ≤ μ i a) (hbound : ∀ i a, μ i a ≤ c i * w a)
    (E : Finset (Fin n → A)) (hE : E ⊆ allMultipleTuples A n)
    (ρ : ℝ) (hsmall : ∀ x ∈ E, (∏ i, w (x i)) ≤ ρ) :
    (∑ x ∈ E, productPrior μ x) ≤
      ((∏ i, c i) * Real.sqrt ρ) * ((n : ℝ) ^ n * Real.exp (∑ a, w a)) := by
  have hpoint (x : Fin n → A) (hx : x ∈ E) :
      productPrior μ x ≤ ((∏ i, c i) * Real.sqrt ρ) * ∏ i, Real.sqrt (w (x i)) := by
    have hsquare : (∏ i, Real.sqrt (w (x i))) ^ 2 = ∏ i, w (x i) := by
      rw [← Finset.prod_pow]
      simp only [Real.sq_sqrt (hw0 _)]
    have hs : (∏ i, Real.sqrt (w (x i))) ≤ Real.sqrt ρ :=
      Real.le_sqrt_of_sq_le (hsquare.trans_le (hsmall x hx))
    calc
      productPrior μ x ≤ ∏ i, c i * w (x i) :=
        Finset.prod_le_prod (fun i _ => hμ i (x i)) (fun i _ => hbound i (x i))
      _ = (∏ i, c i) * (∏ i, Real.sqrt (w (x i))) ^ 2 := by
        rw [Finset.prod_mul_distrib, hsquare]
      _ ≤ ((∏ i, c i) * Real.sqrt ρ) * ∏ i, Real.sqrt (w (x i)) := by
        rw [pow_two, ← mul_assoc]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hs (Finset.prod_nonneg (fun i _ => hc i)))
          (Finset.prod_nonneg (fun i _ => Real.sqrt_nonneg _))
  have hsum : (∑ x ∈ E, ∏ i, Real.sqrt (w (x i))) ≤
      (n : ℝ) ^ n * Real.exp (∑ a, w a) := by
    exact (Finset.sum_le_sum_of_subset_of_nonneg hE
      (fun x _ _ => Finset.prod_nonneg (fun i _ => Real.sqrt_nonneg _))).trans
      (all_multiple_tuple_weight_exp n w hw0 hw1)
  calc
    _ ≤ ∑ x ∈ E, ((∏ i, c i) * Real.sqrt ρ) * ∏ i, Real.sqrt (w (x i)) :=
      Finset.sum_le_sum hpoint
    _ = ((∏ i, c i) * Real.sqrt ρ) * ∑ x ∈ E, ∏ i, Real.sqrt (w (x i)) :=
      (Finset.mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum
      (mul_nonneg (Finset.prod_nonneg (fun i _ => hc i)) (Real.sqrt_nonneg _))

theorem harmonic_all_multiple_mass_le (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (n : ℕ) (Q : Fin n → Finset ℕ) (E : Finset (Fin n → P))
    (hE : E ⊆ allMultipleTuples P n) (R : ℝ) (hR : 0 < R)
    (hprod : ∀ x ∈ E, R ≤ ∏ i, (x i : ℝ)) :
    (∑ x ∈ E, productPrior (fun i => primeSubsetPrior P (Q i)) x) ≤
      ((∏ i, (∑ p ∈ Q i, (p : ℝ)⁻¹)⁻¹) * (Real.sqrt R)⁻¹) *
        ((n : ℝ) ^ n * Real.exp (∑ p : P, (p : ℝ)⁻¹)) := by
  have hw1 (p : P) : (p : ℝ)⁻¹ ≤ 1 := by
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (hP p p.property).one_lt.le
    exact inv_le_one_of_one_le₀ hp1
  have hsmall (x : Fin n → P) (hx : x ∈ E) : (∏ i, (x i : ℝ)⁻¹) ≤ R⁻¹ := by
    rw [Finset.prod_inv_distrib]
    exact inv_anti₀ hR (hprod x hx)
  simpa only [Real.sqrt_inv] using weighted_all_multiple_mass_le n
    (fun p : P => (p : ℝ)⁻¹) (fun p => by positivity) hw1
    (fun i => (∑ p ∈ Q i, (p : ℝ)⁻¹)⁻¹) (fun i => by positivity)
    (fun i => primeSubsetPrior P (Q i))
    (fun i p => primeSubsetPrior_nonneg P (Q i) p)
    (fun i p => primeSubsetPrior_atom P (Q i) p) E hE R⁻¹ hsmall

theorem harmonic_all_multiple_integral_bound (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (n : ℕ) (Q : Fin n → Finset ℕ) (E : Finset (Fin n → P))
    (hE : E ⊆ allMultipleTuples P n) (R : ℝ) (hR : 0 < R)
    (hprod : ∀ x ∈ E, R ≤ ∏ i, (x i : ℝ))
    (F : (Fin n → P) → ℂ) (B : ℝ) (hB : 0 ≤ B) (hF : ∀ x ∈ E, ‖F x‖ ≤ B) :
    ‖∑ x ∈ E, (productPrior (fun i => primeSubsetPrior P (Q i)) x : ℂ) * F x‖ ≤
      B * (((∏ i, (∑ p ∈ Q i, (p : ℝ)⁻¹)⁻¹) * (Real.sqrt R)⁻¹) *
        ((n : ℝ) ^ n * Real.exp (∑ p : P, (p : ℝ)⁻¹))) := by
  let μ := fun i => primeSubsetPrior P (Q i)
  have hn (x : Fin n → P) : 0 ≤ productPrior μ x :=
    productPrior_nonneg μ (fun i p => primeSubsetPrior_nonneg P (Q i) p) x
  calc
    _ ≤ ∑ x ∈ E, ‖(productPrior μ x : ℂ) * F x‖ := norm_sum_le _ _
    _ ≤ ∑ x ∈ E, B * productPrior μ x := by
      apply Finset.sum_le_sum
      intro x hx
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hn x)]
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hF x hx) (hn x)
    _ = B * ∑ x ∈ E, productPrior μ x := (Finset.mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (harmonic_all_multiple_mass_le P hP n Q E hE R hR hprod) hB

theorem inverse_sqrt_exp_product (X D : ℝ) (hX : 0 < X) :
    X * (Real.sqrt (X * Real.exp D))⁻¹ =
      Real.sqrt X * Real.exp (-(D / 2)) := by
  rw [Real.sqrt_mul hX.le, ← Real.exp_half, mul_inv, Real.exp_neg]
  have hx : Real.sqrt X ≠ 0 := (Real.sqrt_pos.mpr hX).ne'
  have hs : Real.sqrt X ^ 2 = X := Real.sq_sqrt hX.le
  field_simp
  nlinarith [hs]

/-- The exact square-root scale of the all-multiple error, before choosing
the large gap constant. The harmonic normalizers are retained explicitly. -/
theorem harmonic_repeated_gap_bound (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (n : ℕ) (Q : Fin n → Finset ℕ) (E : Finset (Fin n → P))
    (hE : E ⊆ allMultipleTuples P n) (X D C : ℝ) (hX : 0 < X) (hC : 0 ≤ C)
    (hprod : ∀ x ∈ E, X * Real.exp D ≤ ∏ i, (x i : ℝ))
    (F : (Fin n → P) → ℂ) (hF : ∀ x ∈ E, ‖F x‖ ≤ X * C) :
    ‖∑ x ∈ E, (productPrior (fun i => primeSubsetPrior P (Q i)) x : ℂ) * F x‖ ≤
      Real.sqrt X * (C * (∏ i, (∑ p ∈ Q i, (p : ℝ)⁻¹)⁻¹) * (n : ℝ) ^ n *
        Real.exp ((∑ p : P, (p : ℝ)⁻¹) - D / 2)) := by
  have hb := harmonic_all_multiple_integral_bound P hP n Q E hE
    (X * Real.exp D) (mul_pos hX (Real.exp_pos _)) hprod F (X * C) (mul_nonneg hX.le hC) hF
  have he : X * C * (((∏ i, (∑ p ∈ Q i, (p : ℝ)⁻¹)⁻¹) *
      (Real.sqrt (X * Real.exp D))⁻¹) * ((n : ℝ) ^ n * Real.exp (∑ p : P, (p : ℝ)⁻¹))) =
      Real.sqrt X * (C * (∏ i, (∑ p ∈ Q i, (p : ℝ)⁻¹)⁻¹) * (n : ℝ) ^ n *
        Real.exp ((∑ p : P, (p : ℝ)⁻¹) - D / 2)) := by
    rw [Real.exp_sub]
    have hxs := inverse_sqrt_exp_product X D hX
    rw [Real.exp_neg] at hxs
    calc
      _ = (X * (Real.sqrt (X * Real.exp D))⁻¹) *
          (C * (∏ i, (∑ p ∈ Q i, (p : ℝ)⁻¹)⁻¹) * (n : ℝ) ^ n *
            Real.exp (∑ p : P, (p : ℝ)⁻¹)) := by ring
      _ = _ := by rw [hxs]; ring
  exact he ▸ hb

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_HarmonicRepeatRemoval
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing repeated primes from an original-prior character statistic -/

namespace Ostmann

open scoped BigOperators FourierTransform SchwartzMap Classical

/-- The event `S` contains the original bin and product restrictions. Its
harmonic law is never renormalized when repeated primes are removed. -/
theorem harmonic_repeat_removal (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (n : ℕ) (Q : Fin n → Finset ℕ) (S : Finset (Fin n → P))
    (χ : Fin n → ∀ p : ℕ, DirichletCharacter ℂ p)
    (hχ : ∀ i p, p ∈ P → χ i p ≠ 1) (t : ∀ p : ℕ, ZMod p)
    (ψ : 𝓢(ℝ, ℂ)) (X H R D : ℝ) (hX : 0 < X) (hR : 0 < R)
    (hsupp : ∀ x : ℝ, H < |x| → 𝓕 ψ x = 0)
    (hsmall : ∀ p ∈ P, H * R < p)
    (hupper : ∀ x ∈ S, (∏ i, (x i : ℝ)) ≤ X * R)
    (hlower : ∀ x ∈ S, X * Real.exp D ≤ ∏ i, (x i : ℝ)) :
    let μ := fun i => primeSubsetPrior P (Q i)
    let F := fun x : Fin n → P => characterTupleSum (fun i => (x i : ℕ)) χ t ψ X
    ‖(∑ x ∈ S, (productPrior μ x : ℂ) * F x) -
      ∑ x ∈ S.filter Function.Injective, (productPrior μ x : ℂ) * F x‖ ≤
      Real.sqrt X * (‖𝓕 ψ 0‖ * (∏ i, (∑ p ∈ Q i, (p : ℝ)⁻¹)⁻¹) * (n : ℝ) ^ n *
        Real.exp ((∑ p : P, (p : ℝ)⁻¹) - D / 2)) := by
  intro μ F
  let T := S.filter (fun x => ¬Function.Injective x)
  let E := T.filter (fun x => x ∈ allMultipleTuples P n)
  have hES : E ⊆ S := (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
  have hET : E ⊆ T := Finset.filter_subset _ _
  have hEA : E ⊆ allMultipleTuples P n := fun _ hx => (Finset.mem_filter.mp hx).2
  have hzero (x : Fin n → P) (hx : x ∈ T) (hne : x ∉ E) : F x = 0 := by
    have hxS := (Finset.mem_filter.mp hx).1
    have hn := (Finset.mem_filter.mp hx).2
    have hm : x ∉ allMultipleTuples P n := fun hm => hne (Finset.mem_filter.mpr ⟨hx, hm⟩)
    obtain ⟨i, j, heq, hij⟩ := Function.not_injective_iff.mp hn
    obtain ⟨k, hk⟩ := exists_singleton_of_not_allMultiple x hm
    exact repeated_tuple_singleton_zero (fun l => (x l : ℕ)) (fun l => hP _ (x l).property)
      χ t ψ X H R hX hR hsupp (fun l => hsmall _ (x l).property) (hupper x hxS)
      i j hij (congrArg Subtype.val heq) k
      (fun l hl => hk l (Subtype.ext hl)) (hχ k _ (x k).property)
  have hsums : (∑ x ∈ S, (productPrior μ x : ℂ) * F x) -
      ∑ x ∈ S.filter Function.Injective, (productPrior μ x : ℂ) * F x =
      ∑ x ∈ E, (productPrior μ x : ℂ) * F x := by
    have hs := Finset.sum_filter_add_sum_filter_not S Function.Injective
      (fun x => (productPrior μ x : ℂ) * F x)
    have he : (∑ x ∈ E, (productPrior μ x : ℂ) * F x) =
        ∑ x ∈ T, (productPrior μ x : ℂ) * F x :=
      Finset.sum_subset hET (fun x hx hne => by rw [hzero x hx hne, mul_zero])
    rw [he, ← hs]
    ring
  rw [hsums]
  apply harmonic_repeated_gap_bound P hP n Q E hEA X D ‖𝓕 ψ 0‖ hX (norm_nonneg _)
    (fun x hx => hlower x (hES hx)) F
  intro x hx
  have hxT := hET hx
  obtain ⟨i, j, heq, hij⟩ := Function.not_injective_iff.mp (Finset.mem_filter.mp hxT).2
  exact repeated_tuple_sum_bound (fun l => (x l : ℕ)) (fun l => hP _ (x l).property)
    χ t ψ X H R hX hR hsupp (fun l => hsmall _ (x l).property) (hupper x (hES hx))
    i j hij (congrArg Subtype.val heq)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_WordCharacterStatistic
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The positive word statistic is the real part of the actual tuple mean -/

namespace Ostmann

open scoped BigOperators SchwartzMap ComplexConjugate Classical

theorem bounded_schwartz_mul_summable (ψ : 𝓢(ℝ, ℂ)) (X : ℝ) (hX : 0 < X)
    (F : ℤ → ℂ) (hF : ∀ a, ‖F a‖ ≤ 1) :
    Summable (fun a : ℤ => F a * ψ ((a : ℝ) / X)) := by
  have hs : Summable (fun a : ℤ => ‖ψ ((a : ℝ) / X)‖) := by
    simpa only [positiveDilate_apply, div_eq_mul_inv, mul_comm] using
      schwartz_int_norm_summable (positiveDilate ψ X⁻¹ (inv_pos.mpr hX))
  apply Summable.of_norm_bounded hs
  intro a
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (hF a)

theorem characterTupleSum_re {I : Type*} [Fintype I] (p : I → ℕ)
    (χ : I → ∀ q : ℕ, DirichletCharacter ℂ q) (t : ∀ q : ℕ, ZMod q)
    (ψ : 𝓢(ℝ, ℂ)) (X : ℝ) (hX : 0 < X) (hψ : ∀ x, (ψ x).im = 0) :
    (characterTupleSum p χ t ψ X).re = ∑' a : ℤ, (ψ ((a : ℝ) / X)).re *
      (∏ i, χ i (p i) ((a : ZMod (p i)) - t (p i))).re := by
  have hs := bounded_schwartz_mul_summable ψ X hX
    (fun a => ∏ i, χ i (p i) ((a : ZMod (p i)) - t (p i)))
    (fun a => by
      rw [norm_prod]
      exact Finset.prod_le_one (fun i _ => norm_nonneg _) (fun i _ => (χ i (p i)).norm_le_one _))
  change Complex.reCLM (∑' a : ℤ, _ * ψ ((a : ℝ) / X)) = _
  rw [Complex.reCLM.map_tsum hs]
  apply tsum_congr
  intro a
  simp only [Complex.reCLM_apply, Complex.mul_re, hψ, mul_zero, sub_zero]
  ring

theorem wordCopyCorrelation_tsum {A B : Type*} {k m : ℕ} (v : A → ℕ)
    (χ : ∀ p : ℕ, DirichletCharacter ℂ p) (t : ∀ p : ℕ, ZMod p)
    (ψ : 𝓢(ℝ, ℂ)) (X : ℝ) (hX : 0 < X) (hψ : ∀ x, (ψ x).im = 0)
    (bin : (Fin k → A) → B) (b : B)
    (z : ((Fin k → A) × (Fin m → A)) × ((Fin k → A) × (Fin m → A))) :
    (∑' a : ℤ, (ψ ((a : ℝ) / X)).re *
      (jointWordAmplitude (fun _ p => χ (v p) ((a : ZMod (v p)) - t (v p)))
          (fun _ p => χ (v p) ((a : ZMod (v p)) - t (v p))) bin b z.1 *
        conj (jointWordAmplitude (fun _ p => χ (v p) ((a : ZMod (v p)) - t (v p)))
          (fun _ p => χ (v p) ((a : ZMod (v p)) - t (v p))) bin b z.2)).re) =
      if bin z.1.1 = b ∧ bin z.2.1 = b then
        (characterTupleSum (v ∘ wordCopyEquiv A k m z) (wordCopyCharacter k m χ) t ψ X).re
      else 0 := by
  simp_rw [wordCopyAmplitude_map]
  by_cases hz : bin z.1.1 = b ∧ bin z.2.1 = b
  · simp only [hz]
    exact (characterTupleSum_re _ _ _ ψ X hX hψ).symm
  · simp [hz]

theorem word_statistic_eq_character_mean {A B : Type*} [Fintype A] {k m : ℕ}
    (v : A → ℕ) (μ : Fin k → A → ℝ) (ν : Fin m → A → ℝ)
    (χ : ∀ p : ℕ, DirichletCharacter ℂ p) (t : ∀ p : ℕ, ZMod p)
    (ψ : 𝓢(ℝ, ℂ)) (X : ℝ) (hX : 0 < X) (hψ : ∀ x, (ψ x).im = 0)
    (bin : (Fin k → A) → B) (b : B) :
    (∑' a : ℤ, wordStatisticTerm ψ X
      (fun a => binnedWordAverage μ (fun _ p => χ (v p) ((a : ZMod (v p)) - t (v p))) bin b)
      (fun i a => ∑ p, (ν i p : ℂ) * χ (v p) ((a : ZMod (v p)) - t (v p))) a) =
      (wordCharacterMean v μ ν χ t ψ X bin b).re := by
  rw [word_statistic_tsum_double_expansion ψ X hX μ ν]
  · conv_lhs =>
      enter [2, z, 2, z', 2]
      rw [wordCopyCorrelation_tsum v χ t ψ X hX hψ bin b (z, z')]
    unfold wordCharacterMean
    rw [← (wordCopyEquiv A k m).sum_comp]
    conv_rhs => rw [Fintype.sum_prod_type]
    simp only [Complex.re_sum]
    apply Finset.sum_congr rfl
    intro z _
    apply Finset.sum_congr rfl
    intro z' _
    rw [Equiv.symm_apply_apply, wordCopyPrior]
    by_cases h : bin z.1 = b ∧ bin z'.1 = b
    · simp [h, Complex.mul_re]
    · simp [h]
  · exact fun a i p => (χ (v p)).norm_le_one _
  · exact fun a i p => (χ (v p)).norm_le_one _

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_WordCharacterRemoval
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Repeat removal for the actual two-copy word statistic -/

namespace Ostmann

open scoped BigOperators FourierTransform SchwartzMap Classical

theorem wordCharacterMean_eq_event_sum {A B : Type*} [Fintype A] {k m : ℕ}
    (v : A → ℕ) (μ : Fin k → A → ℝ) (ν : Fin m → A → ℝ)
    (χ : ∀ p : ℕ, DirichletCharacter ℂ p) (t : ∀ p : ℕ, ZMod p)
    (ψ : 𝓢(ℝ, ℂ)) (X : ℝ) (bin : (Fin k → A) → B) (b : B) :
    wordCharacterMean v μ ν χ t ψ X bin b =
      ∑ x ∈ wordCharacterEvent μ ν bin b,
        (productPrior (Fin.append (Fin.append μ ν) (Fin.append μ ν)) x : ℂ) *
          characterTupleSum (v ∘ x) (wordCopyCharacter k m χ) t ψ X := by
  unfold wordCharacterMean wordCharacterEvent
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hb : bin ((wordCopyEquiv A k m).symm x).1.1 = b ∧
      bin ((wordCopyEquiv A k m).symm x).2.1 = b
  · by_cases hw : productPrior (Fin.append (Fin.append μ ν) (Fin.append μ ν)) x = 0
    · simp [hw]
    · simp [hb, hw]
  · simp [hb]

theorem wordCopyPrimePrior {k m : ℕ} (P : Finset ℕ)
    (Q : Fin k → Finset ℕ) (R : Fin m → Finset ℕ) :
    Fin.append (Fin.append (fun i => primeSubsetPrior P (Q i))
      (fun j => primeSubsetPrior P (R j)))
      (Fin.append (fun i => primeSubsetPrior P (Q i)) (fun j => primeSubsetPrior P (R j))) =
      fun i => primeSubsetPrior P (Fin.append (Fin.append Q R) (Fin.append Q R) i) := by
  have h₁ := map_fin_append (primeSubsetPrior P) Q R
  have h₂ := map_fin_append (primeSubsetPrior P) (Fin.append Q R) (Fin.append Q R)
  rw [← h₁] at h₂
  exact h₂

theorem word_character_repeat_removal {B : Type*} {k m : ℕ}
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (Q : Fin k → Finset ℕ) (R : Fin m → Finset ℕ)
    (χ : ∀ p : ℕ, DirichletCharacter ℂ p) (hχ : ∀ p ∈ P, χ p ≠ 1)
    (t : ∀ p : ℕ, ZMod p) (ψ : 𝓢(ℝ, ℂ)) (X H U D : ℝ)
    (hX : 0 < X) (hU : 0 < U)
    (hsupp : ∀ x : ℝ, H < |x| → 𝓕 ψ x = 0)
    (hsmall : ∀ p ∈ P, H * U < p)
    (bin : (Fin k → P) → B) (b : B)
    (hupper : ∀ x ∈ wordCharacterEvent (fun i => primeSubsetPrior P (Q i))
      (fun j => primeSubsetPrior P (R j)) bin b, (∏ i, (x i : ℝ)) ≤ X * U)
    (hlower : ∀ x ∈ wordCharacterEvent (fun i => primeSubsetPrior P (Q i))
      (fun j => primeSubsetPrior P (R j)) bin b, X * Real.exp D ≤ ∏ i, (x i : ℝ)) :
    let μ := fun i => primeSubsetPrior P (Q i)
    let ν := fun j => primeSubsetPrior P (R j)
    ‖wordCharacterMean Subtype.val μ ν χ t ψ X bin b -
      injectiveWordCharacterMean Subtype.val μ ν χ t ψ X bin b‖ ≤
      Real.sqrt X * (‖𝓕 ψ 0‖ *
        (∏ i, (∑ p ∈ Fin.append (Fin.append Q R) (Fin.append Q R) i, (p : ℝ)⁻¹)⁻¹) *
        (((k + m) + (k + m) : ℕ) : ℝ) ^ ((k + m) + (k + m)) *
        Real.exp ((∑ p : P, (p : ℝ)⁻¹) - D / 2)) := by
  intro μ ν
  rw [wordCharacterMean_eq_event_sum]
  unfold injectiveWordCharacterMean
  rw [wordCopyPrimePrior]
  have hr := harmonic_repeat_removal P hP _ (Fin.append (Fin.append Q R) (Fin.append Q R))
    (wordCharacterEvent μ ν bin b) (wordCopyCharacter k m χ)
    (fun i p hp => wordCopyCharacter_ne_one χ p (hχ p hp) i)
    t ψ X H U D hX hU hsupp hsmall hupper hlower
  convert hr using 1
  all_goals try with_reducible_and_instances rfl
  congr 2
  apply Finset.sum_congr
  · ext x
    simp only [Finset.mem_filter]
  · intro x _
    rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialWordRanges
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact closed integer ranges for the original logarithmic word bins -/

namespace Ostmann
open scoped BigOperators Classical

/-- Integer endpoints express the half-open logarithmic bin exactly. -/
theorem floor_log_eq_iff_integer_range (M j : ℕ) (hM : 0 < M) :
    ⌊Real.log (M : ℝ)⌋₊ = j ↔
      (M : ℝ) ∈ Set.Icc (⌈Real.exp (j : ℝ)⌉₊ : ℝ)
        (⌈Real.exp ((j : ℝ) + 1)⌉₊ - 1 : ℕ) := by
  have hm : (0 : ℝ) < M := by exact_mod_cast hM
  have hlog : 0 ≤ Real.log (M : ℝ) := Real.log_nonneg (by exact_mod_cast hM)
  rw [Nat.floor_eq_iff hlog]
  have hlo : (j : ℝ) ≤ Real.log (M : ℝ) ↔ ⌈Real.exp (j : ℝ)⌉₊ ≤ M := by
    rw [Nat.ceil_le]
    rw [← Real.exp_le_exp, Real.exp_log hm]
  have hhi : Real.log (M : ℝ) < (j : ℝ) + 1 ↔
      M ≤ ⌈Real.exp ((j : ℝ) + 1)⌉₊ - 1 := by
    rw [Real.log_lt_iff_lt_exp hm, ← Nat.lt_ceil]
    have hc : 0 < ⌈Real.exp ((j : ℝ) + 1)⌉₊ := by
      exact Nat.ceil_pos.mpr (Real.exp_pos _)
    omega
  simpa only [Set.mem_Icc, Nat.cast_le] using and_congr hlo hhi

theorem wordLogBin_eq_iff_integer_range {m : ℕ} (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (τ : ℝ) (w : Fin (m + 1) → P)
    (b : Fin (⌊4 * τ⌋₊ + 1))
    (hhi : (∑ i, Real.log (w i : ℝ)) ≤ 4 * τ) :
    wordLogBin τ (fun i => Real.log (w i : ℝ)) = b ↔
      ((∏ i, (w i : ℕ) : ℕ) : ℝ) ∈
        Set.Icc (⌈Real.exp (b.val : ℝ)⌉₊ : ℝ)
          (⌈Real.exp ((b.val : ℝ) + 1)⌉₊ - 1 : ℕ) := by
  rw [Fin.ext_iff, wordLogBin_val τ _ hhi]
  have hp : 0 < ∏ i, (w i : ℕ) := Finset.prod_pos (fun i _ => (hP _ (w i).property).pos)
  have he : Real.log ((∏ i, (w i : ℕ) : ℕ) : ℝ) = ∑ i, Real.log (w i : ℝ) := by
    rw [Nat.cast_prod, Real.log_prod (fun i _ => by
      exact_mod_cast (hP _ (w i).property).ne_zero)]
  rw [← he]
  exact floor_log_eq_iff_integer_range _ _ hp

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialWordBinIdentification
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual depth-zero atom ranges are exactly the two word-bin events -/

namespace Ostmann
open scoped Classical BigOperators

theorem initialWordBinRange_ordered {C : Type*}
    (role : Bool × Option C → CopyScheduleRole) (k m : ℕ) (s : C → ℕ)
    (cell : (Σ c, Fin (s c)) ≃ Fin m) (j : ℕ)
    (y : Fin ((k + m) + (k + m)) → ℕ) (b : Bool) :
    (initialWordBinRange role b j).Holds
      (fun a => ∏ i, y (initialWordTupleEquiv k m s cell ⟨a.val, i⟩)) ↔
    ((∏ i : Fin k, (if b then ((wordCopyEquiv ℕ k m).symm y).1.1 i
      else ((wordCopyEquiv ℕ k m).symm y).2.1 i) : ℕ) : ℝ) ∈
      Set.Icc (⌈Real.exp (j : ℝ)⌉₊ : ℝ) (⌈Real.exp ((j : ℝ) + 1)⌉₊ - 1 : ℕ) := by
  simp only [initialWordBinRange, ScheduleAtomRange.Holds, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, mul_one]
  cases b with
  | false =>
      simp only [Bool.false_eq_true, ite_false, if_false]
      have hp : (∏ i : Fin k, y (initialWordTupleEquiv k m s cell ⟨(false, none), i⟩)) =
          ∏ i, ((wordCopyEquiv ℕ k m).symm y).2.1 i :=
        Finset.prod_congr rfl (fun i _ => (initialWordTuple_negative_word k m s cell y i).symm)
      exact Iff.of_eq (congrArg (fun n : ℕ => (n : ℝ) ∈
        Set.Icc (⌈Real.exp (j : ℝ)⌉₊ : ℝ) (⌈Real.exp ((j : ℝ) + 1)⌉₊ - 1 : ℕ)) hp)
  | true =>
      simp only [ite_true, if_true]
      have hp : (∏ i : Fin k, y (initialWordTupleEquiv k m s cell ⟨(true, none), i⟩)) =
          ∏ i, ((wordCopyEquiv ℕ k m).symm y).1.1 i :=
        Finset.prod_congr rfl (fun i _ => (initialWordTuple_positive_word k m s cell y i).symm)
      exact Iff.of_eq (congrArg (fun n : ℕ => (n : ℝ) ∈
        Set.Icc (⌈Real.exp (j : ℝ)⌉₊ : ℝ) (⌈Real.exp ((j : ℝ) + 1)⌉₊ - 1 : ℕ)) hp)

theorem initialWordBinRanges_ordered {C : Type*}
    (role : Bool × Option C → CopyScheduleRole) (k m : ℕ) (s : C → ℕ)
    (cell : (Σ c, Fin (s c)) ≃ Fin m) (j : ℕ)
    (y : Fin ((k + m) + (k + m)) → ℕ) :
    (∀ r ∈ initialWordBinRanges role j,
      r.Holds (fun a => ∏ i, y (initialWordTupleEquiv k m s cell ⟨a.val, i⟩))) ↔
    (((∏ i, ((wordCopyEquiv ℕ k m).symm y).1.1 i : ℕ) : ℝ) ∈
        Set.Icc (⌈Real.exp (j : ℝ)⌉₊ : ℝ) (⌈Real.exp ((j : ℝ) + 1)⌉₊ - 1 : ℕ) ∧
      ((∏ i, ((wordCopyEquiv ℕ k m).symm y).2.1 i : ℕ) : ℝ) ∈
        Set.Icc (⌈Real.exp (j : ℝ)⌉₊ : ℝ) (⌈Real.exp ((j : ℝ) + 1)⌉₊ - 1 : ℕ)) := by
  simp only [initialWordBinRanges, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, initialWordBinRange_ordered, ite_true, if_true,
    Bool.false_eq_true, ite_false, if_false]

theorem initialWordBinRanges_iff_bin {C : Type*}
    (role : Bool × Option C → CopyScheduleRole) (a m : ℕ) (s : C → ℕ)
    (cell : (Σ c, Fin (s c)) ≃ Fin m)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (τ : ℝ)
    (b : Fin (⌊4 * τ⌋₊ + 1)) (y : Fin (((a + 1) + m) + ((a + 1) + m)) → P)
    (hpos : (∑ i, Real.log (((wordCopyEquiv P (a + 1) m).symm y).1.1 i : ℝ)) ≤ 4 * τ)
    (hneg : (∑ i, Real.log (((wordCopyEquiv P (a + 1) m).symm y).2.1 i : ℝ)) ≤ 4 * τ) :
    (∀ r ∈ initialWordBinRanges role b.val,
      r.Holds (fun atom => ∏ i, (y (initialWordTupleEquiv (a + 1) m s cell ⟨atom.val, i⟩) : ℕ))) ↔
    (wordLogBin τ (fun i => Real.log (((wordCopyEquiv P (a + 1) m).symm y).1.1 i : ℝ)) = b ∧
      wordLogBin τ (fun i => Real.log (((wordCopyEquiv P (a + 1) m).symm y).2.1 i : ℝ)) = b) := by
  have hmap := wordCopyEquiv_map (fun p : P => (p : ℕ))
    ((wordCopyEquiv P (a + 1) m).symm y)
  rw [Equiv.apply_symm_apply] at hmap
  have hi := congrArg (wordCopyEquiv ℕ (a + 1) m).symm hmap
  rw [Equiv.symm_apply_apply] at hi
  refine (initialWordBinRanges_ordered role (a + 1) m s cell b.val
    (fun i => (y i : ℕ))).trans ?_
  have hp : (∏ i, ((wordCopyEquiv ℕ (a + 1) m).symm (fun j => (y j : ℕ))).1.1 i) =
      ∏ i, (((wordCopyEquiv P (a + 1) m).symm y).1.1 i : ℕ) :=
    Finset.prod_congr rfl (fun i _ => (congrFun (congrArg (fun z => z.1.1) hi) i).symm)
  have hn : (∏ i, ((wordCopyEquiv ℕ (a + 1) m).symm (fun j => (y j : ℕ))).2.1 i) =
      ∏ i, (((wordCopyEquiv P (a + 1) m).symm y).2.1 i : ℕ) :=
    Finset.prod_congr rfl (fun i _ => (congrFun (congrArg (fun z => z.2.1) hi) i).symm)
  rw [hp, hn]
  exact and_congr (wordLogBin_eq_iff_integer_range P hP τ _ b hpos).symm
    (wordLogBin_eq_iff_integer_range P hP τ _ b hneg).symm

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialGaussMultipliers
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual bounded Gauss multipliers for every original prime role -/

namespace Ostmann
open scoped Classical

theorem primeGaussMultiplier_norm (χ : ∀ p : ℕ, DirichletCharacter ℂ p) (p : ℕ) :
    ‖primeGaussMultiplier χ p‖ = 1 := by
  unfold primeGaussMultiplier
  split_ifs with hp
  · exact @primitiveGaussPhase_norm p ⟨hp.1.ne_zero⟩ _
      (prime_character_isPrimitive p hp.1 (χ p) hp.2)
  · exact norm_one

theorem primeGaussMultiplier_eq (χ : ∀ p : ℕ, DirichletCharacter ℂ p)
    (p : ℕ) (hp : p.Prime) (hχ : χ p ≠ 1) :
    primeGaussMultiplier χ p = @primitiveGaussPhase p ⟨hp.ne_zero⟩ (χ p) := by
  unfold primeGaussMultiplier
  exact dite_eq_left (show p.Prime ∧ χ p ≠ 1 from ⟨hp, hχ⟩)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialTupleFrequencies
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The initial atom unit guard is precisely the Poisson frequency support -/

namespace Ostmann
open scoped Classical

theorem intCast_isUnit_iff_natAbs_coprime (p : ℕ) (v : ℤ) :
    IsUnit (v : ZMod p) ↔ p.Coprime v.natAbs := by
  rw [ZMod.coe_int_isUnit_iff_isCoprime, Int.isCoprime_iff_nat_coprime,
    Int.natAbs_natCast, Nat.coprime_comm]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialConstituentPoisson
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The fully guarded initial constituent coefficient is the Poisson sum -/

namespace Ostmann
open scoped BigOperators Classical SchwartzMap FourierTransform

theorem initial_constituent_poisson_sum {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (size : I → ℕ) [Nonempty (Σ i, Fin (size i))]
    (χ : (Σ i, Fin (size i)) → ∀ p : ℕ, DirichletCharacter ℂ p)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (x : (Σ i, Fin (size i)) → P)
    (center : ∀ p : ℕ, ZMod p) (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (hX : 0 < X)
    (heven : ∀ t : ℝ, 𝓕 ψ (-t) = 𝓕 ψ t) (N : ℕ)
    (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (hx : Pairwise (fun i j => (x i : ℕ).Coprime (x j : ℕ)))
    (hrange : ∀ r ∈ ranges 0, r.Holds (fun a => ∏ k, (x ⟨a.val, k⟩ : ℕ)))
    (hwindow : ((∏ i, (x i : ℕ) : ℕ) : ℝ) / X ∈ Set.Icc lo hi) :
    (∑ v ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
      fullAtomTransferWeight role childBound pivotBound ranges (scheduleFourierLeaf role ψ X lo hi)
        0 (fun a => ∏ k, (x ⟨a.val, k⟩ : ℕ)) v *
      sampledTuplePhase P hP χ center v x) =
    sampledTupleAmplitude P hP χ center ψ X N x := by
  let M := ∏ i, (x i : ℕ)
  have hM : M ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => (hP _ (x i).property).ne_zero)
  have hMn : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hM
  change _ = ∑ v ∈ tupleFrequencies (fun i => (x i : ℕ)) N,
    (Real.sqrt (X / M) : ℂ) * 𝓕 ψ ((v : ℝ) * X / M) *
      sampledTuplePhase P hP χ center v x
  simp only [tupleFrequencies, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro v _
  rw [fullAtomTransferWeight_initial role size childBound pivotBound ranges
    (scheduleFourierLeaf role ψ X lo hi) (fun i => (x i : ℕ)) v hx hrange]
  have htotal := initial_atom_total role size (fun i => (x i : ℕ))
  have hleaf : scheduleFourierLeaf role ψ X lo hi
      ⟨0, fun a => ∏ k, (x ⟨a.val, k⟩ : ℕ)⟩ v =
      (Real.sqrt (X / M) : ℂ) * 𝓕 ψ ((v : ℝ) * X / M) := by
    unfold scheduleFourierLeaf
    rw [htotal, ite_eq_left hwindow, one_mul]
    exact normalizedFourierProfile_even_original (𝓕 ψ : 𝓢(ℝ, ℂ)) heven X M v hX.ne' hMn
  rw [hleaf]
  simp only [intCast_isUnit_iff_natAbs_coprime]
  by_cases hu : ∀ i, (x i : ℕ).Coprime v.natAbs
  · have hv : v ≠ 0 := by
      intro hz
      obtain ⟨i⟩ := ‹Nonempty (Σ i, Fin (size i))›
      have hh := hu i
      rw [hz, Int.natAbs_zero, Nat.coprime_zero_right] at hh
      exact (hP _ (x i).property).ne_one hh
    exact (congrArg (fun z : ℂ => z * sampledTuplePhase P hP χ center v x)
      (ite_eq_left hu)).trans (ite_eq_left (And.intro hv hu)).symm
  · exact (congrArg (fun z : ℂ => z * sampledTuplePhase P hP χ center v x)
      (ite_eq_right hu)).trans ((zero_mul _).trans
        (ite_eq_right (fun h => hu h.2)).symm)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialGuardedExpectation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Initial guarded expectation under the unchanged harmonic product law -/

namespace Ostmann
open scoped BigOperators Classical SchwartzMap FourierTransform

theorem initial_guarded_expectation {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (size : I → ℕ) [Nonempty (Σ i, Fin (size i))]
    (χ : (Σ i, Fin (size i)) → ∀ p : ℕ, DirichletCharacter ℂ p)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (Q : (Σ i, Fin (size i)) → Finset ℕ)
    (hχ : ∀ i p, p ∈ P → χ i p ≠ 1)
    (pivot : ℕ → (Σ i, Fin (size i))) (center : ∀ p : ℕ, ZMod p)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (hX : 0 < X)
    (heven : ∀ t : ℝ, 𝓕 ψ (-t) = 𝓕 ψ t) (N : ℕ)
    (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (hwindow : ∀ x : (Σ i, Fin (size i)) → P,
      (∏ i, primeSubsetPrior P (Q i) (x i)) ≠ 0 →
      (∀ r ∈ ranges 0, r.Holds (fun a => ∏ k, (x ⟨a.val, k⟩ : ℕ))) →
      ((∏ i, (x i : ℕ) : ℕ) : ℝ) / X ∈ Set.Icc lo hi) :
    constituentPrimeGuardedAmplitude role size (χ) (fun i => primeGaussMultiplier (χ i))
      pivot 0 P hP Q childBound pivotBound ranges (scheduleFourierLeaf role ψ X lo hi)
      (fun v : Finset.Icc (-(N : ℤ)) (N : ℤ) => (v : ℤ)) center =
    ∑ x : (Σ i, Fin (size i)) → P,
      ((∏ i, primeSubsetPrior P (Q i) (x i) : ℝ) : ℂ) *
      (if Pairwise (fun i j => (x i : ℕ).Coprime (x j : ℕ)) ∧
          (∀ r ∈ ranges 0, r.Holds (fun a => ∏ k, (x ⟨a.val, k⟩ : ℕ))) then
        sampledTupleAmplitude P hP χ center ψ X N x else 0) := by
  have hk (i) (p : P) : primeGaussMultiplier (χ i) p =
      @primitiveGaussPhase p.val ⟨(hP p p.property).ne_zero⟩ (χ i p) :=
    primeGaussMultiplier_eq (χ i) p (hP p p.property) (hχ i p p.property)
  rw [constituentPrimeGuardedAmplitude_zero role size χ (fun i => primeGaussMultiplier (χ i))
    pivot P hP Q hk childBound pivotBound ranges (scheduleFourierLeaf role ψ X lo hi)
    (fun v : Finset.Icc (-(N : ℤ)) (N : ℤ) => (v : ℤ)) center]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hz : (∏ i, primeSubsetPrior P (Q i) (x i)) = 0
  · simp only [hz, Complex.ofReal_zero, zero_mul]
  apply congrArg (fun z : ℂ => ((∏ i, primeSubsetPrior P (Q i) (x i) : ℝ) : ℂ) * z)
  by_cases hp : Pairwise (fun i j => (x i : ℕ).Coprime (x j : ℕ))
  · simp only [hp, ite_true, if_true, true_and]
    by_cases hr : ∀ r ∈ ranges 0, r.Holds (fun a => ∏ k, (x ⟨a.val, k⟩ : ℕ))
    · rw [ite_eq_left hr]
      have hs := Finset.sum_coe_sort (Finset.Icc (-(N : ℤ)) (N : ℤ))
        (fun v : ℤ => fullAtomTransferWeight role childBound pivotBound ranges
          (scheduleFourierLeaf role ψ X lo hi) 0 (fun a => ∏ k, (x ⟨a.val, k⟩ : ℕ)) v *
          sampledTuplePhase P hP χ center v x)
      exact hs.trans (initial_constituent_poisson_sum role size χ P hP x center ψ X lo hi hX heven N
        childBound pivotBound ranges hp hr (hwindow x hz hr))
    · rw [ite_eq_right hr]
      apply Finset.sum_eq_zero
      intro v _
      have hz : fullAtomTransferWeight role childBound pivotBound ranges
          (scheduleFourierLeaf role ψ X lo hi) 0 (fun a => ∏ k, (x ⟨a.val, k⟩ : ℕ)) (v : ℤ) = 0 := by
        by_contra h
        exact hr (fun r hr => fullAtomTransferWeight_top_range role childBound pivotBound ranges
          (scheduleFourierLeaf role ψ X lo hi) 0 _ (v : ℤ) h r hr)
      rw [hz, zero_mul]
  · simp only [hp, ite_false, if_false, false_and, mul_zero, Finset.sum_const_zero]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialAmplitudeReindex
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Coordinate invariance of the actual initial prime amplitude -/

namespace Ostmann
open scoped BigOperators Classical SchwartzMap FourierTransform

theorem tupleGraphPhase_equiv {I J : Type*} [Fintype I] [Fintype J]
    (e : I ≃ J) (p : J → ℕ) [∀ j, NeZero (p j)]
    (χ : ∀ j, DirichletCharacter ℂ (p j)) (t : ∀ j, ZMod (p j)) (v : ℤ) :
    tupleGraphPhase (fun i => p (e i)) (fun i => χ (e i)) (fun i => t (e i)) v =
      tupleGraphPhase p χ t v := by
  classical
  rw [tupleGraphPhase_eq_directed, tupleGraphPhase_eq_directed]
  have hg : (fun i j => initialDirectedGraph (e i) (e j)) =
      (initialDirectedGraph : I → I → ℤ) := by
    funext i j
    simp only [initialDirectedGraph, e.injective.eq_iff]
  rw [← hg]
  exact directedPrimePhase_equiv e p χ t
    (fun j => primitiveGaussPhase (χ j) * (χ j)⁻¹ (v : ZMod (p j)))
    initialDirectedGraph v

theorem sampledTuplePhase_equiv {I J : Type*} [Fintype I] [Fintype J]
    (e : I ≃ J) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (χ : J → ∀ p : ℕ, DirichletCharacter ℂ p) (t : ∀ p : ℕ, ZMod p)
    (v : ℤ) (x : J → P) :
    sampledTuplePhase P hP (fun i => χ (e i)) t v (fun i => x (e i)) =
      sampledTuplePhase P hP χ t v x := by
  let : ∀ j, NeZero (x j : ℕ) := fun j => ⟨(hP _ (x j).property).ne_zero⟩
  exact tupleGraphPhase_equiv e (fun j => (x j : ℕ))
    (fun j => χ j (x j)) (fun j => t (x j)) v

theorem tupleFrequencies_equiv {I J : Type*} [Fintype I] [Fintype J]
    (e : I ≃ J) (p : J → ℕ) (N : ℕ) :
    tupleFrequencies (fun i => p (e i)) N = tupleFrequencies p N := by
  ext v
  simp only [tupleFrequencies, Finset.mem_filter, intCast_isUnit_iff_natAbs_coprime]
  constructor
  · rintro ⟨hv, hn, hu⟩
    exact ⟨hv, hn, fun j => by simpa using hu (e.symm j)⟩
  · rintro ⟨hv, hn, hu⟩
    exact ⟨hv, hn, fun i => hu (e i)⟩

theorem sampledTupleAmplitude_equiv {I J : Type*} [Fintype I] [Fintype J]
    (e : I ≃ J) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (χ : J → ∀ p : ℕ, DirichletCharacter ℂ p) (t : ∀ p : ℕ, ZMod p)
    (ψ : 𝓢(ℝ, ℂ)) (X : ℝ) (N : ℕ) (x : J → P) :
    sampledTupleAmplitude P hP (fun i => χ (e i)) t ψ X N (fun i => x (e i)) =
      sampledTupleAmplitude P hP χ t ψ X N x := by
  change (∑ v ∈ tupleFrequencies (fun i => (x (e i) : ℕ)) N,
      (Real.sqrt (X / (∏ i, (x (e i) : ℕ))) : ℂ) *
        𝓕 ψ ((v : ℝ) * X / (∏ i, (x (e i) : ℕ))) *
        sampledTuplePhase P hP (fun i => χ (e i)) t v (fun i => x (e i))) =
    ∑ v ∈ tupleFrequencies (fun j => (x j : ℕ)) N,
      (Real.sqrt (X / (∏ j, (x j : ℕ))) : ℂ) *
        𝓕 ψ ((v : ℝ) * X / (∏ j, (x j : ℕ))) * sampledTuplePhase P hP χ t v x
  rw [tupleFrequencies_equiv e (fun j => (x j : ℕ)) N,
    Equiv.prod_comp e (fun j => (x j : ℕ))]
  apply Finset.sum_congr rfl
  intro v _
  rw [sampledTuplePhase_equiv]

theorem prime_sample_pairwise_iff_injective {I : Type*}
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (x : I → P) :
    Pairwise (fun i j => (x i : ℕ).Coprime (x j : ℕ)) ↔ Function.Injective x := by
  constructor
  · intro h i j he
    by_contra hn
    have hc := h hn
    dsimp only at hc
    rw [he, Nat.coprime_self] at hc
    exact (hP _ (x j).property).ne_one hc
  · intro h i j hn
    apply (hP _ (x i).property).coprime_iff_not_dvd.mpr
    intro hd
    have he : (x i : ℕ) = (x j : ℕ) :=
      ((Nat.dvd_prime (hP _ (x j).property)).mp hd).resolve_left (hP _ (x i).property).ne_one
    exact hn (h (Subtype.ext he))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_WordGraphAmplitude
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The initial graph amplitude under the original word and cell laws -/

namespace Ostmann

open scoped BigOperators FourierTransform SchwartzMap Classical

theorem wordGraphAmplitude_eq {B : Type*} {k m : ℕ}
    [Nonempty (Fin ((k + m) + (k + m)))]
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (μ : Fin k → P → ℝ) (ν : Fin m → P → ℝ)
    (χ : ∀ p : ℕ, DirichletCharacter ℂ p) (hχ : ∀ p ∈ P, χ p ≠ 1)
    (t : ∀ p : ℕ, ZMod p) (ψ : 𝓢(ℝ, ℂ)) (X H : ℝ) (hX : 0 < X)
    (N : ℕ) (hsupp : ∀ u : ℝ, H < |u| → 𝓕 ψ u = 0)
    (bin : (Fin k → P) → B) (b : B)
    (hcut : ∀ x ∈ wordCharacterEvent μ ν bin b,
      H * (∏ i, (x i : ℕ)) ≤ N * X) :
    injectiveWordCharacterMean Subtype.val μ ν χ t ψ X bin b / (Real.sqrt X : ℂ) =
      wordGraphAmplitude P hP μ ν χ t ψ X N bin b := by
  unfold injectiveWordCharacterMean wordGraphAmplitude
  rw [Finset.sum_div]
  apply Finset.sum_congr (by ext x; simp only [Finset.mem_filter])
  intro x hx
  rw [mul_div_assoc]
  congr 1
  simpa only [Function.comp_def] using sampledTupleAmplitude_eq P hP (wordCopyCharacter k m χ)
    (fun i p hp => wordCopyCharacter_ne_one χ p (hχ p hp) i) t ψ X H hX N hsupp x
    (Finset.mem_filter.mp hx).2 (hcut x (Finset.mem_filter.mp hx).1)

theorem initial_amplitude_lower (u v η : ℂ) (X S E : ℝ) (hX : 0 < X)
    (hS : S ≤ u.re) (hE : ‖u - v‖ ≤ E) (hη : v / (Real.sqrt X : ℂ) = η) :
    (S - E) / Real.sqrt X ≤ ‖η‖ := by
  have hu : u.re ≤ ‖u - v‖ + ‖v‖ :=
    (Complex.re_le_norm u).trans (by
      simpa only [sub_add_cancel] using norm_add_le (u - v) v)
  have hlow : S - E ≤ ‖v‖ := by linarith
  rw [← hη, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg X)]
  exact div_le_div_of_nonneg_right hlow (Real.sqrt_pos.mpr hX).le

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialWordExpectation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The ordered word amplitude as an unchanged-prior guarded expectation -/

namespace Ostmann
open scoped BigOperators Classical SchwartzMap FourierTransform

theorem mem_wordCharacterEvent {A B : Type*} [Fintype A] {k m : ℕ}
    (μ : Fin k → A → ℝ) (ν : Fin m → A → ℝ) (bin : (Fin k → A) → B) (b : B)
    (x : Fin ((k + m) + (k + m)) → A) :
    x ∈ wordCharacterEvent μ ν bin b ↔
      (bin ((wordCopyEquiv A k m).symm x).1.1 = b ∧
        bin ((wordCopyEquiv A k m).symm x).2.1 = b) ∧
      productPrior (Fin.append (Fin.append μ ν) (Fin.append μ ν)) x ≠ 0 := by
  simp only [wordCharacterEvent, Finset.mem_filter, Finset.mem_univ, true_and]

theorem wordGraphAmplitude_univ {B : Type*} {k m : ℕ}
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (μ : Fin k → P → ℝ) (ν : Fin m → P → ℝ)
    (χ : ∀ p : ℕ, DirichletCharacter ℂ p) (t : ∀ p : ℕ, ZMod p)
    (ψ : 𝓢(ℝ, ℂ)) (X : ℝ) (N : ℕ) (bin : (Fin k → P) → B) (b : B) :
    wordGraphAmplitude P hP μ ν χ t ψ X N bin b =
      ∑ x : Fin ((k + m) + (k + m)) → P,
        (productPrior (Fin.append (Fin.append μ ν) (Fin.append μ ν)) x : ℂ) *
          if Function.Injective x ∧
              bin ((wordCopyEquiv P k m).symm x).1.1 = b ∧
              bin ((wordCopyEquiv P k m).symm x).2.1 = b then
            sampledTupleAmplitude P hP (wordCopyCharacter k m χ) t ψ X N x else 0 := by
  unfold wordGraphAmplitude wordCharacterEvent
  rw [Finset.sum_filter, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hp : productPrior (Fin.append (Fin.append μ ν) (Fin.append μ ν)) x = 0
  · simp only [hp, Complex.ofReal_zero, zero_mul, ite_self]
  · by_cases hi : Function.Injective x <;>
      by_cases hb₁ : bin ((wordCopyEquiv P k m).symm x).1.1 = b <;>
      by_cases hb₂ : bin ((wordCopyEquiv P k m).symm x).2.1 = b <;>
      simp [ne_eq, hp, hi, hb₁, hb₂]

/-- Reindexing changes no original marginal and no prime-pairwise test. -/
theorem initial_prime_expectation_reindex {I : Type*} [Fintype I] [DecidableEq I] {n : ℕ}
    (e : I ≃ Fin n) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (Q : Fin n → Finset ℕ) (χ : Fin n → ∀ p : ℕ, DirichletCharacter ℂ p)
    (t : ∀ p : ℕ, ZMod p) (ψ : 𝓢(ℝ, ℂ)) (X : ℝ) (N : ℕ)
    (R : (I → P) → Prop) [DecidablePred R] :
    (∑ x : I → P, ((∏ i, primeSubsetPrior P (Q (e i)) (x i) : ℝ) : ℂ) *
      if Pairwise (fun i j => (x i : ℕ).Coprime (x j : ℕ)) ∧
          R x then
        sampledTupleAmplitude P hP (fun i => χ (e i)) t ψ X N x else 0) =
    ∑ x : Fin n → P, (productPrior (fun j => primeSubsetPrior P (Q j)) x : ℂ) *
      if Function.Injective x ∧ R (fun i => x (e i)) then
        sampledTupleAmplitude P hP χ t ψ X N x else 0 := by
  let f : (Fin n → P) ≃ (I → P) := Equiv.arrowCongr e.symm (Equiv.refl P)
  rw [← f.sum_comp]
  apply Finset.sum_congr rfl
  intro x _
  have hp : (∏ i, primeSubsetPrior P (Q (e i)) (x (e i))) =
      productPrior (fun j => primeSubsetPrior P (Q j)) x :=
    Equiv.prod_comp e (fun j => primeSubsetPrior P (Q j) (x j))
  have hi : Pairwise (fun i j => (x (e i) : ℕ).Coprime (x (e j) : ℕ)) ↔
      Function.Injective x := by
    rw [prime_sample_pairwise_iff_injective P hP]
    exact ⟨fun h i j hij => by
      have hh := h (show x (e (e.symm i)) = x (e (e.symm j)) by simpa using hij)
      simpa using congrArg e hh,
      fun h i j hij => e.injective (h hij)⟩
  change ((∏ i, primeSubsetPrior P (Q (e i)) (x (e i)) : ℝ) : ℂ) *
    (if Pairwise (fun i j => (x (e i) : ℕ).Coprime (x (e j) : ℕ)) ∧
      R (fun i => x (e i)) then
      sampledTupleAmplitude P hP (fun i => χ (e i)) t ψ X N (fun i => x (e i)) else 0) = _
  rw [hp, hi, sampledTupleAmplitude_equiv]
  by_cases h : Function.Injective x ∧ R (fun i => x (e i))
  · simp only [h]
  · simp only [h, ite_false, if_false]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialGroupedWordAmplitude
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact identification of the grouped initial expectation with the word amplitude -/

namespace Ostmann
open scoped BigOperators Classical SchwartzMap FourierTransform

theorem initial_grouped_word_expectation {C : Type*} [Fintype C]
    (role : Bool × Option C → CopyScheduleRole) (a m : ℕ) (s : C → ℕ)
    (cell : (Σ c, Fin (s c)) ≃ Fin m) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (Q : Fin (a + 1) → Finset ℕ) (R : Fin m → Finset ℕ)
    (χ : ∀ p : ℕ, DirichletCharacter ℂ p) (t : ∀ p : ℕ, ZMod p)
    (ψ : 𝓢(ℝ, ℂ)) (X τ : ℝ) (N : ℕ) (b : Fin (⌊4 * τ⌋₊ + 1))
    (hbin : ∀ y : Fin (((a + 1) + m) + ((a + 1) + m)) → P,
      productPrior (fun i => primeSubsetPrior P
        (Fin.append (Fin.append Q R) (Fin.append Q R) i)) y ≠ 0 →
      (∑ i, Real.log (((wordCopyEquiv P (a + 1) m).symm y).1.1 i : ℝ)) ≤ 4 * τ ∧
      (∑ i, Real.log (((wordCopyEquiv P (a + 1) m).symm y).2.1 i : ℝ)) ≤ 4 * τ) :
    (∑ x : (Σ v : Bool × Option C, Fin (initialWordSize (a + 1) s v.2)) → P,
      ((∏ i, primeSubsetPrior P
        (Fin.append (Fin.append Q R) (Fin.append Q R)
          (initialWordTupleEquiv (a + 1) m s cell i)) (x i) : ℝ) : ℂ) *
      if Pairwise (fun i j => (x i : ℕ).Coprime (x j : ℕ)) ∧
          (∀ r ∈ initialWordBinRanges role b.val,
            r.Holds (fun v => ∏ i, (x ⟨v.val, i⟩ : ℕ))) then
        sampledTupleAmplitude P hP
          (fun i => wordCopyCharacter (a + 1) m χ (initialWordTupleEquiv (a + 1) m s cell i))
          t ψ X N x else 0) =
    wordGraphAmplitude P hP (fun i => primeSubsetPrior P (Q i))
      (fun j => primeSubsetPrior P (R j)) χ t ψ X N
      (fun w => wordLogBin τ (fun i => Real.log (w i : ℝ))) b := by
  refine (initial_prime_expectation_reindex (initialWordTupleEquiv (a + 1) m s cell)
    P hP (Fin.append (Fin.append Q R) (Fin.append Q R))
    (wordCopyCharacter (a + 1) m χ) t ψ X N
    (fun x => ∀ r ∈ initialWordBinRanges role b.val,
      r.Holds (fun v => ∏ i, (x ⟨v.val, i⟩ : ℕ)))).trans ?_
  rw [wordGraphAmplitude_univ, wordCopyPrimePrior]
  apply Finset.sum_congr rfl
  intro y _
  by_cases hz : productPrior (fun i => primeSubsetPrior P
      (Fin.append (Fin.append Q R) (Fin.append Q R) i)) y = 0
  · simp only [hz, Complex.ofReal_zero, zero_mul]
  · obtain ⟨hp, hn⟩ := hbin y hz
    have hr := initialWordBinRanges_iff_bin role a m s cell P hP τ b y hp hn
    apply congrArg (fun z : ℂ => (productPrior (fun i => primeSubsetPrior P
      (Fin.append (Fin.append Q R) (Fin.append Q R) i)) y : ℂ) * z)
    have hg : (Function.Injective y ∧
        ∀ r ∈ initialWordBinRanges role b.val,
          r.Holds (fun v => ∏ i, (y (initialWordTupleEquiv (a + 1) m s cell ⟨v.val, i⟩) : ℕ))) ↔
        (Function.Injective y ∧
          wordLogBin τ (fun i => Real.log (((wordCopyEquiv P (a + 1) m).symm y).1.1 i : ℝ)) = b ∧
          wordLogBin τ (fun i => Real.log (((wordCopyEquiv P (a + 1) m).symm y).2.1 i : ℝ)) = b) :=
      and_congr_right (fun _ => hr)
    by_cases h : Function.Injective y ∧
        wordLogBin τ (fun i => Real.log (((wordCopyEquiv P (a + 1) m).symm y).1.1 i : ℝ)) = b ∧
        wordLogBin τ (fun i => Real.log (((wordCopyEquiv P (a + 1) m).symm y).2.1 i : ℝ)) = b
    · have h' := hg.mpr h
      exact (ite_eq_left h').trans (ite_eq_left h).symm
    · have h' : ¬ (Function.Injective y ∧
          ∀ r ∈ initialWordBinRanges role b.val,
            r.Holds (fun v => ∏ i, (y (initialWordTupleEquiv (a + 1) m s cell ⟨v.val, i⟩) : ℕ))) :=
        fun hh => h (hg.mp hh)
      exact (ite_eq_right h').trans (ite_eq_right h).symm

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterScheduleRoles
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The finite role set used in the nonquadratic character argument

A positive word, finitely many pivot groups, two fresh anchors at each step,
and one filler have independent negative copies. Only the positive word,
pivots and anchors participate in the copy schedule.
-/
namespace Ostmann
open scoped Classical BigOperators

theorem characterPivotAtom_unique {k : ℕ} (j : Fin k) (v : CharacterRole k)
    (hv : characterRole k v = .pivot j.val) : v = characterPivotAtom j := by
  rcases v with ⟨b, c⟩
  cases b with
  | false => simp [characterRole, signedAtomRole] at hv
  | true =>
    cases c with
    | none => simp [characterRole, signedAtomRole, characterPositiveRole] at hv
    | some c =>
      rcases c with i | a | u
      · have hi : i = j := Fin.ext (CopyScheduleRole.pivot.inj hv)
        subst i
        rfl
      · simp [characterRole, signedAtomRole, characterPositiveRole] at hv
      · simp [characterRole, signedAtomRole, characterPositiveRole] at hv

/-- Every retained H permutation preserves the original signed character. -/
theorem characterSchedule_matching {k : ℕ} (m : ℕ) (r : Fin k → ℕ) (f : ℕ)
    (χ : ∀ p : ℕ, DirichletCharacter ℂ p) (n : ℕ)
    (e : Equiv.Perm (CopyScheduleH
      (fun i : Σ v, Fin (characterSize m r f v) => characterRole k i.1) n))
    (h : CopyScheduleH
      (fun i : Σ v, Fin (characterSize m r f v) => characterRole k i.1) n) :
    signedAtomCharacter (initialWordSize (m + 1) (characterCellSize r f)) χ
        (copyScheduleOrigin n (e h).val) =
      signedAtomCharacter (initialWordSize (m + 1) (characterCellSize r f)) χ
        (copyScheduleOrigin n h.val) :=
  signedAtomCharacter_matching (characterPositiveRole k)
    (initialWordSize (m + 1) (characterCellSize r f)) χ n e h

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_TransferRoundedCutoffs
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Natural cutoffs supplied by the transfer's exponential ranges -/

namespace Ostmann

open Filter
open scoped Topology

theorem natural_exp_cutoff_bounds (E : ℝ) (hE : Real.log 2 ≤ E) :
    0 < ⌊Real.exp E⌋₊ ∧ (⌊Real.exp E⌋₊ : ℝ) ≤ Real.exp E ∧
      Real.exp E ≤ 2 * (⌊Real.exp E⌋₊ : ℝ) := by
  have hexp : (2 : ℝ) ≤ Real.exp E := by
    calc
      _ = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
      _ ≤ Real.exp E := Real.exp_le_exp.mpr hE
  have hn : 1 ≤ ⌊Real.exp E⌋₊ := (Nat.one_le_floor_iff _).mpr (by linarith)
  have hnR : (1 : ℝ) ≤ ⌊Real.exp E⌋₊ := by exact_mod_cast hn
  exact ⟨hn, Nat.floor_le (Real.exp_pos _).le, by linarith [Nat.lt_floor_add_one (Real.exp E)]⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduledFrequencyBounds
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The concrete rounded frequency family and its finite counting cost -/

namespace Ostmann

open scoped BigOperators Classical

theorem transferErrorScale_monotone (Δ m : ℝ) (hΔ : 0 ≤ Δ) : Monotone (transferErrorScale Δ m) := by
  apply monotone_nat_of_le_succ
  intro n
  have h2 : 0 ≤ (2 : ℝ) ^ n * Δ := mul_nonneg (by positivity) hΔ
  have h4 : 0 ≤ (4 : ℝ) ^ n * Real.sqrt m := mul_nonneg (by positivity) (Real.sqrt_nonneg m)
  simp only [transferErrorScale, pow_succ]
  nlinarith

theorem naturalTransferCutoff_monotone (Δ m : ℝ) (hΔ : 0 ≤ Δ) :
    Monotone (naturalTransferCutoff Δ m) := by
  intro a b hab
  exact Nat.floor_le_floor (Real.exp_le_exp.mpr (transferErrorScale_monotone Δ m hΔ hab))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterHBounds
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Product bounds retain the complete selected word bins -/
namespace Ostmann
open scoped Classical BigOperators
open Filter

theorem character_H_card_le {k n : ℕ} (hn : n < k) :
    Fintype.card (CopyScheduleH (characterRole k) n) ≤ 2 ^ n + k + 2 := by
  rw [← Fintype.card_congr (characterHEquiv hn)]
  change Fintype.card ((Fin n → Bool) ⊕ ({j : Fin k // n < j.val} ⊕ Bool)) ≤ _
  simp only [Fintype.card_sum, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  have h := Fintype.card_subtype_le (fun j : Fin k => n < j.val)
  simp only [Fintype.card_fin] at h
  omega

theorem character_H_sum {k n : ℕ} (hn : n < k) (w : CharacterRole k → ℝ) :
    (∑ h : CopyScheduleH (characterRole k) n, w (copyScheduleOrigin n h.val)) =
      (2 : ℝ) ^ n * w (true, none) +
        ((∑ j : {j : Fin k // n < j.val}, w (characterPivotAtom j.val)) +
          ∑ b : Bool, w (characterAnchorAtom ⟨n, hn⟩ b)) := by
  rw [← (characterHEquiv hn).sum_comp]
  change (∑ x : CharacterHIndex k n,
    w (copyScheduleOrigin n (characterHCoordinate hn x).val)) = _
  simp only [characterHCoordinate_origin, Fintype.sum_sum_type, Finset.sum_const,
    Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]

/-- A bounded error per selected atom costs only a constant depending on the
fixed depth, not on the number of primes in the word. -/
theorem character_H_product_bounds {k n : ℕ} (hn : n < k)
    (w : CharacterRole k → ℝ) (lo hi : CharacterRole k → ℕ)
    (c : ℝ) (hc : 0 ≤ c)
    (hlo : ∀ i, Real.exp (w i - c) ≤ lo i)
    (hhi : ∀ i, (hi i : ℝ) ≤ Real.exp (w i + c)) :
    let T := (2 : ℝ) ^ n * w (true, none) +
      ((∑ j : {j : Fin k // n < j.val}, w (characterPivotAtom j.val)) +
        ∑ b : Bool, w (characterAnchorAtom ⟨n, hn⟩ b))
    let C := ((2 : ℝ) ^ k + k + 2) * c
    Real.exp (T - C) ≤
      (∏ h : CopyScheduleH (characterRole k) n, lo (copyScheduleOrigin n h.val) : ℕ) ∧
    (∏ h : CopyScheduleH (characterRole k) n, hi (copyScheduleOrigin n h.val) : ℕ) ≤
      Real.exp (T + C) := by
  intro T C
  have hcard : (Fintype.card (CopyScheduleH (characterRole k) n) : ℝ) ≤
      (2 : ℝ) ^ k + k + 2 := by
    have h : (Fintype.card (CopyScheduleH (characterRole k) n) : ℝ) ≤
        (2 : ℝ) ^ n + k + 2 := by exact_mod_cast character_H_card_le hn
    have hp : (2 : ℝ) ^ n ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hn.le
    linarith
  have hcost := mul_le_mul_of_nonneg_right hcard hc
  have hsum : (∑ h : CopyScheduleH (characterRole k) n,
      w (copyScheduleOrigin n h.val)) = T := character_H_sum hn w
  constructor
  · calc
      Real.exp (T - C) ≤ Real.exp (T - Fintype.card (CopyScheduleH (characterRole k) n) * c) :=
        Real.exp_le_exp.mpr (by dsimp [C] at hcost ⊢; linarith)
      _ = ∏ h : CopyScheduleH (characterRole k) n, Real.exp (w (copyScheduleOrigin n h.val) - c) := by
        rw [← Real.exp_sum, Finset.sum_sub_distrib, hsum]
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ _ := by
        rw [Nat.cast_prod]
        exact Finset.prod_le_prod (fun _ _ => (Real.exp_pos _).le) (fun i _ => hlo _)
  · calc
      _ ≤ ∏ h : CopyScheduleH (characterRole k) n, Real.exp (w (copyScheduleOrigin n h.val) + c) := by
        rw [Nat.cast_prod]
        exact Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _) (fun i _ => hhi _)
      _ = Real.exp (T + Fintype.card (CopyScheduleH (characterRole k) n) * c) := by
        rw [← Real.exp_sum, Finset.sum_add_distrib, hsum]
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ Real.exp (T + C) := Real.exp_le_exp.mpr (by dsimp [C] at hcost ⊢; linarith)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterTargetCenters
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual backwards targets give the copied block's exact center -/
namespace Ostmann
open scoped Classical BigOperators

private theorem sum_drop_eq_sum_later (s : List ℝ) (k : ℕ) (hlen : s.length = k) (n : ℕ) :
    (s.drop (n + 1)).sum =
      ∑ j : {j : Fin k // n < j.val}, s[j.val.val]'(by rw [hlen]; exact j.val.isLt) := by
  let e : Fin (s.drop (n + 1)).length ≃ {j : Fin k // n < j.val} :=
    { toFun := fun i => ⟨⟨n + 1 + i.val, by
        have hi := i.isLt
        simp only [List.length_drop, hlen] at hi
        omega⟩, by change n < n + 1 + i.val; omega⟩
      invFun := fun j => ⟨j.val.val - (n + 1), by
        simp only [List.length_drop, hlen]
        have hj := j.val.isLt
        have hn := j.property
        omega⟩
      left_inv := by intro i; apply Fin.ext; dsimp; omega
      right_inv := by intro j; apply Subtype.ext; apply Fin.ext; dsimp; have := j.property; omega }
  have hsum : (∑ i : Fin (s.drop (n + 1)).length, (s.drop (n + 1))[i.val]) =
      (s.drop (n + 1)).sum := by
    rw [← List.sum_ofFn, List.ofFn_getElem]
  rw [← hsum]
  apply Fintype.sum_equiv e
  intro i
  simp only [List.getElem_drop]
  rfl

theorem characterPivotTarget_future (k : ℕ) (J : ℝ) (a Δ : Fin k → ℝ) (n : ℕ) :
    ((pivotTargets k J a Δ).drop (n + 1)).sum =
      ∑ j : {j : Fin k // n < j.val}, characterPivotTarget k J a Δ j.val :=
  sum_drop_eq_sum_later _ k (by simp [pivotTargets, backwardTargets_length, pivotCoefficients]) n

/-- This is the equality log H = T_j + Delta_j used by the transfer.
It follows from the constructed backwards targets, not a range assumption. -/
theorem character_H_target_center {k n : ℕ} (hn : n < k) (J B z m F : ℝ)
    (a : Fin k → Bool → ℝ) :
    let Δ := fun j : Fin k => characterPivotGap B z m j.val
    let A := fun j => a j false + a j true
    let T := characterPivotTarget k J A Δ
    (∑ h : CopyScheduleH (characterRole k) n,
      characterLogCenter J T a F (copyScheduleOrigin n h.val)) =
        T ⟨n, hn⟩ + characterPivotGap B z m n := by
  intro Δ A T
  rw [character_H_sum hn]
  simp only [characterLogCenter, characterPivotAtom, characterAnchorAtom, Fintype.sum_bool]
  have ht := pivotTargets_recurrence k J A Δ ⟨n, hn⟩
  rw [characterPivotTarget_future] at ht
  change T ⟨n, hn⟩ = (2 : ℝ) ^ n * J + (a ⟨n, hn⟩ false + a ⟨n, hn⟩ true) -
    characterPivotGap B z m n + ∑ j : {j : Fin k // n < j.val}, T j.val at ht
  linarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterDiagonalGap
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original whole-word product pays the diagonal endpoint count -/
namespace Ostmann
open scoped Classical BigOperators

/-- Extract the reciprocal H product before summing the extended pivot.
The loss is only twice the fixed covering error. -/
theorem character_diagonal_product_gap {k n : ℕ} (hn : n < k)
    (J B z m F c : ℝ) (hc : 0 ≤ c) (a : Fin k → Bool → ℝ)
    (lo hi : CharacterRole k → ℕ)
    (hlo : ∀ i, Real.exp (characterLogCenter J
      (characterPivotTarget k J (fun j => a j false + a j true)
        (fun j => characterPivotGap B z m j.val)) a F i - c) ≤ lo i)
    (hhi : ∀ i, (hi i : ℝ) ≤ Real.exp (characterLogCenter J
      (characterPivotTarget k J (fun j => a j false + a j true)
        (fun j => characterPivotGap B z m j.val)) a F i + c)) :
    let T := characterPivotTarget k J (fun j => a j false + a j true)
      (fun j => characterPivotGap B z m j.val)
    let C := characterRangeError k c
    Real.exp (characterPivotGap B z m n - 2 * C) *
        (naturalProductCap (T ⟨n, hn⟩ + C) : ℝ) ≤
      ∏ h : CopyScheduleH (characterRole k) n, (lo (copyScheduleOrigin n h.val) : ℝ) := by
  intro T C
  let w := characterLogCenter J T a F
  have hp := (character_H_product_bounds hn w lo hi c hc hlo hhi).1
  change Real.exp (_ - C) ≤ _ at hp
  rw [← character_H_sum hn w, character_H_target_center hn J B z m F a] at hp
  rw [← Nat.cast_prod]
  apply le_trans _ hp
  calc
    _ ≤ Real.exp (characterPivotGap B z m n - 2 * C) * Real.exp (T ⟨n, hn⟩ + C) :=
      mul_le_mul_of_nonneg_left (Nat.floor_le (Real.exp_pos _).le) (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

/-- A fixed covering loss is absorbed by one unit of the linear gap coefficient. -/
theorem character_diagonal_gap_reserve (n : ℕ) (B z m C : ℝ)
    (hm : 0 ≤ m) (hC : 2 * C ≤ m) :
    (B + 20 * Real.log z - 1) * (2 ^ n : ℕ) * m ≤
      characterPivotGap B z m n - 2 * C := by
  have hp : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
  have hh := mul_le_mul_of_nonneg_right hp hm
  have hs : 0 ≤ (4 : ℝ) ^ (n + 1) * Real.sqrt m := by positivity
  simp only [characterPivotGap, characterBaseGap, Nat.cast_pow, Nat.cast_ofNat]
  nlinarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialWordAtomIntervals
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Whole-atom intervals retain exactly the selected initial word bin -/
namespace Ostmann
open scoped BigOperators Classical

theorem initialWordBinRange_values {C : Type*}
    (role : Bool × Option C → CopyScheduleRole) (b : Bool) (j : ℕ)
    (x : CopyScheduleAtoms role 0 → ℕ) :
    (initialWordBinRange role b j).Holds x ↔
      ⌈Real.exp (j : ℝ)⌉₊ ≤ x ⟨(b, none), trivial⟩ ∧
      x ⟨(b, none), trivial⟩ ≤ ⌈Real.exp ((j : ℝ) + 1)⌉₊ - 1 := by
  simp only [initialWordBinRange, ScheduleAtomRange.Holds, List.map_cons,
    List.map_nil, List.prod_cons, List.prod_nil, mul_one, Set.mem_Icc, Nat.cast_le]

theorem initialWordBinRanges_values {C : Type*}
    (role : Bool × Option C → CopyScheduleRole) (j : ℕ)
    (x : CopyScheduleAtoms role 0 → ℕ) :
    (∀ r ∈ initialWordBinRanges role j, r.Holds x) ↔
      ∀ b : Bool, ⌈Real.exp (j : ℝ)⌉₊ ≤ x ⟨(b, none), trivial⟩ ∧
        x ⟨(b, none), trivial⟩ ≤ ⌈Real.exp ((j : ℝ) + 1)⌉₊ - 1 := by
  simp only [initialWordBinRanges, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, initialWordBinRange_values]
  constructor
  · rintro ⟨ht, hf⟩ b
    cases b
    · exact hf
    · exact ht
  · intro h
    exact ⟨h true, h false⟩

/-- All nonword intervals already hold on the original prior. Thus adding
these guards leaves precisely the two original word-bin events. -/
theorem initialWordAtomIntervals_equiv {C : Type*} [Fintype C]
    (role : Bool × Option C → CopyScheduleRole) (j : ℕ) (lo hi : C → ℕ)
    (x : CopyScheduleAtoms role 0 → ℕ)
    (hcell : ∀ (b : Bool) (c : C), lo c ≤ x ⟨(b, some c), trivial⟩ ∧
      x ⟨(b, some c), trivial⟩ ≤ hi c) :
    (∀ r ∈ atomIntervalRanges role (initialWordAtomLower j lo)
      (initialWordAtomUpper j hi) 0, r.Holds x) ↔
    ∀ r ∈ initialWordBinRanges role j, r.Holds x := by
  rw [atomIntervalRanges_holds_iff, initialWordBinRanges_values]
  constructor
  · intro h b
    exact h ⟨(b, none), trivial⟩
  · intro h v
    rcases v with ⟨⟨b, c⟩, hv⟩
    cases c with
    | none => exact h b
    | some c => exact hcell b c

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterWordIntervals
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integer word-bin endpoints have the same bounded errors as selected cells -/
namespace Ostmann
open scoped Classical

theorem initialWordAtomLower_word_gt_one {C : Type*} (j : ℕ) (hj : 0 < j)
    (lo : C → ℕ) (b : Bool) : 1 < initialWordAtomLower j lo (b, none) := by
  have he : (1 : ℝ) < Real.exp (j : ℝ) := Real.one_lt_exp_iff.mpr (by exact_mod_cast hj)
  have hh := he.trans_le (Nat.le_ceil (Real.exp (j : ℝ)))
  change 1 < ⌈Real.exp (j : ℝ)⌉₊
  exact_mod_cast hh

theorem character_word_interval_errors {k : ℕ} (j : ℕ) (c : ℝ) (hc : 1 ≤ c)
    (T : Fin k → ℝ) (a : Fin k → Bool → ℝ) (F : ℝ)
    (lo hi : CharacterCell k → ℕ)
    (hlo : ∀ v, Real.exp (characterLogCenter j T a F (true, some v) - c) ≤ lo v)
    (hhi : ∀ v, (hi v : ℝ) ≤ Real.exp (characterLogCenter j T a F (true, some v) + c)) :
    (∀ v, Real.exp (characterLogCenter j T a F v - c) ≤ initialWordAtomLower j lo v) ∧
    ∀ v, (initialWordAtomUpper j hi v : ℝ) ≤ Real.exp (characterLogCenter j T a F v + c) := by
  constructor
  · rintro ⟨b, v⟩
    cases v with
    | none =>
      change Real.exp ((j : ℝ) - c) ≤ (⌈Real.exp (j : ℝ)⌉₊ : ℝ)
      exact (Real.exp_le_exp.mpr (by linarith)).trans (Nat.le_ceil _)
    | some v => exact hlo v
  · rintro ⟨b, v⟩
    cases v with
    | none =>
      change ((⌈Real.exp ((j : ℝ) + 1)⌉₊ - 1 : ℕ) : ℝ) ≤ Real.exp ((j : ℝ) + c)
      have hp : 1 ≤ ⌈Real.exp ((j : ℝ) + 1)⌉₊ :=
        Nat.ceil_pos.mpr (Real.exp_pos _)
      rw [Nat.cast_sub hp, Nat.cast_one]
      have hh := Nat.ceil_lt_add_one (Real.exp_pos ((j : ℝ) + 1)).le
      apply le_trans (by linarith : (⌈Real.exp ((j : ℝ) + 1)⌉₊ : ℝ) - 1 ≤
        Real.exp ((j : ℝ) + 1))
      exact Real.exp_le_exp.mpr (by linarith)
    | some v => exact hhi v

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_RepeatFactorBounds
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual normalizer and multiplicity costs in repeat removal -/

namespace Ostmann

open Filter
open scoped BigOperators Classical

theorem doubledRole_normalizers {k m : ℕ} (Q : Fin k → Finset ℕ) (R : Fin m → Finset ℕ) :
    (∏ i, (∑ p ∈ Fin.append (Fin.append Q R) (Fin.append Q R) i, (p : ℝ)⁻¹)⁻¹) =
      (∏ i, (∑ p ∈ Q i, (p : ℝ)⁻¹)⁻¹) ^ 2 *
        (∏ i, (∑ p ∈ R i, (p : ℝ)⁻¹)⁻¹) ^ 2 := by
  simp only [Fin.prod_univ_add, Fin.append_left, Fin.append_right]
  ring

theorem bulk_top_normalizers {m c : ℕ} (B T : Finset ℕ) (R : Fin c → Finset ℕ) :
    (∏ i, (∑ p ∈ Fin.append
      (Fin.append (Fin.append (fun _ : Fin m => B) (fun _ : Fin 1 => T)) R)
      (Fin.append (Fin.append (fun _ : Fin m => B) (fun _ : Fin 1 => T)) R) i,
        (p : ℝ)⁻¹)⁻¹) =
      ((∑ p ∈ B, (p : ℝ)⁻¹)⁻¹) ^ (2 * m) *
        ((∑ p ∈ T, (p : ℝ)⁻¹)⁻¹) ^ 2 *
        (∏ i, (∑ p ∈ R i, (p : ℝ)⁻¹)⁻¹) ^ 2 := by
  rw [doubledRole_normalizers]
  simp only [Fin.prod_univ_add, Fin.append_left, Fin.append_right, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, pow_one]
  ring

theorem bulk_top_normalizers_le {m c : ℕ} (B T : Finset ℕ) (R : Fin c → Finset ℕ)
    (L a b J : ℝ) (hL : 0 < L) (ha : 0 < a) (hb : 0 < b)
    (hB : a * L ≤ ∑ p ∈ B, (p : ℝ)⁻¹)
    (hT : b ≤ ∑ p ∈ T, (p : ℝ)⁻¹)
    (hR : ∀ i, Real.exp (-J) ≤ ∑ p ∈ R i, (p : ℝ)⁻¹) :
    (∏ i, (∑ p ∈ Fin.append
      (Fin.append (Fin.append (fun _ : Fin m => B) (fun _ : Fin 1 => T)) R)
      (Fin.append (Fin.append (fun _ : Fin m => B) (fun _ : Fin 1 => T)) R) i,
        (p : ℝ)⁻¹)⁻¹) ≤
      (a * L)⁻¹ ^ (2 * m) * b⁻¹ ^ 2 * Real.exp (2 * c * J) := by
  rw [bulk_top_normalizers]
  have hbi : (∑ p ∈ B, (p : ℝ)⁻¹)⁻¹ ≤ (a * L)⁻¹ :=
    inv_anti₀ (mul_pos ha hL) hB
  have hti : (∑ p ∈ T, (p : ℝ)⁻¹)⁻¹ ≤ b⁻¹ := inv_anti₀ hb hT
  have hri : (∏ i, (∑ p ∈ R i, (p : ℝ)⁻¹)⁻¹) ≤ Real.exp (c * J) := by
    calc
      _ ≤ ∏ _i : Fin c, Real.exp J := by
        apply Finset.prod_le_prod (fun i _ => by positivity)
        intro i _
        have h := inv_anti₀ (Real.exp_pos (-J)) (hR i)
        simpa only [Real.exp_neg, inv_inv] using h
      _ = _ := by simp [← Real.exp_nat_mul, mul_comm]
  have hn : 0 ≤ ∏ i, (∑ p ∈ R i, (p : ℝ)⁻¹)⁻¹ := by positivity
  calc
    _ ≤ (a * L)⁻¹ ^ (2 * m) * b⁻¹ ^ 2 * (Real.exp (c * J)) ^ 2 := by
      gcongr
    _ = _ := by rw [← Real.exp_nat_mul]; congr 2; ring

/-- Extra roles cost only a fixed power of the number of bulk positions. -/
theorem repeated_positions_power (m b : ℕ) (L z : ℝ) (hL : 0 < L)
    (hn : ((2 * m + b : ℕ) : ℝ) ≤ z * L) :
    L⁻¹ ^ (2 * m) * ((2 * m + b : ℕ) : ℝ) ^ (2 * m + b) ≤
      z ^ (2 * m) * ((2 * m + b : ℕ) : ℝ) ^ b := by
  have hn0 : (0 : ℝ) ≤ (2 * m + b : ℕ) := Nat.cast_nonneg _
  have hz : 0 ≤ z := by nlinarith
  have hr : ((2 * m + b : ℕ) : ℝ) / L ≤ z := (div_le_iff₀ hL).mpr hn
  calc
    _ = (((2 * m + b : ℕ) : ℝ) / L) ^ (2 * m) * ((2 * m + b : ℕ) : ℝ) ^ b := by
      rw [pow_add, div_pow, div_eq_mul_inv]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hr _) (by positivity)

/-- A fixed polynomial loss is absorbed before the gap is chosen. -/
theorem eventual_fixed_role_cost (b : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ m : ℕ in atTop, ((2 * m + b : ℕ) : ℝ) ^ b ≤ Real.exp (ε * m) := by
  have ht : Tendsto (fun x : ℝ => (2 * x + b) ^ b / Real.exp (ε * x)) atTop (nhds 0) := by
    have hp := (isLittleO_pow_exp_pos_mul_atTop b (div_pos hε (by norm_num : (0 : ℝ) < 2))).tendsto_div_nhds_zero
    have hc := hp.comp (tendsto_atTop_add_const_right _ (b : ℝ) (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2)))
    have he : ∀ x : ℝ, (2 * x + b) ^ b / Real.exp (ε * x) =
        Real.exp (ε / 2 * b) * ((2 * x + b) ^ b / Real.exp (ε / 2 * (2 * x + b))) := by
      intro x
      rw [show ε / 2 * (2 * x + b) = ε * x + ε / 2 * b by ring, Real.exp_add]
      field_simp
    simpa only [he, mul_zero, Function.comp_apply, id_eq] using hc.const_mul (Real.exp (ε / 2 * b))
  have hn := ht.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [hn.eventually_le_const (by norm_num : (0 : ℝ) < 1)] with m hm
  have h := (div_le_iff₀ (Real.exp_pos (ε * m))).mp hm
  simpa only [Function.comp_apply, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, one_mul] using h

/-- The bulk normalizers cancel the powers of L in the ordered-tuple cost. -/
theorem eventual_repeat_multiplicity_cost (b : ℕ) (a z : ℝ) (ha : 0 < a) (hz : 0 < z) :
    ∀ᶠ m : ℕ in atTop, ∀ L : ℝ, 0 < L → (m : ℝ) ≤ z * L → b ≤ m →
      (a * L)⁻¹ ^ (2 * m) * ((2 * m + b : ℕ) : ℝ) ^ (2 * m + b) ≤
        Real.exp ((2 * Real.log (3 * z / a) + 1) * m) := by
  filter_upwards [eventual_fixed_role_cost b 1 (by norm_num)] with m hm L hL hmL hbm
  have hnr : ((2 * m + b : ℕ) : ℝ) ≤ 3 * z * L := by
    have hb : (b : ℝ) ≤ m := by exact_mod_cast hbm
    push_cast
    nlinarith
  have hp := repeated_positions_power m b L (3 * z) hL hnr
  have hb := mul_le_mul_of_nonneg_left hp (show 0 ≤ (a⁻¹ : ℝ) ^ (2 * m) by positivity)
  have hpow : (3 * z / a) ^ (2 * m) = Real.exp (((2 * m : ℕ) : ℝ) * Real.log (3 * z / a)) := by
    rw [Real.exp_nat_mul, Real.exp_log (by positivity)]
  calc
    _ = a⁻¹ ^ (2 * m) * (L⁻¹ ^ (2 * m) * ((2 * m + b : ℕ) : ℝ) ^ (2 * m + b)) := by
      rw [mul_inv, mul_pow]
      ring
    _ ≤ a⁻¹ ^ (2 * m) * ((3 * z) ^ (2 * m) * ((2 * m + b : ℕ) : ℝ) ^ b) := hb
    _ = (3 * z / a) ^ (2 * m) * ((2 * m + b : ℕ) : ℝ) ^ b := by
      rw [div_eq_mul_inv, mul_pow]
      ring
    _ ≤ (3 * z / a) ^ (2 * m) * Real.exp (1 * m) :=
      mul_le_mul_of_nonneg_left hm (by positivity)
    _ = _ := by rw [hpow, ← Real.exp_add]; congr 1; push_cast; ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialRepeatRate
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exponential size of the actual repeated-prime error -/

namespace Ostmann

open Filter
open scoped BigOperators FourierTransform SchwartzMap Classical

theorem eventual_wordRepeatFactor_bound (c : ℕ) (a b z A C : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hz : 0 < z) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (ψ : 𝓢(ℝ, ℂ)) :
    ∀ᶠ m : ℕ in atTop, ∀ (L J D : ℝ), 0 < L →
      (m : ℝ) ≤ z * L → z * L ≤ 2 * m →
      ∀ (P B T : Finset ℕ) (R : Fin c → Finset ℕ),
      a * L ≤ ∑ p ∈ B, (p : ℝ)⁻¹ → b ≤ ∑ p ∈ T, (p : ℝ)⁻¹ →
      (∀ i, Real.exp (-J) ≤ ∑ p ∈ R i, (p : ℝ)⁻¹) → J ≤ A * L →
      (∑ p : P, (p : ℝ)⁻¹) ≤ C * L →
      wordRepeatFactor P (Fin.append (fun _ : Fin m => B) (fun _ : Fin 1 => T)) R ψ D ≤
        Real.exp ((2 * Real.log (3 * z / a) + 2 + (4 * c * A + 2 * C) / z) * m - D / 2) := by
  have hcst := (Real.tendsto_exp_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop
    (‖𝓕 ψ 0‖ * b⁻¹ ^ 2)
  filter_upwards [eventual_repeat_multiplicity_cost (2 + 2 * c) a z ha hz,
    eventually_ge_atTop (2 + 2 * c), hcst] with m hm hmc hconst L J D hL hmL hLm P B T R hB hT hR hJ hP
  change ‖𝓕 ψ 0‖ * b⁻¹ ^ 2 ≤ Real.exp (m : ℝ) at hconst
  have hnorm := bulk_top_normalizers_le (m := m) B T R L a b J hL ha hb hB hT hR
  have hmult := hm L hL hmL hmc
  have hn : (m + 1 + c) + (m + 1 + c) = 2 * m + (2 + 2 * c) := by omega
  have hmass : 2 * c * J + (∑ p : P, (p : ℝ)⁻¹) ≤ ((4 * c * A + 2 * C) / z) * m := by
    have h₁ := mul_le_mul_of_nonneg_left hJ (show 0 ≤ (2 : ℝ) * c by positivity)
    have h₂ := mul_le_mul_of_nonneg_left hLm (show 0 ≤ 2 * c * A + C by positivity)
    have hz' : (2 * c * A + C) * L ≤ ((4 * c * A + 2 * C) * m) / z := by
      apply (le_div_iff₀ hz).mpr
      nlinarith
    rw [div_mul_eq_mul_div]
    linarith
  unfold wordRepeatFactor
  have hpow : (((m + 1 + c) + (m + 1 + c) : ℕ) : ℝ) ^ ((m + 1 + c) + (m + 1 + c)) =
      ((2 * m + (2 + 2 * c) : ℕ) : ℝ) ^ (2 * m + (2 + 2 * c)) := by rw [hn]
  rw [hpow]
  calc
    _ ≤ ‖𝓕 ψ 0‖ * ((a * L)⁻¹ ^ (2 * m) * b⁻¹ ^ 2 * Real.exp (2 * c * J)) *
        ((2 * m + (2 + 2 * c) : ℕ) : ℝ) ^ (2 * m + (2 + 2 * c)) *
        Real.exp ((∑ p : P, (p : ℝ)⁻¹) - D / 2) := by
      gcongr
    _ = (‖𝓕 ψ 0‖ * b⁻¹ ^ 2) *
        ((a * L)⁻¹ ^ (2 * m) * ((2 * m + (2 + 2 * c) : ℕ) : ℝ) ^ (2 * m + (2 + 2 * c))) *
        Real.exp (2 * c * J + (∑ p : P, (p : ℝ)⁻¹) - D / 2) := by
      simp only [Real.exp_sub, Real.exp_add]
      ring
    _ ≤ Real.exp (m : ℝ) * Real.exp ((2 * Real.log (3 * z / a) + 1) * m) *
        Real.exp (((4 * c * A + 2 * C) / z) * m - D / 2) := by
      gcongr
    _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialGapRate
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Choosing the initial gap without changing the endpoint rate -/

namespace Ostmann

open Filter
open scoped BigOperators

theorem initial_repeat_coefficient (a z A C : ℝ) (c : ℕ)
    (ha : 0 < a) (hz : 1 ≤ z) (hC : 0 ≤ C) (hc : 4 * c * A ≤ z) :
    2 * Real.log (3 * z / a) + 2 + (4 * c * A + 2 * C) / z ≤
      2 * Real.log z + (2 * Real.log (3 / a) + 3 + 2 * C) := by
  have hz0 : 0 < z := by linarith
  have hr : (4 * c * A + 2 * C) / z ≤ 1 + 2 * C := by
    apply (div_le_iff₀ hz0).mpr
    nlinarith
  have he : 3 * z / a = (3 / a) * z := by ring
  rw [he, Real.log_mul (by positivity) hz0.ne']
  linarith

theorem initial_gap_rate (r K B₀ B_D z E : ℝ) (m : ℕ)
    (hz : 1 ≤ z) (hr : r ≤ 2 * Real.log z + K)
    (hE : E / 2 ≤ m) (hB : 2 * (K + B₀ + 2) ≤ B_D) :
    Real.exp (r * m - ((B_D + 20 * Real.log z) * m - E) / 2) ≤
      Real.exp (-(B₀ + 1) * m) := by
  apply Real.exp_le_exp.mpr
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hlog : 0 ≤ Real.log z := Real.log_nonneg hz
  have h₁ := mul_le_mul_of_nonneg_right hr hm0
  have h₂ := mul_le_mul_of_nonneg_right hB hm0
  nlinarith [mul_nonneg hlog hm0]

theorem exp_extra_unit_le_half (B : ℝ) (m : ℕ) (hm : 1 ≤ m) :
    Real.exp (-(B + 1) * m) ≤ Real.exp (-B * m) / 2 := by
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have he : (2 : ℝ) ≤ Real.exp (m : ℝ) := by
    linarith [Real.add_one_le_exp (m : ℝ)]
  have hi : (Real.exp (m : ℝ))⁻¹ ≤ (2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) he
  calc
    _ = Real.exp (-B * m) * (Real.exp (m : ℝ))⁻¹ := by
      rw [show -(B + 1) * (m : ℝ) = -B * m + -(m : ℝ) by ring, Real.exp_add, Real.exp_neg]
    _ ≤ Real.exp (-B * m) * (2 : ℝ)⁻¹ :=
      mul_le_mul_of_nonneg_left hi (Real.exp_pos _).le
    _ = _ := by ring

theorem initial_amplitude_uniform_lower (η : ℂ) (S R B : ℝ) (m : ℕ)
    (hm : 1 ≤ m) (hmain : Real.exp (-B * m) ≤ S)
    (herr : R ≤ Real.exp (-(B + 1) * m)) (hη : S - R ≤ ‖η‖) :
    Real.exp (-(B + 1) * m) ≤ ‖η‖ := by
  have hh := exp_extra_unit_le_half B m hm
  linarith

theorem eventually_bulkCount (z : ℝ) (hz : 0 < z) (F : ℕ → Prop)
    (hF : ∀ᶠ m : ℕ in atTop, F m) :
    ∀ᶠ L : ℝ in atTop, F ⌊z * L⌋₊ := by
  obtain ⟨M, hM⟩ := eventually_atTop.mp hF
  filter_upwards [eventually_ge_atTop ((M : ℝ) / z)] with L hL
  apply hM
  apply Nat.le_floor
  simpa only [mul_comm] using (div_le_iff₀ hz).mp hL

theorem eventually_bulkCount_bounds (z : ℝ) (hz : 0 < z) :
    ∀ᶠ L : ℝ in atTop, 0 < L ∧ 1 ≤ ⌊z * L⌋₊ ∧
      (⌊z * L⌋₊ : ℝ) ≤ z * L ∧ z * L ≤ 2 * ⌊z * L⌋₊ := by
  filter_upwards [eventually_ge_atTop (2 / z)] with L hL
  have h₂ : (2 : ℝ) ≤ z * L := by simpa only [mul_comm] using (div_le_iff₀ hz).mp hL
  have hLp : 0 < L := (div_pos (by norm_num : (0 : ℝ) < 2) hz).trans_le hL
  have hm : 1 ≤ ⌊z * L⌋₊ := (Nat.one_le_floor_iff (z * L)).mpr (by linarith)
  have hm' : (1 : ℝ) ≤ ⌊z * L⌋₊ := by exact_mod_cast hm
  exact ⟨hLp, hm, Nat.floor_le (by positivity), by linarith [Nat.lt_floor_add_one (z * L)]⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_InitialIntervalZero
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A nontrivial original interval removes the initial zero frequency -/
namespace Ostmann
open scoped Classical

theorem fullAtomTransferWeight_zero_of_interval {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (lo hi : I → ℕ)
    (childBound pivotBound : ℕ → ℕ) (leaf : ScheduleAtomState role → ℤ → ℂ)
    (i : I) (hi₁ : 1 < lo i) (x : CopyScheduleAtoms role 0 → ℕ) :
    fullAtomTransferWeight role childBound pivotBound (atomIntervalRanges role lo hi)
      leaf 0 x (0 : ℤ) = 0 := by
  by_contra h
  have hu := (fullAtomTransferWeight_top_support role childBound pivotBound
    (atomIntervalRanges role lo hi) leaf 0 x (0 : ℤ) h).2 ⟨i, trivial⟩
  have he : x ⟨i, trivial⟩ = 1 := by
    simpa only [frequencyRoot, Int.natAbs_zero, Nat.coprime_zero_right] using hu
  have hr := (atomIntervalRanges_holds_iff role lo hi 0 x).mp
    (fun r hr => fullAtomTransferWeight_top_range role childBound pivotBound
      (atomIntervalRanges role lo hi) leaf 0 x (0 : ℤ) h r hr)
  have hl := (hr ⟨i, trivial⟩).1
  change lo i ≤ x ⟨i, trivial⟩ at hl
  omega

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterPrimeFrequency
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Natural character-frequency cutoffs lie below the actual prime ranges -/
namespace Ostmann
open Filter

/-- A fixed depth has a linear exponent, including the rounded bottom cutoff
with its original factor two in front of sqrt(m). -/
theorem transferErrorScale_linear_bound (k j : ℕ) (d m : ℝ)
    (hj : j ≤ k) (hd : 0 ≤ d) (hm : 1 ≤ m) :
    transferErrorScale (d * m) m j ≤ ((2 : ℝ) ^ k * d + 2 * (4 : ℝ) ^ k) * m := by
  have hs : Real.sqrt m ≤ m := (Real.sqrt_le_iff).mpr ⟨by linarith, by nlinarith⟩
  have htwo : (2 : ℝ) ^ j ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hj
  have hfour : (4 : ℝ) ^ j ≤ 4 ^ k := pow_le_pow_right₀ (by norm_num) hj
  have hfirst := mul_le_mul_of_nonneg_right htwo (mul_nonneg hd (by linarith : 0 ≤ m))
  have hsecond := mul_le_mul hfour hs (Real.sqrt_nonneg _) (by positivity : (0 : ℝ) ≤ 4 ^ k)
  unfold transferErrorScale
  nlinarith only [hfirst, hsecond]

/-- This supplies both the prime-frequency separation and the finite powers
of the cutoff used for denominator removal in the selected energy estimate. -/
theorem eventual_natural_cutoff_power_lt (k r : ℕ) (d z α c : ℝ)
    (hd : 0 ≤ d) (_hz : 0 ≤ z) (hα : 0 < α) (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop, ∀ m : ℝ, 1 ≤ m → m ≤ z * L → ∀ j ≤ k,
      (((naturalTransferCutoff (d * m) m j) ^ r : ℕ) : ℝ) <
        Real.exp (c * Real.exp (α * L)) := by
  let D := (2 : ℝ) ^ k * d + 2 * (4 : ℝ) ^ k
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hb := ((isLittleO_pow_exp_pos_mul_atTop 1 hα).const_mul_left ((r : ℝ) * D * z)).bound
    (by positivity : 0 < c / 2)
  filter_upwards [hb] with L hL m hm hmL j hj
  have hlin : (r : ℝ) * D * z * L < c * Real.exp (α * L) := by
    have hh : |(r : ℝ) * D * z * L| ≤ c / 2 * Real.exp (α * L) := by
      simpa only [Real.norm_eq_abs, pow_one, abs_of_pos (Real.exp_pos _)] using hL
    have hn := le_abs_self ((r : ℝ) * D * z * L)
    nlinarith only [hh, hn, Real.exp_pos (α * L), hc]
  have hscale := transferErrorScale_linear_bound k j d m hj hd hm
  have hm' := mul_le_mul_of_nonneg_left hmL (mul_nonneg (Nat.cast_nonneg r) hD)
  have he : (r : ℝ) * transferErrorScale (d * m) m j < c * Real.exp (α * L) := by
    change transferErrorScale (d * m) m j ≤ D * m at hscale
    have hs := mul_le_mul_of_nonneg_left hscale (Nat.cast_nonneg (α := ℝ) r)
    nlinarith only [hs, hm', hlin]
  calc
    _ = (naturalTransferCutoff (d * m) m j : ℝ) ^ r := by simp only [Nat.cast_pow]
    _ ≤ (Real.exp (transferErrorScale (d * m) m j)) ^ r :=
      pow_le_pow_left₀ (Nat.cast_nonneg _)
        (Nat.floor_le (Real.exp_pos _).le) r
    _ = Real.exp ((r : ℝ) * transferErrorScale (d * m) m j) := (Real.exp_nat_mul _ _).symm
    _ < _ := Real.exp_lt_exp.mpr he

theorem eventual_natural_cutoff_below_primes (k : ℕ) (d z α c : ℝ)
    (hd : 0 ≤ d) (hz : 0 ≤ z) (hα : 0 < α) (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop, ∀ m : ℝ, 1 ≤ m → m ≤ z * L →
      ∀ p : ℕ, Real.exp (c * Real.exp (α * L)) ≤ p →
        ∀ j ≤ k, naturalTransferCutoff (d * m) m j < p := by
  filter_upwards [eventual_natural_cutoff_power_lt k 1 d z α c hd hz hα hc] with L hL
  intro m hm hmL p hp j hj
  have hh := (hL m hm hmL j hj).trans_le hp
  simpa only [pow_one, Nat.cast_lt] using hh

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SelectedBulkCoordinates
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bulk coordinates inside a larger word

The selected bulk slots are copied with the whole word. The top slot is
retained in that word but belongs to the complementary matching block.
-/
namespace Ostmann
open scoped Classical

/-- An H slot over an original bulk position is one of the selected leaves. -/
theorem mem_selectedBulkH_of_origin {I : Type*} (role : I → CopyScheduleRole)
    (n m : ℕ) (bulk : Fin m ↪ I) (hbulk : ∀ i, role (bulk i) = .word)
    (h : CopyScheduleH role n) (i : Fin m) (hi : copyScheduleOrigin n h.val = bulk i) :
    h ∈ Set.range (selectedBulkH role n m bulk hbulk) := by
  have hw : copyScheduleRole role n h.val = .word :=
    copyScheduleRole_origin_word role n h.val (hi ▸ hbulk i)
  obtain ⟨t, j, hj, he⟩ := surviving_word_is_path role n h.val h.property.1 hw
  have hji : j = bulk i := by
    have hh := congrArg (copyScheduleOrigin n) he
    simpa only [copyScheduleOrigin_path, hi] using hh.symm
  subst j
  refine ⟨((scheduledPathEnumeration n).symm t, i), ?_⟩
  apply Subtype.ext
  change copySchedulePath n (scheduledPathEnumeration n ((scheduledPathEnumeration n).symm t))
    (bulk i) = h.val
  simpa only [Equiv.apply_symm_apply] using he.symm

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterSelectedBulk
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original m bulk primes exclude the one top prime of each word -/
namespace Ostmann
open scoped Classical BigOperators

theorem character_word_not_bulk {k : ℕ} (m : ℕ) (r : Fin k → ℕ) (f : ℕ)
    (i : Σ v, Fin (characterSize m r f v))
    (hw : characterRole k i.1 = .word) (hb : i ∉ Set.range (characterBulk m r f)) :
    i = characterTop m r f := by
  obtain ⟨t, ht⟩ := (characterWordEquiv m r f).surjective ⟨i, hw⟩
  have hti : (⟨(true, none), t⟩ : Σ v, Fin (characterSize m r f v)) = i :=
    congrArg Subtype.val ht
  rw [← hti] at hb ⊢
  by_cases hz : t = 0
  · subst t
    rfl
  · obtain ⟨j, hj⟩ := Fin.eq_succ_of_ne_zero hz
    subst t
    exact False.elim (hb ⟨j, rfl⟩)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialWordPriorIntervals
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The nonword interval guards already hold under the original prime law -/
namespace Ostmann
open scoped Classical BigOperators

theorem initialWordTuple_cell_set {C : Type*} (k m : ℕ) (s : C → ℕ)
    (cell : (Σ c, Fin (s c)) ≃ Fin m)
    (Q : Fin k → Finset ℕ) (R : Fin m → Finset ℕ)
    (b : Bool) (c : C) (i : Fin (s c)) :
    Fin.append (Fin.append Q R) (Fin.append Q R)
      (initialWordTupleEquiv k m s cell ⟨(b, some c), i⟩) = R (cell ⟨c, i⟩) := by
  cases b with
  | false =>
    change Fin.append (Fin.append Q R) (Fin.append Q R)
      ((cell ⟨c, i⟩).natAdd k |>.natAdd (k + m)) = _
    simp only [Fin.append_right]
  | true =>
    change Fin.append (Fin.append Q R) (Fin.append Q R)
      ((cell ⟨c, i⟩).natAdd k |>.castAdd (k + m)) = _
    simp only [Fin.append_left, Fin.append_right]

theorem initialWordPrior_cell_product_bounds {C : Type*} [Fintype C]
    (k m : ℕ) (s : C → ℕ) (cell : (Σ c, Fin (s c)) ≃ Fin m)
    (P : Finset ℕ) (Q : Fin k → Finset ℕ) (R : Fin m → Finset ℕ)
    (lo hi : (Σ c, Fin (s c)) → ℕ)
    (hcell : ∀ i q, q ∈ R (cell i) → lo i ≤ q ∧ q ≤ hi i)
    (x : (Σ v : Bool × Option C, Fin (initialWordSize k s v.2)) → P)
    (hx : (∏ i, primeSubsetPrior P
      (Fin.append (Fin.append Q R) (Fin.append Q R)
        (initialWordTupleEquiv k m s cell i)) (x i)) ≠ 0) :
    ∀ (b : Bool) (c : C),
      (∏ i, lo ⟨c, i⟩) ≤ ∏ i, (x ⟨(b, some c), i⟩ : ℕ) ∧
      (∏ i, (x ⟨(b, some c), i⟩ : ℕ)) ≤ ∏ i, hi ⟨c, i⟩ := by
  intro b c
  have hs (i : Fin (s c)) : lo ⟨c, i⟩ ≤ (x ⟨(b, some c), i⟩ : ℕ) ∧
      (x ⟨(b, some c), i⟩ : ℕ) ≤ hi ⟨c, i⟩ := by
    apply hcell
    have hp := primeSubsetPrior_support P _ (x ⟨(b, some c), i⟩)
      ((Finset.prod_ne_zero_iff.mp hx) ⟨(b, some c), i⟩ (Finset.mem_univ _))
    simpa only [initialWordTuple_cell_set] using hp
  exact ⟨Finset.prod_le_prod' (fun i _ => (hs i).1),
    Finset.prod_le_prod' (fun i _ => (hs i).2)⟩

theorem initialWordPrior_atomIntervals_equiv {C : Type*} [Fintype C]
    (role : Bool × Option C → CopyScheduleRole)
    (k m j : ℕ) (s : C → ℕ) (cell : (Σ c, Fin (s c)) ≃ Fin m)
    (P : Finset ℕ) (Q : Fin k → Finset ℕ) (R : Fin m → Finset ℕ)
    (lo hi : (Σ c, Fin (s c)) → ℕ)
    (hcell : ∀ i q, q ∈ R (cell i) → lo i ≤ q ∧ q ≤ hi i)
    (x : (Σ v : Bool × Option C, Fin (initialWordSize k s v.2)) → P)
    (hx : (∏ i, primeSubsetPrior P
      (Fin.append (Fin.append Q R) (Fin.append Q R)
        (initialWordTupleEquiv k m s cell i)) (x i)) ≠ 0) :
    (∀ r ∈ atomIntervalRanges role
      (initialWordAtomLower j (fun c => ∏ i, lo ⟨c, i⟩))
      (initialWordAtomUpper j (fun c => ∏ i, hi ⟨c, i⟩)) 0,
      r.Holds (fun v => ∏ i, (x ⟨v.val, i⟩ : ℕ))) ↔
    ∀ r ∈ initialWordBinRanges role j,
      r.Holds (fun v => ∏ i, (x ⟨v.val, i⟩ : ℕ)) :=
  initialWordAtomIntervals_equiv role j _ _ _
    (initialWordPrior_cell_product_bounds k m s cell P Q R lo hi hcell x hx)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterFullPrimeCells
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original signed product law from its word and nonword prime cells -/
namespace Ostmann
open scoped Classical BigOperators

theorem characterFullPrimeCells_subset {k : ℕ} (m : ℕ) (r : Fin k → ℕ) (f : ℕ)
    (P : Finset ℕ) (Q : Fin (m + 1) → Finset ℕ)
    (R : (v : CharacterCell k) → Fin (characterCellSize r f v) → Finset ℕ)
    (hQ : ∀ i, Q i ⊆ P) (hR : ∀ v i, R v i ⊆ P) :
    ∀ i, characterFullPrimeCells m r f Q R i ⊆ P := by
  rintro ⟨⟨b, v⟩, i⟩
  cases v with
  | none => exact hQ i
  | some v => exact hR v i

/-- This equality identifies the literal scheduled law with the two copies
of the original word followed by the flattened nonword cells. -/
theorem characterFullPrimeCells_source {k : ℕ} (m nc : ℕ) (r : Fin k → ℕ) (f : ℕ)
    (cell : (Σ v, Fin (characterCellSize r f v)) ≃ Fin nc)
    (Q : Fin (m + 1) → Finset ℕ)
    (R : (v : CharacterCell k) → Fin (characterCellSize r f v) → Finset ℕ)
    (i : Σ v, Fin (characterSize m r f v)) :
    Fin.append
      (Fin.append Q (fun j => R (cell.symm j).1 (cell.symm j).2))
      (Fin.append Q (fun j => R (cell.symm j).1 (cell.symm j).2))
      (initialWordTupleEquiv (m + 1) nc (characterCellSize r f) cell i) =
        characterFullPrimeCells m r f Q R i := by
  rcases i with ⟨⟨b, v⟩, i⟩
  cases v with
  | none =>
    cases b with
    | false =>
      change Fin.append
        (Fin.append Q (fun j => R (cell.symm j).1 (cell.symm j).2))
        (Fin.append Q (fun j => R (cell.symm j).1 (cell.symm j).2))
        ((((show Fin (m + 1) from i).castAdd nc).natAdd ((m + 1) + nc))) = Q i
      rw [Fin.append_right]
      exact Fin.append_left Q _ (show Fin (m + 1) from i)
    | true =>
      change Fin.append
        (Fin.append Q (fun j => R (cell.symm j).1 (cell.symm j).2))
        (Fin.append Q (fun j => R (cell.symm j).1 (cell.symm j).2))
        ((((show Fin (m + 1) from i).castAdd nc).castAdd ((m + 1) + nc))) = Q i
      rw [Fin.append_left]
      exact Fin.append_left Q _ (show Fin (m + 1) from i)
  | some v =>
    have h := initialWordTuple_cell_set (m + 1) nc
      (characterCellSize r f) cell Q (fun j => R (cell.symm j).1 (cell.symm j).2) b v i
    rw [cell.symm_apply_apply] at h
    exact h

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterPriorMass
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Harmonic mass floors for every original signed character marginal -/
namespace Ostmann
open Filter
open scoped Classical BigOperators

/-- The bulk has linear mass, the top shell has fixed positive mass, and all
remaining selected cells already have the proved exponential mass floor. -/
theorem eventual_full_character_mass_floor (a b C : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hC : 0 < C) :
    ∀ᶠ L : ℝ in atTop, ∀ (k m : ℕ) (r : Fin k → ℕ) (f : ℕ)
      (Q : Fin (m + 1) → Finset ℕ)
      (R : (v : CharacterCell k) → Fin (characterCellSize r f v) → Finset ℕ),
      b ≤ ∑ p ∈ Q 0, (p : ℝ)⁻¹ →
      (∀ i : Fin m, a * L ≤ ∑ p ∈ Q i.succ, (p : ℝ)⁻¹) →
      (∀ v i, Real.exp (-C * L) ≤ ∑ p ∈ R v i, (p : ℝ)⁻¹) →
      ∀ i, Real.exp (-C * L) ≤
        ∑ p ∈ characterFullPrimeCells m r f Q R i, (p : ℝ)⁻¹ := by
  have he : ∀ᶠ L : ℝ in atTop, Real.exp (-C * L) ≤ min a b :=
    ((Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_id.const_mul_atTop hC)).eventually_le_const (lt_min ha hb)).mono (by
        intro L hL
        simpa only [Function.comp_apply, id_eq, neg_mul] using hL)
  filter_upwards [he, eventually_ge_atTop (1 : ℝ)] with L he hL
  intro k m r f Q R htop hbulk hrest
  have hword (i : Fin (m + 1)) : Real.exp (-C * L) ≤ ∑ p ∈ Q i, (p : ℝ)⁻¹ := by
    refine Fin.cases ?_ (fun j => ?_) i
    · exact (he.trans (min_le_right _ _)).trans htop
    · have hh : a ≤ a * L := by nlinarith only [ha, hL]
      exact ((he.trans (min_le_left _ _)).trans hh).trans (hbulk j)
  rintro ⟨⟨sgn, v⟩, i⟩
  cases v with
  | none => exact hword i
  | some v => exact hrest v i

theorem harmonic_mass_inv_le_exp (Q : Finset ℕ) (C L : ℝ)
    (hQ : Real.exp (-C * L) ≤ ∑ p ∈ Q, (p : ℝ)⁻¹) :
    (∑ p ∈ Q, (p : ℝ)⁻¹)⁻¹ ≤ Real.exp (C * L) := by
  have h := inv_anti₀ (Real.exp_pos (-C * L)) hQ
  simpa only [← Real.exp_neg, neg_mul, neg_neg] using h

theorem harmonic_mass_inv_energy_budget (Q : Finset ℕ) (C L M : ℝ)
    (hC : 0 ≤ C) (hLM : L ≤ M)
    (hQ : Real.exp (-C * L) ≤ ∑ p ∈ Q, (p : ℝ)⁻¹) :
    (∑ p ∈ Q, (p : ℝ)⁻¹)⁻¹ ≤ Real.exp (C * (1 + M)) := by
  apply (harmonic_mass_inv_le_exp Q C L hQ).trans
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by linarith) hC)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_FiniteEnumeration
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # An explicit bridge between equivalent finite enumerations -/

namespace Ostmann

theorem finite_univ_canonical {A : Type*} [Finite A] (F : Fintype A) :
    @Finset.univ A F = @Finset.univ A (Fintype.ofFinite A) := by
  cases Subsingleton.elim F (Fintype.ofFinite A)
  rfl

theorem finset_sdiff_canonical {A : Type*} (d : DecidableEq A) (s t : Finset A) :
    @SDiff.sdiff (Finset A) (@Finset.instSDiff A d) s t =
      @SDiff.sdiff (Finset A) (@Finset.instSDiff A (Classical.decEq A)) s t := by
  cases Subsingleton.elim d (Classical.decEq A)
  rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ConstituentMatchingEnergy
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual matching contribution retains one H prior and sharp history energy -/

namespace Ostmann
open scoped BigOperators Classical ComplexConjugate

theorem primePermutationCorrelation_split {H D : Type*} [Fintype H] [Fintype D]
    (P : Finset ℕ) (v : D → ℤ) (c : ((H → P) × D) → ℂ) :
    primePermutationCorrelation P v c =
      ∑ e : Equiv.Perm H, ∑ d : D, ∑ d' : D,
        if v d = v d' then ∑ l : H → P, c (l, d) * conj (c (l ∘ e.symm, d')) else 0 := by
  unfold primePermutationCorrelation
  apply Finset.sum_congr rfl
  intro e _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d' _
  split_ifs <;> simp

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_MatchedCellSupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Disjoint prime cells force every nonzero matching to preserve its cell -/

namespace Ostmann
open scoped Classical BigOperators

theorem matched_prior_preserves_cell {H K : Type*} [Fintype H]
    (P : Finset ℕ) (Q : H → Finset ℕ) (label : H → K)
    (hdisjoint : ∀ i j, label i ≠ label j → Disjoint (Q i) (Q j))
    (e : Equiv.Perm H) (x : H → P)
    (hx : (∏ i, primeSubsetPrior P (Q i) (x i)) ≠ 0)
    (he : (∏ i, primeSubsetPrior P (Q i) (x (e i))) ≠ 0) :
    ∀ i, label (e i) = label i := by
  intro i
  by_contra hn
  have h₁ : (x (e i) : ℕ) ∈ Q (e i) := primeSubsetPrior_support P _ _
    ((Finset.prod_ne_zero_iff.mp hx) (e i) (Finset.mem_univ _))
  have h₂ : (x (e i) : ℕ) ∈ Q i := primeSubsetPrior_support P _ _
    ((Finset.prod_ne_zero_iff.mp he) i (Finset.mem_univ _))
  exact Finset.disjoint_left.mp (hdisjoint (e i) i hn) h₁ h₂

theorem matched_prior_zero_of_changes_cell {H K : Type*} [Fintype H]
    (P : Finset ℕ) (Q : H → Finset ℕ) (label : H → K)
    (hdisjoint : ∀ i j, label i ≠ label j → Disjoint (Q i) (Q j))
    (e : Equiv.Perm H) (hchange : ∃ i, label (e i) ≠ label i)
    (x : H → P) :
    (∏ i, primeSubsetPrior P (Q i) (x i)) *
      (∏ i, primeSubsetPrior P (Q i) (x (e i))) = 0 := by
  by_contra hn
  have h := mul_ne_zero_iff.mp hn
  obtain ⟨i, hi⟩ := hchange
  exact hi (matched_prior_preserves_cell P Q label hdisjoint e x h.1 h.2 i)

theorem matched_correlation_zero_of_changes_cell {H K : Type*} [Fintype H]
    (P : Finset ℕ) (Q : H → Finset ℕ) (label : H → K)
    (hdisjoint : ∀ i j, label i ≠ label j → Disjoint (Q i) (Q j))
    (e : Equiv.Perm H) (hchange : ∃ i, label (e i) ≠ label i)
    (F : (H → P) → ℂ) :
    (∑ x : H → P, ((∏ i, primeSubsetPrior P (Q i) (x i) : ℝ) : ℂ) *
      ((∏ i, primeSubsetPrior P (Q i) (x (e i)) : ℝ) : ℂ) * F x) = 0 := by
  apply Finset.sum_eq_zero
  intro x _
  rw [← Complex.ofReal_mul, matched_prior_zero_of_changes_cell P Q label hdisjoint e hchange x,
    Complex.ofReal_zero, zero_mul]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_PrimeMatchingSupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Restricting the actual diagonal to cell-preserving matchings -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

theorem primePermutationCorrelation_fintype {H D : Type*} [Finite H] [Finite D]
    (fH : Fintype H) (fD : Fintype D)
    (P : Finset ℕ) (v : D → ℤ) (c : ((H → P) × D) → ℂ) :
    @primePermutationCorrelation H D fH fD P v c =
      @primePermutationCorrelation H D (Fintype.ofFinite H) (Fintype.ofFinite D) P v c := by
  cases Subsingleton.elim fH (Fintype.ofFinite H)
  cases Subsingleton.elim fD (Fintype.ofFinite D)
  rfl

theorem primeMatchingContribution_fintype {H D : Type*} [Finite H] [Finite D]
    (fH : Fintype H) (fD : Fintype D)
    (P : Finset ℕ) (v : D → ℤ) (c : ((H → P) × D) → ℂ) (e : Equiv.Perm H) :
    @primeMatchingContribution H D fH fD P v c e =
      @primeMatchingContribution H D (Fintype.ofFinite H) (Fintype.ofFinite D) P v c e := by
  cases Subsingleton.elim fH (Fintype.ofFinite H)
  cases Subsingleton.elim fD (Fintype.ofFinite D)
  rfl

theorem cellPreservingMatchings_fintype {H K : Type*} [Finite H]
    (fH : Fintype H) (label : H → K) :
    @cellPreservingMatchings H K fH label =
      @cellPreservingMatchings H K (Fintype.ofFinite H) label := by
  cases Subsingleton.elim fH (Fintype.ofFinite H)
  rfl

theorem primeMatchingContribution_zero_of_changes_cell
    {H D K : Type*} [Fintype H] [Fintype D]
    (P : Finset ℕ) (Q : H → Finset ℕ) (label : H → K)
    (hdisjoint : ∀ i j, label i ≠ label j → Disjoint (Q i) (Q j))
    (v : D → ℤ) (c F : ((H → P) × D) → ℂ)
    (hc : ∀ l d, c (l, d) = ((∏ h, primeSubsetPrior P (Q h) (l h) : ℝ) : ℂ) * F (l, d))
    (e : Equiv.Perm H) (he : e ∉ cellPreservingMatchings label) :
    primeMatchingContribution P v c e = 0 := by
  have hn : ∃ i, label (e i) ≠ label i := by
    simpa only [mem_cellPreservingMatchings, not_forall] using he
  obtain ⟨i, hi⟩ := hn
  have hsymm : ∃ j, label (e.symm j) ≠ label j :=
    ⟨e i, by simpa only [e.symm_apply_apply] using hi.symm⟩
  unfold primeMatchingContribution
  apply Finset.sum_eq_zero
  intro d _
  apply Finset.sum_eq_zero
  intro d' _
  split_ifs
  · convert matched_correlation_zero_of_changes_cell P Q label hdisjoint e.symm hsymm
      (fun l => F (l, d) * conj (F (l ∘ e.symm, d'))) using 1
    all_goals try with_reducible_and_instances rfl
    apply Finset.sum_congr rfl
    intro l _
    rw [hc, hc]
    simp only [map_mul, Complex.conj_ofReal, Function.comp_apply]
    ring
  · rfl

theorem primePermutationCorrelation_cell_support
    {H D K : Type*} [Fintype H] [Fintype D]
    (P : Finset ℕ) (Q : H → Finset ℕ) (label : H → K)
    (hdisjoint : ∀ i j, label i ≠ label j → Disjoint (Q i) (Q j))
    (v : D → ℤ) (c F : ((H → P) × D) → ℂ)
    (hc : ∀ l d, c (l, d) = ((∏ h, primeSubsetPrior P (Q h) (l h) : ℝ) : ℂ) * F (l, d)) :
    primePermutationCorrelation P v c =
      ∑ e ∈ cellPreservingMatchings label, primeMatchingContribution P v c e := by
  rw [primePermutationCorrelation_split]
  exact (Finset.sum_subset (Finset.subset_univ _) (fun e _ he =>
    primeMatchingContribution_zero_of_changes_cell P Q label hdisjoint v c F hc e he)).symm

theorem primePermutationCorrelation_cell_split
    {H D K : Type*} [Fintype H] [Fintype D]
    (P : Finset ℕ) (Q : H → Finset ℕ) (label : H → K)
    (hdisjoint : ∀ i j, label i ≠ label j → Disjoint (Q i) (Q j))
    (v : D → ℤ) (c F : ((H → P) × D) → ℂ)
    (hc : ∀ l d, c (l, d) = ((∏ h, primeSubsetPrior P (Q h) (l h) : ℝ) : ℂ) * F (l, d))
    (S : Finset (Equiv.Perm H)) (hS : S ⊆ cellPreservingMatchings label) :
    primePermutationCorrelation P v c =
      (∑ e ∈ S, primeMatchingContribution P v c e) +
      ∑ e ∈ cellPreservingMatchings label \ S, primeMatchingContribution P v c e := by
  rw [primePermutationCorrelation_cell_support P Q label hdisjoint v c F hc]
  exact (Finset.sum_sdiff hS).symm.trans (add_comm _ _)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ConstituentDiagonalSupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact bad/good splitting of the original-prior pivot diagonal -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

section
variable {I D K : Type*} [Fintype I] [Fintype D]
variable (role : I → CopyScheduleRole) (size : I → ℕ)
variable (χ : (Σ i, Fin (size i)) → ∀ p : ℕ, DirichletCharacter ℂ p)
variable (κ : (Σ i, Fin (size i)) → ℕ → ℂ) (pivot : ℕ → (Σ i, Fin (size i)))
variable (n : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
variable (Q : (Σ i, Fin (size i)) → Finset ℕ)
variable (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
variable (leaf : ScheduleAtomState role → ℤ → ℂ) (hist : D → FrequencyTree ℤ n)

theorem constituentCharacterCorrelation_cell_split
    (label : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → K)
    (hdisjoint : ∀ i j, label i ≠ label j →
      Disjoint (Q (copyScheduleOrigin n i.val)) (Q (copyScheduleOrigin n j.val)))
    (u : CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n → P) (M : ℕ)
    (S : Finset (Equiv.Perm (CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n)))
    (hS : S ⊆ cellPreservingMatchings label) :
    let c := constituentCharacterCoefficient role size χ κ pivot n P hP Q
      childBound pivotBound ranges leaf hist u M
    primePermutationCorrelation P (fun d => frequencyRoot n (hist d)) c =
      (∑ e ∈ S, primeMatchingContribution P (fun d => frequencyRoot n (hist d)) c e) +
      ∑ e ∈ cellPreservingMatchings label \ S,
        primeMatchingContribution P (fun d => frequencyRoot n (hist d)) c e := by
  intro c
  generalize hcf : c = c'
  let H := CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n
  let : Fintype H := Fintype.ofFinite H
  let : Fintype D := Fintype.ofFinite D
  let F : ((H → P) × D) → ℂ :=
    constituentCharacterCore role size χ κ pivot n P hP childBound pivotBound ranges leaf hist u M
  have hc (l : H → P) (d : D) : c' (l, d) =
      ((∏ h, primeSubsetPrior P (Q (copyScheduleOrigin n h.val)) (l h) : ℝ) : ℂ) * F (l, d) := by
    rw [← hcf]
    simpa only [finite_univ_canonical] using
      (constituentCharacterCoefficient_factor role size χ κ pivot n P hP Q
        childBound pivotBound ranges leaf hist u M (l, d))
  have hS' : S ⊆ cellPreservingMatchings label := by
    simpa only [cellPreservingMatchings_fintype] using hS
  have hs := primePermutationCorrelation_cell_split P
    (fun h : H => Q (copyScheduleOrigin n h.val)) label hdisjoint
    (fun d => frequencyRoot n (hist d)) c' F hc S hS'
  simpa only [primePermutationCorrelation_fintype, primeMatchingContribution_fintype,
    cellPreservingMatchings_fintype, finset_sdiff_canonical] using hs

theorem constituentPivotDiagonal_cell_split
    (label : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → K)
    (hdisjoint : ∀ i j, label i ≠ label j →
      Disjoint (Q (copyScheduleOrigin n i.val)) (Q (copyScheduleOrigin n j.val)))
    (center : ∀ p : ℕ, ZMod p)
    (u : CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n → P) (M : ℕ)
    (hzero : ∀ x, fullAtomTransferWeight role childBound pivotBound ranges leaf 0 x (0 : ℤ) = 0)
    (hsmall : ∀ d p, p ∈ P → (frequencyRoot n (hist d)).natAbs < p)
    (S : Finset (Equiv.Perm (CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n)))
    (hS : S ⊆ cellPreservingMatchings label) :
    let c := constituentCharacterCoefficient role size χ κ pivot n P hP Q
      childBound pivotBound ranges leaf hist u M
    constituentPivotDiagonal role size χ κ pivot n P hP Q
      childBound pivotBound ranges leaf hist center u M =
      (∑ e ∈ S, primeMatchingContribution P (fun d => frequencyRoot n (hist d)) c e) +
      ∑ e ∈ cellPreservingMatchings label \ S,
        primeMatchingContribution P (fun d => frequencyRoot n (hist d)) c e := by
  exact (constituentPivotDiagonal_characters role size χ κ pivot n P hP Q
    childBound pivotBound ranges leaf hist center u M hzero hsmall).trans
    (constituentCharacterCorrelation_cell_split role size χ κ pivot n P hP Q
      childBound pivotBound ranges leaf hist label hdisjoint u M S hS)

theorem constituentPivotDiagonal_average_split
    (label : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → K)
    (hdisjoint : ∀ i j, label i ≠ label j →
      Disjoint (Q (copyScheduleOrigin n i.val)) (Q (copyScheduleOrigin n j.val)))
    (center : ∀ p : ℕ, ZMod p) (M : ℕ)
    (hzero : ∀ x, fullAtomTransferWeight role childBound pivotBound ranges leaf 0 x (0 : ℤ) = 0)
    (hsmall : ∀ d p, p ∈ P → (frequencyRoot n (hist d)).natAbs < p)
    (S : Finset (Equiv.Perm (CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n)))
    (hS : S ⊆ cellPreservingMatchings label) :
    (∑ u : CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n → P,
      ((∏ y, primeSubsetPrior P (Q (copyScheduleOrigin n y.val)) (u y) : ℝ) : ℂ) *
      constituentPivotDiagonal role size χ κ pivot n P hP Q
        childBound pivotBound ranges leaf hist center u M) =
    constituentMatchingFamily role size χ κ pivot n P hP Q childBound pivotBound ranges leaf hist S M +
    constituentMatchingFamily role size χ κ pivot n P hP Q childBound pivotBound ranges leaf hist
      (cellPreservingMatchings label \ S) M := by
  simp_rw [constituentPivotDiagonal_cell_split role size χ κ pivot n P hP Q childBound pivotBound
    ranges leaf hist label hdisjoint center _ M hzero hsmall S hS, mul_add]
  exact Finset.sum_add_distrib

end
end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_FullAtomProductBounds
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Whole-atom products on every nonzero fixed-pivot history -/
namespace Ostmann
open scoped Classical BigOperators

theorem fullAtomTransferWeight_inserted_H_product_bounds {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (size : I → ℕ) (n : ℕ)
    (childBound pivotBound : ℕ → ℕ) (lo hi : I → ℕ)
    (leaf : ScheduleAtomState role → ℤ → ℂ) (t : FrequencyTree ℤ n)
    (l : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → ℕ)
    (u : CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n → ℕ) (M : ℕ)
    (hw : fullAtomTransferWeight role childBound pivotBound (atomIntervalRanges role lo hi) leaf n
      (scheduledInsertedAtoms role n M
        (fun h => ∏ k, l (constituentH role size n h k))
        (fun y => ∏ k, u (constituentY role size n y k))) t ≠ 0) :
    (∏ h : CopyScheduleH role n, lo (copyScheduleOrigin n h.val)) ≤ (∏ h, l h) ∧
      (∏ h, l h) ≤ ∏ h : CopyScheduleH role n, hi (copyScheduleOrigin n h.val) := by
  have hr := (atomIntervalRanges_holds_iff role lo hi n _).mp
    (fun r hr => fullAtomTransferWeight_top_range role childBound pivotBound
      (atomIntervalRanges role lo hi) leaf n _ t hw r hr)
  have hh (h : CopyScheduleH role n) :
      lo (copyScheduleOrigin n h.val) ≤ ∏ k, l (constituentH role size n h k) ∧
      (∏ k, l (constituentH role size n h k)) ≤ hi (copyScheduleOrigin n h.val) := by
    simpa only [scheduledInsertedAtoms_H] using hr ⟨h.val, h.property.1⟩
  rw [← constituentH_product role size n l]
  exact ⟨Finset.prod_le_prod' (fun h _ => (hh h).1),
    Finset.prod_le_prod' (fun h _ => (hh h).2)⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SelectedAnchorMatchingCount
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Code-preserving matchings of the selected bulk, excluding the top slot -/
namespace Ostmann
open scoped Classical

theorem selectedAnchorMatchingSet_subset {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (n m : ℕ)
    (bulk : Fin m ↪ I) (hbulk : ∀ i, role (bulk i) = .word) :
    selectedAnchorMatchingSet role n m bulk hbulk ⊆ cellPreservingMatchings (selectedBulkLabel role n m bulk hbulk) := by
  intro e he
  obtain ⟨h, _⟩ := (mem_selectedAnchorMatchingSet role n m bulk hbulk e).mp he
  exact (mem_cellPreservingMatchings _ _).mpr h

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterAnchorDecay
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The code-preserving diagonal for the constructed character cells

The energy length is the actual bulk density times L. This retains a bulk
mass of a L rather than assuming the stronger, generally false, bound L.
-/
namespace Ostmann
open Filter
open scoped Classical BigOperators SchwartzMap FourierTransform

theorem le_characterRangeError (k : ℕ) (c : ℝ) (hc : 0 ≤ c) :
    c ≤ characterRangeError k c := by
  have hp : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
  have hk := Nat.cast_nonneg (α := ℝ) k
  have hh : 1 ≤ (2 : ℝ) ^ k + k + 2 := by linarith
  exact (one_mul c).symm.trans_le (mul_le_mul_of_nonneg_right hh hc)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterFourierBudgets
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Explicit finite-frequency and Fourier-window costs -/
namespace Ostmann
open scoped Classical
open scoped FourierTransform SchwartzMap

theorem naturalTransferCutoff_linear_bound (k j : ℕ) (d m : ℝ)
    (hj : j ≤ k) (hd : 0 ≤ d) (hm : 1 ≤ m) :
    (naturalTransferCutoff (d * m) m j : ℝ) ≤
      Real.exp (((2 : ℝ) ^ k * d + 2 * (4 : ℝ) ^ k) * m) := by
  exact (Nat.floor_le (Real.exp_nonneg _)).trans
    (Real.exp_le_exp.mpr (transferErrorScale_linear_bound k j d m hj hd hm))

theorem character_initial_window_bounds (d C m : ℝ)
    (hd : 1 ≤ d) (hm : 1 ≤ m) (hC : 0 ≤ C) (hCm : C ≤ m) :
    1 ≤ Real.exp (d * m - C) ∧
      Real.exp (d * m - C) ≤ Real.exp (d * m + C) ∧
      Real.exp (d * m + C) - Real.exp (d * m - C) ≤ Real.exp ((d + 1) * m) := by
  have hm0 : 0 ≤ m := by linarith
  have hdm : m ≤ d * m := by nlinarith only [hd, hm0]
  refine ⟨Real.one_le_exp_iff.mpr (by linarith),
    Real.exp_le_exp.mpr (by linarith), ?_⟩
  apply (sub_le_self _ (Real.exp_nonneg _)).trans
  exact Real.exp_le_exp.mpr (by nlinarith only [hCm])

theorem character_prime_band_log_ratio (α β L M H : ℝ)
    (hL : 0 ≤ L) (hLM : L ≤ M) (_hβ : 0 ≤ β) (hH : β - α ≤ H) (hH0 : 0 ≤ H) :
    Real.log (Real.exp (Real.exp (β * L))) / Real.exp (α * L) ≤
      Real.exp (H * (1 + M)) := by
  rw [Real.log_exp, ← Real.exp_sub]
  apply Real.exp_le_exp.mpr
  have h₁ := mul_le_mul_of_nonneg_right hH hL
  have h₂ := mul_le_mul_of_nonneg_left hLM hH0
  nlinarith only [h₁, h₂, hH0]

theorem character_prime_band_dyadic_budget (E : ℕ) (β L M H : ℝ)
    (hβ : 0 ≤ β) (hL : 1 ≤ L) (hLM : L ≤ M)
    (hH : β + Real.log ((Real.log 2)⁻¹ + 1) ≤ H) (hH0 : 0 ≤ H)
    (hE : (E : ℝ) ≤ Real.exp (Real.exp (β * L))) :
    ((Nat.log 2 E + 1 : ℕ) : ℝ) ≤ Real.exp (H * (1 + M)) := by
  apply (dyadic_prime_range_count E β L hβ hL hE).trans
  apply Real.exp_le_exp.mpr
  have h₁ := mul_le_mul_of_nonneg_right hH (by linarith : 0 ≤ L)
  have h₂ := mul_le_mul_of_nonneg_left hLM hH0
  nlinarith only [h₁, h₂, hH0]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterBandCutoffs
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integer endpoints for the separated character prime bands -/
namespace Ostmann
open Filter

/-- A fixed positive gap in log-log scale supplies the factor two required
by the one-sided character estimate, even after rounding upward. -/
theorem eventual_double_exp_integer_margin (α β : ℝ) (hβ : 0 < β) (hαβ : α < β) :
    ∀ᶠ L : ℝ in atTop,
      2 * (⌈Real.exp (Real.exp (α * L))⌉₊ : ℝ) ≤ Real.exp (Real.exp (β * L)) := by
  filter_upwards [arithmetic_exponent_absorption α β 0 4 1 0 hβ hαβ hβ (by norm_num),
    eventually_ge_atTop (1 : ℝ)] with L hgap hL
  simp only [pow_zero, zero_mul, Real.exp_zero, one_mul] at hgap
  have hlog4 : Real.log 4 ≤ 3 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
    linarith
  have hm := mul_le_mul_of_nonneg_right hL (Real.exp_nonneg (α * L))
  have he : Real.log 4 + Real.exp (α * L) ≤ Real.exp (β * L) := by
    nlinarith only [hgap, hm, Real.exp_nonneg (α * L), hlog4]
  have hceil := (Nat.ceil_lt_add_one (Real.exp_nonneg (Real.exp (α * L)))).le
  have hexp : 1 ≤ Real.exp (Real.exp (α * L)) :=
    Real.one_le_exp (Real.exp_nonneg _)
  calc
    _ ≤ 4 * Real.exp (Real.exp (α * L)) := by linarith
    _ = Real.exp (Real.log 4 + Real.exp (α * L)) := by
      rw [Real.exp_add, Real.exp_log (by norm_num)]
    _ ≤ _ := Real.exp_le_exp.mpr he

theorem eventual_character_band_lower (α β : ℝ) (hβ : 0 < β) (hαβ : α < β) :
    ∀ᶠ L : ℝ in atTop,
      let A := ⌈Real.exp (Real.exp (α * L))⌉₊
      0 < A ∧ Real.exp (Real.exp (α * L)) ≤ A ∧
        ∀ p : ℕ, Real.exp (Real.exp (β * L)) ≤ p → 2 * A ≤ p := by
  filter_upwards [eventual_double_exp_integer_margin α β hβ hαβ] with L hL
  refine ⟨Nat.ceil_pos.mpr (Real.exp_pos _), Nat.le_ceil _, ?_⟩
  intro p hp
  exact_mod_cast hL.trans hp

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduledDiagonalDecomposition
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The literal iteration diagonal splits into its original-prior matching sums -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

theorem scheduledConstituentDiagonal_split {I K : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (size : I → ℕ)
    (χ : (Σ i, Fin (size i)) → ∀ p : ℕ, DirichletCharacter ℂ p)
    (κ : (Σ i, Fin (size i)) → ℕ → ℂ) (pivot : ℕ → (Σ i, Fin (size i)))
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (Q : (Σ i, Fin (size i)) → Finset ℕ)
    (lo hi : I → ℕ) (V pivotBound : ℕ → ℕ)
    (leaf : ScheduleAtomState role → ℤ → ℂ) (center : ∀ p : ℕ, ZMod p)
    (p : I) (j : ℕ)
    (label : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) j → K)
    (hdisjoint : ∀ a b, label a ≠ label b →
      Disjoint (Q (copyScheduleOrigin j a.val)) (Q (copyScheduleOrigin j b.val)))
    (hzero : ∀ x, fullAtomTransferWeight role V pivotBound
      (atomIntervalRanges role lo hi) leaf 0 x (0 : ℤ) = 0)
    (hlarge : ∀ q ∈ P, V j < q)
    (S : Finset (Equiv.Perm (CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) j)))
    (hS : S ⊆ cellPreservingMatchings label) :
    scheduledConstituentDiagonal role size χ κ pivot P hP Q lo hi V pivotBound leaf center p j =
      (∑ M ∈ Finset.Icc (lo p) (hi p),
        (constituentMatchingFamily role size χ κ pivot j P hP Q V pivotBound
          (atomIntervalRanges role lo hi) leaf (scheduledFrequencyHistory V j) S M).re) +
      ∑ M ∈ Finset.Icc (lo p) (hi p),
        (constituentMatchingFamily role size χ κ pivot j P hP Q V pivotBound
          (atomIntervalRanges role lo hi) leaf (scheduledFrequencyHistory V j)
          (cellPreservingMatchings label \ S) M).re := by
  have hsmall (d : ScheduledFrequencyIndex V j) (q : ℕ) (hq : q ∈ P) :
      (frequencyRoot j (scheduledFrequencyHistory V j d)).natAbs < q :=
    (scheduledFrequencyHistory_root_bound V j d).trans_lt (hlarge q hq)
  have hM (M : ℕ) := congrArg Complex.re
    (constituentPivotDiagonal_average_split role size χ κ pivot j P hP Q V pivotBound
      (atomIntervalRanges role lo hi) leaf (scheduledFrequencyHistory V j)
      label hdisjoint center M hzero hsmall S hS)
  simp only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, Complex.add_re] at hM
  unfold scheduledConstituentDiagonal
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [hM]
  exact Finset.sum_add_distrib

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SelectedAnchorDiagonalSplit
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The literal diagonal split by codes of the selected bulk -/
namespace Ostmann
open scoped Classical BigOperators

theorem selectedAnchorMatchingSet_zero {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (m : ℕ)
    (bulk : Fin m ↪ I) (hbulk : ∀ i, role (bulk i) = .word) :
    selectedAnchorMatchingSet role 0 m bulk hbulk =
      cellPreservingMatchings (selectedBulkLabel role 0 m bulk hbulk) := by
  apply Finset.Subset.antisymm (selectedAnchorMatchingSet_subset role 0 m bulk hbulk)
  intro e he
  apply (mem_selectedAnchorMatchingSet role 0 m bulk hbulk e).mpr
  refine ⟨(mem_cellPreservingMatchings _ _).mp he, ?_⟩
  intro x
  funext i
  exact Fin.elim0 i

theorem selected_anchor_diagonal_split {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (size : I → ℕ)
    (χ : (Σ i, Fin (size i)) → ∀ p : ℕ, DirichletCharacter ℂ p)
    (κ : (Σ i, Fin (size i)) → ℕ → ℂ) (pivot : ℕ → (Σ i, Fin (size i)))
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (Q : (Σ i, Fin (size i)) → Finset ℕ)
    (lo hi : I → ℕ) (V pivotBound : ℕ → ℕ)
    (leaf : ScheduleAtomState role → ℤ → ℂ) (center : ∀ p : ℕ, ZMod p)
    (p : I) (n m : ℕ)
    (bulk : Fin m ↪ (Σ a, Fin (size a))) (hbulk : ∀ i, role (bulk i).1 = .word)
    (hdisjoint : ∀ a b : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n,
      selectedBulkLabel _ n m bulk hbulk a ≠ selectedBulkLabel _ n m bulk hbulk b →
      Disjoint (Q (copyScheduleOrigin n a.val)) (Q (copyScheduleOrigin n b.val)))
    (hzero : ∀ x, fullAtomTransferWeight role V pivotBound
      (atomIntervalRanges role lo hi) leaf 0 x (0 : ℤ) = 0)
    (hlarge : ∀ q ∈ P, V n < q) :
    let ρ := fun i : Σ a, Fin (size a) => role i.1
    let A := selectedAnchorMatchingSet ρ n m bulk hbulk
    let B := cellPreservingMatchings (selectedBulkLabel ρ n m bulk hbulk) \ A
    scheduledConstituentDiagonal role size χ κ pivot P hP Q lo hi V pivotBound leaf center p n =
      (∑ M ∈ Finset.Icc (lo p) (hi p),
        (constituentMatchingFamily role size χ κ pivot n P hP Q V pivotBound
          (atomIntervalRanges role lo hi) leaf (scheduledFrequencyHistory V n) A M).re) +
      ∑ M ∈ Finset.Icc (lo p) (hi p),
        (constituentMatchingFamily role size χ κ pivot n P hP Q V pivotBound
          (atomIntervalRanges role lo hi) leaf (scheduledFrequencyHistory V n) B M).re := by
  exact scheduledConstituentDiagonal_split role size χ κ pivot P hP Q lo hi V pivotBound leaf center p n
    (selectedBulkLabel _ n m bulk hbulk) hdisjoint hzero hlarge _
    (selectedAnchorMatchingSet_subset _ n m bulk hbulk)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterBulkSeparation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The true bulk is disjoint from the complementary H cells -/
namespace Ostmann
open scoped Classical BigOperators

theorem selectedBulkLabel_disjoint_of_original {I : Type*}
    (role : I → CopyScheduleRole) (n m : ℕ) (bulk : Fin m ↪ I)
    (hbulk : ∀ i, role (bulk i) = .word) (Q : I → Finset ℕ)
    (hsep : ∀ i j, j ∉ Set.range bulk → role j ≠ .outside →
      Disjoint (Q (bulk i)) (Q j)) :
    ∀ a b : CopyScheduleH role n,
      selectedBulkLabel role n m bulk hbulk a ≠ selectedBulkLabel role n m bulk hbulk b →
      Disjoint (Q (copyScheduleOrigin n a.val)) (Q (copyScheduleOrigin n b.val)) := by
  have hside (a b : CopyScheduleH role n)
      (ha : a ∈ Set.range (selectedBulkH role n m bulk hbulk))
      (hb : b ∉ Set.range (selectedBulkH role n m bulk hbulk)) :
      Disjoint (Q (copyScheduleOrigin n a.val)) (Q (copyScheduleOrigin n b.val)) := by
    obtain ⟨x, rfl⟩ := ha
    have ho : copyScheduleOrigin n (selectedBulkH role n m bulk hbulk x).val = bulk x.2 :=
      copyScheduleOrigin_path n (scheduledPathEnumeration n x.1) (bulk x.2)
    rw [ho]
    apply hsep x.2 _ _ (copyScheduleH_origin_not_outside role n b)
    rintro ⟨i, hi⟩
    exact hb (mem_selectedBulkH_of_origin role n m bulk hbulk b i hi.symm)
  intro a b hab
  by_cases ha : a ∈ Set.range (selectedBulkH role n m bulk hbulk)
  · by_cases hb : b ∈ Set.range (selectedBulkH role n m bulk hbulk)
    · simp only [selectedBulkLabel, ha, hb, decide_true, ne_eq, not_true_eq_false] at hab
    · exact hside a b ha hb
  · by_cases hb : b ∈ Set.range (selectedBulkH role n m bulk hbulk)
    · exact (hside b a hb ha).symm
    · simp only [selectedBulkLabel, ha, hb, decide_false, ne_eq, not_true_eq_false] at hab

/-- The original top label is the only word slot outside the true bulk. No
separation between different anchor slots is assumed or needed. -/
theorem character_bulk_label_disjoint {k : ℕ} (m : ℕ) (r : Fin k → ℕ) (f n : ℕ)
    (Q : Fin (m + 1) → Finset ℕ) (U : Finset ℕ)
    (R : (v : CharacterCell k) → Fin (characterCellSize r f v) → Finset ℕ)
    (hQ : ∀ i : Fin m, Q i.succ = U) (htop : Disjoint U (Q 0))
    (hR : ∀ v i, Disjoint U (R v i)) :
    ∀ a b : CopyScheduleH (fun i : Σ v, Fin (characterSize m r f v) => characterRole k i.1) n,
      selectedBulkLabel _ n m (characterBulk m r f) (characterBulk_role m r f) a ≠
        selectedBulkLabel _ n m (characterBulk m r f) (characterBulk_role m r f) b →
      Disjoint (characterFullPrimeCells m r f Q R (copyScheduleOrigin n a.val))
        (characterFullPrimeCells m r f Q R (copyScheduleOrigin n b.val)) := by
  apply selectedBulkLabel_disjoint_of_original _ n m (characterBulk m r f)
    (characterBulk_role m r f) (characterFullPrimeCells m r f Q R)
  intro i j hj hout
  rw [characterFullPrimeCells_bulk, hQ]
  by_cases hw : characterRole k j.1 = .word
  · rw [character_word_not_bulk m r f j hw hj, characterFullPrimeCells_top]
    exact htop
  · rcases j with ⟨⟨b, v⟩, t⟩
    cases v with
    | none =>
      cases b with
      | false => exact False.elim (hout rfl)
      | true => exact False.elim (hw rfl)
    | some v => exact hR v t

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterComparisonCounts
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Concrete complexity bounds for the signed character comparison -/
namespace Ostmann
open scoped Classical

theorem characterSize_le (k m N : ℕ) (r : Fin k → ℕ) (f : ℕ)
    (hr : ∀ j, r j ≤ N) (hf : f ≤ N) (v : CharacterRole k) :
    characterSize m r f v ≤ m + N + 1 := by
  rcases v with ⟨b, v⟩
  cases v with
  | none => change m + 1 ≤ _; omega
  | some v =>
    rcases v with j | (a | u)
    · exact (hr j).trans (by omega)
    · change 1 ≤ _; omega
    · exact hf.trans (by omega)

theorem characterSize_linear_bound (m N : ℕ) :
    ((m + N + 1 : ℕ) : ℝ) ≤ ((N : ℝ) + 2) * (1 + (m : ℝ)) := by
  have hm := Nat.cast_nonneg (α := ℝ) m
  have hN := Nat.cast_nonneg (α := ℝ) N
  push_cast
  nlinarith

theorem character_interval_complexity (k n : ℕ) (hn : n ≤ k)
    (lo hi : CharacterRole k → ℕ) :
    (∀ j ≤ n, ∀ r ∈ atomIntervalRanges (characterRole k) lo hi j, r.atoms.length ≤ 1) ∧
      ∀ j ≤ n, (atomIntervalRanges (characterRole k) lo hi j).length ≤
        3 ^ k * Fintype.card (CharacterRole k) := by
  refine ⟨fun j _ r hr => (atomIntervalRanges_singleton _ lo hi j r hr).le, ?_⟩
  intro j hj
  exact atomIntervalRanges_length_le _ lo hi k j (hj.trans hn)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ConstituentHProductLower
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A lower endpoint for the actual supported H product -/
namespace Ostmann
open scoped Classical BigOperators

theorem constituentHProductLower_of_atom_intervals {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (size : I → ℕ) (n : ℕ)
    (childBound pivotBound : ℕ → ℕ) (lo hi : I → ℕ)
    (leaf : ScheduleAtomState role → ℤ → ℂ) (Z : ℝ)
    (hZ : Z ≤ ∏ h : CopyScheduleH role n, (lo (copyScheduleOrigin n h.val) : ℝ)) :
    ConstituentHProductLower role size n childBound pivotBound
      (atomIntervalRanges role lo hi) leaf Z := by
  intro M t l u hw
  apply hZ.trans
  exact_mod_cast (fullAtomTransferWeight_inserted_H_product_bounds role size n
    childBound pivotBound lo hi leaf t l u M hw).1

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterNonanchorDecay
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Code-changing cancellation on the actual signed character cells -/
namespace Ostmann
open Filter
open scoped Classical BigOperators SchwartzMap FourierTransform ComplexConjugate

theorem eventual_character_nonanchor_decay (k n N : ℕ) (hn : n + 1 < k)
    (ψ : 𝓢(ℝ, ℂ)) (hreal : ∀ x, conj (ψ x) = ψ x)
    (B z c Cmass α βg βw γs βa γw νw νa : ℝ)
    (hB : 1 ≤ B) (hz : 1 ≤ z) (hc : 1 ≤ c) (hCmass : 0 < Cmass)
    (hα : 0 < α) (hβg : 0 < βg) (hαw : α < βw) (hsw : γs < βw)
    (hαa : α < βa) (hwa : γw < βa) (hwg : γw ≤ βg)
    (hβw : βw < νw) (hβa : βa < νa) :
    ∀ᶠ L : ℝ in atTop, ∀ m : ℕ, 1 ≤ (m : ℝ) → L ≤ m →
      (m : ℝ) ≤ z * L → (Fintype.card (CharacterRole k) : ℝ) * c ≤ m →
      ∀ (r : Fin k → ℕ) (f : ℕ) (hr : ∀ j, 0 < r j),
      (∀ j, r j ≤ N) → f ≤ N →
      ∀ (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
        (Q : (Σ v, Fin (characterSize m r f v)) → Finset ℕ),
      (∀ i, Q i ⊆ P) →
      (∀ i, Real.exp (-Cmass * L) ≤ ∑ p ∈ Q i, (p : ℝ)⁻¹) →
      (∀ p ∈ P, Real.exp (Real.exp (α * L)) ≤ p ∧
        (p : ℝ) ≤ Real.exp (Real.exp (βg * L))) →
      (∀ j p, p ∈ Q (characterAnchor m r f j false) →
        (p : ℝ) ≤ Real.exp (Real.exp (γs * L))) →
      (∀ i p, p ∈ Q (characterBulk m r f i) →
        Real.exp (Real.exp (νw * L)) ≤ p ∧ (p : ℝ) ≤ Real.exp (Real.exp (γw * L))) →
      (∀ j p, p ∈ Q (characterAnchor m r f j true) →
        Real.exp (Real.exp (νa * L)) ≤ p) →
      ∀ (χ : ∀ p : ℕ, DirichletCharacter ℂ p), (∀ p ∈ P, χ p ^ 2 ≠ 1) →
      ∀ (J : ℕ), 0 < J → ∀ (anchor : Fin k → Bool → ℝ) (F logX : ℝ), 0 < logX →
      let Δ := characterBaseGap B z m
      let T := characterPivotTarget k J (fun j => anchor j false + anchor j true)
        (fun j => characterPivotGap B z m j.val)
      T ⟨n + 1, hn⟩ + c ≤ Real.exp (βg * L) →
      ∀ lower upper : CharacterCell k → ℕ,
      (∀ v, Real.exp (characterLogCenter J T anchor F (true, some v) - c) ≤ lower v) →
      (∀ v, (upper v : ℝ) ≤ Real.exp (characterLogCenter J T anchor F (true, some v) + c)) →
      let lo := initialWordAtomLower J lower
      let hi := initialWordAtomUpper J upper
      let χ₀ := signedAtomCharacter (initialWordSize (m + 1) (characterCellSize r f)) χ
      let V := naturalTransferCutoff Δ m
      let cap := characterPivotCap T (characterRangeError k c)
      let p := characterPivotAtom ⟨n + 1, hn⟩
      let ρ := fun i : Σ v, Fin (characterSize m r f v) => characterRole k i.1
      let Sbad := cellPreservingMatchings (selectedBulkLabel ρ (n + 1) m
        (characterBulk m r f) (characterBulk_role m r f)) \
        selectedAnchorMatchingSet ρ (n + 1) m (characterBulk m r f) (characterBulk_role m r f)
      (∑ M ∈ Finset.Icc (lo p) (hi p),
        (constituentMatchingFamily (characterRole k) (characterSize m r f) χ₀
          (fun i => primeGaussMultiplier (χ₀ i)) (characterPivot m r f hr) (n + 1) P hP Q
          V cap (atomIntervalRanges (characterRole k) lo hi)
          (scheduleFourierLeaf (characterRole k) ψ (Real.exp logX)
            (Real.exp (Δ - (Fintype.card (CharacterRole k) : ℝ) * c))
            (Real.exp (Δ + (Fintype.card (CharacterRole k) : ℝ) * c)))
          (scheduledFrequencyHistory V (n + 1)) Sbad M).re) ≤
        Real.exp (-(characterPivotGap B z m (n + 1) - 2 * characterRangeError k c)) := by
  let d := B + 20 * Real.log z
  let C₀ := (Fintype.card (CharacterRole k) : ℝ) * c
  let D := (2 : ℝ) ^ k * d + 2 * (4 : ℝ) ^ k
  let C := max D (d + 1)
  let H := Cmass + βg + α + Real.log ((Real.log 2)⁻¹ + 1) + 2
  let S := max 1 (max (SchwartzMap.seminorm ℝ 0 0 (𝓕 ψ : 𝓢(ℝ, ℂ)))
    (SchwartzMap.seminorm ℝ 0 1 (𝓕 ψ : 𝓢(ℝ, ℂ))))
  have hz0 : 0 < z := by linarith
  have hd1 : 1 ≤ d := by dsimp [d]; linarith [Real.log_nonneg hz]
  have hd : 0 ≤ d := by linarith
  have hC : 0 ≤ C := (by dsimp [D]; positivity : (0 : ℝ) ≤ D).trans (le_max_left _ _)
  have hlc : 0 ≤ Real.log ((Real.log 2)⁻¹ + 1) := by
    have hh : 0 ≤ (Real.log 2)⁻¹ := inv_nonneg.mpr (Real.log_pos (by norm_num)).le
    exact Real.log_nonneg (by linarith)
  have hH : 0 ≤ H := by dsimp [H]; linarith
  have hHm : Cmass ≤ H := by dsimp [H]; linarith
  have hHdy : βg + Real.log ((Real.log 2)⁻¹ + 1) ≤ H := by dsimp [H]; linarith
  have hHratio : βg - α ≤ H := by dsimp [H]; linarith
  have hS : 1 ≤ S := le_max_left _ _
  have hs : 0 ≤ (N : ℝ) + 2 := by positivity
  filter_upwards [eventual_selected_nonanchor_product_decay (characterRole k) n 1
      (3 ^ k * Fintype.card (CharacterRole k)) ((N : ℝ) + 2) C S H z
      α βw γs βa γw 1 0 hs hC hS hH hz0.le hα hαw hsw hαa hwa (by norm_num) (by norm_num),
    eventual_character_band_lower βw νw (hα.trans (hαw.trans hβw)) hβw,
    eventual_character_band_lower βa νa (hα.trans (hαa.trans hβa)) hβa,
    eventual_natural_cutoff_below_primes k d z α 1 hd hz0.le hα (by norm_num),
    (Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop hβg)).eventually
      (eventually_ge_atTop (2 : ℝ)),
    eventually_ge_atTop (1 : ℝ)] with L hdec hAw hAa hlarge hRthree hL
  intro m hm hLM hmL hCm r f hr hrN hf P hP Q hQP hmass hPrange hsmall hword hbig
    χ hχ J _hJ anchor F logX hlogX Δ T hT lower upper hlower hupper lo hi χ₀ V cap p ρ Sbad
  have hpos (i) : 0 < ∑ q ∈ Q i, (q : ℝ)⁻¹ := (Real.exp_pos _).trans_le (hmass i)
  have hPne : P.Nonempty := by
    have hne : Q (characterTop m r f) ≠ ∅ := by
      intro he
      have hh := hpos (characterTop m r f)
      simp only [he, Finset.sum_empty, lt_self_iff_false] at hh
    obtain ⟨q, hq⟩ := Finset.nonempty_iff_ne_empty.mpr hne
    exact ⟨q, hQP _ hq⟩
  let small : Fin (n + 1) → (Σ v, Fin (characterSize m r f v)) :=
    fun j => characterAnchor m r f (j.castLE hn.le) false
  let large : Fin (n + 1) → (Σ v, Fin (characterSize m r f v)) :=
    fun j => characterAnchor m r f (j.castLE hn.le) true
  let Aw := ⌈Real.exp (Real.exp (βw * L))⌉₊
  let Aa := ⌈Real.exp (Real.exp (βa * L))⌉₊
  let Bs := ⌊Real.exp (Real.exp (γs * L))⌋₊
  let Bw := ⌊Real.exp (Real.exp (γw * L))⌋₊
  let Ea := ⌊Real.exp (Real.exp (βg * L))⌋₊
  let ℓ := Real.exp (Real.exp (α * L))
  let Rmax := Real.exp (Real.exp (βg * L))
  have hBw : (Bw : ℝ) ≤ Rmax := by
    apply (Nat.floor_le (Real.exp_nonneg _)).trans
    apply Real.exp_le_exp.mpr
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right hwg (by linarith)
  have hEa : (Ea : ℝ) ≤ Rmax := Nat.floor_le (Real.exp_nonneg _)
  have hWB := character_initial_window_bounds d C₀ m hd1 hm (by dsimp [C₀]; positivity) hCm
  change 1 ≤ Real.exp (Δ - C₀) ∧ Real.exp (Δ - C₀) ≤ Real.exp (Δ + C₀) ∧
    Real.exp (Δ + C₀) - Real.exp (Δ - C₀) ≤ Real.exp ((d + 1) * m) at hWB
  have hXlo : 1 < Real.exp logX * Real.exp (Δ - C₀) := by
    have he := Real.one_lt_exp_iff.mpr hlogX
    have hlo := hWB.1
    nlinarith only [he, hlo]
  have hw := character_word_interval_errors J c hc T anchor F lower upper hlower hupper
  have hpositive : 0 < ∏ h : CopyScheduleH (characterRole k) (n + 1),
      (lo (copyScheduleOrigin (n + 1) h.val) : ℝ) :=
    Finset.prod_pos (fun h _ => (Real.exp_pos _).trans_le (hw.1 _))
  have hA : 0 < lo p := by exact_mod_cast (Real.exp_pos _).trans_le (hw.1 p)
  have hcap : hi p ≤ cap (n + 1) := by
    dsimp only [cap]
    rw [characterPivotCap_eq hn]
    apply Nat.le_floor
    exact (hw.2 p).trans (Real.exp_le_exp.mpr (by
      change T ⟨n + 1, hn⟩ + c ≤ T ⟨n + 1, hn⟩ + characterRangeError k c
      linarith only [le_characterRangeError k c (by linarith)]))
  have hgap := character_diagonal_product_gap hn J B z m F c (by linarith) anchor
    lo hi hw.1 hw.2
  have hgap' : Real.exp (characterPivotGap B z m (n + 1) - 2 * characterRangeError k c) *
      (hi p : ℝ) ≤ ∏ h : CopyScheduleH (characterRole k) (n + 1),
        (lo (copyScheduleOrigin (n + 1) h.val) : ℝ) := by
    apply (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hcap) (Real.exp_nonneg _)).trans
    simpa only [cap, characterPivotCap_eq hn] using hgap
  have hip : (hi p : ℝ) ≤ Rmax :=
    (hw.2 p).trans (Real.exp_le_exp.mpr hT)
  have huniq : ∀ j ≤ n + 1, ∀ u v, characterRole k u = .pivot j →
      characterRole k v = .pivot j → u = v := by
    intro j hj u v hu hv
    exact (characterPivotAtom_unique ⟨j, hj.trans_lt hn⟩ u hu).trans
      (characterPivotAtom_unique ⟨j, hj.trans_lt hn⟩ v hv).symm
  have hcounts := character_interval_complexity k (n + 1) hn.le lo hi
  have hfreq : (V (n + 1) : ℝ) ≤ Real.exp (C * (1 + (m : ℝ))) := by
    apply (naturalTransferCutoff_linear_bound k (n + 1) d m hn.le hd hm).trans
    apply Real.exp_le_exp.mpr
    have hDC := le_max_left D (d + 1)
    nlinarith only [hDC, hC, Nat.cast_nonneg (α := ℝ) m]
  have hwidth : ∀ i, (WordFourierParameters.uniform (n + 1) (𝓕 ψ : 𝓢(ℝ, ℂ))
      (Real.exp logX) (Real.exp (Δ - C₀)) (Real.exp (Δ + C₀)) hWB.1 hWB.2.1).upper i -
      (WordFourierParameters.uniform (n + 1) (𝓕 ψ : 𝓢(ℝ, ℂ))
      (Real.exp logX) (Real.exp (Δ - C₀)) (Real.exp (Δ + C₀)) hWB.1 hWB.2.1).lower i ≤
        Real.exp (C * (1 + (m : ℝ))) := by
    intro i
    apply hWB.2.2.trans
    apply Real.exp_le_exp.mpr
    have hdC := le_max_right D (d + 1)
    nlinarith only [hdC, hC, Nat.cast_nonneg (α := ℝ) m]
  have result := hdec (characterSize m r f) (m + N + 1) (by omega)
    (characterSize_le k m N r f hrN hf) m (Nat.cast_nonneg _) hmL
    (characterSize_linear_bound m N) χ₀ (fun i => primeGaussMultiplier (χ₀ i))
    (characterPivot m r f hr) (fun i p => (primeGaussMultiplier_norm _ _).le)
    V cap (atomIntervalRanges (characterRole k) lo hi) hcounts.1 hcounts.2 ψ hreal
    (Real.exp logX) (Real.exp (Δ - C₀)) (Real.exp (Δ + C₀)) hWB.1 hWB.2.1
    (Real.exp_pos _) hXlo huniq m (characterBulk m r f) (characterBulk_role m r f)
    (fun e _ i => characterSchedule_matching m r f χ (n + 1) e i)
    small large (fun j => rfl) (fun j => rfl)
    (fun j hj => characterPivot_role m r f hr j (hj.trans hn))
    P hPne hP Q hQP hpos
    (fun j q hq => hχ q (hQP _ hq)) (fun i q hq => hχ q (hQP _ hq))
    ℓ ℓ (Real.exp_pos _) (Real.exp_pos _) Bs Bw Aw Bw Aa Ea hAw.1 hAa.1
    (fun j q hq => ⟨(hPrange q (hQP _ hq)).1, Nat.le_floor (hsmall _ q hq)⟩)
    (fun i q hq => ⟨⟨(hPrange q (hQP _ hq)).1, Nat.le_floor (hword i q hq).2⟩,
      hAw.2.2 q (hword i q hq).1, Nat.le_floor (hword i q hq).2⟩)
    (fun j q hq => ⟨hAa.2.2 q (hbig _ q hq), Nat.le_floor (hPrange q (hQP _ hq)).2⟩)
    (Real.exp (α * L)) Rmax (Real.exp_pos _) (by
      have he : (3 : ℝ) ≤ Real.exp (Real.exp (βg * L)) := by
        have h2 := Real.add_one_le_exp (Real.exp (βg * L))
        have hh : 2 ≤ Real.exp (βg * L) := by simpa only [Function.comp_apply, id_eq] using hRthree
        linarith only [hh, h2]
      exact he)
    (lo p) (hi p) hA hip
    (characterPivotGap B z m (n + 1) - 2 * characterRangeError k c)
    (fun q hq => (Real.le_log_iff_exp_le (by exact_mod_cast (hP q hq).pos)).mpr
      (hPrange q hq).1)
    (fun q hq => (hPrange q hq).2)
    (∏ h : CopyScheduleH (characterRole k) (n + 1),
      (lo (copyScheduleOrigin (n + 1) h.val) : ℝ)) hpositive hgap'
    (constituentHProductLower_of_atom_intervals _ _ _ V cap lo hi _ _ le_rfl)
    V (naturalTransferCutoff_monotone _ _ (mul_nonneg hd (Nat.cast_nonneg _)))
    hfreq ((le_max_left _ _).trans (le_max_right _ _))
    ((le_max_right _ _).trans (le_max_right _ _)) hwidth
    (character_prime_band_dyadic_budget Bw βg L m H hβg.le hL hLM hHdy hH hBw)
    (character_prime_band_dyadic_budget Ea βg L m H hβg.le hL hLM hHdy hH hEa)
    (fun i => (harmonic_mass_inv_energy_budget (Q i) Cmass L m hCmass.le hLM (hmass i)).trans
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hHm (by linarith))))
    (by simp only [one_mul]; exact le_rfl) (by simp only [one_mul]; exact le_rfl)
    hAw.2.1 hAa.2.1 (Nat.floor_le (Real.exp_nonneg _)) (Nat.floor_le (Real.exp_nonneg _))
    (fun q hq => by simpa only [one_mul] using (hPrange q hq).1)
    (character_prime_band_log_ratio α βg L m H (by linarith) hLM hβg.le hHratio hH)
    (fun q hq => hlarge _ hm hmL q (by simpa only [one_mul] using (hPrange q hq).1) _ hn.le)
  simpa only [zero_mul, neg_zero, Real.exp_zero, mul_one] using result

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterLiteralDiagonal
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The literal diagonal of the original signed character prior -/
namespace Ostmann
open scoped Classical BigOperators

/-- The split uses disjointness only between the true bulk and the remaining
original cells. The selected word bin removes the zero frequency. -/
theorem character_literal_diagonal_split {k : ℕ} (m : ℕ) (r : Fin k → ℕ) (f n : ℕ)
    (Q : Fin (m + 1) → Finset ℕ) (U : Finset ℕ)
    (R : (v : CharacterCell k) → Fin (characterCellSize r f v) → Finset ℕ)
    (hQ : ∀ i : Fin m, Q i.succ = U) (htop : Disjoint U (Q 0))
    (hR : ∀ v i, Disjoint U (R v i))
    (χ : (Σ v, Fin (characterSize m r f v)) → ∀ p : ℕ, DirichletCharacter ℂ p)
    (κ : (Σ v, Fin (characterSize m r f v)) → ℕ → ℂ)
    (pivot : ℕ → (Σ v, Fin (characterSize m r f v)))
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (J : ℕ) (hJ : 0 < J) (cellLo cellHi : CharacterCell k → ℕ)
    (V cap : ℕ → ℕ) (leaf : ScheduleAtomState (characterRole k) → ℤ → ℂ)
    (center : ∀ p : ℕ, ZMod p) (p : CharacterRole k)
    (hlarge : ∀ q ∈ P, V n < q) :
    let lo := initialWordAtomLower J cellLo
    let hi := initialWordAtomUpper J cellHi
    let Q₀ := characterFullPrimeCells m r f Q R
    let ρ := fun i : Σ v, Fin (characterSize m r f v) => characterRole k i.1
    let A := selectedAnchorMatchingSet ρ n m (characterBulk m r f) (characterBulk_role m r f)
    let B := cellPreservingMatchings (selectedBulkLabel ρ n m
      (characterBulk m r f) (characterBulk_role m r f)) \ A
    scheduledConstituentDiagonal (characterRole k) (characterSize m r f) χ κ pivot P hP Q₀
      lo hi V cap leaf center p n =
      (∑ M ∈ Finset.Icc (lo p) (hi p),
        (constituentMatchingFamily (characterRole k) (characterSize m r f) χ κ pivot n P hP Q₀
          V cap (atomIntervalRanges (characterRole k) lo hi) leaf
          (scheduledFrequencyHistory V n) A M).re) +
      ∑ M ∈ Finset.Icc (lo p) (hi p),
        (constituentMatchingFamily (characterRole k) (characterSize m r f) χ κ pivot n P hP Q₀
          V cap (atomIntervalRanges (characterRole k) lo hi) leaf
          (scheduledFrequencyHistory V n) B M).re := by
  intro lo hi Q₀ ρ A B
  exact selected_anchor_diagonal_split (characterRole k) (characterSize m r f) χ κ pivot
    P hP Q₀ lo hi V cap leaf center p n m (characterBulk m r f) (characterBulk_role m r f)
    (character_bulk_label_disjoint m r f n Q U R hQ htop hR)
    (fullAtomTransferWeight_zero_of_interval (characterRole k) lo hi V cap leaf
      (true, none) (initialWordAtomLower_word_gt_one J hJ cellLo true)) hlarge

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_CharacterZeroDiagonal
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # At depth zero every compatible matching preserves the empty anchor code -/
namespace Ostmann
open scoped Classical BigOperators

theorem constituentMatchingFamily_empty {I D : Type*} [Fintype I] [Fintype D]
    (role : I → CopyScheduleRole) (size : I → ℕ)
    (χ : (Σ i, Fin (size i)) → ∀ p : ℕ, DirichletCharacter ℂ p)
    (κ : (Σ i, Fin (size i)) → ℕ → ℂ) (pivot : ℕ → (Σ i, Fin (size i)))
    (n : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (Q : (Σ i, Fin (size i)) → Finset ℕ)
    (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (leaf : ScheduleAtomState role → ℤ → ℂ) (hist : D → FrequencyTree ℤ n) (M : ℕ) :
    constituentMatchingFamily role size χ κ pivot n P hP Q childBound pivotBound ranges
      leaf hist ∅ M = 0 := by
  simp only [constituentMatchingFamily, Finset.sum_empty, mul_zero, Finset.sum_const_zero]

theorem character_literal_diagonal_zero {k : ℕ} (m : ℕ) (r : Fin k → ℕ) (f : ℕ)
    (Q : Fin (m + 1) → Finset ℕ) (U : Finset ℕ)
    (R : (v : CharacterCell k) → Fin (characterCellSize r f v) → Finset ℕ)
    (hQ : ∀ i : Fin m, Q i.succ = U) (htop : Disjoint U (Q 0))
    (hR : ∀ v i, Disjoint U (R v i))
    (χ : (Σ v, Fin (characterSize m r f v)) → ∀ p : ℕ, DirichletCharacter ℂ p)
    (κ : (Σ v, Fin (characterSize m r f v)) → ℕ → ℂ)
    (pivot : ℕ → (Σ v, Fin (characterSize m r f v)))
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (J : ℕ) (hJ : 0 < J) (cellLo cellHi : CharacterCell k → ℕ)
    (V cap : ℕ → ℕ) (leaf : ScheduleAtomState (characterRole k) → ℤ → ℂ)
    (center : ∀ p : ℕ, ZMod p) (p : CharacterRole k)
    (hlarge : ∀ q ∈ P, V 0 < q) :
    let lo := initialWordAtomLower J cellLo
    let hi := initialWordAtomUpper J cellHi
    let Q₀ := characterFullPrimeCells m r f Q R
    let ρ := fun i : Σ v, Fin (characterSize m r f v) => characterRole k i.1
    let A := selectedAnchorMatchingSet ρ 0 m (characterBulk m r f) (characterBulk_role m r f)
    scheduledConstituentDiagonal (characterRole k) (characterSize m r f) χ κ pivot P hP Q₀
      lo hi V cap leaf center p 0 =
      ∑ M ∈ Finset.Icc (lo p) (hi p),
        (constituentMatchingFamily (characterRole k) (characterSize m r f) χ κ pivot 0 P hP Q₀
          V cap (atomIntervalRanges (characterRole k) lo hi) leaf
          (scheduledFrequencyHistory V 0) A M).re := by
  have h := character_literal_diagonal_split m r f 0 Q U R hQ htop hR χ κ pivot P hP
    J hJ cellLo cellHi V cap leaf center p hlarge
  dsimp only at h ⊢
  have he : cellPreservingMatchings (selectedBulkLabel
      (fun i : Σ v, Fin (characterSize m r f v) => characterRole k i.1) 0 m
      (characterBulk m r f) (characterBulk_role m r f)) \
      selectedAnchorMatchingSet
        (fun i : Σ v, Fin (characterSize m r f v) => characterRole k i.1) 0 m
        (characterBulk m r f) (characterBulk_role m r f) = ∅ := by
    rw [selectedAnchorMatchingSet_zero, Finset.sdiff_self]
  rw [he] at h
  simpa only [constituentMatchingFamily_empty, Complex.zero_re, Finset.sum_const_zero,
    add_zero] using h

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterDiagonalDecay
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The literal character diagonal satisfies the finite iteration budget -/
namespace Ostmann
open Filter
open scoped Classical BigOperators SchwartzMap FourierTransform ComplexConjugate

theorem character_nonanchor_gap_small (n : ℕ) (B B₁ z m C : ℝ)
    (hm : 0 ≤ m) (hz : 1 ≤ z) (hC : 2 * C ≤ m)
    (hB : 2 * B₁ + 5 ≤ B) :
    Real.exp (-(characterPivotGap B z m n - 2 * C)) ≤
      Real.exp (-(2 * B₁ + 4) * (2 ^ n : ℕ) * m) := by
  apply Real.exp_le_exp.mpr
  have hgap := character_diagonal_gap_reserve n B z m C hm hC
  have hlog := Real.log_nonneg hz
  have hscale : 0 ≤ (2 ^ n : ℕ) * m := mul_nonneg (Nat.cast_nonneg _) hm
  have hcoef : 2 * B₁ + 4 ≤ B + 20 * Real.log z - 1 := by linarith
  have hh := mul_le_mul_of_nonneg_right hcoef hscale
  nlinarith only [hgap, hh]

theorem eventual_character_diagonal_decay (k n Bnb N : ℕ) (hn : n < k)
    (ψ : 𝓢(ℝ, ℂ)) (hreal : ∀ x, conj (ψ x) = ψ x)
    (K B B₁ z c a b Cmass α βg βw γs βa γw νw νa ε : ℝ)
    (hB : 1 ≤ B) (hBstrong : 2 * B₁ + 5 ≤ B) (hz : 1 ≤ z) (hc : 1 ≤ c)
    (ha : 0 < a) (ha1 : a ≤ 1) (hb : 0 < b) (hCmass : 0 < Cmass)
    (hα : 0 < α) (hβg : 0 < βg) (hγw : 0 ≤ γw)
    (hαw : α < βw) (hsw : γs < βw) (hαa : α < βa)
    (hwa : γw < βa) (hwg : γw ≤ βg) (hβw : βw < νw) (hβa : βa < νa)
    (hε : 0 < ε) (hbudget : 4 * Cmass * Bnb ≤ z)
    (hgap : 2 * B₁ +
      ((γw + Real.log ((Real.log 2)⁻¹ + 1)) / a + max (Real.log 3) 0 + ε) +
      Real.log 2 + 6 ≤ B + 20 * Real.log a)
    (hψ : SchwartzMap.seminorm ℝ 0 0 (𝓕 ψ : 𝓢(ℝ, ℂ)) ≤ Real.exp K) :
    ∃ M₀ : ℝ, ∀ᶠ L : ℝ in atTop, ∀ m : ℕ, M₀ ≤ (m : ℝ) → L ≤ m →
      (m : ℝ) ≤ z * L → z * L ≤ 2 * m →
      ∀ (r : Fin k → ℕ) (f : ℕ) (hr : ∀ j, 0 < r j),
      1 + ((∑ j, r j) + 2 * k) ≤ Bnb → (∀ j, r j ≤ N) → f ≤ N →
      ∀ (P U : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
        (Q : Fin (m + 1) → Finset ℕ)
        (R : (v : CharacterCell k) → Fin (characterCellSize r f v) → Finset ℕ),
      (∀ i : Fin m, Q i.succ = U) → Disjoint U (Q 0) →
      (∀ v i, Disjoint U (R v i)) →
      (∀ i, Q i ⊆ P) → (∀ v i, R v i ⊆ P) →
      b ≤ ∑ p ∈ Q 0, (p : ℝ)⁻¹ → a * L ≤ ∑ p ∈ U, (p : ℝ)⁻¹ →
      (∀ v i, Real.exp (-Cmass * L) ≤ ∑ p ∈ R v i, (p : ℝ)⁻¹) →
      (∀ p ∈ P, Real.exp (Real.exp (α * L)) ≤ p ∧
        (p : ℝ) ≤ Real.exp (Real.exp (βg * L))) →
      (∀ p ∈ U, Real.exp (Real.exp (νw * L)) ≤ p ∧
        (p : ℝ) ≤ Real.exp (Real.exp (γw * L))) →
      (∀ j p, p ∈ R (.inr (.inl (j, false))) ⟨0, by change 0 < 1; omega⟩ →
        (p : ℝ) ≤ Real.exp (Real.exp (γs * L))) →
      (∀ j p, p ∈ R (.inr (.inl (j, true))) ⟨0, by change 0 < 1; omega⟩ →
        Real.exp (Real.exp (νa * L)) ≤ p) →
      ∀ (χ : ∀ p : ℕ, DirichletCharacter ℂ p), (∀ p ∈ P, χ p ^ 2 ≠ 1) →
      ∀ (J : ℕ), 0 < J → ∀ (anchor : Fin k → Bool → ℝ) (F logX : ℝ), 0 < logX →
      let Δ := characterBaseGap B z m
      let T := characterPivotTarget k J (fun j => anchor j false + anchor j true)
        (fun j => characterPivotGap B z m j.val)
      T ⟨n, hn⟩ + c ≤ Real.exp (βg * L) →
      ∀ lower upper : CharacterCell k → ℕ,
      (∀ v, Real.exp (characterLogCenter J T anchor F (true, some v) - c) ≤ lower v) →
      (∀ v, (upper v : ℝ) ≤ Real.exp (characterLogCenter J T anchor F (true, some v) + c)) →
      ∀ center : ∀ p : ℕ, ZMod p,
      let lo := initialWordAtomLower J lower
      let hi := initialWordAtomUpper J upper
      let χ₀ := signedAtomCharacter (initialWordSize (m + 1) (characterCellSize r f)) χ
      let V := naturalTransferCutoff Δ m
      let cap := characterPivotCap T (characterRangeError k c)
      scheduledConstituentDiagonal (characterRole k) (characterSize m r f) χ₀
        (fun i => primeGaussMultiplier (χ₀ i)) (characterPivot m r f hr) P hP
        (characterFullPrimeCells m r f Q R) lo hi V cap
        (scheduleFourierLeaf (characterRole k) ψ (Real.exp logX)
          (Real.exp (Δ - (Fintype.card (CharacterRole k) : ℝ) * c))
          (Real.exp (Δ + (Fintype.card (CharacterRole k) : ℝ) * c))) center
        (characterPivotAtom ⟨n, hn⟩) n ≤
        Real.exp (-(2 * B₁ + 3) * (2 ^ n : ℕ) * m) := by
  obtain ⟨M₀, hA⟩ := eventual_character_anchor_decay k n Bnb hn ψ K B B₁ z c a b
    Cmass α γw ε hB hz hc ha ha1 hb hCmass hα hγw hε hbudget hgap hψ
  have hdec := fun (d : ℕ) (hd : d + 1 < k) =>
    eventual_character_nonanchor_decay k d N hd ψ hreal B z c Cmass α βg βw γs βa γw νw νa
      hB hz hc hCmass hα hβg hαw hsw hαa hwa hwg hβw hβa
  have hdecAll := eventually_all.mpr (fun d : Fin k =>
    eventually_all.mpr (fun hd : d.val + 1 < k => hdec d hd))
  refine ⟨max M₀ (max 1 (max ((Fintype.card (CharacterRole k) : ℝ) * c)
    (2 * characterRangeError k c))), ?_⟩
  filter_upwards [hA, hdecAll, eventual_full_character_mass_floor a b Cmass ha hb hCmass,
    eventual_natural_cutoff_below_primes k (B + 20 * Real.log z) z α 1
      (by linarith [Real.log_nonneg hz]) (by linarith) hα (by norm_num)]
    with L hA hD hmass hlarge
  intro m hM hLm hmL hLm₂ r f hr hnb hrN hf P U hP Q R hQU htop hdis hQP hRP
    htopmass hbulk hRmass hPrange hUrange hsmall hbig χ hχ J hJ anchor F logX hlogX
    Δ T hT lower upper hlo hhi center lo hi χ₀ V cap
  let leaf := scheduleFourierLeaf (characterRole k) ψ (Real.exp logX)
    (Real.exp (Δ - (Fintype.card (CharacterRole k) : ℝ) * c))
    (Real.exp (Δ + (Fintype.card (CharacterRole k) : ℝ) * c))
  have hM₀ : M₀ ≤ (m : ℝ) := (le_max_left _ _).trans hM
  have hm : (1 : ℝ) ≤ m := (le_max_left _ _).trans ((le_max_right _ _).trans hM)
  have hCm : (Fintype.card (CharacterRole k) : ℝ) * c ≤ m :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hM))
  have hC : 2 * characterRangeError k c ≤ m :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hM))
  have hA' := hA m hM₀ hLm hmL hLm₂ r f hr hnb P U hP Q R hQU hQP hRP
    htopmass hbulk hRmass (fun p hp => (hPrange p hp).1)
    (fun p hp => (hUrange p hp).2) J hJ anchor F logX hlogX lower upper hlo hhi χ
  have hlarge' : ∀ p ∈ P, V n < p := by
    intro p hp
    exact hlarge m hm hmL p (by simpa only [one_mul] using (hPrange p hp).1) n hn.le
  cases n with
  | zero =>
    have he := character_literal_diagonal_zero m r f Q U R hQU htop hdis χ₀
      (fun i => primeGaussMultiplier (χ₀ i)) (characterPivot m r f hr) P hP J hJ
      lower upper V cap leaf center (characterPivotAtom ⟨0, hn⟩) hlarge'
    dsimp only at he hA' ⊢
    rw [he]
    apply hA'.trans
    apply Real.exp_le_exp.mpr
    push_cast
    nlinarith only [hm]
  | succ d =>
    have hmass' := hmass k m r f Q R htopmass
      (fun i => by rw [hQU]; exact hbulk) hRmass
    have hD' := hD ⟨d, by omega⟩ hn m hm hLm hmL hCm r f hr hrN hf P hP
      (characterFullPrimeCells m r f Q R)
      (characterFullPrimeCells_subset m r f P Q R hQP hRP) hmass' hPrange
      hsmall (fun i p hp => by
        rw [characterFullPrimeCells_bulk, hQU] at hp
        exact hUrange p hp) hbig χ hχ J hJ anchor F logX hlogX hT lower upper hlo hhi
    have he := character_literal_diagonal_split m r f (d + 1) Q U R hQU htop hdis χ₀
      (fun i => primeGaussMultiplier (χ₀ i)) (characterPivot m r f hr) P hP J hJ
      lower upper V cap leaf center (characterPivotAtom ⟨d + 1, hn⟩) hlarge'
    dsimp only at he hA' hD' ⊢
    rw [he]
    exact character_diagonal_sum_small _ _ B₁ m (d + 1) hm hA'
      (hD'.trans (character_nonanchor_gap_small (d + 1) B B₁ z m
        (characterRangeError k c) (by linarith) hz hC hBstrong))
end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterLiftCellBounds
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Lift actual nonword intervals to both signed copies -/
namespace Ostmann
open scoped Classical BigOperators

theorem characterLiftCellBound_support {k : ℕ} (m : ℕ) (r : Fin k → ℕ) (f : ℕ)
    (P : Finset ℕ) (Q : Fin (m + 1) → Finset ℕ)
    (R : (v : CharacterCell k) → Fin (characterCellSize r f v) → Finset ℕ)
    (hQP : ∀ i, Q i ⊆ P)
    (lo hi : (Σ v, Fin (characterCellSize r f v)) → ℕ)
    (hcell : ∀ v i p, p ∈ R v i → lo ⟨v, i⟩ ≤ p ∧ p ≤ hi ⟨v, i⟩) :
    ∀ i p, p ∈ characterFullPrimeCells m r f Q R i →
      characterLiftCellBound m r f 0 lo i ≤ p ∧
      p ≤ characterLiftCellBound m r f (P.sup id) hi i := by
  rintro ⟨⟨sgn, v⟩, i⟩ p hp
  cases v with
  | none => exact ⟨Nat.zero_le _, Finset.le_sup (f := id) (hQP i hp)⟩
  | some v => exact hcell v i p hp

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterRepeatRate
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Repeated-prime loss for the actual top-first character word -/
namespace Ostmann
open Filter
open scoped Classical BigOperators FourierTransform SchwartzMap

/-- The character word puts the top prime first. Its normalizer is the same
as the bulk-first ordering used in the elementary repeat estimate. -/
theorem character_wordRepeatFactor_eq {m c : ℕ} (P B T : Finset ℕ)
    (Q : Fin (m + 1) → Finset ℕ) (R : Fin c → Finset ℕ)
    (hzero : Q 0 = T) (hsucc : ∀ i : Fin m, Q i.succ = B)
    (ψ : 𝓢(ℝ, ℂ)) (D : ℝ) :
    wordRepeatFactor P Q R ψ D =
      wordRepeatFactor P (Fin.append (fun _ : Fin m => B) (fun _ : Fin 1 => T)) R ψ D := by
  have hprod : (∏ i, (∑ p ∈ Q i, (p : ℝ)⁻¹)⁻¹) =
      (∑ p ∈ T, (p : ℝ)⁻¹)⁻¹ * (∑ p ∈ B, (p : ℝ)⁻¹)⁻¹ ^ m := by
    rw [Fin.prod_univ_succ, hzero]
    simp only [hsucc, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  unfold wordRepeatFactor
  rw [doubledRole_normalizers, doubledRole_normalizers, hprod]
  simp only [Fin.prod_univ_add, Fin.append_left, Fin.append_right, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, pow_one]
  ring

theorem eventual_character_repeat_rate (c : ℕ) (a b z A C B₀ B_D E : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hz : 1 ≤ z) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hc : 4 * c * A ≤ z)
    (hgap : 2 * ((2 * Real.log (3 / a) + 3 + 2 * C) + B₀ + 2) ≤ B_D)
    (ψ : 𝓢(ℝ, ℂ)) :
    ∀ᶠ m : ℕ in atTop, ∀ L J : ℝ, 0 < L →
      (m : ℝ) ≤ z * L → z * L ≤ 2 * m →
      ∀ (P B T : Finset ℕ) (Q : Fin (m + 1) → Finset ℕ) (R : Fin c → Finset ℕ),
      Q 0 = T → (∀ i : Fin m, Q i.succ = B) →
      a * L ≤ ∑ p ∈ B, (p : ℝ)⁻¹ → b ≤ ∑ p ∈ T, (p : ℝ)⁻¹ →
      (∀ i, Real.exp (-J) ≤ ∑ p ∈ R i, (p : ℝ)⁻¹) → J ≤ A * L →
      (∑ p : P, (p : ℝ)⁻¹) ≤ C * L →
      wordRepeatFactor P Q R ψ ((B_D + 20 * Real.log z) * m - E) ≤
        Real.exp (-(B₀ + 1) * m) := by
  have hz0 : 0 < z := by linarith
  filter_upwards [eventual_wordRepeatFactor_bound c a b z A C ha hb hz0 hA hC ψ,
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop (E / 2)] with m hm hE
  intro L J hL hmL hLm P B T Q R hzero hsucc hB hT hR hJ hP
  rw [character_wordRepeatFactor_eq P B T Q R hzero hsucc]
  apply (hm L J _ hL hmL hLm P B T R hB hT hR hJ hP).trans
  exact initial_gap_rate _ _ B₀ B_D z E m hz
    (initial_repeat_coefficient a z A C c ha hz hC hc) hE hgap

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterInitialProduct
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The complete initial product has the prescribed logarithmic window -/
namespace Ostmann
open scoped Classical BigOperators

theorem character_log_center_sum (k : ℕ) (J F : ℝ) (T : Fin k → ℝ)
    (a : Fin k → Bool → ℝ) :
    (∑ v : CharacterRole k, characterLogCenter J T a F v) =
      2 * (J + (∑ j, T j) + (∑ j, (a j false + a j true)) + F) := by
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, Fintype.sum_option,
    Fintype.sum_sum_type, Fintype.sum_unique, characterLogCenter]
  simp only [add_comm (a _ true) (a _ false)]
  ring

theorem character_initial_center (k : ℕ) (logX Δ J : ℝ) (T : Fin k → ℝ)
    (a : Fin k → Bool → ℝ) :
    (∑ v : CharacterRole k,
      characterLogCenter J T a (characterFillerTarget logX Δ J T a) v) = logX + Δ := by
  rw [character_log_center_sum]
  unfold characterFillerTarget
  ring

/-- Per-atom interval errors remain bounded after taking all positive and
conjugate copies, independent of the number of primes in the word. -/
theorem character_initial_product_window (k : ℕ) (logX Δ J c : ℝ)
    (T : Fin k → ℝ) (a : Fin k → Bool → ℝ)
    (lo hi : CharacterRole k → ℕ)
    (hlo : ∀ v, Real.exp (characterLogCenter J T a
      (characterFillerTarget logX Δ J T a) v - c) ≤ lo v)
    (hhi : ∀ v, (hi v : ℝ) ≤ Real.exp (characterLogCenter J T a
      (characterFillerTarget logX Δ J T a) v + c))
    (x : CopyScheduleAtoms (characterRole k) 0 → ℕ)
    (hx : ∀ r ∈ atomIntervalRanges (characterRole k) lo hi 0, r.Holds x) :
    let C := (Fintype.card (CharacterRole k) : ℝ) * c
    ((∏ v, x v : ℕ) : ℝ) / Real.exp logX ∈ Set.Icc (Real.exp (Δ - C)) (Real.exp (Δ + C)) := by
  intro C
  let w := characterLogCenter J T a (characterFillerTarget logX Δ J T a)
  have hr := (atomIntervalRanges_holds_iff (characterRole k) lo hi 0 x).mp hx
  have he : (∏ v : CharacterRole k, x ⟨v, trivial⟩) = ∏ v, x v :=
    (initialSurvivorEquiv (characterRole k)).prod_comp x
  have hsum : (∑ v : CharacterRole k, w v) = logX + Δ :=
    character_initial_center k logX Δ J T a
  have hl : Real.exp (logX + Δ - C) ≤ ((∏ v, x v : ℕ) : ℝ) := by
    calc
      _ = ∏ v : CharacterRole k, Real.exp (w v - c) := by
        rw [← Real.exp_sum, Finset.sum_sub_distrib, hsum]
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, C]
      _ ≤ ∏ v : CharacterRole k, (x ⟨v, trivial⟩ : ℝ) := by
        apply Finset.prod_le_prod (fun _ _ => (Real.exp_pos _).le)
        intro v _
        exact (hlo v).trans (by exact_mod_cast (hr ⟨v, trivial⟩).1)
      _ = _ := by rw [← Nat.cast_prod, he]
  have hh : ((∏ v, x v : ℕ) : ℝ) ≤ Real.exp (logX + Δ + C) := by
    calc
      _ = ∏ v : CharacterRole k, (x ⟨v, trivial⟩ : ℝ) := by rw [← Nat.cast_prod, he]
      _ ≤ ∏ v : CharacterRole k, Real.exp (w v + c) := by
        apply Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _)
        intro v _
        exact (show (x ⟨v, trivial⟩ : ℝ) ≤ hi v by exact_mod_cast (hr ⟨v, trivial⟩).2).trans (hhi v)
      _ = _ := by
        rw [← Real.exp_sum, Finset.sum_add_distrib, hsum]
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, C]
  constructor
  · apply (le_div_iff₀ (Real.exp_pos logX)).mpr
    calc
      Real.exp (Δ - C) * Real.exp logX = Real.exp (logX + Δ - C) := by
        rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := hl
  · apply (div_le_iff₀ (Real.exp_pos logX)).mpr
    calc
      _ ≤ Real.exp (logX + Δ + C) := hh
      _ = Real.exp (Δ + C) * Real.exp logX := by
        rw [← Real.exp_add]; congr 1; ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialScheduleRangeAmplitude
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Prior-supported interval guards preserve the original initial statistic -/

namespace Ostmann
open scoped BigOperators Classical SchwartzMap FourierTransform

theorem initial_schedule_word_amplitude_of_range_equiv {C : Type*} [Fintype C]
    (role : Bool × Option C → CopyScheduleRole) (a m : ℕ) (s : C → ℕ)
    (cell : (Σ c, Fin (s c)) ≃ Fin m) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (Q : Fin (a + 1) → Finset ℕ) (R : Fin m → Finset ℕ)
    (χ : ∀ p : ℕ, DirichletCharacter ℂ p) (hχ : ∀ p ∈ P, χ p ≠ 1)
    (pivot : ℕ → (Σ v : Bool × Option C, Fin (initialWordSize (a + 1) s v.2)))
    (center : ∀ p : ℕ, ZMod p) (ψ : 𝓢(ℝ, ℂ)) (X τ lo hi : ℝ) (hX : 0 < X)
    (heven : ∀ v : ℝ, 𝓕 ψ (-v) = 𝓕 ψ v) (N : ℕ)
    (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (b : Fin (⌊4 * τ⌋₊ + 1))
    (hranges : ∀ x : (Σ v : Bool × Option C, Fin (initialWordSize (a + 1) s v.2)) → P,
      (∏ i, primeSubsetPrior P
        (Fin.append (Fin.append Q R) (Fin.append Q R)
          (initialWordTupleEquiv (a + 1) m s cell i)) (x i)) ≠ 0 →
      ((∀ r ∈ ranges 0, r.Holds (fun v => ∏ i, (x ⟨v.val, i⟩ : ℕ))) ↔
        ∀ r ∈ initialWordBinRanges role b.val,
          r.Holds (fun v => ∏ i, (x ⟨v.val, i⟩ : ℕ))))
    (hbin : ∀ y : Fin (((a + 1) + m) + ((a + 1) + m)) → P,
      productPrior (fun i => primeSubsetPrior P
        (Fin.append (Fin.append Q R) (Fin.append Q R) i)) y ≠ 0 →
      (∑ i, Real.log (((wordCopyEquiv P (a + 1) m).symm y).1.1 i : ℝ)) ≤ 4 * τ ∧
      (∑ i, Real.log (((wordCopyEquiv P (a + 1) m).symm y).2.1 i : ℝ)) ≤ 4 * τ)
    (hwindow : ∀ x : (Σ v : Bool × Option C, Fin (initialWordSize (a + 1) s v.2)) → P,
      (∏ i, primeSubsetPrior P
        (Fin.append (Fin.append Q R) (Fin.append Q R)
          (initialWordTupleEquiv (a + 1) m s cell i)) (x i)) ≠ 0 →
      (∀ r ∈ ranges 0, r.Holds (fun v => ∏ i, (x ⟨v.val, i⟩ : ℕ))) →
      ((∏ i, (x i : ℕ) : ℕ) : ℝ) / X ∈ Set.Icc lo hi) :
    constituentPrimeGuardedAmplitude role (fun v => initialWordSize (a + 1) s v.2)
      (fun i => wordCopyCharacter (a + 1) m χ (initialWordTupleEquiv (a + 1) m s cell i))
      (fun i => primeGaussMultiplier
        (wordCopyCharacter (a + 1) m χ (initialWordTupleEquiv (a + 1) m s cell i)))
      pivot 0 P hP
      (fun i => Fin.append (Fin.append Q R) (Fin.append Q R)
        (initialWordTupleEquiv (a + 1) m s cell i))
      childBound pivotBound ranges (scheduleFourierLeaf role ψ X lo hi)
      (fun v : Finset.Icc (-(N : ℤ)) (N : ℤ) => (v : ℤ)) center =
    wordGraphAmplitude P hP (fun i => primeSubsetPrior P (Q i))
      (fun j => primeSubsetPrior P (R j)) χ center ψ X N
      (fun w => wordLogBin τ (fun i => Real.log (w i : ℝ))) b := by
  let : Nonempty (Σ v : Bool × Option C, Fin (initialWordSize (a + 1) s v.2)) :=
    ⟨⟨(true, none), ⟨0, Nat.succ_pos a⟩⟩⟩
  have ht := initial_guarded_expectation role (fun v => initialWordSize (a + 1) s v.2)
    (fun i => wordCopyCharacter (a + 1) m χ (initialWordTupleEquiv (a + 1) m s cell i))
    P hP (fun i => Fin.append (Fin.append Q R) (Fin.append Q R)
      (initialWordTupleEquiv (a + 1) m s cell i))
    (fun i p hp => wordCopyCharacter_ne_one χ p (hχ p hp) _)
    pivot center ψ X lo hi hX heven N childBound pivotBound ranges hwindow
  have hu := initial_grouped_word_expectation role a m s cell P hP Q R χ center
    ψ X τ N b hbin
  refine ht.trans (Eq.trans ?_ hu)
  rw [finite_enumeration_sum]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hz : (∏ i, primeSubsetPrior P
      (Fin.append (Fin.append Q R) (Fin.append Q R)
        (initialWordTupleEquiv (a + 1) m s cell i)) (x i)) = 0
  · simp only [hz, Complex.ofReal_zero, zero_mul]
  · simp only [hranges x hz]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterInitialAmplitude
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The concrete character intervals start at the original word statistic -/
namespace Ostmann
open scoped Classical BigOperators SchwartzMap FourierTransform

theorem character_initial_amplitude (k m nc : ℕ) (r : Fin k → ℕ) (f : ℕ)
    (cell : (Σ c, Fin (characterCellSize r f c)) ≃ Fin nc)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (Q : Fin (m + 1) → Finset ℕ) (R : Fin nc → Finset ℕ)
    (cellLo cellHi : (Σ c, Fin (characterCellSize r f c)) → ℕ)
    (hcell : ∀ i q, q ∈ R (cell i) → cellLo i ≤ q ∧ q ≤ cellHi i)
    (χ : ∀ p : ℕ, DirichletCharacter ℂ p) (hχ : ∀ p ∈ P, χ p ≠ 1)
    (pivot : ℕ → (Σ v, Fin (characterSize m r f v)))
    (center : ∀ p : ℕ, ZMod p) (ψ : 𝓢(ℝ, ℂ))
    (heven : ∀ v : ℝ, 𝓕 ψ (-v) = 𝓕 ψ v)
    (logX Δ τ c : ℝ) (hc : 1 ≤ c) (T : Fin k → ℝ) (a : Fin k → Bool → ℝ)
    (N : ℕ) (childBound pivotBound : ℕ → ℕ) (b : Fin (⌊4 * τ⌋₊ + 1))
    (hlo : ∀ v, Real.exp (characterLogCenter b.val T a
      (characterFillerTarget logX Δ b.val T a) (true, some v) - c) ≤ ∏ i, cellLo ⟨v, i⟩)
    (hhi : ∀ v, (∏ i, cellHi ⟨v, i⟩ : ℕ) ≤ Real.exp (characterLogCenter b.val T a
      (characterFillerTarget logX Δ b.val T a) (true, some v) + c))
    (hbin : ∀ y : Fin (((m + 1) + nc) + ((m + 1) + nc)) → P,
      productPrior (fun i => primeSubsetPrior P
        (Fin.append (Fin.append Q R) (Fin.append Q R) i)) y ≠ 0 →
      (∑ i, Real.log (((wordCopyEquiv P (m + 1) nc).symm y).1.1 i : ℝ)) ≤ 4 * τ ∧
      (∑ i, Real.log (((wordCopyEquiv P (m + 1) nc).symm y).2.1 i : ℝ)) ≤ 4 * τ) :
    let lo := initialWordAtomLower b.val (fun v => ∏ i, cellLo ⟨v, i⟩)
    let hi := initialWordAtomUpper b.val (fun v => ∏ i, cellHi ⟨v, i⟩)
    let C := (Fintype.card (CharacterRole k) : ℝ) * c
    constituentPrimeGuardedAmplitude (characterRole k) (characterSize m r f)
      (fun i => wordCopyCharacter (m + 1) nc χ
        (initialWordTupleEquiv (m + 1) nc (characterCellSize r f) cell i))
      (fun i => primeGaussMultiplier (wordCopyCharacter (m + 1) nc χ
        (initialWordTupleEquiv (m + 1) nc (characterCellSize r f) cell i)))
      pivot 0 P hP
      (fun i => Fin.append (Fin.append Q R) (Fin.append Q R)
        (initialWordTupleEquiv (m + 1) nc (characterCellSize r f) cell i))
      childBound pivotBound (atomIntervalRanges (characterRole k) lo hi)
      (scheduleFourierLeaf (characterRole k) ψ (Real.exp logX)
        (Real.exp (Δ - C)) (Real.exp (Δ + C)))
      (fun v : Finset.Icc (-(N : ℤ)) (N : ℤ) => (v : ℤ)) center =
    wordGraphAmplitude P hP (fun i => primeSubsetPrior P (Q i))
      (fun j => primeSubsetPrior P (R j)) χ center ψ (Real.exp logX) N
      (fun w => wordLogBin τ (fun i => Real.log (w i : ℝ))) b := by
  intro lo hi C
  apply initial_schedule_word_amplitude_of_range_equiv (characterRole k) m nc
    (characterCellSize r f) cell P hP Q R χ hχ pivot center ψ (Real.exp logX) τ
    (Real.exp (Δ - C)) (Real.exp (Δ + C)) (Real.exp_pos _) heven N childBound pivotBound
    (atomIntervalRanges (characterRole k) lo hi) b
  · intro x hx
    exact initialWordPrior_atomIntervals_equiv (characterRole k) (m + 1) nc b.val
      (characterCellSize r f) cell P Q R cellLo cellHi hcell x hx
  · exact hbin
  · intro x _hx hguard
    have herr := character_word_interval_errors b.val c hc T a
      (characterFillerTarget logX Δ b.val T a)
      (fun v => ∏ i, cellLo ⟨v, i⟩) (fun v => ∏ i, cellHi ⟨v, i⟩) hlo hhi
    have hw := character_initial_product_window k logX Δ b.val c T a lo hi herr.1 herr.2
      (fun v => ∏ i, (x ⟨v.val, i⟩ : ℕ)) hguard
    change (scheduleAtomTotal (characterRole k)
      ⟨0, fun v => ∏ i, (x ⟨v.val, i⟩ : ℕ)⟩ : ℝ) / Real.exp logX ∈ _ at hw
    have ht := initial_atom_total (characterRole k)
      (fun v => initialWordSize (m + 1) (characterCellSize r f) v.2)
      (fun i => (x i : ℕ))
    rw [ht] at hw
    exact hw

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterOriginalProductWindow
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original fixed-bin product lies in the constructed Poisson window -/
namespace Ostmann
open scoped Classical BigOperators

theorem character_original_product_window (k m nc : ℕ) (r : Fin k → ℕ) (f : ℕ)
    (cell : (Σ v, Fin (characterCellSize r f v)) ≃ Fin nc)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (Q : Fin (m + 1) → Finset ℕ) (R : Fin nc → Finset ℕ)
    (cellLo cellHi : (Σ v, Fin (characterCellSize r f v)) → ℕ)
    (hcell : ∀ i p, p ∈ R (cell i) → cellLo i ≤ p ∧ p ≤ cellHi i)
    (logX Δ τ c : ℝ) (hc : 1 ≤ c) (T : Fin k → ℝ) (a : Fin k → Bool → ℝ)
    (b : Fin (⌊4 * τ⌋₊ + 1))
    (hlo : ∀ v, Real.exp (characterLogCenter b.val T a
      (characterFillerTarget logX Δ b.val T a) (true, some v) - c) ≤ ∏ i, cellLo ⟨v, i⟩)
    (hhi : ∀ v, (∏ i, cellHi ⟨v, i⟩ : ℕ) ≤ Real.exp (characterLogCenter b.val T a
      (characterFillerTarget logX Δ b.val T a) (true, some v) + c))
    (hbin : ∀ y : Fin (((m + 1) + nc) + ((m + 1) + nc)) → P,
      productPrior (fun i => primeSubsetPrior P
        (Fin.append (Fin.append Q R) (Fin.append Q R) i)) y ≠ 0 →
      (∑ i, Real.log (((wordCopyEquiv P (m + 1) nc).symm y).1.1 i : ℝ)) ≤ 4 * τ ∧
      (∑ i, Real.log (((wordCopyEquiv P (m + 1) nc).symm y).2.1 i : ℝ)) ≤ 4 * τ)
    (y : Fin (((m + 1) + nc) + ((m + 1) + nc)) → P)
    (hy : y ∈ wordCharacterEvent (fun i => primeSubsetPrior P (Q i))
      (fun i => primeSubsetPrior P (R i))
      (fun w => wordLogBin τ (fun i => Real.log (w i : ℝ))) b) :
    let C := (Fintype.card (CharacterRole k) : ℝ) * c
    (∏ i, (y i : ℝ)) / Real.exp logX ∈
      Set.Icc (Real.exp (Δ - C)) (Real.exp (Δ + C)) := by
  intro C
  let role := characterRole k
  let e := initialWordTupleEquiv (m + 1) nc (characterCellSize r f) cell
  let x := fun i => y (e i)
  let lo := initialWordAtomLower b.val (fun v => ∏ i, cellLo ⟨v, i⟩)
  let hi := initialWordAtomUpper b.val (fun v => ∏ i, cellHi ⟨v, i⟩)
  obtain ⟨hb, hp⟩ := (mem_wordCharacterEvent _ _ _ _ y).mp hy
  rw [wordCopyPrimePrior] at hp
  have hx : (∏ i, primeSubsetPrior P
      (Fin.append (Fin.append Q R) (Fin.append Q R) (e i)) (x i)) ≠ 0 := by
    change (∏ i, (fun j => primeSubsetPrior P
      (Fin.append (Fin.append Q R) (Fin.append Q R) j) (y j)) (e i)) ≠ 0
    have he := e.prod_comp (fun j => primeSubsetPrior P
      (Fin.append (Fin.append Q R) (Fin.append Q R) j) (y j))
    intro hz
    exact hp (he.symm.trans hz)
  have hr : ∀ s ∈ initialWordBinRanges role b.val,
      s.Holds (fun v => ∏ i, (x ⟨v.val, i⟩ : ℕ)) := by
    have h := (initialWordBinRanges_iff_bin role m nc (characterCellSize r f) cell P hP
      τ b y (hbin y hp).1 (hbin y hp).2).mpr hb
    exact h
  have hr' : ∀ s ∈ atomIntervalRanges role lo hi 0,
      s.Holds (fun v => ∏ i, (x ⟨v.val, i⟩ : ℕ)) :=
    (initialWordPrior_atomIntervals_equiv role (m + 1) nc b.val
      (characterCellSize r f) cell P Q R cellLo cellHi hcell x hx).mpr hr
  have herr := character_word_interval_errors b.val c hc T a
    (characterFillerTarget logX Δ b.val T a)
    (fun v => ∏ i, cellLo ⟨v, i⟩) (fun v => ∏ i, cellHi ⟨v, i⟩) hlo hhi
  have hw := character_initial_product_window k logX Δ b.val c T a lo hi herr.1 herr.2
    (fun v => ∏ i, (x ⟨v.val, i⟩ : ℕ)) hr'
  change (scheduleAtomTotal role ⟨0, fun v => ∏ i, (x ⟨v.val, i⟩ : ℕ)⟩ : ℝ) /
    Real.exp logX ∈ Set.Icc (Real.exp (Δ - C)) (Real.exp (Δ + C)) at hw
  have ht := initial_atom_total role
    (fun v : CharacterRole k => initialWordSize (m + 1) (characterCellSize r f) v.2)
    (fun i => (x i : ℕ))
  rw [ht] at hw
  have hprod : (∏ i, (x i : ℕ)) = ∏ j, (y j : ℕ) := e.prod_comp (fun j => (y j : ℕ))
  simpa only [hprod, Nat.cast_prod] using hw

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_PrimeWordInitialStatistic
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The already selected word bin gives the original positive statistic -/
namespace Ostmann
open scoped Classical BigOperators SchwartzMap

/-- The statistic only uses the absolute values of the selected cell means. -/
theorem prime_word_fixed_bin_statistic_norm {B : Type*}
    (k nc : ℕ) (P : Finset ℕ) (Q : Fin k → Finset ℕ) (R : Fin nc → Finset ℕ)
    (hQ : ∀ i, Q i ⊆ P) (hR : ∀ i, R i ⊆ P)
    (hQmass : ∀ i, (∑ p ∈ Q i, (p : ℝ)⁻¹) ≠ 0)
    (hRmass : ∀ i, (∑ p ∈ R i, (p : ℝ)⁻¹) ≠ 0)
    (χ : ∀ p : ℕ, DirichletCharacter ℂ p) (t : ∀ p : ℕ, ZMod p)
    (E : Finset ℤ) (ψ : 𝓢(ℝ, ℂ)) (X : ℝ) (hX : 0 < X)
    (bin : (Fin k → P) → B) (b : B) (c ρ γ : ℝ)
    (hρ : 0 ≤ ρ) (hγ : 0 ≤ γ)
    (hψ : ∀ x, 0 ≤ (ψ x).re) (hreal : ∀ x, (ψ x).im = 0)
    (hcE : ∀ a ∈ E, c ≤ (ψ ((a : ℝ) / X)).re)
    (hword : ∀ a ∈ E, ρ ≤ ‖binnedWordAverage (fun i => primeSubsetPrior P (Q i))
      (fun _ p => χ p ((a : ZMod p) - t p)) bin b‖)
    (hcell : ∀ a ∈ E, ∀ i, γ ≤
      ‖∑ p : P, (primeSubsetPrior P (R i) p : ℂ) * χ p ((a : ZMod p) - t p)‖) :
    (E.card : ℝ) * (c * ρ ^ 2 * γ ^ (2 * nc)) ≤
      (wordCharacterMean Subtype.val (fun i => primeSubsetPrior P (Q i))
        (fun i => primeSubsetPrior P (R i)) χ t ψ X bin b).re := by
  let μ := fun i => primeSubsetPrior P (Q i)
  let ν := fun i => primeSubsetPrior P (R i)
  have hnorm (i : Fin nc) (a : ℤ) :
      ‖∑ p : P, (ν i p : ℂ) * χ p ((a : ZMod p) - t p)‖ ≤ 1 := by
    calc
      _ ≤ ∑ p : P, ‖(ν i p : ℂ) * χ p ((a : ZMod p) - t p)‖ := norm_sum_le _ _
      _ ≤ ∑ p : P, ν i p := by
        apply Finset.sum_le_sum
        intro p _
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (primeSubsetPrior_nonneg _ _ _)]
        exact mul_le_of_le_one_right (primeSubsetPrior_nonneg _ _ _) ((χ p).norm_le_one _)
      _ = 1 := primeSubsetPrior_mass P (R i) (hR i) (hRmass i)
  have hG (a : ℤ) : ‖binnedWordAverage μ
      (fun _ p => χ p ((a : ZMod p) - t p)) bin b‖ ≤ 1 :=
    binnedWordAverage_norm_le_one μ _ bin b
      (fun i p => primeSubsetPrior_nonneg _ _ _)
      (fun i => primeSubsetPrior_mass P (Q i) (hQ i) (hQmass i))
      (fun i p => (χ p).norm_le_one _)
  have hl := wordStatistic_lower ψ X hX
    (fun a => binnedWordAverage μ (fun _ p => χ p ((a : ZMod p) - t p)) bin b)
    (fun i a => ∑ p : P, (ν i p : ℂ) * χ p ((a : ZMod p) - t p)) E
    hψ hG hnorm c ρ γ hρ hγ hcE hword
    hcell
  rw [word_statistic_eq_character_mean Subtype.val μ ν χ t ψ X hX hreal bin b] at hl
  exact hl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_PrimeWordInitialAmplitude
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Repeat removal and Poisson preserve the fixed-bin initial lower bound -/
namespace Ostmann
open scoped Classical BigOperators SchwartzMap FourierTransform

/-- The original character amplitude requires no common phase convention. -/
theorem prime_word_fixed_bin_amplitude_norm {B : Type*}
    (k nc : ℕ) (hk : 0 < k) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (Q : Fin k → Finset ℕ) (R : Fin nc → Finset ℕ)
    (hQ : ∀ i, Q i ⊆ P) (hR : ∀ i, R i ⊆ P)
    (hQmass : ∀ i, (∑ p ∈ Q i, (p : ℝ)⁻¹) ≠ 0)
    (hRmass : ∀ i, (∑ p ∈ R i, (p : ℝ)⁻¹) ≠ 0)
    (χ : ∀ p : ℕ, DirichletCharacter ℂ p) (hχ : ∀ p ∈ P, χ p ≠ 1)
    (t : ∀ p : ℕ, ZMod p) (E : Finset ℤ)
    (ψ : 𝓢(ℝ, ℂ)) (X : ℝ) (hX : 0 < X)
    (bin : (Fin k → P) → B) (b : B) (c ρ γ : ℝ)
    (hρ : 0 ≤ ρ) (hγ : 0 ≤ γ)
    (hψ : ∀ x, 0 ≤ (ψ x).re) (hreal : ∀ x, (ψ x).im = 0)
    (hcE : ∀ a ∈ E, c ≤ (ψ ((a : ℝ) / X)).re)
    (hword : ∀ a ∈ E, ρ ≤ ‖binnedWordAverage (fun i => primeSubsetPrior P (Q i))
      (fun _ p => χ p ((a : ZMod p) - t p)) bin b‖)
    (hcell : ∀ a ∈ E, ∀ i, γ ≤
      ‖∑ p : P, (primeSubsetPrior P (R i) p : ℂ) * χ p ((a : ZMod p) - t p)‖)
    (H U D : ℝ) (hU : 0 < U) (N : ℕ)
    (hsupp : ∀ x : ℝ, H < |x| → 𝓕 ψ x = 0)
    (hsmall : ∀ p ∈ P, H * U < p)
    (hupper : ∀ x ∈ wordCharacterEvent (fun i => primeSubsetPrior P (Q i))
      (fun j => primeSubsetPrior P (R j)) bin b, (∏ i, (x i : ℝ)) ≤ X * U)
    (hlower : ∀ x ∈ wordCharacterEvent (fun i => primeSubsetPrior P (Q i))
      (fun j => primeSubsetPrior P (R j)) bin b, X * Real.exp D ≤ ∏ i, (x i : ℝ))
    (hcut : ∀ x ∈ wordCharacterEvent (fun i => primeSubsetPrior P (Q i))
      (fun j => primeSubsetPrior P (R j)) bin b, H * (∏ i, (x i : ℕ)) ≤ N * X) :
    ((E.card : ℝ) * (c * ρ ^ 2 * γ ^ (2 * nc)) -
      Real.sqrt X * (‖𝓕 ψ 0‖ *
        (∏ i, (∑ p ∈ Fin.append (Fin.append Q R) (Fin.append Q R) i, (p : ℝ)⁻¹)⁻¹) *
        (((k + nc) + (k + nc) : ℕ) : ℝ) ^ ((k + nc) + (k + nc)) *
        Real.exp ((∑ p : P, (p : ℝ)⁻¹) - D / 2))) / Real.sqrt X ≤
      ‖wordGraphAmplitude P hP (fun i => primeSubsetPrior P (Q i))
        (fun j => primeSubsetPrior P (R j)) χ t ψ X N bin b‖ := by
  let : Nonempty (Fin ((k + nc) + (k + nc))) := ⟨⟨0, by omega⟩⟩
  have hs := prime_word_fixed_bin_statistic_norm k nc P Q R hQ hR hQmass hRmass χ t E ψ X hX
    bin b c ρ γ hρ hγ hψ hreal hcE hword hcell
  have hr := word_character_repeat_removal P hP Q R χ hχ t ψ X H U D hX hU hsupp hsmall
    bin b hupper hlower
  have hp := wordGraphAmplitude_eq P hP (fun i => primeSubsetPrior P (Q i))
    (fun i => primeSubsetPrior P (R i)) χ hχ t ψ X H hX N hsupp bin b hcut
  exact initial_amplitude_lower _ _ _ X _ _ hX hs hr hp

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterWordAmplitudeLower
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The fixed original bin gives the initial amplitude with its exact error -/
namespace Ostmann
open scoped Classical BigOperators SchwartzMap FourierTransform

theorem character_word_amplitude_lower (k m nc : ℕ) (r : Fin k → ℕ) (f : ℕ)
    (cell : (Σ v, Fin (characterCellSize r f v)) ≃ Fin nc)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (Q : Fin (m + 1) → Finset ℕ) (R : Fin nc → Finset ℕ)
    (hQ : ∀ i, Q i ⊆ P) (hR : ∀ i, R i ⊆ P)
    (hQmass : ∀ i, (∑ p ∈ Q i, (p : ℝ)⁻¹) ≠ 0)
    (hRmass : ∀ i, (∑ p ∈ R i, (p : ℝ)⁻¹) ≠ 0)
    (cellLo cellHi : (Σ v, Fin (characterCellSize r f v)) → ℕ)
    (hcell : ∀ i p, p ∈ R (cell i) → cellLo i ≤ p ∧ p ≤ cellHi i)
    (logX Δ τ c : ℝ) (hc : 1 ≤ c) (T : Fin k → ℝ) (a : Fin k → Bool → ℝ)
    (b : Fin (⌊4 * τ⌋₊ + 1))
    (hlo : ∀ v, Real.exp (characterLogCenter b.val T a
      (characterFillerTarget logX Δ b.val T a) (true, some v) - c) ≤ ∏ i, cellLo ⟨v, i⟩)
    (hhi : ∀ v, (∏ i, cellHi ⟨v, i⟩ : ℕ) ≤ Real.exp (characterLogCenter b.val T a
      (characterFillerTarget logX Δ b.val T a) (true, some v) + c))
    (hbin : ∀ y : Fin (((m + 1) + nc) + ((m + 1) + nc)) → P,
      productPrior (fun i => primeSubsetPrior P
        (Fin.append (Fin.append Q R) (Fin.append Q R) i)) y ≠ 0 →
      (∑ i, Real.log (((wordCopyEquiv P (m + 1) nc).symm y).1.1 i : ℝ)) ≤ 4 * τ ∧
      (∑ i, Real.log (((wordCopyEquiv P (m + 1) nc).symm y).2.1 i : ℝ)) ≤ 4 * τ)
    (χ : ∀ p : ℕ, DirichletCharacter ℂ p) (hχ : ∀ p ∈ P, χ p ≠ 1)
    (t : ∀ p : ℕ, ZMod p) (E : Finset ℤ) (ψ : 𝓢(ℝ, ℂ))
    (s ρ γ H : ℝ) (hs : ∀ x, 0 ≤ (ψ x).re) (hreal : ∀ x, (ψ x).im = 0)
    (hρ : 0 ≤ ρ) (hγ : 0 ≤ γ) (hH : 0 ≤ H)
    (hE : ∀ x ∈ E, s ≤ (ψ ((x : ℝ) / Real.exp logX)).re)
    (hword : ∀ x ∈ E, ρ ≤ ‖binnedWordAverage (fun i => primeSubsetPrior P (Q i))
      (fun _ p => χ p ((x : ZMod p) - t p))
      (fun w => wordLogBin τ (fun i => Real.log (w i : ℝ))) b‖)
    (hmean : ∀ x ∈ E, ∀ i, γ ≤
      ‖∑ p : P, (primeSubsetPrior P (R i) p : ℂ) * χ p ((x : ZMod p) - t p)‖)
    (N : ℕ) (hsupp : ∀ x : ℝ, H < |x| → 𝓕 ψ x = 0)
    (hsmall : ∀ p ∈ P, H * Real.exp (Δ + (Fintype.card (CharacterRole k) : ℝ) * c) < p)
    (hN : H * Real.exp (Δ + (Fintype.card (CharacterRole k) : ℝ) * c) ≤ N) :
    let C := (Fintype.card (CharacterRole k) : ℝ) * c
    ((E.card : ℝ) * (s * ρ ^ 2 * γ ^ (2 * nc)) -
      Real.sqrt (Real.exp logX) * (‖𝓕 ψ 0‖ *
        (∏ i, (∑ p ∈ Fin.append (Fin.append Q R) (Fin.append Q R) i, (p : ℝ)⁻¹)⁻¹) *
        ((((m + 1) + nc) + ((m + 1) + nc) : ℕ) : ℝ) ^ (((m + 1) + nc) + ((m + 1) + nc)) *
        Real.exp ((∑ p : P, (p : ℝ)⁻¹) - (Δ - C) / 2))) / Real.sqrt (Real.exp logX) ≤
      ‖wordGraphAmplitude P hP (fun i => primeSubsetPrior P (Q i))
        (fun i => primeSubsetPrior P (R i)) χ t ψ (Real.exp logX) N
        (fun w => wordLogBin τ (fun i => Real.log (w i : ℝ))) b‖ := by
  intro C
  have hwin := character_original_product_window k m nc r f cell P hP Q R cellLo cellHi
    hcell logX Δ τ c hc T a b hlo hhi hbin
  apply prime_word_fixed_bin_amplitude_norm (m + 1) nc (Nat.succ_pos _) P hP Q R hQ hR
    hQmass hRmass χ hχ t E ψ (Real.exp logX) (Real.exp_pos _)
    (fun w => wordLogBin τ (fun i => Real.log (w i : ℝ))) b s ρ γ hρ hγ hs hreal hE
    hword hmean H (Real.exp (Δ + C)) (Δ - C) (Real.exp_pos _) N hsupp hsmall
  · intro x hx
    have hu := (div_le_iff₀ (Real.exp_pos logX)).mp (hwin x hx).2
    simpa only [C, mul_comm] using hu
  · intro x hx
    have hl := (le_div_iff₀ (Real.exp_pos logX)).mp (hwin x hx).1
    simpa only [C, mul_comm] using hl
  · intro x hx
    have hu := (div_le_iff₀ (Real.exp_pos _)).mp (hwin x hx).2
    have hm := mul_le_mul_of_nonneg_left hu hH
    have hn := mul_le_mul_of_nonneg_right hN (Real.exp_nonneg logX)
    simpa only [Nat.cast_prod] using (show H * (∏ i, (x i : ℝ)) ≤ N * Real.exp logX by
      nlinarith only [hm, hn])

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_FixedBinEndpointRate
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A fixed word bin keeps its rate after selecting the finitely many cells -/
namespace Ostmann
open Filter

theorem eventual_fixed_bin_endpoint_rate (nc : ℕ) (c γ A B : ℝ)
    (hc : 0 < c) (hγ : 0 < γ) :
    ∀ᶠ m : ℕ in atTop, ∀ u ρ : ℝ,
      Real.exp (-A * m) ≤ u → Real.exp (-B * m) ≤ ρ →
      Real.exp (-(A + 2 * B + 1) * m) ≤ u * (c * ρ ^ 2 * γ ^ (2 * nc)) := by
  have hfixed : 0 < c * γ ^ (2 * nc) := by positivity
  have hsmall := ((Real.tendsto_exp_neg_atTop_nhds_zero.comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_le_const hfixed)
  filter_upwards [hsmall] with m hm u ρ hu hρ
  change Real.exp (-(m : ℝ)) ≤ c * γ ^ (2 * nc) at hm
  have hρ0 : 0 ≤ ρ := (Real.exp_pos _).le.trans hρ
  have hu0 : 0 ≤ u := (Real.exp_pos _).le.trans hu
  calc
    _ = Real.exp (-A * m) * (Real.exp (-B * m)) ^ 2 * Real.exp (-(m : ℝ)) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    _ ≤ u * ρ ^ 2 * (c * γ ^ (2 * nc)) := by
      exact mul_le_mul (mul_le_mul hu (pow_le_pow_left₀ (Real.exp_pos _).le hρ 2)
        (sq_nonneg _) hu0) hm (Real.exp_nonneg _) (mul_nonneg hu0 (sq_nonneg _))
    _ = _ := by ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterInitialRate
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The constructed character priors give a uniform initial amplitude -/
namespace Ostmann
open Filter
open scoped Classical BigOperators SchwartzMap FourierTransform

/-- The exponent depends on the endpoint and word rates, but not on the
number of selected nonword cells. That number only changes the threshold. -/
theorem eventual_character_initial_rate (k nc : ℕ)
    (a b z Cmass Ctotal Aend Bword B_D c s γ : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hz : 1 ≤ z)
    (hCmass : 0 ≤ Cmass) (hCtotal : 0 ≤ Ctotal) (hc : 1 ≤ c)
    (hs : 0 < s) (hγ : 0 < γ) (hbudget : 4 * nc * Cmass ≤ z)
    (hgap : 2 * ((2 * Real.log (3 / a) + 3 + 2 * Ctotal) +
      (Aend + 2 * Bword + 1) + 2) ≤ B_D) (ψ : 𝓢(ℝ, ℂ)) :
    ∀ᶠ m : ℕ in atTop, ∀ (r : Fin k → ℕ) (f : ℕ)
      (cell : (Σ v, Fin (characterCellSize r f v)) ≃ Fin nc)
      (L logX τ : ℝ), 0 < L → (m : ℝ) ≤ z * L → z * L ≤ 2 * m →
      ∀ (P B T₀ : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
      (Q : Fin (m + 1) → Finset ℕ) (R : Fin nc → Finset ℕ),
      Q 0 = T₀ → (∀ i : Fin m, Q i.succ = B) →
      (∀ i, Q i ⊆ P) → (∀ i, R i ⊆ P) →
      a * L ≤ ∑ p ∈ B, (p : ℝ)⁻¹ → b ≤ ∑ p ∈ T₀, (p : ℝ)⁻¹ →
      (∀ i, Real.exp (-Cmass * L) ≤ ∑ p ∈ R i, (p : ℝ)⁻¹) →
      (∑ p : P, (p : ℝ)⁻¹) ≤ Ctotal * L →
      ∀ (cellLo cellHi : (Σ v, Fin (characterCellSize r f v)) → ℕ),
      (∀ i p, p ∈ R (cell i) → cellLo i ≤ p ∧ p ≤ cellHi i) →
      ∀ (T : Fin k → ℝ) (anchor : Fin k → Bool → ℝ)
        (bin : Fin (⌊4 * τ⌋₊ + 1)),
      let Δ := (B_D + 20 * Real.log z) * m
      let C := (Fintype.card (CharacterRole k) : ℝ) * c
      (∀ v, Real.exp (characterLogCenter bin.val T anchor
        (characterFillerTarget logX Δ bin.val T anchor) (true, some v) - c) ≤
          ∏ i, cellLo ⟨v, i⟩) →
      (∀ v, (∏ i, cellHi ⟨v, i⟩ : ℕ) ≤ Real.exp (characterLogCenter bin.val T anchor
        (characterFillerTarget logX Δ bin.val T anchor) (true, some v) + c)) →
      (∀ y : Fin (((m + 1) + nc) + ((m + 1) + nc)) → P,
        productPrior (fun i => primeSubsetPrior P
          (Fin.append (Fin.append Q R) (Fin.append Q R) i)) y ≠ 0 →
        (∑ i, Real.log (((wordCopyEquiv P (m + 1) nc).symm y).1.1 i : ℝ)) ≤ 4 * τ ∧
        (∑ i, Real.log (((wordCopyEquiv P (m + 1) nc).symm y).2.1 i : ℝ)) ≤ 4 * τ) →
      ∀ (χ : ∀ p : ℕ, DirichletCharacter ℂ p), (∀ p ∈ P, χ p ≠ 1) →
      ∀ (t : ∀ p : ℕ, ZMod p) (E : Finset ℤ) (ρ H : ℝ),
      Real.sqrt (Real.exp logX) * Real.exp (-Aend * m) ≤ E.card →
      Real.exp (-Bword * m) ≤ ρ →
      (∀ x, 0 ≤ (ψ x).re) → (∀ x, (ψ x).im = 0) → 0 ≤ H →
      (∀ x ∈ E, s ≤ (ψ ((x : ℝ) / Real.exp logX)).re) →
      (∀ x ∈ E, ρ ≤ ‖binnedWordAverage (fun i => primeSubsetPrior P (Q i))
        (fun _ p => χ p ((x : ZMod p) - t p))
        (fun w => wordLogBin τ (fun i => Real.log (w i : ℝ))) bin‖) →
      (∀ x ∈ E, ∀ i, γ ≤
        ‖∑ p : P, (primeSubsetPrior P (R i) p : ℂ) * χ p ((x : ZMod p) - t p)‖) →
      ∀ N : ℕ, (∀ x : ℝ, H < |x| → 𝓕 ψ x = 0) →
      (∀ p ∈ P, H * Real.exp (Δ + C) < p) → H * Real.exp (Δ + C) ≤ N →
      Real.exp (-(Aend + 2 * Bword + 2) * m) ≤
        ‖wordGraphAmplitude P hP (fun i => primeSubsetPrior P (Q i))
          (fun i => primeSubsetPrior P (R i)) χ t ψ (Real.exp logX) N
          (fun w => wordLogBin τ (fun i => Real.log (w i : ℝ))) bin‖ := by
  let B₀ := Aend + 2 * Bword + 1
  let C := (Fintype.card (CharacterRole k) : ℝ) * c
  filter_upwards [eventual_character_repeat_rate nc a b z Cmass Ctotal B₀ B_D C
      ha hb hz hCmass hCtotal hbudget hgap ψ,
    eventual_fixed_bin_endpoint_rate nc s γ Aend Bword hs hγ,
    eventually_ge_atTop (1 : ℕ)] with m hrepeat hend hm
  intro r f cell L logX τ hL hmL hLm P B T₀ hP Q R hzero hsucc hQP hRP hB hT hR hPmass
    cellLo cellHi hcell T anchor bin Δ C' hlo hhi hbin χ hχ t E ρ H hE hρ hψ hreal hH
    hsE hword hmean N hsupp hsmall hN
  have hQpos (i : Fin (m + 1)) : 0 < ∑ p ∈ Q i, (p : ℝ)⁻¹ := by
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [hzero]
      exact hb.trans_le hT
    · rw [hsucc]
      exact (mul_pos ha hL).trans_le hB
  have hRpos (i : Fin nc) : 0 < ∑ p ∈ R i, (p : ℝ)⁻¹ :=
    (Real.exp_pos _).trans_le (hR i)
  have hraw := character_word_amplitude_lower k m nc r f cell P hP Q R hQP hRP
    (fun i => (hQpos i).ne') (fun i => (hRpos i).ne') cellLo cellHi hcell logX Δ τ c hc
    T anchor bin hlo hhi hbin χ hχ t E ψ s ρ γ H hψ hreal
    ((Real.exp_pos _).le.trans hρ) hγ.le hH hsE hword hmean N hsupp hsmall hN
  have hroot : 0 < Real.sqrt (Real.exp logX) := Real.sqrt_pos.mpr (Real.exp_pos _)
  have hmain := hend ((E.card : ℝ) / Real.sqrt (Real.exp logX)) ρ
    ((le_div_iff₀ hroot).mpr (by simpa only [mul_comm] using hE)) hρ
  have herr := hrepeat L (Cmass * L) hL hmL hLm P B T₀ Q R hzero hsucc hB hT
    (by simpa only [neg_mul] using hR) le_rfl hPmass
  have hraw' : (E.card : ℝ) / Real.sqrt (Real.exp logX) *
      (s * ρ ^ 2 * γ ^ (2 * nc)) - wordRepeatFactor P Q R ψ (Δ - C') ≤
      ‖wordGraphAmplitude P hP (fun i => primeSubsetPrior P (Q i))
        (fun i => primeSubsetPrior P (R i)) χ t ψ (Real.exp logX) N
        (fun w => wordLogBin τ (fun i => Real.log (w i : ℝ))) bin‖ := by
    convert hraw using 1
    all_goals try with_reducible_and_instances rfl
    dsimp only [wordRepeatFactor]
    field_simp
    ring
  have he : B₀ + 1 = Aend + 2 * Bword + 2 := by dsimp [B₀]; ring
  simpa only [he] using initial_amplitude_uniform_lower _ _ _ B₀ m hm hmain herr hraw'

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterLengthBounds
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform rounded character lengths -/
namespace Ostmann
open Filter

theorem eventual_character_length_bounds (z : ℝ) (hz : 1 < z) :
    ∀ᶠ L : ℝ in atTop, 0 < L ∧ 1 ≤ ⌊z * L⌋₊ ∧
      L ≤ (⌊z * L⌋₊ : ℝ) ∧ (⌊z * L⌋₊ : ℝ) ≤ z * L ∧
      z * L ≤ 2 * (⌊z * L⌋₊ : ℝ) := by
  filter_upwards [eventually_bulkCount_bounds z (by linarith),
    eventually_ge_atTop (1 / (z - 1))] with L hbounds hL
  refine ⟨hbounds.1, hbounds.2.1, ?_, hbounds.2.2.1, hbounds.2.2.2⟩
  have hz0 : 0 < z - 1 := by linarith
  have hh := (div_le_iff₀ hz0).mp hL
  have hf := Nat.lt_floor_add_one (z * L)
  nlinarith only [hh, hf]

theorem eventual_character_length_ge (z C : ℝ) (hz : 0 < z) :
    ∀ᶠ L : ℝ in atTop, C ≤ (⌊z * L⌋₊ : ℝ) := by
  exact eventually_bulkCount z hz _
    ((tendsto_natCast_atTop_atTop (R := ℝ)).eventually (eventually_ge_atTop C))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterPoissonCutoff
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual rounded initial cutoff covers the Poisson window -/
namespace Ostmann
open Filter

/-- The original two-sqrt reserve absorbs the fixed Fourier support and the
covering error of the selected cells, including the floor in the cutoff. -/
theorem eventual_character_poisson_cutoff (C H : ℝ) (hH : 0 ≤ H) :
    ∀ᶠ m : ℝ in atTop, ∀ Δ : ℝ, 0 ≤ Δ →
      H * Real.exp (Δ + C) ≤ naturalTransferCutoff Δ m 0 := by
  filter_upwards [Real.tendsto_sqrt_atTop.eventually
      (eventually_ge_atTop ((C + Real.log (2 * (H + 1))) / 2)),
    Real.tendsto_sqrt_atTop.eventually (eventually_ge_atTop (Real.log 2 / 2))]
      with m hm hlog Δ hΔ
  have hE : Real.log 2 ≤ Δ + 2 * Real.sqrt m := by linarith
  have he := (natural_exp_cutoff_bounds (Δ + 2 * Real.sqrt m) hE).2.2
  have hg : C + Real.log (2 * (H + 1)) ≤ 2 * Real.sqrt m := by linarith
  have hh := Real.exp_le_exp.mpr hg
  rw [Real.exp_add, Real.exp_log (by positivity : 0 < 2 * (H + 1))] at hh
  have hscale := mul_le_mul_of_nonneg_left hh (Real.exp_nonneg Δ)
  have hnonneg : 0 ≤ Real.exp Δ * Real.exp C := by positivity
  have he' : Real.exp (Δ + 2 * Real.sqrt m) ≤
      2 * (naturalTransferCutoff Δ m 0 : ℝ) := by
    simpa only [naturalTransferCutoff, transferErrorScale, pow_zero, one_mul, mul_one] using he
  rw [Real.exp_add] at he' ⊢
  nlinarith only [hscale, he', hnonneg]

theorem eventual_character_poisson_window (z d C H α : ℝ)
    (hz : 1 ≤ z) (hd : 0 ≤ d) (hH : 0 ≤ H) (hα : 0 < α) :
    ∀ᶠ L : ℝ in atTop,
      let m := ⌊z * L⌋₊
      let Δ := d * (m : ℝ)
      let N := naturalTransferCutoff Δ m 0
      H * Real.exp (Δ + C) ≤ N ∧
        ∀ p : ℕ, Real.exp (Real.exp (α * L)) ≤ p → H * Real.exp (Δ + C) < p := by
  have hz0 : 0 < z := by linarith
  filter_upwards [eventually_bulkCount_bounds z hz0,
    eventually_bulkCount z hz0 _
      ((tendsto_natCast_atTop_atTop (R := ℝ)).eventually
        (eventual_character_poisson_cutoff C H hH)),
    eventual_natural_cutoff_below_primes 0 d z α 1 hd hz0.le hα (by norm_num)]
      with L hm hN hp
  dsimp only
  have hbound := hN (d * (⌊z * L⌋₊ : ℝ)) (mul_nonneg hd (Nat.cast_nonneg _))
  refine ⟨hbound, ?_⟩
  intro p hmin
  have hm1 : (1 : ℝ) ≤ ⌊z * L⌋₊ := by exact_mod_cast hm.2.1
  have hmin' : Real.exp (1 * Real.exp (α * L)) ≤ (p : ℝ) := by
    simpa only [one_mul] using hmin
  exact hbound.trans_lt (by exact_mod_cast hp _ hm1 hm.2.2.1 p hmin' 0 (Nat.zero_le _))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterScheduledInitial
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Identification with the literal scheduled initial amplitude -/
namespace Ostmann
open scoped Classical BigOperators SchwartzMap FourierTransform

theorem character_initial_scheduled_amplitude (k m nc : ℕ) (r : Fin k → ℕ) (f : ℕ)
    (cell : (Σ v, Fin (characterCellSize r f v)) ≃ Fin nc)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (Q : Fin (m + 1) → Finset ℕ) (R : Fin nc → Finset ℕ)
    (cellLo cellHi : (Σ v, Fin (characterCellSize r f v)) → ℕ)
    (hcell : ∀ i q, q ∈ R (cell i) → cellLo i ≤ q ∧ q ≤ cellHi i)
    (χ : ∀ p : ℕ, DirichletCharacter ℂ p) (hχ : ∀ p ∈ P, χ p ≠ 1)
    (pivot : ℕ → (Σ v, Fin (characterSize m r f v)))
    (center : ∀ p : ℕ, ZMod p) (ψ : 𝓢(ℝ, ℂ))
    (heven : ∀ v : ℝ, 𝓕 ψ (-v) = 𝓕 ψ v)
    (logX Δ τ c : ℝ) (hc : 1 ≤ c) (T : Fin k → ℝ) (a : Fin k → Bool → ℝ)
    (V cap : ℕ → ℕ) (b : Fin (⌊4 * τ⌋₊ + 1))
    (hlo : ∀ v, Real.exp (characterLogCenter b.val T a
      (characterFillerTarget logX Δ b.val T a) (true, some v) - c) ≤ ∏ i, cellLo ⟨v, i⟩)
    (hhi : ∀ v, (∏ i, cellHi ⟨v, i⟩ : ℕ) ≤ Real.exp (characterLogCenter b.val T a
      (characterFillerTarget logX Δ b.val T a) (true, some v) + c))
    (hbin : ∀ y : Fin (((m + 1) + nc) + ((m + 1) + nc)) → P,
      productPrior (fun i => primeSubsetPrior P
        (Fin.append (Fin.append Q R) (Fin.append Q R) i)) y ≠ 0 →
      (∑ i, Real.log (((wordCopyEquiv P (m + 1) nc).symm y).1.1 i : ℝ)) ≤ 4 * τ ∧
      (∑ i, Real.log (((wordCopyEquiv P (m + 1) nc).symm y).2.1 i : ℝ)) ≤ 4 * τ) :
    let lo := initialWordAtomLower b.val (fun v => ∏ i, cellLo ⟨v, i⟩)
    let hi := initialWordAtomUpper b.val (fun v => ∏ i, cellHi ⟨v, i⟩)
    let C := (Fintype.card (CharacterRole k) : ℝ) * c
    let χ₀ := signedAtomCharacter (initialWordSize (m + 1) (characterCellSize r f)) χ
    scheduledConstituentAmplitude (characterRole k) (characterSize m r f) χ₀
      (fun i => primeGaussMultiplier (χ₀ i)) pivot P hP
      (characterFullPrimeCells m r f Q (fun v i => R (cell ⟨v, i⟩))) lo hi V cap
      (scheduleFourierLeaf (characterRole k) ψ (Real.exp logX)
        (Real.exp (Δ - C)) (Real.exp (Δ + C))) center 0 =
    wordGraphAmplitude P hP (fun i => primeSubsetPrior P (Q i))
      (fun j => primeSubsetPrior P (R j)) χ center ψ (Real.exp logX) (V 0)
      (fun w => wordLogBin τ (fun i => Real.log (w i : ℝ))) b := by
  have hh := character_initial_amplitude k m nc r f cell P hP Q R cellLo cellHi hcell
    χ hχ pivot center ψ heven logX Δ τ c hc T a (V 0) V cap b hlo hhi hbin
  have hQ : (fun i => Fin.append (Fin.append Q R) (Fin.append Q R)
      (initialWordTupleEquiv (m + 1) nc (characterCellSize r f) cell i)) =
      characterFullPrimeCells m r f Q (fun v i => R (cell ⟨v, i⟩)) := by
    funext i
    have he := characterFullPrimeCells_source m nc r f cell Q
      (fun v j => R (cell ⟨v, j⟩)) i
    simpa only [cell.apply_symm_apply] using he
  have hχ₀ : (fun i : Σ v, Fin (characterSize m r f v) => wordCopyCharacter (m + 1) nc χ
      (initialWordTupleEquiv (m + 1) nc (characterCellSize r f) cell i)) =
      signedAtomCharacter (initialWordSize (m + 1) (characterCellSize r f)) χ := by
    funext i
    exact initialWordTupleEquiv_character (m + 1) nc (characterCellSize r f) cell χ i
  have hκ : (fun i : Σ v, Fin (characterSize m r f v) => primeGaussMultiplier (wordCopyCharacter (m + 1) nc χ
      (initialWordTupleEquiv (m + 1) nc (characterCellSize r f) cell i))) =
      (fun i => primeGaussMultiplier
        (signedAtomCharacter (initialWordSize (m + 1) (characterCellSize r f)) χ i)) := by
    funext i
    exact congrArg primeGaussMultiplier (congrFun hχ₀ i)
  dsimp only at hh
  dsimp only
  unfold scheduledConstituentAmplitude
  apply Eq.trans ?_ hh
  congr 1
  · exact hχ₀.symm
  · exact hκ.symm
  · exact hQ.symm

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterWordSupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Supported top-first words retain their actual logarithmic bin -/
namespace Ostmann
open scoped Classical BigOperators

theorem top_first_word_log_bounds (m : ℕ) (ℓ : Fin (m + 1) → ℝ) (b τ : ℝ)
    (hbulk : ∀ i : Fin m, 0 ≤ ℓ i.succ ∧ ℓ i.succ ≤ b)
    (hsize : (m : ℝ) * b ≤ τ) (htop : τ ≤ ℓ 0 ∧ ℓ 0 ≤ 3 * τ) :
    τ ≤ ∑ i, ℓ i ∧ (∑ i, ℓ i) ≤ 4 * τ := by
  have h₀ : 0 ≤ ∑ i : Fin m, ℓ i.succ :=
    Finset.sum_nonneg (fun i _ => (hbulk i).1)
  have h₁ : (∑ i : Fin m, ℓ i.succ) ≤ (m : ℝ) * b := by
    calc
      _ ≤ ∑ _i : Fin m, b := Finset.sum_le_sum (fun i _ => (hbulk i).2)
      _ = _ := by simp
  rw [Fin.sum_univ_succ]
  constructor <;> linarith [htop.1, htop.2]

theorem supported_character_word_bounds (m : ℕ) (P U T : Finset ℕ)
    (Q : Fin (m + 1) → Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hzero : Q 0 = T) (hsucc : ∀ i : Fin m, Q i.succ = U)
    (b τ : ℝ) (hsize : (m : ℝ) * b ≤ τ)
    (htop : ∀ p ∈ T, τ ≤ Real.log (p : ℝ) ∧ Real.log (p : ℝ) ≤ 3 * τ)
    (hbulk : ∀ p ∈ U, Real.log (p : ℝ) ≤ b)
    (w : Fin (m + 1) → P)
    (hw : productPrior (fun i => primeSubsetPrior P (Q i)) w ≠ 0) :
    τ ≤ ∑ i, Real.log (w i : ℝ) ∧ (∑ i, Real.log (w i : ℝ)) ≤ 4 * τ := by
  have hs (i : Fin (m + 1)) : (w i : ℕ) ∈ Q i := by
    apply primeSubsetPrior_support P (Q i) (w i)
    exact (Finset.prod_ne_zero_iff.mp hw) i (Finset.mem_univ i)
  apply top_first_word_log_bounds m _ b τ
  · intro i
    constructor
    · exact Real.log_nonneg (by exact_mod_cast (hP (w i.succ) (w i.succ).property).one_le)
    · apply hbulk
      simpa only [hsucc] using hs i.succ
  · exact hsize
  · apply htop
    simpa only [hzero] using hs 0

/-- Nonzero mass for the complete two-copy tuple forces nonzero mass for
both original word marginals. -/
theorem wordCopyPrior_word_support {A : Type*} (k nc : ℕ)
    (μ : Fin k → A → ℝ) (ν : Fin nc → A → ℝ)
    (y : Fin ((k + nc) + (k + nc)) → A)
    (hy : productPrior (Fin.append (Fin.append μ ν) (Fin.append μ ν)) y ≠ 0) :
    productPrior μ ((wordCopyEquiv A k nc).symm y).1.1 ≠ 0 ∧
      productPrior μ ((wordCopyEquiv A k nc).symm y).2.1 ≠ 0 := by
  have h := wordCopyPrior μ ν ((wordCopyEquiv A k nc).symm y)
  rw [Equiv.apply_symm_apply] at h
  rw [h] at hy
  change (productPrior μ _ * productPrior ν _) *
    (productPrior μ _ * productPrior ν _) ≠ 0 at hy
  exact ⟨(mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hy).1).1,
    (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hy).2).1⟩

theorem character_initial_word_support (m nc : ℕ) (P U T : Finset ℕ)
    (Q : Fin (m + 1) → Finset ℕ) (R : Fin nc → Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hzero : Q 0 = T)
    (hsucc : ∀ i : Fin m, Q i.succ = U)
    (b τ : ℝ) (hsize : (m : ℝ) * b ≤ τ)
    (htop : ∀ p ∈ T, τ ≤ Real.log (p : ℝ) ∧ Real.log (p : ℝ) ≤ 3 * τ)
    (hbulk : ∀ p ∈ U, Real.log (p : ℝ) ≤ b)
    (y : Fin (((m + 1) + nc) + ((m + 1) + nc)) → P)
    (hy : productPrior (fun i => primeSubsetPrior P
      (Fin.append (Fin.append Q R) (Fin.append Q R) i)) y ≠ 0) :
    (∑ i, Real.log (((wordCopyEquiv P (m + 1) nc).symm y).1.1 i : ℝ)) ≤ 4 * τ ∧
    (∑ i, Real.log (((wordCopyEquiv P (m + 1) nc).symm y).2.1 i : ℝ)) ≤ 4 * τ := by
  have he : (fun i => primeSubsetPrior P
      (Fin.append (Fin.append Q R) (Fin.append Q R) i)) =
      Fin.append (Fin.append (fun i => primeSubsetPrior P (Q i))
        (fun i => primeSubsetPrior P (R i)))
        (Fin.append (fun i => primeSubsetPrior P (Q i)) (fun i => primeSubsetPrior P (R i))) := by
    change (primeSubsetPrior P ∘ Fin.append (Fin.append Q R) (Fin.append Q R)) = _
    rw [← map_fin_append, ← map_fin_append]
    rfl
  rw [he] at hy
  have hw := wordCopyPrior_word_support (m + 1) nc _ _ y hy
  exact ⟨(supported_character_word_bounds m P U T Q hP hzero hsucc b τ hsize htop hbulk _ hw.1).2,
    (supported_character_word_bounds m P U T Q hP hzero hsucc b τ hsize htop hbulk _ hw.2).2⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterScheduledInitialRate
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual endpoint statistic starts the scheduled character iteration -/
namespace Ostmann
open Filter
open scoped Classical BigOperators SchwartzMap FourierTransform

theorem eventual_character_scheduled_initial_rate (k nc : ℕ)
    (a b z Cmass Ctotal Aend Bword B c s γ H α : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hz : 1 < z)
    (hCmass : 0 ≤ Cmass) (hCtotal : 0 ≤ Ctotal) (hc : 1 ≤ c)
    (hs : 0 < s) (hγ : 0 < γ) (hH : 0 ≤ H) (hα : 0 < α)
    (hbudget : 4 * nc * Cmass ≤ z)
    (hgap : 2 * ((2 * Real.log (3 / a) + 3 + 2 * Ctotal) +
      (Aend + 2 * Bword + 1) + 2) ≤ B) (hB : 0 ≤ B)
    (ψ : 𝓢(ℝ, ℂ)) (hψ : ∀ x, 0 ≤ (ψ x).re) (hreal : ∀ x, (ψ x).im = 0)
    (heven : ∀ v : ℝ, 𝓕 ψ (-v) = 𝓕 ψ v)
    (hsupp : ∀ x : ℝ, H < |x| → 𝓕 ψ x = 0) :
    ∀ᶠ L : ℝ in atTop,
    let m := ⌊z * L⌋₊
    ∀ (r : Fin k → ℕ) (f : ℕ)
      (_cell : (Σ v, Fin (characterCellSize r f v)) ≃ Fin nc)
      (logX τ bmax : ℝ) (P U T₀ : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
      (Q : Fin (m + 1) → Finset ℕ)
      (R : (v : CharacterCell k) → Fin (characterCellSize r f v) → Finset ℕ),
    Q 0 = T₀ → (∀ i : Fin m, Q i.succ = U) →
    (∀ i, Q i ⊆ P) → (∀ v i, R v i ⊆ P) →
    a * L ≤ ∑ p ∈ U, (p : ℝ)⁻¹ → b ≤ ∑ p ∈ T₀, (p : ℝ)⁻¹ →
    (∀ v i, Real.exp (-Cmass * L) ≤ ∑ p ∈ R v i, (p : ℝ)⁻¹) →
    (∑ p : P, (p : ℝ)⁻¹) ≤ Ctotal * L →
    (∀ p ∈ P, Real.exp (Real.exp (α * L)) ≤ p) →
    (m : ℝ) * bmax ≤ τ →
    (∀ p ∈ T₀, τ ≤ Real.log (p : ℝ) ∧ Real.log (p : ℝ) ≤ 3 * τ) →
    (∀ p ∈ U, Real.log (p : ℝ) ≤ bmax) →
    ∀ (cellLo cellHi : (Σ v, Fin (characterCellSize r f v)) → ℕ),
    (∀ v i p, p ∈ R v i → cellLo ⟨v, i⟩ ≤ p ∧ p ≤ cellHi ⟨v, i⟩) →
    ∀ (anchor : Fin k → Bool → ℝ) (bin : Fin (⌊4 * τ⌋₊ + 1)),
    let Δ := characterBaseGap B z m
    let T := characterPivotTarget k bin.val (fun j => anchor j false + anchor j true)
      (fun j => characterPivotGap B z m j.val)
    let F := characterFillerTarget logX Δ bin.val T anchor
    (∀ v, Real.exp (characterLogCenter bin.val T anchor F (true, some v) - c) ≤
      ∏ i, cellLo ⟨v, i⟩) →
    (∀ v, (∏ i, cellHi ⟨v, i⟩ : ℕ) ≤
      Real.exp (characterLogCenter bin.val T anchor F (true, some v) + c)) →
    ∀ (χ : ∀ p : ℕ, DirichletCharacter ℂ p), (∀ p ∈ P, χ p ≠ 1) →
    ∀ (center : ∀ p : ℕ, ZMod p) (E : Finset ℤ) (ρ : ℝ),
    Real.sqrt (Real.exp logX) * Real.exp (-Aend * m) ≤ E.card →
    Real.exp (-Bword * m) ≤ ρ →
    (∀ x ∈ E, s ≤ (ψ ((x : ℝ) / Real.exp logX)).re) →
    (∀ x ∈ E, ρ ≤ ‖binnedWordAverage (fun i => primeSubsetPrior P (Q i))
      (fun _ p => χ p ((x : ZMod p) - center p))
      (fun w => wordLogBin τ (fun i => Real.log (w i : ℝ))) bin‖) →
    (∀ x ∈ E, ∀ v i, γ ≤
      ‖∑ p : P, (primeSubsetPrior P (R v i) p : ℂ) * χ p ((x : ZMod p) - center p)‖) →
    ∀ pivot : ℕ → (Σ v, Fin (characterSize m r f v)),
    let V := naturalTransferCutoff Δ m
    let cap := characterPivotCap T (characterRangeError k c)
    let lo := initialWordAtomLower bin.val (fun v => ∏ i, cellLo ⟨v, i⟩)
    let hi := initialWordAtomUpper bin.val (fun v => ∏ i, cellHi ⟨v, i⟩)
    let χ₀ := signedAtomCharacter (initialWordSize (m + 1) (characterCellSize r f)) χ
    Real.exp (-(Aend + 2 * Bword + 2) * m) ≤
      ‖scheduledConstituentAmplitude (characterRole k) (characterSize m r f) χ₀
        (fun i => primeGaussMultiplier (χ₀ i)) pivot P hP
        (characterFullPrimeCells m r f Q R) lo hi V cap
        (scheduleFourierLeaf (characterRole k) ψ (Real.exp logX)
          (Real.exp (Δ - (Fintype.card (CharacterRole k) : ℝ) * c))
          (Real.exp (Δ + (Fintype.card (CharacterRole k) : ℝ) * c))) center 0‖ := by
  have hrate := eventual_character_initial_rate k nc a b z Cmass Ctotal Aend Bword B c s γ
    ha hb hz.le hCmass hCtotal hc hs hγ hbudget hgap ψ
  have hd : 0 ≤ B + 20 * Real.log z := by linarith [Real.log_nonneg hz.le]
  filter_upwards [eventually_bulkCount z (by linarith) _ hrate,
    eventual_character_poisson_window z (B + 20 * Real.log z)
      ((Fintype.card (CharacterRole k) : ℝ) * c) H α hz.le hd hH hα,
    eventual_character_length_bounds z hz] with L hrate hwindow hlength
  intro m r f cell logX τ bmax P U T₀ hP Q R hzero hsucc hQP hRP hbulk htop hR htotal
    hPlower hsize htoplog hbulklog cellLo cellHi hcell anchor bin Δ T F hlo hhi χ hχ
    center E ρ hE hρ hsE hword hmean pivot V cap lo hi χ₀
  let Rflat : Fin nc → Finset ℕ := fun j => R (cell.symm j).1 (cell.symm j).2
  have hRf (i) : Rflat (cell i) = R i.1 i.2 := by
    dsimp only [Rflat]
    rw [cell.symm_apply_apply]
  have hcell' (i) (p) (hp : p ∈ Rflat (cell i)) : cellLo i ≤ p ∧ p ≤ cellHi i := by
    rw [hRf] at hp
    exact hcell i.1 i.2 p hp
  have hbin := character_initial_word_support m nc P U T₀ Q Rflat hP hzero hsucc bmax τ
    hsize htoplog hbulklog
  have hraw := hrate r f cell L logX τ hlength.1 hlength.2.2.2.1 hlength.2.2.2.2
    P U T₀ hP Q Rflat hzero hsucc hQP (fun j => hRP _ _) hbulk htop
    (fun j => hR _ _) htotal cellLo cellHi hcell' T anchor bin hlo hhi hbin χ hχ center E ρ H
    hE hρ hψ hreal hH hsE hword (fun x hx j => hmean x hx _ _) (V 0) hsupp
    (fun p hp => hwindow.2 p (hPlower p hp)) hwindow.1
  have he := character_initial_scheduled_amplitude k m nc r f cell P hP Q Rflat
    cellLo cellHi hcell' χ hχ pivot center ψ heven logX Δ τ c hc T anchor V cap bin
    hlo hhi hbin
  have hRcell : (fun v i => Rflat (cell ⟨v, i⟩)) = R := by
    funext v i
    exact hRf ⟨v, i⟩
  rw [hRcell] at he
  exact he.symm ▸ hraw

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterIterationContradiction
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite character transfer and the final contradiction

All diagonal and final comparison bounds here are derived from the physical
prime ranges and original harmonic priors. The initial amplitude is supplied
by the separately proved fixed-bin endpoint statistic.
-/
namespace Ostmann
open Filter
open scoped Classical BigOperators SchwartzMap FourierTransform ComplexConjugate

theorem eventual_character_iteration_contradiction (n N Bnb : ℕ)
    (r : Fin (n + 1) → ℕ) (f : ℕ) (hr : ∀ j, 0 < r j)
    (hrN : ∀ j, r j ≤ N) (hf : f ≤ N)
    (hnb : 1 + ((∑ j, r j) + 2 * (n + 1)) ≤ Bnb)
    (ψ : 𝓢(ℝ, ℂ)) (hreal : ∀ x, conj (ψ x) = ψ x)
    (K B B₁ z c a b Cmass α βg βw γs βa γw νw νa ε : ℝ)
    (hB : 1 ≤ B) (hBstrong : 2 * B₁ + 5 ≤ B) (hB₁ : 0 ≤ B₁)
    (hz : 1 < z) (hc : 1 ≤ c) (ha : 0 < a) (ha1 : a ≤ 1) (hb : 0 < b)
    (hCmass : 0 < Cmass) (hα : 0 < α) (hβg : 0 < βg) (hγw : 0 ≤ γw)
    (hαw : α < βw) (hsw : γs < βw) (hαa : α < βa)
    (hwa : γw < βa) (hwg : γw ≤ βg) (hβw : βw < νw) (hβa : βa < νa)
    (hε : 0 < ε) (hbudget : 4 * Cmass * Bnb ≤ z)
    (hpivot : Cmass * (∑ j, (r j : ℝ)) ≤ z / 4)
    (hgap : 2 * B₁ +
      ((γw + Real.log ((Real.log 2)⁻¹ + 1)) / a + max (Real.log 3) 0 + ε) +
      Real.log 2 + 6 ≤ B + 20 * Real.log a)
    (hψ : SchwartzMap.seminorm ℝ 0 0 (𝓕 ψ : 𝓢(ℝ, ℂ)) ≤ Real.exp K)
    (hentropy : (βg + Real.log ((Real.log 2)⁻¹ + 1) + max (Real.log 3) 0 + ε) +
      (B + 20 * Real.log z + 1) + 2 * B₁ + 1 ≤ (n : ℝ) * Real.log 2 - 1) :
    ∀ᶠ L : ℝ in atTop,
      let m := ⌊z * L⌋₊
      ∀ (P U : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
        (Q : Fin (m + 1) → Finset ℕ)
        (R : (v : CharacterCell (n + 1)) → Fin (characterCellSize r f v) → Finset ℕ),
      (∀ i : Fin m, Q i.succ = U) → Disjoint U (Q 0) →
      (∀ v i, Disjoint U (R v i)) →
      (∀ i, Q i ⊆ P) → (∀ v i, R v i ⊆ P) →
      b ≤ ∑ p ∈ Q 0, (p : ℝ)⁻¹ → a * L ≤ ∑ p ∈ U, (p : ℝ)⁻¹ →
      (∀ v i, Real.exp (-Cmass * L) ≤ ∑ p ∈ R v i, (p : ℝ)⁻¹) →
      (∀ p ∈ P, Real.exp (Real.exp (α * L)) ≤ p ∧
        (p : ℝ) ≤ Real.exp (Real.exp (βg * L))) →
      (∀ p ∈ U, Real.exp (Real.exp (νw * L)) ≤ p ∧
        (p : ℝ) ≤ Real.exp (Real.exp (γw * L))) →
      (∀ j p, p ∈ R (.inr (.inl (j, false))) ⟨0, by change 0 < 1; omega⟩ →
        (p : ℝ) ≤ Real.exp (Real.exp (γs * L))) →
      (∀ j p, p ∈ R (.inr (.inl (j, true))) ⟨0, by change 0 < 1; omega⟩ →
        Real.exp (Real.exp (νa * L)) ≤ p) →
      ∀ (χ : ∀ p : ℕ, DirichletCharacter ℂ p), (∀ p ∈ P, χ p ^ 2 ≠ 1) →
      ∀ (J : ℕ), 0 < J → ∀ (anchor : Fin (n + 1) → Bool → ℝ) (F logX : ℝ), 0 < logX →
      let Δ := characterBaseGap B z m
      let T := characterPivotTarget (n + 1) J (fun j => anchor j false + anchor j true)
        (fun j => characterPivotGap B z m j.val)
      (∀ j, T j + c ≤ Real.exp (βg * L)) →
      ∀ cellLo cellHi : (Σ v, Fin (characterSize m r f v)) → ℕ,
      (∀ i p, p ∈ characterFullPrimeCells m r f Q R i →
        cellLo i ≤ p ∧ p ≤ cellHi i) →
      (∀ v, Real.exp (characterLogCenter J T anchor F (true, some v) - c) ≤
        ∏ i, cellLo ⟨(true, some v), i⟩) →
      (∀ v, (∏ i, cellHi ⟨(true, some v), i⟩ : ℕ) ≤
        Real.exp (characterLogCenter J T anchor F (true, some v) + c)) →
      ∀ center : ∀ p : ℕ, ZMod p,
      let lo := initialWordAtomLower J (fun v => ∏ i, cellLo ⟨(true, some v), i⟩)
      let hi := initialWordAtomUpper J (fun v => ∏ i, cellHi ⟨(true, some v), i⟩)
      let χ₀ := signedAtomCharacter (initialWordSize (m + 1) (characterCellSize r f)) χ
      let V := naturalTransferCutoff Δ m
      let cap := characterPivotCap T (characterRangeError (n + 1) c)
      Real.exp (-(B₁ - 1) * m) ≤
        ‖scheduledConstituentAmplitude (characterRole (n + 1)) (characterSize m r f) χ₀
          (fun i => primeGaussMultiplier (χ₀ i)) (characterPivot m r f hr) P hP
          (characterFullPrimeCells m r f Q R) lo hi V cap
          (scheduleFourierLeaf (characterRole (n + 1)) ψ (Real.exp logX)
            (Real.exp (Δ - (Fintype.card (CharacterRole (n + 1)) : ℝ) * c))
            (Real.exp (Δ + (Fintype.card (CharacterRole (n + 1)) : ℝ) * c))) center 0‖ → False := by
  have hz0 : 0 < z := by linarith
  have hdiag := fun j : Fin (n + 1) => eventual_character_diagonal_decay (n + 1) j.val Bnb N
    j.isLt ψ hreal K B B₁ z c a b Cmass α βg βw γs βa γw νw νa ε hB hBstrong hz.le hc
    ha ha1 hb hCmass hα hβg hγw hαw hsw hαa hwa hwg hβw hβa hε hbudget hgap hψ
  choose M hM using hdiag
  have hall := eventually_all.mpr hM
  have hthreshold := eventually_all.mpr (fun j => eventual_character_length_ge z (M j) hz0)
  obtain ⟨Mf, hfinal⟩ := eventual_character_final_contradiction n N ψ hreal K B B₁ z c
    Cmass α βg βw γs νw ε hB hB₁ hz.le hc hCmass hα hβg hαw hsw hβw hε hψ hentropy
  filter_upwards [hall, hthreshold, hfinal, eventual_character_length_ge z Mf hz0,
    eventual_character_length_bounds z hz,
    eventual_character_atom_iteration (n + 1) r f hr B (B₁ - 1) z c Cmass (by linarith) hz.le hc
      hCmass.le hpivot,
    eventual_full_character_mass_floor a b Cmass ha hb hCmass,
    (tendsto_id.const_mul_atTop ha).eventually (eventually_ge_atTop (1 : ℝ)),
    eventual_natural_cutoff_below_primes (n + 1) (B + 20 * Real.log z) z α 1
      (by linarith [Real.log_nonneg hz.le]) hz0.le hα (by norm_num)]
    with L hd hth hfina hMf hlength hiter hmass haL hlarge
  intro m P U hP Q R hQU htop hdis hQP hRP htopmass hbulk hRmass hPrange hUrange
    hsmall hbig χ hχ J hJ anchor F logX hlogX Δ T hT cellLo cellHi hcell hlo hhi
    center lo hi χ₀ V cap hinit
  have hm : (1 : ℝ) ≤ m := by exact_mod_cast hlength.2.1
  have hLm : L ≤ (m : ℝ) := hlength.2.2.1
  have hmL : (m : ℝ) ≤ z * L := hlength.2.2.2.1
  have hLm₂ : z * L ≤ 2 * m := hlength.2.2.2.2
  have hQall := characterFullPrimeCells_subset m r f P Q R hQP hRP
  have hmassall := hmass (n + 1) m r f Q R htopmass
    (fun i => by rw [hQU]; exact hbulk) hRmass
  have hpos (i) : (∑ p ∈ characterFullPrimeCells m r f Q R i, (p : ℝ)⁻¹) ≠ 0 :=
    ne_of_gt ((Real.exp_pos _).trans_le (hmassall i))
  have hlargeall (p : ℕ) (hp : p ∈ P) : V (n + 1) < p :=
    hlarge m hm hmL p (by simpa only [one_mul] using (hPrange p hp).1) (n + 1) le_rfl
  have hdiagonal (j : ℕ) (hj : j < n + 1) :=
    hd ⟨j, hj⟩ m (hth ⟨j, hj⟩) hLm hmL hLm₂ r f hr hnb hrN hf P U hP Q R
      hQU htop hdis hQP hRP htopmass hbulk hRmass hPrange hUrange hsmall hbig χ hχ
      J hJ anchor F logX hlogX (hT ⟨j, hj⟩)
      (fun v => ∏ i, cellLo ⟨(true, some v), i⟩)
      (fun v => ∏ i, cellHi ⟨(true, some v), i⟩) hlo hhi center
  have htransfer := hiter J hJ anchor F cellLo cellHi χ₀
    (fun i => primeGaussMultiplier (χ₀ i)) P hP (characterFullPrimeCells m r f Q R)
    (scheduleFourierLeaf (characterRole (n + 1)) ψ (Real.exp logX)
      (Real.exp (Δ - (Fintype.card (CharacterRole (n + 1)) : ℝ) * c))
      (Real.exp (Δ + (Fintype.card (CharacterRole (n + 1)) : ℝ) * c))) center
    (fun _ _ _ => (primeGaussMultiplier_norm _ _).le) hQall hpos hcell hlo hhi
    (fun j i => harmonic_mass_inv_le_exp _ Cmass L (hRmass (.inl j) i))
    hlargeall hinit (by
      intro j hj
      simpa only [sub_add_cancel, characterPivotRole_eq hj, Nat.cast_pow, Nat.cast_ofNat]
        using hdiagonal j hj)
  have hlast := hfina m hMf hLm hmL r f hr hrN hf P hP
    (characterFullPrimeCells m r f Q R) hQall hmassall hPrange hsmall
    (fun i p hp => by
      rw [characterFullPrimeCells_bulk, hQU] at hp
      exact (hUrange p hp).1)
    (fun i => by
      rw [characterFullPrimeCells_bulk, hQU]
      exact haL.trans hbulk) χ hχ J
    (fun v => ∏ i, cellLo ⟨(true, some v), i⟩)
    (fun v => ∏ i, cellHi ⟨(true, some v), i⟩) logX hlogX cap center
  apply hlast
  simpa only [sub_add_cancel] using htransfer

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterUniformIteration
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The finite character contradiction is uniform over the chosen word lengths -/
namespace Ostmann
open Filter
open scoped Classical BigOperators SchwartzMap FourierTransform ComplexConjugate

theorem eventual_uniform_character_iteration_contradiction (n N Bnb : ℕ)
    (ψ : 𝓢(ℝ, ℂ)) (hreal : ∀ x, conj (ψ x) = ψ x)
    (K B B₁ z c a b Cmass α βg βw γs βa γw νw νa ε : ℝ)
    (hB : 1 ≤ B) (hBstrong : 2 * B₁ + 5 ≤ B) (hB₁ : 0 ≤ B₁)
    (hz : 1 < z) (hc : 1 ≤ c) (ha : 0 < a) (ha1 : a ≤ 1) (hb : 0 < b)
    (hCmass : 0 < Cmass) (hα : 0 < α) (hβg : 0 < βg) (hγw : 0 ≤ γw)
    (hαw : α < βw) (hsw : γs < βw) (hαa : α < βa)
    (hwa : γw < βa) (hwg : γw ≤ βg) (hβw : βw < νw) (hβa : βa < νa)
    (hε : 0 < ε) (hbudget : 4 * Cmass * Bnb ≤ z)
    (hgap : 2 * B₁ +
      ((γw + Real.log ((Real.log 2)⁻¹ + 1)) / a + max (Real.log 3) 0 + ε) +
      Real.log 2 + 6 ≤ B + 20 * Real.log a)
    (hψ : SchwartzMap.seminorm ℝ 0 0 (𝓕 ψ : 𝓢(ℝ, ℂ)) ≤ Real.exp K)
    (hentropy : (βg + Real.log ((Real.log 2)⁻¹ + 1) + max (Real.log 3) 0 + ε) +
      (B + 20 * Real.log z + 1) + 2 * B₁ + 1 ≤ (n : ℝ) * Real.log 2 - 1) :
    ∀ᶠ L : ℝ in atTop, ∀ (r : Fin (n + 1) → ℕ) (f : ℕ),
      (∀ j, r j ≤ N) → f ≤ N → ∀ (hr : ∀ j, 0 < r j),
      1 + ((∑ j, r j) + 2 * (n + 1)) ≤ Bnb →
      Cmass * (∑ j, (r j : ℝ)) ≤ z / 4 →
      let m := ⌊z * L⌋₊
      ∀ (P U : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
        (Q : Fin (m + 1) → Finset ℕ)
        (R : (v : CharacterCell (n + 1)) → Fin (characterCellSize r f v) → Finset ℕ),
      (∀ i : Fin m, Q i.succ = U) → Disjoint U (Q 0) →
      (∀ v i, Disjoint U (R v i)) →
      (∀ i, Q i ⊆ P) → (∀ v i, R v i ⊆ P) →
      b ≤ ∑ p ∈ Q 0, (p : ℝ)⁻¹ → a * L ≤ ∑ p ∈ U, (p : ℝ)⁻¹ →
      (∀ v i, Real.exp (-Cmass * L) ≤ ∑ p ∈ R v i, (p : ℝ)⁻¹) →
      (∀ p ∈ P, Real.exp (Real.exp (α * L)) ≤ p ∧
        (p : ℝ) ≤ Real.exp (Real.exp (βg * L))) →
      (∀ p ∈ U, Real.exp (Real.exp (νw * L)) ≤ p ∧
        (p : ℝ) ≤ Real.exp (Real.exp (γw * L))) →
      (∀ j p, p ∈ R (.inr (.inl (j, false))) ⟨0, by change 0 < 1; omega⟩ →
        (p : ℝ) ≤ Real.exp (Real.exp (γs * L))) →
      (∀ j p, p ∈ R (.inr (.inl (j, true))) ⟨0, by change 0 < 1; omega⟩ →
        Real.exp (Real.exp (νa * L)) ≤ p) →
      ∀ (χ : ∀ p : ℕ, DirichletCharacter ℂ p), (∀ p ∈ P, χ p ^ 2 ≠ 1) →
      ∀ (J : ℕ), 0 < J → ∀ (anchor : Fin (n + 1) → Bool → ℝ) (F logX : ℝ), 0 < logX →
      let Δ := characterBaseGap B z m
      let T := characterPivotTarget (n + 1) J (fun j => anchor j false + anchor j true)
        (fun j => characterPivotGap B z m j.val)
      (∀ j, T j + c ≤ Real.exp (βg * L)) →
      ∀ cellLo cellHi : (Σ v, Fin (characterSize m r f v)) → ℕ,
      (∀ i p, p ∈ characterFullPrimeCells m r f Q R i →
        cellLo i ≤ p ∧ p ≤ cellHi i) →
      (∀ v, Real.exp (characterLogCenter J T anchor F (true, some v) - c) ≤
        ∏ i, cellLo ⟨(true, some v), i⟩) →
      (∀ v, (∏ i, cellHi ⟨(true, some v), i⟩ : ℕ) ≤
        Real.exp (characterLogCenter J T anchor F (true, some v) + c)) →
      ∀ center : ∀ p : ℕ, ZMod p,
      let lo := initialWordAtomLower J (fun v => ∏ i, cellLo ⟨(true, some v), i⟩)
      let hi := initialWordAtomUpper J (fun v => ∏ i, cellHi ⟨(true, some v), i⟩)
      let χ₀ := signedAtomCharacter (initialWordSize (m + 1) (characterCellSize r f)) χ
      let V := naturalTransferCutoff Δ m
      let cap := characterPivotCap T (characterRangeError (n + 1) c)
      Real.exp (-(B₁ - 1) * m) ≤
        ‖scheduledConstituentAmplitude (characterRole (n + 1)) (characterSize m r f) χ₀
          (fun i => primeGaussMultiplier (χ₀ i)) (characterPivot m r f hr) P hP
          (characterFullPrimeCells m r f Q R) lo hi V cap
          (scheduleFourierLeaf (characterRole (n + 1)) ψ (Real.exp logX)
            (Real.exp (Δ - (Fintype.card (CharacterRole (n + 1)) : ℝ) * c))
            (Real.exp (Δ + (Fintype.card (CharacterRole (n + 1)) : ℝ) * c))) center 0‖ → False := by
  let F (r : Fin (n + 1) → ℕ) (f : ℕ) (L : ℝ) : Prop := ∀ (hr : ∀ j, 0 < r j),
      1 + ((∑ j, r j) + 2 * (n + 1)) ≤ Bnb →
      Cmass * (∑ j, (r j : ℝ)) ≤ z / 4 →
      let m := ⌊z * L⌋₊
      ∀ (P U : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
        (Q : Fin (m + 1) → Finset ℕ)
        (R : (v : CharacterCell (n + 1)) → Fin (characterCellSize r f v) → Finset ℕ),
      (∀ i : Fin m, Q i.succ = U) → Disjoint U (Q 0) →
      (∀ v i, Disjoint U (R v i)) →
      (∀ i, Q i ⊆ P) → (∀ v i, R v i ⊆ P) →
      b ≤ ∑ p ∈ Q 0, (p : ℝ)⁻¹ → a * L ≤ ∑ p ∈ U, (p : ℝ)⁻¹ →
      (∀ v i, Real.exp (-Cmass * L) ≤ ∑ p ∈ R v i, (p : ℝ)⁻¹) →
      (∀ p ∈ P, Real.exp (Real.exp (α * L)) ≤ p ∧
        (p : ℝ) ≤ Real.exp (Real.exp (βg * L))) →
      (∀ p ∈ U, Real.exp (Real.exp (νw * L)) ≤ p ∧
        (p : ℝ) ≤ Real.exp (Real.exp (γw * L))) →
      (∀ j p, p ∈ R (.inr (.inl (j, false))) ⟨0, by change 0 < 1; omega⟩ →
        (p : ℝ) ≤ Real.exp (Real.exp (γs * L))) →
      (∀ j p, p ∈ R (.inr (.inl (j, true))) ⟨0, by change 0 < 1; omega⟩ →
        Real.exp (Real.exp (νa * L)) ≤ p) →
      ∀ (χ : ∀ p : ℕ, DirichletCharacter ℂ p), (∀ p ∈ P, χ p ^ 2 ≠ 1) →
      ∀ (J : ℕ), 0 < J → ∀ (anchor : Fin (n + 1) → Bool → ℝ) (F logX : ℝ), 0 < logX →
      let Δ := characterBaseGap B z m
      let T := characterPivotTarget (n + 1) J (fun j => anchor j false + anchor j true)
        (fun j => characterPivotGap B z m j.val)
      (∀ j, T j + c ≤ Real.exp (βg * L)) →
      ∀ cellLo cellHi : (Σ v, Fin (characterSize m r f v)) → ℕ,
      (∀ i p, p ∈ characterFullPrimeCells m r f Q R i →
        cellLo i ≤ p ∧ p ≤ cellHi i) →
      (∀ v, Real.exp (characterLogCenter J T anchor F (true, some v) - c) ≤
        ∏ i, cellLo ⟨(true, some v), i⟩) →
      (∀ v, (∏ i, cellHi ⟨(true, some v), i⟩ : ℕ) ≤
        Real.exp (characterLogCenter J T anchor F (true, some v) + c)) →
      ∀ center : ∀ p : ℕ, ZMod p,
      let lo := initialWordAtomLower J (fun v => ∏ i, cellLo ⟨(true, some v), i⟩)
      let hi := initialWordAtomUpper J (fun v => ∏ i, cellHi ⟨(true, some v), i⟩)
      let χ₀ := signedAtomCharacter (initialWordSize (m + 1) (characterCellSize r f)) χ
      let V := naturalTransferCutoff Δ m
      let cap := characterPivotCap T (characterRangeError (n + 1) c)
      Real.exp (-(B₁ - 1) * m) ≤
        ‖scheduledConstituentAmplitude (characterRole (n + 1)) (characterSize m r f) χ₀
          (fun i => primeGaussMultiplier (χ₀ i)) (characterPivot m r f hr) P hP
          (characterFullPrimeCells m r f Q R) lo hi V cap
          (scheduleFourierLeaf (characterRole (n + 1)) ψ (Real.exp logX)
            (Real.exp (Δ - (Fintype.card (CharacterRole (n + 1)) : ℝ) * c))
            (Real.exp (Δ + (Fintype.card (CharacterRole (n + 1)) : ℝ) * c))) center 0‖ → False
  have hF (r : Fin (n + 1) → ℕ) (f : ℕ) (hrN : ∀ j, r j ≤ N) (hf : f ≤ N) :
      ∀ᶠ L : ℝ in atTop, F r f L := by
    by_cases hr : ∀ j, 0 < r j
    · by_cases hnb : 1 + ((∑ j, r j) + 2 * (n + 1)) ≤ Bnb
      · by_cases hpivot : Cmass * (∑ j, (r j : ℝ)) ≤ z / 4
        · have hh := eventual_character_iteration_contradiction n N Bnb r f hr hrN hf hnb
            ψ hreal K B B₁ z c a b Cmass α βg βw γs βa γw νw νa ε hB hBstrong hB₁
            hz hc ha ha1 hb hCmass hα hβg hγw hαw hsw hαa hwa hwg hβw hβa hε
            hbudget hpivot hgap hψ hentropy
          filter_upwards [hh] with L hL
          intro hr' _ _
          exact hL
        · exact Filter.Eventually.of_forall (fun L _ _ hp => (hpivot hp).elim)
      · exact Filter.Eventually.of_forall (fun L _ hn => (hnb hn).elim)
    · exact Filter.Eventually.of_forall (fun L hr' => (hr hr').elim)
  have hall := eventually_all.mpr (fun rr : Fin (n + 1) → Fin (N + 1) =>
    eventually_all.mpr (fun ff : Fin (N + 1) =>
      hF (fun j => (rr j).val) ff.val (fun j => Nat.le_of_lt_succ (rr j).isLt)
        (Nat.le_of_lt_succ ff.isLt)))
  filter_upwards [hall] with L hL r f hrN hf
  exact hL (fun j => ⟨r j, Nat.lt_succ_of_le (hrN j)⟩) ⟨f, Nat.lt_succ_of_le hf⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterEndpointContradiction
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The selected endpoint family contradicts the character comparison -/
namespace Ostmann
open Filter
open scoped Classical BigOperators SchwartzMap FourierTransform ComplexConjugate

theorem eventual_character_endpoint_contradiction (n N Bnb nc : ℕ)
    (a b z Cmass Ctotal Aend Bword B B₁ c s γ H α K βg βw γs βa γw νw νa ε : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hz : 1 < z)
    (hCmass : 0 < Cmass) (hCtotal : 0 ≤ Ctotal) (hc : 1 ≤ c)
    (hs : 0 < s) (hγ : 0 < γ) (hH : 0 ≤ H) (hα : 0 < α)
    (hbudget : 4 * nc * Cmass ≤ z)
    (hgapInitial : 2 * ((2 * Real.log (3 / a) + 3 + 2 * Ctotal) +
      (Aend + 2 * Bword + 1) + 2) ≤ B) (hB : 0 ≤ B)
    (hB₁ : 0 ≤ B₁) (hB₁eq : B₁ = Aend + 2 * Bword + 3)
    (hBstrong : 2 * B₁ + 5 ≤ B) (hBpos : 1 ≤ B) (ha1 : a ≤ 1)
    (hβg : 0 < βg) (hγw : 0 ≤ γw) (hαw : α < βw) (hsw : γs < βw)
    (hαa : α < βa) (hwa : γw < βa) (hwg : γw ≤ βg)
    (hβw : βw < νw) (hβa : βa < νa) (hε : 0 < ε)
    (hbudgetAll : 4 * Cmass * Bnb ≤ z)
    (hgapFinal : 2 * B₁ +
      ((γw + Real.log ((Real.log 2)⁻¹ + 1)) / a + max (Real.log 3) 0 + ε) +
      Real.log 2 + 6 ≤ B + 20 * Real.log a)
    (hentropy : (βg + Real.log ((Real.log 2)⁻¹ + 1) + max (Real.log 3) 0 + ε) +
      (B + 20 * Real.log z + 1) + 2 * B₁ + 1 ≤ (n : ℝ) * Real.log 2 - 1)
    (ψ : 𝓢(ℝ, ℂ)) (hψ : ∀ x, 0 ≤ (ψ x).re) (hreal : ∀ x, (ψ x).im = 0)
    (heven : ∀ v : ℝ, 𝓕 ψ (-v) = 𝓕 ψ v)
    (hψK : SchwartzMap.seminorm ℝ 0 0 (𝓕 ψ : 𝓢(ℝ, ℂ)) ≤ Real.exp K)
    (hsupp : ∀ x : ℝ, H < |x| → 𝓕 ψ x = 0) :
    ∀ᶠ L : ℝ in atTop,
    let m := ⌊z * L⌋₊
    ∀ (r : Fin (n + 1) → ℕ) (f : ℕ) (hr : ∀ j, 0 < r j),
    (∀ j, r j ≤ N) → f ≤ N →
    1 + ((∑ j, r j) + 2 * (n + 1)) ≤ Bnb →
    Cmass * (∑ j, (r j : ℝ)) ≤ z / 4 →
    ∀ (_cell : (Σ v, Fin (characterCellSize r f v)) ≃ Fin nc)
      (logX τ bmax : ℝ) (P U T₀ : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
      (Q : Fin (m + 1) → Finset ℕ)
      (R : (v : CharacterCell (n + 1)) → Fin (characterCellSize r f v) → Finset ℕ),
    0 < logX → Q 0 = T₀ → (∀ i : Fin m, Q i.succ = U) →
    (∀ i, Q i ⊆ P) → (∀ v i, R v i ⊆ P) →
    a * L ≤ ∑ p ∈ U, (p : ℝ)⁻¹ → b ≤ ∑ p ∈ T₀, (p : ℝ)⁻¹ →
    (∀ v i, Real.exp (-Cmass * L) ≤ ∑ p ∈ R v i, (p : ℝ)⁻¹) →
    (∑ p : P, (p : ℝ)⁻¹) ≤ Ctotal * L →
    (∀ p ∈ P, Real.exp (Real.exp (α * L)) ≤ p ∧
      (p : ℝ) ≤ Real.exp (Real.exp (βg * L))) →
    (∀ p ∈ U, Real.exp (Real.exp (νw * L)) ≤ p ∧
      (p : ℝ) ≤ Real.exp (Real.exp (γw * L))) →
    Disjoint U T₀ → (∀ v i, Disjoint U (R v i)) →
    (∀ j p, p ∈ R (.inr (.inl (j, false))) ⟨0, by change 0 < 1; omega⟩ →
      (p : ℝ) ≤ Real.exp (Real.exp (γs * L))) →
    (∀ j p, p ∈ R (.inr (.inl (j, true))) ⟨0, by change 0 < 1; omega⟩ →
      Real.exp (Real.exp (νa * L)) ≤ p) →
    (m : ℝ) * bmax ≤ τ →
    (∀ p ∈ T₀, τ ≤ Real.log (p : ℝ) ∧ Real.log (p : ℝ) ≤ 3 * τ) →
    (∀ p ∈ U, Real.log (p : ℝ) ≤ bmax) →
    ∀ (cellLo cellHi : (Σ v, Fin (characterCellSize r f v)) → ℕ),
    (∀ v i p, p ∈ R v i → cellLo ⟨v, i⟩ ≤ p ∧ p ≤ cellHi ⟨v, i⟩) →
    ∀ (anchor : Fin (n + 1) → Bool → ℝ) (bin : Fin (⌊4 * τ⌋₊ + 1)), 0 < bin.val →
    let Δ := characterBaseGap B z m
    let T := characterPivotTarget (n + 1) bin.val (fun j => anchor j false + anchor j true)
      (fun j => characterPivotGap B z m j.val)
    let F := characterFillerTarget logX Δ bin.val T anchor
    (∀ j, T j + c ≤ Real.exp (βg * L)) →
    (∀ v, Real.exp (characterLogCenter bin.val T anchor F (true, some v) - c) ≤
      ∏ i, cellLo ⟨v, i⟩) →
    (∀ v, (∏ i, cellHi ⟨v, i⟩ : ℕ) ≤
      Real.exp (characterLogCenter bin.val T anchor F (true, some v) + c)) →
    ∀ (χ : ∀ p : ℕ, DirichletCharacter ℂ p), (∀ p ∈ P, χ p ^ 2 ≠ 1) →
    ∀ (center : ∀ p : ℕ, ZMod p) (E : Finset ℤ) (ρ : ℝ),
    Real.sqrt (Real.exp logX) * Real.exp (-Aend * m) ≤ E.card →
    Real.exp (-Bword * m) ≤ ρ →
    (∀ x ∈ E, s ≤ (ψ ((x : ℝ) / Real.exp logX)).re) →
    (∀ x ∈ E, ρ ≤ ‖binnedWordAverage (fun i => primeSubsetPrior P (Q i))
      (fun _ p => χ p ((x : ZMod p) - center p))
      (fun w => wordLogBin τ (fun i => Real.log (w i : ℝ))) bin‖) →
    (∀ x ∈ E, ∀ v i, γ ≤
      ‖∑ p : P, (primeSubsetPrior P (R v i) p : ℂ) * χ p ((x : ZMod p) - center p)‖) →
    False := by
  have hconj (x : ℝ) : conj (ψ x) = ψ x := by
    apply Complex.ext <;> simp [hreal x]
  have hstart := eventual_character_scheduled_initial_rate (n + 1) nc a b z Cmass Ctotal
    Aend Bword B c s γ H α ha hb hz hCmass.le hCtotal hc hs hγ hH hα hbudget
    hgapInitial hB ψ hψ hreal heven hsupp
  have hfinish := eventual_uniform_character_iteration_contradiction n N Bnb ψ hconj
    K B B₁ z c a b Cmass α βg βw γs βa γw νw νa ε hBpos hBstrong hB₁ hz hc
    ha ha1 hb hCmass hα hβg hγw hαw hsw hαa hwa hwg hβw hβa hε hbudgetAll
    hgapFinal hψK hentropy
  filter_upwards [hstart, hfinish] with L hstart hfinish
  intro m r f hr hrN hf hnb hpivot cell logX τ bmax P U T₀ hP Q R
    hlogX hzero hsucc hQP hRP hbulk htop hR htotal hPrange hUrange hUT hUR hsmall hbig
    hsize htoplog hbulklog cellLo cellHi hcell anchor bin hbinpos Δ T F hT hlo hhi
    χ hχ center E ρ hE hρ hsE hword hmean
  have hχ' (p : ℕ) (hp : p ∈ P) : χ p ≠ 1 := by
    intro he
    exact hχ p hp (by rw [he, one_pow])
  have hinit := hstart r f cell logX τ bmax P U T₀ hP Q R hzero hsucc hQP hRP hbulk htop
    hR htotal (fun p hp => (hPrange p hp).1) hsize htoplog hbulklog cellLo cellHi hcell
    anchor bin hlo hhi χ hχ' center E ρ hE hρ hsE hword hmean (characterPivot m r f hr)
  let L₀ := characterLiftCellBound m r f 0 cellLo
  let H₀ := characterLiftCellBound m r f (P.sup id) cellHi
  have hcell' := characterLiftCellBound_support m r f P Q R hQP cellLo cellHi hcell
  have hlo' (v : CharacterCell (n + 1)) :
      Real.exp (characterLogCenter bin.val T anchor F (true, some v) - c) ≤
        ∏ i, L₀ ⟨(true, some v), i⟩ := hlo v
  have hhi' (v : CharacterCell (n + 1)) :
      (∏ i, H₀ ⟨(true, some v), i⟩ : ℕ) ≤
        Real.exp (characterLogCenter bin.val T anchor F (true, some v) + c) := hhi v
  apply hfinish r f hrN hf hr hnb hpivot P U hP Q R hsucc
    (by simpa only [hzero] using hUT) hUR hQP hRP (by simpa only [hzero] using htop)
    hbulk hR hPrange hUrange hsmall hbig χ hχ bin.val hbinpos anchor F logX hlogX hT
    L₀ H₀ hcell' hlo' hhi' center
  have hcoef : B₁ - 1 = Aend + 2 * Bword + 2 := by linarith only [hB₁eq]
  rw [hcoef]
  exact hinit

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterUniformEndpoint
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniformity in the actual selected nonword-cell count -/
namespace Ostmann
open Filter
open scoped Classical BigOperators SchwartzMap FourierTransform ComplexConjugate

theorem eventual_uniform_character_endpoint_contradiction_oai (n N Bnb : ℕ)
    (a b z Cmass Ctotal Aend Bword B B₁ c s γ H α K βg βw γs βa γw νw νa ε : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hz : 1 < z)
    (hCmass : 0 < Cmass) (hCtotal : 0 ≤ Ctotal) (hc : 1 ≤ c)
    (hs : 0 < s) (hγ : 0 < γ) (hH : 0 ≤ H) (hα : 0 < α)
    (hgapInitial : 2 * ((2 * Real.log (3 / a) + 3 + 2 * Ctotal) +
      (Aend + 2 * Bword + 1) + 2) ≤ B) (hB : 0 ≤ B)
    (hB₁ : 0 ≤ B₁) (hB₁eq : B₁ = Aend + 2 * Bword + 3)
    (hBstrong : 2 * B₁ + 5 ≤ B) (hBpos : 1 ≤ B) (ha1 : a ≤ 1)
    (hβg : 0 < βg) (hγw : 0 ≤ γw) (hαw : α < βw) (hsw : γs < βw)
    (hαa : α < βa) (hwa : γw < βa) (hwg : γw ≤ βg)
    (hβw : βw < νw) (hβa : βa < νa) (hε : 0 < ε)
    (hbudgetAll : 4 * Cmass * Bnb ≤ z)
    (hgapFinal : 2 * B₁ +
      ((γw + Real.log ((Real.log 2)⁻¹ + 1)) / a + max (Real.log 3) 0 + ε) +
      Real.log 2 + 6 ≤ B + 20 * Real.log a)
    (hentropy : (βg + Real.log ((Real.log 2)⁻¹ + 1) + max (Real.log 3) 0 + ε) +
      (B + 20 * Real.log z + 1) + 2 * B₁ + 1 ≤ (n : ℝ) * Real.log 2 - 1)
    (ψ : 𝓢(ℝ, ℂ)) (hψ : ∀ x, 0 ≤ (ψ x).re) (hreal : ∀ x, (ψ x).im = 0)
    (heven : ∀ v : ℝ, 𝓕 ψ (-v) = 𝓕 ψ v)
    (hψK : SchwartzMap.seminorm ℝ 0 0 (𝓕 ψ : 𝓢(ℝ, ℂ)) ≤ Real.exp K)
    (hsupp : ∀ x : ℝ, H < |x| → 𝓕 ψ x = 0) :
    ∀ᶠ L : ℝ in atTop, ∀ nc : ℕ, nc ≤ Bnb →
    let m := ⌊z * L⌋₊
    ∀ (r : Fin (n + 1) → ℕ) (f : ℕ) (hr : ∀ j, 0 < r j),
    (∀ j, r j ≤ N) → f ≤ N →
    1 + ((∑ j, r j) + 2 * (n + 1)) ≤ Bnb →
    Cmass * (∑ j, (r j : ℝ)) ≤ z / 4 →
    ∀ (_cell : (Σ v, Fin (characterCellSize r f v)) ≃ Fin nc)
      (logX τ bmax : ℝ) (P U T₀ : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
      (Q : Fin (m + 1) → Finset ℕ)
      (R : (v : CharacterCell (n + 1)) → Fin (characterCellSize r f v) → Finset ℕ),
    0 < logX → Q 0 = T₀ → (∀ i : Fin m, Q i.succ = U) →
    (∀ i, Q i ⊆ P) → (∀ v i, R v i ⊆ P) →
    a * L ≤ ∑ p ∈ U, (p : ℝ)⁻¹ → b ≤ ∑ p ∈ T₀, (p : ℝ)⁻¹ →
    (∀ v i, Real.exp (-Cmass * L) ≤ ∑ p ∈ R v i, (p : ℝ)⁻¹) →
    (∑ p : P, (p : ℝ)⁻¹) ≤ Ctotal * L →
    (∀ p ∈ P, Real.exp (Real.exp (α * L)) ≤ p ∧
      (p : ℝ) ≤ Real.exp (Real.exp (βg * L))) →
    (∀ p ∈ U, Real.exp (Real.exp (νw * L)) ≤ p ∧
      (p : ℝ) ≤ Real.exp (Real.exp (γw * L))) →
    Disjoint U T₀ → (∀ v i, Disjoint U (R v i)) →
    (∀ j p, p ∈ R (.inr (.inl (j, false))) ⟨0, by change 0 < 1; omega⟩ →
      (p : ℝ) ≤ Real.exp (Real.exp (γs * L))) →
    (∀ j p, p ∈ R (.inr (.inl (j, true))) ⟨0, by change 0 < 1; omega⟩ →
      Real.exp (Real.exp (νa * L)) ≤ p) →
    (m : ℝ) * bmax ≤ τ →
    (∀ p ∈ T₀, τ ≤ Real.log (p : ℝ) ∧ Real.log (p : ℝ) ≤ 3 * τ) →
    (∀ p ∈ U, Real.log (p : ℝ) ≤ bmax) →
    ∀ (cellLo cellHi : (Σ v, Fin (characterCellSize r f v)) → ℕ),
    (∀ v i p, p ∈ R v i → cellLo ⟨v, i⟩ ≤ p ∧ p ≤ cellHi ⟨v, i⟩) →
    ∀ (anchor : Fin (n + 1) → Bool → ℝ) (bin : Fin (⌊4 * τ⌋₊ + 1)), 0 < bin.val →
    let Δ := characterBaseGap B z m
    let T := characterPivotTarget (n + 1) bin.val (fun j => anchor j false + anchor j true)
      (fun j => characterPivotGap B z m j.val)
    let F := characterFillerTarget logX Δ bin.val T anchor
    (∀ j, T j + c ≤ Real.exp (βg * L)) →
    (∀ v, Real.exp (characterLogCenter bin.val T anchor F (true, some v) - c) ≤
      ∏ i, cellLo ⟨v, i⟩) →
    (∀ v, (∏ i, cellHi ⟨v, i⟩ : ℕ) ≤
      Real.exp (characterLogCenter bin.val T anchor F (true, some v) + c)) →
    ∀ (χ : ∀ p : ℕ, DirichletCharacter ℂ p), (∀ p ∈ P, χ p ^ 2 ≠ 1) →
    ∀ (center : ∀ p : ℕ, ZMod p) (E : Finset ℤ) (ρ : ℝ),
    Real.sqrt (Real.exp logX) * Real.exp (-Aend * m) ≤ E.card →
    Real.exp (-Bword * m) ≤ ρ →
    (∀ x ∈ E, s ≤ (ψ ((x : ℝ) / Real.exp logX)).re) →
    (∀ x ∈ E, ρ ≤ ‖binnedWordAverage (fun i => primeSubsetPrior P (Q i))
      (fun _ p => χ p ((x : ZMod p) - center p))
      (fun w => wordLogBin τ (fun i => Real.log (w i : ℝ))) bin‖) →
    (∀ x ∈ E, ∀ v i, γ ≤
      ‖∑ p : P, (primeSubsetPrior P (R v i) p : ℂ) * χ p ((x : ZMod p) - center p)‖) →
    False := by
  have hbudget (i : Fin (Bnb + 1)) : 4 * (i.val : ℝ) * Cmass ≤ z := by
    have hi : (i.val : ℝ) ≤ Bnb := by exact_mod_cast Nat.le_of_lt_succ i.isLt
    have hh := mul_le_mul_of_nonneg_left hi (show 0 ≤ 4 * Cmass by positivity)
    nlinarith only [hh, hbudgetAll]
  have hall := eventually_all.mpr (fun i : Fin (Bnb + 1) =>
    eventual_character_endpoint_contradiction n N Bnb i.val
      a b z Cmass Ctotal Aend Bword B B₁ c s γ H α K βg βw γs βa γw νw νa ε
      ha hb hz hCmass hCtotal hc hs hγ hH hα (hbudget i) hgapInitial hB hB₁ hB₁eq
      hBstrong hBpos ha1 hβg hγw hαw hsw hαa hwa hwg hβw hβa hε hbudgetAll
      hgapFinal hentropy ψ hψ hreal heven hψK hsupp)
  filter_upwards [hall] with L hL nc hnc
  exact hL ⟨nc, Nat.lt_succ_of_le hnc⟩

end Ostmann

end OAI
end

theorem solution : type_of% @OAI.Ostmann.eventual_uniform_character_endpoint_contradiction_oai := @OAI.Ostmann.eventual_uniform_character_endpoint_contradiction_oai
