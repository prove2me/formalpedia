-- Prove2me | solution 1 for OAI.Ostmann.eventual_selected_initial_amplitude
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T07:12:21.242263+00:00
-- url     : https://prove2.me/submissions/e20b7e3a-7480-4c79-9d27-e50e08d43f68

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
-- module Solutions.OAIQ095_OS.Ostmann_Construction_OneSidedDecayBudget
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The separated long/short scales absorb the one-sided losses -/

namespace Ostmann

open Filter

theorem eventual_polynomial_log_budget (C z α ε : ℝ) (d : ℕ)
    (hC : 0 ≤ C) (hz : 0 ≤ z) (hα : 0 < α) (hε : 0 < ε) :
    ∀ᶠ L : ℝ in atTop, ∀ m : ℝ, 0 ≤ m → m ≤ z * L →
      C * (1 + m) ^ d ≤ ε * Real.exp (α * L) := by
  have hb := ((isLittleO_pow_exp_pos_mul_atTop d hα).const_mul_left
    (C * (z + 1) ^ d)).bound hε
  filter_upwards [hb, eventually_ge_atTop (1 : ℝ)] with L hlarge hL m hm hmL
  have hx : 1 + m ≤ (z + 1) * L := by nlinarith
  have hp : (1 + m) ^ d ≤ ((z + 1) * L) ^ d := pow_le_pow_left₀ (by linarith) hx d
  have hlarge' : C * (z + 1) ^ d * L ^ d ≤ ε * Real.exp (α * L) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ C * (z + 1) ^ d * L ^ d),
      abs_of_pos (Real.exp_pos _)] using hlarge
  calc
    _ ≤ C * (((z + 1) * L) ^ d) := mul_le_mul_of_nonneg_left hp hC
    _ = C * (z + 1) ^ d * L ^ d := by rw [mul_pow]; ring
    _ ≤ _ := hlarge'

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

theorem productPrior_cons {A : Type*} {n : ℕ}
    (μ : Fin (n + 1) → A → ℝ) (a : A) (x : Fin n → A) :
    productPrior μ (Fin.cons a x) = μ 0 a * productPrior (fun i => μ i.succ) x := by
  simp only [productPrior, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]

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
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SpectatorBulkScale
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The even bulk size and the accumulated giant loss in Section 9 -/

namespace Ostmann
open Filter
open scoped BigOperators

theorem spectatorBulkCount_even (k : ℕ) (L : ℝ) : Even (spectatorBulkCount k L) := by
  exact ⟨⌊(k : ℝ) ^ 4 * L / 2⌋₊, by unfold spectatorBulkCount; omega⟩

theorem spectatorBulkCount_lower (k : ℕ) (L : ℝ) :
    (k : ℝ) ^ 4 * L - 2 < (spectatorBulkCount k L : ℝ) := by
  have h := Nat.sub_one_lt_floor ((k : ℝ) ^ 4 * L / 2)
  unfold spectatorBulkCount
  push_cast
  linarith

theorem spectatorBulkCount_upper (k : ℕ) (L : ℝ) (hL : 0 ≤ L) :
    (spectatorBulkCount k L : ℝ) ≤ (k : ℝ) ^ 4 * L := by
  have h := Nat.floor_le (show 0 ≤ (k : ℝ) ^ 4 * L / 2 by positivity)
  unfold spectatorBulkCount
  push_cast
  linarith

theorem spectatorBulkCount_half (k : ℕ) (L : ℝ)
    (hL : 4 ≤ (k : ℝ) ^ 4 * L) :
    (k : ℝ) ^ 4 * L / 2 ≤ (spectatorBulkCount k L : ℝ) := by
  linarith [spectatorBulkCount_lower k L]

theorem spectatorBulkCount_tendsto (k : ℕ) (hk : 0 < k) :
    Tendsto (fun L : ℝ => (spectatorBulkCount k L : ℝ)) atTop atTop := by
  have hk0 : 0 < (k : ℝ) ^ 4 := by positivity
  apply tendsto_atTop.2
  intro b
  filter_upwards [eventually_ge_atTop ((b + 2) / (k : ℝ) ^ 4)] with L hL
  have h := (div_le_iff₀ hk0).mp hL
  linarith [spectatorBulkCount_lower k L]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingCompensationTargets
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The backwards compensation-center construction of equation (7.4) -/

namespace Ostmann

theorem movingCompensationTargets_sum (J : ℝ) (ds : List ℝ) :
    J + (movingCompensationTargets J ds).sum =
      (2 : ℝ) ^ ds.length * J - movingCompensationTargetError ds := by
  induction ds with
  | nil => simp only [movingCompensationTargets, List.sum_nil, List.length_nil,
      pow_zero, one_mul, movingCompensationTargetError, sub_zero, add_zero]
  | cons d ds ih =>
    simp only [movingCompensationTargets, List.sum_cons, List.length_cons,
      movingCompensationTargetError, pow_succ]
    linarith

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

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_PositiveWordStatistic
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
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

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_BoundedWordStatistic
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The initial positive statistic with its actual finite physical bounds -/

namespace Ostmann
open scoped BigOperators SchwartzMap

/-- The inverse giant transform need not have norm at most one. Only a finite
bound is needed to sum its Schwartz-weighted physical statistic. -/
theorem wordStatisticTerm_summable_of_bounded {m : ℕ}
    (ψ : 𝓢(ℝ, ℂ)) (X : ℝ) (hX : 0 < X)
    (G : ℤ → ℂ) (R : Fin m → ℤ → ℂ) (CG : ℝ) (CR : Fin m → ℝ)
    (hψ : ∀ x, 0 ≤ (ψ x).re)
    (hG : ∀ a, ‖G a‖ ≤ CG) (hR : ∀ i a, ‖R i a‖ ≤ CR i) :
    Summable (wordStatisticTerm ψ X G R) := by
  have hsum : Summable (fun a : ℤ => ‖ψ ((a : ℝ) / X)‖) := by
    simpa only [positiveDilate_apply, div_eq_mul_inv, mul_comm] using
      schwartz_int_norm_summable (positiveDilate ψ X⁻¹ (inv_pos.mpr hX))
  apply Summable.of_norm_bounded (hsum.mul_right (CG ^ 2 * ∏ i, CR i ^ 2))
  intro a
  rw [Real.norm_eq_abs, abs_of_nonneg (wordStatisticTerm_nonneg ψ X G R hψ a)]
  have hg : ‖G a‖ ^ 2 ≤ CG ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (hG a) 2
  have hr : (∏ i, ‖R i a‖ ^ 2) ≤ ∏ i, CR i ^ 2 :=
    Finset.prod_le_prod (fun _ _ => sq_nonneg _) (fun i _ =>
      pow_le_pow_left₀ (norm_nonneg _) (hR i a) 2)
  calc
    wordStatisticTerm ψ X G R a ≤
        ‖ψ ((a : ℝ) / X)‖ * (CG ^ 2 * ∏ i, CR i ^ 2) := by
      unfold wordStatisticTerm
      rw [← mul_assoc]
      exact mul_le_mul (mul_le_mul (Complex.re_le_norm _) hg
        (sq_nonneg _) (norm_nonneg _)) hr (by positivity) (by positivity)
    _ = _ := rfl

/-- Cauchy--Schwarz converts a positive empirical mean into the squared norm
needed for the original statistic, without pointwise positivity of the giant. -/
theorem endpoint_mean_sq_le {ι : Type*} (E : Finset ι) (G : ι → ℂ)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hmean : (E.card : ℝ) * δ ≤ ∑ a ∈ E, (G a).re) :
    (E.card : ℝ) * δ ^ 2 ≤ ∑ a ∈ E, ‖G a‖ ^ 2 := by
  by_cases hE : E.card = 0
  · have he : E = ∅ := Finset.card_eq_zero.mp hE
    simp only [he, Finset.card_empty, Nat.cast_zero, zero_mul, Finset.sum_empty, le_refl]
  have hc : (0 : ℝ) < E.card := by exact_mod_cast Nat.pos_of_ne_zero hE
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq E (fun _ => (1 : ℝ)) (fun a => (G a).re)
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hcs
  have hre : (∑ a ∈ E, (G a).re ^ 2) ≤ ∑ a ∈ E, ‖G a‖ ^ 2 := by
    apply Finset.sum_le_sum
    intro a _
    simpa only [Complex.normSq_eq_norm_sq, pow_two] using Complex.re_sq_le_normSq (G a)
  have hlow : ((E.card : ℝ) * δ) ^ 2 ≤ (∑ a ∈ E, (G a).re) ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg hc.le hδ) hmean 2
  have hupper := hcs.trans (mul_le_mul_of_nonneg_left hre hc.le)
  nlinarith

/-- The selected endpoint mean feeds the whole statistic. No pointwise bound
of one and no pointwise lower bound on the giant function is imposed. -/
theorem wordStatistic_lower_of_endpoint_mean {m : ℕ}
    (ψ : 𝓢(ℝ, ℂ)) (X : ℝ) (hX : 0 < X)
    (G : ℤ → ℂ) (R : Fin m → ℤ → ℂ) (E : Finset ℤ)
    (CG : ℝ) (CR : Fin m → ℝ)
    (hψ : ∀ x, 0 ≤ (ψ x).re)
    (hG : ∀ a, ‖G a‖ ≤ CG) (hR : ∀ i a, ‖R i a‖ ≤ CR i)
    (c δ γ : ℝ) (hc : 0 ≤ c) (hδ : 0 ≤ δ) (hγ : 0 ≤ γ)
    (hcE : ∀ a ∈ E, c ≤ (ψ ((a : ℝ) / X)).re)
    (hmean : (E.card : ℝ) * δ ≤ ∑ a ∈ E, (G a).re)
    (hγE : ∀ a ∈ E, ∀ i, γ ≤ ‖R i a‖) :
    (E.card : ℝ) * (c * δ ^ 2 * γ ^ (2 * m)) ≤
      ∑' a : ℤ, wordStatisticTerm ψ X G R a := by
  have hm := endpoint_mean_sq_le E G δ hδ hmean
  have hfinite : c * γ ^ (2 * m) * (∑ a ∈ E, ‖G a‖ ^ 2) ≤
      ∑ a ∈ E, wordStatisticTerm ψ X G R a := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro a ha
    have hr : γ ^ (2 * m) ≤ ∏ i, ‖R i a‖ ^ 2 := by
      rw [pow_mul]
      calc
        (γ ^ 2) ^ m = ∏ _i : Fin m, γ ^ 2 := by simp
        _ ≤ _ := Finset.prod_le_prod (fun _ _ => sq_nonneg _)
          (fun i _ => pow_le_pow_left₀ hγ (hγE a ha i) 2)
    unfold wordStatisticTerm
    calc
      c * γ ^ (2 * m) * ‖G a‖ ^ 2 = c * ‖G a‖ ^ 2 * γ ^ (2 * m) := by ring
      _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_right (hcE a ha) (sq_nonneg _)) hr
        (by positivity) (mul_nonneg (hψ _) (sq_nonneg _))
  calc
    _ = c * γ ^ (2 * m) * ((E.card : ℝ) * δ ^ 2) := by ring
    _ ≤ c * γ ^ (2 * m) * (∑ a ∈ E, ‖G a‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hm (by positivity)
    _ ≤ ∑ a ∈ E, wordStatisticTerm ψ X G R a := hfinite
    _ ≤ _ := (wordStatisticTerm_summable_of_bounded ψ X hX G R CG CR hψ hG hR).sum_le_tsum E
      (fun a _ => wordStatisticTerm_nonneg ψ X G R hψ a)

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
-- module Solutions.OAIQ095_OS.Ostmann_Characters_RegularTuplePoisson
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Initial Poisson summation for the actual normalized residue transforms -/

namespace Ostmann
open scoped Classical BigOperators FourierTransform SchwartzMap

/-- Exact normalization and cofactor arguments for arbitrary local tests.
This applies to the phase giant and to every normalized residue indicator. -/
theorem tuple_regular_fourier {I : Type*} [Fintype I]
    (p : I → ℕ) [∀ i, NeZero (p i)] [NeZero (∏ i, p i)]
    (hc : Pairwise (fun i j => (p i).Coprime (p j)))
    (F : ∀ i, ZMod (p i) → ℂ) (v : ℤ) :
    additiveFourier (tupleCRTFunction p hc F) (v : ZMod (∏ i, p i)) =
      (Real.sqrt (∏ i, p i : ℕ) : ℂ)⁻¹ *
        movingRegularTransform p (fun i => densityFourier (F i)) 1 v := by
  rw [tupleCRTFunction_fourier]
  simp only [map_intCast, Pi.intCast_apply]
  have hlocal (i : I) : additiveFourier (F i)
      ((tupleCofactor p i : ZMod (p i))⁻¹ * (v : ZMod (p i))) =
      (Real.sqrt (p i : ℝ) : ℂ)⁻¹ * densityFourier (F i)
        ((v : ZMod (p i)) * (tupleCofactor p i : ZMod (p i))⁻¹) := by
    have hs : (Real.sqrt (p i : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.mpr
        (show (0 : ℝ) < p i by exact_mod_cast NeZero.pos (p i))).ne'
    unfold densityFourier
    rw [← mul_assoc, inv_mul_cancel₀ hs, one_mul, mul_comm]
  simp_rw [hlocal]
  rw [Finset.prod_mul_distrib]
  have hs : (Real.sqrt (∏ i, p i : ℕ) : ℂ) = ∏ i, (Real.sqrt (p i : ℝ) : ℂ) := by
    rw [Nat.cast_prod, Real.sqrt_prod _ (fun i _ => Nat.cast_nonneg (p i)), Complex.ofReal_prod]
  rw [hs, Finset.prod_inv_distrib]
  unfold movingRegularTransform
  simp only [Nat.one_mul]

/-- The physical tuple divided by sqrt X is the actual initial regular
Fourier amplitude. The sign of the frequency is retained explicitly. -/
theorem tuple_regular_poisson_normalized {I : Type*} [Fintype I]
    (p : I → ℕ) [∀ i, NeZero (p i)] [NeZero (∏ i, p i)]
    (hc : Pairwise (fun i j => (p i).Coprime (p j)))
    (F : ∀ i, ZMod (p i) → ℂ) (ψ : 𝓢(ℝ, ℂ)) (X : ℝ) (hX : 0 < X) :
    (∑' a : ℤ, (∏ i, F i (a : ZMod (p i))) * ψ ((a : ℝ) / X)) /
        (Real.sqrt X : ℂ) =
      ∑' v : ℤ, (Real.sqrt (X / (∏ i, p i : ℕ)) : ℂ) *
        𝓕 ψ ((v : ℝ) * X / (∏ i, p i : ℕ)) *
          movingRegularTransform p (fun i => densityFourier (F i)) 1 (-v) := by
  have hp := scaled_periodic_poisson (tupleCRTFunction p hc F) ψ X hX
  simp_rw [tupleCRTFunction_intCast, show ∀ v : ℤ,
    -(v : ZMod (∏ i, p i)) = ((-v : ℤ) : ZMod (∏ i, p i)) from fun v => (Int.cast_neg v).symm,
    tuple_regular_fourier p hc F] at hp
  rw [hp, div_eq_mul_inv, ← tsum_mul_left, ← tsum_mul_right]
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

/-- Compact Fourier support produces a finite integer-frequency amplitude;
there is no estimate or discarded tail in this step. -/
theorem tuple_regular_poisson_finite {I : Type*} [Fintype I]
    (p : I → ℕ) [∀ i, NeZero (p i)] [NeZero (∏ i, p i)]
    (hc : Pairwise (fun i j => (p i).Coprime (p j)))
    (F : ∀ i, ZMod (p i) → ℂ) (ψ : 𝓢(ℝ, ℂ)) (X H : ℝ) (hX : 0 < X) (N : ℕ)
    (hcut : H * (∏ i, p i : ℕ) ≤ N * X)
    (hsupp : ∀ x : ℝ, H < |x| → 𝓕 ψ x = 0) :
    (∑' a : ℤ, (∏ i, F i (a : ZMod (p i))) * ψ ((a : ℝ) / X)) /
        (Real.sqrt X : ℂ) =
      ∑ v ∈ Finset.Icc (-(N : ℤ)) N, (Real.sqrt (X / (∏ i, p i : ℕ)) : ℂ) *
        𝓕 ψ ((v : ℝ) * X / (∏ i, p i : ℕ)) *
          movingRegularTransform p (fun i => densityFourier (F i)) 1 (-v) := by
  rw [tuple_regular_poisson_normalized p hc F ψ X hX]
  apply tsum_eq_sum
  intro v hv
  have hn : (N : ℝ) < |(v : ℝ)| := by
    have hi : (N : ℤ) < |v| := by
      simp only [Finset.mem_Icc, not_and_or, not_le] at hv
      rcases hv with hv | hv
      · exact (show (N : ℤ) < -v by omega).trans_le (neg_le_abs v)
      · exact hv.trans_le (le_abs_self v)
    exact_mod_cast hi
  have hM : (0 : ℝ) < (∏ i, p i : ℕ) := by exact_mod_cast NeZero.pos (∏ i, p i)
  have hf : 𝓕 ψ ((v : ℝ) * X / (∏ i, p i : ℕ)) = 0 := by
    apply hsupp
    rw [abs_div, abs_mul, abs_of_pos hX, abs_of_pos hM, lt_div_iff₀ hM]
    exact hcut.trans_lt (mul_lt_mul_of_pos_right hn hX)
  rw [hf, mul_zero, zero_mul]

/-- Reversing the finite frequency interval gives exactly the profile used
by the sampled recursion. No symmetry assumption on the Schwartz window is
needed: the minus sign belongs to the normalized Fourier profile. -/
theorem tuple_regular_poisson_profile {I : Type*} [Fintype I]
    (p : I → ℕ) [∀ i, NeZero (p i)] [NeZero (∏ i, p i)]
    (hc : Pairwise (fun i j => (p i).Coprime (p j)))
    (F : ∀ i, ZMod (p i) → ℂ) (ψ : 𝓢(ℝ, ℂ)) (X H : ℝ) (hX : 0 < X) (N : ℕ)
    (hcut : H * (∏ i, p i : ℕ) ≤ N * X)
    (hsupp : ∀ x : ℝ, H < |x| → 𝓕 ψ x = 0) :
    (∑' a : ℤ, (∏ i, F i (a : ZMod (p i))) * ψ ((a : ℝ) / X)) /
        (Real.sqrt X : ℂ) =
      ∑ v ∈ Finset.Icc (-(N : ℤ)) N,
        normalizedFourierProfile (fun t => 𝓕 ψ t) v ((∏ i, p i : ℕ) / X) *
          movingRegularTransform p (fun i => densityFourier (F i)) 1 v := by
  rw [tuple_regular_poisson_finite p hc F ψ X H hX N hcut hsupp]
  symm
  have hM : ((∏ i, p i : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (NeZero.ne (∏ i, p i))
  simp_rw [normalizedFourierProfile_original _ X ((∏ i, p i : ℕ) : ℝ) _ hX.ne' hM]
  unfold archimedeanLeafFactor
  simp only [mul_one]
  refine Finset.sum_bij (fun v _ => -v) ?_ ?_ ?_ ?_
  · intro v hv
    simp only [Finset.mem_Icc] at hv ⊢
    omega
  · intro v hv w hw he
    exact neg_injective he
  · intro v hv
    refine ⟨-v, ?_, neg_neg v⟩
    simp only [Finset.mem_Icc] at hv ⊢
    omega
  · intro v hv
    simp only [Int.cast_neg, neg_neg]

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

theorem complexUnitPhase_norm_le (z : ℂ) : ‖complexUnitPhase z‖ ≤ 1 := by
  by_cases hz : z = 0
  · simp [hz]
  · simp only [complexUnitPhase, norm_div, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]
    rw [div_self (norm_ne_zero_iff.mpr hz)]

theorem complexUnitPhase_conj (z : ℂ) :
    complexUnitPhase (conj z) = conj (complexUnitPhase z) := by
  simp only [complexUnitPhase, Complex.norm_conj, map_div₀, Complex.conj_ofReal]

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

theorem phaseGiantPhysical_real {p : ℕ} [NeZero p]
    (g : ZMod p → ℂ) (hg : ∀ b, g (-b) = conj (g b)) (x : ZMod p) :
    (phaseGiantPhysical g x).im = 0 := by
  apply densityFourierInverse_real
  intro b
  rw [hg, complexUnitPhase_conj]

theorem densityFourierInverse_energy {p : ℕ} [NeZero p] (g : ZMod p → ℂ) :
    (∑ x, ‖densityFourierInverse g x‖ ^ 2) = ∑ b, ‖g b‖ ^ 2 := by
  rw [← densityFourier_energy g]
  exact (Equiv.neg (ZMod p)).bijective.sum_comp (fun x => ‖densityFourier g x‖ ^ 2)

theorem phaseGiantPhysical_energy {p : ℕ} [NeZero p] (g : ZMod p → ℂ) :
    (∑ x, ‖phaseGiantPhysical g x‖ ^ 2) ≤ p := by
  rw [phaseGiantPhysical, densityFourierInverse_energy]
  calc
    _ ≤ ∑ _b : ZMod p, (1 : ℝ) := Finset.sum_le_sum fun b _ =>
      by simpa only [one_pow] using
        pow_le_pow_left₀ (norm_nonneg _) (complexUnitPhase_norm_le (g b)) 2
    _ = _ := by simp

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_PhaseGiantMean
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The positive uniform-support mean of the Fourier-phase giant -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

theorem densityFourierInverse_sum {p : ℕ} [NeZero p] (g : ZMod p → ℂ) :
    (∑ x, densityFourierInverse g x) = (Real.sqrt (p : ℝ) : ℂ) * g 0 := by
  have hi := additiveFourier_inversion g 0
  simp only [mul_zero, AddChar.map_zero_eq_one, mul_one] at hi
  unfold densityFourierInverse densityFourier
  have hn : (∑ x, additiveFourier g (-x)) = ∑ x, additiveFourier g x := by
    simpa only [Equiv.neg_apply] using
      (Equiv.neg (ZMod p)).bijective.sum_comp (additiveFourier g)
  rw [← Finset.mul_sum, hn, ← hi]

theorem phaseGiantPhysical_sum_zero {p : ℕ} [NeZero p]
    (g : ZMod p → ℂ) (hg : g 0 = 0) : (∑ x, phaseGiantPhysical g x) = 0 := by
  rw [phaseGiantPhysical, densityFourierInverse_sum, hg, complexUnitPhase_zero, mul_zero]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_RepeatedCharacterCancellation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
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
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
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

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_RepeatedPhysicalTests
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Repeated local tests with normalized probability energy -/

namespace Ostmann
open scoped Classical BigOperators FourierTransform SchwartzMap

/-- The physical giant need not be bounded by one; its normalized energy
still gives the exact square-root bound needed for repeated factors. -/
theorem localTest_bound_of_energy {q : ℕ} [NeZero q] (F : ZMod q → ℂ)
    (hF : ∑ x, ‖F x‖ ^ 2 ≤ (q : ℝ)) (x : ZMod q) :
    ‖F x‖ ≤ Real.sqrt q := by
  apply Real.le_sqrt_of_sq_le
  exact (Finset.single_le_sum (fun y _ => sq_nonneg ‖F y‖) (Finset.mem_univ x)).trans hF

/-- Two repeated factors use Cauchy; all remaining factors use the
square-root bound. The local tests may belong to different roles. -/
theorem sum_norm_product_le_sqrt_pow {I : Type*} {q : ℕ} [NeZero q]
    (S : Finset I) (F : I → ZMod q → ℂ) (hS : 2 ≤ S.card)
    (hF : ∀ i ∈ S, ∑ x, ‖F i x‖ ^ 2 ≤ (q : ℝ)) :
    (∑ x : ZMod q, ‖∏ i ∈ S, F i x‖) ≤ (Real.sqrt q) ^ S.card := by
  obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp (by omega : 1 < S.card)
  let R := (S.erase i).erase j
  have hj' : j ∈ S.erase i := Finset.mem_erase.mpr ⟨hij.symm, hj⟩
  have hR : R.card + 2 = S.card := by
    dsimp only [R]
    rw [Finset.card_erase_of_mem hj', Finset.card_erase_of_mem hi]
    omega
  have hrest (x : ZMod q) : (∏ l ∈ R, ‖F l x‖) ≤ Real.sqrt q ^ R.card := by
    simpa only [Finset.prod_const] using Finset.prod_le_prod
      (fun l _ => norm_nonneg (F l x)) (fun l hl =>
        localTest_bound_of_energy (F l) (hF l
          (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hl))) x)
  have htwo : (∑ x : ZMod q, ‖F i x‖ * ‖F j x‖) ≤ (q : ℝ) := by
    apply (Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
      (fun x => ‖F i x‖) (fun x => ‖F j x‖)).trans
    calc
      _ ≤ Real.sqrt q * Real.sqrt q := mul_le_mul
        (Real.sqrt_le_sqrt (hF i hi)) (Real.sqrt_le_sqrt (hF j hj))
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = _ := Real.mul_self_sqrt (Nat.cast_nonneg q)
  calc
    _ = ∑ x : ZMod q, (‖F i x‖ * ‖F j x‖) * ∏ l ∈ R, ‖F l x‖ := by
      apply Finset.sum_congr rfl
      intro x _
      rw [norm_prod, ← Finset.mul_prod_erase S (fun l => ‖F l x‖) hi,
        ← Finset.mul_prod_erase (S.erase i) (fun l => ‖F l x‖) hj']
      ring
    _ ≤ ∑ x : ZMod q, (‖F i x‖ * ‖F j x‖) * Real.sqrt q ^ R.card := by
      exact Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (hrest x) (by positivity))
    _ = (∑ x : ZMod q, ‖F i x‖ * ‖F j x‖) * Real.sqrt q ^ R.card :=
      (Finset.sum_mul ..).symm
    _ ≤ (q : ℝ) * Real.sqrt q ^ R.card :=
      mul_le_mul_of_nonneg_right htwo (by positivity)
    _ = Real.sqrt q ^ 2 * Real.sqrt q ^ R.card := by rw [Real.sq_sqrt (Nat.cast_nonneg q)]
    _ = _ := by rw [← pow_add, Nat.add_comm 2, hR]

theorem product_complete_mean_norm_le {I : Type*} {q : ℕ} [NeZero q]
    (S : Finset I) (F : I → ZMod q → ℂ) (hS : 2 ≤ S.card)
    (hF : ∀ i ∈ S, ∑ x, ‖F i x‖ ^ 2 ≤ (q : ℝ)) :
    ‖additiveFourier (fun x => ∏ i ∈ S, F i x) 0‖ ≤
      (q : ℝ)⁻¹ * Real.sqrt q ^ S.card := by
  rw [additiveFourier_apply]
  simp only [mul_zero, neg_zero, AddChar.map_zero_eq_one, mul_one,
    norm_mul, norm_inv, Complex.norm_natCast]
  exact mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans
    (sum_norm_product_le_sqrt_pow S F hS hF)) (by positivity)

theorem groupedPhysicalTest_product {I : Type*} [Fintype I]
    (P : Finset ℕ) (p : I → P) (F : I → (q : P) → ZMod (q : ℕ) → ℂ) (a : ℤ) :
    (∏ q : P, groupedPhysicalTest P p F q (a : ZMod (q : ℕ))) =
      ∏ i, F i (p i) (a : ZMod (p i : ℕ)) := by
  unfold groupedPhysicalTest
  have he (q : P) :
      (∏ i ∈ Finset.univ.filter (fun i => p i = q), F i q (a : ZMod (q : ℕ))) =
      ∏ i ∈ Finset.univ.filter (fun i => p i = q), F i (p i) (a : ZMod (p i : ℕ)) := by
    apply Finset.prod_congr rfl
    intro i hi
    rw [(Finset.mem_filter.mp hi).2]
  simp_rw [he]
  exact Finset.prod_fiberwise Finset.univ p _

theorem groupedPhysicalTest_singleton {I : Type*} [Fintype I]
    (P : Finset ℕ) (p : I → P) (F : I → (q : P) → ZMod (q : ℕ) → ℂ)
    (i : I) (hi : ∀ j, p j = p i → j = i) :
    groupedPhysicalTest P p F (p i) = F i (p i) := by
  have hf : Finset.univ.filter (fun j => p j = p i) = {i} := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ⟨hi j, fun h => by rw [h]⟩
  funext x
  simp only [groupedPhysicalTest, hf, Finset.prod_singleton]

/-- A single occurrence of a mean-zero test annihilates the entire short-
period sum, without any character assumption. -/
theorem physicalTupleSum_singleton_zero {I : Type*} [Fintype I]
    (P : Finset ℕ) [∀ q : P, NeZero (q : ℕ)] (hP : ∀ q ∈ P, q.Prime) (p : I → P)
    (F : I → (q : P) → ZMod (q : ℕ) → ℂ)
    (i : I) (hi : ∀ j, p j = p i → j = i) (hmean : ∑ x, F i (p i) x = 0)
    (ψ : 𝓢(ℝ, ℂ)) (X H : ℝ) (hX : 0 < X)
    (hperiod : H < X / (∏ q : P, (q : ℕ)))
    (hsupp : ∀ x : ℝ, H < |x| → 𝓕 ψ x = 0) :
    physicalTupleSum P p F ψ X = 0 := by
  let q : P → ℕ := fun q => q
  let : NeZero (∏ q : P, (q : ℕ)) :=
    ⟨(Finset.prod_pos (s := Finset.univ) (f := fun q : P => (q : ℕ))
      (fun q _ => (hP q q.property).pos)).ne'⟩
  have hc : Pairwise (fun a b : P => (a : ℕ).Coprime (b : ℕ)) :=
    fun a b hab => (Nat.coprime_primes (hP a a.property) (hP b b.property)).mpr
      (fun h => hab (Subtype.ext h))
  have hz : additiveFourier (tupleCRTFunction q hc (groupedPhysicalTest P p F)) 0 = 0 := by
    rw [tupleCRTFunction_fourier]
    apply Finset.prod_eq_zero (Finset.mem_univ (p i))
    simp only [map_zero, Pi.zero_apply, mul_zero, groupedPhysicalTest_singleton P p F i hi]
    rw [additiveFourier_apply]
    simp only [mul_zero, neg_zero, AddChar.map_zero_eq_one, mul_one, hmean]
  have hs := periodic_poisson_complete_mean (tupleCRTFunction q hc (groupedPhysicalTest P p F))
    ψ X H hX hperiod hsupp
  simp_rw [tupleCRTFunction_intCast, groupedPhysicalTest_product] at hs
  rw [physicalTupleSum, hs, hz, mul_zero]

theorem groupedPhysicalTest_sqrt_product {I : Type*} [Fintype I]
    (P : Finset ℕ) (p : I → P) :
    (∏ q : P, Real.sqrt (q : ℝ) ^ (Finset.univ.filter (fun i => p i = q)).card) =
      Real.sqrt (∏ i, (p i : ℝ)) := by
  have he (q : P) : (∏ i ∈ Finset.univ.filter (fun i => p i = q), Real.sqrt (p i : ℝ)) =
      Real.sqrt (q : ℝ) ^ (Finset.univ.filter (fun i => p i = q)).card := by
    rw [← Finset.prod_const]
    apply Finset.prod_congr rfl
    intro i hi
    rw [(Finset.mem_filter.mp hi).2]
  simp_rw [← he]
  rw [Finset.prod_fiberwise, Real.sqrt_prod _ (fun i _ => Nat.cast_nonneg (p i).val)]

/-- The repeated tuple estimate needed in Section 7.3. Its dependence on
the product counted with multiplicity is exact. -/
theorem physicalTupleSum_multiple_bound {I : Type*} [Fintype I]
    (P : Finset ℕ) [∀ q : P, NeZero (q : ℕ)] (hP : ∀ q ∈ P, q.Prime) (p : I → P)
    (F : I → (q : P) → ZMod (q : ℕ) → ℂ)
    (hmultiple : ∀ q : P, 2 ≤ (Finset.univ.filter (fun i => p i = q)).card)
    (henergy : ∀ i, ∑ x, ‖F i (p i) x‖ ^ 2 ≤ (p i : ℝ))
    (ψ : 𝓢(ℝ, ℂ)) (X H : ℝ) (hX : 0 < X)
    (hperiod : H < X / (∏ q : P, (q : ℕ)))
    (hsupp : ∀ x : ℝ, H < |x| → 𝓕 ψ x = 0) :
    ‖physicalTupleSum P p F ψ X‖ ≤
      X * ‖𝓕 ψ 0‖ * (Real.sqrt (∏ i, (p i : ℝ)) / ∏ q : P, (q : ℝ)) := by
  let q : P → ℕ := fun q => q
  let : NeZero (∏ q : P, (q : ℕ)) :=
    ⟨(Finset.prod_pos (s := Finset.univ) (f := fun q : P => (q : ℕ))
      (fun q _ => (hP q q.property).pos)).ne'⟩
  have hc : Pairwise (fun a b : P => (a : ℕ).Coprime (b : ℕ)) :=
    fun a b hab => (Nat.coprime_primes (hP a a.property) (hP b b.property)).mpr
      (fun h => hab (Subtype.ext h))
  have hlocal (a : P) : ‖additiveFourier (groupedPhysicalTest P p F a) 0‖ ≤
      (a : ℝ)⁻¹ * Real.sqrt (a : ℝ) ^ (Finset.univ.filter (fun i => p i = a)).card := by
    apply product_complete_mean_norm_le _ _ (hmultiple a)
    intro i hi
    have ha := (Finset.mem_filter.mp hi).2
    subst a
    exact henergy i
  have hm : ‖additiveFourier (tupleCRTFunction q hc (groupedPhysicalTest P p F)) 0‖ ≤
      Real.sqrt (∏ i, (p i : ℝ)) / ∏ a : P, (a : ℝ) := by
    rw [tupleCRTFunction_fourier]
    simp only [map_zero, Pi.zero_apply, mul_zero, norm_prod]
    apply (Finset.prod_le_prod (fun a _ => norm_nonneg _) (fun a _ => hlocal a)).trans_eq
    rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib, groupedPhysicalTest_sqrt_product,
      div_eq_mul_inv, mul_comm]
  have hs := periodic_poisson_complete_mean (tupleCRTFunction q hc (groupedPhysicalTest P p F))
    ψ X H hX hperiod hsupp
  simp_rw [tupleCRTFunction_intCast, groupedPhysicalTest_product] at hs
  rw [physicalTupleSum, hs, norm_mul, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hX]
  exact mul_le_mul_of_nonneg_left hm (mul_nonneg hX.le (norm_nonneg _))

/-- Either every used prime occurs twice, or a singleton mean-zero test
makes the complete residue mean vanish. This is the uniform short-period
bound before any summation over repeated tuples. -/
theorem physicalTupleSum_short_period_bound {I : Type*} [Fintype I]
    (P : Finset ℕ) [∀ q : P, NeZero (q : ℕ)]
    (hP : ∀ q ∈ P, q.Prime) (p : I → P) (hp : Function.Surjective p)
    (F : I → (q : P) → ZMod (q : ℕ) → ℂ)
    (hmean : ∀ i, ∑ x, F i (p i) x = 0)
    (henergy : ∀ i, ∑ x, ‖F i (p i) x‖ ^ 2 ≤ (p i : ℝ))
    (ψ : 𝓢(ℝ, ℂ)) (X H : ℝ) (hX : 0 < X)
    (hperiod : H < X / (∏ q : P, (q : ℕ)))
    (hsupp : ∀ x : ℝ, H < |x| → 𝓕 ψ x = 0) :
    ‖physicalTupleSum P p F ψ X‖ ≤
      X * ‖𝓕 ψ 0‖ * (Real.sqrt (∏ i, (p i : ℝ)) / ∏ q : P, (q : ℝ)) := by
  by_cases hm : ∀ q : P, 2 ≤ (Finset.univ.filter (fun i => p i = q)).card
  · exact physicalTupleSum_multiple_bound P hP p F hm henergy ψ X H hX hperiod hsupp
  · obtain ⟨q, hq⟩ := not_forall.mp hm
    obtain ⟨i, hi⟩ := hp q
    have hpos : 0 < (Finset.univ.filter (fun j => p j = q)).card :=
      Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
    have hone : (Finset.univ.filter (fun j => p j = q)).card = 1 := by omega
    have hsingle (j : I) (hj : p j = p i) : j = i := by
      apply Finset.card_le_one.mp hone.le j
        (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj.trans hi⟩) i
        (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩)
    rw [physicalTupleSum_singleton_zero P hP p F i hsingle (hmean i) ψ X H hX hperiod hsupp,
      norm_zero]
    positivity

/-- Repeating one prime makes the true period short at the initial product
scale. The resulting bound uses the actual physical tests throughout. -/
theorem physicalTupleSum_repeated_bound {I : Type*} [Fintype I]
    (P : Finset ℕ) [∀ q : P, NeZero (q : ℕ)]
    (hP : ∀ q ∈ P, q.Prime) (p : I → P) (hp : Function.Surjective p)
    (F : I → (q : P) → ZMod (q : ℕ) → ℂ)
    (hmean : ∀ i, ∑ x, F i (p i) x = 0)
    (henergy : ∀ i, ∑ x, ‖F i (p i) x‖ ^ 2 ≤ (p i : ℝ))
    (ψ : 𝓢(ℝ, ℂ)) (X H R : ℝ) (hX : 0 < X) (hR : 0 < R)
    (hsupp : ∀ x : ℝ, H < |x| → 𝓕 ψ x = 0)
    (hsmall : ∀ i, H * R < (p i : ℝ)) (hprod : (∏ i, (p i : ℝ)) ≤ X * R)
    (i j : I) (hij : i ≠ j) (heq : p i = p j) :
    ‖physicalTupleSum P p F ψ X‖ ≤
      X * ‖𝓕 ψ 0‖ * (Real.sqrt (∏ i, (p i : ℝ)) / ∏ q : P, (q : ℝ)) := by
  have hs := repeated_tuple_short_period (fun i => (p i : ℕ))
    (fun i => hP (p i) (p i).property) X H R hR hsmall hprod i j hij
    (congrArg Subtype.val heq)
  have he : sampledPrimeSet (fun i => (p i : ℕ)) = P := by
    ext q
    constructor
    · intro hq
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hq
      exact (p i).property
    · intro hq
      obtain ⟨i, hi⟩ := hp ⟨q, hq⟩
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, congrArg Subtype.val hi⟩
  rw [he] at hs
  have hperiod : H < X / (∏ q : P, (q : ℕ)) := by
    rw [Finset.prod_coe_sort P (fun q : ℕ => q)]
    exact hs
  exact physicalTupleSum_short_period_bound P hP p hp F hmean henergy ψ X H hX hperiod hsupp

/-- The ambient prime set may contain unused values. Restricting to the
actual image gives the true squarefree period and leaves every test unchanged. -/
theorem physicalTupleSum_repeated_bound_used {I : Type*} [Fintype I]
    (P : Finset ℕ) [∀ q : P, NeZero (q : ℕ)]
    (hP : ∀ q ∈ P, q.Prime) (p : I → P)
    (F : I → (q : P) → ZMod (q : ℕ) → ℂ)
    (hmean : ∀ i, ∑ x, F i (p i) x = 0)
    (henergy : ∀ i, ∑ x, ‖F i (p i) x‖ ^ 2 ≤ (p i : ℝ))
    (ψ : 𝓢(ℝ, ℂ)) (X H R : ℝ) (hX : 0 < X) (hR : 0 < R)
    (hsupp : ∀ x : ℝ, H < |x| → 𝓕 ψ x = 0)
    (hsmall : ∀ i, H * R < (p i : ℝ)) (hprod : (∏ i, (p i : ℝ)) ≤ X * R)
    (i j : I) (hij : i ≠ j) (heq : p i = p j) :
    ‖physicalTupleSum P p F ψ X‖ ≤
      X * ‖𝓕 ψ 0‖ * (Real.sqrt (∏ i, (p i : ℝ)) /
        ∏ q ∈ Finset.univ.image p, (q : ℝ)) := by
  let Q := sampledPrimeSet (fun i => (p i : ℕ))
  have hQP : Q ⊆ P := by
    intro q hq
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hq
    exact (p i).property
  let toP : Q → P := fun q => ⟨q.val, hQP q.property⟩
  let p' : I → Q := fun i => ⟨(p i : ℕ), Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩
  let F' : I → (q : Q) → ZMod (q : ℕ) → ℂ := fun i q => F i (toP q)
  let : ∀ q : Q, NeZero (q : ℕ) := fun q => ⟨(hP q (hQP q.property)).ne_zero⟩
  have hback (i : I) : toP (p' i) = p i := Subtype.ext rfl
  have hp' : Function.Surjective p' := by
    intro q
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp q.property
    exact ⟨i, Subtype.ext hi⟩
  have hm' (i : I) : (∑ x, F' i (p' i) x) = 0 := by
    simpa only [F', hback] using hmean i
  have he' (i : I) : (∑ x, ‖F' i (p' i) x‖ ^ 2) ≤ (p' i : ℝ) := by
    simpa only [F', hback] using henergy i
  have hij' : p' i = p' j :=
    Subtype.ext (congrArg (fun z : P => (z : ℕ)) heq)
  have h := physicalTupleSum_repeated_bound Q (fun q hq => hP q (hQP hq)) p' hp' F'
    hm' he' ψ X H R hX hR hsupp hsmall hprod i j hij hij'
  have hsum : physicalTupleSum Q p' F' ψ X = physicalTupleSum P p F ψ X := by
    unfold physicalTupleSum
    apply tsum_congr
    intro a
    congr 1
  have hperiod : (∏ q : Q, (q : ℝ)) = ∏ q ∈ Finset.univ.image p, (q : ℝ) := by
    rw [Finset.prod_coe_sort Q (fun q : ℕ => (q : ℝ))]
    have hQ : Q = (Finset.univ.image p).image (fun z : P => (z : ℕ)) := by
      simp only [Q, sampledPrimeSet, Finset.image_image, Function.comp_def]
    rw [hQ]
    rw [Finset.prod_image]
    exact fun a _ b _ hab => Subtype.ext hab
  simpa only [hsum, hperiod, p'] using h

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_PrimePhysicalTest
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact physical tests for the two kinds of prime position -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

/-- Degenerate residue sets give the zero normalized test. Thus the energy
bound holds before a balanced-prime restriction is inserted. -/
theorem normalizedResidueIndicator_energy_le {p : ℕ} [NeZero p]
    (S : Finset (ZMod p)) :
    (∑ x, ‖normalizedResidueIndicator S x‖ ^ 2) ≤ (p : ℝ) := by
  by_cases hS : S.Nonempty
  · by_cases hSp : S.card < p
    · exact (normalizedResidueIndicator_energy S hS hSp).le
    · have hc : S.card = p := by
        have ht := Finset.card_le_univ S
        rw [ZMod.card] at ht
        omega
      have hp : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne p)
      have hv : residueVariance S = 0 := by
        simp only [residueVariance, residueDensity, hc, div_self hp, sub_self, mul_zero]
      simp only [normalizedResidueIndicator, hv, Real.sqrt_zero, div_zero,
        Complex.ofReal_zero, norm_zero, zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero]
      exact Nat.cast_nonneg p
  · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    subst S
    simp only [normalizedResidueIndicator, residueVariance, residueDensity, Finset.card_empty,
      Nat.cast_zero, zero_div, zero_mul, Real.sqrt_zero, div_zero, Complex.ofReal_zero,
      norm_zero, zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero]
    exact Nat.cast_nonneg p

theorem primePhysicalTest_sum {p : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (giant favorable : Bool) :
    (∑ x, primePhysicalTest S giant favorable x) = 0 := by
  cases giant <;> cases favorable <;> simp only [primePhysicalTest, Bool.false_eq_true,
    ↓reduceIte, Finset.sum_const_zero, normalizedResidueIndicator_sum,
    phaseGiantPhysical_sum_zero _ (normalizedResidueTransform_zero S)]

theorem primePhysicalTest_energy {p : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (giant favorable : Bool) :
    (∑ x, ‖primePhysicalTest S giant favorable x‖ ^ 2) ≤ (p : ℝ) := by
  cases giant <;> cases favorable
  · exact normalizedResidueIndicator_energy_le S
  · exact normalizedResidueIndicator_energy_le S
  · simp only [primePhysicalTest, ↓reduceIte, Bool.false_eq_true, norm_zero,
      zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero]
    exact Nat.cast_nonneg p
  · exact phaseGiantPhysical_energy _

theorem primePhysicalTest_real {p : ℕ} [Fact p.Prime]
    (S : Finset (ZMod p)) (giant favorable : Bool) (x : ZMod p) :
    (primePhysicalTest S giant favorable x).im = 0 := by
  cases giant <;> cases favorable
  · exact Complex.ofReal_im _
  · exact Complex.ofReal_im _
  · rfl
  · exact phaseGiantPhysical_real _ (normalizedResidueTransform_neg S) x

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

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_HarmonicRepeatedMass
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Repeated tuples under the original normalized harmonic priors -/

namespace Ostmann

open scoped BigOperators Classical

theorem inverse_sqrt_exp_product (X D : ℝ) (hX : 0 < X) :
    X * (Real.sqrt (X * Real.exp D))⁻¹ =
      Real.sqrt X * Real.exp (-(D / 2)) := by
  rw [Real.sqrt_mul hX.le, ← Real.exp_half, mul_inv, Real.exp_neg]
  have hx : Real.sqrt X ≠ 0 := (Real.sqrt_pos.mpr hX).ne'
  have hs : Real.sqrt X ^ 2 = X := Real.sq_sqrt hX.le
  field_simp
  nlinarith [hs]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_PrimeTupleFiber
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Matching-fibre mass for the original mixed prime priors -/

namespace Ostmann
open scoped Classical BigOperators

/-- This applies simultaneously to the giant, broad-band, and deleted cell
marginals: only their already proved reciprocal-prime atom bounds are used. -/
theorem prime_tuple_prior_point_bound {n : ℕ} (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (μ : Fin n → P → ℝ) (C : Fin n → ℝ)
    (hμ : ∀ i p, 0 ≤ μ i p) (hbound : ∀ i (p : P), (p : ℝ) * μ i p ≤ C i)
    (x : Fin n → P) :
    productPrior μ x ≤ (∏ i, C i) * (∏ i, (x i : ℝ))⁻¹ := by
  have hi (i : Fin n) : μ i (x i) ≤ C i * (x i : ℝ)⁻¹ := by
    have hp : 0 < (x i : ℝ) := Nat.cast_pos.mpr (hP (x i) (x i).property).pos
    exact (le_div_iff₀ hp).mpr (by simpa only [mul_comm] using hbound i (x i))
  have h := Finset.prod_le_prod (s := Finset.univ) (fun i _ => hμ i (x i)) (fun i _ => hi i)
  simpa only [productPrior, Finset.prod_mul_distrib, Finset.prod_inv_distrib] using h

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_RepeatedPhysicalPrior
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing repetitions under the original mixed prime priors -/

namespace Ostmann
open scoped Classical BigOperators FourierTransform SchwartzMap

/-- Summing the reciprocal weight of the distinct values costs at most
`n^n`, even for tuples which have singleton values. -/
theorem tuple_distinct_weight_exp {A : Type*} [Fintype A] (n : ℕ)
    (w : A → ℝ) (hw : ∀ a, 0 ≤ w a) :
    (∑ x : Fin n → A, ∏ a ∈ Finset.univ.image x, w a) ≤
      (n : ℝ) ^ n * Real.exp (∑ a, w a) := by
  have hmaps (x : Fin n → A) (_hx : x ∈ Finset.univ) :
      Finset.univ.image x ∈ (Finset.univ : Finset A).powerset := by simp
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hfiber (S : Finset A) :
      (∑ x ∈ (Finset.univ : Finset (Fin n → A)).filter
        (fun x => Finset.univ.image x = S), ∏ a ∈ Finset.univ.image x, w a) ≤
      (n : ℝ) ^ n * ∏ a ∈ S, w a := by
    let T := (Finset.univ : Finset (Fin n → A)).filter (fun x => Finset.univ.image x = S)
    have hc : T.card ≤ n ^ n := tuple_range_fiber_card_le n S
    calc
      _ = ∑ _x ∈ T, ∏ a ∈ S, w a := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [(Finset.mem_filter.mp hx).2]
      _ = (T.card : ℝ) * ∏ a ∈ S, w a := by simp
      _ ≤ _ := by
        simpa only [Nat.cast_pow] using mul_le_mul_of_nonneg_right
          (Nat.cast_le.mpr hc : (T.card : ℝ) ≤ (n ^ n : ℕ))
          (Finset.prod_nonneg (fun a _ => hw a))
  calc
    _ ≤ ∑ S ∈ (Finset.univ : Finset A).powerset, (n : ℝ) ^ n * ∏ a ∈ S, w a :=
      Finset.sum_le_sum (fun S _ => hfiber S)
    _ = (n : ℝ) ^ n * ∏ a, (1 + w a) := by
      rw [← Finset.mul_sum, ← Finset.prod_one_add]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.prod_one_add_le_exp_sum Finset.univ hw) (by positivity)

/-- The original smooth/harmonic marginal bounds and the physical repeated-
test estimate imply the error in (7.3), retaining every normalizer. -/
theorem repeated_physical_prior_bound_at {n : ℕ}
    (P : Finset ℕ) [∀ q : P, NeZero (q : ℕ)] (hP : ∀ q ∈ P, q.Prime)
    (μ : Fin n → P → ℝ) (C : Fin n → ℝ)
    (hμ : ∀ i p, 0 ≤ μ i p) (hC : ∀ i, 0 ≤ C i)
    (hbound : ∀ i (p : P), (p : ℝ) * μ i p ≤ C i)
    (F : Fin n → (q : P) → ZMod (q : ℕ) → ℂ)
    (hmean : ∀ i q, ∑ x, F i q x = 0)
    (henergy : ∀ i (q : P), ∑ x, ‖F i q x‖ ^ 2 ≤ (q : ℝ))
    (ψ : 𝓢(ℝ, ℂ)) (X H R Δ : ℝ) (hX : 0 < X) (hR : 0 < R)
    (hsupp : ∀ x : ℝ, H < |x| → 𝓕 ψ x = 0)
    (E : Finset (Fin n → P)) (hE : ∀ x ∈ E, ¬ Function.Injective x)
    (hsmall : ∀ x ∈ E, ∀ i, H * R < (x i : ℝ))
    (hprod : ∀ x ∈ E, X * Real.exp Δ ≤ ∏ i, (x i : ℝ))
    (hupper : ∀ x ∈ E, (∏ i, (x i : ℝ)) ≤ X * R)
    (w : (Fin n → P) → ℂ) (hw : ∀ x ∈ E, ‖w x‖ ≤ 1) :
    ‖∑ x ∈ E, (productPrior μ x : ℂ) * w x * physicalTupleSum P x F ψ X‖ ≤
      Real.sqrt X * (‖𝓕 ψ 0‖ * (∏ i, C i) * (n : ℝ) ^ n *
        Real.exp ((∑ p : P, (p : ℝ)⁻¹) - Δ / 2)) := by
  classical
  have hCprod : 0 ≤ ∏ i, C i := Finset.prod_nonneg (fun i _ => hC i)
  let B := Real.sqrt X * (‖𝓕 ψ 0‖ * (∏ i, C i) * Real.exp (-Δ / 2))
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hterm (x : Fin n → P) (hx : x ∈ E) :
      ‖(productPrior μ x : ℂ) * w x * physicalTupleSum P x F ψ X‖ ≤
        B * ∏ p ∈ Finset.univ.image x, (p : ℝ)⁻¹ := by
    obtain ⟨i, j, heq, hij⟩ := Function.not_injective_iff.mp (hE x hx)
    have hs := physicalTupleSum_repeated_bound_used P hP x F
      (fun i => hmean i (x i)) (fun i => henergy i (x i)) ψ X H R hX hR hsupp
      (hsmall x hx) (hupper x hx) i j hij heq
    let M : ℝ := ∏ i, (x i : ℝ)
    let Q : ℝ := ∏ p ∈ Finset.univ.image x, (p : ℝ)
    have hM : 0 < M := Finset.prod_pos (fun i _ => Nat.cast_pos.mpr (hP (x i) (x i).property).pos)
    have hQ : 0 < Q := Finset.prod_pos (fun p _ => Nat.cast_pos.mpr (hP p p.property).pos)
    have hroot : 0 < Real.sqrt M := Real.sqrt_pos.mpr hM
    have hpoint := prime_tuple_prior_point_bound P hP μ C hμ hbound x
    have hnorm : ‖(productPrior μ x : ℂ) * w x * physicalTupleSum P x F ψ X‖ ≤
        ((∏ i, C i) * M⁻¹) * (X * ‖𝓕 ψ 0‖ * (Real.sqrt M / Q)) := by
      rw [norm_mul, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg (productPrior_nonneg μ hμ x)]
      have hfirst : productPrior μ x * ‖w x‖ ≤ (∏ i, C i) * M⁻¹ := by
        simpa only [mul_one] using mul_le_mul hpoint (hw x hx) (norm_nonneg _)
          (mul_nonneg hCprod (inv_nonneg.mpr hM.le))
      exact mul_le_mul hfirst hs (norm_nonneg _) (by positivity)
    have hid : ((∏ i, C i) * M⁻¹) * (X * ‖𝓕 ψ 0‖ * (Real.sqrt M / Q)) =
        (X * (Real.sqrt M)⁻¹) * (‖𝓕 ψ 0‖ * (∏ i, C i)) * Q⁻¹ := by
      have hsq := Real.sq_sqrt hM.le
      field_simp [hM.ne', hQ.ne', hroot.ne']
      linear_combination (∏ i, C i) * ‖𝓕 ψ 0‖ * hsq
    have hi : (Real.sqrt M)⁻¹ ≤ (Real.sqrt (X * Real.exp Δ))⁻¹ :=
      inv_anti₀ (Real.sqrt_pos.mpr (mul_pos hX (Real.exp_pos _)))
        (Real.sqrt_le_sqrt (hprod x hx))
    calc
      _ ≤ (X * (Real.sqrt M)⁻¹) * (‖𝓕 ψ 0‖ * (∏ i, C i)) * Q⁻¹ := hnorm.trans_eq hid
      _ ≤ (X * (Real.sqrt (X * Real.exp Δ))⁻¹) * (‖𝓕 ψ 0‖ * (∏ i, C i)) * Q⁻¹ := by
        gcongr
      _ = _ := by
        rw [inverse_sqrt_exp_product X Δ hX, Finset.prod_inv_distrib]
        dsimp only [B, Q]
        rw [show -Δ / 2 = -(Δ / 2) by ring]
        ring
  calc
    _ ≤ ∑ x ∈ E, B * ∏ p ∈ Finset.univ.image x, (p : ℝ)⁻¹ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum hterm)
    _ = B * ∑ x ∈ E, ∏ p ∈ Finset.univ.image x, (p : ℝ)⁻¹ := (Finset.mul_sum ..).symm
    _ ≤ B * ((n : ℝ) ^ n * Real.exp (∑ p : P, (p : ℝ)⁻¹)) := by
      apply mul_le_mul_of_nonneg_left _ hB
      apply (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ E)
        (fun x _ _ => Finset.prod_nonneg (fun p _ => by positivity))).trans
      convert tuple_distinct_weight_exp n (fun p : P => (p : ℝ)⁻¹) (fun _ => by positivity) using 1
      all_goals try with_reducible_and_instances rfl
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.prod_congr
      · ext p
        simp only [Finset.mem_image]
      · intro p _
        rfl
    _ = _ := by
      dsimp only [B]
      rw [show -Δ / 2 = -(Δ / 2) by ring]
      rw [Real.exp_sub, Real.exp_neg]
      ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_RegularInitialAmplitude
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original initial Fourier amplitude and repeated-prime error -/

namespace Ostmann
open scoped Classical BigOperators FourierTransform SchwartzMap

/-- Before estimating anything, the retained Fourier amplitude and the
discarded repeated tuples sum to the original physical statistic exactly. -/
theorem initial_physical_fourier_decomposition {n : ℕ}
    (P : Finset ℕ) [∀ q : P, NeZero (q : ℕ)] (hP : ∀ q ∈ P, q.Prime)
    (μ : Fin n → P → ℝ) (F : Fin n → (q : P) → ZMod (q : ℕ) → ℂ)
    (ψ : 𝓢(ℝ, ℂ)) (X H : ℝ) (hX : 0 < X) (N : ℕ)
    (w : (Fin n → P) → ℂ)
    (hcut : ∀ x, w x ≠ 0 → H * (∏ i, (x i : ℕ)) ≤ N * X)
    (hsupp : ∀ t : ℝ, H < |t| → 𝓕 ψ t = 0) :
    (∑ x : Fin n → P, (productPrior μ x : ℂ) * w x * physicalTupleSum P x F ψ X) =
      (Real.sqrt X : ℂ) * regularInitialAmplitude P μ F ψ X N w +
        ∑ x ∈ Finset.univ.filter (fun x : Fin n → P => ¬ Function.Injective x),
          (productPrior μ x : ℂ) * w x * physicalTupleSum P x F ψ X := by
  unfold regularInitialAmplitude
  rw [Finset.sum_filter, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hw : w x = 0
  · simp only [hw, mul_zero, zero_mul, ite_self, add_zero]
  by_cases hx : Function.Injective x
  · have hc : Pairwise (fun i j => (x i : ℕ).Coprime (x j : ℕ)) := by
      intro i j hij
      exact (Nat.coprime_primes (hP (x i) (x i).property)
        (hP (x j) (x j).property)).mpr (fun h => hij (hx (Subtype.ext h)))
    let : NeZero (∏ i, (x i : ℕ)) :=
      ⟨(Finset.prod_pos (fun i _ => (hP (x i) (x i).property).pos)).ne'⟩
    have hpoisson := tuple_regular_poisson_profile (fun i => (x i : ℕ)) hc
      (fun i => F i (x i)) ψ X H hX N (hcut x hw) hsupp
    change physicalTupleSum P x F ψ X / (Real.sqrt X : ℂ) =
      primeTupleFourierCoefficient P F ψ X N x at hpoisson
    have hroot : (Real.sqrt X : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hX).ne'
    have he := (div_eq_iff hroot).mp hpoisson
    simp only [hx, not_true_eq_false, ite_true, if_true, ite_false, if_false, add_zero]
    rw [he]
    ring
  · simp only [hx, not_false_eq_true, ite_false, if_false, ite_true, if_true, mul_zero, zero_add]

/-- The positive statistic lower bound survives repeated-prime removal and
becomes the lower bound on the actual finite initial Fourier amplitude. -/
theorem regularInitialAmplitude_lower {n : ℕ}
    (P : Finset ℕ) [∀ q : P, NeZero (q : ℕ)] (hP : ∀ q ∈ P, q.Prime)
    (μ : Fin n → P → ℝ) (F : Fin n → (q : P) → ZMod (q : ℕ) → ℂ)
    (ψ : 𝓢(ℝ, ℂ)) (X H : ℝ) (hX : 0 < X) (N : ℕ)
    (w : (Fin n → P) → ℂ)
    (hcut : ∀ x, w x ≠ 0 → H * (∏ i, (x i : ℕ)) ≤ N * X)
    (hsupp : ∀ t : ℝ, H < |t| → 𝓕 ψ t = 0)
    (δ ε : ℝ)
    (hpositive : Real.sqrt X * (δ + ε) ≤
      ‖∑ x : Fin n → P, (productPrior μ x : ℂ) * w x * physicalTupleSum P x F ψ X‖)
    (herror : ‖∑ x ∈ Finset.univ.filter (fun x : Fin n → P => ¬ Function.Injective x),
      (productPrior μ x : ℂ) * w x * physicalTupleSum P x F ψ X‖ ≤ Real.sqrt X * ε) :
    δ ≤ ‖regularInitialAmplitude P μ F ψ X N w‖ := by
  rw [initial_physical_fourier_decomposition P hP μ F ψ X H hX N w hcut hsupp] at hpositive
  have hn := (norm_add_le ((Real.sqrt X : ℂ) * regularInitialAmplitude P μ F ψ X N w)
    (∑ x ∈ Finset.univ.filter (fun x : Fin n → P => ¬ Function.Injective x),
      (productPrior μ x : ℂ) * w x * physicalTupleSum P x F ψ X)).trans
    (add_le_add le_rfl herror)
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg X)] at hn
  have hs := Real.sqrt_pos.mpr hX
  nlinarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_WordCopyCoordinates
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The two copies of every word and cell role as one ordered tuple -/

namespace Ostmann

open scoped BigOperators ComplexConjugate Classical

theorem productPrior_append {A : Type*} {k m : ℕ}
    (μ : Fin k → A → ℝ) (ν : Fin m → A → ℝ) (x : Fin k → A) (y : Fin m → A) :
    productPrior (Fin.append μ ν) (Fin.append x y) = productPrior μ x * productPrior ν y := by
  simp only [productPrior, Fin.prod_univ_add, Fin.append_left, Fin.append_right]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_HalfPrimeStatistic
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The two independent half-lists in the positive physical statistic -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap FourierTransform ComplexConjugate

theorem physicalTupleTerm_summable {I : Type*} [Fintype I]
    (P : Finset ℕ) [∀ q : P, NeZero (q : ℕ)] (p : I → P)
    (F : I → (q : P) → ZMod (q : ℕ) → ℂ)
    (ψ : 𝓢(ℝ, ℂ)) (X : ℝ) (hX : 0 < X) :
    Summable (fun a : ℤ => (∏ i, F i (p i) (a : ZMod (p i : ℕ))) * ψ ((a : ℝ) / X)) := by
  have hs : Summable (fun a : ℤ => ‖ψ ((a : ℝ) / X)‖) := by
    simpa only [positiveDilate_apply, div_eq_mul_inv, mul_comm] using
      schwartz_int_norm_summable (positiveDilate ψ X⁻¹ (inv_pos.mpr hX))
  apply Summable.of_norm_bounded (hs.mul_left (∏ i, ∑ b, ‖F i (p i) b‖))
  intro a
  rw [norm_mul, norm_prod]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun i _ =>
    Finset.single_le_sum (fun b _ => norm_nonneg (F i (p i) b)) (Finset.mem_univ _))

/-- All positions, including the two giants and the outside spectators,
are sampled twice independently in the initial square. -/
theorem halfPrimeMean_square {n : ℕ} (P : Finset ℕ) (μ : Fin n → P → ℝ)
    (F : Fin n → (q : P) → ZMod (q : ℕ) → ℂ)
    (w : (Fin n → P) → ℂ) (a : ℤ) :
    halfPrimeMean P μ F w a ^ 2 =
      ∑ x : Fin (n + n) → P, (productPrior (Fin.append μ μ) x : ℂ) * doubledHalfWeight w x *
        ∏ i, Fin.append F F i (x i) (a : ZMod (x i : ℕ)) := by
  let e : ((Fin n → P) × (Fin n → P)) ≃ (Fin (n + n) → P) := Fin.appendEquiv n n
  rw [← e.sum_comp, Fintype.sum_prod_type]
  unfold halfPrimeMean
  rw [pow_two, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  change _ = (productPrior (Fin.append μ μ) (Fin.append x y) : ℂ) *
    doubledHalfWeight w (Fin.append x y) *
      ∏ i, Fin.append F F i (Fin.append x y i)
        (a : ZMod ((Fin.append x y : Fin (n + n) → P) i : ℕ))
  simp only [productPrior_append, doubledHalfWeight, Fin.prod_univ_add,
    Fin.append_left, Fin.append_right, Complex.ofReal_mul]
  have hxF : (∏ i : Fin n, F i (Fin.append x y (i.castAdd n))
      (a : ZMod ((Fin.append x y : Fin (n + n) → P) (i.castAdd n) : ℕ))) =
      ∏ i, F i (x i) (a : ZMod (x i : ℕ)) := by
    apply Finset.prod_congr rfl
    intro i _
    exact congrArg (fun q : P => F i q (a : ZMod (q : ℕ))) (Fin.append_left x y i)
  have hyF : (∏ i : Fin n, F i (Fin.append x y (i.natAdd n))
      (a : ZMod ((Fin.append x y : Fin (n + n) → P) (i.natAdd n) : ℕ))) =
      ∏ i, F i (y i) (a : ZMod (y i : ℕ)) := by
    apply Finset.prod_congr rfl
    intro i _
    exact congrArg (fun q : P => F i q (a : ZMod (q : ℕ))) (Fin.append_right x y i)
  rw [hxF, hyF]
  ring

/-- Exchanging only finite original sample sums with the Schwartz sum gives
the exact physical statistic used by the initial Fourier lower bound. -/
theorem halfPrimeMean_statistic {n : ℕ}
    (P : Finset ℕ) [∀ q : P, NeZero (q : ℕ)] (μ : Fin n → P → ℝ)
    (F : Fin n → (q : P) → ZMod (q : ℕ) → ℂ)
    (w : (Fin n → P) → ℂ) (ψ : 𝓢(ℝ, ℂ)) (X : ℝ) (hX : 0 < X) :
    (∑' a : ℤ, halfPrimeMean P μ F w a ^ 2 * ψ ((a : ℝ) / X)) =
      ∑ x : Fin (n + n) → P, (productPrior (Fin.append μ μ) x : ℂ) * doubledHalfWeight w x *
        physicalTupleSum P x (Fin.append F F) ψ X := by
  simp_rw [halfPrimeMean_square, Finset.sum_mul]
  have hs (x : Fin (n + n) → P) : Summable (fun a : ℤ =>
      ((productPrior (Fin.append μ μ) x : ℂ) * doubledHalfWeight w x *
        ∏ i, Fin.append F F i (x i) (a : ZMod (x i : ℕ))) * ψ ((a : ℝ) / X)) := by
    simpa only [mul_assoc] using
      (physicalTupleTerm_summable P x (Fin.append F F) ψ X hX).mul_left
        ((productPrior (Fin.append μ μ) x : ℂ) * doubledHalfWeight w x)
  rw [Summable.tsum_finsetSum (fun x _ => hs x)]
  apply Finset.sum_congr rfl
  intro x _
  rw [physicalTupleSum, ← tsum_mul_left]
  apply tsum_congr
  intro a
  ring

theorem halfPrimeMean_bound {n : ℕ}
    (P : Finset ℕ) [∀ q : P, NeZero (q : ℕ)] (μ : Fin n → P → ℝ)
    (F : Fin n → (q : P) → ZMod (q : ℕ) → ℂ)
    (w : (Fin n → P) → ℂ) (a : ℤ) :
    ‖halfPrimeMean P μ F w a‖ ≤ halfPrimeBound P μ F w := by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro x _
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_prod]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun i _ =>
    Finset.single_le_sum (fun b _ => norm_nonneg (F i (x i) b)) (Finset.mem_univ _))

theorem halfPrimeMean_real {n : ℕ} (P : Finset ℕ) (μ : Fin n → P → ℝ)
    (F : Fin n → (q : P) → ZMod (q : ℕ) → ℂ) (w : (Fin n → P) → ℂ)
    (hF : ∀ i q x, (F i q x).im = 0) (hw : ∀ x, (w x).im = 0) (a : ℤ) :
    (halfPrimeMean P μ F w a).im = 0 := by
  have hFc : ∀ i q x, conj (F i q x) = F i q x := by
    intro i q x
    apply Complex.ext <;> simp only [Complex.conj_re, Complex.conj_im, hF, neg_zero]
  have hwc : ∀ x, conj (w x) = w x := by
    intro x
    apply Complex.ext <;> simp only [Complex.conj_re, Complex.conj_im, hw, neg_zero]
  have h : conj (halfPrimeMean P μ F w a) = halfPrimeMean P μ F w a := by
    simp only [halfPrimeMean, map_sum, map_mul, map_prod, Complex.conj_ofReal, hFc, hwc]
  have hi := congrArg Complex.im h
  simp only [Complex.conj_im] at hi
  linarith

theorem halfPrimeMean_statistic_re {n : ℕ}
    (P : Finset ℕ) [∀ q : P, NeZero (q : ℕ)] (μ : Fin n → P → ℝ)
    (F : Fin n → (q : P) → ZMod (q : ℕ) → ℂ)
    (w : (Fin n → P) → ℂ) (ψ : 𝓢(ℝ, ℂ)) (X : ℝ) (hX : 0 < X)
    (hreal : ∀ a, (halfPrimeMean P μ F w a).im = 0) :
    (∑ x : Fin (n + n) → P, (productPrior (Fin.append μ μ) x : ℂ) * doubledHalfWeight w x *
      physicalTupleSum P x (Fin.append F F) ψ X).re =
      ∑' a : ℤ, (ψ ((a : ℝ) / X)).re * ‖halfPrimeMean P μ F w a‖ ^ 2 := by
  let T := halfPrimeMean P μ F w
  have hs : Summable (fun a : ℤ => ‖ψ ((a : ℝ) / X)‖) := by
    simpa only [positiveDilate_apply, div_eq_mul_inv, mul_comm] using
      schwartz_int_norm_summable (positiveDilate ψ X⁻¹ (inv_pos.mpr hX))
  have hc : Summable (fun a : ℤ => T a ^ 2 * ψ ((a : ℝ) / X)) := by
    apply Summable.of_norm_bounded (hs.mul_left (halfPrimeBound P μ F w ^ 2))
    intro a
    rw [norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (norm_nonneg _) (halfPrimeMean_bound P μ F w a) 2) (norm_nonneg _)
  rw [← halfPrimeMean_statistic P μ F w ψ X hX]
  change (∑' a : ℤ, T a ^ 2 * ψ ((a : ℝ) / X)).re = _
  rw [← Complex.reCLM_apply, Complex.reCLM.map_tsum hc]
  apply tsum_congr
  intro a
  have hi : (T a).im = 0 := hreal a
  have hn : ‖T a‖ ^ 2 = (T a).re ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, hi]
    ring
  change (T a ^ 2 * ψ ((a : ℝ) / X)).re = (ψ ((a : ℝ) / X)).re * ‖T a‖ ^ 2
  rw [hn]
  simp only [pow_two, Complex.mul_re, Complex.mul_im, hi,
    mul_zero, zero_mul, add_zero, sub_zero]
  ring

/-- The selected mean over endpoints gives a lower bound for the full
original doubled-list physical statistic. -/
theorem halfPrimeMean_endpoint_lower {n : ℕ}
    (P : Finset ℕ) [∀ q : P, NeZero (q : ℕ)] (μ : Fin n → P → ℝ)
    (F : Fin n → (q : P) → ZMod (q : ℕ) → ℂ)
    (w : (Fin n → P) → ℂ) (ψ : 𝓢(ℝ, ℂ)) (X : ℝ) (hX : 0 < X)
    (hreal : ∀ a, (halfPrimeMean P μ F w a).im = 0)
    (E : Finset ℤ) (c δ : ℝ) (hc : 0 ≤ c) (hδ : 0 ≤ δ)
    (hψ : ∀ x, 0 ≤ (ψ x).re) (hcE : ∀ a ∈ E, c ≤ (ψ ((a : ℝ) / X)).re)
    (hmean : (E.card : ℝ) * δ ≤ ∑ a ∈ E, (halfPrimeMean P μ F w a).re) :
    (E.card : ℝ) * (c * δ ^ 2) ≤
      ‖∑ x : Fin (n + n) → P, (productPrior (Fin.append μ μ) x : ℂ) * doubledHalfWeight w x *
        physicalTupleSum P x (Fin.append F F) ψ X‖ := by
  have hb := wordStatistic_lower_of_endpoint_mean (m := 0) ψ X hX (halfPrimeMean P μ F w)
    (fun i => Fin.elim0 i) E (halfPrimeBound P μ F w) (fun i => Fin.elim0 i)
    hψ (halfPrimeMean_bound P μ F w) (fun i => Fin.elim0 i)
    c δ 1 hc hδ zero_le_one hcE hmean (fun _ _ i => Fin.elim0 i)
  have hb' : (E.card : ℝ) * (c * δ ^ 2) ≤
      ∑' a : ℤ, (ψ ((a : ℝ) / X)).re * ‖halfPrimeMean P μ F w a‖ ^ 2 := by
    simpa only [wordStatisticTerm, Nat.mul_zero, pow_zero, mul_one, Finset.univ_eq_empty,
      Finset.prod_empty] using hb
  rw [← halfPrimeMean_statistic_re P μ F w ψ X hX hreal] at hb'
  exact hb'.trans (Complex.re_le_norm _)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_HalfPrimeFactorization
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Separating the giant mean from the positive nongiant scalar -/

namespace Ostmann
open scoped Classical BigOperators

theorem weighted_tuple_mean_cons {A : Type*} [Fintype A] {n : ℕ}
    (μ₀ : A → ℝ) (μ : Fin n → A → ℝ) (f₀ : A → ℂ) (f : Fin n → A → ℂ)
    (w : (Fin n → A) → ℂ) :
    (∑ y : Fin (n + 1) → A, (productPrior (Fin.cons μ₀ μ) y : ℂ) *
      w (Fin.tail y) * ∏ i, Fin.cons (α := fun _ => A → ℂ) f₀ f i (y i)) =
      (∑ p : A, (μ₀ p : ℂ) * f₀ p) *
        ∑ x : Fin n → A, (productPrior μ x : ℂ) * w x * ∏ i, f i (x i) := by
  let e : A × (Fin n → A) ≃ (Fin (n + 1) → A) := Fin.consEquiv (fun _ => A)
  rw [← e.sum_comp, Fintype.sum_prod_type, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro x _
  change (productPrior (Fin.cons μ₀ μ) (Fin.cons (α := fun _ => A) p x) : ℂ) *
    w (Fin.tail (Fin.cons (α := fun _ => A) p x)) * ∏ i, Fin.cons (α := fun _ => A → ℂ) f₀ f i (Fin.cons (α := fun _ => A) p x i) = _
  simp only [productPrior_cons, Fin.cons_zero, Fin.cons_succ, Fin.tail_cons,
    Fin.prod_univ_succ, Complex.ofReal_mul]
  ring

/-- At an endpoint all nongiant residue tests have values independent of
the endpoint. Their original expectation is therefore one common scalar. -/
theorem halfPrimeMean_cons_scalar {n : ℕ} (P : Finset ℕ)
    (μ₀ : P → ℝ) (μ : Fin n → P → ℝ)
    (F₀ : (q : P) → ZMod (q : ℕ) → ℂ)
    (F : Fin n → (q : P) → ZMod (q : ℕ) → ℂ)
    (w : (Fin n → P) → ℝ) (c : Fin n → P → ℝ) (a : ℤ)
    (hc : ∀ i q, F i q (a : ZMod (q : ℕ)) = (c i q : ℂ)) :
    halfPrimeMean P (Fin.cons μ₀ μ) (Fin.cons F₀ F)
      (fun y => (w (Fin.tail y) : ℂ)) a =
      (halfPrimeScalar P μ w c : ℂ) * ∑ q : P, (μ₀ q : ℂ) * F₀ q (a : ZMod (q : ℕ)) := by
  let f₀ := fun q : P => F₀ q (a : ZMod (q : ℕ))
  let f := fun i q => F i q (a : ZMod (q : ℕ))
  have hfun (y : Fin (n + 1) → P) (i : Fin (n + 1)) :
      Fin.cons (α := fun _ => (q : P) → ZMod (q : ℕ) → ℂ) F₀ F i (y i) (a : ZMod (y i : ℕ)) = Fin.cons (α := fun _ => P → ℂ) f₀ f i (y i) := by
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  unfold halfPrimeMean
  simp_rw [hfun]
  rw [weighted_tuple_mean_cons μ₀ μ f₀ f (fun x => (w x : ℂ))]
  have hscalar : (∑ x : Fin n → P, (productPrior μ x : ℂ) * (w x : ℂ) * ∏ i, f i (x i)) =
      (halfPrimeScalar P μ w c : ℂ) := by
    dsimp only [f]
    simp_rw [hc]
    simp only [halfPrimeScalar, Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_prod]
  rw [hscalar, mul_comm]

/-- The balanced-event mass lower bound becomes the positive scalar used
in every endpoint mean, with both cutoff weights kept in the expectation. -/
theorem halfPrimeScalar_lower {n : ℕ} (P : Finset ℕ)
    (μ : Fin n → P → ℝ) (w : (Fin n → P) → ℝ) (c : Fin n → P → ℝ)
    (hμ : ∀ i p, 0 ≤ μ i p) (hw : ∀ x, 0 ≤ w x) (hc : ∀ i p, 0 ≤ c i p)
    (S : Finset (Fin n → P)) (β γ : ℝ) (hγ : 0 ≤ γ)
    (hmass : β ≤ ∑ x ∈ S, productPrior μ x * w x)
    (hgood : ∀ x ∈ S, ∀ i, γ ≤ c i (x i)) :
    β * γ ^ n ≤ halfPrimeScalar P μ w c := by
  have hpoint (x : Fin n → P) (hx : x ∈ S) : γ ^ n ≤ ∏ i, c i (x i) := by
    simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
      Finset.prod_le_prod (s := Finset.univ) (fun _ _ => hγ) (fun i _ => hgood x hx i)
  calc
    _ ≤ (∑ x ∈ S, productPrior μ x * w x) * γ ^ n :=
      mul_le_mul_of_nonneg_right hmass (pow_nonneg hγ n)
    _ = ∑ x ∈ S, productPrior μ x * w x * γ ^ n := Finset.sum_mul ..
    _ ≤ ∑ x ∈ S, productPrior μ x * w x * ∏ i, c i (x i) :=
      Finset.sum_le_sum (fun x hx => mul_le_mul_of_nonneg_left (hpoint x hx)
        (mul_nonneg (productPrior_nonneg μ hμ x) (hw x)))
    _ ≤ halfPrimeScalar P μ w c := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ S) (fun x _ _ => mul_nonneg
        (mul_nonneg (productPrior_nonneg μ hμ x) (hw x))
        (Finset.prod_nonneg (fun i _ => hc i (x i))))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SmoothGiantPrior
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact smooth harmonic giant prior from (7.3) -/

namespace Ostmann
open scoped Classical BigOperators

theorem smoothGiantPrior_nonneg (P : Finset ℕ) (φ : ℝ → ℝ) (G : ℝ)
    (hφ : ∀ x, 0 ≤ φ x) (p : P) : 0 ≤ smoothGiantPrior P φ G p :=
  div_nonneg (mul_nonneg (Real.exp_nonneg _) (hφ _)) (Nat.cast_nonneg _)

theorem smoothGiantPrior_mass (P : Finset ℕ) (φ : ℝ → ℝ) (G : ℝ)
    (hpos : 0 < smoothGiantMass P φ G) : ∑ p : P, smoothGiantPrior P φ G p = 1 := by
  have hs : (∑ p : P, φ (Real.log p - G) / (p : ℝ)) = smoothGiantMass P φ G := by
    simpa only [finite_univ_canonical, smoothGiantMass] using
      (Finset.sum_coe_sort P (fun p => φ (Real.log p - G) / (p : ℝ)))
  simp only [smoothGiantPrior, mul_div_assoc, ← Finset.mul_sum]
  rw [hs, smoothGiantLogNormalizer, Real.exp_neg, Real.exp_log hpos]
  exact inv_mul_cancel₀ hpos.ne'

/-- This is exactly `p μ_G(p) = exp(c_g) φ(log p - G)`, with the
normalizing constant computed from the finite original prime support. -/
theorem smoothGiantPrior_cancel_prime (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (φ : ℝ → ℝ) (G : ℝ) (p : P) :
    (p : ℝ) * smoothGiantPrior P φ G p =
      Real.exp (smoothGiantLogNormalizer P φ G) * φ (Real.log p - G) := by
  have hp : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (hP p p.property).ne_zero
  unfold smoothGiantPrior
  field_simp

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SmoothGiantSupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite support for the actual positive-integer giant extension -/

namespace Ostmann
open scoped Classical BigOperators

/-- No positive integer outside this range contributes to the extension.
The endpoints are retained in the finite set. -/
theorem smoothGiant_weight_zero_outside (φ : ℝ → ℝ) (G : ℝ)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0) (p : ℕ) (hp : 0 < p)
    (hpI : p ∉ smoothGiantIntegerRange G) : φ (Real.log p - G) = 0 := by
  have hceil : ⌈Real.exp (G + 1)⌉₊ < p := by
    have hn : ¬(1 ≤ p ∧ p ≤ ⌈Real.exp (G + 1)⌉₊) := by
      simpa only [smoothGiantIntegerRange, Finset.mem_Icc] using hpI
    omega
  have hexp : Real.exp (G + 1) < (p : ℝ) :=
    (Nat.le_ceil (Real.exp (G + 1))).trans_lt (by exact_mod_cast hceil)
  have hlog : G + 1 < Real.log p := by
    simpa only [Real.log_exp] using Real.log_lt_log (Real.exp_pos _) hexp
  exact hout _ (le_trans (by linarith) (le_abs_self _))

/-- The smooth normalizer has the exact finite support stipulated in (7.3). -/
theorem smoothGiant_prime_support (φ : ℝ → ℝ) (G : ℝ)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0) (p : ℕ) (hp : p.Prime)
    (hφp : φ (Real.log p - G) ≠ 0) : p ∈ smoothGiantPrimeRange G := by
  apply Finset.mem_filter.mpr
  refine ⟨?_, hp⟩
  by_contra hn
  exact hφp (smoothGiant_weight_zero_outside φ G hout p hp.pos hn)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialHalfListWeights
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The two independent cutoff weights in an initial half-list -/

namespace Ostmann
open scoped Classical BigOperators

theorem initialLogSumWeight_nonneg {A : Type*} {n : ℕ}
    (value : A → ℕ) (c : ℝ) (x : Fin n → A) :
    0 ≤ initialLogSumWeight value c x := logCellProfile_nonneg _

theorem initialLogSumWeight_le_one {A : Type*} {n : ℕ}
    (value : A → ℕ) (c : ℝ) (x : Fin n → A) :
    initialLogSumWeight value c x ≤ 1 := logCellProfile_le_one _

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

theorem tailSupport_subset (A : Set ℕ) (N p : ℕ) :
    tailSupport A N p ⊆ Finset.range p := by
  classical
  exact Finset.filter_subset _ _

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

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingProductPoissonCutoff
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual product-centered cutoff covers the initial Poisson window -/
namespace Ostmann
open Filter

theorem movingProductNaturalCutoff_zero (T : ℕ → ℝ) (W Y m : ℝ) :
    movingProductNaturalCutoff T W Y m 0 = naturalTransferCutoff (W - Y) m 0 := by
  simp only [movingProductNaturalCutoff, movingProductFrequencyExponent,
    movingProductExponent, naturalTransferCutoff, transferErrorScale,
    pow_zero, one_mul, mul_one, Real.sqrt_mul (show (0 : ℝ) ≤ 4 by norm_num)]
  norm_num

theorem eventual_moving_product_poisson_cutoff (H : ℝ) (hH : 0 ≤ H) :
    ∀ᶠ m : ℝ in atTop, ∀ (T : ℕ → ℝ) (W Y : ℝ), Y ≤ W →
      H * Real.exp (W - Y) ≤ movingProductNaturalCutoff T W Y m 0 := by
  filter_upwards [eventual_character_poisson_cutoff 0 H hH] with m hm T W Y hYW
  rw [movingProductNaturalCutoff_zero]
  simpa only [add_zero] using hm (W - Y) (sub_nonneg.mpr hYW)

theorem eventual_spectator_product_poisson_cutoff (k : ℕ) (hk : 0 < k)
    (H : ℝ) (hH : 0 ≤ H) :
    ∀ᶠ L : ℝ in atTop, ∀ (T : ℕ → ℝ) (W Y : ℝ), Y ≤ W →
      H * Real.exp (W - Y) ≤
        movingProductNaturalCutoff T W Y ((spectatorBulkCount k L : ℝ) / 4) 0 := by
  have ht : Tendsto (fun L : ℝ => (spectatorBulkCount k L : ℝ) / 4) atTop atTop :=
    (spectatorBulkCount_tendsto k hk).atTop_div_const (by norm_num)
  exact ht.eventually (eventual_moving_product_poisson_cutoff H hH)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingTargetTotal
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The backwards target construction preserves the original total log size -/

namespace Ostmann
open scoped BigOperators

theorem movingCompensationTargetError_ofFn (k : ℕ) (d : Fin k → ℝ) :
    movingCompensationTargetError (List.ofFn d) = ∑ i : Fin k, (2 : ℝ) ^ (i : ℕ) * d i := by
  induction k with
  | zero => simp [movingCompensationTargetError]
  | succ k ih =>
    rw [List.ofFn_succ, movingCompensationTargetError, ih, Fin.sum_univ_succ]
    simp only [Fin.val_zero, pow_zero, one_mul, Fin.val_succ, pow_succ]
    calc
      _ = d 0 + ∑ i : Fin k, 2 * (2 ^ (i : ℕ) * d i.succ) := by
        rw [← Finset.mul_sum]
        ring
      _ = _ := by
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        ring

theorem movingCompensationTargetError_gaps (k : ℕ) (BD Bz L : ℝ) :
    movingCompensationTargetError (movingCompensationGaps k BD Bz L) =
      ∑ i : Fin k, spectatorStepGap BD Bz ((k : ℝ) ^ 4) ((2 : ℝ) ^ (i : ℕ))
        (spectatorBulkCount k L) := by
  unfold movingCompensationGaps
  rw [movingCompensationTargetError_ofFn]
  apply Finset.sum_congr rfl
  intro i _
  have hr : (2 : ℝ) ^ (i : ℕ) ≠ 0 := by positivity
  field_simp

theorem moving_protected_and_compensation_total (k : ℕ) (BD Bz L logX G td Δ₀ : ℝ) :
    let gaps := movingCompensationGaps k BD Bz L
    let J := movingProtectedTarget k logX G td
      (Δ₀ + ∑ i : Fin k, spectatorStepGap BD Bz ((k : ℝ) ^ 4)
        ((2 : ℝ) ^ (i : ℕ)) (spectatorBulkCount k L))
    2 * G + 2 * td + J + (movingCompensationTargets J gaps).sum = logX + Δ₀ := by
  intro gaps J
  have hs := movingCompensationTargets_sum J gaps
  have hlen : gaps.length = k := movingCompensationGaps_length k BD Bz L
  rw [hlen, movingCompensationTargetError_gaps] at hs
  have hJ : (2 : ℝ) ^ k * J = logX - 2 * G - 2 * td +
      (Δ₀ + ∑ i : Fin k, spectatorStepGap BD Bz ((k : ℝ) ^ 4)
        ((2 : ℝ) ^ (i : ℕ)) (spectatorBulkCount k L)) := by
    dsimp [J, movingProtectedTarget]
    field_simp
  linarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_HalfPrimeEndpoint
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The common endpoint scalar in the Section 7 half-list -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap

theorem normalizedResidueIndicator_endpoint {p : ℕ} (S : Finset (ZMod p))
    (a : ZMod p) (ha : a ∈ S) :
    normalizedResidueIndicator S a = (endpointResidueValue S : ℂ) := by
  simp only [normalizedResidueIndicator, endpointResidueValue, centeredDensity,
    ite_eq_left ha, residueDensity]

theorem endpointResidueValue_nonneg {p : ℕ} [NeZero p] (S : Finset (ZMod p)) :
    0 ≤ endpointResidueValue S := by
  have hcard : S.card ≤ p := by simpa only [ZMod.card] using S.card_le_univ
  have hp : (0 : ℝ) < p := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne p))
  have hd : residueDensity S ≤ 1 := by
    rw [residueDensity, div_le_one hp]
    exact_mod_cast hcard
  exact div_nonneg (sub_nonneg.mpr hd) (Real.sqrt_nonneg _)

/-- A fixed absolute lower bound suffices for the exponential half-list loss. -/
theorem endpointResidueValue_balanced {p : ℕ} (S : Finset (ZMod p))
    (hlo : (1 / 3 : ℝ) ≤ residueDensity S) (hhi : residueDensity S ≤ 2 / 3) :
    (1 / 2 : ℝ) ≤ endpointResidueValue S := by
  have hv : 0 < residueVariance S := by
    unfold residueVariance
    nlinarith
  have hs : 0 < Real.sqrt (residueVariance S) := Real.sqrt_pos.mpr hv
  have hsq := Real.sq_sqrt hv.le
  have hbound : Real.sqrt (residueVariance S) ≤ 2 * (1 - residueDensity S) := by
    have hvar : residueVariance S ≤ (2 * (1 - residueDensity S)) ^ 2 := by
      unfold residueVariance
      nlinarith
    nlinarith [Real.sqrt_nonneg (residueVariance S)]
  rw [endpointResidueValue, le_div_iff₀ hs]
  linarith

theorem halfPrimeScalar_nonneg {n : ℕ} (P : Finset ℕ)
    (μ : Fin n → P → ℝ) (w : (Fin n → P) → ℝ) (c : Fin n → P → ℝ)
    (hμ : ∀ i p, 0 ≤ μ i p) (hw : ∀ x, 0 ≤ w x) (hc : ∀ i p, 0 ≤ c i p) :
    0 ≤ halfPrimeScalar P μ w c :=
  Finset.sum_nonneg (fun x _ => mul_nonneg
    (mul_nonneg (productPrior_nonneg μ hμ x) (hw x))
    (Finset.prod_nonneg (fun i _ => hc i (x i))))

/-- The endpoint mean of the actual giant, and the balanced weighted event for
the nongiant slots, give the doubled original-prior physical lower bound.
The cutoffs remain inside the half-list weight. -/
theorem halfPrimeMean_giant_endpoint_lower {n : ℕ}
    (P : Finset ℕ) [∀ q : P, NeZero (q : ℕ)]
    (μ₀ : P → ℝ) (μ : Fin n → P → ℝ)
    (F₀ : (q : P) → ZMod (q : ℕ) → ℂ)
    (F : Fin n → (q : P) → ZMod (q : ℕ) → ℂ)
    (w : (Fin n → P) → ℝ) (cval : Fin n → P → ℝ)
    (hμ : ∀ i q, 0 ≤ μ i q) (hw : ∀ x, 0 ≤ w x)
    (hcval : ∀ i q, 0 ≤ cval i q)
    (hF₀ : ∀ q a, (F₀ q a).im = 0) (hF : ∀ i q a, (F i q a).im = 0)
    (E : Finset ℤ) (S : Finset (Fin n → P)) (β γ δ c : ℝ)
    (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (hδ : 0 ≤ δ) (hc : 0 ≤ c)
    (hmass : β ≤ ∑ x ∈ S, productPrior μ x * w x)
    (hgood : ∀ x ∈ S, ∀ i, γ ≤ cval i (x i))
    (hendpoint : ∀ a ∈ E, ∀ i q, F i q (a : ZMod (q : ℕ)) = (cval i q : ℂ))
    (hmean : (E.card : ℝ) * δ ≤
      ∑ a ∈ E, (∑ q : P, (μ₀ q : ℂ) * F₀ q (a : ZMod (q : ℕ))).re)
    (ψ : 𝓢(ℝ, ℂ)) (X : ℝ) (hX : 0 < X)
    (hψ : ∀ x, 0 ≤ (ψ x).re) (hcE : ∀ a ∈ E, c ≤ (ψ ((a : ℝ) / X)).re) :
    let ν := Fin.cons μ₀ μ
    let H := Fin.cons F₀ F
    let W := fun y : Fin (n + 1) → P => (w (Fin.tail y) : ℂ)
    (E.card : ℝ) * (c * (β * γ ^ n * δ) ^ 2) ≤
      ‖∑ x : Fin ((n + 1) + (n + 1)) → P,
        (productPrior (Fin.append ν ν) x : ℂ) * doubledHalfWeight W x *
          physicalTupleSum P x (Fin.append H H) ψ X‖ := by
  dsimp only
  let κ := halfPrimeScalar P μ w cval
  have hk : 0 ≤ κ := halfPrimeScalar_nonneg P μ w cval hμ hw hcval
  have hkl : β * γ ^ n ≤ κ := halfPrimeScalar_lower P μ w cval hμ hw hcval
    S β γ hγ hmass hgood
  apply halfPrimeMean_endpoint_lower P (Fin.cons μ₀ μ) (Fin.cons F₀ F)
    (fun y => (w (Fin.tail y) : ℂ)) ψ X hX
    (fun a => halfPrimeMean_real P _ _ _
      (fun i q b => Fin.cases (hF₀ q b) (fun j => hF j q b) i)
      (fun _ => Complex.ofReal_im _) a)
    E c (β * γ ^ n * δ) hc (by positivity) hψ hcE
  have heq : (∑ a ∈ E, (halfPrimeMean P (Fin.cons μ₀ μ) (Fin.cons F₀ F)
      (fun y => (w (Fin.tail y) : ℂ)) a).re) =
      κ * ∑ a ∈ E, (∑ q : P, (μ₀ q : ℂ) * F₀ q (a : ZMod (q : ℕ))).re := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    rw [halfPrimeMean_cons_scalar P μ₀ μ F₀ F w cval a (hendpoint a ha)]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, κ]
  rw [heq]
  calc
    _ ≤ κ * ((E.card : ℝ) * δ) := by
      have h := mul_le_mul_of_nonneg_right hkl
        (mul_nonneg (Nat.cast_nonneg E.card) hδ)
      nlinarith
    _ ≤ _ := mul_le_mul_of_nonneg_left hmean hk

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_HalfPrimeInitialAmplitude
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The positive statistic for the actual phase/residue half-list -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap FourierTransform

theorem primeHalfTests_sum {n : ℕ} (P : Finset ℕ) [∀ q : P, NeZero (q : ℕ)]
    (S : (q : P) → Finset (ZMod (q : ℕ))) (favorable : P → Bool)
    (i : Fin (n + 1)) (q : P) : (∑ a, primeHalfTests P S favorable i q a) = 0 := by
  refine Fin.cases ?_ (fun j => ?_) i
  · exact primePhysicalTest_sum (S q) true (favorable q)
  · exact normalizedResidueIndicator_sum (S q)

theorem primeHalfTests_energy {n : ℕ} (P : Finset ℕ) [∀ q : P, NeZero (q : ℕ)]
    (S : (q : P) → Finset (ZMod (q : ℕ))) (favorable : P → Bool)
    (i : Fin (n + 1)) (q : P) : (∑ a, ‖primeHalfTests P S favorable i q a‖ ^ 2) ≤ q := by
  refine Fin.cases ?_ (fun j => ?_) i
  · exact primePhysicalTest_energy (S q) true (favorable q)
  · exact normalizedResidueIndicator_energy_le (S q)

/-- This is (7.5) before the asymptotic constants are absorbed: the only
mean premise is the selected actual giant mean, and the nongiant factors
are the manuscript's exact normalized residue indicators. -/
theorem primeHalfTests_statistic_lower {n : ℕ}
    (P : Finset ℕ) [∀ q : P, NeZero (q : ℕ)] (hP : ∀ q ∈ P, q.Prime)
    (S : (q : P) → Finset (ZMod (q : ℕ))) (favorable : P → Bool)
    (μ₀ : P → ℝ) (μ : Fin n → P → ℝ) (w : (Fin n → P) → ℝ)
    (hμ : ∀ i q, 0 ≤ μ i q) (hw : ∀ x, 0 ≤ w x)
    (E : Finset ℤ) (B : Finset (Fin n → P)) (β δ c : ℝ)
    (hβ : 0 ≤ β) (hδ : 0 ≤ δ) (hc : 0 ≤ c)
    (hmass : β ≤ ∑ x ∈ B, productPrior μ x * w x)
    (hbalance : ∀ x ∈ B, ∀ i, (1 / 3 : ℝ) ≤ residueDensity (S (x i)) ∧
      residueDensity (S (x i)) ≤ 2 / 3)
    (hendpoint : ∀ a ∈ E, ∀ q : P, (a : ZMod (q : ℕ)) ∈ S q)
    (hmean : (E.card : ℝ) * δ ≤ ∑ a ∈ E,
      (∑ q : P, (μ₀ q : ℂ) * primePhysicalTest (S q) true (favorable q)
        (a : ZMod (q : ℕ))).re)
    (ψ : 𝓢(ℝ, ℂ)) (X : ℝ) (hX : 0 < X)
    (hψ : ∀ x, 0 ≤ (ψ x).re) (hcE : ∀ a ∈ E, c ≤ (ψ ((a : ℝ) / X)).re) :
    let ν := Fin.cons μ₀ μ
    let F : Fin (n + 1) → (q : P) → ZMod (q : ℕ) → ℂ := primeHalfTests P S favorable
    let W := fun y : Fin (n + 1) → P => (w (Fin.tail y) : ℂ)
    (E.card : ℝ) * (c * (β * (1 / 2 : ℝ) ^ n * δ) ^ 2) ≤
      ‖∑ x : Fin ((n + 1) + (n + 1)) → P,
        (productPrior (Fin.append ν ν) x : ℂ) * doubledHalfWeight W x *
          physicalTupleSum P x (Fin.append F F) ψ X‖ := by
  let : ∀ q : P, Fact (q : ℕ).Prime := fun q => ⟨hP q q.property⟩
  exact halfPrimeMean_giant_endpoint_lower P μ₀ μ
    (fun q => primePhysicalTest (S q) true (favorable q))
    (fun _ q => normalizedResidueIndicator (S q)) w
    (fun _ q => endpointResidueValue (S q)) hμ hw
    (fun _ q => endpointResidueValue_nonneg (S q))
    (fun q a => primePhysicalTest_real (S q) true (favorable q) a)
    (fun _ _ _ => Complex.ofReal_im _) E B β (1 / 2) δ c hβ (by norm_num) hδ hc
    hmass (fun x hx i => endpointResidueValue_balanced (S (x i))
      (hbalance x hx i).1 (hbalance x hx i).2)
    (fun a ha _ q => normalizedResidueIndicator_endpoint (S q) _ (hendpoint a ha q))
    hmean ψ X hX hψ hcE

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_BalancedEndpointRate
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A depth-independent exponential rate for the actual endpoint statistic -/
namespace Ostmann
open Filter

/-- The number of top and compensation roles changes only the threshold.
The exponential coefficient remains independent of their number. -/
theorem eventual_balanced_endpoint_rate (r : ℕ) (a c δ A : ℝ)
    (ha : 0 < a) (hc : 0 < c) (hδ : 0 < δ) :
    ∀ᶠ m : ℕ in atTop, ∀ (L Y X E : ℝ) (n : ℕ),
      L ≤ m → 0 < Y → Y ≤ Real.exp L → 0 ≤ X → n ≤ m + r →
      a * Real.sqrt X / Y ^ 3 ≤ E →
      Real.sqrt X * Real.exp (-(2 * A + 2 * Real.log 2 + 4) * m) ≤
        E * (c * (Real.exp (-A * m) * (1 / 2 : ℝ) ^ n * δ) ^ 2) := by
  have hfixed : 0 < a * c * δ ^ 2 * Real.exp (-(2 * Real.log 2) * r) := by positivity
  have hf := (Real.tendsto_exp_neg_atTop_nhds_zero.comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_le_const hfixed
  filter_upwards [hf] with m hm L Y X E n hL hY hYL _hX hn hE
  change Real.exp (-(m : ℝ)) ≤ a * c * δ ^ 2 * Real.exp (-(2 * Real.log 2) * r) at hm
  have hn' : (n : ℝ) ≤ (m : ℝ) + r := by exact_mod_cast hn
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hYupper : Y ^ 3 ≤ Real.exp (3 * (m : ℝ)) := by
    calc
      _ ≤ (Real.exp L) ^ 3 := pow_le_pow_left₀ hY.le hYL 3
      _ = Real.exp (3 * L) := by rw [← Real.exp_nat_mul]; norm_num
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  have hYinv : Real.exp (-3 * (m : ℝ)) ≤ (Y ^ 3)⁻¹ := by
    have hi := inv_anti₀ (pow_pos hY 3) hYupper
    simpa only [Real.exp_neg, neg_mul] using hi
  have hElower : a * Real.sqrt X * Real.exp (-3 * (m : ℝ)) ≤ E := by
    apply le_trans _ hE
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left hYinv (by positivity)
  have hhalf : ((1 / 2 : ℝ) ^ n) ^ 2 = Real.exp (-(2 * Real.log 2) * n) := by
    have he : (1 / 2 : ℝ) = Real.exp (-Real.log 2) := by
      rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      norm_num
    rw [he, ← Real.exp_nat_mul, ← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hpow : (Real.exp (-A * (m : ℝ))) ^ 2 = Real.exp (-(2 * A) * m) := by
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num
    ring
  have hcoef : Real.exp (-(2 * A + 2 * Real.log 2 + 4) * (m : ℝ)) ≤
      a * c * δ ^ 2 * Real.exp (-3 * (m : ℝ)) * Real.exp (-(2 * A) * m) *
        Real.exp (-(2 * Real.log 2) * n) := by
    calc
      _ = Real.exp (-(m : ℝ)) * Real.exp (-(3 + 2 * A + 2 * Real.log 2) * m) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ (a * c * δ ^ 2 * Real.exp (-(2 * Real.log 2) * r)) *
          Real.exp (-(3 + 2 * A + 2 * Real.log 2) * m) :=
        mul_le_mul_of_nonneg_right hm (Real.exp_nonneg _)
      _ = a * c * δ ^ 2 * Real.exp (-3 * (m : ℝ)) * Real.exp (-(2 * A) * m) *
          Real.exp (-(2 * Real.log 2) * ((m : ℝ) + r)) := by
        simp only [mul_assoc, ← Real.exp_add]
        congr 2
        ring_nf
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (by nlinarith only [hn', hlog2])) (by positivity)
  calc
    _ ≤ Real.sqrt X * (a * c * δ ^ 2 * Real.exp (-3 * (m : ℝ)) *
        Real.exp (-(2 * A) * m) * Real.exp (-(2 * Real.log 2) * n)) :=
      mul_le_mul_of_nonneg_left hcoef (Real.sqrt_nonneg X)
    _ = (a * Real.sqrt X * Real.exp (-3 * (m : ℝ))) *
        (c * (Real.exp (-A * m) * (1 / 2 : ℝ) ^ n * δ) ^ 2) := by
      rw [mul_pow, mul_pow, hpow, hhalf]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hElower (by positivity)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_RepeatedTupleEntropy
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The broad-prime normalization cancels the repeated-tuple entropy -/
namespace Ostmann
open Filter

/-- There are two copies of the `m` broad positions and a fixed number of
cell roles. The `L^(-2m)` in their actual prior removes the `m log m` cost. -/
theorem eventual_repeated_tuple_entropy (r : ℕ) (z : ℝ) (hz : 0 < z) :
    ∀ᶠ m : ℕ in atTop, ∀ L : ℝ, 0 < L → (m : ℝ) ≤ z * L →
      ((2 * (m + r) : ℕ) : ℝ) ^ (2 * (m + r)) / L ^ (2 * m) ≤
        Real.exp ((2 * Real.log (4 * z) + 1) * m) := by
  have hpoly := eventual_polynomial_log_budget ((4 : ℝ) ^ (2 * r)) 1 1 1 (2 * r)
    (by positivity) (by norm_num) (by norm_num) (by norm_num)
  filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually hpoly,
    eventually_ge_atTop (max r 1)] with m hpoly hm L hL hmL
  have hm0 : 0 ≤ (m : ℝ) := Nat.cast_nonneg _
  have hmr : (r : ℝ) ≤ m := by exact_mod_cast (le_max_left r 1).trans hm
  have hn : ((2 * (m + r) : ℕ) : ℝ) ≤ 4 * m := by push_cast; linarith
  have hpow : (4 * (m : ℝ)) ^ (2 * r) ≤ Real.exp (m : ℝ) := by
    have hp := hpoly m hm0 (by simp)
    simp only [one_mul] at hp
    calc
      _ = (4 : ℝ) ^ (2 * r) * (m : ℝ) ^ (2 * r) := by rw [mul_pow]
      _ ≤ (4 : ℝ) ^ (2 * r) * (1 + (m : ℝ)) ^ (2 * r) := by gcongr; linarith
      _ ≤ _ := hp
  have hratio : 4 * (m : ℝ) / L ≤ 4 * z := by
    rw [div_le_iff₀ hL]
    nlinarith only [hmL]
  have hlog : 0 < 4 * z := by positivity
  calc
    _ ≤ (4 * (m : ℝ)) ^ (2 * (m + r)) / L ^ (2 * m) := by
      exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (by positivity) hn _) (by positivity)
    _ = (4 * (m : ℝ) / L) ^ (2 * m) * (4 * (m : ℝ)) ^ (2 * r) := by
      rw [show 2 * (m + r) = 2 * m + 2 * r by omega, pow_add, div_pow]
      ring
    _ ≤ (4 * z) ^ (2 * m) * Real.exp (m : ℝ) :=
      mul_le_mul (pow_le_pow_left₀ (by positivity) hratio _) hpow (by positivity) (by positivity)
    _ = Real.exp ((2 * Real.log (4 * z) + 1) * m) := by
      have he : (4 * z) ^ (2 * m) = Real.exp (((2 * m : ℕ) : ℝ) * Real.log (4 * z)) := by
        rw [Real.exp_nat_mul, Real.exp_log hlog]
      rw [he, ← Real.exp_add]
      congr 1
      push_cast
      ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialRepeatedErrorRate
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The initial gap absorbs the exact repeated-prime error -/
namespace Ostmann
open Filter

/-- The `L^(2m)` factor is precisely the contribution of the two copies of
all broad positions. Cell normalizers remain in the exponent `A*m`. -/
theorem eventual_initial_repeated_error (r : ℕ) (z K A B Bs B₀ : ℝ)
    (hz : 1 ≤ z) (hBs : 2 * (A + B + 2 * Real.log 4 + B₀ + 3) ≤ Bs) :
    ∀ᶠ m : ℕ in atTop, ∀ L C H Δ : ℝ,
      0 < L → (m : ℝ) ≤ z * L → 0 ≤ C →
      C * L ^ (2 * m) ≤ Real.exp (A * m) → H ≤ B * m →
      (Bs + 8 * Real.log z) * m ≤ Δ →
      K * C * ((2 * (m + r) : ℕ) : ℝ) ^ (2 * (m + r)) * Real.exp (H - Δ / 2) ≤
        Real.exp (-(B₀ + 1) * m) := by
  have hz0 : 0 < z := by linarith
  have hK := ((Real.tendsto_exp_atTop.comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).eventually (eventually_ge_atTop K))
  filter_upwards [eventual_repeated_tuple_entropy r z hz0, hK] with m hent hK L C H Δ
    hL hmL hC hnorm hH hΔ
  have hm0 : 0 ≤ (m : ℝ) := Nat.cast_nonneg _
  have hden : L ^ (2 * m) ≠ 0 := pow_ne_zero _ hL.ne'
  have hmass : C * ((2 * (m + r) : ℕ) : ℝ) ^ (2 * (m + r)) ≤
      Real.exp (A * m) * Real.exp ((2 * Real.log (4 * z) + 1) * m) := by
    calc
      _ = (C * L ^ (2 * m)) *
          (((2 * (m + r) : ℕ) : ℝ) ^ (2 * (m + r)) / L ^ (2 * m)) := by
        field_simp
      _ ≤ _ := mul_le_mul hnorm (hent L hL hmL) (by positivity) (Real.exp_nonneg _)
  have hgap : H - Δ / 2 ≤ (B - Bs / 2 - 4 * Real.log z) * m := by nlinarith
  have hlogz : 0 ≤ Real.log z := Real.log_nonneg hz
  have hlog4z : Real.log (4 * z) = Real.log 4 + Real.log z :=
    Real.log_mul (by norm_num) hz0.ne'
  calc
    _ = K * (C * ((2 * (m + r) : ℕ) : ℝ) ^ (2 * (m + r))) * Real.exp (H - Δ / 2) := by ring
    _ ≤ Real.exp (m : ℝ) * (Real.exp (A * m) *
          Real.exp ((2 * Real.log (4 * z) + 1) * m)) *
          Real.exp ((B - Bs / 2 - 4 * Real.log z) * m) := by
      apply mul_le_mul
      · exact mul_le_mul hK hmass (by positivity) (Real.exp_nonneg _)
      · exact Real.exp_le_exp.mpr hgap
      · exact Real.exp_nonneg _
      · positivity
    _ = Real.exp (((m : ℝ) + (A * m + (2 * Real.log (4 * z) + 1) * m)) +
        (B - Bs / 2 - 4 * Real.log z) * m) := by simp only [← Real.exp_add]
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      rw [hlog4z]
      have hh := mul_le_mul_of_nonneg_right hBs hm0
      have hl := mul_nonneg hlogz hm0
      nlinarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialAmplitudeErrorBudget
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual initial statistic pays for the repeated-prime error -/
namespace Ostmann
open Filter

theorem eventual_initial_amplitude_error_budget (r : ℕ)
    (z K A B Bs a c δ A₀ : ℝ)
    (hz : 1 ≤ z) (ha : 0 < a) (hc : 0 < c) (hδ : 0 < δ)
    (hBs : 2 * (A + B + 2 * Real.log 4 + (2 * A₀ + 2 * Real.log 2 + 4) + 3) ≤ Bs) :
    ∀ᶠ m : ℕ in atTop, ∀ (L Y X E C H Δ : ℝ) (n : ℕ),
      0 < L → L ≤ m → (m : ℝ) ≤ z * L →
      0 < Y → Y ≤ Real.exp L → 0 ≤ X → n ≤ m + r →
      a * Real.sqrt X / Y ^ 3 ≤ E →
      0 ≤ C → C * L ^ (2 * m) ≤ Real.exp (A * m) → H ≤ B * m →
      (Bs + 8 * Real.log z) * m ≤ Δ →
      Real.sqrt X * (Real.exp (-(2 * A₀ + 2 * Real.log 2 + 5) * m) +
        K * C * ((2 * (m + (r + 1)) : ℕ) : ℝ) ^ (2 * (m + (r + 1))) *
          Real.exp (H - Δ / 2)) ≤
        E * (c * (Real.exp (-A₀ * m) * (1 / 2 : ℝ) ^ n * δ) ^ 2) := by
  let Q := 2 * A₀ + 2 * Real.log 2 + 4
  have herr := eventual_initial_repeated_error (r + 1) z K A B Bs Q hz hBs
  have hend := eventual_balanced_endpoint_rate r a c δ A₀ ha hc hδ
  have htwo : ∀ᶠ m : ℕ in atTop, Real.log 2 ≤ (m : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually_ge_atTop _
  filter_upwards [herr, hend, htwo] with m herr hend htwo
    L Y X E C H Δ n hL hLm hmL hY hYL hX hn hE hC hnorm hH hgap
  have he := herr L C H Δ hL hmL hC hnorm hH hgap
  have hs := hend L Y X E n hLm hY hYL hX hn hE
  have hfactor : 2 * Real.exp (-(m : ℝ)) ≤ 1 := by
    calc
      _ ≤ 2 * Real.exp (-Real.log 2) := by gcongr
      _ = 1 := by rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]; norm_num
  have hsum : Real.exp (-(Q + 1) * m) + Real.exp (-(Q + 1) * m) ≤ Real.exp (-Q * m) := by
    calc
      _ = Real.exp (-Q * m) * (2 * Real.exp (-(m : ℝ))) := by
        rw [show -(Q + 1) * (m : ℝ) = -Q * m + -(m : ℝ) by ring, Real.exp_add]
        ring
      _ ≤ _ := by simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hfactor (Real.exp_nonneg (-Q * m))
  apply le_trans _ hs
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg X)
  have ht := (add_le_add_left he (Real.exp (-(Q + 1) * m))).trans hsum
  rw [show Q + 1 = 2 * A₀ + 2 * Real.log 2 + 5 by dsimp [Q]; ring] at ht
  dsimp only [Q] at ht
  linarith only [ht]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SelectedCellGap
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The selected actual cells discharge the diagonal's geometric gap -/

namespace Ostmann
open scoped Classical BigOperators

theorem tailCellLinearRate_nonneg (a C : ℝ) : 0 ≤ tailCellLinearRate a C := by
  unfold tailCellLinearRate
  positivity

theorem tailDefectBudget_linear (a C L X : ℝ) (hL : 1 ≤ L)
    (hX : 0 < X) (hXupper : X ≤ Real.exp L) :
    tailDefectBudget a C X ≤ tailCellLinearRate a C * L := by
  have hlog : Real.log X ≤ L := by
    have h := Real.log_le_log hX hXupper
    rwa [Real.log_exp] at h
  have hc := le_abs_self (4 * C + 4 * Real.log 2 + 2 * Real.log 4 / a)
  have hcl := mul_le_mul_of_nonneg_left hL
    (abs_nonneg (4 * C + 4 * Real.log 2 + 2 * Real.log 4 / a))
  unfold tailDefectBudget tailCellLinearRate
  nlinarith only [hlog, hc, hcl]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SelectedInitialTotal
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original initial log total for the selected actual cells -/
namespace Ostmann
open scoped BigOperators

theorem selected_compensation_centers_sum_bounds
    {A B : Set ℕ} {N hi : ℕ} {a C L Y : ℝ} {D : Finset ℕ}
    {centers : List ℕ} {targets : List ℝ}
    (h : List.Forall₂
      (fun j w => SelectedSmallTailCell A B N a C L Y hi D (w / 4) j) centers targets) :
    targets.sum ≤ 4 * (centers.map (fun j : ℕ => (j : ℝ))).sum ∧
      4 * (centers.map (fun j : ℕ => (j : ℝ))).sum ≤
        targets.sum + 4 * centers.length * (64 * tailDefectBudget a C Y + 1) := by
  induction h with
  | nil => simp
  | @cons j w js ws hj hrest ih =>
    have hlo := hj.1
    have hhi := hj.2.1
    simp only [List.sum_cons, List.map_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    constructor <;> nlinarith only [hlo, hhi, ih.1, ih.2]

theorem selected_initial_total_error
    {A B : Set ℕ} {N hi top : ℕ} {a C L Y G cb cd Δ₀ BD Bz : ℝ}
    {D : Finset ℕ} {centers : List ℕ} (k : ℕ)
    (htop : SelectedSmallTailCell A B N a C L Y hi D
      ((movingProtectedTarget k Y G cd
        (Δ₀ + ∑ i : Fin k, spectatorStepGap BD Bz ((k : ℝ) ^ 4)
          ((2 : ℝ) ^ (i : ℕ)) (spectatorBulkCount k L)) - 2 * cb) / 6) top)
    (hcenters : List.Forall₂
      (fun j w => SelectedSmallTailCell A B N a C L Y hi D (w / 4) j) centers
      (movingCompensationTargets
        (movingProtectedTarget k Y G cd
          (Δ₀ + ∑ i : Fin k, spectatorStepGap BD Bz ((k : ℝ) ^ 4)
            ((2 : ℝ) ^ (i : ℕ)) (spectatorBulkCount k L)))
        (movingCompensationGaps k BD Bz L))) :
    |2 * (G + cb + cd + 3 * top +
        2 * (centers.map (fun j : ℕ => (j : ℝ))).sum) - (Y + Δ₀)| ≤
      (6 + 4 * k) * (64 * tailDefectBudget a C Y + 1) := by
  let J := movingProtectedTarget k Y G cd
    (Δ₀ + ∑ i : Fin k, spectatorStepGap BD Bz ((k : ℝ) ^ 4)
      ((2 : ℝ) ^ (i : ℕ)) (spectatorBulkCount k L))
  have htotal := moving_protected_and_compensation_total k BD Bz L Y G cd Δ₀
  change 2 * G + 2 * cd + J +
    (movingCompensationTargets J (movingCompensationGaps k BD Bz L)).sum = Y + Δ₀ at htotal
  have hlen : centers.length = k := by
    have hh := hcenters.length_eq
    simpa only [movingCompensationTargets_length, movingCompensationGaps_length] using hh
  have hsum := selected_compensation_centers_sum_bounds hcenters
  rw [hlen] at hsum
  have hlo := htop.1
  have hhi := htop.2.1
  change (J - 2 * cb) / 6 ≤ (top : ℝ) at hlo
  change (top : ℝ) ≤ (J - 2 * cb) / 6 + 64 * tailDefectBudget a C Y + 1 at hhi
  change (movingCompensationTargets J (movingCompensationGaps k BD Bz L)).sum ≤ _ ∧ _ at hsum
  have hnonneg : 0 ≤ 2 * (G + cb + cd + 3 * top +
      2 * (centers.map (fun j : ℕ => (j : ℝ))).sum) - (Y + Δ₀) := by
    linarith only [hlo, hsum.1, htotal]
  rw [abs_of_nonneg hnonneg]
  nlinarith only [hhi, hsum.2, htotal]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialSmallCellList
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The three top labels and two labels of each compensation type -/
namespace Ostmann

theorem initialSmallCellList_length (top : ℕ) (centers : List ℕ) :
    (initialSmallCellList top centers).length = 3 + 2 * centers.length := by
  unfold initialSmallCellList
  induction centers with
  | nil => simp
  | cons j js ih => simp_all; omega

theorem initialSmallCellList_sum (top : ℕ) (centers : List ℕ) :
    ((initialSmallCellList top centers).map (fun j : ℕ => (j : ℝ))).sum =
      3 * (top : ℝ) + 2 * (centers.map (fun j : ℕ => (j : ℝ))).sum := by
  unfold initialSmallCellList
  induction centers with
  | nil => simp; ring
  | cons j js ih =>
    simp only [List.flatMap_cons, List.map_append, List.sum_append, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil] at ih ⊢
    linarith only [ih]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SelectedInitialCells
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Top and compensation cells for the actual initial cutoff centers -/
namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem SelectedSmallTailCell.prior_data
    {A B : Set ℕ} {N hi j : ℕ} {a C L Y target : ℝ} {D : Finset ℕ}
    (h : SelectedSmallTailCell A B N a C L Y hi D target j)
    (P : Finset ℕ) (hQP : selectedTailCellPrimes A B N Y hi D j ⊆ P) :
    let Q := selectedTailCellPrimes A B N Y hi D j
    (∑ p : P, primeSubsetPrior P Q p) = 1 ∧
    (∀ p : P, 0 ≤ primeSubsetPrior P Q p ∧
      (p : ℝ) * primeSubsetPrior P Q p ≤ Real.exp (2 * L)) ∧
    (∀ p : P, primeSubsetPrior P Q p ≠ 0 →
      (1 / 3 : ℝ) ≤ residueDensity (tailDensityMask A N p) ∧
        residueDensity (tailDensityMask A N p) ≤ 2 / 3) := by
  intro Q
  obtain ⟨_, _, _, _, hpos, hinv, hsupport⟩ := h
  refine ⟨primeSubsetPrior_mass P Q hQP hpos.ne', ?_, ?_⟩
  · intro p
    refine ⟨primeSubsetPrior_nonneg P Q p, ?_⟩
    by_cases hp : (p : ℕ) ∈ Q
    · have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (hsupport p hp).1.ne_zero
      calc
        _ ≤ (p : ℝ) * ((∑ q ∈ Q, (q : ℝ)⁻¹)⁻¹ * (p : ℝ)⁻¹) :=
          mul_le_mul_of_nonneg_left (primeSubsetPrior_atom P Q p) (Nat.cast_nonneg _)
        _ = (∑ q ∈ Q, (q : ℝ)⁻¹)⁻¹ := by field_simp
        _ ≤ _ := hinv
    · simp only [primeSubsetPrior, hp, ite_false, if_false, mul_zero]
      positivity
  · intro p hp
    have hs := hsupport p (primeSubsetPrior_support P Q p hp)
    exact (tailDensityMask_balanced_iff A N p hs.1.pos).mpr ⟨hs.2.2.2.1, hs.2.2.2.2⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialCellPriors
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The selected initial small cells on a common prime space -/
namespace Ostmann
open scoped Classical BigOperators

theorem mem_initialRegularPrimeRange (L : ℝ) (p : ℕ) (hp : p.Prime)
    (hbound : (p : ℝ) ≤ Real.exp (Real.exp ((11 / 1000 : ℝ) * L))) :
    p ∈ initialRegularPrimeRange L := Nat.mem_primesLE.mpr ⟨Nat.le_floor hbound, hp⟩

theorem SelectedSmallTailCell.subset_initialRegularPrimeRange
    {A B : Set ℕ} {N hi j : ℕ} {a C L Y target : ℝ} {D : Finset ℕ}
    (h : SelectedSmallTailCell A B N a C L Y hi D target j) :
    selectedTailCellPrimes A B N Y hi D j ⊆ initialRegularPrimeRange L := by
  intro p hp
  obtain ⟨_, _, hindex, _, _, _, hsupport⟩ := h
  have hs := hsupport p hp
  apply mem_initialRegularPrimeRange L p hs.1
  exact hs.2.2.1.trans (Real.exp_le_exp.mpr hindex)

theorem initialSmallCellList_property (top : ℕ) (centers : List ℕ) (P : ℕ → Prop)
    (htop : P top) (hcenters : ∀ j ∈ centers, P j) :
    ∀ j ∈ initialSmallCellList top centers, P j := by
  intro j hj
  simp only [initialSmallCellList, List.mem_append, List.mem_replicate, List.mem_flatMap] at hj
  rcases hj with ⟨_, rfl⟩ | ⟨w, hw, hjw⟩
  · exact htop
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hjw
    rcases hjw with rfl | rfl <;> exact hcenters _ hw

theorem initial_selected_cells_valid
    {A B : Set ℕ} {N hi top : ℕ} {a C L Y target : ℝ} {D : Finset ℕ}
    {centers : List ℕ} {targets : List ℝ}
    (htop : SelectedSmallTailCell A B N a C L Y hi D target top)
    (hcenters : List.Forall₂
      (fun j w => SelectedSmallTailCell A B N a C L Y hi D (w / 4) j) centers targets) :
    ∀ j ∈ initialSmallCellList top centers,
      ∃ t, SelectedSmallTailCell A B N a C L Y hi D t j := by
  refine initialSmallCellList_property top centers
    (fun j => ∃ t, SelectedSmallTailCell A B N a C L Y hi D t j) ⟨target, htop⟩ ?_
  induction hcenters with
  | nil => simp
  | @cons j w js ws hj hrest ih =>
    intro i hi
    rcases List.mem_cons.mp hi with rfl | hi
    · exact ⟨w / 4, hj⟩
    · exact ih i hi

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialCellRoundingBudget
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The initial cell rounding fits in the fixed gap reserve -/
namespace Ostmann

theorem initial_cell_rounding_budget (k : ℕ) (R D L : ℝ)
    (hk : 2 ≤ k) (hR : 0 ≤ R) (hL : 1 ≤ L) (hD : D ≤ R * L)
    (hlarge : 14 * (64 * R + 3) ≤ (k : ℝ) ^ 3)
    (hscale : 4 ≤ (k : ℝ) ^ 4 * L) :
    (6 + 4 * k) * (64 * D + 1) + 2 * ((3 + 2 * k : ℕ) + 3) ≤
      (spectatorBulkCount k L : ℝ) := by
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have hL0 : 0 ≤ L := by linarith
  have hcoef : (6 + 4 * (k : ℝ)) * (64 * R + 3) ≤ (k : ℝ) ^ 4 / 2 := by
    have hh := mul_le_mul_of_nonneg_left hlarge hk0
    nlinarith only [hh, hk2, hR]
  have herr : (6 + 4 * k) * (64 * D + 1) + 2 * ((3 + 2 * k : ℕ) + 3) ≤
      (6 + 4 * (k : ℝ)) * (64 * R + 3) * L := by
    push_cast
    nlinarith only [mul_le_mul_of_nonneg_left hD (show 0 ≤ 64 * (6 + 4 * (k : ℝ)) by positivity),
      mul_le_mul_of_nonneg_left hL (show 0 ≤ 18 + 12 * (k : ℝ) by positivity), hk0]
  apply herr.trans
  calc
    _ ≤ (k : ℝ) ^ 4 / 2 * L := mul_le_mul_of_nonneg_right hcoef hL0
    _ = (k : ℝ) ^ 4 * L / 2 := by ring
    _ ≤ _ := spectatorBulkCount_half k L hscale

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialLogSumScale
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The initial logarithmic cutoff centers lie below the giant scale -/

namespace Ostmann
open Filter

theorem initialLogSumWeight_support {A : Type*} {n : ℕ}
    (value : A → ℕ) (c : ℝ) (x : Fin n → A)
    (h : initialLogSumWeight value c x ≠ 0) :
    |(∑ i, Real.log (value (x i) : ℝ)) - c| < 1 := by
  by_contra hn
  exact h (logCellProfile_zero_outside _ (le_of_not_gt hn))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialCutoffProduct
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original two cutoff weights control the full sampled product -/
namespace Ostmann
open scoped Classical BigOperators

theorem initialHalfCutoffWeight_nonneg {P : Type*} (value : P → ℕ)
    (b d r : ℕ) (cb cd : ℝ) (x : Fin (b + (d + r)) → P) :
    0 ≤ initialHalfCutoffWeight value b d r cb cd x :=
  mul_nonneg (initialLogSumWeight_nonneg _ _ _) (initialLogSumWeight_nonneg _ _ _)

theorem initialHalfCutoffWeight_le_one {P : Type*} (value : P → ℕ)
    (b d r : ℕ) (cb cd : ℝ) (x : Fin (b + (d + r)) → P) :
    initialHalfCutoffWeight value b d r cb cd x ≤ 1 := by
  exact (mul_le_mul (initialLogSumWeight_le_one _ _ _) (initialLogSumWeight_le_one _ _ _)
    (initialLogSumWeight_nonneg _ _ _) zero_le_one).trans_eq (one_mul 1)

theorem initial_half_cutoff_log_product (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (b d r : ℕ) (μ₀ : P → ℝ) (μb : Fin b → P → ℝ)
    (μd : Fin d → P → ℝ) (μc : Fin r → P → ℝ) (G cb cd : ℝ) (center : Fin r → ℝ)
    (hG : ∀ q : P, μ₀ q ≠ 0 → |Real.log (q : ℝ) - G| ≤ 1)
    (hc : ∀ i (q : P), μc i q ≠ 0 → |Real.log (q : ℝ) - center i| ≤ 1)
    (x : Fin ((b + (d + r)) + 1) → P)
    (hprior : productPrior (Fin.cons μ₀ (Fin.append μb (Fin.append μd μc))) x ≠ 0)
    (hw : initialHalfCutoffWeight (fun q : P => (q : ℕ)) b d r cb cd (Fin.tail x) ≠ 0) :
    |Real.log (∏ i, (x i : ℝ)) - (G + cb + cd + ∑ i, center i)| ≤ r + 3 := by
  have hpriorAt (i : Fin ((b + (d + r)) + 1)) :
      (Fin.cons μ₀ (Fin.append μb (Fin.append μd μc)) : Fin ((b + (d + r)) + 1) → P → ℝ) i (x i) ≠ 0 :=
    (Finset.prod_ne_zero_iff.mp hprior) i (Finset.mem_univ i)
  have hgiant : |Real.log (x 0 : ℝ) - G| ≤ 1 :=
    hG _ (by simpa only [Fin.cons_zero] using hpriorAt 0)
  have hcell (i : Fin r) :
      |Real.log (Fin.tail x ((i.natAdd d).natAdd b) : ℝ) - center i| ≤ 1 := by
    apply hc
    simpa only [Fin.cons_succ, Fin.append_right, Fin.tail] using
      hpriorAt (((i.natAdd d).natAdd b).succ)
  have hcells : |(∑ i : Fin r, Real.log (Fin.tail x ((i.natAdd d).natAdd b) : ℝ)) -
      ∑ i, center i| ≤ r := by
    rw [← Finset.sum_sub_distrib]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
      using Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin r))) => hcell i)
  obtain ⟨hwb, hwd⟩ := mul_ne_zero_iff.mp hw
  have hb := (initialLogSumWeight_support (fun q : P => (q : ℕ)) cb _ hwb).le
  have hd := (initialLogSumWeight_support (fun q : P => (q : ℕ)) cd _ hwd).le
  rw [Real.log_prod (fun i _ => by exact_mod_cast (hP _ (x i).property).ne_zero)]
  rw [Fin.sum_univ_succ, Fin.sum_univ_add, Fin.sum_univ_add]
  obtain ⟨hglo, hghi⟩ := abs_le.mp hgiant
  obtain ⟨hblo, hbhi⟩ := abs_le.mp hb
  obtain ⟨hdlo, hdhi⟩ := abs_le.mp hd
  obtain ⟨hclo, hchi⟩ := abs_le.mp hcells
  dsimp only [Fin.tail] at hblo hbhi hdlo hdhi hclo hchi
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialDoubledCutoffProduct
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Product windows on both actual copies of the weighted initial list -/
namespace Ostmann
open scoped Classical BigOperators

theorem initial_doubled_cutoff_log_product (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (b d r : ℕ) (μ₀ : P → ℝ) (μb : Fin b → P → ℝ)
    (μd : Fin d → P → ℝ) (μc : Fin r → P → ℝ) (G cb cd : ℝ) (center : Fin r → ℝ)
    (hG : ∀ q : P, μ₀ q ≠ 0 → |Real.log (q : ℝ) - G| ≤ 1)
    (hc : ∀ i (q : P), μc i q ≠ 0 → |Real.log (q : ℝ) - center i| ≤ 1)
    (x : Fin (((b + (d + r)) + 1) + ((b + (d + r)) + 1)) → P)
    (hprior : productPrior (Fin.append
      (Fin.cons μ₀ (Fin.append μb (Fin.append μd μc)))
      (Fin.cons μ₀ (Fin.append μb (Fin.append μd μc)))) x ≠ 0)
    (hw : doubledHalfWeight (fun y : Fin ((b + (d + r)) + 1) → P =>
      (initialHalfCutoffWeight (fun q : P => (q : ℕ)) b d r cb cd (Fin.tail y) : ℂ)) x ≠ 0) :
    |Real.log (∏ i, (x i : ℝ)) - 2 * (G + cb + cd + ∑ i, center i)| ≤ 2 * (r + 3) := by
  let n := (b + (d + r)) + 1
  let xl : Fin n → P := fun i => x (i.castAdd n)
  let xr : Fin n → P := fun i => x (i.natAdd n)
  let ν : Fin n → P → ℝ := Fin.cons μ₀ (Fin.append μb (Fin.append μd μc))
  have hp : productPrior ν xl ≠ 0 ∧ productPrior ν xr ≠ 0 := by
    unfold productPrior at hprior ⊢
    rw [Fin.prod_univ_add] at hprior
    simpa only [Fin.append_left, Fin.append_right, ne_eq, mul_eq_zero, not_or] using hprior
  have hw' : (initialHalfCutoffWeight (fun q : P => (q : ℕ)) b d r cb cd (Fin.tail xl) : ℂ) ≠ 0 ∧
      (initialHalfCutoffWeight (fun q : P => (q : ℕ)) b d r cb cd (Fin.tail xr) : ℂ) ≠ 0 :=
    mul_ne_zero_iff.mp hw
  have hl := initial_half_cutoff_log_product P hP b d r μ₀ μb μd μc G cb cd center hG hc
    xl hp.1 (by exact_mod_cast hw'.1)
  have hr := initial_half_cutoff_log_product P hP b d r μ₀ μb μd μc G cb cd center hG hc
    xr hp.2 (by exact_mod_cast hw'.2)
  have hlog (y : Fin n → P) : Real.log (∏ i, (y i : ℝ)) = ∑ i, Real.log (y i : ℝ) :=
    Real.log_prod (fun i _ => by exact_mod_cast (hP _ (y i).property).ne_zero)
  rw [hlog xl] at hl
  rw [hlog xr] at hr
  rw [Real.log_prod (fun i _ => by exact_mod_cast (hP _ (x i).property).ne_zero), Fin.sum_univ_add]
  obtain ⟨hllo, hlhi⟩ := abs_le.mp hl
  obtain ⟨hrlo, hrhi⟩ := abs_le.mp hr
  dsimp only [xl, xr] at hllo hlhi hrlo hrhi
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialMixedNormalizer
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact normalization cost of the two original mixed half-lists -/
namespace Ostmann
open scoped Classical BigOperators

theorem initialHalfNormalizer_nonneg (b d r : ℕ) (a L g : ℝ)
    (ha : 0 ≤ a) (hL : 0 ≤ L) : ∀ i, 0 ≤ initialHalfNormalizer b d r a L g i := by
  intro i
  refine Fin.cases (Real.exp_nonneg _) (fun j => ?_) i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · simpa only [initialHalfNormalizer, Fin.cons_succ, Fin.append_left] using
      inv_nonneg.mpr (mul_nonneg ha hL)
  · refine Fin.addCases (fun t => ?_) (fun t => ?_) j
    · simpa only [initialHalfNormalizer, Fin.cons_succ, Fin.append_right, Fin.append_left] using
        inv_nonneg.mpr (mul_nonneg ha hL)
    · simpa only [initialHalfNormalizer, Fin.cons_succ, Fin.append_right] using
        Real.exp_nonneg (2 * L)

theorem initialHalfNormalizer_prime_bound (P : Finset ℕ) (b d r : ℕ) (a L g : ℝ)
    (μ₀ : P → ℝ) (μb : Fin b → P → ℝ) (μd : Fin d → P → ℝ) (μc : Fin r → P → ℝ)
    (h₀ : ∀ q : P, (q : ℝ) * μ₀ q ≤ Real.exp (g * L))
    (hb : ∀ i (q : P), (q : ℝ) * μb i q ≤ (a * L)⁻¹)
    (hd : ∀ i (q : P), (q : ℝ) * μd i q ≤ (a * L)⁻¹)
    (hc : ∀ i (q : P), (q : ℝ) * μc i q ≤ Real.exp (2 * L)) :
    ∀ i (q : P), (q : ℝ) *
      (Fin.cons μ₀ (Fin.append μb (Fin.append μd μc)) :
        Fin ((b + (d + r)) + 1) → P → ℝ) i q ≤ initialHalfNormalizer b d r a L g i := by
  intro i q
  refine Fin.cases (h₀ q) (fun j => ?_) i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · simpa only [initialHalfNormalizer, Fin.cons_succ, Fin.append_left] using hb j q
  · refine Fin.addCases (fun t => ?_) (fun t => ?_) j
    · simpa only [initialHalfNormalizer, Fin.cons_succ, Fin.append_right, Fin.append_left] using hd t q
    · simpa only [initialHalfNormalizer, Fin.cons_succ, Fin.append_right] using hc t q

theorem initialHalfNormalizer_prod (b d r : ℕ) (a L g : ℝ) :
    (∏ i, initialHalfNormalizer b d r a L g i) =
      Real.exp (g * L) * ((a * L)⁻¹) ^ (b + d) * (Real.exp (2 * L)) ^ r := by
  simp only [initialHalfNormalizer, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ,
    Fin.prod_univ_add, Fin.append_left, Fin.append_right, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, pow_add]
  ring

theorem initial_mixed_normalizer_identity (b d r : ℕ) (a L g : ℝ)
    (ha : 0 < a) (hL : 0 < L) :
    let C := initialHalfNormalizer b d r a L g
    (∏ i, Fin.append C C i) * (a * L) ^ (2 * (b + d)) =
      Real.exp ((2 * g + 4 * r) * L) := by
  intro C
  have hC : (∏ i, C i) = Real.exp (g * L) * ((a * L)⁻¹) ^ (b + d) *
      (Real.exp (2 * L)) ^ r := initialHalfNormalizer_prod b d r a L g
  have hcancel : ((a * L)⁻¹) ^ (b + d) * (a * L) ^ (b + d) = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ (mul_pos ha hL).ne', one_pow]
  have hhalf : (∏ i, C i) * (a * L) ^ (b + d) =
      Real.exp (g * L) * (Real.exp (2 * L)) ^ r := by
    rw [hC]
    calc
      _ = (Real.exp (g * L) * (Real.exp (2 * L)) ^ r) *
          (((a * L)⁻¹) ^ (b + d) * (a * L) ^ (b + d)) := by ring
      _ = _ := by rw [hcancel, mul_one]
  calc
    _ = ((∏ i, C i) * (a * L) ^ (b + d)) ^ 2 := by
      rw [Fin.prod_univ_add]
      simp only [Fin.append_left, Fin.append_right]
      rw [show 2 * (b + d) = (b + d) * 2 by omega, pow_mul]
      ring
    _ = (Real.exp (g * L) * (Real.exp (2 * L)) ^ r) ^ 2 := by rw [hhalf]
    _ = _ := by
      rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_nat_mul]
      congr 1
      push_cast
      ring

theorem initial_mixed_normalizer_bound (b d r : ℕ) (a L g : ℝ)
    (ha : 0 < a) (hL : 0 < L) (hcell : (2 * g + 4 * r) * L ≤ 4 * (b + d : ℕ)) :
    let C := initialHalfNormalizer b d r a L g
    (∏ i, Fin.append C C i) * L ^ (2 * (b + d)) ≤
      Real.exp ((4 - 2 * Real.log a) * (b + d : ℕ)) := by
  intro C
  have hid := initial_mixed_normalizer_identity b d r a L g ha hL
  have hpow : a ^ (2 * (b + d)) = Real.exp (((2 * (b + d) : ℕ) : ℝ) * Real.log a) := by
    rw [Real.exp_nat_mul, Real.exp_log ha]
  apply (mul_le_mul_iff_left₀ (pow_pos ha (2 * (b + d)))).mp
  calc
    _ = (∏ i, Fin.append C C i) * (a * L) ^ (2 * (b + d)) := by rw [mul_pow]; ring
    _ = Real.exp ((2 * g + 4 * r) * L) := hid
    _ ≤ Real.exp (4 * (b + d : ℕ)) := Real.exp_le_exp.mpr hcell
    _ = Real.exp ((4 - 2 * Real.log a) * (b + d : ℕ)) * a ^ (2 * (b + d)) := by
      rw [hpow, ← Real.exp_add]
      congr 1
      push_cast
      ring

theorem initial_cell_normalizer_budget (k : ℕ) (hk : 2 ≤ k) (L g : ℝ)
    (hL : 0 ≤ L) (hg : g ≤ 1) (hscale : 4 ≤ (k : ℝ) ^ 4 * L) :
    (2 * g + 4 * (3 + 2 * k : ℕ)) * L ≤ 4 * (spectatorBulkCount k L : ℝ) := by
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hk3 : (8 : ℝ) ≤ (k : ℝ) ^ 3 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hk2 3
    norm_num at hh
    exact hh
  have hk4 : 8 * (k : ℝ) ≤ (k : ℝ) ^ 4 := by
    nlinarith [mul_le_mul_of_nonneg_right hk3 (show 0 ≤ (k : ℝ) by positivity)]
  have hcoef : 2 * g + 4 * (3 + 2 * k : ℕ) ≤ 2 * (k : ℝ) ^ 4 := by
    push_cast
    nlinarith
  have hprod := mul_le_mul_of_nonneg_right hcoef hL
  have hm := spectatorBulkCount_half k L hscale
  linarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialPrimeWindow
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Every live initial prime exceeds the Poisson product ratio -/
namespace Ostmann
open Filter

theorem eventual_linear_product_prime_window (H C z α : ℝ) (hC : 0 ≤ C) (hα : 0 < α) :
    ∀ᶠ L : ℝ in atTop, ∀ m : ℕ, (m : ℝ) ≤ z * L →
      ∀ D : ℝ, D ≤ C * m → ∀ p : ℕ,
        Real.exp (Real.exp (α * L)) ≤ (p : ℝ) → H * Real.exp D < (p : ℝ) := by
  have hlinear := ((isLittleO_pow_exp_pos_mul_atTop 1 hα).const_mul_left (C * z)).bound
    (show (0 : ℝ) < 1 / 4 by norm_num)
  have hconstant := (Real.tendsto_exp_atTop.comp
    (tendsto_id.const_mul_atTop hα)).eventually (eventually_ge_atTop (4 * H))
  filter_upwards [hlinear, hconstant] with L hlinear hconstant m hm D hD p hp
  simp only [Function.comp_apply, id_eq] at hconstant
  have hl : C * z * L ≤ (1 / 4 : ℝ) * Real.exp (α * L) := by
    apply (le_abs_self _).trans
    simpa only [Real.norm_eq_abs, pow_one, abs_of_pos (Real.exp_pos _)] using hlinear
  have hd : D ≤ C * z * L := by
    have hh := mul_le_mul_of_nonneg_left hm hC
    linarith
  calc
    H * Real.exp D ≤ Real.exp H * Real.exp D :=
      mul_le_mul_of_nonneg_right (by linarith [Real.add_one_le_exp H]) (Real.exp_nonneg _)
    _ = Real.exp (H + D) := (Real.exp_add _ _).symm
    _ < Real.exp (Real.exp (α * L)) := Real.exp_lt_exp.mpr (by
      nlinarith only [hl, hd, hconstant, Real.exp_pos (α * L)])
    _ ≤ _ := hp

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialSampledProductWindow
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The retained logarithmic window gives both Poisson cutoffs -/
namespace Ostmann
open scoped BigOperators

theorem sampled_product_window_of_log_error {I : Type*} [Fintype I]
    (v : I → ℕ) (hv : ∀ i, v i ≠ 0) (X Δ E : ℝ) (hX : 0 < X)
    (hlog : |Real.log (∏ i, (v i : ℝ)) - (Real.log X + Δ)| ≤ E) :
    X * Real.exp (Δ - E) ≤ ∏ i, (v i : ℝ) ∧
      (∏ i, (v i : ℝ)) ≤ X * Real.exp (Δ + E) := by
  have hp : 0 < ∏ i, (v i : ℝ) := Finset.prod_pos (fun i _ => by
    exact_mod_cast Nat.pos_of_ne_zero (hv i))
  obtain ⟨hl, hu⟩ := abs_le.mp hlog
  constructor
  · calc
      _ = Real.exp (Real.log X + (Δ - E)) := by rw [Real.exp_add, Real.exp_log hX]
      _ ≤ Real.exp (Real.log (∏ i, (v i : ℝ))) := Real.exp_le_exp.mpr (by linarith)
      _ = _ := Real.exp_log hp
  · calc
      _ = Real.exp (Real.log (∏ i, (v i : ℝ))) := (Real.exp_log hp).symm
      _ ≤ Real.exp (Real.log X + (Δ + E)) := Real.exp_le_exp.mpr (by linarith)
      _ = _ := by rw [Real.exp_add, Real.exp_log hX]

theorem sampled_product_poisson_cutoff {I : Type*} [Fintype I]
    (v : I → ℕ) (X H R : ℝ) (N : ℕ) (hX : 0 ≤ X) (hH : 0 ≤ H)
    (hupper : (∏ i, (v i : ℝ)) ≤ X * R) (hN : H * R ≤ N) :
    H * (∏ i, v i) ≤ N * X := by
  have hp : ((∏ i, v i : ℕ) : ℝ) = ∏ i, (v i : ℝ) := by push_cast; rfl
  rw [hp]
  calc
    _ ≤ H * (X * R) := mul_le_mul_of_nonneg_left hupper hH
    _ = (H * R) * X := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hN hX

/-- The cutoff weights restrict the sampled product without changing any
marginal prior. The only extra loss is the already bounded cell rounding. -/
theorem initial_doubled_product_window (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (b d r : ℕ) (μ₀ : P → ℝ) (μb : Fin b → P → ℝ)
    (μd : Fin d → P → ℝ) (μc : Fin r → P → ℝ) (G cb cd : ℝ) (center : Fin r → ℝ)
    (hG : ∀ q : P, μ₀ q ≠ 0 → |Real.log (q : ℝ) - G| ≤ 1)
    (hc : ∀ i (q : P), μc i q ≠ 0 → |Real.log (q : ℝ) - center i| ≤ 1)
    (X Δ E : ℝ) (hX : 0 < X)
    (htarget : |2 * (G + cb + cd + ∑ i, center i) - (Real.log X + Δ)| ≤ E)
    (x : Fin (((b + (d + r)) + 1) + ((b + (d + r)) + 1)) → P)
    (hprior : productPrior (Fin.append
      (Fin.cons μ₀ (Fin.append μb (Fin.append μd μc)))
      (Fin.cons μ₀ (Fin.append μb (Fin.append μd μc)))) x ≠ 0)
    (hw : doubledHalfWeight (fun y : Fin ((b + (d + r)) + 1) → P =>
      (initialHalfCutoffWeight (fun q : P => (q : ℕ)) b d r cb cd (Fin.tail y) : ℂ)) x ≠ 0) :
    X * Real.exp (Δ - (E + 2 * (r + 3))) ≤ ∏ i, (x i : ℝ) ∧
      (∏ i, (x i : ℝ)) ≤ X * Real.exp (Δ + (E + 2 * (r + 3))) := by
  have hlog := initial_doubled_cutoff_log_product P hP b d r μ₀ μb μd μc
    G cb cd center hG hc x hprior hw
  apply sampled_product_window_of_log_error (fun i => (x i : ℕ))
    (fun i => (hP _ (x i).property).ne_zero) X Δ (E + 2 * (r + 3)) hX
  exact (abs_sub_le _ _ _).trans (by linarith only [add_le_add hlog htarget])

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SmoothGiantAmbientPrior
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The full smooth giant law inside an ambient prime set -/
namespace Ostmann
open scoped Classical BigOperators

theorem smoothGiantMass_ambient (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (φ : ℝ → ℝ) (G : ℝ) (hout : ∀ x, 1 ≤ |x| → φ x = 0)
    (hsub : smoothGiantPrimeRange G ⊆ P) :
    smoothGiantMass P φ G = smoothGiantMass (smoothGiantPrimeRange G) φ G := by
  symm
  apply Finset.sum_subset hsub
  intro p hp hn
  have hz : φ (Real.log p - G) = 0 := by
    by_contra hne
    exact hn (smoothGiant_prime_support φ G hout p (hP p hp) hne)
  simp only [hz, zero_div]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SelectedInitialPriorBounds
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Probability and point-mass bounds for the selected original half-list -/
namespace Ostmann
open scoped Classical BigOperators

theorem selected_initial_prior_bounds
    {A B : Set ℕ} {N hi top : ℕ} {a C L Y G target g a₀ : ℝ}
    {D Qb Qd : Finset ℕ} {centers : List ℕ} {targets : List ℝ}
    (htop : SelectedSmallTailCell A B N a C L Y hi D target top)
    (hcenters : List.Forall₂
      (fun j w => SelectedSmallTailCell A B N a C L Y hi D (w / 4) j) centers targets)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hsmall : initialRegularPrimeRange L ⊆ P) (hgiant : smoothGiantPrimeRange G ⊆ P)
    (hmass : 0 < smoothGiantMass (smoothGiantPrimeRange G) logCellProfile G)
    (hnorm : smoothGiantLogNormalizer (smoothGiantPrimeRange G) logCellProfile G ≤ g * L)
    (hbmass : ∑ p : P, primeSubsetPrior P Qb p = 1)
    (hdmass : ∑ p : P, primeSubsetPrior P Qd p = 1)
    (hpoint : ∀ p : P, (p : ℝ) * primeSubsetPrior P Qb p ≤ (a₀ * L)⁻¹ ∧
      (p : ℝ) * primeSubsetPrior P Qd p ≤ (a₀ * L)⁻¹)
    (b d : ℕ) :
    let ν := selectedInitialHalfPrior P A B N hi Y G D Qb Qd b d top centers
    (∀ i p, 0 ≤ ν i p) ∧ (∀ i, ∑ p : P, ν i p = 1) ∧
    (∀ i (p : P), (p : ℝ) * ν i p ≤
      initialHalfNormalizer b d (initialSmallCellList top centers).length a₀ L g i) := by
  intro ν
  have hc (i : Fin (initialSmallCellList top centers).length) :=
    initial_selected_cells_valid htop hcenters _
      (List.get_mem (initialSmallCellList top centers) i)
  have hdata (i : Fin (initialSmallCellList top centers).length) :=
    (hc i).choose_spec.prior_data P
      ((hc i).choose_spec.subset_initialRegularPrimeRange.trans hsmall)
  have he := smoothGiantMass_ambient P hP logCellProfile G logCellProfile_zero_outside hgiant
  have hgmass : ∑ p : P, smoothGiantPrior P logCellProfile G p = 1 :=
    smoothGiantPrior_mass P logCellProfile G (he.symm ▸ hmass)
  have hgnorm : smoothGiantLogNormalizer P logCellProfile G ≤ g * L := by
    simpa only [smoothGiantLogNormalizer, he] using hnorm
  refine ⟨?_, ?_, ?_⟩
  · intro i p
    refine Fin.cases (smoothGiantPrior_nonneg P logCellProfile G logCellProfile_nonneg p)
      (fun j => ?_) i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · simpa only [ν, selectedInitialHalfPrior, Fin.cons_succ, Fin.append_left] using
        primeSubsetPrior_nonneg P Qb p
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · simpa only [ν, selectedInitialHalfPrior, Fin.cons_succ, Fin.append_right,
          Fin.append_left] using primeSubsetPrior_nonneg P Qd p
      · simpa only [ν, selectedInitialHalfPrior, Fin.cons_succ, Fin.append_right] using
          ((hdata j).2.1 p).1
  · intro i
    refine Fin.cases hgmass (fun j => ?_) i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · simpa only [ν, selectedInitialHalfPrior, Fin.cons_succ, Fin.append_left] using hbmass
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · simpa only [ν, selectedInitialHalfPrior, Fin.cons_succ, Fin.append_right,
          Fin.append_left] using hdmass
      · simpa only [ν, selectedInitialHalfPrior, Fin.cons_succ, Fin.append_right] using
          (hdata j).1
  · apply initialHalfNormalizer_prime_bound
    · intro p
      rw [smoothGiantPrior_cancel_prime P hP]
      exact (mul_le_of_le_one_right (Real.exp_nonneg _) (logCellProfile_le_one _)).trans
        (Real.exp_le_exp.mpr hgnorm)
    · intro _ p
      exact (hpoint p).1
    · intro _ p
      exact (hpoint p).2
    · intro i p
      exact (hdata i).2.1 p |>.2

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SmoothGiantActiveSupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Size and separation on the support of the smooth giant law -/

namespace Ostmann

theorem smoothGiantPrior_active_bounds (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (φ : ℝ → ℝ) (G : ℝ) (hout : ∀ x, 1 ≤ |x| → φ x = 0)
    (p : P) (hp : smoothGiantPrior P φ G p ≠ 0) :
    Real.exp (G - 1) < (p : ℝ) ∧ (p : ℝ) < Real.exp (G + 1) := by
  have hφ : φ (Real.log (p : ℕ) - G) ≠ 0 := by
    intro h
    apply hp
    simp only [smoothGiantPrior, h, mul_zero, zero_div]
  have habs : |Real.log (p : ℕ) - G| < 1 := lt_of_not_ge (fun h => hφ (hout _ h))
  have hpos : (0 : ℝ) < (p : ℕ) := by exact_mod_cast (hP _ p.property).pos
  constructor
  · apply (Real.exp_lt_exp.mpr (show G - 1 < Real.log (p : ℕ) by linarith [(abs_lt.mp habs).1])).trans_eq
    exact Real.exp_log hpos
  · rw [← Real.exp_log hpos]
    exact Real.exp_lt_exp.mpr (by linarith [(abs_lt.mp habs).2])

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SelectedInitialProductWindow
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact product center of the original selected mixed prior -/
namespace Ostmann
open scoped Classical BigOperators

theorem selected_initial_center_bounds
    {A B : Set ℕ} {N hi top : ℕ} {a C L Y G cb cd Bs BD Bz : ℝ}
    {D : Finset ℕ} {centers : List ℕ} (k : ℕ)
    (htop : SelectedSmallTailCell A B N a C L Y hi D
      ((movingProtectedTarget k Y G cd (movingInitialGapTotal k Bs BD Bz L) - 2 * cb) / 6) top)
    (hcenters : List.Forall₂ (fun j w => SelectedSmallTailCell A B N a C L Y hi D (w / 4) j)
      centers (movingCompensationTargets
        (movingProtectedTarget k Y G cd (movingInitialGapTotal k Bs BD Bz L))
        (movingCompensationGaps k BD Bz L))) :
    let Δ := spectatorBaseGap Bs ((k : ℝ) ^ 4) (spectatorBulkCount k L)
    Δ ≤ selectedInitialLogCenter G Y cb cd top centers ∧
      selectedInitialLogCenter G Y cb cd top centers ≤
        Δ + (6 + 4 * k) * (64 * tailDefectBudget a C Y + 1) := by
  intro Δ
  have herror := selected_initial_total_error k htop hcenters
  have hsum := selected_compensation_centers_sum_bounds hcenters
  have htotal := moving_protected_and_compensation_total k BD Bz L Y G cd Δ
  have ht := htop.1
  change (movingProtectedTarget k Y G cd (movingInitialGapTotal k Bs BD Bz L) - 2 * cb) / 6 ≤
    (top : ℝ) at ht
  change 2 * G + 2 * cd + movingProtectedTarget k Y G cd (movingInitialGapTotal k Bs BD Bz L) +
    (movingCompensationTargets (movingProtectedTarget k Y G cd (movingInitialGapTotal k Bs BD Bz L))
      (movingCompensationGaps k BD Bz L)).sum = Y + Δ at htotal
  constructor
  · dsimp only [selectedInitialLogCenter]
    linarith only [ht, hsum.1, htotal]
  · have hh := (abs_le.mp herror).2
    dsimp only [selectedInitialLogCenter]
    linarith only [hh]

theorem selectedInitialCellCenter_sum (top : ℕ) (centers : List ℕ) :
    (∑ i : Fin (initialSmallCellList top centers).length,
      ((initialSmallCellList top centers).get i : ℝ)) =
        3 * top + 2 * (centers.map (fun j : ℕ => (j : ℝ))).sum := by
  rw [← List.sum_ofFn]
  have he : (List.ofFn (fun i : Fin (initialSmallCellList top centers).length =>
      ((initialSmallCellList top centers).get i : ℝ))) =
      (initialSmallCellList top centers).map (fun j : ℕ => (j : ℝ)) := by
    change List.ofFn ((fun j : ℕ => (j : ℝ)) ∘ (initialSmallCellList top centers).get) = _
    rw [← List.map_ofFn, List.ofFn_get]
  rw [he]
  exact initialSmallCellList_sum top centers

/-- The narrow window is centered at the actual selected total. Its width
depends only on the number of fixed cell roles, including the giant. -/
theorem selected_initial_product_window
    {A B : Set ℕ} {N endpoint top : ℕ} {a C L Y G cb cd target : ℝ}
    {D : Finset ℕ} {centers : List ℕ} {targets : List ℝ}
    (htop : SelectedSmallTailCell A B N a C L Y endpoint D target top)
    (hcenters : List.Forall₂
      (fun j w => SelectedSmallTailCell A B N a C L Y endpoint D (w / 4) j) centers targets)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (b d : ℕ)
    (μb : Fin b → P → ℝ) (μd : Fin d → P → ℝ) :
    let cells := initialSmallCellList top centers
    let μc := fun i : Fin cells.length => primeSubsetPrior P
      (selectedTailCellPrimes A B N Y endpoint D (cells.get i))
    let ν := Fin.cons (smoothGiantPrior P logCellProfile G)
      (Fin.append μb (Fin.append μd μc))
    let Δ := selectedInitialLogCenter G Y cb cd top centers
    ∀ x : Fin (((b + (d + cells.length)) + 1) + ((b + (d + cells.length)) + 1)) → P,
      productPrior (Fin.append ν ν) x ≠ 0 →
      doubledHalfWeight (fun y : Fin ((b + (d + cells.length)) + 1) → P =>
        (initialHalfCutoffWeight (fun q : P => (q : ℕ)) b d cells.length cb cd (Fin.tail y) : ℂ)) x ≠ 0 →
      Real.exp Y * Real.exp (Δ - 2 * (cells.length + 3)) ≤ ∏ i, (x i : ℝ) ∧
        (∏ i, (x i : ℝ)) ≤ Real.exp Y * Real.exp (Δ + 2 * (cells.length + 3)) := by
  intro cells μc ν Δ x hprior hw
  have hgiant (p : P) (hp : smoothGiantPrior P logCellProfile G p ≠ 0) :
      |Real.log (p : ℝ) - G| ≤ 1 := by
    have hh := smoothGiantPrior_active_bounds P hP logCellProfile G logCellProfile_zero_outside p hp
    have hp0 : 0 < (p : ℝ) := by exact_mod_cast (hP p p.property).pos
    have hlo := (Real.lt_log_iff_exp_lt hp0).mpr hh.1
    have hhi := (Real.log_lt_iff_lt_exp hp0).mpr hh.2
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hcell (i : Fin cells.length) (p : P) (hp : μc i p ≠ 0) :
      |Real.log (p : ℝ) - (cells.get i : ℝ)| ≤ 1 := by
    have hmem := primeSubsetPrior_support P _ p hp
    obtain ⟨t, ht⟩ := initial_selected_cells_valid htop hcenters _ (List.get_mem cells i)
    obtain ⟨_, _, _, _, _, _, hsupport⟩ := ht
    have hs := hsupport p hmem
    have hp0 : 0 < (p : ℝ) := by exact_mod_cast hs.1.pos
    have hlo := (Real.lt_log_iff_exp_lt hp0).mpr hs.2.1
    have hhi := (Real.log_le_iff_le_exp hp0).mpr hs.2.2.1
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have htarget : |2 * (G + cb + cd + ∑ i : Fin cells.length, (cells.get i : ℝ)) -
      (Real.log (Real.exp Y) + Δ)| ≤ 0 := by
    rw [Real.log_exp]
    change |2 * (G + cb + cd + ∑ i : Fin (initialSmallCellList top centers).length,
      ((initialSmallCellList top centers).get i : ℝ)) -
        (Y + selectedInitialLogCenter G Y cb cd top centers)| ≤ 0
    rw [selectedInitialCellCenter_sum]
    simp only [selectedInitialLogCenter]
    ring_nf
    simp
  simpa only [zero_add] using initial_doubled_product_window P hP b d cells.length
    (smoothGiantPrior P logCellProfile G) μb μd μc G cb cd (fun i => (cells.get i : ℝ))
    hgiant hcell (Real.exp Y) Δ 0 (Real.exp_pos _) htarget x hprior hw

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SelectedInitialWindowRate
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The selected product center fits the original one-unit gap reserve -/
namespace Ostmann

theorem selected_initial_window_rate
    {A B : Set ℕ} {N hi top : ℕ} {a C L Y G cb cd Bs BD Bz R : ℝ}
    {D : Finset ℕ} {centers : List ℕ} (k : ℕ) (hk : 2 ≤ k)
    (hL : 1 ≤ L) (hR : 0 ≤ R) (hD : tailDefectBudget a C Y ≤ R * L)
    (hlarge : 14 * (64 * R + 3) ≤ (k : ℝ) ^ 3)
    (hscale : 4 ≤ (k : ℝ) ^ 4 * L)
    (htop : SelectedSmallTailCell A B N a C L Y hi D
      ((movingProtectedTarget k Y G cd (movingInitialGapTotal k Bs BD Bz L) - 2 * cb) / 6) top)
    (hcenters : List.Forall₂ (fun j w => SelectedSmallTailCell A B N a C L Y hi D (w / 4) j)
      centers (movingCompensationTargets
        (movingProtectedTarget k Y G cd (movingInitialGapTotal k Bs BD Bz L))
        (movingCompensationGaps k BD Bz L))) (hlen : centers.length = k) :
    let m := spectatorBulkCount k L
    let Δ := selectedInitialLogCenter G Y cb cd top centers
    let W : ℝ := 2 * ((initialSmallCellList top centers).length + 3)
    (Bs - 1 + 8 * Real.log ((k : ℝ) ^ 4)) * m ≤ Δ - W ∧
      Δ + W ≤ (Bs + 1 + 8 * Real.log ((k : ℝ) ^ 4)) * m := by
  intro m Δ W
  have hbound := selected_initial_center_bounds k htop hcenters
  have hround := initial_cell_rounding_budget k R (tailDefectBudget a C Y) L
    hk hR hL hD hlarge hscale
  have hW : W = 2 * (((3 + 2 * k : ℕ) : ℝ) + 3) := by
    dsimp only [W]
    rw [initialSmallCellList_length, hlen]
  rw [← hW] at hround
  dsimp only [spectatorBaseGap] at hbound
  constructor <;> dsimp only [Δ, m] at * <;> linarith only [hbound.1, hbound.2, hround]

theorem selected_initial_normalizer_rate (k : ℕ) (hk : 2 ≤ k) (L : ℝ)
    (hL : 0 < L) (hscale : 4 ≤ (k : ℝ) ^ 4 * L)
    (top : ℕ) (centers : List ℕ) (hlen : centers.length = k) :
    let m := spectatorBulkCount k L
    let C := initialHalfNormalizer (m / 2) (m / 2)
      (initialSmallCellList top centers).length (1 / 320000) L (91 / 100)
    (∏ i, Fin.append C C i) * L ^ (2 * m) ≤
      Real.exp ((4 - 2 * Real.log (1 / 320000)) * m) := by
  intro m C
  have heven : m / 2 + m / 2 = m := by
    obtain ⟨t, ht⟩ := spectatorBulkCount_even k L
    dsimp only [m]
    omega
  have hcell := initial_cell_normalizer_budget k hk L (91 / 100) hL.le (by norm_num) hscale
  have hlen' : (initialSmallCellList top centers).length = 3 + 2 * k := by
    rw [initialSmallCellList_length, hlen]
  have hh := initial_mixed_normalizer_bound (m / 2) (m / 2)
    (initialSmallCellList top centers).length (1 / 320000) L (91 / 100)
    (by norm_num) hL (by simpa only [hlen', heven] using hcell)
  simpa only [heven] using hh

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SupportedRegularInitialAmplitude
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Initial Poisson bounds on the actual support of the original prior -/
namespace Ostmann
open scoped Classical BigOperators SchwartzMap FourierTransform

theorem priorSupportedWeight_support {A : Type*} {n : ℕ}
    (μ : Fin n → A → ℝ) (w : (Fin n → A) → ℂ) (x : Fin n → A)
    (hx : priorSupportedWeight μ w x ≠ 0) : productPrior μ x ≠ 0 ∧ w x ≠ 0 := by
  by_cases hp : productPrior μ x = 0
  · simp only [priorSupportedWeight, hp, ite_true, if_true, ne_eq, not_true_eq_false] at hx
  · exact ⟨hp, by simpa only [priorSupportedWeight, hp, ite_false, if_false] using hx⟩

theorem priorSupportedWeight_sum {A : Type*} [Fintype A] {n : ℕ}
    (μ : Fin n → A → ℝ) (w F : (Fin n → A) → ℂ) :
    (∑ x, (productPrior μ x : ℂ) * priorSupportedWeight μ w x * F x) =
      ∑ x, (productPrior μ x : ℂ) * w x * F x := by
  apply Finset.sum_congr rfl
  intro x _
  by_cases hp : productPrior μ x = 0 <;> simp only [priorSupportedWeight, hp, ite_true, if_true,
    ite_false, if_false, Complex.ofReal_zero, zero_mul, mul_zero]

theorem regularInitialAmplitude_priorSupportedWeight {n : ℕ}
    (P : Finset ℕ) [∀ q : P, NeZero (q : ℕ)] (μ : Fin n → P → ℝ)
    (F : Fin n → (q : P) → ZMod (q : ℕ) → ℂ)
    (ψ : 𝓢(ℝ, ℂ)) (X : ℝ) (N : ℕ) (w : (Fin n → P) → ℂ) :
    regularInitialAmplitude P μ F ψ X N (priorSupportedWeight μ w) =
      regularInitialAmplitude P μ F ψ X N w :=
  priorSupportedWeight_sum μ w _

/-- Product and frequency bounds need hold only where the original weighted
summand is nonzero. Zero prior atoms are removed by an exact identity. -/
theorem regularInitialAmplitude_lower_on_support {n : ℕ}
    (P : Finset ℕ) [∀ q : P, NeZero (q : ℕ)] (hP : ∀ q ∈ P, q.Prime)
    (μ : Fin n → P → ℝ) (C : Fin n → ℝ)
    (hμ : ∀ i p, 0 ≤ μ i p) (hC : ∀ i, 0 ≤ C i)
    (hbound : ∀ i (p : P), (p : ℝ) * μ i p ≤ C i)
    (F : Fin n → (q : P) → ZMod (q : ℕ) → ℂ)
    (hzero : ∀ i q, (∑ a, F i q a) = 0)
    (henergy : ∀ i q, (∑ a, ‖F i q a‖ ^ 2) ≤ q)
    (ψ : 𝓢(ℝ, ℂ)) (X H R Δ δ : ℝ) (hX : 0 < X) (hR : 0 < R) (N : ℕ)
    (w : (Fin n → P) → ℂ) (hw : ∀ x, ‖w x‖ ≤ 1)
    (hcut : ∀ x, productPrior μ x ≠ 0 → w x ≠ 0 → H * (∏ i, (x i : ℕ)) ≤ N * X)
    (hsupp : ∀ t : ℝ, H < |t| → 𝓕 ψ t = 0)
    (hsmall : ∀ i (p : P), μ i p ≠ 0 → H * R < (p : ℝ))
    (hlower : ∀ x, productPrior μ x ≠ 0 → w x ≠ 0 → X * Real.exp Δ ≤ ∏ i, (x i : ℝ))
    (hupper : ∀ x, productPrior μ x ≠ 0 → w x ≠ 0 → (∏ i, (x i : ℝ)) ≤ X * R)
    (hpositive : Real.sqrt X * (δ +
      ‖𝓕 ψ 0‖ * (∏ i, C i) * (n : ℝ) ^ n *
        Real.exp ((∑ p : P, (p : ℝ)⁻¹) - Δ / 2)) ≤
      ‖∑ x : Fin n → P, (productPrior μ x : ℂ) * w x * physicalTupleSum P x F ψ X‖) :
    δ ≤ ‖regularInitialAmplitude P μ F ψ X N w‖ := by
  have hnorm (x) : ‖priorSupportedWeight μ w x‖ ≤ 1 := by
    by_cases hp : productPrior μ x = 0
    · simp only [priorSupportedWeight, hp, ite_true, if_true, norm_zero, zero_le_one]
    · simpa only [priorSupportedWeight, hp, ite_false, if_false] using hw x
  have hpos := hpositive
  rw [← priorSupportedWeight_sum μ w (fun x => physicalTupleSum P x F ψ X)] at hpos
  let E := Finset.univ.filter (fun x : Fin n → P =>
    ¬ Function.Injective x ∧ productPrior μ x ≠ 0 ∧ w x ≠ 0)
  have hEsupport (x) (hx : x ∈ E) : ¬ Function.Injective x ∧ productPrior μ x ≠ 0 ∧ w x ≠ 0 :=
    (Finset.mem_filter.mp hx).2
  have herr := repeated_physical_prior_bound_at P hP μ C hμ hC hbound F hzero henergy
    ψ X H R Δ hX hR hsupp E (fun x hx => (hEsupport x hx).1)
    (fun x hx i => hsmall i (x i)
      ((Finset.prod_ne_zero_iff.mp (hEsupport x hx).2.1) i (Finset.mem_univ i)))
    (fun x hx => hlower x (hEsupport x hx).2.1 (hEsupport x hx).2.2)
    (fun x hx => hupper x (hEsupport x hx).2.1 (hEsupport x hx).2.2)
    w (fun x _ => hw x)
  have heq : (∑ x ∈ Finset.univ.filter (fun x : Fin n → P => ¬ Function.Injective x),
      (productPrior μ x : ℂ) * priorSupportedWeight μ w x * physicalTupleSum P x F ψ X) =
      ∑ x ∈ E, (productPrior μ x : ℂ) * w x * physicalTupleSum P x F ψ X := by
    simp only [E, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hi : Function.Injective x <;> by_cases hp : productPrior μ x = 0 <;>
      by_cases hz : w x = 0 <;> simp [priorSupportedWeight, hi, hp, hz]
  have hresult := regularInitialAmplitude_lower P hP μ F ψ X H hX N
    (priorSupportedWeight μ w)
    (fun x hx => hcut x (priorSupportedWeight_support μ w x hx).1
      (priorSupportedWeight_support μ w x hx).2) hsupp δ
    (‖𝓕 ψ 0‖ * (∏ i, C i) * (n : ℝ) ^ n *
      Real.exp ((∑ p : P, (p : ℝ)⁻¹) - Δ / 2)) hpos (by rw [heq]; exact herr)
  rwa [regularInitialAmplitude_priorSupportedWeight] at hresult

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SupportedHalfInitialAmplitude
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Initial half-list lower bound with the actual live prime supports -/
namespace Ostmann
open scoped Classical BigOperators SchwartzMap FourierTransform

theorem primeHalfTests_initialAmplitude_lower_on_support {n : ℕ}
    (P : Finset ℕ) [∀ q : P, NeZero (q : ℕ)] (hP : ∀ q ∈ P, q.Prime)
    (S : (q : P) → Finset (ZMod (q : ℕ))) (favorable : P → Bool)
    (ν : Fin (n + 1) → P → ℝ) (C : Fin (n + 1) → ℝ)
    (hν : ∀ i q, 0 ≤ ν i q) (hC : ∀ i, 0 ≤ C i)
    (hbound : ∀ i (q : P), (q : ℝ) * ν i q ≤ C i)
    (w : (Fin n → P) → ℝ) (hw : ∀ x, 0 ≤ w x) (hw1 : ∀ x, w x ≤ 1)
    (E : Finset ℤ) (B : Finset (Fin n → P)) (β δ c : ℝ)
    (hβ : 0 ≤ β) (hδ : 0 ≤ δ) (hc : 0 ≤ c)
    (hmass : β ≤ ∑ x ∈ B, productPrior (Fin.tail ν) x * w x)
    (hbalance : ∀ x ∈ B, ∀ i, (1 / 3 : ℝ) ≤ residueDensity (S (x i)) ∧
      residueDensity (S (x i)) ≤ 2 / 3)
    (hendpoint : ∀ a ∈ E, ∀ q : P, (a : ZMod (q : ℕ)) ∈ S q)
    (hmean : (E.card : ℝ) * δ ≤ ∑ a ∈ E,
      (∑ q : P, (ν 0 q : ℂ) * primePhysicalTest (S q) true (favorable q)
        (a : ZMod (q : ℕ))).re)
    (ψ : 𝓢(ℝ, ℂ)) (X H R Δ η : ℝ) (hX : 0 < X) (hR : 0 < R) (N : ℕ)
    (hψ : ∀ x, 0 ≤ (ψ x).re) (hcE : ∀ a ∈ E, c ≤ (ψ ((a : ℝ) / X)).re) :
    let F : Fin (n + 1) → (q : P) → ZMod (q : ℕ) → ℂ := primeHalfTests P S favorable
    let W := doubledHalfWeight (fun y : Fin (n + 1) → P => (w (Fin.tail y) : ℂ))
    (∀ x, productPrior (Fin.append ν ν) x ≠ 0 → W x ≠ 0 → H * (∏ i, (x i : ℕ)) ≤ N * X) →
    (∀ t : ℝ, H < |t| → 𝓕 ψ t = 0) →
    (∀ i (p : P), ν i p ≠ 0 → H * R < (p : ℝ)) →
    (∀ x, productPrior (Fin.append ν ν) x ≠ 0 → W x ≠ 0 → X * Real.exp Δ ≤ ∏ i, (x i : ℝ)) →
    (∀ x, productPrior (Fin.append ν ν) x ≠ 0 → W x ≠ 0 → (∏ i, (x i : ℝ)) ≤ X * R) →
    Real.sqrt X * (η + ‖𝓕 ψ 0‖ * (∏ i, Fin.append C C i) *
      (((n + 1) + (n + 1) : ℕ) : ℝ) ^ ((n + 1) + (n + 1)) *
        Real.exp ((∑ p : P, (p : ℝ)⁻¹) - Δ / 2)) ≤
      (E.card : ℝ) * (c * (β * (1 / 2 : ℝ) ^ n * δ) ^ 2) →
    η ≤ ‖regularInitialAmplitude P (Fin.append ν ν) (Fin.append F F) ψ X N W‖ := by
  intro F W hcut hsupp hsmall hlower hupper hscale
  have hpositive := primeHalfTests_statistic_lower P hP S favorable (ν 0) (Fin.tail ν) w
    (fun i q => hν i.succ q) hw E B β δ c hβ hδ hc hmass hbalance hendpoint hmean
    ψ X hX hψ hcE
  simp only [Fin.cons_self_tail] at hpositive
  have hW (x : Fin ((n + 1) + (n + 1)) → P) : ‖W x‖ ≤ 1 := by
    have hh (y : Fin (n + 1) → P) : ‖(w (Fin.tail y) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_of_nonneg (hw _)]
      exact hw1 _
    change ‖(w (Fin.tail (fun i => x (i.castAdd (n + 1)))) : ℂ) *
      (w (Fin.tail (fun i => x (i.natAdd (n + 1)))) : ℂ)‖ ≤ 1
    rw [norm_mul]
    exact (mul_le_mul (hh _) (hh _) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  exact regularInitialAmplitude_lower_on_support P hP (Fin.append ν ν) (Fin.append C C)
    (fun i q => Fin.addCases (fun j => by simpa only [Fin.append_left] using hν j q)
      (fun j => by simpa only [Fin.append_right] using hν j q) i)
    (fun i => Fin.addCases (fun j => by simpa only [Fin.append_left] using hC j)
      (fun j => by simpa only [Fin.append_right] using hC j) i)
    (fun i q => Fin.addCases (fun j => by simpa only [Fin.append_left] using hbound j q)
      (fun j => by simpa only [Fin.append_right] using hbound j q) i)
    (Fin.append F F)
    (fun i q => Fin.addCases (fun j => by simpa only [Fin.append_left, F] using (primeHalfTests_sum (n := n) P S favorable j q))
      (fun j => by simpa only [Fin.append_right, F] using (primeHalfTests_sum (n := n) P S favorable j q)) i)
    (fun i q => Fin.addCases (fun j => by simpa only [Fin.append_left, F] using (primeHalfTests_energy (n := n) P S favorable j q))
      (fun j => by simpa only [Fin.append_right, F] using (primeHalfTests_energy (n := n) P S favorable j q)) i)
    ψ X H R Δ η hX hR N W hW hcut hsupp
    (fun i q => Fin.addCases
      (fun j hj => hsmall j q (by simpa only [Fin.append_left] using hj))
      (fun j hj => hsmall j q (by simpa only [Fin.append_right] using hj)) i) hlower hupper (hscale.trans hpositive)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_UniformSupportedInitialAmplitude
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A uniform exponential lower bound for the actual mixed initial amplitude -/
namespace Ostmann
open Filter
open scoped Classical BigOperators SchwartzMap FourierTransform

/-- The cell count affects the threshold but not the final exponential rate.
All product restrictions are imposed only on the live original prior. -/
theorem uniform_supported_initial_amplitude (r : ℕ) (z A B Bs a c δ : ℝ)
    (hz : 1 ≤ z) (ha : 0 < a) (hc : 0 < c) (hδ : 0 < δ)
    (hBs : 2 * (A + B + 2 * Real.log 4 +
      (4 * (Real.log 2 + 2) + 2 * Real.log 2 + 4) + 3) ≤ Bs)
    (ψ : 𝓢(ℝ, ℂ)) (T : ℝ)
    (hψ : ∀ x, 0 ≤ (ψ x).re) (hsupp : ∀ t : ℝ, T < |t| → 𝓕 ψ t = 0) :
    ∀ᶠ m : ℕ in atTop, ∀ (L Y X Δ R : ℝ),
      0 < L → L ≤ m → (m : ℝ) ≤ z * L →
      0 < Y → Y ≤ Real.exp L → 0 < X → 0 < R →
      (Bs + 8 * Real.log z) * m ≤ Δ →
      ∀ (P : Finset ℕ) [∀ q : P, NeZero (q : ℕ)] (_hP : ∀ q ∈ P, q.Prime),
      ∀ (S : (q : P) → Finset (ZMod (q : ℕ))) (favorable : P → Bool)
        (ν : Fin ((m + r) + 1) → P → ℝ) (C : Fin ((m + r) + 1) → ℝ),
      (∀ i q, 0 ≤ ν i q) → (∀ i, 0 ≤ C i) →
      (∀ i (q : P), (q : ℝ) * ν i q ≤ C i) →
      (∏ i, Fin.append C C i) * L ^ (2 * m) ≤ Real.exp (A * m) →
      (∑ p : P, (p : ℝ)⁻¹) ≤ B * m →
      ∀ (w : (Fin (m + r) → P) → ℝ) (E : Finset ℤ)
        (balanced : Finset (Fin (m + r) → P)),
      (∀ x, 0 ≤ w x) → (∀ x, w x ≤ 1) →
      Real.exp (-(2 * (Real.log 2 + 2)) * m) ≤
        ∑ x ∈ balanced, productPrior (Fin.tail ν) x * w x →
      (∀ x ∈ balanced, ∀ i, (1 / 3 : ℝ) ≤ residueDensity (S (x i)) ∧
        residueDensity (S (x i)) ≤ 2 / 3) →
      a * Real.sqrt X / Y ^ 3 ≤ (E.card : ℝ) →
      (∀ e ∈ E, c ≤ (ψ ((e : ℝ) / X)).re) →
      (∀ e ∈ E, ∀ q : P, (e : ZMod (q : ℕ)) ∈ S q) →
      (E.card : ℝ) * δ ≤ ∑ e ∈ E,
        (∑ q : P, (ν 0 q : ℂ) * primePhysicalTest (S q) true (favorable q)
          (e : ZMod (q : ℕ))).re →
      (∀ i (q : P), ν i q ≠ 0 → T * R < (q : ℝ)) →
      ∀ N : ℕ,
      let W := doubledHalfWeight (fun y : Fin ((m + r) + 1) → P => (w (Fin.tail y) : ℂ))
      (∀ x, productPrior (Fin.append ν ν) x ≠ 0 → W x ≠ 0 →
        T * (∏ i, (x i : ℕ)) ≤ N * X) →
      (∀ x, productPrior (Fin.append ν ν) x ≠ 0 → W x ≠ 0 →
        X * Real.exp Δ ≤ ∏ i, (x i : ℝ)) →
      (∀ x, productPrior (Fin.append ν ν) x ≠ 0 → W x ≠ 0 →
        (∏ i, (x i : ℝ)) ≤ X * R) →
      let F : Fin ((m + r) + 1) → (q : P) → ZMod (q : ℕ) → ℂ := primeHalfTests P S favorable
      Real.exp (-(6 * Real.log 2 + 13) * m) ≤
        ‖regularInitialAmplitude P (Fin.append ν ν) (Fin.append F F) ψ X N W‖ := by
  have hbudget := eventual_initial_amplitude_error_budget r z ‖𝓕 ψ 0‖ A B Bs a c δ
    (2 * (Real.log 2 + 2)) hz ha hc hδ (by nlinarith only [hBs])
  filter_upwards [hbudget] with m hbudget
  intro L Y X Δ R hL hLm hmL hY hYL hX hR hgap P _ hP S favorable ν C
    hν hC hbound hnorm hmass w E balanced hw hw1 hbalanced hbalance hE hcE hendpoint hmean
    hsmall N W hcut hlower hupper F
  have hprod : 0 ≤ ∏ i, Fin.append C C i := Finset.prod_nonneg (fun i _ => by
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [Fin.append_left] using hC j
    · simpa only [Fin.append_right] using hC j)
  have hs := hbudget L Y X (E.card : ℝ) (∏ i, Fin.append C C i)
    (∑ p : P, (p : ℝ)⁻¹) Δ (m + r) hL hLm hmL hY hYL hX.le le_rfl
    hE hprod hnorm hmass hgap
  have hrate : 2 * (2 * (Real.log 2 + 2)) + 2 * Real.log 2 + 5 =
      6 * Real.log 2 + 13 := by ring
  rw [hrate] at hs
  have hcount : ((m + r) + 1) + ((m + r) + 1) = 2 * (m + (r + 1)) := by omega
  exact primeHalfTests_initialAmplitude_lower_on_support P hP S favorable ν C
    hν hC hbound w hw hw1 E balanced (Real.exp (-(2 * (Real.log 2 + 2)) * m)) δ c
    (Real.exp_nonneg _) hδ.le hc.le hbalanced hbalance hendpoint hmean
    ψ X T R Δ (Real.exp (-(6 * Real.log 2 + 13) * m)) hX hR N hψ hcE
    hcut hsupp hsmall hlower hupper (by simpa only [hcount] using hs)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SelectedInitialAmplitude
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original initial amplitude for the selected mixed priors -/
namespace Ostmann
open Filter
open scoped Classical BigOperators SchwartzMap FourierTransform

theorem eventual_selected_initial_amplitude_oai
    (k : ℕ) (hk : 2 ≤ k) (Bs BD Bz a C atail c δ H : ℝ)
    (hBs : 0 ≤ Bs) (hH : 0 ≤ H) (hatail : 0 < atail) (hc : 0 < c) (hδ : 0 < δ)
    (hgap : 2 * ((4 - 2 * Real.log (1 / 320000)) + 2 + 2 * Real.log 4 +
      (4 * (Real.log 2 + 2) + 2 * Real.log 2 + 4) + 3) ≤ Bs - 1)
    (hklarge : 14 * (64 * tailCellLinearRate a C + 3) ≤ (k : ℝ) ^ 3)
    (ψ : 𝓢(ℝ, ℂ)) (hψ : ∀ x, 0 ≤ (ψ x).re)
    (hsupp : ∀ t : ℝ, H < |t| → 𝓕 ψ t = 0) :
    ∀ᶠ L : ℝ in atTop, ∀ {A B : Set ℕ} {N hi top : ℕ}
      {Y G cb cd : ℝ} {D Qb Qd : Finset ℕ} {centers : List ℕ},
      0 < Y → Y ≤ Real.exp L →
      SelectedSmallTailCell A B N a C L Y hi D
        ((movingProtectedTarget k Y G cd (movingInitialGapTotal k Bs BD Bz L) - 2 * cb) / 6) top →
      List.Forall₂ (fun j w => SelectedSmallTailCell A B N a C L Y hi D (w / 4) j)
        centers (movingCompensationTargets
          (movingProtectedTarget k Y G cd (movingInitialGapTotal k Bs BD Bz L))
          (movingCompensationGaps k BD Bz L)) → centers.length = k →
      ∀ (P : Finset ℕ) [∀ q : P, NeZero (q : ℕ)], (∀ p ∈ P, p.Prime) →
      initialRegularPrimeRange L ⊆ P → smoothGiantPrimeRange G ⊆ P →
      0 < smoothGiantMass (smoothGiantPrimeRange G) logCellProfile G →
      smoothGiantLogNormalizer (smoothGiantPrimeRange G) logCellProfile G ≤ (91 / 100) * L →
      (∑ p : P, primeSubsetPrior P Qb p) = 1 →
      (∑ p : P, primeSubsetPrior P Qd p) = 1 →
      (∀ p : P, (p : ℝ) * primeSubsetPrior P Qb p ≤ (L / 320000)⁻¹ ∧
        (p : ℝ) * primeSubsetPrior P Qd p ≤ (L / 320000)⁻¹) →
      let m := spectatorBulkCount k L
      let cells := initialSmallCellList top centers
      let ν := selectedInitialHalfPrior P A B N hi Y G D Qb Qd (m / 2) (m / 2) top centers
      let w := initialHalfCutoffWeight (fun p : P => (p : ℕ)) (m / 2) (m / 2) cells.length cb cd
      let good := fun p : P => (1 / 3 : ℝ) ≤ residueDensity (tailDensityMask A N p) ∧
        residueDensity (tailDensityMask A N p) ≤ 2 / 3
      Real.exp (-(2 * (Real.log 2 + 2)) * m) ≤
        ∑ x ∈ balancedTupleSet (m / 2 + (m / 2 + cells.length)) (fun _ p => good p),
          productPrior (Fin.tail ν) x * w x →
      (∀ i (p : P), ν i p ≠ 0 → Real.exp (Real.exp ((4 / 10000 : ℝ) * L)) ≤ (p : ℝ)) →
      (∑ p : P, (p : ℝ)⁻¹) ≤ 2 * m →
      ∀ (E : Finset ℤ) (favorable : P → Bool),
      atail * Real.sqrt (Real.exp Y) / Y ^ 3 ≤ (E.card : ℝ) →
      (∀ e ∈ E, c ≤ (ψ ((e : ℝ) / Real.exp Y)).re) →
      (∀ e ∈ E, ∀ p : P, (e : ZMod (p : ℕ)) ∈ tailDensityMask A N p) →
      (E.card : ℝ) * δ ≤ ∑ e ∈ E,
        (∑ p : P, (smoothGiantPrior P logCellProfile G p : ℂ) *
          primePhysicalTest (tailDensityMask A N p) true (favorable p)
            (e : ZMod (p : ℕ))).re →
      ∀ T : ℕ → ℝ,
      let Δ := selectedInitialLogCenter G Y cb cd top centers
      let width : ℝ := 2 * (cells.length + 3)
      let V := movingProductNaturalCutoff T (Y + Δ + width) Y ((m : ℝ) / 4) 0
      let F : Fin ((m / 2 + (m / 2 + cells.length)) + 1) →
        (p : P) → ZMod (p : ℕ) → ℂ := primeHalfTests P (fun p => tailDensityMask A N p) favorable
      Real.exp (-(6 * Real.log 2 + 13) * m) ≤
        ‖regularInitialAmplitude P (Fin.append ν ν) (Fin.append F F) ψ (Real.exp Y) V
          (doubledHalfWeight (fun y => (w (Fin.tail y) : ℂ)))‖ := by
  classical
  have hz : 1 ≤ (k : ℝ) ^ 4 := one_le_pow₀ (by exact_mod_cast (show 1 ≤ k by omega))
  have hrate : 0 ≤ Bs + 1 + 8 * Real.log ((k : ℝ) ^ 4) := by
    have := Real.log_nonneg hz
    linarith
  obtain ⟨M, hM⟩ := eventually_atTop.mp (uniform_supported_initial_amplitude
    (3 + 2 * k) ((k : ℝ) ^ 4) (4 - 2 * Real.log (1 / 320000)) 2 (Bs - 1)
    atail c δ hz hatail hc hδ hgap ψ H hψ hsupp)
  filter_upwards [(spectatorBulkCount_tendsto k (by omega)).eventually
      (eventually_ge_atTop (M : ℝ)),
    eventual_linear_product_prime_window H (Bs + 1 + 8 * Real.log ((k : ℝ) ^ 4))
      ((k : ℝ) ^ 4) (4 / 10000) hrate (by norm_num),
    eventual_spectator_product_poisson_cutoff k (by omega) H hH,
    eventually_ge_atTop (1 : ℝ), eventually_ge_atTop (4 / (k : ℝ) ^ 4)]
    with L hm0 hprime hpoisson hL hscale
  intro A B N hi top Y G cb cd D Qb Qd centers hY hYhi htop hcenters hlen
    P _ hP hsmall hgiant hmass hnorm hb hd hpoint m cells ν w good hbalanced
    hlive htotal E favorable hE hcE hendpoint hmean T Δ width V F
  have hscale' : 4 ≤ (k : ℝ) ^ 4 * L := by
    simpa only [mul_comm] using (div_le_iff₀ (by positivity : 0 < (k : ℝ) ^ 4)).mp hscale
  have hmupper : (m : ℝ) ≤ (k : ℝ) ^ 4 * L := spectatorBulkCount_upper k L (by linarith)
  have hmlower : L ≤ (m : ℝ) := by
    have h := spectatorBulkCount_half k L hscale'
    have hk4 : (2 : ℝ) ≤ (k : ℝ) ^ 4 := by
      have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2)
        (show (2 : ℝ) ≤ k by exact_mod_cast hk) 4
      norm_num at hh
      linarith
    nlinarith only [h, mul_le_mul_of_nonneg_right hk4 (by linarith : 0 ≤ L)]
  have hdata := selected_initial_prior_bounds (a₀ := 1 / 320000) htop hcenters P hP hsmall hgiant hmass hnorm
    hb hd (by simpa only [div_eq_mul_inv, mul_comm, one_mul] using hpoint) (m / 2) (m / 2)
  have hwindow := selected_initial_window_rate k hk hL (tailCellLinearRate_nonneg a C)
    (tailDefectBudget_linear a C L Y hL hY hYhi) hklarge hscale' htop hcenters hlen
  have hnormcost := selected_initial_normalizer_rate k hk L (by linarith) hscale' top centers hlen
  have hlen' : cells.length = 3 + 2 * k := by
    dsimp only [cells]
    rw [initialSmallCellList_length, hlen]
  have heven : m / 2 + m / 2 = m := by
    obtain ⟨t, ht⟩ := spectatorBulkCount_even k L
    dsimp only [m]
    omega
  have heq : m + (3 + 2 * k) = m / 2 + (m / 2 + cells.length) := by omega
  have hh := hM m (by exact_mod_cast hm0)
  rw [heq] at hh
  have hwidth : 0 ≤ width := by dsimp only [width]; positivity
  have hlow : 0 ≤ Δ - width := by
    have hg : 0 ≤ Bs - 1 + 8 * Real.log ((k : ℝ) ^ 4) := by
      have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      have hl4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
      have hla : Real.log (1 / 320000 : ℝ) ≤ 0 := Real.log_nonpos (by norm_num) (by norm_num)
      linarith [Real.log_nonneg hz]
    exact (mul_nonneg hg (Nat.cast_nonneg _)).trans hwindow.1
  have hpoisson' : H * Real.exp (Δ + width) ≤ V := by
    have hw : Y ≤ Y + Δ + width := by linarith
    have hh := hpoisson T (Y + Δ + width) Y hw
    have he : Y + Δ + width - Y = Δ + width := by ring
    simpa only [he] using hh
  apply hh L Y (Real.exp Y) (Δ - width) (Real.exp (Δ + width))
    (by linarith) hmlower hmupper hY hYhi (Real.exp_pos _) (Real.exp_pos _) hwindow.1
    P hP (fun p => tailDensityMask A N p) favorable ν
    (initialHalfNormalizer (m / 2) (m / 2) cells.length (1 / 320000) L (91 / 100))
    hdata.1 (initialHalfNormalizer_nonneg _ _ _ _ _ _ (by norm_num) (by linarith)) hdata.2.2
    hnormcost htotal w E
    (balancedTupleSet (m / 2 + (m / 2 + cells.length)) (fun _ p => good p))
    (initialHalfCutoffWeight_nonneg _ _ _ _ _ _) (initialHalfCutoffWeight_le_one _ _ _ _ _ _)
    hbalanced (by
      intro x hx i
      have hx' : ∀ j, good (x j) := by
        simpa only [balancedTupleSet, Finset.mem_filter, Finset.mem_univ, true_and] using hx
      exact hx' i) hE hcE hendpoint hmean
    (fun i p hp => hprime m hmupper (Δ + width) hwindow.2 p (hlive i p hp)) V
  all_goals
    intro x hx hw
    have hprod := selected_initial_product_window htop hcenters P hP (m / 2) (m / 2)
      (fun _ => primeSubsetPrior P Qb) (fun _ => primeSubsetPrior P Qd) x hx hw
  · exact sampled_product_poisson_cutoff (fun i => (x i : ℕ)) (Real.exp Y) H
      (Real.exp (Δ + width)) V (Real.exp_nonneg _) hH hprod.2 hpoisson'
  · exact hprod.1
  · exact hprod.2

end Ostmann

end OAI
end

theorem solution : type_of% @OAI.Ostmann.eventual_selected_initial_amplitude_oai := @OAI.Ostmann.eventual_selected_initial_amplitude_oai
