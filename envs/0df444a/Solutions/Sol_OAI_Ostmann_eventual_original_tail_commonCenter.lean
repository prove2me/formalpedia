-- Prove2me | solution 1 for OAI.Ostmann.eventual_original_tail_commonCenter
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T07:08:36.956229+00:00
-- url     : https://prove2.me/submissions/2789dae5-ec02-4c2b-8881-522b0533891f

import Mathlib
import Definitions.Def_OAIQ095D007
import Theorems.Thm_OAI_Ostmann_eventual_original_tuple_witness_lift
import Theorems.Thm_OAI_Ostmann_eventual_original_witness_probability

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
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_CRTPhaseLift
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Identifying the CRT phase with the common real translation -/

namespace Ostmann

theorem crt_translation_phase {d M : ℕ} [NeZero d] [NeZero M]
    (h : d.Coprime M) (t : ZMod M) (h₀ u : ℤ)
    (hlift : (d : ℤ) ∣ (t.val : ℤ) + (M : ℤ) * h₀) :
    ZMod.stdAddChar (t * ((d : ZMod M)⁻¹ * (u : ZMod M))) =
      realAdditivePhase ((((t.val : ℝ) / M + h₀) * u) / d) := by
  obtain ⟨k, hk⟩ := hlift
  have hd : IsUnit (d : ZMod M) := (ZMod.isUnit_iff_coprime d M).mpr h
  have hkmod : (d : ZMod M) * (k : ZMod M) = t := by
    have hh := congrArg (fun z : ℤ => (z : ZMod M)) hk
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self,
      zero_mul, add_zero, ZMod.natCast_zmod_val] using hh.symm
  have hkinv : (d : ZMod M)⁻¹ * t = (k : ZMod M) := by
    rw [← hkmod, ← mul_assoc, ZMod.inv_mul_of_unit _ hd, one_mul]
  have harg : t * ((d : ZMod M)⁻¹ * (u : ZMod M)) = ((k * u : ℤ) : ZMod M) := by
    rw [Int.cast_mul, ← hkinv]
    ring
  have hkreal : (t.val : ℝ) + (M : ℝ) * h₀ = (d : ℝ) * k := by exact_mod_cast hk
  have hreal : (((t.val : ℝ) / M + h₀) * u) / d = ((k * u : ℤ) : ℝ) / M := by
    have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne d
    have hMR : (M : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne M
    calc
      _ = ((t.val : ℝ) + M * h₀) * u / ((M : ℝ) * d) := by field_simp
      _ = _ := by rw [hkreal]; push_cast; field_simp
  rw [harg, hreal, ZMod.stdAddChar_coe]
  unfold realAdditivePhase
  congr 1
  push_cast
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_IntegerFrequencySplit
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Separating positive and negative frequencies with a finite cutoff -/

namespace Ostmann

open scoped BigOperators ComplexConjugate Classical

theorem integer_frequency_conjugate_split (F : ℤ → ℂ) (N : ℕ) (c : ℂ)
    (hzero : F 0 = 0) (hneg : ∀ n : ℕ, F (-(n : ℤ)) = c * conj (F n))
    (hcut : ∀ n : ℕ, N < n → F n = 0) :
    (∑' n : ℤ, F n) = (∑ n ∈ Finset.Icc 1 N, F n) +
      c * conj (∑ n ∈ Finset.Icc 1 N, F n) := by
  have hp (n : ℕ) (hn : n ∉ Finset.Icc 1 N) : F n = 0 := by
    simp only [Finset.mem_Icc, not_and_or, not_le] at hn
    rcases hn with hn | hn
    · have he : n = 0 := by omega
      simpa only [he, Nat.cast_zero] using hzero
    · exact hcut n hn
  have hm (n : ℕ) (hn : n ∉ Finset.Icc 1 N) : F (-(n : ℤ)) = 0 := by
    rw [hneg, hp n hn, map_zero, mul_zero]
  have hps : Summable (fun n : ℕ => F n) := summable_of_ne_finset_zero hp
  have hms : Summable (fun n : ℕ => F (-(n : ℤ))) := summable_of_ne_finset_zero hm
  rw [hps.tsum_of_nat_of_neg hms, hzero, sub_zero, tsum_eq_sum hp, tsum_eq_sum hm]
  simp only [hneg, ← Finset.mul_sum, map_sum]

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
-- module Solutions.OAIQ095_OS.Ostmann_Characters_TranslatedCharacterPoisson
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The translated primitive-character Poisson identity

This is the exact finite-modulus transform used before the squarefree
frequency decomposition in Section 3 of the manuscript.
-/

namespace Ostmann

open scoped BigOperators FourierTransform SchwartzMap

theorem translated_character_crt_fourier {d M : ℕ} [NeZero d] [NeZero M]
    (h : d.Coprime M) (f : ZMod d → ℂ) (χ : DirichletCharacter ℂ M)
    (hχ : χ.IsPrimitive) (t : ZMod M) (u : ZMod (d * M)) :
    additiveFourier (fun x => f ((ZMod.chineseRemainder h) x).1 *
      χ (((ZMod.chineseRemainder h) x).2 - t)) (-u) =
      additiveFourier f (-((M : ZMod d)⁻¹ * ((ZMod.chineseRemainder h) u).1)) *
      ZMod.stdAddChar (t * ((d : ZMod M)⁻¹ * ((ZMod.chineseRemainder h) u).2)) *
      (M : ℂ)⁻¹ * χ⁻¹ ((d : ZMod M)⁻¹ * ((ZMod.chineseRemainder h) u).2) *
      gaussSum χ ZMod.stdAddChar := by
  rw [additiveFourier_crt h f (fun x => χ (x - t)) (-u),
    additiveFourier_translate, primitive_character_fourier _ hχ]
  simp only [map_neg]
  change additiveFourier f ((M : ZMod d)⁻¹ * -((ZMod.chineseRemainder h) u).1) *
    (ZMod.stdAddChar (-(t * ((d : ZMod M)⁻¹ * -((ZMod.chineseRemainder h) u).2))) *
      ((M : ℂ)⁻¹ * χ⁻¹ (-((d : ZMod M)⁻¹ * -((ZMod.chineseRemainder h) u).2)) *
        gaussSum χ ZMod.stdAddChar)) = _
  simp only [mul_neg, neg_neg]
  ring

theorem quadratic_character_inverse_value {M : ℕ} (χ : DirichletCharacter ℂ M)
    (hχ : χ.IsQuadratic) (x : ZMod M) (hx : IsUnit x) : χ (x⁻¹) = χ x := by
  obtain ⟨v, rfl⟩ := hx
  rw [ZMod.inv_coe_unit]
  have hh := MulChar.inv_apply χ (v : ZMod M)
  rw [Ring.inverse_unit, hχ.inv] at hh
  exact hh.symm

/-- For a quadratic character, the inverse frequency multiplier contributes
the ordinary character value of the other coprime modulus. -/
theorem quadratic_translated_crt_fourier {d M : ℕ} [NeZero d] [NeZero M]
    (h : d.Coprime M) (f : ZMod d → ℂ) (χ : DirichletCharacter ℂ M)
    (hχ : χ.IsPrimitive) (hq : χ.IsQuadratic) (t : ZMod M) (u : ZMod (d * M)) :
    additiveFourier (fun x => f ((ZMod.chineseRemainder h) x).1 *
      χ (((ZMod.chineseRemainder h) x).2 - t)) (-u) =
      additiveFourier f (-((M : ZMod d)⁻¹ * ((ZMod.chineseRemainder h) u).1)) *
      ZMod.stdAddChar (t * ((d : ZMod M)⁻¹ * ((ZMod.chineseRemainder h) u).2)) *
      (M : ℂ)⁻¹ * χ (d : ZMod M) * χ ((ZMod.chineseRemainder h) u).2 *
      gaussSum χ ZMod.stdAddChar := by
  rw [translated_character_crt_fourier h f χ hχ, hq.inv, map_mul χ,
    quadratic_character_inverse_value χ hq _ ((ZMod.isUnit_iff_coprime d M).mpr h)]
  ring

theorem quadratic_character_poisson {d M : ℕ} [NeZero d] [NeZero M]
    (h : d.Coprime M) (f : ZMod d → ℂ) (χ : DirichletCharacter ℂ M)
    (hχ : χ.IsPrimitive) (hq : χ.IsQuadratic) (t : ZMod M) (ψ : 𝓢(ℝ, ℂ)) :
    (∑' n : ℤ, f (n : ZMod d) * χ ((n : ZMod M) - t) *
      ψ ((n : ℝ) / (d * M : ℕ))) =
      (d : ℂ) * gaussSum χ ZMod.stdAddChar * ∑' n : ℤ,
        𝓕 ψ (n : ℝ) *
        additiveFourier f (-((M : ZMod d)⁻¹ * (n : ZMod d))) *
        ZMod.stdAddChar (t * ((d : ZMod M)⁻¹ * (n : ZMod M))) *
        χ (d : ZMod M) * χ (n : ZMod M) := by
  have he (n : ℤ) : (ZMod.chineseRemainder h) (n : ZMod (d * M)) =
      ((n : ZMod d), (n : ZMod M)) := by
    exact map_intCast (ZMod.chineseRemainder h) n
  have hp := integer_poisson_transform ψ
    (fun x : ZMod (d * M) => f ((ZMod.chineseRemainder h) x).1 *
      χ (((ZMod.chineseRemainder h) x).2 - t))
  simp_rw [he] at hp
  rw [hp]
  simp_rw [quadratic_translated_crt_fourier h f χ hχ hq, he]
  simp_rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  push_cast
  have hM : (M : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne M
  field_simp

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_ScaledPoisson
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
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

theorem scaled_quadratic_character_poisson {d M : ℕ} [NeZero d] [NeZero M]
    (h : d.Coprime M) (f : ZMod d → ℂ) (χ : DirichletCharacter ℂ M)
    (hχ : χ.IsPrimitive) (hq : χ.IsQuadratic) (t : ZMod M) (ψ : 𝓢(ℝ, ℂ))
    (X : ℝ) (hX : 0 < X) :
    (∑' n : ℤ, f (n : ZMod d) * χ ((n : ZMod M) - t) * ψ ((n : ℝ) / X)) =
      (X : ℂ) / M * gaussSum χ ZMod.stdAddChar * ∑' n : ℤ,
        𝓕 ψ ((n : ℝ) * X / (d * M : ℕ)) *
        additiveFourier f (-((M : ZMod d)⁻¹ * (n : ZMod d))) *
        ZMod.stdAddChar (t * ((d : ZMod M)⁻¹ * (n : ZMod M))) *
        χ (d : ZMod M) * χ (n : ZMod M) := by
  have hd : (0 : ℝ) < d := by exact_mod_cast NeZero.pos d
  have hM : (0 : ℝ) < M := by exact_mod_cast NeZero.pos M
  have ha : 0 < (d * M : ℕ) / X := div_pos (by rw [Nat.cast_mul]; exact mul_pos hd hM) hX
  have hp := quadratic_character_poisson h f χ hχ hq t
    (positiveDilate ψ ((d * M : ℕ) / X) ha)
  have harg (n : ℤ) : ((d * M : ℕ) : ℝ) / X * ((n : ℝ) / (d * M : ℕ)) = n / X := by
    field_simp
  simp_rw [positiveDilate_apply, harg, positiveDilate_fourier] at hp
  have hfreq (n : ℤ) : (n : ℝ) / ((d * M : ℕ) / X) = (n : ℝ) * X / (d * M : ℕ) := by rw [div_div_eq_mul_div]
  simp_rw [hfreq] at hp
  rw [hp]
  simp_rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne d
  have hMC : (M : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne M
  push_cast
  field_simp

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_DistinctTupleProducts
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Grouping distinct ordered products by their underlying subsets -/

namespace Ostmann

open scoped BigOperators Classical

theorem card_tupleImage_fiber {A : Type*} [Fintype A] [DecidableEq A]
    (k : ℕ) (Q : Finset A) (hQ : Q.card = k) :
    Fintype.card {e : Fin k ↪ A // tupleImage e = Q} = k.factorial := by
  rw [Fintype.card_congr (tupleImageFiberEquiv k Q)]
  let E : Fin k ≃ Q := Fintype.equivOfCardEq (by simpa using hQ.symm)
  simpa using Fintype.card_equiv E

theorem distinct_tuple_sum {A R : Type*} [Fintype A] [DecidableEq A]
    [CommSemiring R] (k : ℕ) (y : A → R) :
    (∑ e : Fin k ↪ A, ∏ i, y (e i)) =
      (k.factorial : R) * ∑ Q ∈ (Finset.univ : Finset A).powersetCard k, ∏ a ∈ Q, y a := by
  have hmaps (e : Fin k ↪ A) (_ : e ∈ (Finset.univ : Finset (Fin k ↪ A))) :
      tupleImage e ∈ (Finset.univ : Finset A).powersetCard k := by
    apply Finset.mem_powersetCard.mpr
    refine ⟨Finset.subset_univ _, ?_⟩
    have hc : (Finset.univ.image e).card = (Finset.univ : Finset (Fin k)).card :=
      Finset.card_image_iff.mpr e.injective.injOn
    simpa only [tupleImage, Finset.card_univ, Fintype.card_fin] using hc
  rw [← Finset.sum_fiberwise_of_maps_to hmaps, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro Q hQ
  have hcard := (Finset.mem_powersetCard.mp hQ).2
  have hprod (e : Fin k ↪ A) (he : tupleImage e = Q) :
      (∏ i, y (e i)) = ∏ a ∈ Q, y a := by
    rw [← he, tupleImage, Finset.prod_image e.injective.injOn]
  calc
    _ = ∑ _e ∈ (Finset.univ : Finset (Fin k ↪ A)).filter (fun e => tupleImage e = Q),
        ∏ a ∈ Q, y a := by
      apply Finset.sum_congr rfl
      intro e he
      exact hprod e (Finset.mem_filter.mp he).2
    _ = _ := by
      rw [Finset.sum_const]
      have hf : ((Finset.univ : Finset (Fin k ↪ A)).filter (fun e => tupleImage e = Q)).card =
          k.factorial := by
        simpa only [Fintype.card_subtype] using card_tupleImage_fiber k Q hcard
      rw [hf]
      simp only [nsmul_eq_mul]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Supply_TernaryProductPolynomial
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The generating polynomial for a finite ternary population

The differential equation below yields an elementary repeat-removal bound.
It uses only `y^3 = y`, the identity satisfied by the oriented quadratic
characters, and does not invoke partition inversion as an additional input.
-/

namespace Ostmann

open scoped BigOperators Classical
open Polynomial

theorem ternaryProduct_coeff {A : Type*} [DecidableEq A]
    (S : Finset A) (y : A → ℝ) (k : ℕ) :
    (ternaryProduct S y).coeff k = ∑ T ∈ S.powersetCard k, ∏ i ∈ T, y i := by
  have hexp : ternaryProduct S y =
      ∑ T ∈ S.powerset, C (∏ i ∈ T, y i) * X ^ T.card := by
    unfold ternaryProduct
    simp_rw [add_comm (1 : ℝ[X])]
    rw [Finset.prod_add_one]
    apply Finset.sum_congr rfl
    intro T _
    simp only [Finset.prod_mul_distrib, ← map_prod, Finset.prod_const]
  rw [hexp, finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [Finset.powersetCard_eq_filter, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro T _
  simp only [eq_comm]

theorem distinct_tuple_product_coeff {A : Type*} [Fintype A] [DecidableEq A]
    (y : A → ℝ) (k : ℕ) :
    (∑ e : Fin k ↪ A, ∏ i, y (e i)) =
      (k.factorial : ℝ) * (ternaryProduct Finset.univ y).coeff k := by
  rw [ternaryProduct_coeff, distinct_tuple_sum]

theorem ternaryProduct_differential {A : Type*} [DecidableEq A]
    (S : Finset A) (y : A → ℝ) (hy : ∀ i ∈ S, (y i) ^ 3 = y i) :
    (1 - X ^ 2) * derivative (ternaryProduct S y) =
      (C (∑ i ∈ S, y i) - C (∑ i ∈ S, (y i) ^ 2) * X) * ternaryProduct S y := by
  have hterm (i : A) (hi : i ∈ S) :
      (1 - X ^ 2) * C (y i) =
        (C (y i) - C ((y i) ^ 2) * X) * (1 + C (y i) * X) := by
    have hc : C (y i) ^ 3 = (C (y i) : ℝ[X]) := by rw [← map_pow, hy i hi]
    simp only [map_pow]
    linear_combination X ^ 2 * hc
  unfold ternaryProduct
  rw [derivative_prod_finset, Finset.mul_sum]
  calc
    _ = ∑ i ∈ S, (C (y i) - C ((y i) ^ 2) * X) *
        ∏ j ∈ S, (1 + C (y j) * X) := by
      apply Finset.sum_congr rfl
      intro i hi
      simp only [derivative_add, derivative_one, derivative_mul, derivative_C,
        zero_mul, derivative_X, mul_one, zero_add]
      rw [show (1 - X ^ 2) * ((∏ j ∈ S.erase i, (1 + C (y j) * X)) * C (y i)) =
          ((1 - X ^ 2) * C (y i)) * ∏ j ∈ S.erase i, (1 + C (y j) * X) by ring,
        hterm i hi, mul_assoc, Finset.mul_prod_erase S (fun j => (1 + C (y j) * X : ℝ[X])) hi]
    _ = _ := by
      rw [← Finset.sum_mul, Finset.sum_sub_distrib, ← Finset.sum_mul, ← map_sum, ← map_sum]

theorem ternaryProduct_coeff_recurrence {A : Type*} [DecidableEq A]
    (S : Finset A) (y : A → ℝ) (hy : ∀ i ∈ S, (y i) ^ 3 = y i) (n : ℕ) :
    ((n + 2 : ℕ) : ℝ) * (ternaryProduct S y).coeff (n + 2) =
      (∑ i ∈ S, y i) * (ternaryProduct S y).coeff (n + 1) -
      ((∑ i ∈ S, (y i) ^ 2) - n) * (ternaryProduct S y).coeff n := by
  have h := congrArg (fun p : ℝ[X] => p.coeff (n + 1))
    (ternaryProduct_differential S y hy)
  simp only [sub_mul, one_mul, coeff_sub, coeff_derivative, coeff_C_mul] at h
  have hx : (X ^ 2 * derivative (ternaryProduct S y)).coeff (n + 1) =
      n * (ternaryProduct S y).coeff n := by
    cases n with
    | zero => simp [coeff_X_pow_mul']
    | succ n =>
      rw [show n + 1 + 1 = n + 2 by omega, coeff_X_pow_mul]
      simp only [coeff_derivative]
      push_cast
      ring
  have hx' : (C (∑ i ∈ S, (y i) ^ 2) * X * ternaryProduct S y).coeff (n + 1) =
      (∑ i ∈ S, (y i) ^ 2) * (ternaryProduct S y).coeff n := by
    rw [mul_assoc, coeff_C_mul, coeff_X_mul]
  rw [hx, hx'] at h
  push_cast at h ⊢
  nlinarith only [h]

@[simp] theorem ternaryDistinct_one {A : Type*} [DecidableEq A]
    (S : Finset A) (y : A → ℝ) :
    ternaryDistinct S y 1 = ∑ i ∈ S, y i := by
  rw [ternaryDistinct, ternaryProduct_coeff]
  simp [Finset.powersetCard_one]

theorem ternaryDistinct_recurrence {A : Type*} [DecidableEq A]
    (S : Finset A) (y : A → ℝ) (hy : ∀ i ∈ S, (y i) ^ 3 = y i) (n : ℕ) :
    ternaryDistinct S y (n + 2) =
      (∑ i ∈ S, y i) * ternaryDistinct S y (n + 1) -
      (n + 1) * ((∑ i ∈ S, (y i) ^ 2) - n) * ternaryDistinct S y n := by
  have h := ternaryProduct_coeff_recurrence S y hy n
  push_cast at h
  unfold ternaryDistinct
  rw [show (n + 2).factorial = (n + 2) * (n + 1).factorial from Nat.factorial_succ (n + 1)]
  push_cast
  rw [mul_assoc, mul_left_comm ((n : ℝ) + 2), h, Nat.factorial_succ]
  push_cast
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_RepeatRemovalPointwise
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A moment-sensitive bound for deleting repeated indices

A square-root shift gives a convenient alternative to the cycle expansion:
`|D_k-S^k| ≤ (|S|+sqrt(k*J))^k-|S|^k`. After normalization and Hölder,
this has the same vanishing relative error at the manuscript's scales.
-/

namespace Ostmann

open scoped BigOperators Classical

theorem recurrence_power_error (f c : ℕ → ℝ) (s b : ℝ) (k : ℕ)
    (hb : 0 ≤ b) (hzero : f 0 = 1) (hone : f 1 = s)
    (hrec : ∀ n, n + 2 ≤ k → f (n + 2) = s * f (n + 1) - c n * f n)
    (hc : ∀ n, n + 2 ≤ k → |c n| ≤ b ^ 2) :
    |f k - s ^ k| ≤ (|s| + b) ^ k - |s| ^ k := by
  have hq : 0 ≤ |s| + b := add_nonneg (abs_nonneg s) hb
  have hbound (n : ℕ) (h : |f n - s ^ n| ≤ (|s| + b) ^ n - |s| ^ n) :
      |f n| ≤ (|s| + b) ^ n := by
    calc
      |f n| = |(f n - s ^ n) + s ^ n| := by rw [sub_add_cancel]
      _ ≤ |f n - s ^ n| + |s ^ n| := abs_add_le _ _
      _ ≤ (|s| + b) ^ n := by rw [abs_pow]; linarith
  have hall : ∀ n, n ≤ k → |f n - s ^ n| ≤ (|s| + b) ^ n - |s| ^ n := by
    intro n
    induction n using Nat.twoStepInduction with
    | zero => intro _; simp [hzero]
    | one => intro _; simp only [hone, pow_one, sub_self, abs_zero]; linarith
    | more n ihn ihn1 =>
      intro hn
      have he0 := ihn (by omega)
      have he1 := ihn1 (by omega)
      have hf0 := hbound n he0
      have hid : f (n + 2) - s ^ (n + 2) =
          s * (f (n + 1) - s ^ (n + 1)) - c n * f n := by
        rw [hrec n hn, pow_succ]
        ring
      have hmul : b ^ 2 * (|s| + b) ^ n ≤ b * (|s| + b) ^ (n + 1) := by
        rw [pow_succ (|s| + b) n]
        have hh := mul_nonneg (abs_nonneg s) hb
        have hp := mul_nonneg hh (pow_nonneg hq n)
        nlinarith only [hp]
      calc
        |f (n + 2) - s ^ (n + 2)| =
            |s * (f (n + 1) - s ^ (n + 1)) - c n * f n| := congrArg abs hid
        _ ≤ |s| * |f (n + 1) - s ^ (n + 1)| + |c n| * |f n| := by
          simpa only [abs_mul] using abs_sub (s * (f (n + 1) - s ^ (n + 1))) (c n * f n)
        _ ≤ |s| * ((|s| + b) ^ (n + 1) - |s| ^ (n + 1)) +
            b ^ 2 * (|s| + b) ^ n := add_le_add
          (mul_le_mul_of_nonneg_left he1 (abs_nonneg s))
          (mul_le_mul (hc n hn) hf0 (abs_nonneg _) (sq_nonneg b))
        _ ≤ |s| * ((|s| + b) ^ (n + 1) - |s| ^ (n + 1)) +
            b * (|s| + b) ^ (n + 1) := add_le_add_right hmul _
        _ = (|s| + b) ^ (n + 2) - |s| ^ (n + 2) := by rw [pow_succ, pow_succ]; ring
  exact hall k le_rfl

theorem ternary_distinct_product_error {A : Type*} [Fintype A] [DecidableEq A]
    (y : A → ℝ) (hy : ∀ i, y i = 0 ∨ y i = 1 ∨ y i = -1)
    (k : ℕ) (hk : k ≤ Fintype.card A) :
    |(∑ e : Fin k ↪ A, ∏ i, y (e i)) - (∑ i, y i) ^ k| ≤
      (|(∑ i, y i)| + Real.sqrt ((k : ℝ) * Fintype.card A)) ^ k - |(∑ i, y i)| ^ k := by
  have hycube (i : A) : (y i) ^ 3 = y i := by
    rcases hy i with h | h | h <;> rw [h] <;> norm_num
  have hysq (i : A) : (y i) ^ 2 ≤ 1 := by
    rcases hy i with h | h | h <;> rw [h] <;> norm_num
  have hJ : (0 : ℝ) ≤ Fintype.card A := Nat.cast_nonneg _
  have hK : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have hmass : (∑ i, (y i) ^ 2) ≤ (Fintype.card A : ℝ) := by
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] using
      Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hysq i)
  have hmass0 : 0 ≤ ∑ i, (y i) ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  rw [distinct_tuple_product_coeff]
  apply recurrence_power_error (fun n => ternaryDistinct Finset.univ y n)
    (fun n => (n + 1) * ((∑ i, (y i) ^ 2) - n)) (∑ i, y i)
    (Real.sqrt ((k : ℝ) * Fintype.card A)) k (Real.sqrt_nonneg _)
    (ternaryDistinct_zero _ _) (ternaryDistinct_one _ _)
  · intro n _
    exact ternaryDistinct_recurrence _ _ (fun i _ => hycube i) n
  · intro n hn
    have hnJ : (n : ℝ) ≤ Fintype.card A := by exact_mod_cast (show n ≤ Fintype.card A by omega)
    have hnK : (n : ℝ) + 1 ≤ k := by exact_mod_cast (show n + 1 ≤ k by omega)
    have hd : |(∑ i, (y i) ^ 2) - n| ≤ Fintype.card A := by
      rw [abs_le]
      constructor <;> linarith
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ n + 1),
      Real.sq_sqrt (mul_nonneg hK hJ)]
    exact mul_le_mul hnK hd (abs_nonneg _) hK

theorem normalized_ternary_distinct_product_error {A : Type*} [Fintype A] [DecidableEq A]
    (y : A → ℝ) (hy : ∀ i, y i = 0 ∨ y i = 1 ∨ y i = -1)
    (k : ℕ) (hk : k ≤ Fintype.card A) (hA : 0 < Fintype.card A) :
    |(∑ e : Fin k ↪ A, ∏ i, y (e i)) / (Fintype.card A : ℝ) ^ k -
        ((∑ i, y i) / (Fintype.card A : ℝ)) ^ k| ≤
      (|((∑ i, y i) / (Fintype.card A : ℝ))| +
        Real.sqrt ((k : ℝ) * Fintype.card A) / Fintype.card A) ^ k -
      |((∑ i, y i) / (Fintype.card A : ℝ))| ^ k := by
  have hJ : (0 : ℝ) < Fintype.card A := by exact_mod_cast hA
  have h := div_le_div_of_nonneg_right (ternary_distinct_product_error y hy k hk)
    (pow_pos hJ k).le
  rw [div_pow, ← sub_div, abs_div, abs_of_pos (pow_pos hJ k)]
  apply h.trans_eq
  rw [sub_div, ← div_pow, ← div_pow, add_div, abs_div, abs_of_pos hJ]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_WeightedMomentShift
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A constant shift in a weighted integral moment -/

namespace Ostmann

open scoped BigOperators

/-- Minkowski for a countable weighted moment, stated without any measure
construction. The weights may have infinite support. -/
theorem weighted_moment_shift {ι : Type*} (w f : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hf : ∀ i, 0 ≤ f i) (b : ℝ) (hb : 0 ≤ b)
    (k : ℕ) (hk : 0 < k) (hws : Summable w)
    (hfs : Summable (fun i => w i * f i ^ k)) :
    Summable (fun i => w i * (f i + b) ^ k) ∧
      (∑' i, w i * (f i + b) ^ k) ≤
        ((∑' i, w i * f i ^ k) ^ (1 / (k : ℝ)) +
          b * (∑' i, w i) ^ (1 / (k : ℝ))) ^ k := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  let u : ι → ℝ := fun i => w i ^ (1 / (k : ℝ))
  have hu (i : ι) : 0 ≤ u i := Real.rpow_nonneg (hw i) _
  have hup (i : ι) : u i ^ k = w i := by
    simpa only [u, one_div] using Real.rpow_inv_natCast_pow (hw i) hk.ne'
  have hfa (i : ι) : (u i * f i) ^ (k : ℝ) = w i * f i ^ k := by
    rw [Real.rpow_natCast, mul_pow, hup]
  have hba (i : ι) : (u i * b) ^ (k : ℝ) = w i * b ^ k := by
    rw [Real.rpow_natCast, mul_pow, hup]
  have hsa (i : ι) : (u i * f i + u i * b) ^ (k : ℝ) = w i * (f i + b) ^ k := by
    rw [← mul_add, Real.rpow_natCast, mul_pow, hup]
  have hsumf : Summable (fun i => (u i * f i) ^ (k : ℝ)) := by simpa only [hfa] using hfs
  have hsumb : Summable (fun i => (u i * b) ^ (k : ℝ)) := by
    simpa only [hba] using hws.mul_right (b ^ k)
  obtain ⟨hs, hi⟩ := Real.Lp_add_le_tsum_of_nonneg hk1
    (fun i => mul_nonneg (hu i) (hf i)) (fun i => mul_nonneg (hu i) hb) hsumf hsumb
  simp only [hsa, hfa, hba] at hs hi
  have hI : 0 ≤ ∑' i, w i * (f i + b) ^ k :=
    tsum_nonneg (fun i => mul_nonneg (hw i) (pow_nonneg (add_nonneg (hf i) hb) _))
  have hconst : (∑' i, w i * b ^ k) ^ (1 / (k : ℝ)) =
      b * (∑' i, w i) ^ (1 / (k : ℝ)) := by
    rw [tsum_mul_right, Real.mul_rpow (tsum_nonneg hw) (pow_nonneg hb k),
      one_div, Real.pow_rpow_inv_natCast hb hk.ne', mul_comm]
  rw [hconst] at hi
  refine ⟨hs, ?_⟩
  have hh := pow_le_pow_left₀ (Real.rpow_nonneg hI _) hi k
  rw [one_div, Real.rpow_inv_natCast_pow hI hk.ne'] at hh
  simpa only [one_div] using hh

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_WeightedRepeatRemoval
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing repeated primes inside the positive amplified moment -/

namespace Ostmann

open scoped BigOperators Classical

/-- A pointwise square-root shift controls the error in the weighted moment.
All quantities on the right are the actual unperturbed moments. -/
theorem weighted_power_approximation {ι : Type*} (w f D : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hf : ∀ i, 0 ≤ f i) (b : ℝ) (hb : 0 ≤ b)
    (k : ℕ) (hk : 0 < k) (hws : Summable w)
    (hfs : Summable (fun i => w i * f i ^ k))
    (hD : ∀ i, |D i - f i ^ k| ≤ (f i + b) ^ k - f i ^ k) :
    Summable (fun i => w i * D i) ∧
      |(∑' i, w i * D i) - (∑' i, w i * f i ^ k)| ≤
        ((∑' i, w i * f i ^ k) ^ (1 / (k : ℝ)) +
          b * (∑' i, w i) ^ (1 / (k : ℝ))) ^ k - (∑' i, w i * f i ^ k) := by
  obtain ⟨hs, hbnd⟩ := weighted_moment_shift w f hw hf b hb k hk hws hfs
  have hp (i : ι) : ‖w i * (D i - f i ^ k)‖ ≤
      w i * (f i + b) ^ k - w i * f i ^ k := by
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw i), ← mul_sub]
    exact mul_le_mul_of_nonneg_left (hD i) (hw i)
  have hen : Summable (fun i => ‖w i * (D i - f i ^ k)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hp (hs.sub hfs)
  have he : Summable (fun i => w i * (D i - f i ^ k)) :=
    Summable.of_norm_bounded (hs.sub hfs) hp
  have hd : Summable (fun i => w i * D i) := by
    simpa only [mul_sub, sub_add_cancel] using he.add hfs
  refine ⟨hd, ?_⟩
  calc
    |(∑' i, w i * D i) - (∑' i, w i * f i ^ k)| =
        ‖∑' i, w i * (D i - f i ^ k)‖ := by rw [← hd.tsum_sub hfs]; simp only [mul_sub, Real.norm_eq_abs]
    _ ≤ ∑' i, ‖w i * (D i - f i ^ k)‖ := norm_tsum_le_tsum_norm hen
    _ ≤ ∑' i, (w i * (f i + b) ^ k - w i * f i ^ k) :=
      hen.tsum_le_tsum hp (hs.sub hfs)
    _ = (∑' i, w i * (f i + b) ^ k) - (∑' i, w i * f i ^ k) := hs.tsum_sub hfs
    _ ≤ _ := sub_le_sub_right hbnd _

theorem ternaryMean_abs_le_one {A : Type*} [Fintype A]
    (y : A → ℝ) (hy : ∀ i, y i = 0 ∨ y i = 1 ∨ y i = -1) :
    |ternaryMean y| ≤ 1 := by
  by_cases hA : Fintype.card A = 0
  · simp [ternaryMean, hA]
  have hJ : (0 : ℝ) < Fintype.card A := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hA)
  rw [ternaryMean, abs_div, abs_of_pos hJ, div_le_one hJ]
  calc
    |∑ i, y i| ≤ ∑ i, |y i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : A, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      rcases hy i with h | h | h <;> simp [h]
    _ = _ := by simp

/-- Actual distinct-index averaging, with no assumed repeat-removal estimate. -/
theorem weighted_ternary_distinct_moment {ι A : Type*} [Fintype A] [DecidableEq A]
    (w : ι → ℝ) (y : ι → A → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hy : ∀ i a, y i a = 0 ∨ y i a = 1 ∨ y i a = -1)
    (k : ℕ) (hk : 0 < k) (heven : Even k) (hkA : k ≤ Fintype.card A)
    (hws : Summable w) :
    Summable (fun i => w i * ternaryDistinctMean (y i) k) ∧
      |(∑' i, w i * ternaryDistinctMean (y i) k) -
          (∑' i, w i * ternaryMean (y i) ^ k)| ≤
        ((∑' i, w i * ternaryMean (y i) ^ k) ^ (1 / (k : ℝ)) +
          (Real.sqrt ((k : ℝ) * Fintype.card A) / Fintype.card A) *
            (∑' i, w i) ^ (1 / (k : ℝ))) ^ k -
          (∑' i, w i * ternaryMean (y i) ^ k) := by
  have hA : 0 < Fintype.card A := lt_of_lt_of_le hk hkA
  have hf (i : ι) : |ternaryMean (y i)| ^ k ≤ 1 :=
    pow_le_one₀ (abs_nonneg _) (ternaryMean_abs_le_one (y i) (hy i))
  have hfs : Summable (fun i => w i * |ternaryMean (y i)| ^ k) := by
    apply Summable.of_nonneg_of_le (fun i => mul_nonneg (hw i) (pow_nonneg (abs_nonneg _) _))
      (fun i => ?_) hws
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (hf i) (hw i)
  have hh := weighted_power_approximation w (fun i => |ternaryMean (y i)|)
    (fun i => ternaryDistinctMean (y i) k) hw (fun _ => abs_nonneg _)
    (Real.sqrt ((k : ℝ) * Fintype.card A) / Fintype.card A) (by positivity)
    k hk hws hfs (fun i => by
      simpa only [ternaryDistinctMean, ternaryMean, heven.pow_abs] using
        normalized_ternary_distinct_product_error (y i) (hy i) k hkA hA)
  simpa only [heven.pow_abs] using hh

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_PhysicalMomentLower
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Jensen amplification of the actual translated-character biases -/

namespace Ostmann

open scoped BigOperators Classical

theorem ternaryMean_sum_lower {ι A : Type*} [Fintype A]
    (S : Finset ι) (y : ι → A → ℝ) (c : ℝ) (hA : 0 < Fintype.card A)
    (hy : ∀ a, (S.card : ℝ) * c ≤ ∑ i ∈ S, y i a) :
    (S.card : ℝ) * c ≤ ∑ i ∈ S, ternaryMean (y i) := by
  have hJ : (0 : ℝ) < Fintype.card A := by exact_mod_cast hA
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun a _ => hy a)
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Finset.sum_comm] at hs
  simp only [ternaryMean, ← Finset.sum_div]
  apply (le_div_iff₀ hJ).mpr
  nlinarith only [hs]

theorem finite_even_moment_lower {ι : Type*} (S : Finset ι) (f : ι → ℝ)
    (c : ℝ) (hc : 0 ≤ c) (k : ℕ) (heven : Even k)
    (hbias : (S.card : ℝ) * c ≤ ∑ i ∈ S, f i) :
    (S.card : ℝ) * c ^ k ≤ ∑ i ∈ S, f i ^ k := by
  by_cases hS : S.Nonempty
  · have hcard : (0 : ℝ) < S.card := by exact_mod_cast Finset.card_pos.mpr hS
    have hw : (∑ _i ∈ S, (S.card : ℝ)⁻¹) = 1 := by simp [hcard.ne']
    have hmean : c ≤ (S.card : ℝ)⁻¹ * ∑ i ∈ S, f i := by
      rw [← div_eq_inv_mul, le_div_iff₀ hcard]
      nlinarith only [hbias]
    have hj := Real.pow_arith_mean_le_arith_mean_pow_of_even S
      (fun _ => (S.card : ℝ)⁻¹) f (fun _ _ => inv_nonneg.mpr hcard.le) hw heven
    simp only [← Finset.mul_sum] at hj
    have hp := (pow_le_pow_left₀ hc hmean k).trans hj
    rw [← div_eq_inv_mul, le_div_iff₀ hcard] at hp
    nlinarith only [hp]
  · simp [Finset.not_nonempty_iff_eq_empty.mp hS]

/-- Positive weight on a finite endpoint tail amplifies its simultaneous
individual prime biases. The moment on the right is an actual infinite sum. -/
theorem weighted_finite_bias_moment {ι A : Type*} [Fintype A]
    (S : Finset ι) (w : ι → ℝ) (y : ι → A → ℝ) (c w₀ : ℝ)
    (k : ℕ) (heven : Even k) (hA : 0 < Fintype.card A)
    (hc : 0 ≤ c) (hw₀ : 0 ≤ w₀) (hw : ∀ i, 0 ≤ w i)
    (hwS : ∀ i ∈ S, w₀ ≤ w i) (hws : Summable w)
    (hy : ∀ i a, y i a = 0 ∨ y i a = 1 ∨ y i a = -1)
    (hbias : ∀ a, (S.card : ℝ) * c ≤ ∑ i ∈ S, y i a) :
    w₀ * S.card * c ^ k ≤ ∑' i, w i * ternaryMean (y i) ^ k := by
  have he (i : ι) : 0 ≤ ternaryMean (y i) ^ k := heven.pow_nonneg _
  have hfs : Summable (fun i => w i * ternaryMean (y i) ^ k) := by
    apply Summable.of_nonneg_of_le (fun i => mul_nonneg (hw i) (he i)) _ hws
    intro i
    have hpow : ternaryMean (y i) ^ k ≤ 1 := by
      rw [← heven.pow_abs]
      exact pow_le_one₀ (abs_nonneg _) (ternaryMean_abs_le_one (y i) (hy i))
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hpow (hw i)
  have hm := finite_even_moment_lower S (fun i => ternaryMean (y i)) c hc k heven
    (ternaryMean_sum_lower S y c hA hbias)
  calc
    w₀ * S.card * c ^ k = w₀ * ((S.card : ℝ) * c ^ k) := by ring
    _ ≤ w₀ * ∑ i ∈ S, ternaryMean (y i) ^ k := mul_le_mul_of_nonneg_left hm hw₀
    _ = ∑ i ∈ S, w₀ * ternaryMean (y i) ^ k := Finset.mul_sum _ _ _
    _ ≤ ∑ i ∈ S, w i * ternaryMean (y i) ^ k :=
      Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_right (hwS i hi) (he i))
    _ ≤ _ := hfs.sum_le_tsum S (fun i _ => mul_nonneg (hw i) (he i))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_ProgressionLiftCount
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform integer-lift counts in a residue class -/

namespace Ostmann

/-- A residue class has at most interval length / modulus + 1 representatives.
This form is uniform in the residue and works across zero. -/
theorem progression_Ico_card_le (lo hi q r : ℤ) (hlo : lo ≤ hi) (hq : 0 < q) :
    (((Finset.Ico lo hi).filter fun n => n ≡ r [ZMOD q]).card : ℚ) ≤
      ((hi : ℚ) - lo) / q + 1 := by
  let A : ℚ := ((lo : ℚ) - r) / q
  let B : ℚ := ((hi : ℚ) - r) / q
  have hcard := Int.Ico_filter_modEq_card lo hi hq r
  have hcast : (((Finset.Ico lo hi).filter fun n => n ≡ r [ZMOD q]).card : ℚ) =
      max (((⌈B⌉ : ℤ) : ℚ) - ((⌈A⌉ : ℤ) : ℚ)) 0 := by
    dsimp [A, B]
    exact_mod_cast hcard
  have ha : A ≤ (⌈A⌉ : ℤ) := Int.le_ceil A
  have hb : ((⌈B⌉ : ℤ) : ℚ) < B + 1 := Int.ceil_lt_add_one B
  have hdiff : ((⌈B⌉ : ℤ) : ℚ) - ((⌈A⌉ : ℤ) : ℚ) ≤
      ((hi : ℚ) - lo) / q + 1 := by
    calc
      _ ≤ B - A + 1 := by linarith
      _ = _ := by dsimp [A, B]; ring
  have hq' : (0 : ℚ) < q := by exact_mod_cast hq
  have hwidth : (0 : ℚ) ≤ (hi : ℚ) - lo := by exact_mod_cast sub_nonneg.mpr hlo
  rw [hcast]
  exact max_le hdiff (by positivity)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityCRTProduct
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Constructing the density product and its Fourier hypotheses -/

namespace Ostmann

open scoped BigOperators

theorem densityCRTList_intCast (ps : List ℕ) (hp : ∀ p ∈ ps, p.Prime)
    (hc : ps.Pairwise Nat.Coprime) (S : ∀ p : ℕ, Finset (ZMod p)) (n : ℤ) :
    let : NeZero ps.prod := ⟨(prime_list_prod_pos ps hp).ne'⟩
    (densityCRTList ps hp hc S).value (n : ZMod ps.prod) =
      (ps.map fun p => (centeredDensity (S p) (n : ZMod p) : ℂ)).prod := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    have hp' : ∀ q ∈ ps, q.Prime := fun q hq => hp q (List.mem_cons_of_mem p hq)
    have hcp := List.pairwise_cons.mp hc
    let : Fact p.Prime := ⟨hp p List.mem_cons_self⟩
    let : NeZero ps.prod := ⟨(prime_list_prod_pos ps hp').ne'⟩
    change (centeredDensity (S p)
      ((ZMod.chineseRemainder (Nat.coprime_list_prod_right_iff.mpr hcp.1)) (n : ZMod (p * ps.prod))).1 : ℂ) *
      (densityCRTList ps hp' hcp.2 S).value
        ((ZMod.chineseRemainder (Nat.coprime_list_prod_right_iff.mpr hcp.1)) (n : ZMod (p * ps.prod))).2 = _
    rw [map_intCast]
    change (centeredDensity (S p) (n : ZMod p) : ℂ) *
      (densityCRTList ps hp' hcp.2 S).value (n : ZMod ps.prod) = _
    rw [ih hp' hcp.2]
    rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_PrimeCRTFourier
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Multiplying the local correlation bounds over the prime factors -/

namespace Ostmann

open scoped BigOperators ComplexConjugate

theorem primeCRTFunction_intCast (ps : List ℕ) (hp : ∀ p ∈ ps, p.Prime)
    (hc : ps.Pairwise Nat.Coprime) (F : ∀ p : ℕ, ZMod p → ℂ) (n : ℤ) :
    primeCRTFunction ps hp hc F (n : ZMod ps.prod) = (ps.map fun p => F p (n : ZMod p)).prod := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    have hp' : ∀ q ∈ ps, q.Prime := fun q hq => hp q (List.mem_cons_of_mem p hq)
    have hcp := List.pairwise_cons.mp hc
    change F p ((ZMod.chineseRemainder (Nat.coprime_list_prod_right_iff.mpr hcp.1))
      (n : ZMod (p * ps.prod))).1 * primeCRTFunction ps hp' hcp.2 F
        ((ZMod.chineseRemainder (Nat.coprime_list_prod_right_iff.mpr hcp.1))
          (n : ZMod (p * ps.prod))).2 = _
    rw [map_intCast]
    change F p (n : ZMod p) * primeCRTFunction ps hp' hcp.2 F (n : ZMod ps.prod) = _
    rw [ih hp' hcp.2]
    rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_PrimeSetQuadratic
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual quadratic density sums indexed by prime divisors -/

namespace Ostmann

open scoped BigOperators ComplexConjugate SchwartzMap

theorem primeSet_prod_le_of_subset (P U : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hU : U ⊆ P) : U.toList.prod ≤ P.toList.prod := by
  have he (Q : Finset ℕ) : Q.toList.prod = ∏ p ∈ Q, p := by
    simp
  rw [he, he]
  exact Finset.prod_le_prod_of_subset_of_one_le hU (fun _ _ => Nat.zero_le _)
    (fun p hp _ => (hP p hp).one_lt.le)

theorem primeSet_prod_dvd_of_subset (P U : Finset ℕ) (hU : U ⊆ P) :
    U.toList.prod ∣ P.toList.prod := by
  simpa using Finset.prod_dvd_prod_of_subset U P (fun p : ℕ => p) hU

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_AmplificationWeight
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original positive periodic amplification weight -/

namespace Ostmann

open scoped BigOperators Classical

theorem amplificationWeight_pos (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (D : ∀ p : ℕ, Finset (ZMod p)) (n : ℤ) :
    0 < amplificationWeight Q D n := by
  apply Finset.prod_pos
  intro p hp
  let : NeZero p := ⟨(hQ p hp).ne_zero⟩
  have hh := (abs_le.mp (centeredDensity_abs_le (D p) (n : ZMod p))).1
  linarith

theorem amplificationWeight_le (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (D : ∀ p : ℕ, Finset (ZMod p)) (n : ℤ) :
    amplificationWeight Q D n ≤ (17 / 16 : ℝ) ^ Q.card := by
  unfold amplificationWeight
  calc
    _ ≤ ∏ _p ∈ Q, (17 / 16 : ℝ) := by
      apply Finset.prod_le_prod
      · intro p hp
        let : NeZero p := ⟨(hQ p hp).ne_zero⟩
        have hh := (abs_le.mp (centeredDensity_abs_le (D p) (n : ZMod p))).1
        linarith
      · intro p hp
        let : NeZero p := ⟨(hQ p hp).ne_zero⟩
        have hh := (abs_le.mp (centeredDensity_abs_le (D p) (n : ZMod p))).2
        linarith
    _ = _ := by rw [Finset.prod_const]

theorem amplificationWeight_lower (Q : Finset ℕ)
    (D : ∀ p : ℕ, Finset (ZMod p)) (n : ℤ)
    (hD : ∀ p ∈ Q, (D p).card / (p : ℝ) ≤ 2 / 3)
    (hn : ∀ p ∈ Q, (n : ZMod p) ∈ D p) :
    (49 / 48 : ℝ) ^ Q.card ≤ amplificationWeight Q D n := by
  rw [amplificationWeight, ← Finset.prod_const]
  apply Finset.prod_le_prod (fun _ _ => by norm_num)
  intro p hp
  have hd := hD p hp
  rw [centeredDensity, ite_eq_left (hn p hp)]
  linarith

theorem exp_le_amplificationWeight (Q : Finset ℕ)
    (D : ∀ p : ℕ, Finset (ZMod p)) (n : ℤ)
    (hD : ∀ p ∈ Q, (D p).card / (p : ℝ) ≤ 2 / 3)
    (hn : ∀ p ∈ Q, (n : ZMod p) ∈ D p) :
    Real.exp ((Q.card : ℝ) / 50) ≤ amplificationWeight Q D n := by
  have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 49 / 48)
  have hlog : (1 / 50 : ℝ) ≤ Real.log (49 / 48) := by norm_num at hh ⊢; linarith
  apply le_trans _ (amplificationWeight_lower Q D n hD hn)
  calc
    _ ≤ Real.exp ((Q.card : ℝ) * Real.log (49 / 48)) := by
      apply Real.exp_le_exp.mpr
      nlinarith [Nat.cast_nonneg (α := ℝ) Q.card]
    _ = (49 / 48 : ℝ) ^ Q.card := by
      simpa only [Real.exp_log (by norm_num : (0 : ℝ) < 49 / 48)] using
        Real.exp_nat_mul (Real.log (49 / 48)) Q.card

theorem primeDivisorDensity_intCast (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (D : ∀ p : ℕ, Finset (ZMod p)) (U : Finset ℕ) (hU : U ⊆ Q) (n : ℤ) :
    primeDivisorDensity Q hQ D U (n : ZMod U.toList.prod) =
      ∏ p ∈ U, (centeredDensity (D p) (n : ZMod p) : ℂ) := by
  rw [primeDivisorDensity, dite_eq_left hU]
  simpa using densityCRTList_intCast U.toList
    (primeSet_list_prime U (fun p hp => hQ p (hU hp)))
    (primeSet_list_coprime U (fun p hp => hQ p (hU hp))) D n

/-- Exact divisor expansion, with the same CRT density functions as those
already used in the Fourier coefficient construction. -/
theorem amplificationWeight_expansion (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (D : ∀ p : ℕ, Finset (ZMod p)) (n : ℤ) :
    (amplificationWeight Q D n : ℂ) =
      ∑ U ∈ Q.powerset, (1 / 16 : ℂ) ^ U.card *
        primeDivisorDensity Q hQ D U (n : ZMod U.toList.prod) := by
  unfold amplificationWeight
  push_cast
  simp_rw [add_comm (1 : ℂ)]
  rw [Finset.prod_add_one]
  apply Finset.sum_congr rfl
  intro U hU
  rw [primeDivisorDensity_intCast Q hQ D U (Finset.mem_powerset.mp hU) n,
    Finset.prod_mul_distrib, Finset.prod_const]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_PhysicalAmplification
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original physical-space amplified moment -/

namespace Ostmann

open scoped BigOperators SchwartzMap

theorem orientedQuadraticValue_ternary (ε : ℕ → ℝ) (t : ℕ → ℤ) (n : ℤ) (p : ℕ)
    (hε : ε p = 1 ∨ ε p = -1) :
    orientedQuadraticValue ε t n p = 0 ∨ orientedQuadraticValue ε t n p = 1 ∨
      orientedQuadraticValue ε t n p = -1 := by
  rcases hε with h | h <;>
    rcases jacobiSym.trichotomy (n - t p) p with hχ | hχ | hχ <;>
    simp [orientedQuadraticValue, h, hχ]

theorem physicalWeight_nonneg (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (D : ∀ p : ℕ, Finset (ZMod p)) (ψ : 𝓢(ℝ, ℂ)) (hψ : ∀ x, 0 ≤ (ψ x).re)
    (X : ℝ) (n : ℤ) : 0 ≤ physicalWeight Q D ψ X n :=
  mul_nonneg (hψ _) (amplificationWeight_pos Q hQ D n).le

theorem physicalWeight_summable (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (D : ∀ p : ℕ, Finset (ZMod p)) (ψ : 𝓢(ℝ, ℂ)) (X : ℝ) (hX : 0 < X) :
    Summable (physicalWeight Q D ψ X) := by
  have hsn : Summable (fun n : ℤ => ‖ψ ((n : ℝ) / X)‖) := by
    simpa only [positiveDilate_apply, div_eq_mul_inv, mul_comm] using
      schwartz_int_norm_summable (positiveDilate ψ X⁻¹ (inv_pos.mpr hX))
  apply Summable.of_norm_bounded (hsn.mul_right ((17 / 16 : ℝ) ^ Q.card))
  intro n
  rw [physicalWeight, Real.norm_eq_abs, abs_mul,
    abs_of_pos (amplificationWeight_pos Q hQ D n)]
  exact mul_le_mul (Complex.abs_re_le_norm _) (amplificationWeight_le Q hQ D n)
    (amplificationWeight_pos Q hQ D n).le (norm_nonneg _)

theorem physicalWeight_lower (Q : Finset ℕ)
    (D : ∀ p : ℕ, Finset (ZMod p)) (ψ : 𝓢(ℝ, ℂ)) (X cψ : ℝ)
    (hX : 0 < X) (hcψ : 0 ≤ cψ) (hψ : ∀ x ∈ Set.Icc (0 : ℝ) 1, cψ ≤ (ψ x).re)
    (n : ℤ) (hn0 : 0 ≤ (n : ℝ)) (hnX : (n : ℝ) ≤ X)
    (hD : ∀ p ∈ Q, (D p).card / (p : ℝ) ≤ 2 / 3)
    (hn : ∀ p ∈ Q, (n : ZMod p) ∈ D p) :
    cψ * Real.exp ((Q.card : ℝ) / 50) ≤ physicalWeight Q D ψ X n := by
  have hψ' := hψ ((n : ℝ) / X) ⟨div_nonneg hn0 hX.le, (div_le_one hX).mpr hnX⟩
  exact mul_le_mul hψ' (exp_le_amplificationWeight Q D n hD hn)
    (Real.exp_nonneg _) (hcψ.trans hψ')

theorem physical_moment_from_tail_bias
    (Q P : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime) (hP : 0 < P.card)
    (D : ∀ p : ℕ, Finset (ZMod p)) (ψ : 𝓢(ℝ, ℂ)) (X cψ c : ℝ)
    (hX : 0 < X) (hcψ : 0 ≤ cψ) (hc : 0 ≤ c)
    (hψ0 : ∀ x, 0 ≤ (ψ x).re)
    (hψ1 : ∀ x ∈ Set.Icc (0 : ℝ) 1, cψ ≤ (ψ x).re)
    (S : Finset ℤ) (hS : ∀ n ∈ S, 0 ≤ (n : ℝ) ∧ (n : ℝ) ≤ X)
    (hD : ∀ p ∈ Q, (D p).card / (p : ℝ) ≤ 2 / 3)
    (hSD : ∀ n ∈ S, ∀ p ∈ Q, (n : ZMod p) ∈ D p)
    (ε : ℕ → ℝ) (t : ℕ → ℤ) (hε : ∀ p ∈ P, ε p = 1 ∨ ε p = -1)
    (hbias : ∀ p ∈ P, (S.card : ℝ) * c ≤ ∑ n ∈ S, orientedQuadraticValue ε t n p)
    (k : ℕ) (heven : Even k) :
    (cψ * Real.exp ((Q.card : ℝ) / 50)) * S.card * c ^ k ≤
      ∑' n : ℤ, physicalWeight Q D ψ X n *
        ternaryMean (fun p : P => orientedQuadraticValue ε t n p) ^ k := by
  apply weighted_finite_bias_moment S (physicalWeight Q D ψ X)
    (fun n (p : P) => orientedQuadraticValue ε t n p) c
    (cψ * Real.exp ((Q.card : ℝ) / 50)) k heven (by simpa using hP) hc (by positivity)
    (physicalWeight_nonneg Q hQ D ψ hψ0 X)
    (fun n hn => physicalWeight_lower Q D ψ X cψ hX hcψ hψ1 n
      (hS n hn).1 (hS n hn).2 hD (hSD n hn))
    (physicalWeight_summable Q hQ D ψ X hX)
    (fun n p => orientedQuadraticValue_ternary ε t n p (hε p p.property))
    (fun p => hbias p p.property)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_AmplificationMean
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The positive periodic amplification has mean one -/

namespace Ostmann

open scoped BigOperators

theorem primeCRTFunction_mean_one (ps : List ℕ) (hp : ∀ p ∈ ps, p.Prime)
    (hc : ps.Pairwise Nat.Coprime) (F : ∀ p : ℕ, ZMod p → ℂ)
    (hF : ∀ p (h : p ∈ ps), @additiveFourier p ⟨(hp p h).ne_zero⟩ (F p) 0 = 1) :
    let : NeZero ps.prod := ⟨(prime_list_prod_pos ps hp).ne'⟩
    additiveFourier (primeCRTFunction ps hp hc F) 0 = 1 := by
  induction ps with
  | nil =>
    intro _
    change @additiveFourier 1 _ (fun _ => 1) 0 = 1
    simp [additiveFourier_apply]
  | cons p ps ih =>
    have hp' : ∀ q ∈ ps, q.Prime := fun q hq => hp q (List.mem_cons_of_mem p hq)
    have hcp := List.pairwise_cons.mp hc
    let : NeZero p := ⟨(hp p List.mem_cons_self).ne_zero⟩
    let : NeZero ps.prod := ⟨(prime_list_prod_pos ps hp').ne'⟩
    change additiveFourier (fun x : ZMod (p * ps.prod) =>
      F p ((ZMod.chineseRemainder (Nat.coprime_list_prod_right_iff.mpr hcp.1)) x).1 *
      primeCRTFunction ps hp' hcp.2 F
        ((ZMod.chineseRemainder (Nat.coprime_list_prod_right_iff.mpr hcp.1)) x).2) 0 = 1
    rw [additiveFourier_crt (m := p) (n := ps.prod)]
    simp only [map_zero, Prod.fst_zero, Prod.snd_zero, mul_zero]
    rw [hF p List.mem_cons_self,
      ih hp' hcp.2 (fun q hq => hF q (List.mem_cons_of_mem p hq)), mul_one]

theorem amplificationCRT_intCast (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (D : ∀ p : ℕ, Finset (ZMod p)) (n : ℤ) :
    amplificationCRT Q hQ D (n : ZMod Q.toList.prod) = (amplificationWeight Q D n : ℂ) := by
  rw [amplificationCRT, primeCRTFunction_intCast, amplificationWeight]
  push_cast
  simp

theorem amplificationCRT_mean_one (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (D : ∀ p : ℕ, Finset (ZMod p)) :
    let : NeZero Q.toList.prod := ⟨(prime_list_prod_pos _ (primeSet_list_prime Q hQ)).ne'⟩
    additiveFourier (amplificationCRT Q hQ D) 0 = 1 := by
  apply primeCRTFunction_mean_one
  intro p hp
  let : NeZero p := ⟨(primeSet_list_prime Q hQ p hp).ne_zero⟩
  have hsum : (∑ x : ZMod p, (centeredDensity (D p) x : ℂ)) = 0 := by
    rw [← Complex.ofReal_sum, centeredDensity_sum, Complex.ofReal_zero]
  rw [additiveFourier_apply]
  simp only [mul_zero, neg_zero, AddChar.map_zero_eq_one, mul_one,
    Finset.sum_add_distrib, ← Finset.mul_sum, hsum, mul_zero, add_zero,
    Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, mul_one]
  exact inv_mul_cancel₀ (by exact_mod_cast (primeSet_list_prime Q hQ p hp).ne_zero)

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

theorem periodic_poisson_single_frequency {N : ℕ} [NeZero N]
    (F : ZMod N → ℂ) (ψ : 𝓢(ℝ, ℂ)) (X H : ℝ) (hX : 0 < X)
    (hmean : additiveFourier F 0 = 1) (hH : H < X / N)
    (hsupp : ∀ x : ℝ, H < |x| → 𝓕 ψ x = 0) :
    (∑' n : ℤ, F (n : ZMod N) * ψ ((n : ℝ) / X)) = (X : ℂ) * 𝓕 ψ 0 := by
  rw [scaled_periodic_poisson F ψ X hX]
  have hn (n : ℤ) (hne : n ≠ 0) :
      𝓕 ψ ((n : ℝ) * X / N) * additiveFourier F (-(n : ZMod N)) = 0 := by
    have habs : (1 : ℝ) ≤ |(n : ℝ)| := by
      exact_mod_cast (show (1 : ℤ) ≤ |n| by have hh := abs_pos.mpr hne; omega)
    have hN : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
    have hlarge : H < |(n : ℝ) * X / N| := by
      rw [abs_div, abs_mul, abs_of_pos hX, abs_of_pos hN]
      have hb := mul_le_mul_of_nonneg_right habs (div_nonneg hX.le hN.le)
      have he : |(n : ℝ)| * X / N = |(n : ℝ)| * (X / N) := by ring
      rw [he]
      exact hH.trans_le (by simpa only [one_mul] using hb)
    rw [hsupp _ hlarge, zero_mul]
  rw [tsum_eq_single 0 hn]
  simp [hmean]

/-- Exact form of the total-weight identity for the manuscript's original
positive periodic weight. -/
theorem amplification_total_weight (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (D : ∀ p : ℕ, Finset (ZMod p)) (ψ : 𝓢(ℝ, ℂ)) (X H : ℝ) (hX : 0 < X)
    (hH : H < X / Q.toList.prod) (hsupp : ∀ x : ℝ, H < |x| → 𝓕 ψ x = 0) :
    (∑' n : ℤ, physicalWeight Q D ψ X n) = X * (𝓕 ψ 0).re := by
  let : NeZero Q.toList.prod := ⟨(prime_list_prod_pos _ (primeSet_list_prime Q hQ)).ne'⟩
  have hp := periodic_poisson_single_frequency (amplificationCRT Q hQ D) ψ X H hX
    (amplificationCRT_mean_one Q hQ D) hH hsupp
  have hsc : Summable (fun n : ℤ => amplificationCRT Q hQ D (n : ZMod Q.toList.prod) * ψ ((n : ℝ) / X)) := by
    have hsn : Summable (fun n : ℤ => ‖ψ ((n : ℝ) / X)‖) := by
      simpa only [positiveDilate_apply, div_eq_mul_inv, mul_comm] using
        schwartz_int_norm_summable (positiveDilate ψ X⁻¹ (inv_pos.mpr hX))
    apply Summable.of_norm_bounded (hsn.mul_left ((17 / 16 : ℝ) ^ Q.card))
    intro n
    rw [amplificationCRT_intCast, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (amplificationWeight_pos Q hQ D n)]
    exact mul_le_mul_of_nonneg_right (amplificationWeight_le Q hQ D n) (norm_nonneg _)
  have hre := congrArg Complex.reCLM hp
  rw [Complex.reCLM.map_tsum hsc] at hre
  simpa only [amplificationCRT_intCast, Complex.reCLM_apply, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, physicalWeight, mul_comm] using hre

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Supply_PrimeSubsetProducts
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Products of distinct primes index the amplified coefficient array -/

namespace Ostmann

open scoped BigOperators Classical

theorem primeSubset_product_injective (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) :
    Set.InjOn (fun Q : Finset ℕ => ∏ p ∈ Q, p) {Q | Q ⊆ P} := by
  intro Q hQ R hR heq
  have h := congrArg Nat.primeFactors heq
  rwa [Nat.primeFactors_prod (fun p hp => hP p (hQ hp)),
    Nat.primeFactors_prod (fun p hp => hP p (hR hp))] at h

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticFrequencyTerm
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The frequency summand and its exact quadratic normalization -/

namespace Ostmann

open scoped BigOperators SchwartzMap

theorem quadraticFrequencyTerm_zero_above {q : ℕ} [NeZero q]
    (g : ZMod q → ℂ) (a : ZMod q) (θ : ℝ) (Φ : 𝓢(ℝ, ℂ))
    (R H : ℝ) (N u : ℕ) (hR : 0 < R)
    (hN : H * R * q ≤ N) (hu : N < u)
    (hΦ : ∀ x : ℝ, H < x → Φ x = 0) :
    quadraticFrequencyTerm g a θ Φ R u = 0 := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hnu : (N : ℝ) < u := by exact_mod_cast hu
  have harg : H < (u : ℝ) / (R * q) := by
    apply (lt_div_iff₀ (mul_pos hR hqR)).mpr
    nlinarith
  simp only [quadraticFrequencyTerm, hΦ _ harg, mul_zero]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_SignedQuadraticFrequency
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The signed Fourier series and its positive-frequency half -/

namespace Ostmann

open scoped BigOperators ComplexConjugate SchwartzMap FourierTransform
open MeasureTheory

theorem densityFourier_conj {q : ℕ} [NeZero q] (f : ZMod q → ℂ)
    (hf : ∀ x, conj (f x) = f x) (a : ZMod q) :
    densityFourier f (-a) = conj (densityFourier f a) := by
  simp only [densityFourier, additiveFourier_apply, map_mul, map_sum, map_inv₀,
    map_natCast, Complex.conj_ofReal, stdAddChar_conj, hf, mul_neg, neg_neg]

theorem primeDivisorDensity_conj (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (D : ∀ p : ℕ, Finset (ZMod p)) (U : Finset ℕ) (hU : U ⊆ Q)
    (x : ZMod U.toList.prod) :
    conj (primeDivisorDensity Q hQ D U x) = primeDivisorDensity Q hQ D U x := by
  obtain ⟨n, rfl⟩ := ZMod.intCast_surjective x
  rw [primeDivisorDensity_intCast Q hQ D U hU]
  simp only [map_prod, Complex.conj_ofReal]

/-- Reality of the original physical cutoff supplies Hermitian symmetry of
its Fourier transform without any additional analytic input. -/
theorem fourier_real_conj (f : ℝ → ℂ) (hf : ∀ x, conj (f x) = f x) (ξ : ℝ) :
    𝓕 f (-ξ) = conj (𝓕 f ξ) := by
  rw [Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul,
    ← integral_conj]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [smul_eq_mul, map_mul, ← Complex.exp_conj, Complex.conj_ofReal,
    Complex.conj_I, hf]
  congr 2
  push_cast
  ring

theorem integerQuadraticFrequency_natCast {q : ℕ} [NeZero q]
    (g : ZMod q → ℂ) (a : ZMod q) (θ : ℝ) (Φ : 𝓢(ℝ, ℂ))
    (R : ℝ) (M u : ℕ) :
    integerQuadraticFrequency g a θ Φ R M u =
      (realJacobi u M : ℂ) * quadraticFrequencyTerm g a θ Φ R u := by
  simp only [integerQuadraticFrequency, quadraticFrequencyTerm, realJacobi,
    Int.cast_natCast]
  push_cast
  ring

theorem integerQuadraticFrequency_neg {q : ℕ} [NeZero q]
    (g : ZMod q → ℂ) (a : ZMod q) (θ : ℝ) (Φ : 𝓢(ℝ, ℂ))
    (R : ℝ) (M : ℕ) (hg : ∀ x, g (-x) = conj (g x))
    (hΦ : ∀ x, Φ (-x) = conj (Φ x)) (u : ℤ) :
    integerQuadraticFrequency g a θ Φ R M (-u) =
      (jacobiSym (-1) M : ℂ) * conj (integerQuadraticFrequency g a θ Φ R M u) := by
  have hj : jacobiSym (-u) M = jacobiSym (-1) M * jacobiSym u M := by
    rw [neg_eq_neg_one_mul, jacobiSym.mul_left]
  simp only [integerQuadraticFrequency, hj, Int.cast_mul, Int.cast_neg, mul_neg,
    neg_div, hg, hΦ, map_mul, ← conj_realAdditivePhase]
  simp only [← Complex.ofReal_intCast, Complex.conj_ofReal]
  ring

theorem integerQuadraticFrequency_split {q : ℕ} [NeZero q]
    (g : ZMod q → ℂ) (a : ZMod q) (θ : ℝ) (Φ : 𝓢(ℝ, ℂ))
    (R H : ℝ) (M N : ℕ) (hM : 1 < M) (hR : 0 < R)
    (hg : ∀ x, g (-x) = conj (g x)) (hΦ : ∀ x, Φ (-x) = conj (Φ x))
    (hcut : H * R * q ≤ N) (hsupp : ∀ x : ℝ, H < x → Φ x = 0) :
    (∑' u : ℤ, integerQuadraticFrequency g a θ Φ R M u) =
      (∑ u ∈ Finset.Icc 1 N,
        (realJacobi u M : ℂ) * quadraticFrequencyTerm g a θ Φ R u) +
      (jacobiSym (-1) M : ℂ) * conj (∑ u ∈ Finset.Icc 1 N,
        (realJacobi u M : ℂ) * quadraticFrequencyTerm g a θ Φ R u) := by
  have hh := integer_frequency_conjugate_split
    (integerQuadraticFrequency g a θ Φ R M) N (jacobiSym (-1) M : ℂ)
  simp_rw [integerQuadraticFrequency_natCast] at hh
  apply hh
  · simp only [integerQuadraticFrequency, jacobiSym.zero_left hM,
      Int.cast_zero, zero_mul]
  · intro n
    simpa only [integerQuadraticFrequency_natCast] using
      integerQuadraticFrequency_neg g a θ Φ R M hg hΦ n
  · intro n hn
    rw [quadraticFrequencyTerm_zero_above g a θ Φ R H N n hR hcut hn hsupp, mul_zero]

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

theorem jacobiComplex_natCast (M : ℕ) [NeZero M] (s : ℕ) :
    jacobiComplex M (s : ZMod M) = (realJacobi s M : ℂ) := by
  change ((jacobiCharacterInt M) (s : ZMod M) : ℂ) = ((jacobiSym (s : ℤ) M : ℝ) : ℂ)
  rw [← Int.cast_natCast s, jacobiCharacterInt_intCast]
  simp

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
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
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
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
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
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
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

theorem poisson_sqrt_normalizer (d M : ℕ) [NeZero d] [NeZero M]
    (X : ℝ) (hX : 0 < X) :
    (X : ℂ) / M * (Real.sqrt (d : ℝ) : ℂ)⁻¹ =
      (Real.sqrt X : ℂ) / (Real.sqrt (M : ℝ) : ℂ) *
        (Real.sqrt ((M : ℝ) / X * d) : ℂ)⁻¹ := by
  have hM : (0 : ℝ) < M := by exact_mod_cast NeZero.pos M
  have hd : (0 : ℝ) < d := by exact_mod_cast NeZero.pos d
  have hxC : (Real.sqrt X : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hX).ne'
  have hmC : (Real.sqrt (M : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hM).ne'
  have hdC : (Real.sqrt (d : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hd).ne'
  have hmc : (M : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne M
  have hx : (Real.sqrt X : ℂ) ^ 2 = X := by exact_mod_cast Real.sq_sqrt hX.le
  have hm : (Real.sqrt (M : ℝ) : ℂ) ^ 2 = M := by exact_mod_cast Real.sq_sqrt hM.le
  rw [Real.sqrt_mul (div_nonneg hM.le hX.le), Real.sqrt_div hM.le]
  push_cast
  field_simp
  rw [hx, hm, mul_comm]

/-- The scalar outside the signed frequency sum has modulus sqrt(X).
The translation is the actual CRT lift, not an independent phase parameter. -/
theorem normalized_jacobi_poisson {d M : ℕ} [NeZero d] [NeZero M]
    (hcop : d.Coprime M) (hM : Squarefree M) (hodd : Odd M)
    (f : ZMod d → ℂ) (t : ZMod M) (h₀ : ℕ)
    (hlift : (d : ℤ) ∣ (t.val : ℤ) + (M : ℤ) * h₀)
    (ψ : 𝓢(ℝ, ℂ)) (X : ℝ) (hX : 0 < X) :
    (∑' n : ℤ, f (n : ZMod d) * (jacobiSym ((n : ℤ) - t.val) M : ℂ) *
        ψ ((n : ℝ) / X)) =
      (Real.sqrt X : ℂ) * jacobiGaussPhase M * (realJacobi d M : ℂ) *
        ((Real.sqrt ((M : ℝ) / X * d) : ℂ)⁻¹ *
          ∑' u : ℤ, integerQuadraticFrequency (densityFourier f)
            (-(M : ZMod d)⁻¹) ((h₀ : ℝ) + (t.val : ℝ) / M)
            (𝓕 ψ) ((M : ℝ) / X) M u) := by
  have hp := scaled_quadratic_character_poisson hcop f (jacobiComplex M)
    (jacobiComplex_squarefree_primitive M hM hodd) (jacobiComplex_isQuadratic M) t ψ X hX
  have ht (n : ℤ) : (jacobiComplex M) ((n : ZMod M) - t) =
      (jacobiSym (n - t.val) M : ℂ) := by
    rw [show (n : ZMod M) - t = ((n - t.val : ℤ) : ZMod M) by simp]
    exact jacobiComplex_intCast M _
  simp_rw [ht] at hp
  rw [hp]
  have hs : (Real.sqrt (d : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by exact_mod_cast NeZero.pos d : (0 : ℝ) < d)).ne'
  have he (u : ℤ) :
      𝓕 ψ ((u : ℝ) * X / (d * M : ℕ)) *
        additiveFourier f (-((M : ZMod d)⁻¹ * (u : ZMod d))) *
        ZMod.stdAddChar (t * ((d : ZMod M)⁻¹ * (u : ZMod M))) *
        jacobiComplex M (d : ZMod M) * jacobiComplex M (u : ZMod M) =
      ((realJacobi d M : ℂ) * (Real.sqrt (d : ℝ) : ℂ)⁻¹) *
        integerQuadraticFrequency (densityFourier f) (-(M : ZMod d)⁻¹)
          ((h₀ : ℝ) + (t.val : ℝ) / M) (𝓕 ψ) ((M : ℝ) / X) M u := by
    have harg : (u : ℝ) * X / (d * M : ℕ) = u / ((M : ℝ) / X * d) := by
      have hm : (M : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne M
      have hd : (d : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne d
      push_cast
      field_simp
    rw [crt_translation_phase hcop t (h₀ : ℤ) u hlift,
      jacobiComplex_natCast, jacobiComplex_intCast, harg]
    simp only [integerQuadraticFrequency, densityFourier, neg_mul, Int.cast_natCast,
      add_comm (h₀ : ℝ)]
    field_simp
  simp_rw [he]
  rw [tsum_mul_left]
  calc
    _ = ((X : ℂ) / M * (Real.sqrt (d : ℝ) : ℂ)⁻¹) *
        gaussSum (jacobiComplex M) ZMod.stdAddChar * (realJacobi d M : ℂ) *
        ∑' u : ℤ, integerQuadraticFrequency (densityFourier f) (-(M : ZMod d)⁻¹)
          ((h₀ : ℝ) + (t.val : ℝ) / M) (𝓕 ψ) ((M : ℝ) / X) M u := by ring
    _ = _ := by
      rw [poisson_sqrt_normalizer d M X hX]
      unfold jacobiGaussPhase
      ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_PrimeSetDivisorSum
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Divisor sums of the actual squarefree prime-set modulus -/

namespace Ostmann

open scoped BigOperators

theorem primeSet_modulus_squarefree (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime) :
    Squarefree Q.toList.prod := by
  simpa using primeSubset_product_squarefree Q hQ

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_OriginalSignedFourier
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The positive half of the original signed Fourier expression -/

namespace Ostmann

open scoped BigOperators ComplexConjugate SchwartzMap

theorem primeDivisorSignedFrequency_split (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (D : ∀ p : ℕ, Finset (ZMod p)) (U : Finset ℕ) (hU : U ⊆ Q)
    (M N h₀ : ℕ) (θ R H : ℝ) (Φ : 𝓢(ℝ, ℂ))
    (hM : 1 < M) (hR : 0 < R) (hcut : H * R * U.toList.prod ≤ N)
    (hΦ : ∀ x, Φ (-x) = conj (Φ x)) (hsupp : ∀ x : ℝ, H < x → Φ x = 0) :
    primeDivisorSignedFrequency Q hQ D U M h₀ θ R Φ =
      primeDivisorFrequency Q hQ D U M N h₀ θ R Φ +
      (jacobiSym (-1) M : ℂ) * conj (primeDivisorFrequency Q hQ D U M N h₀ θ R Φ) := by
  let : NeZero U.toList.prod := ⟨(prime_list_prod_pos _
    (primeSet_list_prime U (fun p hp => hQ p (hU hp)))).ne'⟩
  have he := integerQuadraticFrequency_split
    (densityFourier (primeDivisorDensity Q hQ D U)) (quadraticInverseResidue M U)
    ((h₀ : ℝ) + θ) Φ R H M N hM hR
    (densityFourier_conj _ (primeDivisorDensity_conj Q hQ D U hU)) hΦ hcut hsupp
  simp only [primeDivisorSignedFrequency, primeDivisorFrequency, dite_eq_left hU]
  rw [he]
  simp only [primeDivisorDensity, dite_eq_left hU, map_mul, map_inv₀, Complex.conj_ofReal]
  ring

theorem quadraticSymbolCoefficient_conj (M : ℕ) (U : Finset ℕ) :
    conj (quadraticSymbolCoefficient M U) = quadraticSymbolCoefficient M U := by
  simp only [quadraticSymbolCoefficient, map_mul, map_pow, Complex.conj_ofReal]

/-- The entire divisor sum has a common conjugation sign. Thus the positive
half controls the signed expression before any absolute values are distributed. -/
theorem originalSignedFourier_split (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (D : ∀ p : ℕ, Finset (ZMod p)) (M N h₀ : ℕ)
    (θ R H : ℝ) (Φ : 𝓢(ℝ, ℂ)) (hM : 1 < M) (hR : 0 < R) (hH : 0 ≤ H)
    (hcut : H * R * Q.toList.prod ≤ N)
    (hΦ : ∀ x, Φ (-x) = conj (Φ x)) (hsupp : ∀ x : ℝ, H < x → Φ x = 0) :
    originalSignedFourier Q hQ D M h₀ θ R Φ =
      originalPositiveFourier Q hQ D M N h₀ θ R Φ +
      (jacobiSym (-1) M : ℂ) * conj (originalPositiveFourier Q hQ D M N h₀ θ R Φ) := by
  unfold originalSignedFourier originalPositiveFourier
  simp only [map_sum, map_mul, quadraticSymbolCoefficient_conj]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro U hU
  have hsub := Finset.mem_powerset.mp hU
  have hcutU := (mul_le_mul_of_nonneg_left
    (Nat.cast_le.mpr (primeSet_prod_le_of_subset Q U hQ hsub)) (mul_nonneg hH hR.le)).trans hcut
  rw [primeDivisorSignedFrequency_split Q hQ D U hsub M N h₀ θ R H Φ
    hM hR hcutU hΦ hsupp]
  ring

theorem originalSignedFourier_norm_le (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (D : ∀ p : ℕ, Finset (ZMod p)) (M N h₀ : ℕ)
    (θ R H : ℝ) (Φ : 𝓢(ℝ, ℂ)) (hM : 1 < M) (hR : 0 < R) (hH : 0 ≤ H)
    (hcut : H * R * Q.toList.prod ≤ N)
    (hΦ : ∀ x, Φ (-x) = conj (Φ x)) (hsupp : ∀ x : ℝ, H < x → Φ x = 0) :
    ‖originalSignedFourier Q hQ D M h₀ θ R Φ‖ ≤
      2 * ‖originalPositiveFourier Q hQ D M N h₀ θ R Φ‖ := by
  rw [originalSignedFourier_split Q hQ D M N h₀ θ R H Φ hM hR hH hcut hΦ hsupp]
  apply (norm_add_le _ _).trans
  rw [norm_mul, Complex.norm_conj]
  have hc : ‖(jacobiSym (-1) M : ℂ)‖ ≤ 1 := by
    rcases jacobiSym.trichotomy (-1) M with h | h | h <;> rw [h] <;> norm_num
  nlinarith [norm_nonneg (originalPositiveFourier Q hQ D M N h₀ θ R Φ)]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_AmplifiedCharacterPoisson
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Poisson transfer of the original amplified character sum -/

namespace Ostmann

open scoped BigOperators SchwartzMap FourierTransform ComplexConjugate

theorem bounded_schwartz_lattice_summable (b : ℤ → ℂ) (B : ℝ)
    (hb : ∀ n, ‖b n‖ ≤ B) (ψ : 𝓢(ℝ, ℂ)) (X : ℝ) (hX : 0 < X) :
    Summable (fun n : ℤ => b n * ψ ((n : ℝ) / X)) := by
  have hsn : Summable (fun n : ℤ => ‖ψ ((n : ℝ) / X)‖) := by
    simpa only [positiveDilate_apply, div_eq_mul_inv, mul_comm] using
      schwartz_int_norm_summable (positiveDilate ψ X⁻¹ (inv_pos.mpr hX))
  apply Summable.of_norm_bounded (hsn.mul_left B)
  intro n
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hb n) (norm_nonneg _)

theorem norm_jacobiComplex_int_le (n : ℤ) (M : ℕ) : ‖(jacobiSym n M : ℂ)‖ ≤ 1 := by
  rcases jacobiSym.trichotomy n M with h | h | h <;> rw [h] <;> norm_num

theorem primeDivisorDensity_norm (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (D : ∀ p : ℕ, Finset (ZMod p)) (U : Finset ℕ) (hU : U ⊆ Q)
    (x : ZMod U.toList.prod) : ‖primeDivisorDensity Q hQ D U x‖ ≤ 1 := by
  let : NeZero U.toList.prod := ⟨(prime_list_prod_pos _
    (primeSet_list_prime U (fun p hp => hQ p (hU hp)))).ne'⟩
  rw [primeDivisorDensity, dite_eq_left hU]
  exact (densityCRTList U.toList (primeSet_list_prime U (fun p hp => hQ p (hU hp)))
    (primeSet_list_coprime U (fun p hp => hQ p (hU hp))) D).norm_le_one x

theorem amplified_jacobi_poisson (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (D : ∀ p : ℕ, Finset (ZMod p)) (M h₀ : ℕ) [NeZero M]
    (hcop : Q.toList.prod.Coprime M) (hM : Squarefree M) (hodd : Odd M)
    (t : ZMod M) (hlift : (Q.toList.prod : ℤ) ∣ (t.val : ℤ) + (M : ℤ) * h₀)
    (ψ : 𝓢(ℝ, ℂ)) (X : ℝ) (hX : 0 < X) :
    (∑' n : ℤ, (amplificationWeight Q D n : ℂ) *
        (jacobiSym (n - t.val) M : ℂ) * ψ ((n : ℝ) / X)) =
      (Real.sqrt X : ℂ) * jacobiGaussPhase M *
        originalSignedFourier Q hQ D M h₀ ((t.val : ℝ) / M) ((M : ℝ) / X) (𝓕 ψ) := by
  classical
  have hsum (U : Finset ℕ) (hU : U ∈ Q.powerset) : Summable (fun n : ℤ =>
      (1 / 16 : ℂ) ^ U.card * (primeDivisorDensity Q hQ D U (n : ZMod U.toList.prod) *
        (jacobiSym (n - t.val) M : ℂ) * ψ ((n : ℝ) / X))) := by
    apply Summable.mul_left
    apply bounded_schwartz_lattice_summable _ 1 _ ψ X hX
    intro n
    rw [norm_mul]
    exact (mul_le_mul (primeDivisorDensity_norm Q hQ D U (Finset.mem_powerset.mp hU) _)
      (norm_jacobiComplex_int_le _ M) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  calc
    _ = ∑' n : ℤ, ∑ U ∈ Q.powerset,
        (1 / 16 : ℂ) ^ U.card * (primeDivisorDensity Q hQ D U (n : ZMod U.toList.prod) *
          (jacobiSym (n - t.val) M : ℂ) * ψ ((n : ℝ) / X)) := by
      apply tsum_congr
      intro n
      rw [amplificationWeight_expansion Q hQ D n, Finset.sum_mul, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro U _
      ring
    _ = ∑ U ∈ Q.powerset, (1 / 16 : ℂ) ^ U.card *
        ∑' n : ℤ, primeDivisorDensity Q hQ D U (n : ZMod U.toList.prod) *
          (jacobiSym (n - t.val) M : ℂ) * ψ ((n : ℝ) / X) := by
      rw [Summable.tsum_finsetSum hsum]
      simp only [tsum_mul_left]
    _ = _ := by
      unfold originalSignedFourier
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro U hU
      have hsub := Finset.mem_powerset.mp hU
      have hd := primeSet_prod_dvd_of_subset Q U hsub
      let : NeZero U.toList.prod := ⟨(prime_list_prod_pos _
        (primeSet_list_prime U (fun p hp => hQ p (hsub hp)))).ne'⟩
      have hdu : (U.toList.prod : ℤ) ∣ (Q.toList.prod : ℤ) := by exact_mod_cast hd
      rw [normalized_jacobi_poisson (hcop.of_dvd_left hd) hM hodd
        (primeDivisorDensity Q hQ D U) t h₀ (hdu.trans hlift) ψ X hX]
      simp only [primeDivisorSignedFrequency, dite_eq_left hsub,
        quadraticSymbolCoefficient, quadraticInverseResidue]
      push_cast
      ring

/-- The actual amplified physical sum is controlled by the original positive
Fourier statistic with its exact square-root scale. -/
theorem amplified_jacobi_positive_bound (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (D : ∀ p : ℕ, Finset (ZMod p)) (M N h₀ : ℕ) [NeZero M]
    (hcop : Q.toList.prod.Coprime M) (hM : Squarefree M) (hodd : Odd M) (hM1 : 1 < M)
    (t : ZMod M) (hlift : (Q.toList.prod : ℤ) ∣ (t.val : ℤ) + (M : ℤ) * h₀)
    (ψ : 𝓢(ℝ, ℂ)) (hreal : ∀ x, conj (ψ x) = ψ x) (X H : ℝ) (hX : 0 < X)
    (hH : 0 ≤ H) (hcut : H * ((M : ℝ) / X) * Q.toList.prod ≤ N)
    (hsupp : ∀ x : ℝ, H < x → 𝓕 ψ x = 0) :
    ‖∑' n : ℤ, (amplificationWeight Q D n : ℂ) *
        (jacobiSym (n - t.val) M : ℂ) * ψ ((n : ℝ) / X)‖ ≤
      2 * Real.sqrt X *
        ‖originalPositiveFourier Q hQ D M N h₀ ((t.val : ℝ) / M) ((M : ℝ) / X) (𝓕 ψ)‖ := by
  rw [amplified_jacobi_poisson Q hQ D M h₀ hcop hM hodd t hlift ψ X hX,
    norm_mul, norm_mul, jacobiGaussPhase_norm M hM hodd,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), mul_one]
  have hh := originalSignedFourier_norm_le Q hQ D M N h₀ ((t.val : ℝ) / M)
    ((M : ℝ) / X) H (𝓕 ψ) hM1
    (div_pos (by exact_mod_cast NeZero.pos M) hX) hH hcut
    (fourier_real_conj ψ hreal) hsupp
  nlinarith [Real.sqrt_nonneg X]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_FallingFactorialError
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The elementary collision loss for sampling distinct indices -/

namespace Ostmann

/-- A convenient collision bound with no restriction that k be smaller than J. -/
theorem pow_le_descFactorial_add (J : ℕ) (hJ : 1 ≤ J) (k : ℕ) :
    J ^ k ≤ J.descFactorial k + k ^ 2 * J ^ (k - 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    by_cases hk : k = 0
    · subst k
      simp
    have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk
    by_cases hkJ : k ≤ J
    · have hmul := Nat.mul_le_mul_left J ih
      have hprev : J * J ^ (k - 1) = J ^ k := by
        rw [← pow_succ', Nat.sub_add_cancel hk1]
      have hdesc : J * J.descFactorial k =
          J.descFactorial (k + 1) + k * J.descFactorial k := by
        rw [Nat.descFactorial_succ, ← Nat.add_mul, Nat.sub_add_cancel hkJ]
      have hsmall := Nat.mul_le_mul_left k (Nat.descFactorial_le_pow J k)
      have herr : J * (k ^ 2 * J ^ (k - 1)) = k ^ 2 * J ^ k := by
        calc
          _ = k ^ 2 * (J * J ^ (k - 1)) := by ring
          _ = _ := by rw [hprev]
      rw [Nat.mul_add, hdesc, herr, ← pow_succ' J k] at hmul
      have hpoly : k ^ 2 + k ≤ (k + 1) ^ 2 := by nlinarith
      have hfinal := Nat.mul_le_mul_right (J ^ k) hpoly
      simp only [Nat.add_sub_cancel]
      nlinarith
    · have hJK : J ≤ (k + 1) ^ 2 := by
        have : J ≤ k := by omega
        nlinarith
      have h := Nat.mul_le_mul_right (J ^ k) hJK
      rw [pow_succ' J k]
      simpa only [Nat.add_sub_cancel] using h.trans (Nat.le_add_left _ _)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_CommonCenter
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Extracting one common center

The finite incidence argument in Section 3: large matching-prime sets
with small pairwise intersections have total size at most twice the
ambient set. A large moment therefore forces one large matching set.
-/

namespace Ostmann

open scoped BigOperators

theorem sum_centerIncidence {I P : Type*} [Fintype I] [Fintype P] [DecidableEq P]
    (S : I → Finset P) :
    (∑ p : P, centerIncidence S p) = ∑ i : I, ((S i).card : ℝ) := by
  unfold centerIncidence
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp

theorem sum_centerIncidence_sq {I P : Type*} [Fintype I] [Fintype P] [DecidableEq P]
    (S : I → Finset P) :
    (∑ p : P, centerIncidence S p ^ 2) =
      ∑ i : I, ∑ j : I, ((S i ∩ S j).card : ℝ) := by
  have hind (i j : I) :
      (∑ p : P, (if p ∈ S i then (1 : ℝ) else 0) * (if p ∈ S j then 1 else 0)) =
        (S i ∩ S j).card := by
    calc
      _ = ∑ p : P, if p ∈ S i ∩ S j then (1 : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro p _
        by_cases hi : p ∈ S i <;> by_cases hj : p ∈ S j <;> simp [hi, hj]
      _ = _ := by
        simp
        congr 1
        ext p
        simp
  simp only [centerIncidence, pow_two, Fintype.sum_mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun j _ => hind i j)

/-- Incidence Cauchy--Schwarz, with the diagonal separated before estimating intersections. -/
theorem commonCenter_incidence_bound {I P : Type*} [Fintype I] [Fintype P]
    [DecidableEq P] (S : I → Finset P) (K : ℝ) (hK : 0 ≤ K)
    (hinter : ∀ i j, i ≠ j → ((S i ∩ S j).card : ℝ) ≤ K) :
    (∑ i : I, ((S i).card : ℝ)) ^ 2 ≤
      (Fintype.card P : ℝ) *
        ((∑ i : I, ((S i).card : ℝ)) + K * (Fintype.card I : ℝ) ^ 2) := by
  classical
  have hcs := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset P))
    (f := centerIncidence S)
  rw [sum_centerIncidence, sum_centerIncidence_sq] at hcs
  simp only [Finset.card_univ] at hcs
  apply hcs.trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  calc
    _ ≤ ∑ i : I, ∑ j : I, ((if i = j then ((S i).card : ℝ) else 0) + K) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      by_cases hij : i = j
      · subst j
        simpa using hK
      · simpa only [hij, ite_false, if_false, zero_add] using hinter i j hij
    _ = _ := by
      simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ,
        ite_true, if_true, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring

/-- The quantitative absorption used for the high matching sets. -/
theorem commonCenter_total_le_twice {R J b A K : ℝ}
    (hJ : 0 ≤ J) (hb : 0 ≤ b) (hA : 0 < A)
    (hinc : R ^ 2 ≤ J * (R + K * b ^ 2))
    (hlarge : b * A ≤ R) (hsmall : 2 * K * J ≤ A ^ 2) : R ≤ 2 * J := by
  have hsq : (b * A) ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (mul_nonneg hb hA.le) hlarge 2
  have hprod := mul_le_mul_of_nonneg_right hsmall (sq_nonneg b)
  have hquad : R ^ 2 ≤ 2 * J * R := by nlinarith
  nlinarith

theorem commonCenter_family_total_le_twice {I P : Type*} [Fintype I] [Fintype P]
    [DecidableEq P] (S : I → Finset P) (A K : ℝ) (hA : 0 < A) (hK : 0 ≤ K)
    (hlarge : ∀ i, A ≤ ((S i).card : ℝ))
    (hinter : ∀ i j, i ≠ j → ((S i ∩ S j).card : ℝ) ≤ K)
    (hsmall : 2 * K * (Fintype.card P : ℝ) ≤ A ^ 2) :
    (∑ i : I, ((S i).card : ℝ)) ≤ 2 * (Fintype.card P : ℝ) := by
  apply commonCenter_total_le_twice
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) hA
    (commonCenter_incidence_bound S K hK hinter) _ hsmall
  calc
    (Fintype.card I : ℝ) * A = ∑ _i : I, A := by simp
    _ ≤ _ := Finset.sum_le_sum fun i _ => hlarge i

/-- A lower moment and the total incidence budget force a single large center. -/
theorem exists_commonCenter_of_moment {I P : Type*} [Fintype I] [Fintype P]
    [DecidableEq P] [Nonempty I] (S : I → Finset P) (A K L : ℝ) (k : ℕ)
    (hA : 0 < A) (hK : 0 ≤ K)
    (hlarge : ∀ i, A ≤ ((S i).card : ℝ))
    (hinter : ∀ i j, i ≠ j → ((S i ∩ S j).card : ℝ) ≤ K)
    (hsmall : 2 * K * (Fintype.card P : ℝ) ≤ A ^ 2)
    (hmoment : L ≤ ∑ i : I, ((S i).card : ℝ) ^ (k + 1)) :
    ∃ i : I, L ≤ 2 * (Fintype.card P : ℝ) * ((S i).card : ℝ) ^ k := by
  classical
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ
    (fun i => ((S i).card : ℝ)) Finset.univ_nonempty
  refine ⟨i, hmoment.trans ?_⟩
  calc
    _ ≤ ∑ j : I, ((S i).card : ℝ) ^ k * (S j).card := by
      apply Finset.sum_le_sum
      intro j _
      rw [pow_succ]
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (Nat.cast_nonneg _) (hi j (Finset.mem_univ _)) k) (Nat.cast_nonneg _)
    _ = ((S i).card : ℝ) ^ k * (∑ j : I, ((S j).card : ℝ)) := by rw [Finset.mul_sum]
    _ ≤ ((S i).card : ℝ) ^ k * (2 * (Fintype.card P : ℝ)) :=
      mul_le_mul_of_nonneg_left (commonCenter_family_total_le_twice S A K hA hK
        hlarge hinter hsmall) (pow_nonneg (Nat.cast_nonneg _) _)
    _ = _ := by ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_CommonCenterMoments
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The falling-factorial moment step in common-center extraction -/

namespace Ostmann

open scoped BigOperators

theorem descFactorial_gap_le (r k d : ℕ) (hd : d ≤ k) :
    r.descFactorial k ≤ r ^ d * r.descFactorial (k - d) := by
  rw [← Nat.descFactorial_mul_descFactorial (Nat.sub_le k d), Nat.sub_sub_self hd]
  apply Nat.mul_le_mul_right
  exact (Nat.descFactorial_le_pow _ _).trans (Nat.pow_le_pow_left (Nat.sub_le r _) d)

/-- Small matching sets contribute only a power of the threshold times a lower moment. -/
theorem smallCenter_factorial_moment_le {I : Type*} [Fintype I]
    (r : I → ℕ) (k d : ℕ) (hd : d ≤ k) (A : ℝ) (hA : 0 ≤ A) :
    (∑ i : I, if (r i : ℝ) < A then ((r i).descFactorial k : ℝ) else 0) ≤
      A ^ d * ∑ i : I, ((r i).descFactorial (k - d) : ℝ) := by
  classical
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  split_ifs with hi
  · have h : ((r i).descFactorial k : ℝ) ≤
        (r i : ℝ) ^ d * ((r i).descFactorial (k - d) : ℝ) := by
      exact_mod_cast descFactorial_gap_le (r i) k d hd
    exact h.trans (mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (Nat.cast_nonneg _) hi.le d) (Nat.cast_nonneg _))
  · exact mul_nonneg (pow_nonneg hA _) (Nat.cast_nonneg _)

/-- The mass surviving the small-set removal is a moment of high matching sets. -/
theorem highCenter_factorial_moment_ge {I : Type*} [Fintype I]
    (r : I → ℕ) (k d : ℕ) (hd : d ≤ k) (A B L : ℝ) (hA : 0 ≤ A)
    (hlo : (∑ i : I, ((r i).descFactorial (k - d) : ℝ)) ≤ B)
    (hhi : L ≤ ∑ i : I, ((r i).descFactorial k : ℝ)) :
    L - A ^ d * B ≤
      ∑ i : I, if A ≤ (r i : ℝ) then ((r i).descFactorial k : ℝ) else 0 := by
  classical
  have hsmall := (smallCenter_factorial_moment_le r k d hd A hA).trans
    (mul_le_mul_of_nonneg_left hlo (pow_nonneg hA _))
  have hsplit :
      (∑ i : I, ((r i).descFactorial k : ℝ)) =
      (∑ i : I, if (r i : ℝ) < A then ((r i).descFactorial k : ℝ) else 0) +
      (∑ i : I, if A ≤ (r i : ℝ) then ((r i).descFactorial k : ℝ) else 0) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : (r i : ℝ) < A
    · simp only [hi, not_le.mpr hi, ite_true, if_true, ite_false, if_false, add_zero]
    · simp only [hi, le_of_not_gt hi, ite_true, if_true, ite_false, if_false, zero_add]
  linarith

/-- The two factorial moment estimates in `quad-lift-factorials` produce a common center. -/
theorem exists_commonCenter_from_factorial_moments {I P : Type*}
    [Fintype I] [Fintype P] [DecidableEq P]
    (S : I → Finset P) (k d : ℕ) (hd : d ≤ k + 1) (A K B L : ℝ)
    (hA : 0 < A) (hK : 0 ≤ K)
    (hinter : ∀ i j, i ≠ j → ((S i ∩ S j).card : ℝ) ≤ K)
    (hsmall : 2 * K * (Fintype.card P : ℝ) ≤ A ^ 2)
    (hlo : (∑ i : I, ((S i).card.descFactorial (k + 1 - d) : ℝ)) ≤ B)
    (hhi : L ≤ ∑ i : I, ((S i).card.descFactorial (k + 1) : ℝ))
    (hpositive : 0 < L - A ^ d * B) :
    ∃ i : I, A ≤ ((S i).card : ℝ) ∧
      L - A ^ d * B ≤ 2 * (Fintype.card P : ℝ) * ((S i).card : ℝ) ^ k := by
  classical
  let H := {i : I // A ≤ ((S i).card : ℝ)}
  have hsum : (∑ i : H, ((S i.1).card.descFactorial (k + 1) : ℝ)) =
      ∑ i : I, if A ≤ ((S i).card : ℝ) then ((S i).card.descFactorial (k + 1) : ℝ) else 0 := by
    rw [← Finset.sum_filter]
    exact (Finset.sum_subtype (p := fun i : I => A ≤ ((S i).card : ℝ))
      (Finset.univ.filter fun i : I => A ≤ ((S i).card : ℝ))
      (by intro i; simp) (fun i => ((S i).card.descFactorial (k + 1) : ℝ))).symm
  have hh : L - A ^ d * B ≤ ∑ i : H, ((S i.1).card.descFactorial (k + 1) : ℝ) := by
    rw [hsum]
    exact highCenter_factorial_moment_ge (fun i => (S i).card) (k + 1) d hd A B L hA.le hlo hhi
  have hH : Nonempty H := by
    by_contra h
    have : IsEmpty H := ⟨fun i => h ⟨i⟩⟩
    simp only [Finset.univ_eq_empty, Finset.sum_empty] at hh
    linarith
  let : Nonempty H := hH
  have hpows : L - A ^ d * B ≤ ∑ i : H, ((S i.1).card : ℝ) ^ (k + 1) := by
    apply hh.trans
    apply Finset.sum_le_sum
    intro i _
    exact_mod_cast Nat.descFactorial_le_pow (S i.1).card (k + 1)
  obtain ⟨i, hi⟩ := exists_commonCenter_of_moment (fun i : H => S i.1) A K
    (L - A ^ d * B) k hA hK (fun i => i.2)
    (fun i j hij => hinter i.1 j.1 (fun h => hij (Subtype.ext h))) hsmall hpows
  exact ⟨i.1, i.2, hi⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_CommonCenterCongruences
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Intersections of the matching-prime sets attached to integer lifts -/

namespace Ostmann

open scoped BigOperators

theorem matchingPrimes_inter_dvd (P : Finset ℕ) (a : ℤ) (t : ℕ → ℤ) (n m : ℤ)
    {p : ℕ} (hp : p ∈ matchingPrimes P a t n ∩ matchingPrimes P a t m) :
    p ∣ (n - m).natAbs := by
  obtain ⟨hn, hm⟩ := Finset.mem_inter.mp hp
  have hd := dvd_sub (Finset.mem_filter.mp hn).2 (Finset.mem_filter.mp hm).2
  have heq : (n - a * t p) - (m - a * t p) = n - m := by ring
  rw [heq] at hd
  exact Int.natCast_dvd.mp hd

/-- Distinct lifts cannot share more than `k` large prime congruences. -/
theorem matchingPrimes_inter_card_le (P : Finset ℕ) (a : ℤ) (t : ℕ → ℤ)
    (n m : ℤ) (hnm : n ≠ m) (k : ℕ) (B : ℝ) (hB : 0 < B)
    (hprime : ∀ p ∈ P, p.Prime) (hlog : ∀ p ∈ P, B ≤ Real.log (p : ℝ))
    (hdiff : Real.log ((n - m).natAbs : ℝ) < (k + 1 : ℕ) * B) :
    (matchingPrimes P a t n ∩ matchingPrimes P a t m).card ≤ k := by
  let S := matchingPrimes P a t n ∩ matchingPrimes P a t m
  have hsub : S ⊆ P := fun p hp => (Finset.mem_filter.mp (Finset.mem_inter.mp hp).1).1
  have hpos : 0 < (n - m).natAbs := Int.natAbs_pos.mpr (sub_ne_zero.mpr hnm)
  have hbudget := sum_log_prime_divisors_le S hpos
    (fun p hp => hprime p (hsub hp)) (fun p hp => matchingPrimes_inter_dvd P a t n m hp)
  have hlow : (S.card : ℝ) * B ≤ ∑ p ∈ S, Real.log (p : ℝ) := by
    calc
      _ = ∑ _p ∈ S, B := by simp
      _ ≤ _ := Finset.sum_le_sum fun p hp => hlog p (hsub hp)
  have hcard : (S.card : ℝ) < (k + 1 : ℕ) := by nlinarith
  have : S.card < k + 1 := by exact_mod_cast hcard
  exact Nat.lt_succ_iff.mp this

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_CommonCenterReduction
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reducing the common rational center and transporting its congruences -/

namespace Ostmann

theorem exists_reduced_commonCenter (n : ℤ) (a : ℕ) (ha : 0 < a) :
    ∃ h : ℤ, ∃ m : ℕ, 0 < m ∧ m ≤ a ∧ h.natAbs.Coprime m ∧
      |h| ≤ |n| ∧ n * (m : ℤ) = (a : ℤ) * h := by
  let q : ℚ := Rat.divInt n a
  have ha0 : (a : ℤ) ≠ 0 := by exact_mod_cast ha.ne'
  obtain ⟨c, hn, hac⟩ := Rat.num_den_mk ha0 (show q = Rat.divInt n a from rfl)
  refine ⟨q.num, q.den, q.pos, ?_, q.reduced, ?_, ?_⟩
  · exact Nat.le_of_dvd ha (Int.natCast_dvd_natCast.mp (Rat.den_dvd n a))
  · have hm : (0 : ℤ) < q.den := by exact_mod_cast q.pos
    have hc : 0 < c := by nlinarith
    have hc1 : (1 : ℤ) ≤ c := hc
    rw [hn, abs_mul, abs_of_pos hc]
    nlinarith [abs_nonneg q.num]
  · rw [hn, hac]
    ring

/-- The common lift gives the same field center after reducing the rational number. -/
theorem reduced_commonCenter_mod_prime (n h : ℤ) (a m p : ℕ)
    [Fact p.Prime] (ha : 0 < a) (hap : a < p) (hm : 0 < m) (hma : m ≤ a)
    (heq : n * (m : ℤ) = (a : ℤ) * h) (t : ℤ)
    (hcong : (p : ℤ) ∣ n - (a : ℤ) * t) :
    (t : ZMod p) = (h : ZMod p) / (m : ZMod p) := by
  have ha0 : (a : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact Nat.not_dvd_of_pos_of_lt ha hap
  have hm0 : (m : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact Nat.not_dvd_of_pos_of_lt hm (hma.trans_lt hap)
  have hn : (n : ZMod p) = (a : ZMod p) * (t : ZMod p) := by
    have hz : ((n - (a : ℤ) * t : ℤ) : ZMod p) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hcong
    simpa only [Int.cast_sub, Int.cast_mul, Int.cast_natCast, sub_eq_zero] using hz
  have hcross : (n : ZMod p) * (m : ZMod p) = (a : ZMod p) * (h : ZMod p) := by
    simpa only [Int.cast_mul, Int.cast_natCast] using congrArg (fun x : ℤ => (x : ZMod p)) heq
  rw [hn, mul_assoc] at hcross
  exact (eq_div_iff hm0).mpr (mul_left_cancel₀ ha0 hcross)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_CommonCenterAssembly
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Common-center extraction for the actual congruence matching sets -/

namespace Ostmann

open scoped BigOperators

theorem image_matchingPrimeSubtype (P : Finset ℕ) (a : ℤ) (t : ℕ → ℤ) (n : ℤ) :
    (matchingPrimeSubtype P a t n).image Subtype.val = matchingPrimes P a t n := by
  ext p
  constructor
  · intro hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    exact Finset.mem_filter.mpr ⟨q.2, (Finset.mem_filter.mp hq).2⟩
  · intro hp
    obtain ⟨hP, hd⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_image.mpr ⟨⟨p, hP⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd⟩, rfl⟩

theorem card_matchingPrimeSubtype (P : Finset ℕ) (a : ℤ) (t : ℕ → ℤ) (n : ℤ) :
    (matchingPrimeSubtype P a t n).card = (matchingPrimes P a t n).card := by
  rw [← image_matchingPrimeSubtype]
  exact (Finset.card_image_of_injective _ Subtype.val_injective).symm

theorem card_inter_matchingPrimeSubtype (P : Finset ℕ) (a : ℤ) (t : ℕ → ℤ) (n m : ℤ) :
    (matchingPrimeSubtype P a t n ∩ matchingPrimeSubtype P a t m).card =
      (matchingPrimes P a t n ∩ matchingPrimes P a t m).card := by
  rw [← Finset.card_image_of_injective _ Subtype.val_injective,
    Finset.image_inter _ _ Subtype.val_injective,
    image_matchingPrimeSubtype, image_matchingPrimeSubtype]

/-- The finite form of `quad-common-centre-size` and `quad-common-centre`.
The only moment assumptions are the explicit counts of integer lifts. -/
theorem exists_commonCenter_of_lift_moments (P : Finset ℕ) (N : Finset ℤ)
    (a : ℕ) (ha : 0 < a) (t : ℕ → ℤ) (k d K : ℕ) (hd : d ≤ k + 1)
    (A B L V : ℝ) (hA : 0 < A) (hV : 0 < V)
    (hprime : ∀ p ∈ P, p.Prime) (hap : ∀ p ∈ P, a < p)
    (hlog : ∀ p ∈ P, V ≤ Real.log (p : ℝ))
    (hspan : ∀ n ∈ N, ∀ m ∈ N, n ≠ m →
      Real.log ((n - m).natAbs : ℝ) < (K + 1 : ℕ) * V)
    (hsmall : 2 * K * (P.card : ℝ) ≤ A ^ 2)
    (hlo : (∑ n : N, ((matchingPrimes P a t n.1).card.descFactorial (k + 1 - d) : ℝ)) ≤ B)
    (hhi : L ≤ ∑ n : N, ((matchingPrimes P a t n.1).card.descFactorial (k + 1) : ℝ))
    (hpositive : 0 < L - A ^ d * B) :
    ∃ n ∈ N, ∃ h : ℤ, ∃ m : ℕ,
      0 < m ∧ m ≤ a ∧ h.natAbs.Coprime m ∧ |h| ≤ |n| ∧
      A ≤ ((matchingPrimes P a t n).card : ℝ) ∧
      L - A ^ d * B ≤ 2 * P.card * ((matchingPrimes P a t n).card : ℝ) ^ k ∧
      ∀ (p : ℕ) (hp : p ∈ matchingPrimes P a t n),
        let _ : Fact p.Prime := ⟨hprime p (Finset.mem_filter.mp hp).1⟩
        (t p : ZMod p) = (h : ZMod p) / (m : ZMod p) := by
  classical
  have hinter (n m : N) (hne : n ≠ m) :
      ((matchingPrimeSubtype P a t n.1 ∩ matchingPrimeSubtype P a t m.1).card : ℝ) ≤ K := by
    rw [card_inter_matchingPrimeSubtype]
    exact_mod_cast matchingPrimes_inter_card_le P a t n.1 m.1
      (fun h => hne (Subtype.ext h)) K V hV hprime hlog (hspan n n.2 m m.2 (fun h => hne (Subtype.ext h)))
  have hlo' : (∑ n : N, ((matchingPrimeSubtype P a t n.1).card.descFactorial (k + 1 - d) : ℝ)) ≤ B := by
    simpa only [card_matchingPrimeSubtype] using hlo
  have hhi' : L ≤ ∑ n : N, ((matchingPrimeSubtype P a t n.1).card.descFactorial (k + 1) : ℝ) := by
    simpa only [card_matchingPrimeSubtype] using hhi
  obtain ⟨n, hnsize, hnlarge⟩ := exists_commonCenter_from_factorial_moments
    (fun n : N => matchingPrimeSubtype P a t n.1) k d hd A K B L hA (Nat.cast_nonneg _)
    hinter (by simpa only [Fintype.card_coe] using hsmall) hlo' hhi' hpositive
  rw [card_matchingPrimeSubtype] at hnsize hnlarge
  obtain ⟨h, m, hm, hma, hred, hbound, heq⟩ := exists_reduced_commonCenter n.1 a ha
  refine ⟨n.1, n.2, h, m, hm, hma, hred, hbound, hnsize, ?_, ?_⟩
  · simpa only [Fintype.card_coe] using hnlarge
  · intro p hp
    have hpP := (Finset.mem_filter.mp hp).1
    let : Fact p.Prime := ⟨hprime p hpP⟩
    exact reduced_commonCenter_mod_prime n.1 h a m p ha (hap p hpP) hm hma heq (t p)
      (Finset.mem_filter.mp hp).2

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_CommonCenterTupleCounts
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Ordered distinct tuples and common-center lift moments -/

namespace Ostmann

open scoped BigOperators

theorem card_matchingTuple {P : Type*} [Fintype P] [DecidableEq P]
    (S : Finset P) (r : ℕ) :
    Fintype.card {e : Fin r ↪ P // ∀ i, e i ∈ S} = S.card.descFactorial r := by
  rw [← Fintype.card_congr (matchingTupleEquiv S r), Fintype.card_embedding_eq]
  simp only [Fintype.card_coe, Fintype.card_fin]

/-- Exact double counting of all ordered distinct tuple/lift incidences. -/
theorem sum_matching_factorials {N P : Type*} [Fintype N] [Fintype P] [DecidableEq P]
    (S : N → Finset P) (r : ℕ) :
    (∑ n, (S n).card.descFactorial r) =
      ∑ e : Fin r ↪ P, Fintype.card {n : N // ∀ i, e i ∈ S n} := by
  classical
  have h := Fintype.card_congr (incidenceSwap (fun n (e : Fin r ↪ P) => ∀ i, e i ∈ S n))
  simp only [Fintype.card_sigma, card_matchingTuple] at h
  exact h

/-- A family of distinct tuples each admitting a lift supplies the high
factorial-moment lower bound; no unique-lift assumption is required. -/
theorem card_tuples_le_sum_matching_factorials {N P : Type*}
    [Fintype N] [Fintype P] [DecidableEq P]
    (S : N → Finset P) (r : ℕ) (E : Finset (Fin r ↪ P))
    (hlift : ∀ e ∈ E, ∃ n, ∀ i, e i ∈ S n) :
    E.card ≤ ∑ n, (S n).card.descFactorial r := by
  classical
  rw [sum_matching_factorials]
  calc
    E.card = ∑ _e ∈ E, 1 := by simp
    _ ≤ ∑ e ∈ E, Fintype.card {n : N // ∀ i, e i ∈ S n} := by
      apply Finset.sum_le_sum
      intro e he
      obtain ⟨n, hn⟩ := hlift e he
      have : Nonempty {n : N // ∀ i, e i ∈ S n} := ⟨⟨n, hn⟩⟩
      exact Fintype.card_pos_iff.mpr this
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ E) (by simp)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_CommonCenterLiftBounds
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform lift bounds for ordered distinct prime tuples -/

namespace Ostmann

open scoped BigOperators

theorem primeTupleProduct_pos (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime)
    {r : ℕ} (e : Fin r ↪ P) : 0 < primeTupleProduct P e :=
  Finset.prod_pos (fun i _ => (hprime _ (e i).2).pos)

private theorem tuple_prime_coprime (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime)
    {r : ℕ} (e : Fin r ↪ P) {i j : Fin r} (hij : i ≠ j) :
    ((e i).1).Coprime ((e j).1) := by
  have hne : (e i).1 ≠ (e j).1 := fun h => hij (e.injective (Subtype.ext h))
  apply (hprime _ (e i).2).coprime_iff_not_dvd.mpr
  intro h
  exact hne (((hprime _ (e j).2).eq_one_or_self_of_dvd _ h).resolve_left
    (hprime _ (e i).2).ne_one)

/-- Two lifts of the same distinct prime tuple lie in the same progression
modulo the product of those primes. -/
theorem tuple_lifts_modEq (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime)
    (a : ℤ) (t : ℕ → ℤ) {r : ℕ} (e : Fin r ↪ P) (n m : ℤ)
    (hn : ∀ i, ((e i).1 : ℤ) ∣ n - a * t (e i).1)
    (hm : ∀ i, ((e i).1 : ℤ) ∣ m - a * t (e i).1) :
    n ≡ m [ZMOD (primeTupleProduct P e : ℤ)] := by
  apply Int.modEq_iff_dvd.mpr
  have hpair : ((Finset.univ : Finset (Fin r)) : Set (Fin r)).Pairwise
      (fun i j => IsCoprime ((e i).1 : ℤ) ((e j).1 : ℤ)) := by
    intro i _ j _ hij
    exact (tuple_prime_coprime P hprime e hij).cast
  have hd : (∏ i : Fin r, ((e i).1 : ℤ)) ∣ m - n := by
    apply Finset.prod_dvd_of_coprime hpair
    intro i _
    have h := dvd_sub (hm i) (hn i)
    simpa only [sub_sub_sub_cancel_right] using h
  simpa only [primeTupleProduct, Nat.cast_prod] using hd

/-- Uniform in the chosen tuple and its residue class. -/
theorem card_integerLiftSet_le (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime)
    (a : ℤ) (t : ℕ → ℤ) {r : ℕ} (e : Fin r ↪ P) (H : ℕ) :
    ((integerLiftSet P a t e H).card : ℚ) ≤
      (2 * (H : ℚ) + 1) / (primeTupleProduct P e : ℚ) + 1 := by
  classical
  have hM : 0 < primeTupleProduct P e := primeTupleProduct_pos P hprime e
  by_cases hnon : (integerLiftSet P a t e H).Nonempty
  · obtain ⟨m, hm⟩ := hnon
    have hm' := (Finset.mem_filter.mp hm).2
    have hsub : integerLiftSet P a t e H ⊆
        (Finset.Ico (-(H : ℤ)) (H + 1)).filter
          (fun n => n ≡ m [ZMOD (primeTupleProduct P e : ℤ)]) := by
      intro n hn
      obtain ⟨hI, hn'⟩ := Finset.mem_filter.mp hn
      exact Finset.mem_filter.mpr ⟨hI, tuple_lifts_modEq P hprime a t e n m hn' hm'⟩
    have hcard : ((integerLiftSet P a t e H).card : ℚ) ≤
        (((Finset.Ico (-(H : ℤ)) (H + 1)).filter
          (fun n => n ≡ m [ZMOD (primeTupleProduct P e : ℤ)])).card : ℚ) := by
      exact_mod_cast Finset.card_le_card hsub
    refine hcard.trans ?_
    have hp := progression_Ico_card_le (-(H : ℤ)) (H + 1)
      (primeTupleProduct P e) m (by omega) (by exact_mod_cast hM)
    convert hp using 1
    all_goals try with_reducible_and_instances rfl
    push_cast
    ring
  · rw [Finset.not_nonempty_iff_eq_empty.mp hnon, Finset.card_empty, Nat.cast_zero]
    positivity

theorem primeTupleProduct_lower (P : Finset ℕ) (Z : ℕ)
    (hZ : ∀ p ∈ P, Z ≤ p) {r : ℕ} (e : Fin r ↪ P) :
    Z ^ r ≤ primeTupleProduct P e := by
  have h := Finset.prod_le_prod' (fun (i : Fin r) (_ : i ∈ Finset.univ) => hZ _ (e i).2)
  simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, primeTupleProduct] using h

/-- The bound used in the lower factorial moment is uniform over the tuple. -/
theorem card_integerLiftSet_le_uniform (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime)
    (a : ℤ) (t : ℕ → ℤ) {r : ℕ} (e : Fin r ↪ P) (H Z : ℕ)
    (hZ : 0 < Z) (hmin : ∀ p ∈ P, Z ≤ p) :
    ((integerLiftSet P a t e H).card : ℚ) ≤ (2 * (H : ℚ) + 1) / (Z : ℚ) ^ r + 1 := by
  have hprod : (Z : ℚ) ^ r ≤ (primeTupleProduct P e : ℚ) := by
    exact_mod_cast primeTupleProduct_lower P Z hmin e
  have hpos : (0 : ℚ) < Z := by exact_mod_cast hZ
  have hn : (0 : ℚ) ≤ 2 * (H : ℚ) + 1 := by positivity
  have hd := div_le_div_of_nonneg_left hn (pow_pos hpos r) hprod
  exact (card_integerLiftSet_le P hprime a t e H).trans (by linarith)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticAmplificationIdentity
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Identifying the shared coefficient test with the distinct-prime expansion -/

namespace Ostmann

open scoped BigOperators Classical

theorem jacobi_product_right (u : ℤ) (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p ≠ 0) :
    jacobiSym u (∏ p ∈ Q, p) = ∏ p ∈ Q, jacobiSym u p := by
  induction Q using Finset.induction_on with
  | empty => simp
  | @insert p Q hp ih =>
    have hpn := hQ p (Finset.mem_insert_self _ _)
    have hQn : ∀ q ∈ Q, q ≠ 0 := fun q hq => hQ q (Finset.mem_insert_of_mem hq)
    rw [Finset.prod_insert hp, jacobiSym.mul_right' u hpn
      (Finset.prod_ne_zero_iff.mpr hQn), ih hQn, Finset.prod_insert hp]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_PrimeTupleTranslation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Constructing the common translation for an actual tuple of primes -/

namespace Ostmann

open scoped BigOperators Classical

theorem primeTupleSet_subset (P : Finset ℕ) {k : ℕ} (e : Fin k ↪ P) :
    primeTupleSet P e ⊆ P := by
  intro p hp
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
  exact (e i).property

theorem primeTupleProduct_eq_set (P : Finset ℕ) {k : ℕ} (e : Fin k ↪ P) :
    primeTupleProduct P e = (primeTupleSet P e).toList.prod := by
  simp only [primeTupleProduct, primeTupleSet, Finset.prod_toList]
  rw [Finset.prod_image]
  intro i _ j _ h
  exact e.injective (Subtype.ext h)

theorem primeTupleProduct_squarefree (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {k : ℕ} (e : Fin k ↪ P) : Squarefree (primeTupleProduct P e) := by
  rw [primeTupleProduct_eq_set]
  exact primeSet_modulus_squarefree _ (fun p hp => hP p (primeTupleSet_subset P e hp))

theorem primeTupleProduct_odd (P : Finset ℕ) (hodd : ∀ p ∈ P, Odd p)
    {k : ℕ} (e : Fin k ↪ P) : Odd (primeTupleProduct P e) := by
  change Odd (∏ i, (e i).val)
  exact Finset.prod_induction _ (fun n => Odd n)
    (fun a b ha hb => ha.mul hb) (by decide) (fun i _ => hodd _ (e i).property)

theorem primeTupleProduct_one_lt (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {k : ℕ} (hk : 0 < k) (e : Fin k ↪ P) : 1 < primeTupleProduct P e := by
  have hlow := primeTupleProduct_lower P 2 (fun p hp => (hP p hp).two_le) e
  exact (Nat.one_lt_pow (by omega : k ≠ 0) (by decide : 1 < 2)).trans_le hlow

theorem jacobi_primeTuple_translation (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {k : ℕ} (e : Fin k ↪ P) (t : ℕ → ℤ) (tM n : ℤ)
    (ht : ∀ i, (tM : ZMod (e i).val) = (t (e i).val : ZMod (e i).val)) :
    (jacobiSym (n - tM) (primeTupleProduct P e) : ℝ) =
      ∏ i, (jacobiSym (n - t (e i).val) (e i).val : ℝ) := by
  rw [primeTupleProduct_eq_set]
  simp only [Finset.prod_toList]
  rw [jacobi_product_right _ _ (fun p hp =>
    (hP p (primeTupleSet_subset P e hp)).ne_zero), Int.cast_prod]
  unfold primeTupleSet
  rw [Finset.prod_image (fun i _ j _ h => e.injective (Subtype.ext h))]
  apply Finset.prod_congr rfl
  intro i _
  let : NeZero (e i).val := ⟨(hP _ (e i).property).ne_zero⟩
  have hh : ((n - tM : ℤ) : ZMod (e i).val) = ((n - t (e i).val : ℤ) : ZMod (e i).val) := by
    simp only [Int.cast_sub, ht i]
  have he := congrArg (jacobiCharacter (e i).val) hh
  simpa only [jacobiCharacter_intCast] using he

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_PrimeProductTranslations
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # CRT translation tables indexed by the prime product alone -/

namespace Ostmann

open scoped BigOperators Classical

theorem exists_primeSet_translation (U : Finset ℕ) (hU : ∀ p ∈ U, p.Prime)
    (t : ℕ → ℤ) (L : ℕ) [NeZero L] (hcop : L.Coprime U.toList.prod) :
    ∃ τ h₀ : ℕ, τ < U.toList.prod ∧ h₀ < L ∧
      (L : ℤ) ∣ (τ : ℤ) + (U.toList.prod : ℤ) * h₀ ∧
      ∀ p ∈ U, (τ : ZMod p) = (t p : ZMod p) := by
  let a (p : ℕ) := (t p : ZMod p).val
  have hn : ∀ p ∈ U, p ≠ 0 := fun p hp => (hU p hp).ne_zero
  have hpair : Set.Pairwise U Nat.Coprime := by
    intro p hp q hq hpq
    exact (Nat.coprime_primes (hU p hp) (hU q hq)).mpr hpq
  let z := Nat.chineseRemainderOfFinset a id U hn hpair
  have hz : z.val < U.toList.prod := by
    simpa only [Finset.prod_toList, id_eq] using Nat.chineseRemainderOfFinset_lt_prod a id hn hpair
  let r : ZMod L := -(z.val : ZMod L) * (U.toList.prod : ZMod L)⁻¹
  have hu : IsUnit (U.toList.prod : ZMod L) := (ZMod.isUnit_iff_coprime _ _).mpr hcop.symm
  refine ⟨z.val, r.val, hz, ZMod.val_lt r, ?_, ?_⟩
  · apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ L).mp
    simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val]
    change (z.val : ZMod L) + (U.toList.prod : ZMod L) * r = 0
    dsimp [r]
    rw [mul_comm (-(z.val : ZMod L)), ← mul_assoc, ZMod.mul_inv_of_unit _ hu]
    ring
  · intro p hp
    let : NeZero p := ⟨hn p hp⟩
    have hh := (ZMod.natCast_eq_natCast_iff z.val (a p) p).mpr (z.property p hp)
    simpa only [a, ZMod.natCast_zmod_val] using hh

/-- The chosen translation depends on the squarefree product, so all
permutations of a tuple use the same Fourier phase and coefficient array. -/
theorem exists_primeProduct_translations (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (k L : ℕ) [NeZero L] (t : ℕ → ℤ)
    (hcop : ∀ M ∈ primeSubsetProducts P k, L.Coprime M) :
    ∃ τ h₀ : ℕ → ℕ, ∀ M ∈ primeSubsetProducts P k,
      τ M < M ∧ h₀ M < L ∧ (L : ℤ) ∣ (τ M : ℤ) + (M : ℤ) * h₀ M ∧
      ∀ p ∈ M.primeFactors, (τ M : ZMod p) = (t p : ZMod p) := by
  have hex (M : ℕ) : ∃ a b : ℕ, M ∈ primeSubsetProducts P k →
      a < M ∧ b < L ∧ (L : ℤ) ∣ (a : ℤ) + (M : ℤ) * b ∧
      ∀ p ∈ M.primeFactors, (a : ZMod p) = (t p : ZMod p) := by
    by_cases hM : M ∈ primeSubsetProducts P k
    · obtain ⟨U, hU, hprod⟩ := Finset.mem_image.mp hM
      have hUP := (Finset.mem_powersetCard.mp hU).1
      have hp : ∀ p ∈ U, p.Prime := fun p hp => hP p (hUP hp)
      have hprod' : U.toList.prod = M := by simpa only [Finset.prod_toList] using hprod
      obtain ⟨a, b, ha, hb, hd, hc⟩ := exists_primeSet_translation U hp t L
        (by simpa only [hprod'] using hcop M hM)
      refine ⟨a, b, fun _ => ⟨?_, hb, ?_, ?_⟩⟩
      · simpa only [hprod'] using ha
      · simpa only [hprod'] using hd
      · have hf : M.primeFactors = U := by rw [← hprod, Nat.primeFactors_prod hp]
        simpa only [hf] using hc
    · exact ⟨0, 0, fun h => (hM h).elim⟩
  choose τ h₀ hh using hex
  exact ⟨τ, h₀, hh⟩

theorem primeTupleProduct_mem (P : Finset ℕ) {k : ℕ} (e : Fin k ↪ P) :
    primeTupleProduct P e ∈ primeSubsetProducts P k := by
  apply Finset.mem_image.mpr
  refine ⟨primeTupleSet P e, Finset.mem_powersetCard.mpr ⟨primeTupleSet_subset P e, ?_⟩, ?_⟩
  · have hc : (primeTupleSet P e).card = (Finset.univ : Finset (Fin k)).card := by
      apply Finset.card_image_iff.mpr
      intro i _ j _ he
      exact e.injective (Subtype.ext he)
    simpa only [Finset.card_univ, Fintype.card_fin] using hc
  · simpa only [Finset.prod_toList] using (primeTupleProduct_eq_set P e).symm

theorem primeTuple_member_primeFactors (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {k : ℕ} (e : Fin k ↪ P) (i : Fin k) : (e i).val ∈ (primeTupleProduct P e).primeFactors := by
  rw [primeTupleProduct_eq_set, Finset.prod_toList,
    Nat.primeFactors_prod (fun p hp => hP p (primeTupleSet_subset P e hp))]
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_PrimeTupleAverages
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact transfer between ordered prime tuples and their products -/

namespace Ostmann

open scoped BigOperators Classical

theorem distinct_tuple_statistic_sum {A : Type*} [Fintype A] [DecidableEq A]
    (k : ℕ) (F : Finset A → ℝ) :
    (∑ e : Fin k ↪ A, F (tupleImage e)) =
      (k.factorial : ℝ) * ∑ U ∈ (Finset.univ : Finset A).powersetCard k, F U := by
  have hmaps (e : Fin k ↪ A) (_ : e ∈ (Finset.univ : Finset (Fin k ↪ A))) :
      tupleImage e ∈ (Finset.univ : Finset A).powersetCard k := by
    apply Finset.mem_powersetCard.mpr
    refine ⟨Finset.subset_univ _, ?_⟩
    have hc : (Finset.univ.image e).card = (Finset.univ : Finset (Fin k)).card :=
      Finset.card_image_iff.mpr e.injective.injOn
    simpa only [tupleImage, Finset.card_univ, Fintype.card_fin] using hc
  rw [← Finset.sum_fiberwise_of_maps_to hmaps, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro U hU
  calc
    _ = ∑ _e ∈ (Finset.univ : Finset (Fin k ↪ A)).filter (fun e => tupleImage e = U), F U := by
      apply Finset.sum_congr rfl
      intro e he
      rw [(Finset.mem_filter.mp he).2]
    _ = _ := by
      rw [Finset.sum_const]
      have hc : ((Finset.univ : Finset (Fin k ↪ A)).filter
          (fun e => tupleImage e = U)).card = k.factorial := by
        simpa only [Fintype.card_subtype] using
          card_tupleImage_fiber k U (Finset.mem_powersetCard.mp hU).2
      rw [hc, nsmul_eq_mul]

theorem primeTuple_statistic_sum (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (k : ℕ) (f : ℕ → ℝ) :
    (∑ e : Fin k ↪ P, f (primeTupleProduct P e)) =
      (k.factorial : ℝ) * ∑ m ∈ primeSubsetProducts P k, f m := by
  have he (e : Fin k ↪ P) : primeTupleProduct P e = ∏ p ∈ tupleImage e, p.val := by
    rw [tupleImage, Finset.prod_image e.injective.injOn]
    rfl
  simp_rw [he]
  rw [distinct_tuple_statistic_sum k (fun U : Finset P => f (∏ p ∈ U, p.val))]
  congr 1
  let emb : P ↪ ℕ := Function.Embedding.subtype _
  have hmap : (Finset.univ : Finset P).map emb = P := by ext p; simp [emb]
  have hs := congrArg (fun R : Finset ℕ => ∑ U ∈ R.powersetCard k, f (∏ p ∈ U, p)) hmap
  simp only [Finset.powersetCard_map, Finset.sum_map] at hs
  change (∑ U ∈ (Finset.univ : Finset P).powersetCard k, f (∏ p ∈ U.map emb, p)) =
    ∑ U ∈ P.powersetCard k, f (∏ p ∈ U, p) at hs
  simp only [Finset.prod_map] at hs
  change (∑ U ∈ (Finset.univ : Finset P).powersetCard k, f (∏ p ∈ U, p.val)) =
    ∑ U ∈ P.powersetCard k, f (∏ p ∈ U, p) at hs
  rw [hs, primeSubsetProducts, Finset.sum_image]
  intro U hU V hV hprod
  exact primeSubset_product_injective P hP
    (Finset.mem_powersetCard.mp hU).1 (Finset.mem_powersetCard.mp hV).1 hprod

theorem primeTuple_uniform_mean (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (k : ℕ) (f : ℕ → ℝ) :
    (Fintype.card (Fin k ↪ P) : ℝ)⁻¹ * (∑ e : Fin k ↪ P, f (primeTupleProduct P e)) =
      (P.card.choose k : ℝ)⁻¹ * ∑ m ∈ primeSubsetProducts P k, f m := by
  rw [primeTuple_statistic_sum P hP k f, Fintype.card_embedding_eq,
    Fintype.card_coe, Fintype.card_fin, Nat.descFactorial_eq_factorial_mul_choose]
  push_cast
  have hk : (k.factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos k).ne'
  rw [mul_inv_rev]
  field_simp

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_OriginalTupleLifts
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Original Fourier witnesses give a positive family of integer tuple lifts -/

namespace Ostmann

open Filter
open scoped BigOperators SchwartzMap Classical

theorem primeTuple_event_probability (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (k : ℕ) (E : ℕ → Prop) [DecidablePred E] :
    (Fintype.card (Fin k ↪ P) : ℝ)⁻¹ *
      ((Finset.univ : Finset (Fin k ↪ P)).filter (fun e => E (primeTupleProduct P e))).card =
      (P.card.choose k : ℝ)⁻¹ * ((primeSubsetProducts P k).filter E).card := by
  have hh := primeTuple_uniform_mean P hP k (fun m => if E m then (1 : ℝ) else 0)
  simpa only [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one] using hh

theorem tupleLiftFamily_probability (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (k A H : ℕ) (t : ℕ → ℤ) (E : ℕ → Prop) [DecidablePred E]
    (hlift : ∀ e : Fin k ↪ P, E (primeTupleProduct P e) →
      ∃ a ∈ Finset.Icc 1 A, ∃ n ∈ Finset.Ico (-(H : ℤ)) (H + 1),
        ∀ i, ((e i).1 : ℤ) ∣ n - (a : ℤ) * t (e i).1) :
    (P.card.choose k : ℝ)⁻¹ * ((primeSubsetProducts P k).filter E).card ≤
      (Fintype.card (Fin k ↪ P) : ℝ)⁻¹ * (tupleLiftFamily P k A H t).card := by
  rw [← primeTuple_event_probability P hP k E]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg _))
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro e he
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlift e (Finset.mem_filter.mp he).2⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_FourierGridMargin
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original prime-product range supplies the strict Fourier grid margin -/

namespace Ostmann

theorem fourier_grid_margin_of_prime_scale (T R : ℝ) (L : ℕ)
    (hT : 1 ≤ T) (hL : (L : ℝ) ≤ Real.exp (T / 50))
    (hR : Real.exp (10 * T) ≤ R) :
    (L : ℝ) ^ 6 + Real.exp (-200 * T) ≤ R := by
  have hpow : (L : ℝ) ^ 6 ≤ Real.exp T := by
    calc
      _ ≤ Real.exp (T / 50) ^ 6 := pow_le_pow_left₀ (Nat.cast_nonneg _) hL 6
      _ = Real.exp (6 * (T / 50)) := (Real.exp_nat_mul _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  have hsmall : Real.exp (-200 * T) ≤ Real.exp T := Real.exp_le_exp.mpr (by linarith)
  have hfactor : (2 : ℝ) ≤ Real.exp (9 * T) := by linarith [Real.add_one_le_exp (9 * T)]
  calc
    _ ≤ 2 * Real.exp T := by linarith
    _ ≤ Real.exp (9 * T) * Real.exp T := mul_le_mul_of_nonneg_right hfactor (Real.exp_nonneg _)
    _ = Real.exp (10 * T) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ R := hR

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_PhysicalTuplePoisson
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Transferring each genuine distinct-prime term to positive frequencies -/

namespace Ostmann

open scoped BigOperators SchwartzMap FourierTransform ComplexConjugate

theorem ofReal_re_of_conj_eq (z : ℂ) (h : conj z = z) : (z.re : ℂ) = z := by
  have hi := congrArg Complex.im h
  simp only [Complex.conj_im] at hi
  have hz : z.im = 0 := by linarith
  exact Complex.ext (by simp) (by simp [hz])

theorem physical_tuple_jacobi_norm (Q P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (D : ∀ p : ℕ, Finset (ZMod p)) (ψ : 𝓢(ℝ, ℂ))
    (hreal : ∀ x, conj (ψ x) = ψ x) (X : ℝ)
    (ε : ℕ → ℝ) (hε : ∀ p ∈ P, ε p = 1 ∨ ε p = -1) (t : ℕ → ℤ)
    {k : ℕ} (e : Fin k ↪ P) (tM : ℤ)
    (ht : ∀ i, (tM : ZMod (e i).val) = (t (e i).val : ZMod (e i).val)) :
    |∑' n : ℤ, physicalWeight Q D ψ X n * ∏ i, orientedQuadraticValue ε t n (e i).val| =
      ‖∑' n : ℤ, (amplificationWeight Q D n : ℂ) *
        (jacobiSym (n - tM) (primeTupleProduct P e) : ℂ) * ψ ((n : ℝ) / X)‖ := by
  have hp (n : ℤ) : physicalWeight Q D ψ X n * ∏ i, orientedQuadraticValue ε t n (e i).val =
      (∏ i, ε (e i).val) * amplificationWeight Q D n *
        (jacobiSym (n - tM) (primeTupleProduct P e) : ℝ) * (ψ ((n : ℝ) / X)).re := by
    simp only [physicalWeight, orientedQuadraticValue, Finset.prod_mul_distrib]
    rw [← jacobi_primeTuple_translation P hP e t tM n ht]
    ring
  have he : (((∑' n : ℤ, physicalWeight Q D ψ X n *
        ∏ i, orientedQuadraticValue ε t n (e i).val) : ℝ) : ℂ) =
      (∏ i, (ε (e i).val : ℂ)) * ∑' n : ℤ, (amplificationWeight Q D n : ℂ) *
        (jacobiSym (n - tM) (primeTupleProduct P e) : ℂ) * ψ ((n : ℝ) / X) := by
    rw [Complex.ofReal_tsum, ← tsum_mul_left]
    apply tsum_congr
    intro n
    rw [hp]
    push_cast
    rw [ofReal_re_of_conj_eq _ (hreal _)]
    ring
  have hc : ‖∏ i, (ε (e i).val : ℂ)‖ = 1 := by
    rw [norm_prod]
    have hh (i : Fin k) : ‖(ε (e i).val : ℂ)‖ = 1 := by
      rcases hε _ (e i).property with h | h <;> rw [h] <;> norm_num
    simp only [hh, Finset.prod_const_one]
  simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs, hc, one_mul] using congrArg norm he

theorem physical_tuple_positive_bound (Q P : Finset ℕ)
    (hQ : ∀ p ∈ Q, p.Prime) (hP : ∀ p ∈ P, p.Prime) (hodd : ∀ p ∈ P, Odd p)
    (D : ∀ p : ℕ, Finset (ZMod p)) (ψ : 𝓢(ℝ, ℂ))
    (hreal : ∀ x, conj (ψ x) = ψ x) (X H : ℝ) (hX : 0 < X) (hH : 0 ≤ H)
    (ε : ℕ → ℝ) (hε : ∀ p ∈ P, ε p = 1 ∨ ε p = -1) (t : ℕ → ℤ)
    {k : ℕ} (hk : 0 < k) (e : Fin k ↪ P)
    (hcop : Q.toList.prod.Coprime (primeTupleProduct P e)) (N h₀ : ℕ)
    (hcut : H * ((primeTupleProduct P e : ℝ) / X) * Q.toList.prod ≤ N)
    (hsupp : ∀ x : ℝ, H < x → 𝓕 ψ x = 0)
    (tM : ℤ) (htM : 0 ≤ tM) (htMlt : tM < primeTupleProduct P e)
    (ht : ∀ i, (tM : ZMod (e i).val) = (t (e i).val : ZMod (e i).val))
    (hlift : (Q.toList.prod : ℤ) ∣ tM + (primeTupleProduct P e : ℤ) * h₀) :
    |∑' n : ℤ, physicalWeight Q D ψ X n * ∏ i, orientedQuadraticValue ε t n (e i).val| ≤
      2 * Real.sqrt X * ‖originalPositiveFourier Q hQ D (primeTupleProduct P e) N h₀
        ((tM : ℝ) / primeTupleProduct P e) ((primeTupleProduct P e : ℝ) / X) (𝓕 ψ)‖ := by
  let : NeZero (primeTupleProduct P e) := ⟨(primeTupleProduct_pos P hP e).ne'⟩
  have hval : ((tM : ZMod (primeTupleProduct P e)).val : ℤ) = tM := by
    rw [ZMod.val_intCast, Int.emod_eq_of_lt htM htMlt]
  have hr : (((tM : ZMod (primeTupleProduct P e)).val : ℕ) : ℝ) = tM := by
    exact_mod_cast hval
  rw [physical_tuple_jacobi_norm Q P hP D ψ hreal X ε hε t e tM ht]
  have hh := amplified_jacobi_positive_bound Q hQ D (primeTupleProduct P e) N h₀ hcop
    (primeTupleProduct_squarefree P hP e) (primeTupleProduct_odd P hodd e)
    (primeTupleProduct_one_lt P hP hk e) (tM : ZMod (primeTupleProduct P e))
    (by simpa only [hval] using hlift) ψ hreal X H hX hH hcut hsupp
  simpa only [hval, hr] using hh

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_RepeatRemovalBudget
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Explicit numerical budgets for the relative repeat-removal error -/

namespace Ostmann

open Filter Asymptotics

/-- A shift of at most one quarter of the inverse moment order changes the
moment by a factor less than `3/2`. -/
theorem moment_small_shift (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (k : ℕ) (hk : 0 < k) (hsmall : 4 * k * B ≤ A) :
    (A + B) ^ k ≤ (3 / 2 : ℝ) * A ^ k := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  by_cases hA0 : A = 0
  · have hB0 : B = 0 := by nlinarith
    simp [hA0, hB0, hk.ne']
  have hApos : 0 < A := lt_of_le_of_ne hA (Ne.symm hA0)
  have hkx : (k : ℝ) * (B / A) ≤ 1 / 4 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 4)).mpr
    rw [show ((k : ℝ) * (B / A)) * 4 = (4 * k * B) / A by ring]
    exact (div_le_one hApos).mpr hsmall
  have he : Real.exp (1 / 4 : ℝ) ≤ 3 / 2 := by
    have hh := Real.exp_bound_div_one_sub_of_interval
      (by norm_num : (0 : ℝ) ≤ 1 / 4) (by norm_num : (1 / 4 : ℝ) < 1)
    norm_num at hh ⊢
    linarith
  calc
    (A + B) ^ k = A ^ k * (1 + B / A) ^ k := by
      rw [← mul_pow]
      congr 1
      field_simp
    _ ≤ A ^ k * (Real.exp (B / A)) ^ k := by
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg hA k)
      apply pow_le_pow_left₀ (by positivity)
      simpa only [add_comm] using Real.add_one_le_exp (B / A)
    _ = A ^ k * Real.exp (k * (B / A)) := by rw [Real.exp_nat_mul]
    _ ≤ A ^ k * Real.exp (1 / 4) := by gcongr
    _ ≤ _ := by nlinarith [pow_nonneg hA k]

/-- The squared form avoids logarithms of either moment and is convenient
when inserting `I≥sqrt(X)*exp(.016K)` and `I₀≤C*X`. -/
theorem repeat_shift_of_squared_budget (I I₀ : ℝ) (hI : 0 ≤ I) (hI₀ : 0 ≤ I₀)
    (J k : ℕ) (hJ : 0 < J) (hk : 0 < k)
    (hbudget : ((16 * (k : ℝ) ^ 3 / J) ^ k) * I₀ ^ 2 ≤ I ^ 2) :
    4 * k * ((Real.sqrt ((k : ℝ) * J) / J) * I₀ ^ (1 / (k : ℝ))) ≤
      I ^ (1 / (k : ℝ)) := by
  have hJR : (0 : ℝ) < J := by exact_mod_cast hJ
  have hKR : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have hroot₀ : (I₀ ^ (1 / (k : ℝ))) ^ k = I₀ := by
    simpa only [one_div] using Real.rpow_inv_natCast_pow hI₀ hk.ne'
  have hroot : (I ^ (1 / (k : ℝ))) ^ k = I := by
    simpa only [one_div] using Real.rpow_inv_natCast_pow hI hk.ne'
  have hb : (4 * k * (Real.sqrt ((k : ℝ) * J) / J)) ^ 2 = 16 * (k : ℝ) ^ 3 / J := by
    rw [mul_pow, div_pow, Real.sq_sqrt (mul_nonneg hKR hJR.le)]
    field_simp
    ring
  have hh : ((4 * k * (Real.sqrt ((k : ℝ) * J) / J)) ^ k * I₀) ^ 2 ≤ I ^ 2 := by
    rw [mul_pow, ← pow_mul, mul_comm k 2, pow_mul, hb]
    exact hbudget
  have hh' : (4 * k * (Real.sqrt ((k : ℝ) * J) / J)) ^ k * I₀ ≤ I := by
    nlinarith [show 0 ≤ (4 * k * (Real.sqrt ((k : ℝ) * J) / J)) ^ k * I₀ by positivity]
  apply (pow_le_pow_iff_left₀ (by positivity) (Real.rpow_nonneg hI _) hk.ne').mp
  rw [show 4 * (k : ℝ) * ((Real.sqrt ((k : ℝ) * J) / J) * I₀ ^ (1 / (k : ℝ))) =
    (4 * k * (Real.sqrt ((k : ℝ) * J) / J)) * I₀ ^ (1 / (k : ℝ)) by ring,
    mul_pow, hroot₀, hroot]
  exact hh'

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_RepeatRemovalAsymptotics
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The chosen prime population makes the relative deletion error small -/

namespace Ostmann

open Filter Asymptotics

theorem eventual_repeat_power_budget (C ε : ℝ) (hC : 1 ≤ C) (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, ∀ (k : ℕ) (K : ℝ),
      (k : ℝ) ≤ 2 * T ^ (3 / 5 : ℝ) →
      T ^ (9999999 / 10000000 : ℝ) / 1000 ≤ K →
      (16 * C * T * (k : ℝ) ^ 3) ^ k * C ^ 2 ≤ Real.exp (ε * K) := by
  let B := 128 * C
  let D := 2 * B + 8 + 2 * C
  have hC0 : 0 ≤ C := by linarith
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hl := (isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 / 10 by norm_num)).bound zero_lt_one
  have hp := (tendsto_rpow_atTop
    (show (0 : ℝ) < 9999999 / 10000000 - 7 / 10 by norm_num)).eventually_ge_atTop
    (1000 * D / ε)
  filter_upwards [hl, hp, eventually_ge_atTop (1 : ℝ)] with T hlog hpow hT k K hk hK
  have hTpos : 0 < T := by linarith
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg hT
  have hlog' : Real.log T ≤ T ^ (1 / 10 : ℝ) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg hlogT,
      abs_of_nonneg (Real.rpow_nonneg hTpos.le _), one_mul] using hlog
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have hρ : T ^ (3 / 5 : ℝ) ≤ T := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hT (show (3 / 5 : ℝ) ≤ 1 by norm_num)
  have hkT : (k : ℝ) ≤ 2 * T := hk.trans (by gcongr)
  have hbase : 16 * C * T * (k : ℝ) ^ 3 ≤ Real.exp (B + 4 * Real.log T) := by
    calc
      _ ≤ 16 * C * T * (2 * T) ^ 3 := by gcongr
      _ = B * T ^ 4 := by dsimp [B]; ring
      _ ≤ Real.exp B * T ^ 4 := by gcongr; linarith [Real.add_one_le_exp B]
      _ = Real.exp (B + 4 * Real.log T) := by
        rw [Real.exp_add]
        congr 1
        simpa only [Nat.cast_ofNat, Real.exp_log hTpos] using
          (Real.exp_nat_mul (Real.log T) 4).symm
  have hklog : (k : ℝ) * Real.log T ≤ 2 * T ^ (7 / 10 : ℝ) := by
    calc
      _ ≤ (2 * T ^ (3 / 5 : ℝ)) * T ^ (1 / 10 : ℝ) :=
        mul_le_mul hk hlog' hlogT (by positivity)
      _ = _ := by rw [mul_assoc, ← Real.rpow_add hTpos]; norm_num
  have hρ' : T ^ (3 / 5 : ℝ) ≤ T ^ (7 / 10 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hT (by norm_num)
  have h1 : (1 : ℝ) ≤ T ^ (7 / 10 : ℝ) := Real.one_le_rpow hT (by norm_num)
  have hexp : (k : ℝ) * (B + 4 * Real.log T) + 2 * C ≤ D * T ^ (7 / 10 : ℝ) := by
    have hk7 : (k : ℝ) ≤ 2 * T ^ (7 / 10 : ℝ) :=
      hk.trans (mul_le_mul_of_nonneg_left hρ' (by norm_num))
    have hkb := mul_le_mul_of_nonneg_left hk7 hB
    have hc := mul_le_mul_of_nonneg_left h1 (show 0 ≤ 2 * C by positivity)
    dsimp [D]
    nlinarith only [hkb, hc, hklog]
  have hbudget : D * T ^ (7 / 10 : ℝ) ≤ ε * K := by
    have hp' := (div_le_iff₀ hε).mp hpow
    have hh := mul_le_mul_of_nonneg_right hp' (Real.rpow_nonneg hTpos.le (7 / 10 : ℝ))
    have heq : T ^ (9999999 / 10000000 - 7 / 10 : ℝ) * T ^ (7 / 10 : ℝ) =
        T ^ (9999999 / 10000000 : ℝ) := by
      rw [← Real.rpow_add hTpos]
      norm_num
    have heq' : (T ^ (9999999 / 10000000 - 7 / 10 : ℝ) * ε) * T ^ (7 / 10 : ℝ) =
        ε * T ^ (9999999 / 10000000 : ℝ) := by rw [mul_right_comm, heq, mul_comm]
    rw [heq'] at hh
    have hK' := mul_le_mul_of_nonneg_left hK hε.le
    nlinarith only [hh, hK']
  calc
    _ ≤ (Real.exp (B + 4 * Real.log T)) ^ k * (Real.exp C) ^ 2 := by
      apply mul_le_mul (pow_le_pow_left₀ (by positivity) hbase k) _ (sq_nonneg C) (by positivity)
      exact pow_le_pow_left₀ hC0 (by linarith [Real.add_one_le_exp C]) 2
    _ = Real.exp ((k : ℝ) * (B + 4 * Real.log T) + 2 * C) := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
      norm_num
    _ ≤ _ := Real.exp_le_exp.mpr (hexp.trans hbudget)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_AmplifiedRepeatRemoval
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Retaining the amplified moment after deleting all repeated primes -/

namespace Ostmann

open Filter
open scoped BigOperators Classical

theorem repeat_squared_budget (C T K X I I₀ : ℝ) (J k : ℕ)
    (hX : 0 < X) (hI₀ : 0 ≤ I₀)
    (hJ : 0 < J) (hpop : Real.exp T ≤ C * T * J)
    (hXk : X ≤ Real.exp ((k : ℝ) * T)) (hweight : I₀ ≤ C * X)
    (hmoment : Real.sqrt X * Real.exp ((2 / 125 : ℝ) * K) ≤ I)
    (hnum : (16 * C * T * (k : ℝ) ^ 3) ^ k * C ^ 2 ≤
      Real.exp ((4 / 125 : ℝ) * K)) :
    (16 * (k : ℝ) ^ 3 / J) ^ k * I₀ ^ 2 ≤ I ^ 2 := by
  have hJR : (0 : ℝ) < J := by exact_mod_cast hJ
  have hA : 0 ≤ 16 * (k : ℝ) ^ 3 / J := by positivity
  have ha : (16 * (k : ℝ) ^ 3 / J) * Real.exp T ≤ 16 * C * T * (k : ℝ) ^ 3 := by
    have hq : Real.exp T / J ≤ C * T := (div_le_iff₀ hJR).mpr hpop
    calc
      _ = (16 * (k : ℝ) ^ 3) * (Real.exp T / J) := by ring
      _ ≤ (16 * (k : ℝ) ^ 3) * (C * T) := by gcongr
      _ = _ := by ring
  have hap := pow_le_pow_left₀ (mul_nonneg hA (Real.exp_nonneg T)) ha k
  rw [mul_pow, ← Real.exp_nat_mul] at hap
  have hsquare := pow_le_pow_left₀ hI₀ hweight 2
  rw [mul_pow] at hsquare
  have hmoment2 := pow_le_pow_left₀ (by positivity : 0 ≤ Real.sqrt X * Real.exp ((2 / 125 : ℝ) * K)) hmoment 2
  rw [mul_pow, Real.sq_sqrt hX.le, ← Real.exp_nat_mul] at hmoment2
  norm_num only at hmoment2
  have he : (2 : ℝ) * ((2 / 125 : ℝ) * K) = (4 / 125 : ℝ) * K := by ring
  rw [he] at hmoment2
  calc
    _ ≤ (16 * (k : ℝ) ^ 3 / J) ^ k * (C ^ 2 * X ^ 2) := by gcongr
    _ = ((16 * (k : ℝ) ^ 3 / J) ^ k * X) * (C ^ 2 * X) := by ring
    _ ≤ ((16 * (k : ℝ) ^ 3 / J) ^ k * Real.exp ((k : ℝ) * T)) * (C ^ 2 * X) := by gcongr
    _ ≤ (16 * C * T * (k : ℝ) ^ 3) ^ k * (C ^ 2 * X) := by gcongr
    _ = ((16 * C * T * (k : ℝ) ^ 3) ^ k * C ^ 2) * X := by ring
    _ ≤ Real.exp ((4 / 125 : ℝ) * K) * X := by gcongr
    _ ≤ I ^ 2 := by simpa only [mul_comm] using hmoment2

/-- The actual ternary distinct-prime moment retains at least half of its
positive amplified moment, uniformly for sufficiently large `T`. -/
theorem eventual_amplified_repeat_removal (C : ℝ) (hC : 1 ≤ C) :
    ∀ᶠ T : ℝ in atTop, ∀ {ι A : Type} [Fintype A] [DecidableEq A]
      (w : ι → ℝ) (y : ι → A → ℝ) (k : ℕ) (K X : ℝ),
      (∀ i, 0 ≤ w i) → (∀ i a, y i a = 0 ∨ y i a = 1 ∨ y i a = -1) →
      Summable w → 0 < k → Even k → k ≤ Fintype.card A →
      (k : ℝ) ≤ 2 * T ^ (3 / 5 : ℝ) →
      T ^ (9999999 / 10000000 : ℝ) / 1000 ≤ K → 0 < X →
      Real.exp T ≤ C * T * Fintype.card A → X ≤ Real.exp ((k : ℝ) * T) →
      (∑' i, w i) ≤ C * X →
      Real.sqrt X * Real.exp ((2 / 125 : ℝ) * K) ≤
        (∑' i, w i * ternaryMean (y i) ^ k) →
      (∑' i, w i * ternaryMean (y i) ^ k) / 2 ≤
        (∑' i, w i * ternaryDistinctMean (y i) k) := by
  filter_upwards [eventual_repeat_power_budget C (4 / 125) hC (by norm_num),
    eventually_ge_atTop (0 : ℝ)] with T hnum _hT
  intro ι A _ _ w y k K X hw hy hws hk heven hkA hkU hK hX hpop hXk hweight hmoment
  let I := ∑' i, w i * ternaryMean (y i) ^ k
  let I₀ := ∑' i, w i
  have hI₀ : 0 ≤ I₀ := tsum_nonneg hw
  have hI : 0 ≤ I := le_trans (by positivity) hmoment
  have hJ : 0 < Fintype.card A := lt_of_lt_of_le hk hkA
  have hsq := repeat_squared_budget C T K X I I₀ (Fintype.card A) k
    hX hI₀ hJ hpop hXk hweight hmoment (hnum k K hkU hK)
  have hsmall := repeat_shift_of_squared_budget I I₀ hI hI₀ (Fintype.card A) k hJ hk hsq
  have hshift := moment_small_shift (I ^ (1 / (k : ℝ)))
    ((Real.sqrt ((k : ℝ) * Fintype.card A) / Fintype.card A) * I₀ ^ (1 / (k : ℝ)))
    (Real.rpow_nonneg hI _) (by positivity) k hk hsmall
  have hroot : (I ^ (1 / (k : ℝ))) ^ k = I := by
    simpa only [one_div] using Real.rpow_inv_natCast_pow hI hk.ne'
  rw [hroot] at hshift
  have herr := (weighted_ternary_distinct_moment w y hw hy k hk heven hkA hws).2
  change |(∑' i, w i * ternaryDistinctMean (y i) k) - I| ≤ _ at herr
  have hl := (abs_le.mp herr).1
  change I / 2 ≤ _
  linarith only [hl, hshift]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_DistinctMomentAverage
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Passing the physical distinct moment to a uniform finite average -/

namespace Ostmann

open scoped BigOperators Classical

theorem weighted_distinct_average_le {ι A : Type*} [Fintype A] [DecidableEq A]
    (w : ι → ℝ) (y : ι → A → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hy : ∀ i a, |y i a| ≤ 1) (hws : Summable w)
    (k : ℕ) (F : (Fin k ↪ A) → ℝ) (C : ℝ)
    (hF : ∀ e, 0 ≤ F e) (hC : 0 ≤ C) (hkA : k ≤ Fintype.card A)
    (hb : ∀ e, |∑' i, w i * ∏ j, y i (e j)| ≤ C * F e) :
    (∑' i, w i * ternaryDistinctMean (y i) k) ≤
      C * ((Fintype.card (Fin k ↪ A) : ℝ)⁻¹ * ∑ e, F e) := by
  have hs (e : Fin k ↪ A) : Summable (fun i => w i * ∏ j, y i (e j)) := by
    apply Summable.of_norm_bounded hws
    intro i
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw i), Finset.abs_prod]
    have hp : (∏ j : Fin k, |y i (e j)|) ≤ 1 := by
      exact (Finset.prod_le_prod (fun j _ => abs_nonneg _) (fun j _ => hy i (e j))).trans_eq
        (Finset.prod_const_one)
    exact mul_le_of_le_one_right (hw i) hp
  have he : (∑' i, w i * ternaryDistinctMean (y i) k) =
      (∑ e : Fin k ↪ A, ∑' i, w i * ∏ j, y i (e j)) / (Fintype.card A : ℝ) ^ k := by
    simp only [ternaryDistinctMean, ← mul_div_assoc, Finset.mul_sum]
    rw [tsum_div_const, Summable.tsum_finsetSum (fun e _ => hs e)]
  have hsum : (∑ e : Fin k ↪ A, ∑' i, w i * ∏ j, y i (e j)) ≤ C * ∑ e, F e := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun e _ => (le_abs_self _).trans (hb e))
  have hn : (Fintype.card (Fin k ↪ A) : ℝ) ≤ (Fintype.card A : ℝ) ^ k := by
    exact_mod_cast (show Fintype.card (Fin k ↪ A) ≤ Fintype.card A ^ k by
      rw [Fintype.card_embedding_eq, Fintype.card_fin]
      exact Nat.descFactorial_le_pow _ _)
  have hnpos : (0 : ℝ) < Fintype.card (Fin k ↪ A) := by
    exact_mod_cast (show 0 < Fintype.card (Fin k ↪ A) by
      rw [Fintype.card_embedding_eq, Fintype.card_fin]
      exact Nat.descFactorial_pos.mpr hkA)
  rw [he]
  calc
    _ ≤ (C * ∑ e, F e) / (Fintype.card A : ℝ) ^ k :=
      div_le_div_of_nonneg_right hsum (by positivity)
    _ ≤ (C * ∑ e, F e) / Fintype.card (Fin k ↪ A) :=
      div_le_div_of_nonneg_left (mul_nonneg hC (Finset.sum_nonneg (fun e _ => hF e))) hnpos hn
    _ = _ := by ring

/-- The amplified lower bound forces the uniform first moment needed by the
finite witness-probability argument. -/
theorem amplified_distinct_first_mean {ι A : Type*} [Fintype A] [DecidableEq A]
    (w : ι → ℝ) (y : ι → A → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hy : ∀ i a, |y i a| ≤ 1) (hws : Summable w)
    (k : ℕ) (F : (Fin k ↪ A) → ℝ) (X K : ℝ) (hX : 0 < X) (hK : 3000 ≤ K)
    (hF : ∀ e, 0 ≤ F e) (hkA : k ≤ Fintype.card A)
    (hb : ∀ e, |∑' i, w i * ∏ j, y i (e j)| ≤ 2 * Real.sqrt X * F e)
    (hlower : Real.sqrt X * Real.exp ((2 / 125 : ℝ) * K) / 2 ≤
      ∑' i, w i * ternaryDistinctMean (y i) k) :
    Real.exp ((3 / 200 : ℝ) * K) ≤
      (Fintype.card (Fin k ↪ A) : ℝ)⁻¹ * ∑ e, F e := by
  have hh := hlower.trans (weighted_distinct_average_le w y hw hy hws k F
    (2 * Real.sqrt X) hF (by positivity) hkA hb)
  have hroot := Real.sqrt_pos.mpr hX
  have hfour : Real.exp ((2 / 125 : ℝ) * K) / 4 ≤
      (Fintype.card (Fin k ↪ A) : ℝ)⁻¹ * ∑ e, F e := by nlinarith
  apply le_trans _ hfour
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 4)).mpr
  have hexp : (4 : ℝ) ≤ Real.exp (K / 1000) := by
    have h := Real.add_one_le_exp (K / 1000)
    linarith
  calc
    _ ≤ Real.exp ((3 / 200 : ℝ) * K) * Real.exp (K / 1000) := by gcongr
    _ = Real.exp ((2 / 125 : ℝ) * K) := by rw [← Real.exp_add]; congr 1; ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_PhysicalAmplificationBudget
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original amplification dominates all fixed-bias and tail losses -/

namespace Ostmann

open Filter Asymptotics

theorem eventual_amplification_log_loss (C ε : ℝ) (hC : 0 ≤ C) (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, ∀ k K : ℝ,
      0 ≤ k → k ≤ 2 * T ^ (3 / 5 : ℝ) →
      T ^ (9999999 / 10000000 : ℝ) / 1000 ≤ K →
      C * (1 + k) + 6 * Real.log T ≤ ε * K := by
  let D := 3 * C + 6
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hl := (isLittleO_log_rpow_atTop (show (0 : ℝ) < 3 / 5 by norm_num)).bound zero_lt_one
  have hp := (tendsto_rpow_atTop
    (show (0 : ℝ) < 9999999 / 10000000 - 3 / 5 by norm_num)).eventually_ge_atTop
    (1000 * D / ε)
  filter_upwards [hl, hp, eventually_ge_atTop (1 : ℝ)] with T hlog hpow hT k K hk hkU hK
  have hTpos : 0 < T := by linarith
  have hlog' : Real.log T ≤ T ^ (3 / 5 : ℝ) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hT),
      abs_of_nonneg (Real.rpow_nonneg hTpos.le _), one_mul] using hlog
  have h1 : (1 : ℝ) ≤ T ^ (3 / 5 : ℝ) := Real.one_le_rpow hT (by norm_num)
  have hb : C * (1 + k) + 6 * Real.log T ≤ D * T ^ (3 / 5 : ℝ) := by
    have hc := mul_le_mul_of_nonneg_left h1 hC
    have hkc := mul_le_mul_of_nonneg_left hkU hC
    dsimp [D]
    nlinarith only [hc, hkc, hlog']
  have hp' := (div_le_iff₀ hε).mp hpow
  have hh := mul_le_mul_of_nonneg_right hp' (Real.rpow_nonneg hTpos.le (3 / 5 : ℝ))
  have he : (T ^ (9999999 / 10000000 - 3 / 5 : ℝ) * ε) * T ^ (3 / 5 : ℝ) =
      ε * T ^ (9999999 / 10000000 : ℝ) := by
    rw [mul_right_comm, ← Real.rpow_add hTpos]
    norm_num
    ring
  rw [he] at hh
  have hK' := mul_le_mul_of_nonneg_left hK hε.le
  have hb' : D * T ^ (3 / 5 : ℝ) ≤ ε * K := by nlinarith only [hh, hK']
  exact hb.trans hb'

theorem eventual_physical_amplification_factor (a c : ℝ) (ha : 0 < a) (hc : 0 < c) :
    ∀ᶠ T : ℝ in atTop, ∀ (k : ℕ) (K : ℝ),
      (k : ℝ) ≤ 2 * T ^ (3 / 5 : ℝ) →
      T ^ (9999999 / 10000000 : ℝ) / 1000 ≤ K →
      Real.exp ((2 / 125 : ℝ) * K) ≤ a * Real.exp (K / 50) * c ^ k / T ^ 6 := by
  let C := |Real.log a| + |Real.log c|
  have hC : 0 ≤ C := by dsimp [C]; positivity
  filter_upwards [eventual_amplification_log_loss C (1 / 250) hC (by norm_num),
    eventually_ge_atTop (1 : ℝ)] with T hbudget hT k K hk hK
  have hTpos : 0 < T := by linarith
  have hb := hbudget k K (Nat.cast_nonneg _) hk hK
  have hl : -(K / 250) ≤ Real.log a + (k : ℝ) * Real.log c - 6 * Real.log T := by
    have ha' := neg_abs_le (Real.log a)
    have hc' := mul_le_mul_of_nonneg_left (neg_abs_le (Real.log c)) (Nat.cast_nonneg k)
    have hka := mul_nonneg (abs_nonneg (Real.log a)) (Nat.cast_nonneg (α := ℝ) k)
    dsimp [C] at hb
    nlinarith only [hb, ha', hc', hka, abs_nonneg (Real.log c)]
  have he := Real.exp_le_exp.mpr hl
  have hid : Real.exp (Real.log a + (k : ℝ) * Real.log c - 6 * Real.log T) =
      a * c ^ k / T ^ 6 := by
    rw [Real.exp_sub, Real.exp_add, Real.exp_log ha, Real.exp_nat_mul,
      Real.exp_log hc]
    have hden : Real.exp (6 * Real.log T) = T ^ 6 := by
      simpa only [Nat.cast_ofNat, Real.exp_log hTpos] using Real.exp_nat_mul (Real.log T) 6
    rw [hden]
  rw [hid] at he
  have hm := mul_le_mul_of_nonneg_left he (Real.exp_nonneg (K / 50))
  have hleft : Real.exp (K / 50) * Real.exp (-(K / 250)) =
      Real.exp ((2 / 125 : ℝ) * K) := by rw [← Real.exp_add]; congr 1; ring
  rw [hleft] at hm
  convert hm using 1
  all_goals try with_reducible_and_instances rfl
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_OriginalAmplifiedMoment
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original positive amplified moment and distinct-prime lower bound -/

namespace Ostmann

open Filter
open scoped BigOperators SchwartzMap FourierTransform

theorem eventual_physical_amplification_lower (cψ a c : ℝ)
    (hcψ : 0 < cψ) (ha : 0 < a) (hc : 0 < c) :
    ∀ᶠ T : ℝ in atTop, ∀ (Q P : Finset ℕ) (_hQ : ∀ p ∈ Q, p.Prime),
      0 < P.card → ∀ (D : ∀ p : ℕ, Finset (ZMod p)) (ψ : 𝓢(ℝ, ℂ)) (X : ℝ),
      0 < X → (∀ x, 0 ≤ (ψ x).re) →
      (∀ x ∈ Set.Icc (0 : ℝ) 1, cψ ≤ (ψ x).re) →
      ∀ (S : Finset ℤ), (∀ n ∈ S, 0 ≤ (n : ℝ) ∧ (n : ℝ) ≤ X) →
      a * Real.sqrt X / T ^ 6 ≤ (S.card : ℝ) →
      (∀ p ∈ Q, (D p).card / (p : ℝ) ≤ 2 / 3) →
      (∀ n ∈ S, ∀ p ∈ Q, (n : ZMod p) ∈ D p) →
      ∀ (ε : ℕ → ℝ) (t : ℕ → ℤ), (∀ p ∈ P, ε p = 1 ∨ ε p = -1) →
      (∀ p ∈ P, (S.card : ℝ) * c ≤ ∑ n ∈ S, orientedQuadraticValue ε t n p) →
      ∀ k : ℕ, Even k → (k : ℝ) ≤ 2 * T ^ (3 / 5 : ℝ) →
      T ^ (9999999 / 10000000 : ℝ) / 1000 ≤ (Q.card : ℝ) →
      Real.sqrt X * Real.exp ((2 / 125 : ℝ) * Q.card) ≤
        ∑' n : ℤ, physicalWeight Q D ψ X n *
          ternaryMean (fun p : P => orientedQuadraticValue ε t n p) ^ k := by
  filter_upwards [eventual_physical_amplification_factor (cψ * a) c (mul_pos hcψ ha) hc,
    eventually_ge_atTop (1 : ℝ)] with T hf hT
  intro Q P hQ hP D ψ X hX hψ0 hψ1 S hS hcard hD hSD ε t hε hbias k heven hk hK
  have hm := physical_moment_from_tail_bias Q P hQ hP D ψ X cψ c hX hcψ.le hc.le
    hψ0 hψ1 S hS hD hSD ε t hε hbias k heven
  have hnum := mul_le_mul_of_nonneg_left (hf k Q.card hk hK) (Real.sqrt_nonneg X)
  calc
    _ ≤ Real.sqrt X * ((cψ * a) * Real.exp ((Q.card : ℝ) / 50) * c ^ k / T ^ 6) := hnum
    _ = (cψ * Real.exp ((Q.card : ℝ) / 50)) * (a * Real.sqrt X / T ^ 6) * c ^ k := by ring
    _ ≤ (cψ * Real.exp ((Q.card : ℝ) / 50)) * S.card * c ^ k := by gcongr
    _ ≤ _ := hm

/-- Combining the physical amplification, the exact total-weight Poisson
identity and the derived repeat-removal estimate. -/
theorem eventual_original_distinct_moment (cψ a c C : ℝ)
    (hcψ : 0 < cψ) (ha : 0 < a) (hc : 0 < c) (hC : 1 ≤ C) :
    ∀ᶠ T : ℝ in atTop, ∀ (Q P : Finset ℕ) (_hQ : ∀ p ∈ Q, p.Prime)
      (D : ∀ p : ℕ, Finset (ZMod p)) (ψ : 𝓢(ℝ, ℂ)) (X H : ℝ),
      0 < X → (∀ x, 0 ≤ (ψ x).re) →
      (∀ x ∈ Set.Icc (0 : ℝ) 1, cψ ≤ (ψ x).re) →
      H < X / Q.toList.prod → (∀ x : ℝ, H < |x| → 𝓕 ψ x = 0) →
      (𝓕 ψ 0).re ≤ C →
      ∀ (S : Finset ℤ), (∀ n ∈ S, 0 ≤ (n : ℝ) ∧ (n : ℝ) ≤ X) →
      a * Real.sqrt X / T ^ 6 ≤ (S.card : ℝ) →
      (∀ p ∈ Q, (D p).card / (p : ℝ) ≤ 2 / 3) →
      (∀ n ∈ S, ∀ p ∈ Q, (n : ZMod p) ∈ D p) →
      ∀ (ε : ℕ → ℝ) (t : ℕ → ℤ), (∀ p ∈ P, ε p = 1 ∨ ε p = -1) →
      (∀ p ∈ P, (S.card : ℝ) * c ≤ ∑ n ∈ S, orientedQuadraticValue ε t n p) →
      ∀ k : ℕ, 0 < k → Even k → k ≤ P.card →
      (k : ℝ) ≤ 2 * T ^ (3 / 5 : ℝ) →
      T ^ (9999999 / 10000000 : ℝ) / 1000 ≤ (Q.card : ℝ) →
      Real.exp T ≤ C * T * P.card → X ≤ Real.exp ((k : ℝ) * T) →
      Real.sqrt X * Real.exp ((2 / 125 : ℝ) * Q.card) / 2 ≤
        ∑' n : ℤ, physicalWeight Q D ψ X n *
          ternaryDistinctMean (fun p : P => orientedQuadraticValue ε t n p) k := by
  filter_upwards [eventual_physical_amplification_lower cψ a c hcψ ha hc,
    eventual_amplified_repeat_removal C hC] with T hamp hrep
  intro Q P hQ D ψ X H hX hψ0 hψ1 hH hsupp hCψ S hS hcard hD hSD
    ε t hε hbias k hk heven hkP hkU hK hpop hXk
  have hP : 0 < P.card := lt_of_lt_of_le hk hkP
  have hm := hamp Q P hQ hP D ψ X hX hψ0 hψ1 S hS hcard hD hSD ε t hε hbias k heven hkU hK
  have hweight : (∑' n, physicalWeight Q D ψ X n) ≤ C * X := by
    rw [amplification_total_weight Q hQ D ψ X H hX hH hsupp]
    nlinarith only [mul_le_mul_of_nonneg_left hCψ hX.le]
  have hd := hrep (physicalWeight Q D ψ X)
    (fun n (p : P) => orientedQuadraticValue ε t n p) k Q.card X
    (physicalWeight_nonneg Q hQ D ψ hψ0 X)
    (fun n p => orientedQuadraticValue_ternary ε t n p (hε p p.property))
    (physicalWeight_summable Q hQ D ψ X hX) hk heven (by simpa using hkP)
    hkU hK hX (by simpa using hpop) hXk hweight hm
  exact (div_le_div_of_nonneg_right hm (by norm_num : (0 : ℝ) ≤ 2)).trans hd

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_OriginalMomentBudget
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Numerical budgets for the original Fourier moments -/

namespace Ostmann

open Filter
open scoped BigOperators

theorem eventual_two_pow_moment_budget :
    ∀ᶠ T : ℝ in atTop, ∀ (k : ℕ) (K : ℝ),
      1 ≤ k → (k : ℝ) ≤ 2 * T ^ (3 / 5 : ℝ) →
      T ^ (9999999 / 10000000 : ℝ) / 1000 ≤ K →
      (2 : ℝ) ^ k ≤ Real.exp (K / 10) := by
  filter_upwards [eventual_repeat_power_budget 1 (1 / 10) (by norm_num) (by norm_num),
    eventually_ge_atTop (1 : ℝ)] with T hb hT k K hk hkU hK
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hbase : (2 : ℝ) ≤ 16 * 1 * T * (k : ℝ) ^ 3 := by
    have hpow : (1 : ℝ) ≤ (k : ℝ) ^ 3 := one_le_pow₀ hk1
    nlinarith
  have hh := hb k K hkU hK
  norm_num only [one_pow, mul_one] at hh
  exact (pow_le_pow_left₀ (by norm_num) hbase k).trans (by simpa only [one_mul, mul_one, div_eq_mul_inv, mul_comm] using hh)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_CommonCenterConcreteMoments
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual integer-lift factorial moments used for common centers -/

namespace Ostmann

open scoped BigOperators

/-- The lower-order moment upper bound follows from counting residue-class
lifts of each ordered distinct prime tuple. -/
theorem interval_factorial_moment_le (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime)
    (a : ℤ) (t : ℕ → ℤ) (r H Z : ℕ) (hZ : 0 < Z) (hmin : ∀ p ∈ P, Z ≤ p) :
    (∑ n : (Finset.Ico (-(H : ℤ)) (H + 1)),
      ((matchingPrimes P a t n.1).card.descFactorial r : ℝ)) ≤
    (P.card.descFactorial r : ℝ) * ((2 * (H : ℝ) + 1) / (Z : ℝ) ^ r + 1) := by
  classical
  let S := fun n : (Finset.Ico (-(H : ℤ)) (H + 1)) => matchingPrimeSubtype P a t n.1
  have hcount (e : Fin r ↪ P) :
      (Fintype.card {n : (Finset.Ico (-(H : ℤ)) (H + 1)) // ∀ i, e i ∈ S n} : ℝ) ≤
        (2 * (H : ℝ) + 1) / (Z : ℝ) ^ r + 1 := by
    rw [Fintype.card_congr (intervalMatchingLiftEquiv P a t e H), Fintype.card_coe]
    have h := card_integerLiftSet_le_uniform P hprime a t e H Z hZ hmin
    have hc := Rat.cast_le (K := ℝ).mpr h
    push_cast at hc
    exact hc
  calc
    _ = ∑ e : Fin r ↪ P,
        (Fintype.card {n : (Finset.Ico (-(H : ℤ)) (H + 1)) // ∀ i, e i ∈ S n} : ℝ) := by
      have h := sum_matching_factorials S r
      dsimp [S] at h
      simp only [card_matchingPrimeSubtype] at h
      exact_mod_cast h
    _ ≤ ∑ _e : Fin r ↪ P, ((2 * (H : ℝ) + 1) / (Z : ℝ) ^ r + 1) :=
      Finset.sum_le_sum fun e _ => hcount e
    _ = _ := by simp; ring

/-- A supplied family of witnessed tuples gives the high moment directly. -/
theorem interval_factorial_moment_ge (P : Finset ℕ) (a : ℤ) (t : ℕ → ℤ) (r H : ℕ)
    (E : Finset (Fin r ↪ P))
    (hlift : ∀ e ∈ E, ∃ n ∈ Finset.Ico (-(H : ℤ)) (H + 1),
      ∀ i, ((e i).1 : ℤ) ∣ n - a * t (e i).1) :
    (E.card : ℝ) ≤ ∑ n : (Finset.Ico (-(H : ℤ)) (H + 1)),
      ((matchingPrimes P a t n.1).card.descFactorial r : ℝ) := by
  classical
  have h := card_tuples_le_sum_matching_factorials
    (fun n : (Finset.Ico (-(H : ℤ)) (H + 1)) => matchingPrimeSubtype P a t n.1) r E
    (fun e he => by
      obtain ⟨n, hn, hni⟩ := hlift e he
      exact ⟨⟨n, hn⟩, fun i => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hni i⟩⟩)
  simp only [card_matchingPrimeSubtype] at h
  exact_mod_cast h

/-- The interval length supplies the prime-intersection logarithmic budget. -/
theorem liftInterval_log_difference (H K : ℕ) (V : ℝ)
    (hbudget : Real.log (2 * (H : ℝ)) < (K + 1 : ℕ) * V)
    (n m : ℤ) (hn : n ∈ Finset.Ico (-(H : ℤ)) (H + 1))
    (hm : m ∈ Finset.Ico (-(H : ℤ)) (H + 1)) (hne : n ≠ m) :
    Real.log ((n - m).natAbs : ℝ) < (K + 1 : ℕ) * V := by
  have hn' := Finset.mem_Ico.mp hn
  have hm' := Finset.mem_Ico.mp hm
  have hd : (n - m).natAbs ≤ 2 * H := by omega
  have hp : (0 : ℝ) < (n - m).natAbs := by
    exact_mod_cast Int.natAbs_pos.mpr (sub_ne_zero.mpr hne)
  have hd' : ((n - m).natAbs : ℝ) ≤ 2 * (H : ℝ) := by exact_mod_cast hd
  exact (Real.log_le_log hp hd').trans_lt hbudget

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_CommonCenterFromTuples
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A rational common center from witnessed prime tuples

This is the finite counting step in the paragraph “One common centre for many
primes” of Section 3 of the manuscript. The hypotheses are the actual family
of witnessed tuples and numerical inequalities; the factorial moments and
intersection estimates are proved from the congruences.
-/

namespace Ostmann

open scoped BigOperators

theorem exists_commonCenter_of_tuple_lifts (P : Finset ℕ)
    (a : ℕ) (ha : 0 < a) (t : ℕ → ℤ) (k d K H Z : ℕ) (hd : d ≤ k + 1)
    (A V : ℝ) (hA : 0 < A) (hV : 0 < V) (hZ : 0 < Z)
    (hprime : ∀ p ∈ P, p.Prime) (hap : ∀ p ∈ P, a < p)
    (hmin : ∀ p ∈ P, Z ≤ p) (hlog : ∀ p ∈ P, V ≤ Real.log (p : ℝ))
    (hbudget : Real.log (2 * (H : ℝ)) < (K + 1 : ℕ) * V)
    (hsmall : 2 * K * (P.card : ℝ) ≤ A ^ 2)
    (E : Finset (Fin (k + 1) ↪ P))
    (hlift : ∀ e ∈ E, ∃ n ∈ Finset.Ico (-(H : ℤ)) (H + 1),
      ∀ i, ((e i).1 : ℤ) ∣ n - a * t (e i).1)
    (hpositive : 0 < (E.card : ℝ) - A ^ d * liftMomentUpper P.card (k + 1 - d) H Z) :
    ∃ n ∈ Finset.Ico (-(H : ℤ)) (H + 1), ∃ h : ℤ, ∃ m : ℕ,
      0 < m ∧ m ≤ a ∧ h.natAbs.Coprime m ∧ |h| ≤ |n| ∧
      A ≤ ((matchingPrimes P a t n).card : ℝ) ∧
      (E.card : ℝ) - A ^ d * liftMomentUpper P.card (k + 1 - d) H Z ≤
        2 * P.card * ((matchingPrimes P a t n).card : ℝ) ^ k ∧
      ∀ (p : ℕ) (hp : p ∈ matchingPrimes P a t n),
        let _ : Fact p.Prime := ⟨hprime p (Finset.mem_filter.mp hp).1⟩
        (t p : ZMod p) = (h : ZMod p) / (m : ZMod p) := by
  exact exists_commonCenter_of_lift_moments P (Finset.Ico (-(H : ℤ)) (H + 1))
    a ha t k d K hd A (liftMomentUpper P.card (k + 1 - d) H Z) E.card V
    hA hV hprime hap hlog
    (fun n hn m hm hne => liftInterval_log_difference H K V hbudget n m hn hm hne)
    hsmall (interval_factorial_moment_le P hprime a t (k + 1 - d) H Z hZ hmin)
    (interval_factorial_moment_ge P a t (k + 1) H E hlift) hpositive

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_UniformDenominatorLifts
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Selecting one denominator for a large family of witnessed tuples -/

namespace Ostmann

open scoped BigOperators Classical

theorem exists_uniform_denominator_lifts (P : Finset ℕ) {k : ℕ}
    (E : Finset (Fin k ↪ P)) (Amax H : ℕ) (hAmax : 0 < Amax) (t : ℕ → ℤ)
    (hlift : ∀ e ∈ E, ∃ a ∈ Finset.Icc 1 Amax,
      ∃ n ∈ Finset.Ico (-(H : ℤ)) (H + 1),
        ∀ i, ((e i).1 : ℤ) ∣ n - (a : ℤ) * t (e i).1) :
    ∃ a ∈ Finset.Icc 1 Amax, ∃ E' : Finset (Fin k ↪ P), E' ⊆ E ∧
      (E.card : ℝ) / Amax ≤ E'.card ∧
      ∀ e ∈ E', ∃ n ∈ Finset.Ico (-(H : ℤ)) (H + 1),
        ∀ i, ((e i).1 : ℤ) ∣ n - (a : ℤ) * t (e i).1 := by
  choose a ha h using fun e : E => hlift e.1 e.2
  let D := Finset.Icc 1 Amax
  let f : E → D := fun e => ⟨a e, ha e⟩
  let : Nonempty D := ⟨⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hAmax⟩⟩⟩
  have hcard : Fintype.card D = Amax := by simp [D]
  have hcount : Fintype.card D • ((E.card : ℝ) / Amax) ≤ (Fintype.card E : ℝ) := by
    rw [hcard, nsmul_eq_mul, Fintype.card_coe]
    have hA0 : (Amax : ℝ) ≠ 0 := by exact_mod_cast hAmax.ne'
    rw [mul_div_cancel₀ _ hA0]
  obtain ⟨d, hd⟩ := Fintype.exists_le_card_fiber_of_nsmul_le_card f hcount
  let T := (Finset.univ : Finset E).filter fun e => f e = d
  let E' := T.image Subtype.val
  have hE' : E' ⊆ E := by
    intro e he
    obtain ⟨e', _, rfl⟩ := Finset.mem_image.mp he
    exact e'.2
  have hsize : (E.card : ℝ) / Amax ≤ (E'.card : ℝ) := by
    have hc : E'.card = T.card := Finset.card_image_of_injective _ Subtype.val_injective
    rw [hc]
    exact hd
  refine ⟨d.1, d.2, E', hE', hsize, ?_⟩
  intro e he
  obtain ⟨e', he', rfl⟩ := Finset.mem_image.mp he
  have heq : a e' = d.1 := congrArg Subtype.val (Finset.mem_filter.mp he').2
  simpa only [heq] using h e'

/-- The common-center theorem applies to tuple-dependent denominators:
the finite pigeonhole loss is paid explicitly before the moment argument. -/
theorem exists_commonCenter_of_bounded_denominators (P : Finset ℕ)
    (t : ℕ → ℤ) (k d K H Z Amax : ℕ) (hd : d ≤ k + 1)
    (A V : ℝ) (hA : 0 < A) (hV : 0 < V) (hZ : 0 < Z) (hAmax : 0 < Amax)
    (hprime : ∀ p ∈ P, p.Prime) (hap : ∀ p ∈ P, Amax < p)
    (hmin : ∀ p ∈ P, Z ≤ p) (hlog : ∀ p ∈ P, V ≤ Real.log (p : ℝ))
    (hbudget : Real.log (2 * (H : ℝ)) < (K + 1 : ℕ) * V)
    (hsmall : 2 * K * (P.card : ℝ) ≤ A ^ 2)
    (E : Finset (Fin (k + 1) ↪ P))
    (hlift : ∀ e ∈ E, ∃ a ∈ Finset.Icc 1 Amax,
      ∃ n ∈ Finset.Ico (-(H : ℤ)) (H + 1),
        ∀ i, ((e i).1 : ℤ) ∣ n - (a : ℤ) * t (e i).1)
    (hpositive : 0 < (E.card : ℝ) / Amax -
      A ^ d * liftMomentUpper P.card (k + 1 - d) H Z) :
    ∃ a ∈ Finset.Icc 1 Amax,
      ∃ n ∈ Finset.Ico (-(H : ℤ)) (H + 1), ∃ h : ℤ, ∃ m : ℕ,
        0 < m ∧ m ≤ Amax ∧ h.natAbs.Coprime m ∧ |h| ≤ |n| ∧
        A ≤ ((matchingPrimes P a t n).card : ℝ) ∧
        (E.card : ℝ) / Amax - A ^ d * liftMomentUpper P.card (k + 1 - d) H Z ≤
          2 * P.card * ((matchingPrimes P a t n).card : ℝ) ^ k ∧
        ∀ (p : ℕ) (hp : p ∈ matchingPrimes P a t n),
          let _ : Fact p.Prime := ⟨hprime p (Finset.mem_filter.mp hp).1⟩
          (t p : ZMod p) = (h : ZMod p) / (m : ZMod p) := by
  obtain ⟨a, ha, E', _, hsize, hlift'⟩ :=
    exists_uniform_denominator_lifts P E Amax H hAmax t hlift
  have ha' := Finset.mem_Icc.mp ha
  have hpositive' : 0 < (E'.card : ℝ) -
      A ^ d * liftMomentUpper P.card (k + 1 - d) H Z := by linarith
  obtain ⟨n, hn, h, m, hm, hma, hcop, hbound, hlarge, hmoment, hcenters⟩ :=
    exists_commonCenter_of_tuple_lifts P a (by omega) t k d K H Z hd A V hA hV hZ
      hprime (fun p hp => ha'.2.trans_lt (hap p hp)) hmin hlog hbudget hsmall E' hlift' hpositive'
  exact ⟨a, ha, n, hn, h, m, hm, hma.trans ha'.2, hcop, hbound, hlarge,
    (by linarith), hcenters⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_CommonCenterProbability
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Common-center extraction directly from the original lift probability -/

namespace Ostmann

open scoped BigOperators Classical

theorem pow_le_twice_descFactorial (J k : ℕ) (hk : 1 ≤ k) (hsize : 2 * k ^ 2 ≤ J) :
    J ^ k ≤ 2 * J.descFactorial k := by
  have hJ : 1 ≤ J := by nlinarith
  have hp : J ^ k = J * J ^ (k - 1) := by rw [← pow_succ', Nat.sub_add_cancel hk]
  have hb := pow_le_descFactorial_add J hJ k
  have hloss := Nat.mul_le_mul_right (J ^ (k - 1)) hsize
  nlinarith

/-- All combinatorial moments are computed from actual congruence lifts.
The remaining assumptions are explicit scalar inequalities. -/
theorem exists_commonCenter_of_lift_probability (P : Finset ℕ)
    (t : ℕ → ℤ) (k d K H Z Amax : ℕ) (hd : d ≤ k + 1)
    (A V ρ : ℝ) (hA : 0 < A) (hV : 0 < V) (hρ : 0 < ρ)
    (hZ : 0 < Z) (hAmax : 0 < Amax)
    (hprime : ∀ p ∈ P, p.Prime) (hap : ∀ p ∈ P, Amax < p)
    (hmin : ∀ p ∈ P, Z ≤ p) (hlog : ∀ p ∈ P, V ≤ Real.log (p : ℝ))
    (hbudget : Real.log (2 * (H : ℝ)) < (K + 1 : ℕ) * V)
    (hsmall : 2 * K * (P.card : ℝ) ≤ A ^ 2)
    (hsize : 2 * (k + 1) ^ 2 ≤ P.card)
    (hprob : ρ ≤ (Fintype.card (Fin (k + 1) ↪ P) : ℝ)⁻¹ *
      (tupleLiftFamily P (k + 1) Amax H t).card)
    (hdiscard : A ^ d * liftMomentUpper P.card (k + 1 - d) H Z ≤
      ρ * (P.card : ℝ) ^ (k + 1) / (4 * Amax)) :
    ∃ a ∈ Finset.Icc 1 Amax,
      ∃ n ∈ Finset.Ico (-(H : ℤ)) (H + 1), ∃ h : ℤ, ∃ m : ℕ,
        0 < m ∧ m ≤ Amax ∧ h.natAbs.Coprime m ∧ |h| ≤ |n| ∧
        A ≤ ((matchingPrimes P a t n).card : ℝ) ∧
        ρ * (P.card : ℝ) ^ (k + 1) / (4 * Amax) ≤
          2 * P.card * ((matchingPrimes P a t n).card : ℝ) ^ k ∧
        ∀ (p : ℕ) (hp : p ∈ matchingPrimes P a t n),
          let _ : Fact p.Prime := ⟨hprime p (Finset.mem_filter.mp hp).1⟩
          (t p : ZMod p) = (h : ZMod p) / (m : ZMod p) := by
  have hJ : 0 < P.card := by nlinarith
  have hJr : 0 < (P.card : ℝ) := by exact_mod_cast hJ
  have hAr : 0 < (Amax : ℝ) := by exact_mod_cast hAmax
  have hhalf : (P.card : ℝ) ^ (k + 1) ≤ 2 * (P.card.descFactorial (k + 1) : ℝ) := by
    exact_mod_cast pow_le_twice_descFactorial P.card (k + 1) (by omega) hsize
  have hcount : ρ * (P.card.descFactorial (k + 1) : ℝ) ≤
      (tupleLiftFamily P (k + 1) Amax H t).card := by
    rw [Fintype.card_embedding_eq, Fintype.card_coe, Fintype.card_fin] at hprob
    have hfac : (0 : ℝ) < P.card.descFactorial (k + 1) := by nlinarith [pow_pos hJr (k + 1)]
    have hh := (le_inv_mul_iff₀ hfac).mp hprob
    nlinarith
  have hcount' : ρ * (P.card : ℝ) ^ (k + 1) / (2 * Amax) ≤
      ((tupleLiftFamily P (k + 1) Amax H t).card : ℝ) / Amax := by
    apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 2 * Amax) hAr).mpr
    nlinarith [mul_le_mul_of_nonneg_left hhalf hρ.le]
  have hratio : ρ * (P.card : ℝ) ^ (k + 1) / (2 * Amax) =
      2 * (ρ * (P.card : ℝ) ^ (k + 1) / (4 * Amax)) := by ring
  rw [hratio] at hcount'
  have hpositive : 0 < ((tupleLiftFamily P (k + 1) Amax H t).card : ℝ) / Amax -
      A ^ d * liftMomentUpper P.card (k + 1 - d) H Z := by
    have hpos : 0 < ρ * (P.card : ℝ) ^ (k + 1) / (4 * Amax) := by positivity
    linarith
  obtain ⟨a, ha, n, hn, h, m, hm, hma, hcop, hbound, hlarge, hmoment, hcenters⟩ :=
    exists_commonCenter_of_bounded_denominators P t k d K H Z Amax hd A V
      hA hV hZ hAmax hprime hap hmin hlog hbudget hsmall
      (tupleLiftFamily P (k + 1) Amax H t)
      (fun e he => (Finset.mem_filter.mp he).2) hpositive
  refine ⟨a, ha, n, hn, h, m, hm, hma, hcop, hbound, hlarge, ?_, hcenters⟩
  linarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_CommonCenterDiscard
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Numerical cost of discarding small common centers -/

namespace Ostmann

open Filter

/-- The original interval length and prime lower bound control the lower
factorial moment, with only an exponential-in-the-tuple-length loss. -/
theorem liftMomentUpper_le_scaled (T : ℝ) (J r H Z : ℕ)
    (hT : 0 ≤ T)
    (hZ : Real.exp T / 2 ≤ (Z : ℝ))
    (hH : (H : ℝ) ≤ 2 * Real.exp ((r - 10 : ℕ) * T + T / 5)) :
    liftMomentUpper J (r - 10) H Z ≤
      6 * (2 : ℝ) ^ r * Real.exp (T / 5) * (J : ℝ) ^ (r - 10) := by
  have hZpos : (0 : ℝ) < Z := lt_of_lt_of_le (by positivity) hZ
  have hZpow := pow_le_pow_left₀ (by positivity : 0 ≤ Real.exp T / 2) hZ (r - 10)
  have heq : (Real.exp T / 2) ^ (r - 10) *
      ((2 : ℝ) ^ (r - 10) * Real.exp (T / 5)) =
      Real.exp ((r - 10 : ℕ) * T + T / 5) := by
    rw [div_pow, ← mul_assoc, div_mul_cancel₀ _ (by positivity : (2 : ℝ) ^ (r - 10) ≠ 0),
      ← Real.exp_nat_mul, ← Real.exp_add]
  have hexp : 1 ≤ Real.exp ((r - 10 : ℕ) * T + T / 5) :=
    Real.one_le_exp (by positivity)
  have hratio : (2 * (H : ℝ) + 1) / (Z : ℝ) ^ (r - 10) ≤
      5 * (2 : ℝ) ^ (r - 10) * Real.exp (T / 5) := by
    apply (div_le_iff₀ (pow_pos hZpos _)).mpr
    have hh := mul_le_mul_of_nonneg_right hZpow
      (show 0 ≤ (2 : ℝ) ^ (r - 10) * Real.exp (T / 5) by positivity)
    rw [heq] at hh
    nlinarith only [hH, hexp, hh]
  have hpow : (2 : ℝ) ^ (r - 10) ≤ (2 : ℝ) ^ r :=
    pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _)
  have hone : (1 : ℝ) ≤ (2 : ℝ) ^ r * Real.exp (T / 5) := by
    have hp : (1 : ℝ) ≤ (2 : ℝ) ^ r := one_le_pow₀ (by norm_num)
    have he : (1 : ℝ) ≤ Real.exp (T / 5) := Real.one_le_exp (by positivity)
    nlinarith
  have hterm : (2 * (H : ℝ) + 1) / (Z : ℝ) ^ (r - 10) + 1 ≤
      6 * (2 : ℝ) ^ r * Real.exp (T / 5) := by
    have hh := mul_le_mul_of_nonneg_right hpow (Real.exp_nonneg (T / 5))
    nlinarith only [hratio, hone, hh]
  have hd : (J.descFactorial (r - 10) : ℝ) ≤ (J : ℝ) ^ (r - 10) := by
    exact_mod_cast Nat.descFactorial_le_pow J (r - 10)
  unfold liftMomentUpper
  exact (mul_le_mul hd hterm (by positivity) (by positivity)).trans_eq (by ring)

/-- The cost of ten missing prime factors dominates the tuple and logarithmic
losses at the manuscript's population scale. -/
theorem eventual_commonCenter_population_budget (Cpop : ℝ) (hCpop : 500 ≤ Cpop) :
    ∀ᶠ T : ℝ in atTop, ∀ (J r : ℕ),
      Real.exp T ≤ Cpop * T * J → (2 : ℝ) ^ r ≤ Real.exp (T / 10) →
      48 * (2 : ℝ) ^ r * Real.exp (33 * T / 5) ≤ (J : ℝ) ^ 10 := by
  have hCpop0 : 0 < Cpop := by linarith
  have hp := ((isLittleO_pow_exp_pos_mul_atTop 10 (show (0 : ℝ) < 1 by norm_num)).const_mul_left
    (48 * Cpop ^ 10)).bound (show (0 : ℝ) < 1 by norm_num)
  filter_upwards [hp, eventually_ge_atTop (1 : ℝ)] with T hpoly hT J r hJ hr
  have hTpos : 0 < T := by linarith
  have hp' : 48 * (Cpop * T) ^ 10 ≤ Real.exp T := by
    have hh : (48 * Cpop ^ 10) * T ^ 10 ≤ Real.exp T := by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (by positivity :
        0 ≤ (48 * Cpop ^ 10) * T ^ 10), abs_of_pos (Real.exp_pos _),
        one_mul] using hpoly
    nlinarith only [hh]
  have hten := pow_le_pow_left₀ (Real.exp_nonneg T) hJ 10
  have hc : (48 * (2 : ℝ) ^ r * Real.exp (33 * T / 5)) * (Cpop * T) ^ 10 ≤
      (J : ℝ) ^ 10 * (Cpop * T) ^ 10 := by
    calc
      _ = (48 * (Cpop * T) ^ 10) * (2 : ℝ) ^ r * Real.exp (33 * T / 5) := by ring
      _ ≤ Real.exp T * Real.exp (T / 10) * Real.exp (33 * T / 5) := by gcongr
      _ = Real.exp (77 * T / 10) := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
      _ ≤ Real.exp (10 * T) := Real.exp_le_exp.mpr (by linarith)
      _ ≤ _ := by
        rw [← Real.exp_nat_mul, show (Cpop * T * J) ^ 10 =
          (J : ℝ) ^ 10 * (Cpop * T) ^ 10 by ring] at hten
        exact hten
  exact (mul_le_mul_iff_left₀ (show 0 < (Cpop * T) ^ 10 by positivity)).mp hc

theorem eventual_commonCenter_discard_budget (Cpop : ℝ) (hCpop : 500 ≤ Cpop) :
    ∀ᶠ T : ℝ in atTop, ∀ (J r H Z Amax : ℕ) (K : ℝ),
      10 ≤ r → K ≤ T → 0 < Amax →
      Real.exp T ≤ Cpop * T * J → (2 : ℝ) ^ r ≤ Real.exp (T / 10) →
      Real.exp T / 2 ≤ (Z : ℝ) →
      (H : ℝ) ≤ 2 * Real.exp ((r - 10 : ℕ) * T + T / 5) →
      (Amax : ℝ) ≤ 2 * Real.exp (T / 5) →
      Real.exp (3 * T / 5) ^ 10 * liftMomentUpper J (r - 10) H Z ≤
        Real.exp (-K / 5) * (J : ℝ) ^ r / (4 * Amax) := by
  filter_upwards [eventual_commonCenter_population_budget Cpop hCpop, eventually_ge_atTop (0 : ℝ)]
    with T hpop hT J r H Z Amax K hr hK hA hJ hpow hZ hH hAU
  have hAr : (0 : ℝ) < Amax := by exact_mod_cast hA
  have hnum := hpop J r hJ hpow
  have hlift := liftMomentUpper_le_scaled T J r H Z hT hZ hH
  have he : Real.exp (32 * T / 5) ≤ Real.exp (-K / 5) * Real.exp (33 * T / 5) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  have hnum' : 48 * (2 : ℝ) ^ r * Real.exp (32 * T / 5) ≤
      Real.exp (-K / 5) * (J : ℝ) ^ 10 := by
    calc
      _ ≤ 48 * (2 : ℝ) ^ r * (Real.exp (-K / 5) * Real.exp (33 * T / 5)) := by gcongr
      _ = Real.exp (-K / 5) * (48 * (2 : ℝ) ^ r * Real.exp (33 * T / 5)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hnum (Real.exp_nonneg _)
  apply (le_div_iff₀ (show (0 : ℝ) < 4 * Amax by positivity)).mpr
  calc
    _ ≤ Real.exp (3 * T / 5) ^ 10 *
        (6 * (2 : ℝ) ^ r * Real.exp (T / 5) * (J : ℝ) ^ (r - 10)) *
        (4 * (2 * Real.exp (T / 5))) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hlift (by positivity)
      · exact mul_le_mul_of_nonneg_left hAU (by norm_num)
      · positivity
      · positivity
    _ = (48 * (2 : ℝ) ^ r * Real.exp (32 * T / 5)) * (J : ℝ) ^ (r - 10) := by
      rw [← Real.exp_nat_mul]
      norm_num only [Nat.cast_ofNat]
      have hex : Real.exp ((10 : ℝ) * (3 * T / 5)) * Real.exp (T / 5) * Real.exp (T / 5) =
          Real.exp (32 * T / 5) := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
      calc
        _ = 48 * (2 : ℝ) ^ r *
            (Real.exp ((10 : ℝ) * (3 * T / 5)) * Real.exp (T / 5) * Real.exp (T / 5)) *
              (J : ℝ) ^ (r - 10) := by ring
        _ = _ := by rw [hex]
    _ ≤ (Real.exp (-K / 5) * (J : ℝ) ^ 10) * (J : ℝ) ^ (r - 10) := by gcongr
    _ = Real.exp (-K / 5) * (J : ℝ) ^ r := by
      rw [mul_assoc, ← pow_add, Nat.add_sub_of_le hr]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_CommonCenterScale
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Numerical scales for common-center extraction -/

namespace Ostmann

open Filter

theorem commonCenter_log_budget (T : ℝ) (r H : ℕ)
    (hT : 1 ≤ T) (hr : 10 ≤ r)
    (hH : (H : ℝ) ≤ 2 * Real.exp ((r - 10 : ℕ) * T + T / 5)) :
    Real.log (2 * (H : ℝ)) < ((r + 1 : ℕ) : ℝ) * T := by
  have hr' : ((r - 10 : ℕ) : ℝ) = r - 10 := by
    rw [Nat.cast_sub hr]; norm_num
  by_cases hHz : H = 0
  · subst H
    simp only [Nat.cast_zero, mul_zero, Real.log_zero]
    positivity
  have hHpos : (0 : ℝ) < H := by exact_mod_cast Nat.pos_of_ne_zero hHz
  apply (Real.log_lt_iff_lt_exp (by positivity : 0 < 2 * (H : ℝ))).mpr
  have hf : (4 : ℝ) < Real.exp (54 * T / 5) := by
    linarith [Real.add_one_le_exp (54 * T / 5)]
  calc
    _ ≤ 4 * Real.exp ((r - 10 : ℕ) * T + T / 5) := by linarith
    _ < Real.exp (54 * T / 5) * Real.exp ((r - 10 : ℕ) * T + T / 5) :=
      mul_lt_mul_of_pos_right hf (Real.exp_pos _)
    _ = _ := by rw [← Real.exp_add, hr']; push_cast; congr 1; ring

theorem eventual_commonCenter_small_budget :
    ∀ᶠ T : ℝ in atTop, ∀ (J r : ℕ),
      (r : ℝ) ≤ 2 * T ^ (3 / 5 : ℝ) → (J : ℝ) ≤ Real.exp (T + 1) →
      2 * r * (J : ℝ) ≤ (Real.exp (3 * T / 5)) ^ 2 := by
  have hp := ((isLittleO_pow_exp_pos_mul_atTop 1 (show (0 : ℝ) < 1 / 5 by norm_num)).const_mul_left
    (4 * Real.exp 1)).bound (show (0 : ℝ) < 1 by norm_num)
  filter_upwards [hp, eventually_ge_atTop (1 : ℝ)] with T hpoly hT J r hr hJ
  have hTpos : 0 < T := by linarith
  have hrT : (r : ℝ) ≤ 2 * T := hr.trans (by
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hT
      (show (3 / 5 : ℝ) ≤ 1 by norm_num))
  have hp' : 4 * Real.exp 1 * T ≤ Real.exp (T / 5) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 4 * Real.exp 1 * T),
      abs_of_pos (Real.exp_pos _), pow_one, one_mul, one_div, inv_mul_eq_div] using hpoly
  calc
    _ ≤ (2 * (2 * T)) * Real.exp (T + 1) := by gcongr
    _ = 4 * T * Real.exp (T + 1) := by ring
    _ = (4 * Real.exp 1 * T) * Real.exp T := by rw [Real.exp_add]; ring
    _ ≤ Real.exp (T / 5) * Real.exp T := by gcongr
    _ = _ := by rw [← Real.exp_add, ← Real.exp_nat_mul]; norm_num; ring

theorem commonCenter_denominator_lt_primes (T : ℝ) (Amax p : ℕ)
    (hT : 3 ≤ T) (hA : (Amax : ℝ) ≤ 2 * Real.exp (T / 5))
    (hp : Real.exp T ≤ (p : ℝ)) : Amax < p := by
  have hf : (2 : ℝ) < Real.exp (4 * T / 5) := by linarith [Real.add_one_le_exp (4 * T / 5)]
  have hh : (Amax : ℝ) < p := calc
    _ ≤ 2 * Real.exp (T / 5) := hA
    _ < Real.exp (4 * T / 5) * Real.exp (T / 5) := mul_lt_mul_of_pos_right hf (Real.exp_pos _)
    _ = Real.exp T := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ p := hp
  exact_mod_cast hh

theorem commonCenter_relative_size (T K J R Amax : ℝ) (k : ℕ)
    (hT : 30 ≤ T) (hK : K ≤ T) (hJ : 0 < J) (hR : 0 ≤ R)
    (hA : 0 < Amax) (hAU : Amax ≤ 2 * Real.exp (T / 5)) (hk : 0 < k)
    (hmoment : Real.exp (-K / 5) * J ^ (k + 1) / (4 * Amax) ≤ 2 * J * R ^ k) :
    J * Real.exp (-T / k) ≤ R := by
  have hfactor : (16 : ℝ) ≤ Real.exp (4 * T / 5 - K / 5) := by
    linarith [Real.add_one_le_exp (4 * T / 5 - K / 5)]
  have hcost : 8 * Amax ≤ Real.exp (-K / 5) * Real.exp T := by
    calc
      _ ≤ 16 * Real.exp (T / 5) := by linarith
      _ ≤ Real.exp (4 * T / 5 - K / 5) * Real.exp (T / 5) := by gcongr
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hm := (div_le_iff₀ (show 0 < 4 * Amax by positivity)).mp hmoment
  have hh : J ^ k ≤ Real.exp T * R ^ k := by
    have hc := mul_le_mul_of_nonneg_right hcost (mul_nonneg hJ.le (pow_nonneg hR k))
    rw [pow_succ] at hm
    have hpos : 0 < Real.exp (-K / 5) * J := by positivity
    nlinarith only [hm, hc, hpos]
  have hh' := mul_le_mul_of_nonneg_right hh (Real.exp_nonneg (-T))
  have hcanc : (Real.exp T * R ^ k) * Real.exp (-T) = R ^ k := by
    rw [mul_right_comm, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
  rw [hcanc] at hh'
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hpow : (J * Real.exp (-T / k)) ^ k = J ^ k * Real.exp (-T) := by
    rw [mul_pow, ← Real.exp_nat_mul]
    congr 2
    field_simp
  apply le_of_pow_le_pow_left₀ hk.ne' hR
  rwa [hpow]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_CommonCenterCutoffs
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integer cutoffs for the original rational-center extraction -/

namespace Ostmann

theorem commonCenter_original_cutoffs (T X : ℝ) (r : ℕ) (hT : 1 ≤ T) (hX : 1 ≤ X)
    (hXU : X ≤ Real.exp ((r - 10 : ℕ) * T)) :
    0 < ⌈Real.exp (13 * T / 100)⌉₊ ∧
    (⌈Real.exp (13 * T / 100)⌉₊ : ℝ) ≤ 2 * Real.exp (T / 5) ∧
    (⌈X * Real.exp (13 * T / 100)⌉₊ : ℝ) ≤
      2 * Real.exp ((r - 10 : ℕ) * T + T / 5) ∧
    0 < ⌊Real.exp T⌋₊ ∧ Real.exp T / 2 ≤ (⌊Real.exp T⌋₊ : ℝ) := by
  have hT0 : 0 ≤ T := by linarith
  have hE : 1 ≤ Real.exp (13 * T / 100) := Real.one_le_exp (by positivity)
  have hE' : Real.exp (13 * T / 100) ≤ Real.exp (T / 5) :=
    Real.exp_le_exp.mpr (by linarith)
  have hA : (⌈Real.exp (13 * T / 100)⌉₊ : ℝ) ≤ 2 * Real.exp (T / 5) := by
    have hh := Nat.ceil_lt_add_one (Real.exp_nonneg (13 * T / 100))
    linarith
  have hXE : 0 ≤ X * Real.exp (13 * T / 100) := by positivity
  have hH : (⌈X * Real.exp (13 * T / 100)⌉₊ : ℝ) ≤
      2 * Real.exp ((r - 10 : ℕ) * T + T / 5) := by
    have hh := Nat.ceil_lt_add_one hXE
    have hbound : X * Real.exp (13 * T / 100) ≤ Real.exp ((r - 10 : ℕ) * T + T / 5) := by
      rw [Real.exp_add]
      exact mul_le_mul hXU hE' (Real.exp_nonneg _) (Real.exp_nonneg _)
    have h1 : 1 ≤ X * Real.exp (13 * T / 100) := by nlinarith
    linarith
  have h2 : (2 : ℝ) ≤ Real.exp T := by linarith [Real.add_one_le_exp T]
  have hfloor := Nat.lt_floor_add_one (Real.exp T)
  have hfloorpos : 0 < ⌊Real.exp T⌋₊ := by
    have hh : (1 : ℝ) ≤ ⌊Real.exp T⌋₊ := by linarith
    exact_mod_cast hh
  exact ⟨Nat.ceil_pos.mpr (Real.exp_pos _), hA, hH, hfloorpos, by linarith⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_OriginalCommonCenter
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A common rational center from the original positive lift family -/

namespace Ostmann

open Filter
open scoped BigOperators Classical

/-- The scalar hypotheses of the finite common-center theorem have now been
discharged at the original scales. The input probability is supplied by
`eventual_original_lift_probability`. -/
theorem eventual_original_commonCenter (Cpop : ℝ) (hCpop : 500 ≤ Cpop) :
    ∀ᶠ T : ℝ in atTop, ∀ (P : Finset ℕ) (t : ℕ → ℤ) (k : ℕ) (K X : ℝ),
      ∀ hP : ∀ p ∈ P, p.Prime, (∀ p ∈ P, Real.exp T ≤ (p : ℝ)) →
      Real.exp T ≤ Cpop * T * P.card → (P.card : ℝ) ≤ Real.exp (T + 1) →
      10 ≤ k + 1 → 2 * (k + 1) ^ 2 ≤ P.card →
      ((k + 1 : ℕ) : ℝ) ≤ 2 * T ^ (3 / 5 : ℝ) →
      T ^ (9999999 / 10000000 : ℝ) / 1000 ≤ K → K ≤ T →
      1 ≤ X → X ≤ Real.exp (((k + 1 - 10 : ℕ) : ℝ) * T) →
      Real.exp (-K / 5) ≤ (Fintype.card (Fin (k + 1) ↪ P) : ℝ)⁻¹ *
        (tupleLiftFamily P (k + 1) ⌈Real.exp (13 * T / 100)⌉₊
          ⌈X * Real.exp (13 * T / 100)⌉₊ t).card →
      ∃ a ∈ Finset.Icc 1 ⌈Real.exp (13 * T / 100)⌉₊,
        ∃ n ∈ Finset.Ico (-(⌈X * Real.exp (13 * T / 100)⌉₊ : ℤ))
          (⌈X * Real.exp (13 * T / 100)⌉₊ + 1), ∃ h : ℤ, ∃ m : ℕ,
          0 < m ∧ m ≤ ⌈Real.exp (13 * T / 100)⌉₊ ∧ h.natAbs.Coprime m ∧ |h| ≤ |n| ∧
          Real.exp (3 * T / 5) ≤ ((matchingPrimes P a t n).card : ℝ) ∧
          (P.card : ℝ) * Real.exp (-T / k) ≤ ((matchingPrimes P a t n).card : ℝ) ∧
          ∀ (p : ℕ) (hp : p ∈ matchingPrimes P a t n),
            let _ : Fact p.Prime := ⟨hP p (Finset.mem_filter.mp hp).1⟩
            (t p : ZMod p) = (h : ZMod p) / (m : ZMod p) := by
  filter_upwards [eventual_commonCenter_discard_budget Cpop hCpop, eventual_commonCenter_small_budget,
    eventual_two_pow_moment_budget, eventually_ge_atTop (30 : ℝ)] with T hd hs hp hT
  intro P t k K X hP hmin hpop hPU hk hsize hkU hK hKT hX hXU hprob
  let Amax := ⌈Real.exp (13 * T / 100)⌉₊
  let H := ⌈X * Real.exp (13 * T / 100)⌉₊
  let Z := ⌊Real.exp T⌋₊
  obtain ⟨hApos, hAU, hHU, hZpos, hZlo⟩ := commonCenter_original_cutoffs T X (k + 1)
    (by linarith) hX hXU
  have hpow : (2 : ℝ) ^ (k + 1) ≤ Real.exp (T / 10) :=
    (hp (k + 1) K (by omega) hkU hK).trans (Real.exp_le_exp.mpr (by linarith))
  have hdiscard := hd P.card (k + 1) H Z Amax K hk hKT hApos hpop hpow hZlo hHU hAU
  have hlog (p : ℕ) (hpp : p ∈ P) : T ≤ Real.log (p : ℝ) :=
    (Real.le_log_iff_exp_le (by exact_mod_cast (hP p hpp).pos)).mpr (hmin p hpp)
  have hfloor (p : ℕ) (hpp : p ∈ P) : Z ≤ p := by
    have hh : (Z : ℝ) ≤ p := (Nat.floor_le (Real.exp_nonneg T)).trans (hmin p hpp)
    exact_mod_cast hh
  obtain ⟨a, ha, n, hn, h, m, hm, hma, hcop, hbound, hlarge, hmoment, hcenters⟩ :=
    exists_commonCenter_of_lift_probability P t k 10 (k + 1) H Z Amax hk
      (Real.exp (3 * T / 5)) T (Real.exp (-K / 5)) (Real.exp_pos _) (by linarith)
      (Real.exp_pos _) hZpos hApos hP
      (fun p hpp => commonCenter_denominator_lt_primes T Amax p (by linarith) hAU (hmin p hpp))
      hfloor hlog (commonCenter_log_budget T (k + 1) H (by linarith) hk hHU)
      (hs P.card (k + 1) hkU hPU) hsize hprob hdiscard
  have hJ : (0 : ℝ) < P.card := by
    have hh : 0 < P.card := by nlinarith
    exact_mod_cast hh
  refine ⟨a, ha, n, hn, h, m, hm, hma, hcop, hbound, hlarge, ?_, hcenters⟩
  exact commonCenter_relative_size T K P.card (matchingPrimes P a t n).card Amax k
    hT hKT hJ (Nat.cast_nonneg _) (by exact_mod_cast hApos) hAU (by omega) hmoment

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_OriginalPositiveFirstMoment
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # First moment of the original positive-frequency statistic -/

namespace Ostmann

open scoped BigOperators SchwartzMap FourierTransform ComplexConjugate
open Filter

theorem physical_positive_first_mean (Q P : Finset ℕ)
    (hQ : ∀ p ∈ Q, p.Prime) (hP : ∀ p ∈ P, p.Prime) (hodd : ∀ p ∈ P, Odd p)
    (D : ∀ p : ℕ, Finset (ZMod p)) (ψ : 𝓢(ℝ, ℂ))
    (hreal : ∀ x, conj (ψ x) = ψ x) (hψ0 : ∀ x, 0 ≤ (ψ x).re)
    (X H : ℝ) (hX : 0 < X) (hH : 0 ≤ H)
    (ε : ℕ → ℝ) (hε : ∀ p ∈ P, ε p = 1 ∨ ε p = -1) (t : ℕ → ℤ)
    (k N : ℕ) (hk : 0 < k) (hkP : k ≤ P.card) (hK : 3000 ≤ (Q.card : ℝ))
    (τ : ℕ → ℤ) (h₀ : ℕ → ℕ)
    (hdata : ∀ e : Fin k ↪ P,
      Q.toList.prod.Coprime (primeTupleProduct P e) ∧
      H * ((primeTupleProduct P e : ℝ) / X) * Q.toList.prod ≤ N ∧
      0 ≤ τ (primeTupleProduct P e) ∧ τ (primeTupleProduct P e) < primeTupleProduct P e ∧
      (∀ i, (τ (primeTupleProduct P e) : ZMod (e i).val) = (t (e i).val : ZMod (e i).val)) ∧
      (Q.toList.prod : ℤ) ∣ τ (primeTupleProduct P e) +
        (primeTupleProduct P e : ℤ) * h₀ (primeTupleProduct P e))
    (hsupp : ∀ x : ℝ, H < x → 𝓕 ψ x = 0)
    (hlower : Real.sqrt X * Real.exp ((2 / 125 : ℝ) * Q.card) / 2 ≤
      ∑' n : ℤ, physicalWeight Q D ψ X n *
        ternaryDistinctMean (fun p : P => orientedQuadraticValue ε t n p) k) :
    Real.exp ((3 / 200 : ℝ) * Q.card) ≤
      (P.card.choose k : ℝ)⁻¹ * ∑ m ∈ primeSubsetProducts P k,
        originalPrimeProductStatistic Q hQ D N τ h₀ ψ X m := by
  have hb (e : Fin k ↪ P) :
      |∑' n : ℤ, physicalWeight Q D ψ X n * ∏ i, orientedQuadraticValue ε t n (e i).val| ≤
      2 * Real.sqrt X * originalPrimeProductStatistic Q hQ D N τ h₀ ψ X (primeTupleProduct P e) := by
    obtain ⟨hc, hcut, ht0, htlt, ht, hl⟩ := hdata e
    exact physical_tuple_positive_bound Q P hQ hP hodd D ψ hreal X H hX hH ε hε t hk e hc
      N (h₀ (primeTupleProduct P e)) hcut hsupp (τ (primeTupleProduct P e)) ht0 htlt ht hl
  have hm := amplified_distinct_first_mean (physicalWeight Q D ψ X)
    (fun n (p : P) => orientedQuadraticValue ε t n p)
    (physicalWeight_nonneg Q hQ D ψ hψ0 X)
    (fun n p => by
      rcases orientedQuadraticValue_ternary ε t n p (hε p p.property) with h | h | h <;>
        rw [h] <;> norm_num)
    (physicalWeight_summable Q hQ D ψ X hX) k
    (fun e : Fin k ↪ P => originalPrimeProductStatistic Q hQ D N τ h₀ ψ X (primeTupleProduct P e))
    X Q.card hX hK (fun _ => norm_nonneg _) (by simpa using hkP) hb hlower
  rwa [primeTuple_uniform_mean P hP k] at hm

/-- The phase table in the first-moment bound is constructed by CRT and is
indexed by products, so it is compatible with the fixed coefficient moments. -/
theorem exists_positive_first_mean (Q P : Finset ℕ)
    (hQ : ∀ p ∈ Q, p.Prime) (hP : ∀ p ∈ P, p.Prime) (hodd : ∀ p ∈ P, Odd p)
    (D : ∀ p : ℕ, Finset (ZMod p)) (ψ : 𝓢(ℝ, ℂ))
    (hreal : ∀ x, conj (ψ x) = ψ x) (hψ0 : ∀ x, 0 ≤ (ψ x).re)
    (X H : ℝ) (hX : 0 < X) (hH : 0 ≤ H)
    (ε : ℕ → ℝ) (hε : ∀ p ∈ P, ε p = 1 ∨ ε p = -1) (t : ℕ → ℤ)
    (k N : ℕ) (hk : 0 < k) (hkP : k ≤ P.card) (hK : 3000 ≤ (Q.card : ℝ))
    (hcop : ∀ M ∈ primeSubsetProducts P k, Q.toList.prod.Coprime M)
    (hcut : ∀ M ∈ primeSubsetProducts P k, H * ((M : ℝ) / X) * Q.toList.prod ≤ N)
    (hsupp : ∀ x : ℝ, H < x → 𝓕 ψ x = 0)
    (hlower : Real.sqrt X * Real.exp ((2 / 125 : ℝ) * Q.card) / 2 ≤
      ∑' n : ℤ, physicalWeight Q D ψ X n *
        ternaryDistinctMean (fun p : P => orientedQuadraticValue ε t n p) k) :
    ∃ τ : ℕ → ℤ, ∃ h₀ : ℕ → ℕ,
      (∀ M ∈ primeSubsetProducts P k,
        0 ≤ τ M ∧ τ M < M ∧ h₀ M < Q.toList.prod ∧
        (Q.toList.prod : ℤ) ∣ τ M + (M : ℤ) * h₀ M ∧
        ∀ p ∈ M.primeFactors, (τ M : ZMod p) = (t p : ZMod p)) ∧
      Real.exp ((3 / 200 : ℝ) * Q.card) ≤
        (P.card.choose k : ℝ)⁻¹ * ∑ m ∈ primeSubsetProducts P k,
          originalPrimeProductStatistic Q hQ D N τ h₀ ψ X m := by
  let : NeZero Q.toList.prod := ⟨(prime_list_prod_pos _ (primeSet_list_prime Q hQ)).ne'⟩
  obtain ⟨τ, h₀, hτ⟩ := exists_primeProduct_translations P hP k Q.toList.prod t hcop
  refine ⟨fun M => (τ M : ℤ), h₀, ?_, ?_⟩
  · intro M hM
    obtain ⟨ha, hb, hd, hc⟩ := hτ M hM
    exact ⟨Int.natCast_nonneg _, Int.ofNat_lt.mpr ha, hb, hd, by simpa using hc⟩
  · apply physical_positive_first_mean Q P hQ hP hodd D ψ hreal hψ0 X H hX hH ε hε t
      k N hk hkP hK (fun M => (τ M : ℤ)) h₀ _ hsupp hlower
    intro e
    have he := primeTupleProduct_mem P e
    obtain ⟨ha, hb, hd, hc⟩ := hτ (primeTupleProduct P e) he
    refine ⟨hcop _ he, hcut _ he, Int.natCast_nonneg _, Int.ofNat_lt.mpr ha, ?_, hd⟩
    intro i
    simpa only [Int.cast_natCast] using hc (e i).val (primeTuple_member_primeFactors P hP e i)

/-- The original tail bias and size estimates now imply the Fourier first
moment. There is no assumed Fourier lower bound in this statement. -/
theorem eventual_original_positive_mean (cψ a c C : ℝ)
    (hcψ : 0 < cψ) (ha : 0 < a) (hc : 0 < c) (hC : 1 ≤ C) :
    ∀ᶠ T : ℝ in atTop, ∀ (Q P : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
      (_hP : ∀ p ∈ P, p.Prime) (_hodd : ∀ p ∈ P, Odd p)
      (D : ∀ p : ℕ, Finset (ZMod p)) (ψ : 𝓢(ℝ, ℂ)) (X H : ℝ),
      0 < X → 0 ≤ H → (∀ x, conj (ψ x) = ψ x) → (∀ x, 0 ≤ (ψ x).re) →
      (∀ x ∈ Set.Icc (0 : ℝ) 1, cψ ≤ (ψ x).re) →
      H < X / Q.toList.prod → (∀ x : ℝ, H < |x| → 𝓕 ψ x = 0) →
      (𝓕 ψ 0).re ≤ C → ∀ (S : Finset ℤ),
      (∀ n ∈ S, 0 ≤ (n : ℝ) ∧ (n : ℝ) ≤ X) →
      a * Real.sqrt X / T ^ 6 ≤ (S.card : ℝ) →
      (∀ p ∈ Q, (D p).card / (p : ℝ) ≤ 2 / 3) →
      (∀ n ∈ S, ∀ p ∈ Q, (n : ZMod p) ∈ D p) →
      ∀ (ε : ℕ → ℝ) (t : ℕ → ℤ), (∀ p ∈ P, ε p = 1 ∨ ε p = -1) →
      (∀ p ∈ P, (S.card : ℝ) * c ≤ ∑ n ∈ S, orientedQuadraticValue ε t n p) →
      ∀ k N : ℕ, 0 < k → Even k → k ≤ P.card →
      (k : ℝ) ≤ 2 * T ^ (3 / 5 : ℝ) →
      T ^ (9999999 / 10000000 : ℝ) / 1000 ≤ (Q.card : ℝ) →
      3000 ≤ (Q.card : ℝ) → Real.exp T ≤ C * T * P.card → X ≤ Real.exp ((k : ℝ) * T) →
      (∀ M ∈ primeSubsetProducts P k, Q.toList.prod.Coprime M) →
      (∀ M ∈ primeSubsetProducts P k, H * ((M : ℝ) / X) * Q.toList.prod ≤ N) →
      ∃ τ : ℕ → ℤ, ∃ h₀ : ℕ → ℕ,
        (∀ M ∈ primeSubsetProducts P k,
          0 ≤ τ M ∧ τ M < M ∧ h₀ M < Q.toList.prod ∧
          (Q.toList.prod : ℤ) ∣ τ M + (M : ℤ) * h₀ M ∧
          ∀ p ∈ M.primeFactors, (τ M : ZMod p) = (t p : ZMod p)) ∧
        Real.exp ((3 / 200 : ℝ) * Q.card) ≤
          (P.card.choose k : ℝ)⁻¹ * ∑ m ∈ primeSubsetProducts P k,
            originalPrimeProductStatistic Q hQ D N τ h₀ ψ X m := by
  filter_upwards [eventual_original_distinct_moment cψ a c C hcψ ha hc hC] with T hm
  intro Q P hQ hP hodd D ψ X H hX hH0 hreal hψ0 hψ1 hH hsupp hCψ S hS hcard hD hSD
    ε t hε hbias k N hk heven hkP hkU hK hK3000 hpop hXk hcop hcut
  apply exists_positive_first_mean Q P hQ hP hodd D ψ hreal hψ0 X H hX hH0 ε hε t
    k N hk hkP hK3000 hcop hcut
  · intro x hx
    exact hsupp x (by rwa [abs_of_nonneg (hH0.trans hx.le)])
  · exact hm Q P hQ D ψ X H hX hψ0 hψ1 hH hsupp hCψ S hS hcard hD hSD
      ε t hε hbias k hk heven hkP hkU hK hpop hXk

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_OriginalLiftProbability
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A positive family of simultaneous lifts from the original tail data -/

namespace Ostmann

open Filter
open scoped BigOperators SchwartzMap FourierTransform ComplexConjugate Classical

/-- This combines the physical amplification, Poisson, fixed-family moments,
and inverse phase argument. No Fourier moment or witness event is assumed. -/
theorem eventual_original_lift_probability (hBonami : PublishedBonamiBound)
    (cψ a c C B : ℝ) (hcψ : 0 < cψ) (ha : 0 < a) (hc : 0 < c)
    (hC : 500 ≤ C) (hB : 3 ≤ B) (ψ : 𝓢(ℝ, ℂ))
    (hreal : ∀ x, conj (ψ x) = ψ x) (hψ0 : ∀ x, 0 ≤ (ψ x).re)
    (hψ1 : ∀ x ∈ Set.Icc (0 : ℝ) 1, cψ ≤ (ψ x).re)
    (hsupp : ∀ x : ℝ, B ^ 2 < |x| → 𝓕 ψ x = 0) (hCψ : (𝓕 ψ 0).re ≤ C) :
    ∀ᶠ T : ℝ in atTop, ∀ (Q P : Finset ℕ) (_hQ : ∀ p ∈ Q, p.Prime),
      (∀ p ∈ P, p.Prime) → (∀ p ∈ P, Odd p) →
      ∀ (D : ∀ p : ℕ, Finset (ZMod p)) (X : ℝ),
      0 < X → B ^ 2 < X / Q.toList.prod →
      ∀ (S : Finset ℤ), (∀ n ∈ S, 0 ≤ (n : ℝ) ∧ (n : ℝ) ≤ X) →
      a * Real.sqrt X / T ^ 6 ≤ (S.card : ℝ) →
      (∀ p ∈ Q, (D p).card / (p : ℝ) ≤ 2 / 3) →
      (∀ n ∈ S, ∀ p ∈ Q, (n : ZMod p) ∈ D p) →
      ∀ (ε : ℕ → ℝ) (t : ℕ → ℤ), (∀ p ∈ P, ε p = 1 ∨ ε p = -1) →
      (∀ p ∈ P, (S.card : ℝ) * c ≤ ∑ n ∈ S, orientedQuadraticValue ε t n p) →
      ∀ k l N Z : ℕ, 1 ≤ k → Even k → 2 * k ^ 2 ≤ P.card →
      T ^ (3 / 5 : ℝ) / 2 ≤ k → (k : ℝ) ≤ 2 * T ^ (3 / 5 : ℝ) →
      T ^ (9999999 / 10000000 : ℝ) / 1000 ≤ (Q.card : ℝ) →
      3000 ≤ Q.card → (Q.card : ℝ) ≤ T ^ (9999999 / 10000000 : ℝ) →
      (∀ p ∈ Q, 1000000 ≤ p) → (Q.toList.prod : ℝ) ≤ Real.exp (T / 50) →
      2 ≤ Q.toList.prod →
      Real.exp T ≤ C * T * P.card → X ≤ Real.exp ((k : ℝ) * T) →
      (∀ M ∈ primeSubsetProducts P k, Q.toList.prod.Coprime M) →
      (∀ p ∈ P, p ≤ Z) → (∀ p ∈ P, Real.exp T ≤ (p : ℝ)) →
      1 ≤ Z → (Z : ℝ) ≤ Real.exp (T + 1) →
      1 ≤ l → T ^ (1 / 1000000 : ℝ) / 2 ≤ l → (l : ℝ) ≤ T ^ (1 / 1000000 : ℝ) →
      1 ≤ N → (N : ℝ) ≤ Real.exp (14 * T) →
      (∀ M ∈ primeSubsetProducts P k,
        B ^ 2 * ((M : ℝ) / X) * Q.toList.prod ≤ N ∧
        Real.exp (10 * T) ≤ (M : ℝ) / X ∧ (M : ℝ) / X ≤ Real.exp (14 * T)) →
      Real.exp (-(Q.card : ℝ) / 5) ≤ (Fintype.card (Fin k ↪ P) : ℝ)⁻¹ *
        (tupleLiftFamily P k ⌈Real.exp (13 * T / 100)⌉₊
          ⌈X * Real.exp (13 * T / 100)⌉₊ t).card := by
  have hsupport (x : ℝ) (hx : B ^ 2 < x) : 𝓕 ψ x = 0 := hsupp x (hx.trans_le (le_abs_self x))
  filter_upwards [eventual_original_positive_mean cψ a c C hcψ ha hc (by linarith),
    eventual_original_witness_probability hBonami C hC (B ^ 2) (𝓕 ψ) (sq_nonneg _) hsupport,
    eventual_original_tuple_witness_lift B (𝓕 ψ) hB hsupport,
    eventually_ge_atTop (1 : ℝ)] with T hfirst hprob hlift hT
  intro Q P hQ hP hodd D X hX hBX S hS hsize hD hSD ε t hε hbias k l N Z
    hk heven hksize hkL hkU hK hK3 hKU hlarge hL hL2 hpop hXk hcop hPZ hmin
    hZ hZU hl hlL hlU hN1 hN hscale
  have hkP : k ≤ P.card := by nlinarith
  have hpopC : Real.exp T ≤ C * T * P.card := hpop.trans (by
    gcongr)
  obtain ⟨τ, h₀, hphase, hmean⟩ := hfirst Q P hQ hP hodd D ψ X (B ^ 2)
    hX (sq_nonneg _) hreal hψ0 hψ1 hBX hsupp hCψ S hS hsize hD hSD ε t hε hbias
    k N hk heven hkP hkU hK (by exact_mod_cast hK3) hpopC hXk hcop
    (fun m hm => (hscale m hm).1)
  have hphaseRange (m : ℕ) (hm : m ∈ primeSubsetProducts P k) :
      h₀ m < Q.toList.prod ∧ 0 ≤ (τ m : ℝ) / m ∧ (τ m : ℝ) / m ≤ 1 ∧
      1 ≤ (m : ℝ) / X ∧ (m : ℝ) / X ≤ Real.exp (14 * T) ∧
      (Q.toList.prod : ℝ) ^ 6 + Real.exp (-200 * T) ≤ (m : ℝ) / X := by
    obtain ⟨ht0, htM, hh, _, _⟩ := hphase m hm
    have hm0 : (0 : ℝ) < m := by
      have hm' : (0 : ℤ) < m := ht0.trans_lt htM
      exact_mod_cast hm'
    refine ⟨hh, div_nonneg (by exact_mod_cast ht0) hm0.le,
      (div_le_one hm0).mpr (by exact_mod_cast htM.le), ?_, (hscale m hm).2.2, ?_⟩
    · exact (Real.one_le_exp (by linarith : 0 ≤ 10 * T)).trans (hscale m hm).2.1
    · exact fourier_grid_margin_of_prime_scale T _ _ hT hL (hscale m hm).2.1
  have hp := hprob Q hQ D P N Z k l hK hK3 hKU hlarge
    (hL.trans (Real.exp_le_exp.mpr (by linarith))) hL2 hP hodd hPZ hmin hZ hpop hZU
    hk hksize hkL hkU hl hlL hlU hN1 hN h₀ (fun m => (τ m : ℝ) / m)
    (fun m => (m : ℝ) / X) hphaseRange (fun m hm => (hscale m hm).1) hmean
  apply hp.trans
  apply tupleLiftFamily_probability P hP k _ _ t
    (fun m => principalSmallWitness Q hQ D m N (h₀ m) ((τ m : ℝ) / m) ((m : ℝ) / X) (𝓕 ψ))
  apply hlift Q hQ D P hP k N t τ h₀ X hX hL hKU
  intro m hm
  refine ⟨(hscale m hm).2.1, (hscale m hm).2.2, ?_⟩
  intro p hp
  exact (ZMod.intCast_eq_intCast_iff_dvd_sub (t p) (τ m) p).mp ((hphase m hm).2.2.2.2 p hp).symm

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_OriginalTailCenter
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original tail assumptions give a common rational center -/

namespace Ostmann

open Filter
open scoped BigOperators SchwartzMap FourierTransform ComplexConjugate Classical

theorem eventual_original_tail_commonCenter_oai (hBonami : PublishedBonamiBound)
    (cψ a c C B : ℝ) (hcψ : 0 < cψ) (ha : 0 < a) (hc : 0 < c)
    (hC : 500 ≤ C) (hB : 3 ≤ B) (ψ : 𝓢(ℝ, ℂ))
    (hreal : ∀ x, conj (ψ x) = ψ x) (hψ0 : ∀ x, 0 ≤ (ψ x).re)
    (hψ1 : ∀ x ∈ Set.Icc (0 : ℝ) 1, cψ ≤ (ψ x).re)
    (hsupp : ∀ x : ℝ, B ^ 2 < |x| → 𝓕 ψ x = 0) (hCψ : (𝓕 ψ 0).re ≤ C) :
    ∀ᶠ T : ℝ in atTop, ∀ (Q P : Finset ℕ) (_hQ : ∀ p ∈ Q, p.Prime),
      ∀ hP : ∀ p ∈ P, p.Prime, (∀ p ∈ P, Odd p) →
      ∀ (D : ∀ p : ℕ, Finset (ZMod p)) (X : ℝ),
      1 ≤ X → B ^ 2 < X / Q.toList.prod →
      ∀ (S : Finset ℤ), (∀ n ∈ S, 0 ≤ (n : ℝ) ∧ (n : ℝ) ≤ X) →
      a * Real.sqrt X / T ^ 6 ≤ (S.card : ℝ) →
      (∀ p ∈ Q, (D p).card / (p : ℝ) ≤ 2 / 3) →
      (∀ n ∈ S, ∀ p ∈ Q, (n : ZMod p) ∈ D p) →
      ∀ (ε : ℕ → ℝ) (t : ℕ → ℤ), (∀ p ∈ P, ε p = 1 ∨ ε p = -1) →
      (∀ p ∈ P, (S.card : ℝ) * c ≤ ∑ n ∈ S, orientedQuadraticValue ε t n p) →
      ∀ k l N Z : ℕ, 10 ≤ k → Even k → 2 * k ^ 2 ≤ P.card →
      T ^ (3 / 5 : ℝ) / 2 ≤ k → (k : ℝ) ≤ 2 * T ^ (3 / 5 : ℝ) →
      T ^ (9999999 / 10000000 : ℝ) / 1000 ≤ (Q.card : ℝ) →
      3000 ≤ Q.card → (Q.card : ℝ) ≤ T ^ (9999999 / 10000000 : ℝ) →
      (∀ p ∈ Q, 1000000 ≤ p) → (Q.toList.prod : ℝ) ≤ Real.exp (T / 50) →
      2 ≤ Q.toList.prod →
      Real.exp T ≤ C * T * P.card → (P.card : ℝ) ≤ Real.exp (T + 1) →
      X ≤ Real.exp (((k - 10 : ℕ) : ℝ) * T) →
      (∀ M ∈ primeSubsetProducts P k, Q.toList.prod.Coprime M) →
      (∀ p ∈ P, p ≤ Z) → (∀ p ∈ P, Real.exp T ≤ (p : ℝ)) →
      1 ≤ Z → (Z : ℝ) ≤ Real.exp (T + 1) →
      1 ≤ l → T ^ (1 / 1000000 : ℝ) / 2 ≤ l → (l : ℝ) ≤ T ^ (1 / 1000000 : ℝ) →
      1 ≤ N → (N : ℝ) ≤ Real.exp (14 * T) →
      (∀ M ∈ primeSubsetProducts P k,
        B ^ 2 * ((M : ℝ) / X) * Q.toList.prod ≤ N ∧
        Real.exp (10 * T) ≤ (M : ℝ) / X ∧ (M : ℝ) / X ≤ Real.exp (14 * T)) →
      ∃ a ∈ Finset.Icc 1 ⌈Real.exp (13 * T / 100)⌉₊,
        ∃ n ∈ Finset.Ico (-(⌈X * Real.exp (13 * T / 100)⌉₊ : ℤ))
          (⌈X * Real.exp (13 * T / 100)⌉₊ + 1), ∃ h : ℤ, ∃ m : ℕ,
          0 < m ∧ m ≤ ⌈Real.exp (13 * T / 100)⌉₊ ∧ h.natAbs.Coprime m ∧ |h| ≤ |n| ∧
          Real.exp (3 * T / 5) ≤ ((matchingPrimes P a t n).card : ℝ) ∧
          (P.card : ℝ) * Real.exp (-T / (k - 1 : ℕ)) ≤ ((matchingPrimes P a t n).card : ℝ) ∧
          ∀ (p : ℕ) (hp : p ∈ matchingPrimes P a t n),
            let _ : Fact p.Prime := ⟨hP p (Finset.mem_filter.mp hp).1⟩
            (t p : ZMod p) = (h : ZMod p) / (m : ZMod p) := by
  filter_upwards [eventual_original_lift_probability hBonami cψ a c C B hcψ ha hc hC hB ψ
    hreal hψ0 hψ1 hsupp hCψ, eventual_original_commonCenter C hC,
    eventually_ge_atTop (1 : ℝ)] with T hlift hcenter hT
  intro Q P hQ hP hodd D X hX hBX S hS hsize hD hSD ε t hε hbias k l N Z
    hk heven hksize hkL hkU hK hK3 hKU hlarge hL hL2 hpop hPU hXU hcop hPZ hmin
    hZ hZU hll hlL hlU hN1 hN hscale
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  have hXk : X ≤ Real.exp (((j + 1 : ℕ) : ℝ) * T) := hXU.trans (Real.exp_le_exp.mpr (by
    have hh : ((j + 1 - 10 : ℕ) : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.sub_le (j + 1) 10
    exact mul_le_mul_of_nonneg_right hh (by linarith)))
  have hp := hlift Q P hQ hP hodd D X (by linarith) hBX S hS hsize hD hSD ε t hε hbias
    (j + 1) l N Z (by omega) heven hksize hkL hkU hK hK3 hKU hlarge hL hL2 hpop hXk hcop
    hPZ hmin hZ hZU hll hlL hlU hN1 hN hscale
  have hKT : (Q.card : ℝ) ≤ T := hKU.trans (by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hT
      (show (9999999 / 10000000 : ℝ) ≤ 1 by norm_num))
  have hc := hcenter P t j Q.card X hP hmin hpop hPU hk hksize hkU hK hKT hX hXU hp
  simpa only [Nat.succ_eq_add_one, Nat.add_sub_cancel] using hc

end Ostmann

end OAI
end

theorem solution : type_of% @OAI.Ostmann.eventual_original_tail_commonCenter_oai := @OAI.Ostmann.eventual_original_tail_commonCenter_oai
