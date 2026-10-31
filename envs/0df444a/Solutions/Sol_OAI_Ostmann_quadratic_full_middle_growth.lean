-- Prove2me | solution 1 for OAI.Ostmann.quadratic_full_middle_growth
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T06:49:56.356474+00:00
-- url     : https://prove2.me/submissions/3586070a-456d-46ef-b147-a7a4d875a69d

import Mathlib
import Definitions.Def_OAIQ095D005

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

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticSieveTranspose
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reciprocity supplies the transpose needed for quadratic kernels -/

namespace Ostmann

open scoped BigOperators Classical

theorem quadraticSieveEnergy_reciprocityTwist (N : ℕ) (b : ℕ → ℂ) :
    quadraticSieveEnergy N (reciprocityTwist b) = quadraticSieveEnergy N b := by
  apply Finset.sum_congr rfl
  intro s _
  unfold reciprocityTwist
  split_ifs <;> simp

theorem quadraticTransposeSum_one_mod_four (N : ℕ) (b : ℕ → ℂ) (u : ℕ)
    (hu : u % 4 = 1) : quadraticTransposeSum N b u = quadraticSieveSum N b u := by
  apply Finset.sum_congr rfl
  intro s hs
  have hsodd := (Finset.mem_filter.mp hs).2.1
  rw [jacobiSym.quadratic_reciprocity_one_mod_four hu hsodd]

theorem quadraticTransposeSum_three_mod_four (N : ℕ) (b : ℕ → ℂ) (u : ℕ)
    (hu : u % 4 = 3) :
    quadraticTransposeSum N b u = quadraticSieveSum N (reciprocityTwist b) u := by
  apply Finset.sum_congr rfl
  intro s hs
  have hsodd := (Finset.mem_filter.mp hs).2.1
  rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hsodd) with hs1 | hs3
  · rw [jacobiSym.quadratic_reciprocity_one_mod_four' (Nat.odd_iff.mpr (by omega)) hs1]
    simp [reciprocityTwist, hs1]
  · rw [jacobiSym.quadratic_reciprocity_three_mod_four hu hs3]
    simp [reciprocityTwist, hs3]

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

 theorem quadraticTranspose_of_bound {M N : ℕ} {K : ℝ}
    (h : QuadraticSieveBound M N K) (b : ℕ → ℂ) :
    (∑ m ∈ oddSquarefreeRange M, ‖quadraticTransposeSum N b m‖ ^ 2) ≤
      2 * K * quadraticSieveEnergy N b := by
  have h1 := h b
  have h3 := h (reciprocityTwist b)
  rw [quadraticSieveEnergy_reciprocityTwist] at h3
  have ht : (∑ u ∈ oddSquarefreeRange M, ‖quadraticTransposeSum N b u‖ ^ 2) ≤
      (∑ u ∈ oddSquarefreeRange M, ‖quadraticSieveSum N b u‖ ^ 2) +
      ∑ u ∈ oddSquarefreeRange M, ‖quadraticSieveSum N (reciprocityTwist b) u‖ ^ 2 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro u hu
    have huodd := (Finset.mem_filter.mp hu).2.1
    rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp huodd) with hu1 | hu3
    · rw [quadraticTransposeSum_one_mod_four N b u hu1]
      linarith [sq_nonneg ‖quadraticSieveSum N (reciprocityTwist b) u‖]
    · rw [quadraticTransposeSum_three_mod_four N b u hu3]
      linarith [sq_nonneg ‖quadraticSieveSum N b u‖]
  nlinarith

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

 theorem quadraticSieveSum_restrict {N R : ℕ} (hNR : N ≤ R) (b : ℕ → ℂ) (m : ℕ) :
    quadraticSieveSum R (fun n => if n ∈ oddSquarefreeRange N then b n else 0) m =
      quadraticSieveSum N b m := by
  have hs := Finset.sum_subset (oddSquarefreeRange_mono hNR)
    (f := fun n => (if n ∈ oddSquarefreeRange N then b n else 0) * (jacobiSym (n : ℤ) m : ℂ))
    (by intro n _ hn; simp [hn])
  simpa only [Finset.sum_ite_mem, ite_mul, zero_mul, Finset.inter_self, quadraticSieveSum] using hs.symm

 theorem quadraticSieveEnergy_restrict {N R : ℕ} (hNR : N ≤ R) (b : ℕ → ℂ) :
    quadraticSieveEnergy R (fun n => if n ∈ oddSquarefreeRange N then b n else 0) =
      quadraticSieveEnergy N b := by
  have hs := Finset.sum_subset (oddSquarefreeRange_mono hNR)
    (f := fun n => ‖(if n ∈ oddSquarefreeRange N then b n else 0)‖ ^ 2)
    (by intro n _ hn; simp [hn])
  simpa only [apply_ite, norm_zero, ite_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, Finset.sum_ite_mem, Finset.inter_self, quadraticSieveEnergy] using hs.symm

 theorem QuadraticSieveBound.mono_second {M N R : ℕ} {K : ℝ}
    (hNR : N ≤ R) (h : QuadraticSieveBound M R K) : QuadraticSieveBound M N K := by
  intro b
  have hh := h (fun n => if n ∈ oddSquarefreeRange N then b n else 0)
  simpa only [quadraticSieveSum_restrict hNR, quadraticSieveEnergy_restrict hNR] using hh

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

 theorem quadraticTransposeSum_divisibility (s N : ℕ) (hs : Squarefree s) (ho : Odd s)
    (b : ℕ → ℂ) (m : ℤ) :
    quadraticTransposeSum N (fun n => if s ∣ n then b n else 0) m =
      (jacobiSym m s : ℂ) * quadraticTransposeSum (N / s) (quadraticDivisibilityCoeff s b) m := by
  unfold quadraticTransposeSum
  simp only [ite_mul, zero_mul]
  rw [← Finset.sum_filter, sum_oddSquarefree_multiples s N hs ho]
  simp only [quadraticDivisibilityCoeff, ite_mul, zero_mul, ← Finset.sum_filter]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  have hr0 := (Finset.mem_filter.mp (Finset.mem_filter.mp hr).1).2.2.ne_zero
  rw [jacobiSym.mul_right' m hs.ne_zero hr0]
  push_cast
  ring

 theorem quadraticSieveEnergy_divisibility (s N : ℕ) (hs : Squarefree s) (ho : Odd s)
    (b : ℕ → ℂ) :
    quadraticSieveEnergy (N / s) (quadraticDivisibilityCoeff s b) =
      quadraticSieveEnergy N (fun n => if s ∣ n then b n else 0) := by
  unfold quadraticSieveEnergy quadraticDivisibilityCoeff
  simp only [apply_ite, norm_zero, ite_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, ← Finset.sum_filter]
  exact (sum_oddSquarefree_multiples s N hs ho (fun n => ‖b n‖ ^ 2)).symm

 theorem quadratic_divisibility_energy {s M N : ℕ} {K : ℝ}
    (hs : Squarefree s) (ho : Odd s) (h : QuadraticSieveBound M (N / s) K)
    (b : ℕ → ℂ) :
    (∑ m ∈ oddSquarefreeRange M,
      ‖quadraticTransposeSum N (fun n => if s ∣ n then b n else 0) m‖ ^ 2) ≤
      2 * K * quadraticSieveEnergy N (fun n => if s ∣ n then b n else 0) := by
  have hb := quadraticTranspose_of_bound h (quadraticDivisibilityCoeff s b)
  rw [quadraticSieveEnergy_divisibility s N hs ho] at hb
  apply le_trans _ hb
  apply Finset.sum_le_sum
  intro m _
  rw [quadraticTransposeSum_divisibility s N hs ho, norm_mul, mul_pow]
  rcases jacobiSym.trichotomy (m : ℤ) s with hm | hm | hm <;> simp [hm]

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

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticBilinearExpansion
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The two-array coprime expansion needed for divisor restrictions -/

namespace Ostmann

open scoped Classical BigOperators ComplexConjugate

 theorem quadratic_coprime_bilinear_expansion (N₁ N₂ : ℕ) (a b : ℕ → ℂ) (m : ℤ) :
    quadraticCoprimeBilinear N₁ N₂ a b m =
      ∑ d ∈ Finset.Icc 1 N₂, (ArithmeticFunction.moebius d : ℂ) *
        quadraticTransposeSum N₁ (fun n => if d ∣ n then a n else 0) m *
        conj (quadraticTransposeSum N₂ (fun n => if d ∣ n then b n else 0) m) := by
  have hp (n₁ n₂ : ℕ) (hn₂ : n₂ ∈ oddSquarefreeRange N₂) :
      (if n₁.Coprime n₂ then (1 : ℂ) else 0) *
        a n₁ * conj (b n₂) * (jacobiSym m n₁ : ℂ) * (jacobiSym m n₂ : ℂ) =
      ∑ d ∈ Finset.Icc 1 N₂, (ArithmeticFunction.moebius d : ℂ) *
        (if d ∣ n₁ then a n₁ else 0) * conj (if d ∣ n₂ then b n₂ else 0) *
        (jacobiSym m n₁ : ℂ) * (jacobiSym m n₂ : ℂ) := by
    have hr := (Finset.mem_filter.mp hn₂).1
    rw [coprime_mask_truncated n₁ n₂ N₂ (Finset.mem_Icc.mp hr).1 (Finset.mem_Icc.mp hr).2]
    simp only [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro d _
    by_cases h₁ : d ∣ n₁ <;> by_cases h₂ : d ∣ n₂ <;>
      simp [h₁, h₂, mul_left_comm, mul_comm]
  unfold quadraticCoprimeBilinear
  calc
    _ = ∑ n₁ ∈ oddSquarefreeRange N₁, ∑ n₂ ∈ oddSquarefreeRange N₂,
        ∑ d ∈ Finset.Icc 1 N₂, (ArithmeticFunction.moebius d : ℂ) *
          (if d ∣ n₁ then a n₁ else 0) * conj (if d ∣ n₂ then b n₂ else 0) *
          (jacobiSym m n₁ : ℂ) * (jacobiSym m n₂ : ℂ) := by
      apply Finset.sum_congr rfl
      intro n₁ _
      exact Finset.sum_congr rfl (fun n₂ hn₂ => hp n₁ n₂ hn₂)
    _ = ∑ n₁ ∈ oddSquarefreeRange N₁, ∑ d ∈ Finset.Icc 1 N₂,
        ∑ n₂ ∈ oddSquarefreeRange N₂, (ArithmeticFunction.moebius d : ℂ) *
          (if d ∣ n₁ then a n₁ else 0) * conj (if d ∣ n₂ then b n₂ else 0) *
          (jacobiSym m n₁ : ℂ) * (jacobiSym m n₂ : ℂ) :=
      Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)
    _ = ∑ d ∈ Finset.Icc 1 N₂, ∑ n₁ ∈ oddSquarefreeRange N₁,
        ∑ n₂ ∈ oddSquarefreeRange N₂, (ArithmeticFunction.moebius d : ℂ) *
          (if d ∣ n₁ then a n₁ else 0) * conj (if d ∣ n₂ then b n₂ else 0) *
          (jacobiSym m n₁ : ℂ) * (jacobiSym m n₂ : ℂ) := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d _
      simp only [quadraticTransposeSum, map_sum, map_mul, map_intCast,
        Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro n₁ _
      apply Finset.sum_congr rfl
      intro n₂ _
      ring

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

 theorem quadratic_coprime_bilinear_pointwise (N₁ N₂ : ℕ) (a b : ℕ → ℂ) (m : ℤ) :
    ‖quadraticCoprimeBilinear N₁ N₂ a b m‖ ≤
      ∑ d ∈ Finset.Icc 1 N₂,
        ‖quadraticTransposeSum N₁ (fun n => if d ∣ n then a n else 0) m‖ *
        ‖quadraticTransposeSum N₂ (fun n => if d ∣ n then b n else 0) m‖ := by
  rw [quadratic_coprime_bilinear_expansion]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro d _
  have hd : ‖(ArithmeticFunction.moebius d : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_intCast]
    exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := d))
  simp only [norm_mul, Complex.norm_conj]
  calc
    _ ≤ 1 * ‖quadraticTransposeSum N₁ (fun n => if d ∣ n then a n else 0) m‖ *
        ‖quadraticTransposeSum N₂ (fun n => if d ∣ n then b n else 0) m‖ := by
      gcongr
    _ = _ := by ring

 theorem quadratic_coprime_bilinear_cauchy (M N₁ N₂ : ℕ) (a b : ℕ → ℂ) :
    (∑ m ∈ oddSquarefreeRange M, ‖quadraticCoprimeBilinear N₁ N₂ a b m‖) ≤
      Real.sqrt (∑ d ∈ Finset.Icc 1 N₂, ∑ m ∈ oddSquarefreeRange M,
        ‖quadraticTransposeSum N₁ (fun n => if d ∣ n then a n else 0) m‖ ^ 2) *
      Real.sqrt (∑ d ∈ Finset.Icc 1 N₂, ∑ m ∈ oddSquarefreeRange M,
        ‖quadraticTransposeSum N₂ (fun n => if d ∣ n then b n else 0) m‖ ^ 2) := by
  calc
    _ ≤ ∑ m ∈ oddSquarefreeRange M, ∑ d ∈ Finset.Icc 1 N₂,
        ‖quadraticTransposeSum N₁ (fun n => if d ∣ n then a n else 0) m‖ *
        ‖quadraticTransposeSum N₂ (fun n => if d ∣ n then b n else 0) m‖ :=
      Finset.sum_le_sum (fun m _ => quadratic_coprime_bilinear_pointwise N₁ N₂ a b m)
    _ = ∑ z ∈ (Finset.Icc 1 N₂).product (oddSquarefreeRange M),
        ‖quadraticTransposeSum N₁ (fun n => if z.1 ∣ n then a n else 0) z.2‖ *
        ‖quadraticTransposeSum N₂ (fun n => if z.1 ∣ n then b n else 0) z.2‖ := by
      rw [Finset.sum_comm, Finset.product_eq_sprod, Finset.sum_product]
    _ ≤ _ := by
      have hc := Real.sum_mul_le_sqrt_mul_sqrt
        ((Finset.Icc 1 N₂).product (oddSquarefreeRange M))
        (fun z => ‖quadraticTransposeSum N₁ (fun n => if z.1 ∣ n then a n else 0) z.2‖)
        (fun z => ‖quadraticTransposeSum N₂ (fun n => if z.1 ∣ n then b n else 0) z.2‖)
      simpa only [Finset.product_eq_sprod, Finset.sum_product] using hc

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticDivisorSplit
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact split of a product divisor between coprime coefficients -/

namespace Ostmann

open scoped Classical BigOperators ComplexConjugate

 theorem quadratic_divisor_split_unique {d n₁ n₂ e : ℕ} (_hd : d ≠ 0)
    (hcop : n₁.Coprime n₂) (he : e ∣ d) (h₁ : e ∣ n₁) (h₂ : d / e ∣ n₂) :
    e = d.gcd n₁ := by
  have hcross : (d / e).Coprime n₁ := hcop.symm.of_dvd_left h₂
  have hg := Nat.gcd_mul_of_coprime_of_dvd hcross h₁
  simpa only [Nat.div_mul_cancel he] using hg.symm

 theorem quadratic_divisor_split_exists {d n₁ n₂ : ℕ} (hd : 0 < d)
    (hcop : n₁.Coprime n₂) (hdiv : d ∣ n₁ * n₂) :
    d.gcd n₁ ∈ d.divisors ∧ d.gcd n₁ ∣ n₁ ∧ d / d.gcd n₁ ∣ n₂ := by
  have hprod : d.gcd n₁ * d.gcd n₂ = d :=
    (Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime hcop).mpr hdiv
  have hg : 0 < d.gcd n₁ := Nat.gcd_pos_of_pos_left n₁ hd
  have heq : d / d.gcd n₁ = d.gcd n₂ := by
    exact Nat.div_eq_of_eq_mul_left hg (by simpa only [Nat.mul_comm] using hprod.symm)
  exact ⟨Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left _ _, hd.ne'⟩,
    Nat.gcd_dvd_right _ _, heq ▸ Nat.gcd_dvd_right d n₂⟩

 theorem quadratic_product_divisor_indicator {d n₁ n₂ : ℕ} (hd : 0 < d)
    (hcop : n₁.Coprime n₂) :
    (if d ∣ n₁ * n₂ then (1 : ℂ) else 0) =
      ∑ e ∈ d.divisors, if e ∣ n₁ ∧ d / e ∣ n₂ then (1 : ℂ) else 0 := by
  by_cases hdiv : d ∣ n₁ * n₂
  · obtain ⟨he, h₁, h₂⟩ := quadratic_divisor_split_exists hd hcop hdiv
    rw [ite_eq_left hdiv, Finset.sum_eq_single (d.gcd n₁)]
    · rw [ite_eq_left ⟨h₁, h₂⟩]
    · intro e he' hne
      apply ite_eq_right
      intro hh
      exact hne (quadratic_divisor_split_unique hd.ne' hcop
        (Nat.dvd_of_mem_divisors he') hh.1 hh.2)
    · exact fun hn => (hn he).elim
  · rw [ite_eq_right hdiv]
    symm
    apply Finset.sum_eq_zero
    intro e he
    apply ite_eq_right
    intro hh
    have hp := Nat.mul_dvd_mul hh.1 hh.2
    rw [Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors he)] at hp
    exact hdiv hp

 theorem quadratic_divisor_bilinear_split (N₁ N₂ d : ℕ) (hd : 0 < d)
    (a b : ℕ → ℂ) (m : ℤ) :
    quadraticDivisorBilinear N₁ N₂ d a b m =
      ∑ e ∈ d.divisors, quadraticCoprimeBilinear N₁ N₂
        (fun n => if e ∣ n then a n else 0)
        (fun n => if d / e ∣ n then b n else 0) m := by
  have hp (n₁ n₂ : ℕ) :
      (if n₁.Coprime n₂ ∧ d ∣ n₁ * n₂ then (1 : ℂ) else 0) *
        a n₁ * conj (b n₂) * (jacobiSym m n₁ : ℂ) * (jacobiSym m n₂ : ℂ) =
      ∑ e ∈ d.divisors, (if n₁.Coprime n₂ then (1 : ℂ) else 0) *
        (if e ∣ n₁ then a n₁ else 0) * conj (if d / e ∣ n₂ then b n₂ else 0) *
        (jacobiSym m n₁ : ℂ) * (jacobiSym m n₂ : ℂ) := by
    by_cases hc : n₁.Coprime n₂
    · simp_rw [ite_eq_left hc, one_mul]
      have hi : (if n₁.Coprime n₂ ∧ d ∣ n₁ * n₂ then (1 : ℂ) else 0) =
          (if d ∣ n₁ * n₂ then 1 else 0) := by
        by_cases hx : d ∣ n₁ * n₂ <;> simp [hc, hx]
      rw [hi, quadratic_product_divisor_indicator hd hc]
      simp only [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro e _
      by_cases h₁ : e ∣ n₁ <;> by_cases h₂ : d / e ∣ n₂ <;> simp [h₁, h₂]
    · simp [hc]
  unfold quadraticDivisorBilinear
  simp_rw [hp]
  calc
    _ = ∑ n₁ ∈ oddSquarefreeRange N₁, ∑ e ∈ d.divisors,
        ∑ n₂ ∈ oddSquarefreeRange N₂,
          (if n₁.Coprime n₂ then (1 : ℂ) else 0) *
            (if e ∣ n₁ then a n₁ else 0) * conj (if d / e ∣ n₂ then b n₂ else 0) *
            (jacobiSym m n₁ : ℂ) * (jacobiSym m n₂ : ℂ) :=
      Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)
    _ = _ := Finset.sum_comm

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticRestrictedBilinear
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Divisor restrictions shorten each side of the coprime bilinear form

The Möbius divisor is kept separate from the fixed divisor. No replacement
of two divisibility conditions by their product is needed.
-/

namespace Ostmann

open scoped Classical BigOperators

 theorem quadratic_restricted_transpose_energy {M N s D : ℕ} {K : ℝ}
    (hs : Squarefree s) (ho : Odd s) (hK : 0 ≤ K)
    (h : QuadraticSieveBound M (N / s) K) (a : ℕ → ℂ) :
    (∑ u ∈ Finset.Icc 1 D, ∑ m ∈ oddSquarefreeRange M,
      ‖quadraticTransposeSum N
        (fun n => if u ∣ n then (if s ∣ n then a n else 0) else 0) m‖ ^ 2) ≤
      2 * K * ∑ n ∈ oddSquarefreeRange N,
        (n.divisors.card : ℝ) * ‖if s ∣ n then a n else 0‖ ^ 2 := by
  calc
    _ ≤ ∑ u ∈ Finset.Icc 1 D,
        2 * K * quadraticSieveEnergy N
          (fun n => if u ∣ n then (if s ∣ n then a n else 0) else 0) := by
      apply Finset.sum_le_sum
      intro u _
      have heq : (fun n => if u ∣ n then (if s ∣ n then a n else 0) else 0) =
          (fun n => if s ∣ n then (if u ∣ n then a n else 0) else 0) := by
        funext n
        by_cases hu : u ∣ n <;> by_cases hs' : s ∣ n <;> simp [hu, hs']
      rw [heq]
      exact quadratic_divisibility_energy hs ho h _
    _ ≤ _ := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left
        (quadratic_divisibility_partial_energy D N (fun n => if s ∣ n then a n else 0))
        (by positivity)

 theorem quadratic_coprime_restricted_bound {M N₁ N₂ s₁ s₂ : ℕ} {K₁ K₂ : ℝ}
    (hs₁ : Squarefree s₁) (ho₁ : Odd s₁) (hs₂ : Squarefree s₂) (ho₂ : Odd s₂)
    (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂)
    (h₁ : QuadraticSieveBound M (N₁ / s₁) K₁)
    (h₂ : QuadraticSieveBound M (N₂ / s₂) K₂) (a b : ℕ → ℂ) :
    (∑ m ∈ oddSquarefreeRange M,
      ‖quadraticCoprimeBilinear N₁ N₂
        (fun n => if s₁ ∣ n then a n else 0)
        (fun n => if s₂ ∣ n then b n else 0) m‖) ≤
      Real.sqrt (2 * K₁ * ∑ n ∈ oddSquarefreeRange N₁,
        (n.divisors.card : ℝ) * ‖if s₁ ∣ n then a n else 0‖ ^ 2) *
      Real.sqrt (2 * K₂ * ∑ n ∈ oddSquarefreeRange N₂,
        (n.divisors.card : ℝ) * ‖if s₂ ∣ n then b n else 0‖ ^ 2) := by
  apply (quadratic_coprime_bilinear_cauchy M N₁ N₂ _ _).trans
  exact mul_le_mul
    (Real.sqrt_le_sqrt (quadratic_restricted_transpose_energy hs₁ ho₁ hK₁ h₁ a))
    (Real.sqrt_le_sqrt (quadratic_restricted_transpose_energy hs₂ ho₂ hK₂ h₂ b))
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

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

 theorem quadraticDivisorMoment_nonneg (N : ℕ) (a : ℕ → ℂ) :
    0 ≤ quadraticDivisorMoment N a := by
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

 theorem quadratic_divisor_weight_sqrt_sum (N : ℕ) (S : Finset ℕ)
    (K : ℝ) (hK : 0 ≤ K) (a : ℕ → ℂ) :
    (∑ s ∈ S, Real.sqrt (2 * K * quadraticDivisorWeight N s a)) ≤
      Real.sqrt (2 * K * S.card * quadraticDivisorMoment N a) := by
  have hw (s : ℕ) : 0 ≤ 2 * K * quadraticDivisorWeight N s a :=
    mul_nonneg (by positivity) (quadraticDivisorWeight_nonneg N s a)
  have hc := Real.sum_mul_le_sqrt_mul_sqrt S (fun _ => (1 : ℝ))
    (fun s => Real.sqrt (2 * K * quadraticDivisorWeight N s a))
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hc
  have he : (∑ s ∈ S, Real.sqrt (2 * K * quadraticDivisorWeight N s a) ^ 2) =
      2 * K * ∑ s ∈ S, quadraticDivisorWeight N s a := by
    simp only [Real.sq_sqrt (hw _), Finset.mul_sum]
  rw [he, ← Real.sqrt_mul (Nat.cast_nonneg S.card)] at hc
  apply hc.trans
  apply Real.sqrt_le_sqrt
  calc
    _ ≤ (S.card : ℝ) * (2 * K * quadraticDivisorMoment N a) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (quadratic_divisor_weight_sum N S a) (by positivity))
        (Nat.cast_nonneg _)
    _ = _ := by ring

 theorem quadratic_divisor_family_bound (M N₁ N₂ : ℕ) (S₁ S₂ : Finset ℕ)
    (K₁ K₂ : ℝ) (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂)
    (hs₁ : ∀ s ∈ S₁, Squarefree s ∧ Odd s)
    (hs₂ : ∀ s ∈ S₂, Squarefree s ∧ Odd s)
    (h₁ : ∀ s ∈ S₁, QuadraticSieveBound M (N₁ / s) K₁)
    (h₂ : ∀ s ∈ S₂, QuadraticSieveBound M (N₂ / s) K₂) (a b : ℕ → ℂ) :
    (∑ s₁ ∈ S₁, ∑ s₂ ∈ S₂, ∑ m ∈ oddSquarefreeRange M,
      ‖quadraticCoprimeBilinear N₁ N₂
        (fun n => if s₁ ∣ n then a n else 0)
        (fun n => if s₂ ∣ n then b n else 0) m‖) ≤
      Real.sqrt (2 * K₁ * S₁.card * quadraticDivisorMoment N₁ a) *
      Real.sqrt (2 * K₂ * S₂.card * quadraticDivisorMoment N₂ b) := by
  calc
    _ ≤ ∑ s₁ ∈ S₁, ∑ s₂ ∈ S₂,
        Real.sqrt (2 * K₁ * quadraticDivisorWeight N₁ s₁ a) *
        Real.sqrt (2 * K₂ * quadraticDivisorWeight N₂ s₂ b) := by
      apply Finset.sum_le_sum
      intro s₁ hs₁'
      apply Finset.sum_le_sum
      intro s₂ hs₂'
      exact quadratic_coprime_restricted_bound (hs₁ s₁ hs₁').1 (hs₁ s₁ hs₁').2
        (hs₂ s₂ hs₂').1 (hs₂ s₂ hs₂').2 hK₁ hK₂ (h₁ s₁ hs₁') (h₂ s₂ hs₂') a b
    _ = (∑ s₁ ∈ S₁, Real.sqrt (2 * K₁ * quadraticDivisorWeight N₁ s₁ a)) *
        ∑ s₂ ∈ S₂, Real.sqrt (2 * K₂ * quadraticDivisorWeight N₂ s₂ b) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro _ _
      rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul (quadratic_divisor_weight_sqrt_sum N₁ S₁ K₁ hK₁ a)
      (quadratic_divisor_weight_sqrt_sum N₂ S₂ K₂ hK₂ b)
      (Finset.sum_nonneg (fun _ _ => Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticDivisorRectangle
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact finite divisor rectangle underlying the bilinear estimate -/

namespace Ostmann

open scoped Classical BigOperators ComplexConjugate

 theorem mem_oddSquarefreeRange_of_dvd {s n N : ℕ} (hn : n ∈ oddSquarefreeRange N)
    (hs : s ∣ n) : s ∈ oddSquarefreeRange N := by
  obtain ⟨hr, ho, hsq⟩ := Finset.mem_filter.mp hn
  have hsm : s ∈ n.divisors := Nat.mem_divisors.mpr ⟨hs, hsq.ne_zero⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
    ⟨Nat.pos_of_mem_divisors hsm, (Nat.le_of_dvd (Finset.mem_Icc.mp hr).1 hs).trans
      (Finset.mem_Icc.mp hr).2⟩,
    ho.of_dvd_nat hs, hsq.squarefree_of_dvd hs⟩

 theorem quadratic_restricted_bilinear_zero_left {N₁ N₂ s₁ s₂ : ℕ}
    (hs : s₁ ∉ oddSquarefreeRange N₁) (a b : ℕ → ℂ) (m : ℤ) :
    quadraticCoprimeBilinear N₁ N₂ (fun n => if s₁ ∣ n then a n else 0)
      (fun n => if s₂ ∣ n then b n else 0) m = 0 := by
  unfold quadraticCoprimeBilinear
  apply Finset.sum_eq_zero
  intro n₁ hn₁
  apply Finset.sum_eq_zero
  intro n₂ _
  have hd : ¬s₁ ∣ n₁ := fun h => hs (mem_oddSquarefreeRange_of_dvd hn₁ h)
  simp [hd]

 theorem quadratic_restricted_bilinear_zero_right {N₁ N₂ s₁ s₂ : ℕ}
    (hs : s₂ ∉ oddSquarefreeRange N₂) (a b : ℕ → ℂ) (m : ℤ) :
    quadraticCoprimeBilinear N₁ N₂ (fun n => if s₁ ∣ n then a n else 0)
      (fun n => if s₂ ∣ n then b n else 0) m = 0 := by
  unfold quadraticCoprimeBilinear
  apply Finset.sum_eq_zero
  intro n₁ _
  apply Finset.sum_eq_zero
  intro n₂ hn₂
  have hd : ¬s₂ ∣ n₂ := fun h => hs (mem_oddSquarefreeRange_of_dvd hn₂ h)
  simp [hd]

 theorem quadratic_restricted_bilinear_support {N₁ N₂ s₁ s₂ : ℕ}
    (a b : ℕ → ℂ) (m : ℤ)
    (h : quadraticCoprimeBilinear N₁ N₂ (fun n => if s₁ ∣ n then a n else 0)
      (fun n => if s₂ ∣ n then b n else 0) m ≠ 0) :
    s₁ ∈ oddSquarefreeRange N₁ ∧ s₂ ∈ oddSquarefreeRange N₂ := by
  constructor
  · by_contra hs
    exact h (quadratic_restricted_bilinear_zero_left hs a b m)
  · by_contra hs
    exact h (quadratic_restricted_bilinear_zero_right hs a b m)

 theorem quadratic_divisor_bilinear_rectangle (N₁ N₂ d : ℕ) (hd : 0 < d)
    (a b : ℕ → ℂ) (m : ℤ) :
    quadraticDivisorBilinear N₁ N₂ d a b m =
      ∑ z ∈ (oddSquarefreeRange N₁).product (oddSquarefreeRange N₂),
        if z.1 * z.2 = d then quadraticCoprimeBilinear N₁ N₂
          (fun n => if z.1 ∣ n then a n else 0)
          (fun n => if z.2 ∣ n then b n else 0) m else 0 := by
  rw [quadratic_divisor_bilinear_split N₁ N₂ d hd]
  apply Finset.sum_bij_ne_zero (fun e _ _ => (e, d / e))
  · intro e _ he
    exact Finset.mem_product.mpr (quadratic_restricted_bilinear_support a b m he)
  · intro e _ _ f _ _ hef
    exact congrArg Prod.fst hef
  · intro z hz hz0
    have heq : z.1 * z.2 = d := by
      by_contra heq
      simp only [ite_eq_right heq] at hz0
      exact hz0 rfl
    have hzpos : 0 < z.1 :=
      (Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_product.mp hz).1).1).1
    have hdiv : d / z.1 = z.2 :=
      Nat.div_eq_of_eq_mul_left hzpos (by simpa only [mul_comm] using heq.symm)
    refine ⟨z.1, Nat.mem_divisors.mpr ⟨⟨z.2, heq.symm⟩, hd.ne'⟩, ?_, ?_⟩
    · simpa only [ite_eq_left heq, hdiv] using hz0
    · exact Prod.ext rfl hdiv
  · intro e he _
    have heq : e * (d / e) = d := Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors he)
    exact (ite_eq_left heq).symm

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticDivisorRange
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bounding the original product-divisibility sum by its exact rectangle -/

namespace Ostmann

open scoped Classical BigOperators

 theorem quadratic_divisor_range_triangle (M N₁ N₂ D : ℕ) (a b : ℕ → ℂ) :
    (∑ d ∈ Finset.Ioc D (2 * D), ∑ m ∈ oddSquarefreeRange M,
      ‖quadraticDivisorBilinear N₁ N₂ d a b m‖) ≤
    ∑ z ∈ quadraticDivisorRangePairs N₁ N₂ D, ∑ m ∈ oddSquarefreeRange M,
      ‖quadraticCoprimeBilinear N₁ N₂
        (fun n => if z.1 ∣ n then a n else 0)
        (fun n => if z.2 ∣ n then b n else 0) m‖ := by
  let R := (oddSquarefreeRange N₁).product (oddSquarefreeRange N₂)
  let F : ℕ × ℕ → ℝ := fun z => ∑ m ∈ oddSquarefreeRange M,
    ‖quadraticCoprimeBilinear N₁ N₂
      (fun n => if z.1 ∣ n then a n else 0)
      (fun n => if z.2 ∣ n then b n else 0) m‖
  have hp (d : ℕ) (hd : 0 < d) :
      (∑ m ∈ oddSquarefreeRange M, ‖quadraticDivisorBilinear N₁ N₂ d a b m‖) ≤
        ∑ z ∈ R, if z.1 * z.2 = d then F z else 0 := by
    calc
      _ ≤ ∑ m ∈ oddSquarefreeRange M, ∑ z ∈ R,
          if z.1 * z.2 = d then
            ‖quadraticCoprimeBilinear N₁ N₂
              (fun n => if z.1 ∣ n then a n else 0)
              (fun n => if z.2 ∣ n then b n else 0) m‖ else 0 := by
        apply Finset.sum_le_sum
        intro m _
        rw [quadratic_divisor_bilinear_rectangle N₁ N₂ d hd]
        apply (norm_sum_le _ _).trans_eq
        apply Finset.sum_congr rfl
        intro z _
        split_ifs <;> simp
      _ = _ := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro z _
        by_cases hz : z.1 * z.2 = d <;> simp [hz, F]
  calc
    _ ≤ ∑ d ∈ Finset.Ioc D (2 * D), ∑ z ∈ R,
        if z.1 * z.2 = d then F z else 0 := by
      apply Finset.sum_le_sum
      intro d hd
      exact hp d (lt_of_le_of_lt (Nat.zero_le D) (Finset.mem_Ioc.mp hd).1)
    _ = ∑ z ∈ R, if D < z.1 * z.2 ∧ z.1 * z.2 ≤ 2 * D then F z else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro z _
      simp only [Finset.sum_ite_eq, Finset.mem_Ioc]
    _ = _ := by rw [← Finset.sum_filter]; rfl

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

 theorem quadraticDyadicDivisors_card (N j : ℕ) :
    (quadraticDyadicDivisors N j).card ≤ 2 ^ j := by
  have hs : quadraticDyadicDivisors N j ⊆ Finset.Ico (2 ^ j) (2 ^ (j + 1)) := by
    intro s hs
    exact Finset.mem_Ico.mpr (quadraticDyadicDivisors_bounds hs)
  calc
    _ ≤ (Finset.Ico (2 ^ j) (2 ^ (j + 1))).card := Finset.card_le_card hs
    _ = 2 ^ j := by rw [Nat.card_Ico, pow_succ]; omega

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

 theorem quadratic_dyadic_pair_sum {R : Type*} [AddCommMonoid R]
    (N₁ N₂ : ℕ) (f : ℕ → ℕ → R) :
    (∑ i ∈ Finset.range (Nat.log 2 N₁ + 1), ∑ j ∈ Finset.range (Nat.log 2 N₂ + 1),
      ∑ s ∈ quadraticDyadicDivisors N₁ i, ∑ t ∈ quadraticDyadicDivisors N₂ j, f s t) =
      ∑ s ∈ oddSquarefreeRange N₁, ∑ t ∈ oddSquarefreeRange N₂, f s t := by
  calc
    _ = ∑ i ∈ Finset.range (Nat.log 2 N₁ + 1), ∑ s ∈ quadraticDyadicDivisors N₁ i,
        ∑ j ∈ Finset.range (Nat.log 2 N₂ + 1), ∑ t ∈ quadraticDyadicDivisors N₂ j, f s t :=
      Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)
    _ = ∑ i ∈ Finset.range (Nat.log 2 N₁ + 1), ∑ s ∈ quadraticDyadicDivisors N₁ i,
        ∑ t ∈ oddSquarefreeRange N₂, f s t := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_congr rfl (fun s _ => quadratic_dyadic_divisors_sum N₂ (f s))
    _ = _ := quadratic_dyadic_divisors_sum N₁ _

 theorem quadratic_dyadic_divisor_family_bound (M N₁ N₂ i j : ℕ)
    (K₁ K₂ : ℝ) (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂)
    (h₁ : QuadraticSieveBound M (N₁ / 2 ^ i) K₁)
    (h₂ : QuadraticSieveBound M (N₂ / 2 ^ j) K₂) (a b : ℕ → ℂ) :
    (∑ s₁ ∈ quadraticDyadicDivisors N₁ i, ∑ s₂ ∈ quadraticDyadicDivisors N₂ j,
      ∑ m ∈ oddSquarefreeRange M, ‖quadraticCoprimeBilinear N₁ N₂
        (fun n => if s₁ ∣ n then a n else 0)
        (fun n => if s₂ ∣ n then b n else 0) m‖) ≤
      Real.sqrt (2 * K₁ * (2 ^ i : ℕ) * quadraticDivisorMoment N₁ a) *
      Real.sqrt (2 * K₂ * (2 ^ j : ℕ) * quadraticDivisorMoment N₂ b) := by
  have hs (N k s : ℕ) (h : s ∈ quadraticDyadicDivisors N k) :
      Squarefree s ∧ Odd s := by
    obtain ⟨hr, _⟩ := Finset.mem_filter.mp h
    exact ⟨(Finset.mem_filter.mp hr).2.2, (Finset.mem_filter.mp hr).2.1⟩
  have hcut₁ : ∀ s ∈ quadraticDyadicDivisors N₁ i,
      QuadraticSieveBound M (N₁ / s) K₁ := by
    intro s hs'
    exact QuadraticSieveBound.mono_second (Nat.div_le_div_left
      (quadraticDyadicDivisors_bounds hs').1 (by positivity)) h₁
  have hcut₂ : ∀ s ∈ quadraticDyadicDivisors N₂ j,
      QuadraticSieveBound M (N₂ / s) K₂ := by
    intro s hs'
    exact QuadraticSieveBound.mono_second (Nat.div_le_div_left
      (quadraticDyadicDivisors_bounds hs').1 (by positivity)) h₂
  apply (quadratic_divisor_family_bound M N₁ N₂ _ _ K₁ K₂ hK₁ hK₂
    (hs N₁ i) (hs N₂ j) hcut₁ hcut₂ a b).trans
  apply mul_le_mul _ _ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  · apply Real.sqrt_le_sqrt
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (by exact_mod_cast quadraticDyadicDivisors_card N₁ i)
        (by positivity)) (quadraticDivisorMoment_nonneg N₁ a)
  · apply Real.sqrt_le_sqrt
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (by exact_mod_cast quadraticDyadicDivisors_card N₂ j)
        (by positivity)) (quadraticDivisorMoment_nonneg N₂ b)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticDyadicSelection
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Selecting a genuine divisor block with the original product range -/

namespace Ostmann

open scoped Classical BigOperators

 theorem quadratic_dyadic_divisor_mass_total (M N₁ N₂ D : ℕ) (a b : ℕ → ℂ) :
    (∑ i ∈ Finset.range (Nat.log 2 N₁ + 1), ∑ j ∈ Finset.range (Nat.log 2 N₂ + 1),
      quadraticDyadicDivisorMass M N₁ N₂ D i j a b) =
      ∑ z ∈ quadraticDivisorRangePairs N₁ N₂ D, ∑ m ∈ oddSquarefreeRange M,
        ‖quadraticCoprimeBilinear N₁ N₂
          (fun n => if z.1 ∣ n then a n else 0)
          (fun n => if z.2 ∣ n then b n else 0) m‖ := by
  unfold quadraticDyadicDivisorMass
  rw [quadratic_dyadic_pair_sum]
  rw [quadraticDivisorRangePairs, Finset.sum_filter, Finset.product_eq_sprod,
    Finset.sum_product]

 theorem quadratic_positive_block_product_bounds {M N₁ N₂ D i j : ℕ} (a b : ℕ → ℂ)
    (h : 0 < quadraticDyadicDivisorMass M N₁ N₂ D i j a b) :
    D < 4 * (2 ^ i * 2 ^ j) ∧ 2 ^ i * 2 ^ j ≤ 2 * D := by
  have hw (s t : ℕ) : 0 ≤
      (if D < s * t ∧ s * t ≤ 2 * D then
        ∑ m ∈ oddSquarefreeRange M, ‖quadraticCoprimeBilinear N₁ N₂
          (fun n => if s ∣ n then a n else 0)
          (fun n => if t ∣ n then b n else 0) m‖ else 0) := by
    split_ifs
    · exact Finset.sum_nonneg (fun _ _ => norm_nonneg _)
    · rfl
  obtain ⟨s, hs, hsum⟩ := (Finset.sum_pos_iff_of_nonneg (fun s _ =>
    Finset.sum_nonneg (fun t _ => hw s t))).mp h
  obtain ⟨t, ht, hp⟩ := (Finset.sum_pos_iff_of_nonneg (fun t _ => hw s t)).mp hsum
  have hd : D < s * t ∧ s * t ≤ 2 * D := by
    by_contra hd
    simp only [ite_eq_right hd, lt_self_iff_false] at hp
  obtain ⟨hsl, hsu⟩ := quadraticDyadicDivisors_bounds hs
  obtain ⟨htl, htu⟩ := quadraticDyadicDivisors_bounds ht
  have hlo := Nat.mul_le_mul hsl htl
  have hhi := Nat.mul_lt_mul_of_lt_of_lt hsu htu
  rw [pow_succ, pow_succ] at hhi
  constructor
  · nlinarith [hd.1]
  · exact hlo.trans hd.2

 theorem quadratic_divisor_block_selection (M N₁ N₂ D : ℕ) (a b : ℕ → ℂ)
    (hpos : 0 < ∑ d ∈ Finset.Ioc D (2 * D), ∑ m ∈ oddSquarefreeRange M,
      ‖quadraticDivisorBilinear N₁ N₂ d a b m‖) :
    ∃ i ≤ Nat.log 2 N₁, ∃ j ≤ Nat.log 2 N₂,
      0 < quadraticDyadicDivisorMass M N₁ N₂ D i j a b ∧
      D < 4 * (2 ^ i * 2 ^ j) ∧ 2 ^ i * 2 ^ j ≤ 2 * D ∧
      (∑ d ∈ Finset.Ioc D (2 * D), ∑ m ∈ oddSquarefreeRange M,
        ‖quadraticDivisorBilinear N₁ N₂ d a b m‖) ≤
      ((Nat.log 2 N₁ + 1 : ℕ) : ℝ) * (Nat.log 2 N₂ + 1) *
        quadraticDyadicDivisorMass M N₁ N₂ D i j a b := by
  let J := (Finset.range (Nat.log 2 N₁ + 1)).product (Finset.range (Nat.log 2 N₂ + 1))
  let F : ℕ × ℕ → ℝ := fun z => quadraticDyadicDivisorMass M N₁ N₂ D z.1 z.2 a b
  have hJ : J.Nonempty := ⟨(0, 0), Finset.mem_product.mpr
    ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega)⟩⟩
  obtain ⟨z, hz, hmax⟩ := Finset.exists_max_image J F hJ
  have hsum : (∑ d ∈ Finset.Ioc D (2 * D), ∑ m ∈ oddSquarefreeRange M,
      ‖quadraticDivisorBilinear N₁ N₂ d a b m‖) ≤
      ((Nat.log 2 N₁ + 1 : ℕ) : ℝ) * (Nat.log 2 N₂ + 1) * F z := by
    calc
      _ ≤ ∑ w ∈ J, F w := by
        rw [show J = (Finset.range (Nat.log 2 N₁ + 1)).product
          (Finset.range (Nat.log 2 N₂ + 1)) from rfl,
          Finset.product_eq_sprod, Finset.sum_product]
        rw [quadratic_dyadic_divisor_mass_total]
        exact quadratic_divisor_range_triangle M N₁ N₂ D a b
      _ ≤ J.card • F z := Finset.sum_le_card_nsmul J F (F z) hmax
      _ = _ := by simp [J, nsmul_eq_mul, Nat.cast_mul, mul_assoc]
  have hblock : 0 < F z := by
    by_contra! hn
    have hz' : ((Nat.log 2 N₁ + 1 : ℕ) : ℝ) * (Nat.log 2 N₂ + 1) * F z ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) hn
    exact (not_lt_of_ge (hsum.trans hz')) hpos
  obtain ⟨h₁, h₂⟩ := quadratic_positive_block_product_bounds a b hblock
  obtain ⟨hi, hj⟩ := Finset.mem_product.mp hz
  exact ⟨z.1, by have := Finset.mem_range.mp hi; omega,
    z.2, by have := Finset.mem_range.mp hj; omega, hblock, h₁, h₂, hsum⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticBilinearComparison
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The divisor-constrained comparison with concrete selected scales

This is the finite comparison of Heath-Brown (1995), Lemma 10. We retain the
explicit number of dyadic bins instead of enlarging the selected scales to
hide logarithms. All quadratic matrix bounds are at the actual shorter ranges.
-/

namespace Ostmann

open scoped Classical BigOperators

 theorem quadratic_dyadic_divisor_mass_bound (M N₁ N₂ D i j : ℕ)
    (K₁ K₂ : ℝ) (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂)
    (h₁ : QuadraticSieveBound M (N₁ / 2 ^ i) K₁)
    (h₂ : QuadraticSieveBound M (N₂ / 2 ^ j) K₂) (a b : ℕ → ℂ) :
    quadraticDyadicDivisorMass M N₁ N₂ D i j a b ≤
      Real.sqrt (2 * K₁ * (2 ^ i : ℕ) * quadraticDivisorMoment N₁ a) *
      Real.sqrt (2 * K₂ * (2 ^ j : ℕ) * quadraticDivisorMoment N₂ b) := by
  apply le_trans _ (quadratic_dyadic_divisor_family_bound M N₁ N₂ i j
    K₁ K₂ hK₁ hK₂ h₁ h₂ a b)
  apply Finset.sum_le_sum
  intro s _
  apply Finset.sum_le_sum
  intro t _
  split_ifs
  · rfl
  · exact Finset.sum_nonneg (fun _ _ => norm_nonneg _)

 theorem quadratic_bilinear_comparison (M N₁ N₂ D : ℕ) (a b : ℕ → ℂ)
    (hpos : 0 < ∑ d ∈ Finset.Ioc D (2 * D), ∑ m ∈ oddSquarefreeRange M,
      ‖quadraticDivisorBilinear N₁ N₂ d a b m‖) :
    ∃ i ≤ Nat.log 2 N₁, ∃ j ≤ Nat.log 2 N₂,
      D < 4 * (2 ^ i * 2 ^ j) ∧ 2 ^ i * 2 ^ j ≤ 2 * D ∧
      ∀ K₁ K₂ : ℝ, 0 ≤ K₁ → 0 ≤ K₂ →
      QuadraticSieveBound M (N₁ / 2 ^ i) K₁ →
      QuadraticSieveBound M (N₂ / 2 ^ j) K₂ →
      (∑ d ∈ Finset.Ioc D (2 * D), ∑ m ∈ oddSquarefreeRange M,
        ‖quadraticDivisorBilinear N₁ N₂ d a b m‖) ≤
      ((Nat.log 2 N₁ + 1 : ℕ) : ℝ) * (Nat.log 2 N₂ + 1) *
        (Real.sqrt (2 * K₁ * (2 ^ i : ℕ) * quadraticDivisorMoment N₁ a) *
          Real.sqrt (2 * K₂ * (2 ^ j : ℕ) * quadraticDivisorMoment N₂ b)) := by
  obtain ⟨i, hi, j, hj, _, hD₁, hD₂, hb⟩ := quadratic_divisor_block_selection
    M N₁ N₂ D a b hpos
  refine ⟨i, hi, j, hj, hD₁, hD₂, ?_⟩
  intro K₁ K₂ hK₁ hK₂ h₁ h₂
  exact hb.trans (mul_le_mul_of_nonneg_left
    (quadratic_dyadic_divisor_mass_bound M N₁ N₂ D i j K₁ K₂ hK₁ hK₂ h₁ h₂ a b)
    (by positivity))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticComparisonEnvelope
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The numerical minimum in the first recursive quadratic comparison

Here P is the product of the two selected divisor scales and Y is B to the
current sieve exponent. This is the three-term calculation in Heath-Brown,
section 8, equations (19)--(20).
-/

namespace Ostmann

theorem quadratic_comparison_prefactor {M N B P : ℝ}
    (hM : 0 < M) (hN : 0 < N) (hB : 0 < B) (hP : 0 < P) :
    let S := M / N * Real.sqrt P * min 1 (N / (Real.sqrt M * Real.sqrt B * P))
    0 ≤ S ∧ S ≤ M / N * Real.sqrt P ∧ S ≤ Real.sqrt M / (Real.sqrt B * Real.sqrt P) := by
  dsimp only
  have hbase : 0 ≤ M / N * Real.sqrt P := by positivity
  refine ⟨by positivity, ?_, ?_⟩
  · simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (min_le_left 1 (N / (Real.sqrt M * Real.sqrt B * P))) hbase
  · apply (mul_le_mul_of_nonneg_left
      (min_le_right 1 (N / (Real.sqrt M * Real.sqrt B * P))) hbase).trans
    apply le_of_eq
    have hm := Real.sq_sqrt hM.le
    have hp := Real.sq_sqrt hP.le
    have hsm : Real.sqrt M ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hM)
    have hsb : Real.sqrt B ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hB)
    have hsp : Real.sqrt P ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hP)
    field_simp
    nlinarith

theorem quadratic_comparison_envelope {M N B P Y : ℝ}
    (hM : 0 < M) (hN : 0 < N) (hB : 0 < B) (hP : 1 ≤ P) (hY : 0 ≤ Y) :
    (M / N * Real.sqrt P * min 1 (N / (Real.sqrt M * Real.sqrt B * P))) *
      (Y + Real.sqrt (Y * N) + N / Real.sqrt P) ≤
        2 * (M + Real.sqrt M / Real.sqrt B * Y) := by
  have hP₀ : 0 < P := lt_of_lt_of_le zero_lt_one hP
  let S := M / N * Real.sqrt P * min 1 (N / (Real.sqrt M * Real.sqrt B * P))
  let A := Real.sqrt M / Real.sqrt B * Y
  obtain ⟨hS, hS₁, hS₂⟩ := quadratic_comparison_prefactor hM hN hB hP₀
  change 0 ≤ S at hS
  change S ≤ M / N * Real.sqrt P at hS₁
  change S ≤ Real.sqrt M / (Real.sqrt B * Real.sqrt P) at hS₂
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hsp : Real.sqrt P ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hP₀)
  have hsb : Real.sqrt B ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hB)
  have hsp₁ : 1 ≤ Real.sqrt P := (Real.le_sqrt (by norm_num) hP₀.le).2 (by simpa using hP)
  have hfirst : S * Y ≤ A := by
    apply (mul_le_mul_of_nonneg_right hS₂ hY).trans
    dsimp only [A]
    apply mul_le_mul_of_nonneg_right _ hY
    exact div_le_div_of_nonneg_left (Real.sqrt_nonneg M) (Real.sqrt_pos.2 hB)
      (by nlinarith [Real.sqrt_nonneg B])
  have hthird : S * (N / Real.sqrt P) ≤ M := by
    apply (mul_le_mul_of_nonneg_right hS₁ (by positivity)).trans
    apply le_of_eq
    field_simp
  have hSsq : S ^ 2 ≤ (M / N * Real.sqrt P) *
      (Real.sqrt M / (Real.sqrt B * Real.sqrt P)) := by
    simpa only [pow_two] using mul_le_mul hS₁ hS₂ hS (by positivity)
  have hcrosssq : (S * Real.sqrt (Y * N)) ^ 2 ≤ M * A := by
    calc
      _ = S ^ 2 * (Y * N) := by rw [mul_pow, Real.sq_sqrt (mul_nonneg hY hN.le)]
      _ ≤ ((M / N * Real.sqrt P) *
          (Real.sqrt M / (Real.sqrt B * Real.sqrt P))) * (Y * N) :=
        mul_le_mul_of_nonneg_right hSsq (mul_nonneg hY hN.le)
      _ = M * A := by dsimp [A]; field_simp
  have hcross : S * Real.sqrt (Y * N) ≤ (M + A) / 2 := by
    have hc : 0 ≤ S * Real.sqrt (Y * N) := mul_nonneg hS (Real.sqrt_nonneg _)
    nlinarith [sq_nonneg (M - A)]
  change S * (Y + Real.sqrt (Y * N) + N / Real.sqrt P) ≤ 2 * (M + A)
  nlinarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticDivisorDyadicPartition
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Disjoint divisor blocks, including the divisor-one boundary -/

namespace Ostmann

open scoped Classical BigOperators

theorem quadraticDivisorDyadicBlock_subset (Q j : ℕ) :
    quadraticDivisorDyadicBlock Q j ⊆ Finset.Ioc (2 ^ j) (2 * 2 ^ j) := by
  intro d hd
  obtain ⟨hd, hj⟩ := Finset.mem_filter.mp hd
  have hd₂ := (Finset.mem_Icc.mp hd).1
  have hn : d - 1 ≠ 0 := by omega
  have hlo := Nat.pow_log_le_self 2 hn
  have hhi := Nat.lt_pow_succ_log_self (by decide : 1 < 2) (d - 1)
  rw [hj] at hlo hhi
  rw [pow_succ] at hhi
  apply Finset.mem_Ioc.mpr
  omega

theorem quadratic_divisor_dyadic_sum {R : Type*} [AddCommMonoid R] (Q : ℕ) (F : ℕ → R) :
    (∑ j ∈ Finset.range (Nat.log 2 Q + 1),
      ∑ d ∈ quadraticDivisorDyadicBlock Q j, F d) = ∑ d ∈ Finset.Icc 2 Q, F d := by
  simp only [quadraticDivisorDyadicBlock, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  have hle : Nat.log 2 (d - 1) < Nat.log 2 Q + 1 := by
    have hh := Nat.log_mono_right (b := 2)
      (show d - 1 ≤ Q by have := (Finset.mem_Icc.mp hd).2; omega)
    omega
  simp only [Finset.sum_ite_eq, Finset.mem_range, hle, ite_true, if_true]

theorem quadratic_divisor_sum_one_blocks {R : Type*} [AddCommMonoid R]
    {Q : ℕ} (hQ : 1 ≤ Q) (F : ℕ → R) :
    (∑ d ∈ Finset.Icc 1 Q, F d) = F 1 +
      ∑ j ∈ Finset.range (Nat.log 2 Q + 1), ∑ d ∈ quadraticDivisorDyadicBlock Q j, F d := by
  rw [quadratic_divisor_dyadic_sum]
  have hmem : 1 ∈ Finset.Icc 1 Q := Finset.mem_Icc.mpr ⟨le_rfl, hQ⟩
  have heq : (Finset.Icc 1 Q).erase 1 = Finset.Icc 2 Q := by
    ext d
    simp only [Finset.mem_erase, Finset.mem_Icc]
    omega
  rw [← heq, Finset.add_sum_erase _ _ hmem]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticCorrectionBlocks
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact correction blocks retain the joint frequency sums -/

namespace Ostmann

open scoped Classical BigOperators

theorem quadraticDivisorDyadicBlock_eq_filter (Q j : ℕ) :
    quadraticDivisorDyadicBlock Q j =
      (Finset.Ioc (2 ^ j) (2 * 2 ^ j)).filter (fun d => d ≤ Q) := by
  classical
  ext d
  constructor
  · intro hd
    exact Finset.mem_filter.mpr ⟨quadraticDivisorDyadicBlock_subset Q j hd,
      (Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1).2⟩
  · intro hd
    obtain ⟨hd, hQ⟩ := Finset.mem_filter.mp hd
    obtain ⟨hlo, hhi⟩ := Finset.mem_Ioc.mp hd
    have hp : 1 ≤ (2 : ℕ) ^ j := one_le_pow₀ (by norm_num)
    have hl : 2 ^ j ≤ d - 1 := by omega
    have hu : d - 1 < 2 ^ (j + 1) := by rw [pow_succ]; omega
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, hQ⟩,
      Nat.log_eq_of_pow_le_of_lt_pow hl hu⟩

theorem quadratic_correction_divisor_sum {Q : ℕ} (hQ : 1 ≤ Q) (F : ℕ → ℂ) :
    (∑ d ∈ Finset.Icc 1 Q, F d) = F 1 +
      ∑ j ∈ Finset.range (Nat.log 2 Q + 1),
        ∑ d ∈ Finset.Ioc (2 ^ j) (2 * 2 ^ j), if d ≤ Q then F d else 0 := by
  rw [quadratic_divisor_sum_one_blocks hQ]
  simp_rw [quadraticDivisorDyadicBlock_eq_filter, Finset.sum_filter]

theorem quadratic_correction_divisor_bound {Q : ℕ} (hQ : 1 ≤ Q)
    (F : ℕ → ℂ) (A : ℝ) (T : ℕ → ℝ) (hunit : ‖F 1‖ ≤ A)
    (hblock : ∀ j < Nat.log 2 Q + 1,
      ‖∑ d ∈ Finset.Ioc (2 ^ j) (2 * 2 ^ j), if d ≤ Q then F d else 0‖ ≤ T j) :
    ‖∑ d ∈ Finset.Icc 1 Q, F d‖ ≤ A + ∑ j ∈ Finset.range (Nat.log 2 Q + 1), T j := by
  rw [quadratic_correction_divisor_sum hQ]
  apply (norm_add_le _ _).trans
  exact add_le_add hunit ((norm_sum_le _ _).trans
    (Finset.sum_le_sum fun j hj => hblock j (Finset.mem_range.mp hj)))

theorem quadraticDyadicDivisors_eq_filter (K j : ℕ) :
    quadraticDyadicDivisors K j = (oddSquarefreeRange (2 * 2 ^ j)).filter
      (fun b => 2 ^ j ≤ b ∧ b ≤ K ∧ b < 2 * 2 ^ j) := by
  classical
  ext b
  constructor
  · intro hb
    have hbounds := quadraticDyadicDivisors_bounds hb
    obtain ⟨hb, _⟩ := Finset.mem_filter.mp hb
    obtain ⟨hr, ho, hsf⟩ := Finset.mem_filter.mp hb
    rw [pow_succ] at hbounds
    refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hr).1, by omega⟩, ho, hsf⟩,
      hbounds.1, (Finset.mem_Icc.mp hr).2, ?_⟩
    omega
  · intro hb
    obtain ⟨hb, hlo, hK, hhi⟩ := Finset.mem_filter.mp hb
    obtain ⟨hr, ho, hsf⟩ := Finset.mem_filter.mp hb
    refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hr).1, hK⟩, ho, hsf⟩, ?_⟩
    apply Nat.log_eq_of_pow_le_of_lt_pow hlo
    rw [pow_succ]
    omega

theorem quadratic_correction_frequency_sum (K : ℕ) (F : ℕ → ℂ) :
    (∑ b ∈ oddSquarefreeRange K, F b) =
      ∑ j ∈ Finset.range (Nat.log 2 K + 1), ∑ b ∈ oddSquarefreeRange (2 * 2 ^ j),
        if 2 ^ j ≤ b ∧ b ≤ K ∧ b < 2 * 2 ^ j then F b else 0 := by
  rw [← quadratic_dyadic_divisors_sum K F]
  simp_rw [quadraticDyadicDivisors_eq_filter, Finset.sum_filter]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticGaussCRT
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Factoring the actual quadratic Gauss coefficient over coprime denominators -/

namespace Ostmann

open scoped Classical BigOperators

 theorem jacobiComplex_crt {m n : ℕ} [NeZero m] [NeZero n]
    (h : m.Coprime n) (x : ZMod (m * n)) :
    jacobiComplex (m * n) x =
      jacobiComplex m ((ZMod.chineseRemainder h) x).1 *
      jacobiComplex n ((ZMod.chineseRemainder h) x).2 := by
  obtain ⟨z, rfl⟩ := ZMod.intCast_surjective x
  have he : (ZMod.chineseRemainder h) (z : ZMod (m * n)) =
      ((z : ZMod m), (z : ZMod n)) := map_intCast (ZMod.chineseRemainder h) z
  rw [he]
  change jacobiComplex (m * n) (z : ZMod (m * n)) =
    jacobiComplex m (z : ZMod m) * jacobiComplex n (z : ZMod n)
  rw [jacobiComplex_intCast, jacobiComplex_intCast, jacobiComplex_intCast,
    jacobiSym.mul_right' z (NeZero.ne m) (NeZero.ne n)]
  push_cast
  rfl

 theorem jacobiComplex_inv_unit (m : ℕ) [NeZero m] (x : ZMod m) (hx : IsUnit x) :
    jacobiComplex m x⁻¹ = jacobiComplex m x := by
  have hmul : jacobiComplex m x * jacobiComplex m x⁻¹ = 1 := by
    rw [← map_mul, ZMod.mul_inv_of_unit x hx, map_one]
  have hsq : jacobiComplex m x * jacobiComplex m x = 1 := by
    have hh := congrArg (fun χ : DirichletCharacter ℂ m => χ x)
      (jacobiComplex_isQuadratic m).sq_eq_one
    simpa only [pow_two, MulChar.coeToFun_mul, Pi.mul_apply, MulChar.one_apply hx] using hh
  exact mul_left_cancel₀ (IsUnit.ne_zero (hx.map (jacobiComplex m))) (hmul.trans hsq.symm)

 theorem quadratic_gauss_crt {m n : ℕ} [NeZero m] [NeZero n]
    (h : m.Coprime n) (hm : Squarefree m) (hn : Squarefree n)
    (hom : Odd m) (hon : Odd n) :
    gaussSum (jacobiComplex (m * n)) ZMod.stdAddChar =
      jacobiComplex m (n : ZMod m) * jacobiComplex n (m : ZMod n) *
        gaussSum (jacobiComplex m) ZMod.stdAddChar *
        gaussSum (jacobiComplex n) ZMod.stdAddChar := by
  have hp := additiveFourier_crt h (jacobiComplex m) (jacobiComplex n) (-1)
  have heq : (fun x : ZMod (m * n) =>
      jacobiComplex m ((ZMod.chineseRemainder h) x).1 *
      jacobiComplex n ((ZMod.chineseRemainder h) x).2) = jacobiComplex (m * n) :=
    funext (fun x => (jacobiComplex_crt h x).symm)
  rw [heq, primitive_character_fourier _
      (jacobiComplex_squarefree_primitive (m * n) ((Nat.squarefree_mul h).mpr ⟨hm, hn⟩)
        (hom.mul hon)),
    primitive_character_fourier _ (jacobiComplex_squarefree_primitive m hm hom),
    primitive_character_fourier _ (jacobiComplex_squarefree_primitive n hn hon),
    (jacobiComplex_isQuadratic (m * n)).inv,
    (jacobiComplex_isQuadratic m).inv, (jacobiComplex_isQuadratic n).inv] at hp
  simp only [map_neg, map_one, Prod.fst_neg, Prod.snd_neg, Prod.fst_one, Prod.snd_one,
    mul_neg, mul_one, neg_neg] at hp
  rw [jacobiComplex_inv_unit m _ ((ZMod.isUnit_iff_coprime n m).mpr h.symm),
    jacobiComplex_inv_unit n _ ((ZMod.isUnit_iff_coprime m n).mpr h)] at hp
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne m
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne n
  push_cast at hp
  field_simp [hm0, hn0] at hp
  linear_combination hp

 theorem quadratic_gauss_phase_crt {m n : ℕ} [NeZero m] [NeZero n]
    (h : m.Coprime n) (hm : Squarefree m) (hn : Squarefree n)
    (hom : Odd m) (hon : Odd n) :
    jacobiGaussPhase (m * n) =
      jacobiComplex m (n : ZMod m) * jacobiComplex n (m : ZMod n) *
        jacobiGaussPhase m * jacobiGaussPhase n := by
  unfold jacobiGaussPhase
  rw [quadratic_gauss_crt h hm hn hom hon, Nat.cast_mul,
    Real.sqrt_mul (Nat.cast_nonneg m), Complex.ofReal_mul]
  ring

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

 theorem quadratic_jacobi_reciprocity_sign {m n : ℕ} [NeZero m] [NeZero n]
    (h : m.Coprime n) (hm : Odd m) (hn : Odd n) :
    jacobiComplex m (n : ZMod m) * jacobiComplex n (m : ZMod n) =
      if m % 4 = 3 ∧ n % 4 = 3 then (-1 : ℂ) else 1 := by
  have hc₁ : jacobiComplex m (n : ZMod m) = (jacobiSym (n : ℤ) m : ℂ) := by
    simpa only [Int.cast_natCast] using jacobiComplex_intCast m (n : ℤ)
  have hc₂ : jacobiComplex n (m : ZMod n) = (jacobiSym (m : ℤ) n : ℂ) := by
    simpa only [Int.cast_natCast] using jacobiComplex_intCast n (m : ℤ)
  rw [hc₁, hc₂, ← Int.cast_mul]
  have hs : jacobiSym (n : ℤ) m ^ 2 = 1 := jacobiSym.sq_one (by exact h.symm)
  by_cases hm3 : m % 4 = 3
  · by_cases hn3 : n % 4 = 3
    · rw [ite_eq_left ⟨hm3, hn3⟩,
        jacobiSym.quadratic_reciprocity_three_mod_four hm3 hn3]
      have hh : jacobiSym (n : ℤ) m * -jacobiSym (n : ℤ) m = -1 := by nlinarith
      rw [hh, Int.cast_neg, Int.cast_one]
    · have hn1 : n % 4 = 1 := by
        obtain hn1 | hn3' := Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hn)
        · exact hn1
        · exact (hn3 hn3').elim
      rw [ite_eq_right (fun hh => hn3 hh.2),
        jacobiSym.quadratic_reciprocity_one_mod_four' hm hn1, ← pow_two, hs, Int.cast_one]
  · have hm1 : m % 4 = 1 := by
      obtain hm1 | hm3' := Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hm)
      · exact hm1
      · exact (hm3 hm3').elim
    rw [ite_eq_right (fun hh => hm3 hh.1),
      jacobiSym.quadratic_reciprocity_one_mod_four hm1 hn, ← pow_two, hs, Int.cast_one]

 theorem quadraticGaussMultiplier_mul {m n : ℕ} (h : m.Coprime n)
    (hm : Squarefree m) (hn : Squarefree n) (hom : Odd m) (hon : Odd n) :
    quadraticGaussMultiplier (m * n) =
      (if m % 4 = 3 ∧ n % 4 = 3 then (-1 : ℂ) else 1) *
        quadraticGaussMultiplier m * quadraticGaussMultiplier n := by
  let : NeZero m := ⟨hm.ne_zero⟩
  let : NeZero n := ⟨hn.ne_zero⟩
  rw [quadraticGaussMultiplier, dite_eq_right (mul_ne_zero hm.ne_zero hn.ne_zero),
    quadraticGaussMultiplier, dite_eq_right hm.ne_zero,
    quadraticGaussMultiplier, dite_eq_right hn.ne_zero,
    quadratic_gauss_phase_crt h hm hn hom hon, quadratic_jacobi_reciprocity_sign h hom hon]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticGaussBilinear
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Separating the Gauss factor in the actual divisor bilinear sum -/

namespace Ostmann

open scoped Classical BigOperators ComplexConjugate

 theorem quadraticGaussLeft_norm {N n : ℕ} (hn : n ∈ oddSquarefreeRange N)
    (a : ℕ → ℂ) : ‖quadraticGaussLeft a n‖ = ‖a n‖ := by
  obtain ⟨_, ho, hs⟩ := Finset.mem_filter.mp hn
  rw [quadraticGaussLeft, norm_mul, quadraticGaussMultiplier_norm hs ho, mul_one]

 theorem quadraticGaussRight_norm {N n : ℕ} (hn : n ∈ oddSquarefreeRange N)
    (b : ℕ → ℂ) : ‖quadraticGaussRight b n‖ = ‖b n‖ := by
  obtain ⟨_, ho, hs⟩ := Finset.mem_filter.mp hn
  rw [quadraticGaussRight, norm_mul, Complex.norm_conj,
    quadraticGaussMultiplier_norm hs ho, mul_one]

 theorem quadraticDivisorMoment_gaussLeft (N : ℕ) (a : ℕ → ℂ) :
    quadraticDivisorMoment N (quadraticGaussLeft a) = quadraticDivisorMoment N a := by
  apply Finset.sum_congr rfl
  intro n hn
  rw [quadraticGaussLeft_norm hn]

 theorem quadraticDivisorMoment_gaussRight (N : ℕ) (b : ℕ → ℂ) :
    quadraticDivisorMoment N (quadraticGaussRight b) = quadraticDivisorMoment N b := by
  apply Finset.sum_congr rfl
  intro n hn
  rw [quadraticGaussRight_norm hn]

 theorem quadraticDivisorMoment_threeClass (N : ℕ) (a : ℕ → ℂ) :
    quadraticDivisorMoment N (quadraticThreeClass a) ≤ quadraticDivisorMoment N a := by
  apply Finset.sum_le_sum
  intro n _
  unfold quadraticThreeClass
  split_ifs
  · rfl
  · simp only [norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero]
    positivity

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticFourierSeparation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact logarithmic Fourier separation of a smooth pair weight -/

namespace Ostmann

open MeasureTheory
open scoped Classical BigOperators SchwartzMap FourierTransform ComplexConjugate

 theorem quadratic_schwartz_inversion (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    f x = ∫ u : ℝ, realAdditivePhase (u * x) * 𝓕 f u := by
  have hi := congrArg (fun g : 𝓢(ℝ, ℂ) => g x)
    (show (𝓕⁻ (𝓕 f : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ)) = f from
      FourierTransform.fourierInv_fourier_eq f)
  rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq_fourier_neg,
    Real.fourier_real_eq_integral_exp_smul] at hi
  rw [← hi]
  apply integral_congr_ae
  filter_upwards with u
  congr 1
  unfold realAdditivePhase
  congr 1
  push_cast
  ring

 theorem quadratic_log_pair_integrable (f : 𝓢(ℝ, ℂ)) (c : ℂ) (s t : ℕ) :
    Integrable (fun u : ℝ => c * realAdditivePhase (u * Real.log s) *
      realAdditivePhase (u * Real.log t) * 𝓕 f u) := by
  apply (((𝓕 f : 𝓢(ℝ, ℂ)).integrable.norm).const_mul ‖c‖).mono'
    (by unfold realAdditivePhase; fun_prop)
  filter_upwards with u
  simp only [norm_mul, norm_realAdditivePhase, mul_one, le_refl]

 theorem quadratic_finite_log_separation (f : 𝓢(ℝ, ℂ)) (S T : Finset ℕ)
    (c : ℕ → ℕ → ℂ) :
    (∑ s ∈ S, ∑ t ∈ T, c s t * f (Real.log s + Real.log t)) =
      ∫ u : ℝ, 𝓕 f u * ∑ s ∈ S, ∑ t ∈ T,
        c s t * realAdditivePhase (u * Real.log s) *
          realAdditivePhase (u * Real.log t) := by
  have ht (s t : ℕ) : c s t * f (Real.log s + Real.log t) =
      ∫ u : ℝ, c s t * realAdditivePhase (u * Real.log s) *
        realAdditivePhase (u * Real.log t) * 𝓕 f u := by
    rw [quadratic_schwartz_inversion, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with u
    rw [mul_add, realAdditivePhase_add]
    ring
  simp_rw [ht]
  calc
    _ = ∑ s ∈ S, ∫ u : ℝ, ∑ t ∈ T,
        c s t * realAdditivePhase (u * Real.log s) *
          realAdditivePhase (u * Real.log t) * 𝓕 f u := by
      apply Finset.sum_congr rfl
      intro s _
      exact (integral_finsetSum T
        (fun t _ => quadratic_log_pair_integrable f (c s t) s t)).symm
    _ = ∫ u : ℝ, ∑ s ∈ S, ∑ t ∈ T,
        c s t * realAdditivePhase (u * Real.log s) *
          realAdditivePhase (u * Real.log t) * 𝓕 f u :=
      (integral_finsetSum S (fun s _ =>
        integrable_finsetSum T (fun t _ => quadratic_log_pair_integrable f (c s t) s t))).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with u
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t _
      ring

 theorem quadraticLogModulate_norm (u : ℝ) (a : ℕ → ℂ) (n : ℕ) :
    ‖quadraticLogModulate u a n‖ = ‖a n‖ := by
  rw [quadraticLogModulate, norm_mul, norm_realAdditivePhase, mul_one]

 theorem quadraticDivisorMoment_logModulate (N : ℕ) (u : ℝ) (a : ℕ → ℂ) :
    quadraticDivisorMoment N (quadraticLogModulate u a) = quadraticDivisorMoment N a := by
  apply Finset.sum_congr rfl
  intro n _
  rw [quadraticLogModulate_norm]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticWeightedBilinear
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Smooth logarithmic weights in the literal divisor bilinear form -/

namespace Ostmann

open MeasureTheory
open scoped Classical BigOperators SchwartzMap FourierTransform ComplexConjugate

 theorem quadratic_log_modulated_bilinear (N₁ N₂ d : ℕ) (a b : ℕ → ℂ) (m : ℤ) (u : ℝ) :
    quadraticDivisorBilinear N₁ N₂ d (quadraticLogModulate u a) (quadraticLogModulate (-u) b) m =
    ∑ s ∈ oddSquarefreeRange N₁, ∑ t ∈ oddSquarefreeRange N₂,
      ((if s.Coprime t ∧ d ∣ s * t then (1 : ℂ) else 0) *
        a s * conj (b t) * (jacobiSym m s : ℂ) * (jacobiSym m t : ℂ)) *
        realAdditivePhase (u * Real.log s) * realAdditivePhase (u * Real.log t) := by
  unfold quadraticDivisorBilinear quadraticLogModulate
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro t _
  simp only [map_mul, conj_realAdditivePhase, neg_mul, neg_neg]
  ring

 theorem quadratic_log_weighted_separation (f : 𝓢(ℝ, ℂ)) (N₁ N₂ d : ℕ)
    (a b : ℕ → ℂ) (m : ℤ) :
    quadraticLogWeightedDivisor f N₁ N₂ d a b m =
      ∫ u : ℝ, 𝓕 f u * quadraticDivisorBilinear N₁ N₂ d
        (quadraticLogModulate u a) (quadraticLogModulate (-u) b) m := by
  unfold quadraticLogWeightedDivisor
  rw [quadratic_finite_log_separation]
  apply integral_congr_ae
  filter_upwards with u
  rw [quadratic_log_modulated_bilinear]

 theorem quadratic_log_integrand_integrable (f : 𝓢(ℝ, ℂ)) (N₁ N₂ d : ℕ)
    (a b : ℕ → ℂ) (m : ℤ) :
    Integrable (fun u : ℝ => 𝓕 f u * quadraticDivisorBilinear N₁ N₂ d
      (quadraticLogModulate u a) (quadraticLogModulate (-u) b) m) := by
  have hi := integrable_finsetSum (oddSquarefreeRange N₁) (fun s _ =>
    integrable_finsetSum (oddSquarefreeRange N₂) (fun t _ =>
      quadratic_log_pair_integrable f
        ((if s.Coprime t ∧ d ∣ s * t then (1 : ℂ) else 0) *
          a s * conj (b t) * (jacobiSym m s : ℂ) * (jacobiSym m t : ℂ)) s t))
  apply hi.congr
  filter_upwards with u
  rw [quadratic_log_modulated_bilinear, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  ring

 theorem quadratic_log_weighted_norm (f : 𝓢(ℝ, ℂ)) (N₁ N₂ d : ℕ)
    (a b : ℕ → ℂ) (m : ℤ) :
    ‖quadraticLogWeightedDivisor f N₁ N₂ d a b m‖ ≤
      ∫ u : ℝ, ‖𝓕 f u‖ * ‖quadraticDivisorBilinear N₁ N₂ d
        (quadraticLogModulate u a) (quadraticLogModulate (-u) b) m‖ := by
  rw [quadratic_log_weighted_separation]
  simpa only [norm_mul] using norm_integral_le_integral_norm
    (fun u : ℝ => 𝓕 f u * quadraticDivisorBilinear N₁ N₂ d
      (quadraticLogModulate u a) (quadraticLogModulate (-u) b) m)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticUniformBilinear
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A uniform bound over the finitely many actual divisor scales -/

namespace Ostmann

open scoped Classical BigOperators

 theorem quadratic_bilinear_uniform_bound (M N₁ N₂ D : ℕ) (a b : ℕ → ℂ)
    (K₁ K₂ : ℕ → ℝ) (T : ℝ) (hT : 0 ≤ T)
    (hK₁ : ∀ i ≤ Nat.log 2 N₁, 0 ≤ K₁ i)
    (hK₂ : ∀ j ≤ Nat.log 2 N₂, 0 ≤ K₂ j)
    (h₁ : ∀ i ≤ Nat.log 2 N₁, QuadraticSieveBound M (N₁ / 2 ^ i) (K₁ i))
    (h₂ : ∀ j ≤ Nat.log 2 N₂, QuadraticSieveBound M (N₂ / 2 ^ j) (K₂ j))
    (hcost : ∀ i ≤ Nat.log 2 N₁, ∀ j ≤ Nat.log 2 N₂,
      D < 4 * (2 ^ i * 2 ^ j) → 2 ^ i * 2 ^ j ≤ 2 * D →
      Real.sqrt (2 * K₁ i * (2 ^ i : ℕ) * quadraticDivisorMoment N₁ a) *
        Real.sqrt (2 * K₂ j * (2 ^ j : ℕ) * quadraticDivisorMoment N₂ b) ≤ T) :
    (∑ d ∈ Finset.Ioc D (2 * D), ∑ m ∈ oddSquarefreeRange M,
      ‖quadraticDivisorBilinear N₁ N₂ d a b m‖) ≤
      ((Nat.log 2 N₁ + 1 : ℕ) : ℝ) * (Nat.log 2 N₂ + 1) * T := by
  by_cases hp : 0 < ∑ d ∈ Finset.Ioc D (2 * D), ∑ m ∈ oddSquarefreeRange M,
      ‖quadraticDivisorBilinear N₁ N₂ d a b m‖
  · obtain ⟨i, hi, j, hj, hD₁, hD₂, hb⟩ := quadratic_bilinear_comparison M N₁ N₂ D a b hp
    exact (hb (K₁ i) (K₂ j) (hK₁ i hi) (hK₂ j hj) (h₁ i hi) (h₂ j hj)).trans
      (mul_le_mul_of_nonneg_left (hcost i hi j hj hD₁ hD₂) (by positivity))
  · exact (le_of_not_gt hp).trans (by positivity)

 theorem quadratic_log_modulated_uniform_bound (M N₁ N₂ D : ℕ) (a b : ℕ → ℂ)
    (K₁ K₂ : ℕ → ℝ) (T : ℝ) (hT : 0 ≤ T)
    (hK₁ : ∀ i ≤ Nat.log 2 N₁, 0 ≤ K₁ i)
    (hK₂ : ∀ j ≤ Nat.log 2 N₂, 0 ≤ K₂ j)
    (h₁ : ∀ i ≤ Nat.log 2 N₁, QuadraticSieveBound M (N₁ / 2 ^ i) (K₁ i))
    (h₂ : ∀ j ≤ Nat.log 2 N₂, QuadraticSieveBound M (N₂ / 2 ^ j) (K₂ j))
    (hcost : ∀ i ≤ Nat.log 2 N₁, ∀ j ≤ Nat.log 2 N₂,
      D < 4 * (2 ^ i * 2 ^ j) → 2 ^ i * 2 ^ j ≤ 2 * D →
      Real.sqrt (2 * K₁ i * (2 ^ i : ℕ) * quadraticDivisorMoment N₁ a) *
        Real.sqrt (2 * K₂ j * (2 ^ j : ℕ) * quadraticDivisorMoment N₂ b) ≤ T)
    (u : ℝ) :
    (∑ d ∈ Finset.Ioc D (2 * D), ∑ m ∈ oddSquarefreeRange M,
      ‖quadraticDivisorBilinear N₁ N₂ d
        (quadraticLogModulate u a) (quadraticLogModulate (-u) b) m‖) ≤
      ((Nat.log 2 N₁ + 1 : ℕ) : ℝ) * (Nat.log 2 N₂ + 1) * T := by
  apply quadratic_bilinear_uniform_bound M N₁ N₂ D _ _ K₁ K₂ T hT hK₁ hK₂ h₁ h₂
  intro i hi j hj hD₁ hD₂
  rw [quadraticDivisorMoment_logModulate, quadraticDivisorMoment_logModulate]
  exact hcost i hi j hj hD₁ hD₂

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticLogKernel
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A concrete smooth logarithmic cutoff for the quadratic Poisson kernel -/

namespace Ostmann

open scoped SchwartzMap

 theorem quadraticLogWindow_apply (ρ : 𝓢(ℝ, ℂ)) (X u : ℝ) :
    quadraticLogWindow ρ X u = (quadraticLogBump u : ℂ) * ρ (X * Real.exp (-u)) := rfl

 theorem quadraticLogWindow_eq (ρ : 𝓢(ℝ, ℂ)) (X u : ℝ) (hu : |u| ≤ 2) :
    quadraticLogWindow ρ X u = ρ (X * Real.exp (-u)) := by
  have hb : quadraticLogBump u = 1 := quadraticLogBump.one_of_mem_closedBall (by
    simpa only [Metric.mem_closedBall, Real.dist_eq, sub_zero, quadraticLogBump] using hu)
  rw [quadraticLogWindow_apply, hb, Complex.ofReal_one, one_mul]

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

 theorem quadratic_fourier_translate_norm (f : 𝓢(ℝ, ℂ)) (a u : ℝ) :
    ‖𝓕 (f.compSubConstCLM ℂ a) u‖ = ‖𝓕 f u‖ := by
  rw [quadratic_fourier_translate, norm_mul, norm_realAdditivePhase, one_mul]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticFourierDerivative
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The second derivative controls the large Fourier frequencies -/

namespace Ostmann

open MeasureTheory LineDeriv
open scoped SchwartzMap FourierTransform

 theorem quadratic_fourier_line_derivative (f : 𝓢(ℝ, ℂ)) (u : ℝ) :
    𝓕 (∂_{(1 : ℝ)} f) u = (2 * Real.pi * Complex.I) * (u : ℂ) * 𝓕 f u := by
  have hh := congrArg (fun g : 𝓢(ℝ, ℂ) => g u)
    (SchwartzMap.fourier_lineDerivOp_eq f (1 : ℝ))
  have hg : (fun x : ℝ => inner ℝ x (1 : ℝ)).HasTemperateGrowth := by
    exact ((innerSL ℝ).flip (1 : ℝ)).hasTemperateGrowth
  change 𝓕 (∂_{(1 : ℝ)} f) u =
    (2 * Real.pi * Complex.I) *
      (SchwartzMap.smulLeftCLM ℂ (fun x : ℝ => inner ℝ x (1 : ℝ)) (𝓕 f)) u at hh
  rw [SchwartzMap.smulLeftCLM_apply_apply hg] at hh
  simpa [RCLike.inner_apply, Complex.real_smul, mul_assoc] using hh

 theorem quadratic_fourier_second_derivative (f : 𝓢(ℝ, ℂ)) (u : ℝ) :
    𝓕 (∂_{(1 : ℝ)} (∂_{(1 : ℝ)} f)) u =
      ((2 * Real.pi * Complex.I) * (u : ℂ)) ^ 2 * 𝓕 f u := by
  rw [quadratic_fourier_line_derivative, quadratic_fourier_line_derivative]
  ring

 theorem quadratic_fourier_second_derivative_norm (f : 𝓢(ℝ, ℂ)) (u : ℝ) :
    ‖𝓕 (∂_{(1 : ℝ)} (∂_{(1 : ℝ)} f)) u‖ =
      (2 * Real.pi) ^ 2 * u ^ 2 * ‖𝓕 f u‖ := by
  have hc : ‖(2 * Real.pi * Complex.I : ℂ)‖ = 2 * Real.pi := by
    rw [norm_mul, Complex.norm_I, mul_one]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    norm_num
  rw [quadratic_fourier_second_derivative, norm_mul, norm_pow, norm_mul, hc,
    Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticFourierL1
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A concrete Fourier L1 bound from two physical-space derivatives -/

namespace Ostmann

open MeasureTheory LineDeriv
open scoped SchwartzMap FourierTransform

 theorem quadratic_fourier_norm_le_integral (f : 𝓢(ℝ, ℂ)) (u : ℝ) :
    ‖𝓕 f u‖ ≤ ∫ x : ℝ, ‖f x‖ := by
  rw [quadratic_fourier_phase_integral]
  simpa only [norm_mul, norm_realAdditivePhase, one_mul] using
    norm_integral_le_integral_norm (fun x : ℝ => realAdditivePhase (-(x * u)) * f x)

 theorem quadratic_fourier_frequency_bound (f : 𝓢(ℝ, ℂ)) (u : ℝ) :
    u ^ 2 * ‖𝓕 f u‖ ≤
      (∫ x : ℝ, ‖(∂_{(1 : ℝ)} (∂_{(1 : ℝ)} f)) x‖) / (2 * Real.pi) ^ 2 := by
  have hp : 0 < (2 * Real.pi) ^ 2 := by positivity
  apply (le_div_iff₀ hp).mpr
  have hh := quadratic_fourier_norm_le_integral (∂_{(1 : ℝ)} (∂_{(1 : ℝ)} f)) u
  rw [quadratic_fourier_second_derivative_norm] at hh
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticLogDerivative
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Explicit derivatives of the compact logarithmic Poisson cutoff -/

namespace Ostmann

open LineDeriv
open scoped SchwartzMap

 theorem quadraticSmoothLogCutoff_apply (u : ℝ) :
    quadraticSmoothLogCutoff u = (quadraticLogBump u : ℂ) := rfl

 theorem quadraticEulerDerivative_apply (ρ : 𝓢(ℝ, ℂ)) (x : ℝ) :
    quadraticEulerDerivative ρ x = (x : ℂ) * deriv ρ x := by
  rw [quadraticEulerDerivative, SchwartzMap.smulLeftCLM_apply_apply (by fun_prop),
    SchwartzMap.derivCLM_apply, Complex.real_smul]

 theorem quadratic_log_composition_derivative (ρ : 𝓢(ℝ, ℂ)) (X u : ℝ) :
    HasDerivAt (fun v : ℝ => ρ (X * Real.exp (-v)))
      (-quadraticEulerDerivative ρ (X * Real.exp (-u))) u := by
  have he : HasDerivAt (fun v : ℝ => X * Real.exp (-v))
      (-(X * Real.exp (-u))) u := by
    simpa only [Pi.neg_apply, id_eq, neg_mul, mul_neg, mul_one] using
      (((hasDerivAt_id u).neg.exp).const_mul X)
  have hh := (ρ.hasDerivAt (X * Real.exp (-u))).scomp u he
  simpa only [Function.comp_def, quadraticEulerDerivative_apply, Complex.real_smul,
    Complex.ofReal_neg, neg_mul] using hh

 theorem quadratic_line_derivative_one (f : 𝓢(ℝ, ℂ)) :
    ∂_{(1 : ℝ)} f = SchwartzMap.derivCLM ℂ ℂ f := by
  ext x
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv, SchwartzMap.derivCLM_apply,
    fderiv_apply_one_eq_deriv]

 theorem quadraticLogWindow_hasDerivAt (ρ : 𝓢(ℝ, ℂ)) (X u : ℝ) :
    HasDerivAt (quadraticLogWindow ρ X) (quadraticLogFirst ρ X u) u := by
  have hh := (quadraticSmoothLogCutoff.hasDerivAt u).mul
    (quadratic_log_composition_derivative ρ X u)
  change HasDerivAt (fun v => quadraticSmoothLogCutoff v * ρ (X * Real.exp (-v)))
    (quadraticLogFirst ρ X u) u
  simpa only [Pi.mul_def, quadraticLogFirst,
    SchwartzMap.derivCLM_apply, quadraticSmoothLogCutoff_apply, mul_neg,
    sub_eq_add_neg] using hh

 theorem quadraticLogWindow_deriv (ρ : 𝓢(ℝ, ℂ)) (X : ℝ) :
    (fun u => deriv (quadraticLogWindow ρ X) u) = quadraticLogFirst ρ X := by
  funext u
  exact (quadraticLogWindow_hasDerivAt ρ X u).deriv

 theorem quadraticLogWindow_second (ρ : 𝓢(ℝ, ℂ)) (X u : ℝ) :
    (∂_{(1 : ℝ)} (∂_{(1 : ℝ)} (quadraticLogWindow ρ X))) u =
      (SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.derivCLM ℂ ℂ
        quadraticSmoothLogCutoff)) u * ρ (X * Real.exp (-u)) -
      2 * (SchwartzMap.derivCLM ℂ ℂ quadraticSmoothLogCutoff) u *
        quadraticEulerDerivative ρ (X * Real.exp (-u)) +
      quadraticSmoothLogCutoff u *
        quadraticEulerDerivative (quadraticEulerDerivative ρ) (X * Real.exp (-u)) := by
  have h₁ := ((SchwartzMap.derivCLM ℂ ℂ quadraticSmoothLogCutoff).hasDerivAt u).mul
    (quadratic_log_composition_derivative ρ X u)
  have h₂ := (quadraticSmoothLogCutoff.hasDerivAt u).mul
    (quadratic_log_composition_derivative (quadraticEulerDerivative ρ) X u)
  have hh := h₁.sub h₂
  have he : HasDerivAt (quadraticLogFirst ρ X)
      ((SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.derivCLM ℂ ℂ
        quadraticSmoothLogCutoff)) u * ρ (X * Real.exp (-u)) -
      2 * (SchwartzMap.derivCLM ℂ ℂ quadraticSmoothLogCutoff) u *
        quadraticEulerDerivative ρ (X * Real.exp (-u)) +
      quadraticSmoothLogCutoff u *
        quadraticEulerDerivative (quadraticEulerDerivative ρ) (X * Real.exp (-u))) u := by
    refine hh.congr_deriv ?_
    · simp only [SchwartzMap.derivCLM_apply]
      ring
  rw [quadratic_line_derivative_one, quadratic_line_derivative_one,
    SchwartzMap.derivCLM_apply]
  change deriv (fun v => deriv (quadraticLogWindow ρ X) v) u = _
  rw [quadraticLogWindow_deriv]
  exact he.deriv

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticLogDecay
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform Schwartz decay on the compact logarithmic window -/

namespace Ostmann

open MeasureTheory
open scoped SchwartzMap

 theorem quadraticLogDecayConstant_nonneg (ρ : 𝓢(ℝ, ℂ)) (A : ℕ) :
    0 ≤ quadraticLogDecayConstant ρ A := by
  unfold quadraticLogDecayConstant
  positivity

 theorem quadratic_log_value_decay (ρ : 𝓢(ℝ, ℂ)) (A : ℕ)
    {X u : ℝ} (hX : 0 < X) (hu : u ≤ 3) :
    ‖ρ (X * Real.exp (-u))‖ ≤ quadraticLogDecayConstant ρ A / X ^ A := by
  have hy : 0 < X * Real.exp (-u) := mul_pos hX (Real.exp_pos _)
  have hs := SchwartzMap.norm_pow_mul_le_seminorm ℝ ρ A (X * Real.exp (-u))
  rw [Real.norm_eq_abs, abs_of_pos hy] at hs
  have he : X = (X * Real.exp (-u)) * Real.exp u := by
    rw [mul_assoc, ← Real.exp_add]
    simp
  apply (le_div_iff₀ (pow_pos hX A)).mpr
  calc
    _ = Real.exp u ^ A * ((X * Real.exp (-u)) ^ A * ‖ρ (X * Real.exp (-u))‖) := by
      calc
        _ = ‖ρ (X * Real.exp (-u))‖ * ((X * Real.exp (-u)) * Real.exp u) ^ A :=
          congrArg (fun z : ℝ => ‖ρ (X * Real.exp (-u))‖ * z ^ A) he
        _ = _ := by rw [mul_pow]; ring
    _ ≤ Real.exp 3 ^ A * SchwartzMap.seminorm ℝ A 0 ρ := by
      apply mul_le_mul
      · exact pow_le_pow_left₀ (Real.exp_nonneg _) (Real.exp_le_exp.mpr hu) A
      · exact hs
      · positivity
      · positivity
    _ = _ := rfl

 theorem quadratic_log_product_decay (B ρ : 𝓢(ℝ, ℂ)) (A : ℕ)
    (hB : tsupport B ⊆ Set.Icc (-3 : ℝ) 3) {X : ℝ} (hX : 0 < X) (u : ℝ) :
    ‖B u * ρ (X * Real.exp (-u))‖ ≤
      (quadraticLogDecayConstant ρ A / X ^ A) * ‖B u‖ := by
  by_cases hb : B u = 0
  · simp [hb]
  · have hu : u ∈ tsupport B := subset_tsupport B hb
    rw [norm_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right
      (quadratic_log_value_decay ρ A hX (hB hu).2) (norm_nonneg _)

 theorem quadratic_log_product_integral (B ρ : 𝓢(ℝ, ℂ)) (A : ℕ)
    (hB : tsupport B ⊆ Set.Icc (-3 : ℝ) 3) {X : ℝ} (hX : 0 < X) :
    (∫ u : ℝ, ‖B u * ρ (X * Real.exp (-u))‖) ≤
      (quadraticLogDecayConstant ρ A / X ^ A) * ∫ u : ℝ, ‖B u‖ := by
  calc
    _ ≤ ∫ u : ℝ, (quadraticLogDecayConstant ρ A / X ^ A) * ‖B u‖ :=
      integral_mono_of_nonneg (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
        (B.integrable.norm.const_mul _) (Filter.Eventually.of_forall
          (quadratic_log_product_decay B ρ A hB hX))
    _ = _ := integral_const_mul _ _

 theorem quadraticSmoothLogCutoff_support :
    tsupport quadraticSmoothLogCutoff ⊆ Set.Icc (-3 : ℝ) 3 := by
  intro u hu
  have hs : tsupport quadraticSmoothLogCutoff ⊆ tsupport quadraticLogBump :=
    tsupport_comp_subset (g := Complex.ofReal) (by simp) quadraticLogBump
  have hh := hs hu
  rw [quadraticLogBump.tsupport_eq] at hh
  have ha : |u| ≤ 3 := by
    simpa only [quadraticLogBump, Metric.mem_closedBall, Real.dist_eq, sub_zero] using hh
  exact abs_le.mp ha

 theorem quadraticSmoothLogCutoff_deriv_support :
    tsupport (SchwartzMap.derivCLM ℂ ℂ quadraticSmoothLogCutoff) ⊆
      Set.Icc (-3 : ℝ) 3 :=
  (SchwartzMap.tsupport_derivCLM_subset ℂ quadraticSmoothLogCutoff).trans
    quadraticSmoothLogCutoff_support

 theorem quadraticSmoothLogCutoff_second_support :
    tsupport (SchwartzMap.derivCLM ℂ ℂ
      (SchwartzMap.derivCLM ℂ ℂ quadraticSmoothLogCutoff)) ⊆ Set.Icc (-3 : ℝ) 3 :=
  (SchwartzMap.tsupport_derivCLM_subset ℂ _).trans
    quadraticSmoothLogCutoff_deriv_support

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticLogNormBounds
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform integral bounds for the actual logarithmic cutoff -/

namespace Ostmann

open MeasureTheory LineDeriv
open scoped SchwartzMap

 theorem quadratic_log_window_norm_bound (ρ : 𝓢(ℝ, ℂ)) (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℝ, 0 < X →
      (∫ u : ℝ, ‖quadraticLogWindow ρ X u‖) ≤ C / X ^ A := by
  refine ⟨quadraticLogDecayConstant ρ A * (∫ u : ℝ, ‖quadraticSmoothLogCutoff u‖),
    mul_nonneg (quadraticLogDecayConstant_nonneg ρ A) (integral_nonneg (fun _ => norm_nonneg _)), ?_⟩
  intro X hX
  have hh := quadratic_log_product_integral quadraticSmoothLogCutoff ρ A
    quadraticSmoothLogCutoff_support hX
  calc
    _ = ∫ u : ℝ, ‖quadraticSmoothLogCutoff u * ρ (X * Real.exp (-u))‖ := rfl
    _ ≤ _ := hh
    _ = _ := by ring

 theorem quadratic_log_window_second_norm_bound (ρ : 𝓢(ℝ, ℂ)) (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℝ, 0 < X →
      (∫ u : ℝ, ‖(∂_{(1 : ℝ)} (∂_{(1 : ℝ)} (quadraticLogWindow ρ X))) u‖) ≤
        C / X ^ A := by
  let B := quadraticSmoothLogCutoff
  let B₁ := SchwartzMap.derivCLM ℂ ℂ B
  let B₂ := SchwartzMap.derivCLM ℂ ℂ B₁
  let ρ₁ := quadraticEulerDerivative ρ
  let ρ₂ := quadraticEulerDerivative ρ₁
  let C₀ := quadraticLogDecayConstant ρ A
  let C₁ := quadraticLogDecayConstant ρ₁ A
  let C₂ := quadraticLogDecayConstant ρ₂ A
  let I₀ := ∫ u : ℝ, ‖B u‖
  let I₁ := ∫ u : ℝ, ‖B₁ u‖
  let I₂ := ∫ u : ℝ, ‖B₂ u‖
  have hC₀ : 0 ≤ C₀ := quadraticLogDecayConstant_nonneg _ _
  have hC₁ : 0 ≤ C₁ := quadraticLogDecayConstant_nonneg _ _
  have hC₂ : 0 ≤ C₂ := quadraticLogDecayConstant_nonneg _ _
  have hI₀ : 0 ≤ I₀ := integral_nonneg (fun _ => norm_nonneg _)
  have hI₁ : 0 ≤ I₁ := integral_nonneg (fun _ => norm_nonneg _)
  have hI₂ : 0 ≤ I₂ := integral_nonneg (fun _ => norm_nonneg _)
  refine ⟨C₀ * I₂ + 2 * C₁ * I₁ + C₂ * I₀, by positivity, ?_⟩
  intro X hX
  let G₀ := fun u : ℝ => (C₀ / X ^ A) * ‖B₂ u‖
  let G₁ := fun u : ℝ => (C₁ / X ^ A) * ‖B₁ u‖
  let G₂ := fun u : ℝ => (C₂ / X ^ A) * ‖B u‖
  have hG₀ : Integrable G₀ := B₂.integrable.norm.const_mul _
  have hG₁ : Integrable G₁ := B₁.integrable.norm.const_mul _
  have hG₂ : Integrable G₂ := B.integrable.norm.const_mul _
  have hb (u : ℝ) :
      ‖(∂_{(1 : ℝ)} (∂_{(1 : ℝ)} (quadraticLogWindow ρ X))) u‖ ≤
        G₀ u + 2 * G₁ u + G₂ u := by
    have h₀ := quadratic_log_product_decay B₂ ρ A quadraticSmoothLogCutoff_second_support hX u
    have h₁ := quadratic_log_product_decay B₁ ρ₁ A quadraticSmoothLogCutoff_deriv_support hX u
    have h₂ := quadratic_log_product_decay B ρ₂ A quadraticSmoothLogCutoff_support hX u
    rw [quadraticLogWindow_second]
    change ‖B₂ u * ρ (X * Real.exp (-u)) - 2 * B₁ u * ρ₁ (X * Real.exp (-u)) +
      B u * ρ₂ (X * Real.exp (-u))‖ ≤ _
    calc
      _ ≤ ‖B₂ u * ρ (X * Real.exp (-u)) - 2 * B₁ u * ρ₁ (X * Real.exp (-u))‖ +
          ‖B u * ρ₂ (X * Real.exp (-u))‖ := norm_add_le _ _
      _ ≤ (‖B₂ u * ρ (X * Real.exp (-u))‖ +
          ‖2 * B₁ u * ρ₁ (X * Real.exp (-u))‖) +
          ‖B u * ρ₂ (X * Real.exp (-u))‖ := add_le_add (norm_sub_le _ _) le_rfl
      _ = ‖B₂ u * ρ (X * Real.exp (-u))‖ +
          2 * ‖B₁ u * ρ₁ (X * Real.exp (-u))‖ +
          ‖B u * ρ₂ (X * Real.exp (-u))‖ := by
        norm_num [mul_assoc, norm_mul]
      _ ≤ _ := add_le_add (add_le_add h₀ (mul_le_mul_of_nonneg_left h₁ (by norm_num))) h₂
  calc
    _ ≤ ∫ u : ℝ, G₀ u + 2 * G₁ u + G₂ u :=
      integral_mono (∂_{(1 : ℝ)} (∂_{(1 : ℝ)} (quadraticLogWindow ρ X))).integrable.norm
        ((hG₀.add (hG₁.const_mul 2)).add hG₂) hb
    _ = (C₀ / X ^ A) * I₂ + 2 * ((C₁ / X ^ A) * I₁) + (C₂ / X ^ A) * I₀ := by
      rw [integral_add (f := fun u => G₀ u + 2 * G₁ u) (g := G₂)
        (hG₀.add (hG₁.const_mul 2)) hG₂,
        integral_add (f := G₀) (g := fun u => 2 * G₁ u) hG₀ (hG₁.const_mul 2)]
      simp only [G₀, G₁, G₂, integral_const_mul, I₀, I₁, I₂]
    _ = _ := by ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticLogFourierEnvelope
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A common Fourier majorant for varying Poisson parameters -/

namespace Ostmann

open MeasureTheory LineDeriv
open scoped SchwartzMap FourierTransform

 theorem quadraticFourierEnvelope_nonneg (u : ℝ) : 0 ≤ quadraticFourierEnvelope u :=
  Real.rpow_nonneg (by positivity) _

 theorem quadraticFourierEnvelope_integrable : Integrable quadraticFourierEnvelope :=
  integrable_one_add_norm (E := ℝ) (by norm_num : (Module.finrank ℝ ℝ : ℝ) < 2)

 theorem quadratic_fourier_pointwise_bound (f : 𝓢(ℝ, ℂ)) (u : ℝ) :
    ‖𝓕 f u‖ ≤ 2 * ((∫ x : ℝ, ‖f x‖) +
      (∫ x : ℝ, ‖(∂_{(1 : ℝ)} (∂_{(1 : ℝ)} f)) x‖) / (2 * Real.pi) ^ 2) *
        quadraticFourierEnvelope u := by
  let A := ∫ x : ℝ, ‖f x‖
  let B := (∫ x : ℝ, ‖(∂_{(1 : ℝ)} (∂_{(1 : ℝ)} f)) x‖) / (2 * Real.pi) ^ 2
  have h₀ := quadratic_fourier_norm_le_integral f u
  have h₂ := quadratic_fourier_frequency_bound f u
  have he : (1 + ‖u‖) ^ 2 ≤ 2 * (1 + u ^ 2) := by
    rw [Real.norm_eq_abs]
    nlinarith [sq_nonneg (|u| - 1), sq_abs u]
  have hm := mul_le_mul_of_nonneg_right he (norm_nonneg (𝓕 f u))
  have hw : (1 + ‖u‖) ^ 2 * ‖𝓕 f u‖ ≤ 2 * (A + B) := by
    calc
      _ ≤ 2 * (1 + u ^ 2) * ‖𝓕 f u‖ := hm
      _ = 2 * (‖𝓕 f u‖ + u ^ 2 * ‖𝓕 f u‖) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add h₀ h₂) (by norm_num)
  rw [quadraticFourierEnvelope, Real.rpow_neg (by positivity : 0 ≤ 1 + ‖u‖),
    Real.rpow_two, ← div_eq_mul_inv]
  exact (le_div_iff₀ (by positivity : 0 < (1 + ‖u‖) ^ 2)).mpr (by nlinarith [hw])

 theorem quadratic_log_window_envelope_decay (ρ : 𝓢(ℝ, ℂ)) (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℝ, 0 < X → ∀ u : ℝ,
      ‖𝓕 (quadraticLogWindow ρ X) u‖ ≤ (C / X ^ A) * quadraticFourierEnvelope u := by
  obtain ⟨C₀, hC₀, h₀⟩ := quadratic_log_window_norm_bound ρ A
  obtain ⟨C₂, hC₂, h₂⟩ := quadratic_log_window_second_norm_bound ρ A
  have hp : 0 < (2 * Real.pi) ^ 2 := by positivity
  refine ⟨2 * (C₀ + C₂ / (2 * Real.pi) ^ 2), by positivity, ?_⟩
  intro X hX u
  calc
    _ ≤ 2 * ((∫ x : ℝ, ‖quadraticLogWindow ρ X x‖) +
      (∫ x : ℝ, ‖(∂_{(1 : ℝ)} (∂_{(1 : ℝ)} (quadraticLogWindow ρ X))) x‖) /
        (2 * Real.pi) ^ 2) * quadraticFourierEnvelope u := quadratic_fourier_pointwise_bound _ _
    _ ≤ 2 * (C₀ / X ^ A + (C₂ / X ^ A) / (2 * Real.pi) ^ 2) *
        quadraticFourierEnvelope u := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (add_le_add (h₀ X hX)
          (div_le_div_of_nonneg_right (h₂ X hX) hp.le)) (by norm_num))
        (quadraticFourierEnvelope_nonneg u)
    _ = _ := by ring

 theorem quadratic_log_window_envelope (ρ : 𝓢(ℝ, ℂ)) (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℝ, 0 < X → ∀ u : ℝ,
      ‖𝓕 (quadraticLogWindow ρ X) u‖ ≤
        C * min 1 (1 / X ^ A) * quadraticFourierEnvelope u := by
  obtain ⟨C₀, hC₀, h₀⟩ := quadratic_log_window_envelope_decay ρ 0
  obtain ⟨C₁, hC₁, h₁⟩ := quadratic_log_window_envelope_decay ρ A
  let C := max C₀ C₁
  have hC : 0 ≤ C := le_max_of_le_left hC₀
  refine ⟨C, hC, ?_⟩
  intro X hX u
  rw [mul_min_of_nonneg _ _ hC, min_mul_of_nonneg _ _ (quadraticFourierEnvelope_nonneg u),
    mul_one, mul_one_div]
  apply le_min
  · have hh : ‖𝓕 (quadraticLogWindow ρ X) u‖ ≤ C₀ * quadraticFourierEnvelope u := by
      simpa using h₀ X hX u
    exact hh.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (quadraticFourierEnvelope_nonneg u))
  · exact (h₁ X hX u).trans (mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right (le_max_right _ _) (by positivity))
      (quadraticFourierEnvelope_nonneg u))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticHalfReflection
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The fixed half-reflection needed for square-root Poisson weights -/

namespace Ostmann

open MeasureTheory
open scoped SchwartzMap FourierTransform

 theorem quadraticHalfReflection_apply (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    quadraticHalfReflection f x = f (-x / 2) := by
  change f (x * (-1 / 2 : ℝ)) = _
  congr 1
  ring

 theorem quadratic_half_reflection_fourier (f : 𝓢(ℝ, ℂ)) (u : ℝ) :
    𝓕 (quadraticHalfReflection f) u = 2 * 𝓕 f (-2 * u) := by
  let G := fun x : ℝ => realAdditivePhase (2 * x * u) * f x
  have ht := Measure.integral_comp_mul_right G (-1 / 2 : ℝ)
  norm_num at ht
  rw [quadratic_fourier_phase_integral, quadratic_fourier_phase_integral]
  calc
    _ = ∫ x : ℝ, G (x * (-1 / 2 : ℝ)) := by
      apply integral_congr_ae
      filter_upwards with x
      rw [quadraticHalfReflection_apply]
      dsimp only [G]
      congr 2 <;> ring
    _ = (2 : ℝ) • ∫ x : ℝ, G x := by simpa only [neg_div, mul_neg, Complex.real_smul, Complex.ofReal_ofNat] using ht
    _ = _ := by
      rw [Complex.real_smul]
      push_cast
      congr 1
      apply integral_congr_ae
      filter_upwards with x
      dsimp only [G]
      congr 2
      ring

 theorem quadratic_half_reflection_fourier_norm (f : 𝓢(ℝ, ℂ)) (u : ℝ) :
    ‖𝓕 (quadraticHalfReflection f) u‖ = 2 * ‖𝓕 f (-2 * u)‖ := by
  rw [quadratic_half_reflection_fourier, norm_mul]
  norm_num

 theorem quadraticFourierEnvelope_half_reflection (u : ℝ) :
    quadraticFourierEnvelope (-2 * u) ≤ quadraticFourierEnvelope u := by
  apply Real.rpow_le_rpow_of_nonpos (by positivity)
  · rw [norm_mul]
    norm_num [Real.norm_eq_abs]
    linarith [abs_nonneg u]
  · norm_num

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticLogRootKernel
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The square-root weight in the second Poisson transform -/

namespace Ostmann

open MeasureTheory
open scoped SchwartzMap FourierTransform

private theorem quadratic_log_pair_range {N s t : ℕ} (hN : 0 < N)
    (hs : N ≤ s) (hs₂ : s ≤ 2 * N) (ht : N ≤ t) (ht₂ : t ≤ 2 * N) :
    |Real.log s + Real.log t - 2 * Real.log N| ≤ 2 := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hsR : (0 : ℝ) < s := hNR.trans_le (by exact_mod_cast hs)
  have htR : (0 : ℝ) < t := hNR.trans_le (by exact_mod_cast ht)
  have hslo : Real.log N ≤ Real.log s := Real.log_le_log hNR (by exact_mod_cast hs)
  have htlo : Real.log N ≤ Real.log t := Real.log_le_log hNR (by exact_mod_cast ht)
  have hsu : Real.log s ≤ Real.log 2 + Real.log N := by
    have hh := Real.log_le_log hsR (show (s : ℝ) ≤ 2 * N by exact_mod_cast hs₂)
    rwa [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hNR.ne'] at hh
  have htu : Real.log t ≤ Real.log 2 + Real.log N := by
    have hh := Real.log_le_log htR (show (t : ℝ) ≤ 2 * N by exact_mod_cast ht₂)
    rwa [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hNR.ne'] at hh
  have hl2 : Real.log 2 ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hh ⊢
    exact hh
  have hu : |Real.log s + Real.log t - 2 * Real.log N| ≤ 2 := by
    rw [abs_le]
    constructor <;> linarith
  exact hu

 theorem quadratic_log_root_kernel_identity (ρ : 𝓢(ℝ, ℂ)) (X : ℝ)
    {N s t : ℕ} (hN : 0 < N) (hs : N ≤ s) (hs₂ : s ≤ 2 * N)
    (ht : N ≤ t) (ht₂ : t ≤ 2 * N) :
    quadraticLogRootKernel ρ X N (Real.log s + Real.log t) =
      ρ (X * Real.sqrt ((s : ℝ) * t)) := by
  let v := Real.log s + Real.log t - 2 * Real.log N
  have hv : |v| ≤ 2 := quadratic_log_pair_range hN hs hs₂ ht ht₂
  have hv₂ : |-v / 2| ≤ 2 := by
    rw [abs_div, abs_neg]
    norm_num
    linarith
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hsR : (0 : ℝ) < s := hNR.trans_le (by exact_mod_cast hs)
  have htR : (0 : ℝ) < t := hNR.trans_le (by exact_mod_cast ht)
  have hvlog : v = Real.log (((s : ℝ) * t) / (N : ℝ) ^ 2) := by
    rw [Real.log_div (mul_ne_zero hsR.ne' htR.ne') (pow_ne_zero _ hNR.ne'),
      Real.log_mul hsR.ne' htR.ne', Real.log_pow]
    norm_num [v]
  have he : Real.exp (v / 2) ^ 2 = ((s : ℝ) * t) / (N : ℝ) ^ 2 := by
    rw [← Real.exp_nat_mul]
    norm_num only [Nat.cast_ofNat]
    rw [show (2 : ℝ) * (v / 2) = v by ring, hvlog, Real.exp_log (by positivity)]
  have hsquare : ((N : ℝ) * Real.exp (v / 2)) ^ 2 = (s : ℝ) * t := by
    rw [mul_pow, he]
    field_simp
  have hr : (N : ℝ) * Real.exp (v / 2) = Real.sqrt ((s : ℝ) * t) := by
    have hnonneg : 0 ≤ (N : ℝ) * Real.exp (v / 2) := by positivity
    have hsq := Real.sq_sqrt (show 0 ≤ (s : ℝ) * t by positivity)
    have hsqrt := Real.sqrt_nonneg ((s : ℝ) * t)
    nlinarith
  rw [quadraticLogRootKernel, SchwartzMap.compSubConstCLM_apply,
    quadraticHalfReflection_apply]
  change quadraticLogWindow ρ (X * N) (-v / 2) = _
  rw [quadraticLogWindow_eq ρ _ _ hv₂, show -(-v / 2) = v / 2 by ring]
  congr 1
  calc
    _ = X * ((N : ℝ) * Real.exp (v / 2)) := by ring
    _ = _ := by rw [hr]

 theorem quadratic_log_root_kernel_envelope (ρ : 𝓢(ℝ, ℂ)) (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 0 < N → ∀ X Y : ℝ, 0 < Y → Y ≤ X → ∀ u : ℝ,
      ‖𝓕 (quadraticLogRootKernel ρ X N) u‖ ≤
        C * min 1 (1 / (Y * N) ^ A) * quadraticFourierEnvelope u := by
  obtain ⟨C, hC, hc⟩ := quadratic_log_window_envelope ρ A
  refine ⟨2 * C, by positivity, ?_⟩
  intro N hN X Y hY hYX u
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hX : 0 < X := hY.trans_le hYX
  rw [quadraticLogRootKernel, quadratic_fourier_translate_norm,
    quadratic_half_reflection_fourier_norm]
  have hh := hc (X * N) (by positivity) (-2 * u)
  calc
    _ ≤ 2 * (C * min 1 (1 / (X * N) ^ A) * quadraticFourierEnvelope (-2 * u)) := by
      gcongr
    _ ≤ 2 * (C * min 1 (1 / (Y * N) ^ A) * quadraticFourierEnvelope u) := by
      gcongr
      · exact quadraticFourierEnvelope_nonneg _
      · exact quadraticFourierEnvelope_half_reflection u
    _ = _ := by ring

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

 theorem quadraticFourierSquare_even (ρ : 𝓢(ℝ, ℂ)) (a : ℝ) (ha : 1 ≤ |a|) :
    Function.Even (quadraticFourierSquare ρ a ha) :=
  quadraticSquareCompose_even _ _ _

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticCorrectionCutoffGeometry
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual frequency-dependent cutoffs lie in fixed divisor bands -/

namespace Ostmann

theorem quadratic_correction_base_formula {M H : ℝ} {e b : ℕ}
    (hM : 0 < M) (hH : 0 < H) (he : 0 < e) (_hb : 0 < b) :
    quadraticCorrectionBase M H e b =
      H * Real.sqrt e / (Real.sqrt M * Real.sqrt b) := by
  unfold quadraticCorrectionBase
  rw [Real.sqrt_div (by positivity), Real.sqrt_mul (by positivity : (0 : ℝ) ≤ e),
    Real.sqrt_sq_eq_abs, abs_of_pos hH, Real.sqrt_mul hM.le]
  ring

theorem quadratic_correction_base_band {M H : ℝ} {e B b : ℕ}
    (hM : 0 < M) (hH : 0 < H) (he : 0 < e) (hB : 0 < B)
    (hb : B ≤ b) (hb' : b ≤ 2 * B) :
    quadraticCorrectionBase M H e B / 2 ≤ quadraticCorrectionBase M H e b ∧
      quadraticCorrectionBase M H e b ≤ quadraticCorrectionBase M H e B := by
  have hBR : (0 : ℝ) < B := by exact_mod_cast hB
  have hbR : (0 : ℝ) < b := by exact_mod_cast hB.trans_le hb
  have hb₁ : (B : ℝ) ≤ b := by exact_mod_cast hb
  have hb₂ : (b : ℝ) ≤ 2 * B := by exact_mod_cast hb'
  have hn : 0 ≤ (e : ℝ) * H ^ 2 := by positivity
  have hlo : (e : ℝ) * H ^ 2 / (M * B) ≤
      2 * ((e : ℝ) * H ^ 2 / (M * b)) := by
    calc
      _ = 2 * ((e : ℝ) * H ^ 2 / (M * (2 * B))) := by ring
      _ ≤ _ := by gcongr
  have hhi : (e : ℝ) * H ^ 2 / (M * b) ≤ (e : ℝ) * H ^ 2 / (M * B) := by gcongr
  unfold quadraticCorrectionBase
  constructor
  · have h₁ := Real.sq_sqrt (div_nonneg hn (by positivity : 0 ≤ M * B))
    have h₂ := Real.sq_sqrt (div_nonneg hn (by positivity : 0 ≤ M * b))
    have h₁₀ := Real.sqrt_nonneg ((e : ℝ) * H ^ 2 / (M * B))
    have h₂₀ := Real.sqrt_nonneg ((e : ℝ) * H ^ 2 / (M * b))
    nlinarith
  · exact Real.sqrt_le_sqrt hhi

theorem quadratic_correction_cutoff_band {M H J : ℝ} {e B b : ℕ}
    (hM : 0 < M) (hH : 0 < H) (he : 0 < e) (hB : 0 < B)
    (hJ : 1 ≤ J) (hb : B ≤ b) (hb' : b ≤ 2 * B) :
    quadraticCorrectionBase M H e B / (4 * J) ≤
        quadraticSecondLower (quadraticCorrectionBase M H e b) J ∧
      quadraticSecondLower (quadraticCorrectionBase M H e b) J ≤
        quadraticCorrectionBase M H e B / (2 * J) ∧
      quadraticCorrectionBase M H e B * J ≤
        quadraticSecondUpper (quadraticCorrectionBase M H e b) J ∧
      quadraticSecondUpper (quadraticCorrectionBase M H e b) J ≤
        2 * quadraticCorrectionBase M H e B * J := by
  obtain ⟨hlo, hhi⟩ := quadratic_correction_base_band hM hH he hB hb hb'
  have hJ₀ : 0 < J := zero_lt_one.trans_le hJ
  unfold quadraticSecondLower quadraticSecondUpper
  refine ⟨?_, div_le_div_of_nonneg_right hhi (by positivity), ?_, ?_⟩
  · have hh := div_le_div_of_nonneg_right hlo (by positivity : 0 ≤ 2 * J)
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    ring
  · nlinarith [mul_le_mul_of_nonneg_right hlo hJ₀.le]
  · nlinarith [mul_le_mul_of_nonneg_right hhi hJ₀.le]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticCorrectionWeightBalance
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual cutoff geometry balances the low and high divisor weights -/

namespace Ostmann

theorem quadratic_correction_weight_identity {M H : ℝ} {e B : ℕ}
    (hM : 0 < M) (hH : 0 < H) (he : 0 < e) (hB : 0 < B) :
    (M / ((e : ℝ) * H)) * quadraticCorrectionBase M H e B =
      Real.sqrt M / (Real.sqrt e * Real.sqrt B) := by
  rw [quadratic_correction_base_formula hM hH he hB]
  have heR : (0 : ℝ) < e := by exact_mod_cast he
  have hsM := Real.sq_sqrt hM.le
  have hse := Real.sq_sqrt heR.le
  have hsM₀ := (Real.sqrt_pos.mpr hM).ne'
  have hse₀ := (Real.sqrt_pos.mpr heR).ne'
  have hsB₀ := (Real.sqrt_pos.mpr (show (0 : ℝ) < B by exact_mod_cast hB)).ne'
  field_simp
  nlinarith

theorem quadratic_high_weight_balance {M H J : ℝ} {e B D : ℕ}
    (hM : 0 < M) (hH : 0 < H) (he : 0 < e) (hB : 0 < B) (hD : 0 < D)
    (hJ : 1 ≤ J) (hcut : quadraticCorrectionBase M H e B / (8 * J) ≤ (D : ℝ)) :
    Real.sqrt M / (Real.sqrt e * Real.sqrt B * D) ≤
      8 * J * min (M / ((e : ℝ) * H))
        (Real.sqrt M / (Real.sqrt e * Real.sqrt B * D)) := by
  let α := M / ((e : ℝ) * H)
  let β := Real.sqrt M / (Real.sqrt e * Real.sqrt B)
  have hα : 0 ≤ α := by dsimp [α]; positivity
  have hβ : 0 ≤ β := by dsimp [β]; positivity
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have hJpos : 0 < 8 * J := by positivity
  have hi : α * quadraticCorrectionBase M H e B = β :=
    quadratic_correction_weight_identity hM hH he hB
  have hcut' : quadraticCorrectionBase M H e B ≤ (D : ℝ) * (8 * J) :=
    (div_le_iff₀ hJpos).mp hcut
  have hh := mul_le_mul_of_nonneg_left hcut' hα
  have hab : β / D ≤ 8 * J * α := by
    apply (div_le_iff₀ hDR).mpr
    nlinarith [hi]
  have hβJ : β / D ≤ 8 * J * (β / D) := by
    have hn : 0 ≤ β / D := div_nonneg hβ hDR.le
    nlinarith
  have heq : Real.sqrt M / (Real.sqrt e * Real.sqrt B * D) = β / D := by dsimp [β]; ring
  rw [heq]
  change β / D ≤ 8 * J * min α (β / D)
  by_cases hle : α ≤ β / D
  · rw [min_eq_left hle]
    exact hab
  · rw [min_eq_right (le_of_not_ge hle)]
    exact hβJ

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticEvenFourier
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The retained second-transform frequencies have both signs -/

namespace Ostmann

open scoped SchwartzMap FourierTransform

theorem quadratic_schwartz_fourier_even (f : 𝓢(ℝ, ℂ)) (hf : Function.Even f) :
    Function.Even (𝓕 f : 𝓢(ℝ, ℂ)) := by
  intro x
  have h := Real.fourier_comp_linearIsometry (LinearIsometryEquiv.neg ℝ) (f : ℝ → ℂ) x
  have he : (f : ℝ → ℂ) ∘ LinearIsometryEquiv.neg ℝ = f := by
    funext y
    exact hf y
  rw [he] at h
  exact h.symm

theorem quadraticFourierSquare_fourier_even (ρ : 𝓢(ℝ, ℂ)) (a : ℝ) (ha : 1 ≤ |a|) :
    Function.Even (𝓕 (quadraticFourierSquare ρ a ha) : 𝓢(ℝ, ℂ)) :=
  quadratic_schwartz_fourier_even _ (quadraticFourierSquare_even ρ a ha)

theorem quadraticFourierSquare_signed_argument (ρ : 𝓢(ℝ, ℂ)) (a : ℝ)
    (ha : 1 ≤ |a|) (l : ℤ) (Y : ℝ) :
    𝓕 (quadraticFourierSquare ρ a ha) ((l : ℝ) * Y) =
      𝓕 (quadraticFourierSquare ρ a ha) ((l.natAbs : ℝ) * Y) := by
  rcases le_total 0 l with hl | hl
  · have hi : (l.natAbs : ℤ) = l := by rw [Int.natCast_natAbs, abs_of_nonneg hl]
    have he : (l.natAbs : ℝ) = (l : ℝ) := by
      simpa only [Int.cast_natCast] using congrArg (fun z : ℤ => (z : ℝ)) hi
    rw [he]
  · have he : (l : ℝ) = -((l.natAbs : ℕ) : ℝ) := by
      have hi : l = -(l.natAbs : ℤ) := by
        rw [Int.natCast_natAbs, abs_of_nonpos hl, neg_neg]
      simpa only [Int.cast_natCast, Int.cast_neg] using congrArg (fun z : ℤ => (z : ℝ)) hi
    rw [he, neg_mul]
    exact quadraticFourierSquare_fourier_even ρ a ha _

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticMiddleArgument
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The literal retained Fourier frequency is a positive square-root weight -/

namespace Ostmann

open scoped SchwartzMap FourierTransform

theorem quadratic_second_scale_factor {M : ℝ} {e b : ℕ}
    (hM : 0 < M) (he : 0 < e) (hb : 0 < b) (s t : ℕ) :
    quadraticSecondScale M e (s * t) b =
      Real.sqrt ((e : ℝ) / (M * b)) * Real.sqrt ((s : ℝ) * t) := by
  unfold quadraticSecondScale
  rw [Nat.cast_mul, show (e : ℝ) * ((s : ℝ) * t) / (M * b) =
    ((e : ℝ) / (M * b)) * ((s : ℝ) * t) by ring,
    Real.sqrt_mul (by positivity)]

theorem quadratic_middle_frequency_argument (ρ : 𝓢(ℝ, ℂ)) (a : ℝ) (ha : 1 ≤ |a|)
    {M : ℝ} {e b : ℕ} (hM : 0 < M) (he : 0 < e) (hb : 0 < b)
    (l : ℤ) (d s t : ℕ) :
    𝓕 (quadraticFourierSquare ρ a ha)
      ((l : ℝ) * (quadraticSecondScale M e (s * t) b / d)) =
    𝓕 (quadraticFourierSquare ρ a ha)
      (((l.natAbs : ℝ) / d * Real.sqrt ((e : ℝ) / (M * b))) *
        Real.sqrt ((s : ℝ) * t)) := by
  rw [quadraticFourierSquare_signed_argument,
    quadratic_second_scale_factor hM he hb]
  congr 1
  ring

theorem quadratic_middle_parameter_pos {M : ℝ} {e b d : ℕ} {l : ℤ}
    (hM : 0 < M) (he : 0 < e) (hb : 0 < b) (hd : 0 < d) (hl : l ≠ 0) :
    0 < (l.natAbs : ℝ) / d * Real.sqrt ((e : ℝ) / (M * b)) := by
  have hl₀ : 0 < l.natAbs := Int.natAbs_pos.mpr hl
  positivity

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticVaryingBilinear
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A common Fourier majorant for frequency-dependent smooth weights -/

namespace Ostmann

open MeasureTheory
open scoped Classical BigOperators SchwartzMap FourierTransform

 theorem quadratic_varying_weighted_bilinear_bound (f : ℕ → ℕ → 𝓢(ℝ, ℂ))
    (ω : ℝ → ℝ) (hω : Integrable ω) (hω₀ : ∀ u, 0 ≤ ω u) (M N₁ N₂ D : ℕ)
    (a b : ℕ → ℂ) (K₁ K₂ : ℕ → ℝ) (T : ℝ) (hT : 0 ≤ T)
    (hK₁ : ∀ i ≤ Nat.log 2 N₁, 0 ≤ K₁ i)
    (hK₂ : ∀ j ≤ Nat.log 2 N₂, 0 ≤ K₂ j)
    (h₁ : ∀ i ≤ Nat.log 2 N₁, QuadraticSieveBound M (N₁ / 2 ^ i) (K₁ i))
    (h₂ : ∀ j ≤ Nat.log 2 N₂, QuadraticSieveBound M (N₂ / 2 ^ j) (K₂ j))
    (hf : ∀ d ∈ Finset.Ioc D (2 * D), ∀ m ∈ oddSquarefreeRange M,
      ∀ u : ℝ, ‖𝓕 (f d m) u‖ ≤ ω u)
    (hcost : ∀ i ≤ Nat.log 2 N₁, ∀ j ≤ Nat.log 2 N₂,
      D < 4 * (2 ^ i * 2 ^ j) → 2 ^ i * 2 ^ j ≤ 2 * D →
      Real.sqrt (2 * K₁ i * (2 ^ i : ℕ) * quadraticDivisorMoment N₁ a) *
        Real.sqrt (2 * K₂ j * (2 ^ j : ℕ) * quadraticDivisorMoment N₂ b) ≤ T) :
    (∑ d ∈ Finset.Ioc D (2 * D), ∑ m ∈ oddSquarefreeRange M,
      ‖quadraticLogWeightedDivisor (f d m) N₁ N₂ d a b m‖) ≤
      (∫ u : ℝ, ω u) *
        (((Nat.log 2 N₁ + 1 : ℕ) : ℝ) * (Nat.log 2 N₂ + 1) * T) := by
  let G : ℕ → ℕ → ℝ → ℝ := fun d m u => ‖𝓕 (f d m) u‖ *
    ‖quadraticDivisorBilinear N₁ N₂ d
      (quadraticLogModulate u a) (quadraticLogModulate (-u) b) m‖
  let C : ℝ := ((Nat.log 2 N₁ + 1 : ℕ) : ℝ) * (Nat.log 2 N₂ + 1) * T
  have hI (d m : ℕ) : Integrable (G d m) := by
    simpa only [G, norm_mul] using (quadratic_log_integrand_integrable (f d m) N₁ N₂ d a b m).norm
  have hsum : Integrable (fun u : ℝ =>
      ∑ d ∈ Finset.Ioc D (2 * D), ∑ m ∈ oddSquarefreeRange M, G d m u) :=
    integrable_finsetSum _ (fun d _ => integrable_finsetSum _ (fun m _ => hI d m))
  have hbound (u : ℝ) : (∑ d ∈ Finset.Ioc D (2 * D),
      ∑ m ∈ oddSquarefreeRange M, G d m u) ≤ ω u * C := by
    calc
      _ ≤ ∑ d ∈ Finset.Ioc D (2 * D), ∑ m ∈ oddSquarefreeRange M,
          ω u * ‖quadraticDivisorBilinear N₁ N₂ d
            (quadraticLogModulate u a) (quadraticLogModulate (-u) b) m‖ := by
        apply Finset.sum_le_sum
        intro d hd
        apply Finset.sum_le_sum
        intro m hm
        exact mul_le_mul_of_nonneg_right (hf d hd m hm u) (norm_nonneg _)
      _ = ω u * (∑ d ∈ Finset.Ioc D (2 * D), ∑ m ∈ oddSquarefreeRange M,
          ‖quadraticDivisorBilinear N₁ N₂ d
            (quadraticLogModulate u a) (quadraticLogModulate (-u) b) m‖) := by
        simp only [← Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (quadratic_log_modulated_uniform_bound M N₁ N₂ D a b K₁ K₂ T hT
          hK₁ hK₂ h₁ h₂ hcost u) (hω₀ u)
  calc
    _ ≤ ∑ d ∈ Finset.Ioc D (2 * D), ∑ m ∈ oddSquarefreeRange M, ∫ u : ℝ, G d m u := by
      apply Finset.sum_le_sum
      intro d _
      apply Finset.sum_le_sum
      intro m _
      exact quadratic_log_weighted_norm (f d m) N₁ N₂ d a b m
    _ = ∑ d ∈ Finset.Ioc D (2 * D), ∫ u : ℝ,
        ∑ m ∈ oddSquarefreeRange M, G d m u := by
      apply Finset.sum_congr rfl
      intro d _
      exact (integral_finsetSum _ (fun m _ => hI d m)).symm
    _ = ∫ u : ℝ, ∑ d ∈ Finset.Ioc D (2 * D), ∑ m ∈ oddSquarefreeRange M, G d m u :=
      (integral_finsetSum _ (fun d _ =>
        integrable_finsetSum _ (fun m _ => hI d m))).symm
    _ ≤ ∫ u : ℝ, ω u * C :=
      integral_mono hsum (hω.mul_const C) hbound
    _ = _ := integral_mul_const C _

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticWeightedGaussBound
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Smooth divisor comparison with the actual quadratic Gauss coefficient -/

namespace Ostmann

open MeasureTheory
open scoped Classical BigOperators ComplexConjugate SchwartzMap FourierTransform

 theorem quadratic_log_weighted_gauss_split (f : 𝓢(ℝ, ℂ)) (N₁ N₂ d : ℕ)
    (a b : ℕ → ℂ) (m : ℤ) :
    quadraticLogWeightedGaussDivisor f N₁ N₂ d a b m =
      quadraticLogWeightedDivisor f N₁ N₂ d (quadraticGaussLeft a) (quadraticGaussRight b) m -
      2 * quadraticLogWeightedDivisor f N₁ N₂ d
        (quadraticThreeClass (quadraticGaussLeft a))
        (quadraticThreeClass (quadraticGaussRight b)) m := by
  unfold quadraticLogWeightedGaussDivisor quadraticLogWeightedDivisor
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro s hs
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro t ht
  obtain ⟨_, hos, hss⟩ := Finset.mem_filter.mp hs
  obtain ⟨_, hot, hst⟩ := Finset.mem_filter.mp ht
  by_cases hc : s.Coprime t ∧ d ∣ s * t
  · rw [ite_eq_left hc, quadraticGaussMultiplier_mul hc.1 hss hst hos hot]
    simp only [quadraticGaussLeft, quadraticGaussRight, quadraticThreeClass,
      map_mul, starRingEnd_self_apply]
    by_cases hs3 : s % 4 = 3 <;> by_cases ht3 : t % 4 = 3 <;>
      simp only [hs3, ht3, and_self, and_false, false_and, ite_true, if_true, ite_false, if_false,
        map_zero, map_mul, starRingEnd_self_apply, mul_zero, zero_mul, sub_zero, one_mul] <;> ring
  · simp [hc]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticVaryingGauss
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Varying smooth weights with the actual Gauss coefficient -/

namespace Ostmann

open MeasureTheory
open scoped Classical BigOperators ComplexConjugate SchwartzMap FourierTransform

 theorem quadratic_varying_weighted_gauss_bound (f : ℕ → ℕ → 𝓢(ℝ, ℂ))
    (ω : ℝ → ℝ) (hω : Integrable ω) (hω₀ : ∀ u, 0 ≤ ω u) (M N₁ N₂ D : ℕ)
    (a b : ℕ → ℂ) (K₁ K₂ : ℕ → ℝ) (T : ℝ) (hT : 0 ≤ T)
    (hK₁ : ∀ i ≤ Nat.log 2 N₁, 0 ≤ K₁ i)
    (hK₂ : ∀ j ≤ Nat.log 2 N₂, 0 ≤ K₂ j)
    (h₁ : ∀ i ≤ Nat.log 2 N₁, QuadraticSieveBound M (N₁ / 2 ^ i) (K₁ i))
    (h₂ : ∀ j ≤ Nat.log 2 N₂, QuadraticSieveBound M (N₂ / 2 ^ j) (K₂ j))
    (hf : ∀ d ∈ Finset.Ioc D (2 * D), ∀ m ∈ oddSquarefreeRange M,
      ∀ u : ℝ, ‖𝓕 (f d m) u‖ ≤ ω u)
    (hcost : ∀ i ≤ Nat.log 2 N₁, ∀ j ≤ Nat.log 2 N₂,
      D < 4 * (2 ^ i * 2 ^ j) → 2 ^ i * 2 ^ j ≤ 2 * D →
      Real.sqrt (2 * K₁ i * (2 ^ i : ℕ) * quadraticDivisorMoment N₁ a) *
        Real.sqrt (2 * K₂ j * (2 ^ j : ℕ) * quadraticDivisorMoment N₂ b) ≤ T) :
    (∑ d ∈ Finset.Ioc D (2 * D), ∑ m ∈ oddSquarefreeRange M,
      ‖quadraticLogWeightedGaussDivisor (f d m) N₁ N₂ d a b m‖) ≤
      3 * (∫ u : ℝ, ω u) *
        (((Nat.log 2 N₁ + 1 : ℕ) : ℝ) * (Nat.log 2 N₂ + 1) * T) := by
  have hc₁ : ∀ i ≤ Nat.log 2 N₁, ∀ j ≤ Nat.log 2 N₂,
      D < 4 * (2 ^ i * 2 ^ j) → 2 ^ i * 2 ^ j ≤ 2 * D →
      Real.sqrt (2 * K₁ i * (2 ^ i : ℕ) * quadraticDivisorMoment N₁ (quadraticGaussLeft a)) *
        Real.sqrt (2 * K₂ j * (2 ^ j : ℕ) * quadraticDivisorMoment N₂ (quadraticGaussRight b)) ≤ T := by
    simpa only [quadraticDivisorMoment_gaussLeft, quadraticDivisorMoment_gaussRight] using hcost
  have hc₂ : ∀ i ≤ Nat.log 2 N₁, ∀ j ≤ Nat.log 2 N₂,
      D < 4 * (2 ^ i * 2 ^ j) → 2 ^ i * 2 ^ j ≤ 2 * D →
      Real.sqrt (2 * K₁ i * (2 ^ i : ℕ) * quadraticDivisorMoment N₁
        (quadraticThreeClass (quadraticGaussLeft a))) *
        Real.sqrt (2 * K₂ j * (2 ^ j : ℕ) * quadraticDivisorMoment N₂
          (quadraticThreeClass (quadraticGaussRight b))) ≤ T := by
    intro i hi j hj hlo hhi
    apply le_trans _ (hc₁ i hi j hj hlo hhi)
    gcongr
    · have := hK₁ i hi
      positivity
    · exact quadraticDivisorMoment_threeClass _ _
    · have := hK₂ j hj
      positivity
    · exact quadraticDivisorMoment_threeClass _ _
  have hb₁ := quadratic_varying_weighted_bilinear_bound f ω hω hω₀ M N₁ N₂ D
    (quadraticGaussLeft a) (quadraticGaussRight b) K₁ K₂ T hT hK₁ hK₂ h₁ h₂ hf hc₁
  have hb₂ := quadratic_varying_weighted_bilinear_bound f ω hω hω₀ M N₁ N₂ D
    (quadraticThreeClass (quadraticGaussLeft a))
    (quadraticThreeClass (quadraticGaussRight b)) K₁ K₂ T hT hK₁ hK₂ h₁ h₂ hf hc₂
  calc
    _ ≤ ∑ d ∈ Finset.Ioc D (2 * D), ∑ m ∈ oddSquarefreeRange M,
        (‖quadraticLogWeightedDivisor (f d m) N₁ N₂ d (quadraticGaussLeft a) (quadraticGaussRight b) m‖ +
        2 * ‖quadraticLogWeightedDivisor (f d m) N₁ N₂ d
          (quadraticThreeClass (quadraticGaussLeft a))
          (quadraticThreeClass (quadraticGaussRight b)) m‖) := by
      apply Finset.sum_le_sum
      intro d _
      apply Finset.sum_le_sum
      intro m _
      rw [quadratic_log_weighted_gauss_split]
      exact (norm_sub_le _ _).trans (by norm_num [norm_mul])
    _ = (∑ d ∈ Finset.Ioc D (2 * D), ∑ m ∈ oddSquarefreeRange M,
        ‖quadraticLogWeightedDivisor (f d m) N₁ N₂ d (quadraticGaussLeft a) (quadraticGaussRight b) m‖) +
        2 * (∑ d ∈ Finset.Ioc D (2 * D), ∑ m ∈ oddSquarefreeRange M,
          ‖quadraticLogWeightedDivisor (f d m) N₁ N₂ d
          (quadraticThreeClass (quadraticGaussLeft a))
          (quadraticThreeClass (quadraticGaussRight b)) m‖) := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    _ ≤ _ := by nlinarith [hb₁, hb₂]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticRootDivisor
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The literal square-root weights in the second Poisson comparison -/

namespace Ostmann

open MeasureTheory
open scoped Classical BigOperators ComplexConjugate SchwartzMap FourierTransform

 theorem quadratic_root_gauss_divisor_eq (ρ : 𝓢(ℝ, ℂ)) (X : ℝ)
    {N : ℕ} (hN : 0 < N) (d : ℕ) (a b : ℕ → ℂ) (m : ℤ)
    (ha : ∀ n < N, a n = 0) (hb : ∀ n < N, b n = 0) :
    quadraticRootGaussDivisor ρ X N d a b m =
      quadraticLogWeightedGaussDivisor (quadraticLogRootKernel ρ X N) (2 * N) (2 * N) d a b m := by
  unfold quadraticRootGaussDivisor quadraticLogWeightedGaussDivisor
  apply Finset.sum_congr rfl
  intro s hs
  apply Finset.sum_congr rfl
  intro t ht
  by_cases hsa : a s = 0
  · simp [hsa]
  by_cases htb : b t = 0
  · simp [htb]
  have hslo : N ≤ s := by
    by_contra hh
    exact hsa (ha s (by omega))
  have htlo : N ≤ t := by
    by_contra hh
    exact htb (hb t (by omega))
  have hshi := (Finset.mem_Icc.mp (Finset.mem_filter.mp hs).1).2
  have hthi := (Finset.mem_Icc.mp (Finset.mem_filter.mp ht).1).2
  rw [quadratic_log_root_kernel_identity ρ X hN hslo hshi htlo hthi]

 theorem quadratic_varying_root_gauss_bound (ρ : 𝓢(ℝ, ℂ)) (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (M N D : ℕ) (X : ℕ → ℕ → ℝ) (Y : ℝ), 0 < N → 0 < Y →
      (∀ d ∈ Finset.Ioc D (2 * D), ∀ m ∈ oddSquarefreeRange M, Y ≤ X d m) →
      ∀ (a b : ℕ → ℂ) (K₁ K₂ : ℕ → ℝ) (T : ℝ), 0 ≤ T →
      (∀ n < N, a n = 0) → (∀ n < N, b n = 0) →
      (∀ i ≤ Nat.log 2 (2 * N), 0 ≤ K₁ i) →
      (∀ j ≤ Nat.log 2 (2 * N), 0 ≤ K₂ j) →
      (∀ i ≤ Nat.log 2 (2 * N), QuadraticSieveBound M (2 * N / 2 ^ i) (K₁ i)) →
      (∀ j ≤ Nat.log 2 (2 * N), QuadraticSieveBound M (2 * N / 2 ^ j) (K₂ j)) →
      (∀ i ≤ Nat.log 2 (2 * N), ∀ j ≤ Nat.log 2 (2 * N),
        D < 4 * (2 ^ i * 2 ^ j) → 2 ^ i * 2 ^ j ≤ 2 * D →
        Real.sqrt (2 * K₁ i * (2 ^ i : ℕ) * quadraticDivisorMoment (2 * N) a) *
          Real.sqrt (2 * K₂ j * (2 ^ j : ℕ) * quadraticDivisorMoment (2 * N) b) ≤ T) →
      (∑ d ∈ Finset.Ioc D (2 * D), ∑ m ∈ oddSquarefreeRange M,
        ‖quadraticRootGaussDivisor ρ (X d m) N d a b m‖) ≤
          C * min 1 (1 / (Y * N) ^ A) *
            ((((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ)) ^ 2 * T) := by
  obtain ⟨C, hC, hc⟩ := quadratic_log_root_kernel_envelope ρ A
  let J := ∫ u : ℝ, quadraticFourierEnvelope u
  have hJ : 0 ≤ J := integral_nonneg quadraticFourierEnvelope_nonneg
  refine ⟨3 * C * J, by positivity, ?_⟩
  intro M N D X Y hN hY hYX a b K₁ K₂ T hT ha hb hK₁ hK₂ h₁ h₂ hcost
  let Z := min 1 (1 / (Y * N) ^ A)
  have hZ : 0 ≤ Z := by dsimp [Z]; positivity
  let f : ℕ → ℕ → 𝓢(ℝ, ℂ) := fun d m => quadraticLogRootKernel ρ (X d m) N
  let ω := fun u : ℝ => (C * Z) * quadraticFourierEnvelope u
  have hω : Integrable ω := quadraticFourierEnvelope_integrable.const_mul _
  have hω₀ : ∀ u, 0 ≤ ω u := fun u => mul_nonneg (mul_nonneg hC hZ)
    (quadraticFourierEnvelope_nonneg u)
  have hf : ∀ d ∈ Finset.Ioc D (2 * D), ∀ m ∈ oddSquarefreeRange M,
      ∀ u : ℝ, ‖𝓕 (f d m) u‖ ≤ ω u := by
    intro d hd m hm u
    exact hc N hN (X d m) Y hY (hYX d hd m hm) u
  have hcomp := quadratic_varying_weighted_gauss_bound f ω hω hω₀
    M (2 * N) (2 * N) D a b K₁ K₂ T hT hK₁ hK₂ h₁ h₂ hf hcost
  have he : (∑ d ∈ Finset.Ioc D (2 * D), ∑ m ∈ oddSquarefreeRange M,
      ‖quadraticRootGaussDivisor ρ (X d m) N d a b m‖) =
      ∑ d ∈ Finset.Ioc D (2 * D), ∑ m ∈ oddSquarefreeRange M,
      ‖quadraticLogWeightedGaussDivisor (f d m) (2 * N) (2 * N) d a b m‖ := by
    apply Finset.sum_congr rfl
    intro d _
    apply Finset.sum_congr rfl
    intro m _
    rw [quadratic_root_gauss_divisor_eq ρ (X d m) hN d a b m ha hb]
  rw [he]
  calc
    _ ≤ 3 * (∫ u : ℝ, ω u) *
        ((((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ)) ^ 2 * T) := by
      simpa only [pow_two, Nat.cast_add, Nat.cast_one] using hcomp
    _ = _ := by
      dsimp only [ω, J]
      rw [integral_const_mul]
      ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticUniformRootDivisor
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A uniform comparison for every positive second-transform parameter -/

namespace Ostmann

open scoped Classical BigOperators SchwartzMap

theorem quadratic_positive_root_gauss_bound (ρ : 𝓢(ℝ, ℂ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (M N D : ℕ) (X : ℕ → ℕ → ℝ), 0 < N →
      (∀ d ∈ Finset.Ioc D (2 * D), ∀ m ∈ oddSquarefreeRange M, 0 < X d m) →
      ∀ (a b : ℕ → ℂ) (K₁ K₂ : ℕ → ℝ) (T : ℝ), 0 ≤ T →
      (∀ n < N, a n = 0) → (∀ n < N, b n = 0) →
      (∀ i ≤ Nat.log 2 (2 * N), 0 ≤ K₁ i) →
      (∀ j ≤ Nat.log 2 (2 * N), 0 ≤ K₂ j) →
      (∀ i ≤ Nat.log 2 (2 * N), QuadraticSieveBound M (2 * N / 2 ^ i) (K₁ i)) →
      (∀ j ≤ Nat.log 2 (2 * N), QuadraticSieveBound M (2 * N / 2 ^ j) (K₂ j)) →
      (∀ i ≤ Nat.log 2 (2 * N), ∀ j ≤ Nat.log 2 (2 * N),
        D < 4 * (2 ^ i * 2 ^ j) → 2 ^ i * 2 ^ j ≤ 2 * D →
        Real.sqrt (2 * K₁ i * (2 ^ i : ℕ) * quadraticDivisorMoment (2 * N) a) *
          Real.sqrt (2 * K₂ j * (2 ^ j : ℕ) * quadraticDivisorMoment (2 * N) b) ≤ T) →
      (∑ d ∈ Finset.Ioc D (2 * D), ∑ m ∈ oddSquarefreeRange M,
        ‖quadraticRootGaussDivisor ρ (X d m) N d a b m‖) ≤
          C * ((((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ)) ^ 2 * T) := by
  obtain ⟨C, hC, hc⟩ := quadratic_varying_root_gauss_bound ρ 0
  refine ⟨C, hC, ?_⟩
  intro M N D X hN hX a b K₁ K₂ T hT ha hb hK₁ hK₂ h₁ h₂ hcost
  let F := (Finset.Ioc D (2 * D)).product (oddSquarefreeRange M)
  by_cases hF : F.Nonempty
  · obtain ⟨z, hz, hmin⟩ := F.exists_min_image (fun z => X z.1 z.2) hF
    obtain ⟨hzd, hzm⟩ := Finset.mem_product.mp hz
    have hY : 0 < X z.1 z.2 := hX z.1 hzd z.2 hzm
    have hYX : ∀ d ∈ Finset.Ioc D (2 * D), ∀ m ∈ oddSquarefreeRange M,
        X z.1 z.2 ≤ X d m := by
      intro d hd m hm
      exact hmin (d, m) (Finset.mem_product.mpr ⟨hd, hm⟩)
    simpa only [pow_zero, div_one, min_self, mul_one] using
      hc M N D X (X z.1 z.2) hN hY hYX a b K₁ K₂ T hT ha hb hK₁ hK₂ h₁ h₂ hcost
  · have hf : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hF
    have hz : (∑ d ∈ Finset.Ioc D (2 * D), ∑ m ∈ oddSquarefreeRange M,
        ‖quadraticRootGaussDivisor ρ (X d m) N d a b m‖) = 0 := by
      calc
        _ = ∑ z ∈ F, ‖quadraticRootGaussDivisor ρ (X z.1 z.2) N z.1 a b z.2‖ := by
          dsimp only [F]
          rw [Finset.product_eq_sprod, Finset.sum_product]
        _ = 0 := by rw [hf, Finset.sum_empty]
    rw [hz]
    positivity

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticMiddleDivisor
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The literal middle-frequency correction in the second Poisson formula -/

namespace Ostmann

open scoped Classical BigOperators ComplexConjugate SchwartzMap FourierTransform

theorem quadratic_middle_divisor_eq (ρ : 𝓢(ℝ, ℂ)) (a : ℝ) (ha : 1 ≤ |a|)
    {M : ℝ} {e b : ℕ} (hM : 0 < M) (he : 0 < e) (hb : 0 < b)
    (N d : ℕ) (v w : ℕ → ℂ) (l : ℤ) :
    quadraticMiddleDivisor ρ a ha M e N d v w b l =
      quadraticRootGaussDivisor (𝓕 (quadraticFourierSquare ρ a ha))
        ((l.natAbs : ℝ) / d * Real.sqrt ((e : ℝ) / (M * b))) N d v w b := by
  unfold quadraticMiddleDivisor quadraticRootGaussDivisor
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro t _
  rw [quadratic_middle_frequency_argument ρ a ha hM he hb]

theorem quadratic_middle_window_eq (ρ : 𝓢(ℝ, ℂ)) (a : ℝ) (ha : 1 ≤ |a|)
    (M : ℝ) (e N d : ℕ) (v w : ℕ → ℂ) (b L : ℕ) :
    quadraticMiddleWindow ρ a ha M e N d v w b L =
      ∑ l ∈ Finset.Icc (-(L : ℤ)) L,
        if l = 0 then 0 else quadraticMiddleDivisor ρ a ha M e N d v w b l := by
  unfold quadraticMiddleWindow quadraticLatticeWindow quadraticMiddleDivisor
  simp_rw [Finset.mul_sum]
  conv_lhs =>
    arg 2
    ext s
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  by_cases hl : l = 0 <;> simp [hl]

theorem quadratic_middle_divisor_bound (ρ : 𝓢(ℝ, ℂ)) (a : ℝ) (ha : 1 ≤ |a|) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (M : ℝ) (e B N D : ℕ), 0 < M → 0 < e → 0 < N →
      ∀ (l : ℤ), l ≠ 0 → ∀ (v w : ℕ → ℂ) (K₁ K₂ : ℕ → ℝ) (T : ℝ), 0 ≤ T →
      (∀ n < N, v n = 0) → (∀ n < N, w n = 0) →
      (∀ i ≤ Nat.log 2 (2 * N), 0 ≤ K₁ i) →
      (∀ j ≤ Nat.log 2 (2 * N), 0 ≤ K₂ j) →
      (∀ i ≤ Nat.log 2 (2 * N), QuadraticSieveBound B (2 * N / 2 ^ i) (K₁ i)) →
      (∀ j ≤ Nat.log 2 (2 * N), QuadraticSieveBound B (2 * N / 2 ^ j) (K₂ j)) →
      (∀ i ≤ Nat.log 2 (2 * N), ∀ j ≤ Nat.log 2 (2 * N),
        D < 4 * (2 ^ i * 2 ^ j) → 2 ^ i * 2 ^ j ≤ 2 * D →
        Real.sqrt (2 * K₁ i * (2 ^ i : ℕ) * quadraticDivisorMoment (2 * N) v) *
          Real.sqrt (2 * K₂ j * (2 ^ j : ℕ) * quadraticDivisorMoment (2 * N) w) ≤ T) →
      (∑ d ∈ Finset.Ioc D (2 * D), ∑ b ∈ oddSquarefreeRange B,
        ‖quadraticMiddleDivisor ρ a ha M e N d v w b l‖) ≤
          C * ((((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ)) ^ 2 * T) := by
  obtain ⟨C, hC, hc⟩ := quadratic_positive_root_gauss_bound (𝓕 (quadraticFourierSquare ρ a ha))
  refine ⟨C, hC, ?_⟩
  intro M e B N D hM he hN l hl v w K₁ K₂ T hT hv hw hK₁ hK₂ h₁ h₂ hcost
  let X := fun d b : ℕ => (l.natAbs : ℝ) / d * Real.sqrt ((e : ℝ) / (M * b))
  have hX : ∀ d ∈ Finset.Ioc D (2 * D), ∀ b ∈ oddSquarefreeRange B, 0 < X d b := by
    intro d hd b hb
    have hd₀ : 0 < d := lt_of_le_of_lt (Nat.zero_le D) (Finset.mem_Ioc.mp hd).1
    have hb₀ : 0 < b := (Finset.mem_Icc.mp (Finset.mem_filter.mp hb).1).1
    exact quadratic_middle_parameter_pos hM he hb₀ hd₀ hl
  have hbound := hc B N D X hN hX v w K₁ K₂ T hT hv hw hK₁ hK₂ h₁ h₂ hcost
  apply le_trans (le_of_eq ?_) hbound
  apply Finset.sum_congr rfl
  intro d _
  apply Finset.sum_congr rfl
  intro b hb
  have hb₀ : 0 < b := (Finset.mem_Icc.mp (Finset.mem_filter.mp hb).1).1
  rw [quadratic_middle_divisor_eq ρ a ha hM he hb₀]

theorem quadratic_middle_window_bound (ρ : 𝓢(ℝ, ℂ)) (a : ℝ) (ha : 1 ≤ |a|) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (M : ℝ) (e B N D : ℕ), 0 < M → 0 < e → 0 < N →
      ∀ (L : ℕ), ∀ (v w : ℕ → ℂ) (K₁ K₂ : ℕ → ℝ) (T : ℝ), 0 ≤ T →
      (∀ n < N, v n = 0) → (∀ n < N, w n = 0) →
      (∀ i ≤ Nat.log 2 (2 * N), 0 ≤ K₁ i) →
      (∀ j ≤ Nat.log 2 (2 * N), 0 ≤ K₂ j) →
      (∀ i ≤ Nat.log 2 (2 * N), QuadraticSieveBound B (2 * N / 2 ^ i) (K₁ i)) →
      (∀ j ≤ Nat.log 2 (2 * N), QuadraticSieveBound B (2 * N / 2 ^ j) (K₂ j)) →
      (∀ i ≤ Nat.log 2 (2 * N), ∀ j ≤ Nat.log 2 (2 * N),
        D < 4 * (2 ^ i * 2 ^ j) → 2 ^ i * 2 ^ j ≤ 2 * D →
        Real.sqrt (2 * K₁ i * (2 ^ i : ℕ) * quadraticDivisorMoment (2 * N) v) *
          Real.sqrt (2 * K₂ j * (2 ^ j : ℕ) * quadraticDivisorMoment (2 * N) w) ≤ T) →
      (∑ d ∈ Finset.Ioc D (2 * D), ∑ b ∈ oddSquarefreeRange B,
        ‖quadraticMiddleWindow ρ a ha M e N d v w b L‖) ≤
          (2 * L + 1) * C * ((((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ)) ^ 2 * T) := by
  obtain ⟨C, hC, hc⟩ := quadratic_middle_divisor_bound ρ a ha
  refine ⟨C, hC, ?_⟩
  intro M e B N D hM he hN L v w K₁ K₂ T hT hv hw hK₁ hK₂ h₁ h₂ hcost
  let S := Finset.Ioc D (2 * D)
  let R := oddSquarefreeRange B
  let U := Finset.Icc (-(L : ℤ)) L
  let f := fun (l : ℤ) (d b : ℕ) =>
    if l = 0 then (0 : ℝ) else ‖quadraticMiddleDivisor ρ a ha M e N d v w b l‖
  have hpoint (l : ℤ) : (∑ d ∈ S, ∑ b ∈ R, f l d b) ≤
      C * ((((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ)) ^ 2 * T) := by
    by_cases hl : l = 0
    · simp only [f, hl, ite_true, if_true, Finset.sum_const_zero]
      positivity
    · simpa only [f, hl, ite_false, if_false] using
        hc M e B N D hM he hN l hl v w K₁ K₂ T hT hv hw hK₁ hK₂ h₁ h₂ hcost
  have hcard : U.card = 2 * L + 1 := by
    dsimp only [U]
    rw [Int.card_Icc]
    omega
  calc
    _ ≤ ∑ d ∈ S, ∑ b ∈ R, ∑ l ∈ U, f l d b := by
      apply Finset.sum_le_sum
      intro d _
      apply Finset.sum_le_sum
      intro b _
      rw [quadratic_middle_window_eq]
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro l _
      by_cases hl : l = 0 <;> simp [f, hl]
    _ = ∑ l ∈ U, ∑ d ∈ S, ∑ b ∈ R, f l d b := by
      conv_lhs =>
        arg 2
        ext d
        rw [Finset.sum_comm]
      rw [Finset.sum_comm]
    _ ≤ ∑ _l ∈ U, C * ((((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ)) ^ 2 * T) :=
      Finset.sum_le_sum (fun l _ => hpoint l)
    _ = _ := by
      rw [Finset.sum_const, nsmul_eq_mul, hcard]
      push_cast
      ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticCorrectionWeights
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual Mobius and square-root weights of the divisor corrections -/

namespace Ostmann

open scoped Classical BigOperators SchwartzMap

theorem quadratic_moebius_root_weight {D B d b : ℕ}
    (hD : 0 < D) (hB : 0 < B) (hd : D ≤ d) (hb : B ≤ b) :
    ‖((ArithmeticFunction.moebius d : ℂ) / d) / (Real.sqrt b : ℂ)‖ ≤
      1 / ((D : ℝ) * Real.sqrt B) := by
  have hμ : ‖(ArithmeticFunction.moebius d : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_intCast]
    exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := d))
  have hDr : 0 < (D : ℝ) := by exact_mod_cast hD
  have hBr : 0 < (B : ℝ) := by exact_mod_cast hB
  have hdr : (D : ℝ) ≤ d := by exact_mod_cast hd
  have hbr : (B : ℝ) ≤ b := by exact_mod_cast hb
  rw [norm_div, norm_div, Complex.norm_natCast, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  calc
    _ ≤ (1 / (D : ℝ)) / Real.sqrt B := by
      have hfirst : ‖(ArithmeticFunction.moebius d : ℂ)‖ / (d : ℝ) ≤ 1 / (D : ℝ) :=
        div_le_div₀ (by norm_num : (0 : ℝ) ≤ 1) hμ hDr hdr
      exact div_le_div₀ (div_nonneg (by norm_num) hDr.le)
        hfirst (Real.sqrt_pos.2 hBr) (Real.sqrt_le_sqrt hbr)
    _ = _ := by ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticTwoScaleCost
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The two actual shortened matrix ranges in the quadratic comparison -/

namespace Ostmann

private theorem sqrt_add_subadditive {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt (x + y) ≤ Real.sqrt x + Real.sqrt y := by
  have hxy := Real.sq_sqrt (add_nonneg hx hy)
  have hxs := Real.sq_sqrt hx
  have hys := Real.sq_sqrt hy
  have hn := Real.sqrt_nonneg (x + y)
  nlinarith [Real.sqrt_nonneg x, Real.sqrt_nonneg y,
    mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg y)]

theorem quadratic_two_scale_sqrt_cost {Y N u v : ℝ}
    (hY : 0 ≤ Y) (hN : 0 ≤ N) (hu : 1 ≤ u) (hv : 1 ≤ v) :
    Real.sqrt (Y + N / u) * Real.sqrt (Y + N / v) ≤
      Y + 2 * Real.sqrt (Y * N) + N / Real.sqrt (u * v) := by
  have hu₀ : 0 < u := zero_lt_one.trans_le hu
  have hv₀ : 0 < v := zero_lt_one.trans_le hv
  have hsu : Real.sqrt (N / u) ≤ Real.sqrt N := Real.sqrt_le_sqrt
    ((div_le_self hN hu).trans_eq rfl)
  have hsv : Real.sqrt (N / v) ≤ Real.sqrt N := Real.sqrt_le_sqrt
    ((div_le_self hN hv).trans_eq rfl)
  have hprod : Real.sqrt (N / u) * Real.sqrt (N / v) = N / Real.sqrt (u * v) := by
    rw [Real.sqrt_div hN, Real.sqrt_div hN, div_mul_div_comm,
      ← pow_two, Real.sq_sqrt hN, ← Real.sqrt_mul hu₀.le]
  calc
    _ ≤ (Real.sqrt Y + Real.sqrt (N / u)) * (Real.sqrt Y + Real.sqrt (N / v)) :=
      mul_le_mul (sqrt_add_subadditive hY (div_nonneg hN hu₀.le))
        (sqrt_add_subadditive hY (div_nonneg hN hv₀.le))
        (Real.sqrt_nonneg _) (by positivity)
    _ = Y + Real.sqrt Y * Real.sqrt (N / u) + Real.sqrt Y * Real.sqrt (N / v) +
        N / Real.sqrt (u * v) := by
      rw [← hprod]
      nlinarith only [Real.sq_sqrt hY]
    _ ≤ Y + Real.sqrt Y * Real.sqrt N + Real.sqrt Y * Real.sqrt N +
        N / Real.sqrt (u * v) := by
      gcongr
    _ = _ := by rw [Real.sqrt_mul hY]; ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticGrowthMatrixCost
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A common matrix budget for each actual divisor band -/

namespace Ostmann

private theorem root_product_factor {F Y N u v E₁ E₂ : ℝ}
    (hF : 0 ≤ F) (hY : 0 ≤ Y) (hN : 0 ≤ N)
    (hu : 0 < u) (hv : 0 < v) (hE₁ : 0 ≤ E₁) (hE₂ : 0 ≤ E₂) :
    Real.sqrt (2 * (F * (Y + N / u)) * u * E₁) *
      Real.sqrt (2 * (F * (Y + N / v)) * v * E₂) =
      2 * F * Real.sqrt (u * v) *
        (Real.sqrt (Y + N / u) * Real.sqrt (Y + N / v)) *
          (Real.sqrt E₁ * Real.sqrt E₂) := by
  have ha : 0 ≤ Y + N / u := by positivity
  have hb : 0 ≤ Y + N / v := by positivity
  apply (sq_eq_sq₀ (by positivity) (by positivity)).mp
  simp only [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ 2 * (F * (Y + N / u)) * u * E₁),
    Real.sq_sqrt (by positivity : 0 ≤ 2 * (F * (Y + N / v)) * v * E₂),
    Real.sq_sqrt (mul_nonneg hu.le hv.le), Real.sq_sqrt ha, Real.sq_sqrt hb,
    Real.sq_sqrt hE₁, Real.sq_sqrt hE₂]
  ring

/-- The divisor-product upper cutoff gives one budget independent of the
chosen two divisor blocks. The lower cutoff controls the geometry. -/
theorem quadratic_growth_band_root_bound {F Y N u v D E₁ E₂ : ℝ}
    (hF : 0 ≤ F) (hY : 0 ≤ Y) (hN : 0 ≤ N)
    (hu : 1 ≤ u) (hv : 1 ≤ v) (hD : 0 < D)
    (hP : u * v ≤ 2 * D) (hE₁ : 0 ≤ E₁) (hE₂ : 0 ≤ E₂) :
    Real.sqrt (2 * (F * (Y + N / u)) * u * E₁) *
      Real.sqrt (2 * (F * (Y + N / v)) * v * E₂) ≤
      8 * F * Real.sqrt D *
        (Y + Real.sqrt (Y * N) + N / Real.sqrt D) *
          (Real.sqrt E₁ * Real.sqrt E₂) := by
  have hu₀ : 0 < u := zero_lt_one.trans_le hu
  have hv₀ : 0 < v := zero_lt_one.trans_le hv
  have hsp : Real.sqrt (u * v) ≤ 2 * Real.sqrt D := by
    have hh : u * v ≤ 4 * D := by linarith
    calc
      _ ≤ Real.sqrt (4 * D) := Real.sqrt_le_sqrt hh
      _ = 2 * Real.sqrt D := by rw [Real.sqrt_mul (by norm_num)]; norm_num
  have hsd : Real.sqrt D ≠ 0 := (Real.sqrt_pos.mpr hD).ne'
  have hsu : Real.sqrt (u * v) ≠ 0 := (Real.sqrt_pos.mpr (mul_pos hu₀ hv₀)).ne'
  have hp := quadratic_two_scale_sqrt_cost hY hN hu hv
  rw [root_product_factor hF hY hN hu₀ hv₀ hE₁ hE₂]
  calc
    _ ≤ 2 * F * Real.sqrt (u * v) *
        (Y + 2 * Real.sqrt (Y * N) + N / Real.sqrt (u * v)) *
          (Real.sqrt E₁ * Real.sqrt E₂) := by gcongr
    _ ≤ 8 * F * Real.sqrt D *
        (Y + Real.sqrt (Y * N) + N / Real.sqrt D) *
          (Real.sqrt E₁ * Real.sqrt E₂) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      have hy := mul_le_mul_of_nonneg_right hsp hY
      have hc := mul_le_mul_of_nonneg_right hsp (Real.sqrt_nonneg (Y * N))
      have hn := hN
      have hid₁ : Real.sqrt (u * v) * (N / Real.sqrt (u * v)) = N := by field_simp
      have hid₂ : Real.sqrt D * (N / Real.sqrt D) = N := by field_simp
      have hh : Real.sqrt (u * v) *
          (Y + 2 * Real.sqrt (Y * N) + N / Real.sqrt (u * v)) ≤
          4 * Real.sqrt D * (Y + Real.sqrt (Y * N) + N / Real.sqrt D) := by
        rw [mul_add, mul_add, hid₁]
        rw [mul_add, mul_add]
        nlinarith [mul_nonneg (Real.sqrt_nonneg D) hY]
      nlinarith [mul_le_mul_of_nonneg_left hh hF]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticGrowthBandBalance
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The common band budget has the required low/high recursive size -/

namespace Ostmann

theorem quadratic_growth_band_budget_nonneg {F Y N D E : ℝ}
    (hF : 0 ≤ F) (hY : 0 ≤ Y) (hN : 0 ≤ N) (_hD : 0 ≤ D) (hE : 0 ≤ E) :
    0 ≤ quadraticGrowthBandBudget F Y N D E := by
  unfold quadraticGrowthBandBudget
  positivity

/-- The minimum comes from the two outer corrections, with the actual
normalizations M/N and sqrt(M)/(sqrt(B)D). -/
theorem quadratic_first_growth_band_balance {M N B D F Y E : ℝ}
    (hM : 0 < M) (hN : 0 < N) (hB : 0 < B) (hD : 1 ≤ D)
    (hF : 0 ≤ F) (hY : 0 ≤ Y) (hE : 0 ≤ E) :
    min (M / N) (Real.sqrt M / (Real.sqrt B * D)) *
        quadraticGrowthBandBudget F Y N D E ≤
      16 * F * (M + Real.sqrt M / Real.sqrt B * Y) * E := by
  have hD₀ : 0 < D := zero_lt_one.trans_le hD
  have hsM₀ : Real.sqrt M ≠ 0 := (Real.sqrt_pos.mpr hM).ne'
  have hid : (M / N) * (N / (Real.sqrt M * Real.sqrt B * D)) =
      Real.sqrt M / (Real.sqrt B * D) := by
    field_simp
    nlinarith only [Real.sq_sqrt hM.le]
  have hmin : min (M / N) (Real.sqrt M / (Real.sqrt B * D)) =
      (M / N) * min 1 (N / (Real.sqrt M * Real.sqrt B * D)) := by
    rw [mul_min_of_nonneg _ _ (div_nonneg hM.le hN.le), mul_one, hid]
  have hb := quadratic_comparison_envelope hM hN hB hD hY
  rw [hmin]
  unfold quadraticGrowthBandBudget
  calc
    _ = (8 * F * E) *
        ((M / N * Real.sqrt D * min 1 (N / (Real.sqrt M * Real.sqrt B * D))) *
          (Y + Real.sqrt (Y * N) + N / Real.sqrt D)) := by ring
    _ ≤ (8 * F * E) * (2 * (M + Real.sqrt M / Real.sqrt B * Y)) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticDoubledBandBudget
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The coefficient interval [N,2N] and the original correction normalizers -/

namespace Ostmann

theorem quadratic_first_doubled_band_balance {M N B D F Y E : ℝ}
    (hM : 0 < M) (hN : 0 < N) (hB : 0 < B) (hD : 1 ≤ D)
    (hF : 0 ≤ F) (hY : 0 ≤ Y) (hE : 0 ≤ E) :
    min (M / N) (Real.sqrt M / (Real.sqrt B * D)) *
        quadraticGrowthBandBudget F Y (2 * N) D E ≤
      16 * F * (2 * M + Real.sqrt (2 * M) / Real.sqrt B * Y) * E := by
  have heq : M / N = (2 * M) / (2 * N) := by ring
  have hsq : Real.sqrt M ≤ Real.sqrt (2 * M) := Real.sqrt_le_sqrt (by linarith)
  have hmin : min (M / N) (Real.sqrt M / (Real.sqrt B * D)) ≤
      min ((2 * M) / (2 * N)) (Real.sqrt (2 * M) / (Real.sqrt B * D)) := by
    rw [heq]
    exact min_le_min le_rfl (div_le_div_of_nonneg_right hsq (by positivity))
  exact (mul_le_mul_of_nonneg_right hmin
    (quadratic_growth_band_budget_nonneg hF hY (by positivity) (by positivity) hE)).trans
    (quadratic_first_growth_band_balance (by positivity) (by positivity) hB hD hF hY hE)

theorem quadratic_first_high_budget {M N J F Y E : ℝ} {e B D : ℕ}
    (hM : 0 < M) (hN : 0 < N) (he : 0 < e) (hB : 0 < B) (hD : 0 < D)
    (hJ : 1 ≤ J) (hF : 0 ≤ F) (hY : 0 ≤ Y) (hE : 0 ≤ E)
    (hcut : quadraticCorrectionBase M N e B / (8 * J) ≤ (D : ℝ)) :
    (Real.sqrt M / (Real.sqrt e * Real.sqrt B * D)) *
        quadraticGrowthBandBudget F Y (2 * N) D E ≤
      128 * J * F * (2 * (M / e) + Real.sqrt (2 * (M / e)) / Real.sqrt B * Y) * E := by
  have heR : (0 : ℝ) < e := by exact_mod_cast he
  have hBR : (0 : ℝ) < B := by exact_mod_cast hB
  have hDR : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hα : M / ((e : ℝ) * N) = (M / e) / N := by ring
  have hβ : Real.sqrt M / (Real.sqrt e * Real.sqrt B * D) =
      Real.sqrt (M / e) / (Real.sqrt B * D) := by
    rw [Real.sqrt_div hM.le]
    ring
  have hw := quadratic_high_weight_balance hM hN he hB hD hJ hcut
  rw [hα, hβ] at hw
  have hb := quadratic_first_doubled_band_balance (div_pos hM heR) hN hBR hDR hF hY hE
  have ht : 0 ≤ quadraticGrowthBandBudget F Y (2 * N) D E :=
    quadratic_growth_band_budget_nonneg hF hY (by positivity) (by positivity) hE
  rw [hβ]
  calc
    _ ≤ (8 * J * min ((M / e) / N) (Real.sqrt (M / e) / (Real.sqrt B * D))) *
        quadraticGrowthBandBudget F Y (2 * N) D E := mul_le_mul_of_nonneg_right hw ht
    _ = (8 * J) * (min ((M / e) / N) (Real.sqrt (M / e) / (Real.sqrt B * D)) *
        quadraticGrowthBandBudget F Y (2 * N) D E) := by ring
    _ ≤ (8 * J) * (16 * F * (2 * (M / e) + Real.sqrt (2 * (M / e)) / Real.sqrt B * Y) * E) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticFrequencyAggregation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Frequency aggregation preserves each complete divisor comparison -/

namespace Ostmann

open scoped Classical BigOperators

theorem quadratic_correction_frequency_reindex (K Q : ℕ) (F : ℕ → ℕ → ℂ) :
    (∑ d ∈ Finset.Icc 1 Q, ∑ b ∈ oddSquarefreeRange K, F d b) =
      ∑ i ∈ Finset.range (Nat.log 2 K + 1), ∑ d ∈ Finset.Icc 1 Q,
        ∑ b ∈ oddSquarefreeRange (2 * 2 ^ i),
          if 2 ^ i ≤ b ∧ b ≤ K ∧ b < 2 * 2 ^ i then F d b else 0 := by
  calc
    _ = ∑ d ∈ Finset.Icc 1 Q, ∑ i ∈ Finset.range (Nat.log 2 K + 1),
        ∑ b ∈ oddSquarefreeRange (2 * 2 ^ i),
          if 2 ^ i ≤ b ∧ b ≤ K ∧ b < 2 * 2 ^ i then F d b else 0 :=
      Finset.sum_congr rfl (fun d _ => quadratic_correction_frequency_sum K (F d))
    _ = _ := Finset.sum_comm

theorem quadratic_correction_frequency_bound (K Q : ℕ) (F : ℕ → ℕ → ℂ) (c : ℂ)
    (T : ℝ) (hband : ∀ i < Nat.log 2 K + 1,
      ‖c * (∑ d ∈ Finset.Icc 1 Q, ∑ b ∈ oddSquarefreeRange (2 * 2 ^ i),
        if 2 ^ i ≤ b ∧ b ≤ K ∧ b < 2 * 2 ^ i then F d b else 0)‖ ≤ T) :
    ‖c * (∑ d ∈ Finset.Icc 1 Q, ∑ b ∈ oddSquarefreeRange K, F d b)‖ ≤
      ((Nat.log 2 K + 1 : ℕ) : ℝ) * T := by
  rw [quadratic_correction_frequency_reindex, Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _i ∈ Finset.range (Nat.log 2 K + 1), T :=
      Finset.sum_le_sum (fun i hi => hband i (Finset.mem_range.mp hi))
    _ = _ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

theorem quadratic_frequency_block_le {K i : ℕ} (hK : 0 < K) (hi : i < Nat.log 2 K + 1) :
    2 ^ i ≤ K :=
  (Nat.pow_le_pow_right (by norm_num) (by omega : i ≤ Nat.log 2 K)).trans
    (Nat.pow_log_le_self 2 hK.ne')

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticGrowthDivisorBudget
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual shorter sieve matrices supply every divisor-band budget -/

namespace Ostmann

open scoped Classical BigOperators

theorem quadratic_growth_cutoff_nonneg {C ε ξ : ℝ} (hC : 0 ≤ C) (B N i : ℕ) :
    0 ≤ quadraticGrowthCutoff C ε ξ B N i := by
  unfold quadraticGrowthCutoff
  positivity

theorem quadratic_growth_divisor_budget_nonneg {C ε ξ : ℝ} (hC : 0 ≤ C)
    (B N D : ℕ) (v w : ℕ → ℂ) :
    0 ≤ quadraticGrowthDivisorBudget C ε ξ B N D v w := by
  unfold quadraticGrowthDivisorBudget
  exact quadratic_growth_band_budget_nonneg (by positivity) (by positivity)
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) (by positivity)

theorem quadratic_growth_cutoff_cost {C ε ξ : ℝ} (hC : 0 ≤ C)
    {B N D : ℕ} (hD : 0 < D) (v w : ℕ → ℂ)
    {i j : ℕ} (hP : 2 ^ i * 2 ^ j ≤ 2 * D) :
    Real.sqrt (2 * quadraticGrowthCutoff C ε ξ B N i * (2 ^ i : ℕ) *
        quadraticDivisorMoment N v) *
      Real.sqrt (2 * quadraticGrowthCutoff C ε ξ B N j * (2 ^ j : ℕ) *
        quadraticDivisorMoment N w) ≤
      quadraticGrowthDivisorBudget C ε ξ B N D v w := by
  apply quadratic_growth_band_root_bound (by positivity) (by positivity) (Nat.cast_nonneg N)
    (by exact_mod_cast (show 1 ≤ (2 : ℕ) ^ i from one_le_pow₀ (by norm_num)))
    (by exact_mod_cast (show 1 ≤ (2 : ℕ) ^ j from one_le_pow₀ (by norm_num)))
    (by exact_mod_cast hD) (by exact_mod_cast hP)
    (Finset.sum_nonneg fun _ _ => by positivity) (Finset.sum_nonneg fun _ _ => by positivity)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticVariableCorrectionCutoff
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Frequency-dependent divisor cutoffs retain the same matrix bounds -/

namespace Ostmann

open scoped Classical BigOperators

theorem quadratic_variable_correction_weight (F : ℕ → ℕ → ℂ) {D B : ℕ}
    (hD : 0 < D) (hB : 0 < B) (P : ℕ → ℕ → Prop) [DecidableRel P] :
    ‖∑ d ∈ Finset.Ioc D (2 * D), ∑ b ∈ oddSquarefreeRange (2 * B),
      if B ≤ b ∧ P d b then
        (((ArithmeticFunction.moebius d : ℂ) / d) / (Real.sqrt b : ℂ)) * F d b else 0‖ ≤
      (1 / ((D : ℝ) * Real.sqrt B)) *
        ∑ d ∈ Finset.Ioc D (2 * D), ∑ b ∈ oddSquarefreeRange (2 * B), ‖F d b‖ := by
  classical
  calc
    _ ≤ ∑ d ∈ Finset.Ioc D (2 * D), ∑ b ∈ oddSquarefreeRange (2 * B),
        (1 / ((D : ℝ) * Real.sqrt B)) * ‖F d b‖ := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro d hd
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro b _
      split_ifs with h
      · rw [norm_mul]
        exact mul_le_mul_of_nonneg_right
          (quadratic_moebius_root_weight hD hB (Finset.mem_Ioc.mp hd).1.le h.1) (norm_nonneg _)
      · rw [norm_zero]
        positivity
    _ = _ := by simp only [Finset.mul_sum]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticVariableMatrixBands
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Complete variable-cutoff corrections on their actual divisor bands -/

namespace Ostmann

open scoped Classical BigOperators SchwartzMap FourierTransform

theorem quadratic_variable_middle_band_bound (ρ : 𝓢(ℝ, ℂ)) (a : ℝ) (ha : 1 ≤ |a|) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (M : ℝ) (e B N D : ℕ), 0 < M → 0 < e → 0 < B → 0 < N → 0 < D →
      ∀ (L : ℕ) (P : ℕ → ℕ → Prop) [DecidableRel P],
      ∀ (v w : ℕ → ℂ) (K₁ K₂ : ℕ → ℝ) (T : ℝ), 0 ≤ T →
      (∀ n < N, v n = 0) → (∀ n < N, w n = 0) →
      (∀ i ≤ Nat.log 2 (2 * N), 0 ≤ K₁ i) →
      (∀ j ≤ Nat.log 2 (2 * N), 0 ≤ K₂ j) →
      (∀ i ≤ Nat.log 2 (2 * N), QuadraticSieveBound (2 * B) (2 * N / 2 ^ i) (K₁ i)) →
      (∀ j ≤ Nat.log 2 (2 * N), QuadraticSieveBound (2 * B) (2 * N / 2 ^ j) (K₂ j)) →
      (∀ i ≤ Nat.log 2 (2 * N), ∀ j ≤ Nat.log 2 (2 * N),
        D < 4 * (2 ^ i * 2 ^ j) → 2 ^ i * 2 ^ j ≤ 2 * D →
        Real.sqrt (2 * K₁ i * (2 ^ i : ℕ) * quadraticDivisorMoment (2 * N) v) *
          Real.sqrt (2 * K₂ j * (2 ^ j : ℕ) * quadraticDivisorMoment (2 * N) w) ≤ T) →
      ‖∑ d ∈ Finset.Ioc D (2 * D), ∑ b ∈ oddSquarefreeRange (2 * B),
        if B ≤ b ∧ P d b then
          (((ArithmeticFunction.moebius d : ℂ) / d) / (Real.sqrt b : ℂ)) *
            quadraticMiddleWindow ρ a ha M e N d v w b L else 0‖ ≤
        ((2 * L + 1) * C * (((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ) ^ 2 * T)) /
          ((D : ℝ) * Real.sqrt B) := by
  obtain ⟨C, hC, hc⟩ := quadratic_middle_window_bound ρ a ha
  refine ⟨C, hC, ?_⟩
  intro M e B N D hM he hB hN hD L P _ v w K₁ K₂ T hT hv hw hK₁ hK₂ h₁ h₂ hcost
  apply (quadratic_variable_correction_weight _ hD hB P).trans
  have hh := hc M e (2 * B) N D hM he hN L v w K₁ K₂ T hT hv hw hK₁ hK₂ h₁ h₂ hcost
  calc
    _ ≤ (1 / ((D : ℝ) * Real.sqrt B)) *
        ((2 * L + 1) * C * (((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ) ^ 2 * T)) :=
      mul_le_mul_of_nonneg_left hh (by positivity)
    _ = _ := by ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticMiddleBandGrowth
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original middle-divisor correction at the current sieve exponent -/

namespace Ostmann

open scoped Classical BigOperators SchwartzMap

theorem quadratic_middle_band_growth (ρ : 𝓢(ℝ, ℂ)) (a : ℝ) (ha : 1 ≤ |a|) :
    ∃ Cρ : ℝ, 0 ≤ Cρ ∧ ∀ C ε ξ M J : ℝ, 0 ≤ C →
      ∀ e B N D L : ℕ, 0 < M → 0 < e → 0 < B → 0 < N → 0 < D → 1 ≤ J →
      quadraticCorrectionBase M N e B / (8 * J) ≤ (D : ℝ) →
      ∀ P : ℕ → ℕ → Prop, ∀ v w : ℕ → ℂ,
      (∀ n < N, v n = 0) → (∀ n < N, w n = 0) →
      (∀ i ≤ Nat.log 2 (2 * N), QuadraticSieveBound (2 * B) (2 * N / 2 ^ i)
        (quadraticGrowthCutoff C ε ξ (2 * B) (2 * N) i)) →
      ‖((Real.sqrt M / Real.sqrt e : ℝ) : ℂ) *
          quadraticMiddleCorrectionBand ρ a ha M e B N D L P v w‖ ≤
        128 * J * (2 * L + 1) * Cρ * ((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ) ^ 2 *
          quadraticCorrectionGrowthScale C ε ξ M e B N v w := by
  classical
  obtain ⟨Cρ, hCρ, hcρ⟩ := quadratic_variable_middle_band_bound ρ a ha
  refine ⟨Cρ, hCρ, ?_⟩
  intro C ε ξ M J hC e B N D L hM he hB hN hD hJ hcut P v w hv hw hmat
  let T := quadraticGrowthDivisorBudget C ε ξ (2 * B) (2 * N) D v w
  have hT : 0 ≤ T := quadratic_growth_divisor_budget_nonneg hC _ _ _ _ _
  have hl := hcρ M e B N D hM he hB hN hD L P v w
    (quadraticGrowthCutoff C ε ξ (2 * B) (2 * N))
    (quadraticGrowthCutoff C ε ξ (2 * B) (2 * N)) T hT hv hw
    (fun i _ => quadratic_growth_cutoff_nonneg hC _ _ i)
    (fun i _ => quadratic_growth_cutoff_nonneg hC _ _ i) hmat hmat
    (fun _ _ _ _ _ hp => quadratic_growth_cutoff_cost hC hD v w hp)
  change ‖quadraticMiddleCorrectionBand ρ a ha M e B N D L P v w‖ ≤ _ at hl
  have hb := quadratic_first_high_budget hM (show (0 : ℝ) < N by exact_mod_cast hN)
    he hB hD hJ
    (show 0 ≤ C * (((2 * B : ℕ) : ℝ) * (2 * N : ℕ)) ^ ε by positivity)
    (show 0 ≤ ((2 * B : ℕ) : ℝ) ^ ξ by positivity)
    (show 0 ≤ Real.sqrt (quadraticDivisorMoment (2 * N) v) *
      Real.sqrt (quadraticDivisorMoment (2 * N) w) by positivity) hcut
  have hb' : (Real.sqrt M / (Real.sqrt e * Real.sqrt B * D)) * T ≤
      128 * J * quadraticCorrectionGrowthScale C ε ξ M e B N v w := by
    simpa only [T, quadraticGrowthDivisorBudget, quadraticCorrectionGrowthScale,
      Nat.cast_mul, Nat.cast_ofNat, mul_assoc] using hb
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  apply (mul_le_mul_of_nonneg_left hl (by positivity)).trans
  calc
    _ = ((2 * L + 1) * Cρ * ((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ) ^ 2) *
        (Real.sqrt M / (Real.sqrt e * Real.sqrt B * D) * T) := by ring
    _ ≤ ((2 * L + 1) * Cρ * ((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ) ^ 2) *
        (128 * J * quadraticCorrectionGrowthScale C ε ξ M e B N v w) :=
      mul_le_mul_of_nonneg_left hb' (by positivity)
    _ = _ := by ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticFrequencyGrowth
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A uniform current-exponent bound over all frequency blocks -/

namespace Ostmann

open scoped Classical BigOperators

theorem quadratic_frequency_root_power {ξ : ℝ} {B K : ℕ}
    (hξ : 1 / 2 ≤ ξ) (hξ' : ξ ≤ 2) (hB : 0 < B) (hBK : B ≤ K) :
    (((2 * B : ℕ) : ℝ) ^ ξ) / Real.sqrt B ≤ 4 * (K : ℝ) ^ (ξ - 1 / 2) := by
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have hpow := Real.rpow_le_rpow hBr.le (show (B : ℝ) ≤ K by exact_mod_cast hBK)
    (show 0 ≤ ξ - 1 / 2 by linarith)
  have htwo : (2 : ℝ) ^ ξ ≤ 4 := by
    apply (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hξ').trans_eq
    norm_num
  calc
    _ = (2 : ℝ) ^ ξ * (B : ℝ) ^ (ξ - 1 / 2) := by
      rw [Nat.cast_mul, Nat.cast_ofNat, Real.mul_rpow (by norm_num) hBr.le,
        Real.rpow_sub hBr, ← Real.sqrt_eq_rpow]
      ring
    _ ≤ _ := mul_le_mul htwo hpow (by positivity) (by norm_num)

theorem quadratic_frequency_power_cost {ε : ℝ} (hε : 0 ≤ ε) {B N K R : ℕ}
    (hBK : B ≤ K) (hNR : N ≤ R) :
    ((((2 * B : ℕ) : ℝ) * (2 * N : ℕ)) ^ ε) ≤
      (4 * (K : ℝ) * R) ^ ε := by
  apply Real.rpow_le_rpow (by positivity) _ hε
  have hh := mul_le_mul (show (B : ℝ) ≤ K by exact_mod_cast hBK)
    (show (N : ℝ) ≤ R by exact_mod_cast hNR) (Nat.cast_nonneg N) (Nat.cast_nonneg K)
  push_cast
  nlinarith

theorem quadratic_correction_growth_uniform {C ε ξ M : ℝ}
    (hC : 0 ≤ C) (hε : 0 ≤ ε) (hξ : 1 / 2 ≤ ξ) (hξ' : ξ ≤ 2) (hM : 0 < M)
    {e B N K R : ℕ} (he : 0 < e) (hB : 0 < B) (hBK : B ≤ K) (hNR : N ≤ R)
    (v w : ℕ → ℂ) :
    quadraticCorrectionGrowthScale C ε ξ M e B N v w ≤
      10 * C * (4 * (K : ℝ) * R) ^ ε *
        (M + Real.sqrt M * (K : ℝ) ^ (ξ - 1 / 2)) *
          (Real.sqrt (quadraticDivisorMoment (2 * N) v) *
            Real.sqrt (quadraticDivisorMoment (2 * N) w)) := by
  have heR : (1 : ℝ) ≤ e := by exact_mod_cast he
  have hdiv : M / e ≤ M := div_le_self hM.le heR
  have hroot : Real.sqrt (2 * (M / e)) ≤ 2 * Real.sqrt M := by
    have hs := Real.sq_sqrt (show 0 ≤ 2 * (M / e) by positivity)
    have hsM := Real.sq_sqrt hM.le
    have hs₀ := Real.sqrt_nonneg (2 * (M / e))
    have hsM₀ := Real.sqrt_nonneg M
    nlinarith
  have hp := quadratic_frequency_root_power hξ hξ' hB hBK
  have hinner : 2 * (M / e) + Real.sqrt (2 * (M / e)) / Real.sqrt B * ((2 * B : ℕ) : ℝ) ^ ξ ≤
      10 * (M + Real.sqrt M * (K : ℝ) ^ (ξ - 1 / 2)) := by
    calc
      _ = 2 * (M / e) + Real.sqrt (2 * (M / e)) *
          ((((2 * B : ℕ) : ℝ) ^ ξ) / Real.sqrt B) := by ring
      _ ≤ 2 * M + (2 * Real.sqrt M) * (4 * (K : ℝ) ^ (ξ - 1 / 2)) :=
        add_le_add (by linarith) (mul_le_mul hroot hp (by positivity) (by positivity))
      _ ≤ _ := by nlinarith [mul_nonneg (Real.sqrt_nonneg M) (Real.rpow_nonneg (Nat.cast_nonneg K) (ξ - 1 / 2))]
  have hfactor := mul_le_mul_of_nonneg_left (quadratic_frequency_power_cost hε hBK hNR) hC
  unfold quadraticCorrectionGrowthScale
  apply le_trans (mul_le_mul_of_nonneg_right
    (mul_le_mul hfactor hinner (by positivity) (by positivity)) (by positivity))
  apply le_of_eq
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticRoundedCorrectionGeometry
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Rounding the coefficient interval preserves the actual correction cutoffs -/

namespace Ostmann

theorem quadratic_correction_base_double {M H N : ℝ} {e B : ℕ}
    (hM : 0 < M) (hH : 0 < H) (hN : 0 < N) (hNH : N ≤ 2 * H)
    (he : 0 < e) (hB : 0 < B) :
    quadraticCorrectionBase M N e B ≤ 2 * quadraticCorrectionBase M H e B := by
  rw [quadratic_correction_base_formula hM hH he hB,
    quadratic_correction_base_formula hM hN he hB]
  calc
    _ ≤ (2 * H) * Real.sqrt e / (Real.sqrt M * Real.sqrt B) := by gcongr
    _ = _ := by ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticUnitDivisor
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The divisor-one block, retained separately from positive dyadic intervals -/

namespace Ostmann

open scoped Classical BigOperators

theorem quadratic_unit_divisor_bound (M N₁ N₂ : ℕ) (K₁ K₂ : ℝ)
    (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂)
    (h₁ : QuadraticSieveBound M N₁ K₁) (h₂ : QuadraticSieveBound M N₂ K₂)
    (a b : ℕ → ℂ) :
    (∑ m ∈ oddSquarefreeRange M, ‖quadraticDivisorBilinear N₁ N₂ 1 a b m‖) ≤
      Real.sqrt (2 * K₁ * quadraticDivisorMoment N₁ a) *
        Real.sqrt (2 * K₂ * quadraticDivisorMoment N₂ b) := by
  have hshape : ∀ s ∈ ({1} : Finset ℕ), Squarefree s ∧ Odd s := by
    intro s hs
    have he : s = 1 := Finset.mem_singleton.mp hs
    subst s
    norm_num
  have hcut₁ : ∀ s ∈ ({1} : Finset ℕ), QuadraticSieveBound M (N₁ / s) K₁ := by
    intro s hs
    simpa only [Finset.mem_singleton.mp hs, Nat.div_one] using h₁
  have hcut₂ : ∀ s ∈ ({1} : Finset ℕ), QuadraticSieveBound M (N₂ / s) K₂ := by
    intro s hs
    simpa only [Finset.mem_singleton.mp hs, Nat.div_one] using h₂
  have h := quadratic_divisor_family_bound M N₁ N₂ {1} {1} K₁ K₂
    hK₁ hK₂ hshape hshape hcut₁ hcut₂ a b
  have he (m : ℤ) : quadraticDivisorBilinear N₁ N₂ 1 a b m =
      quadraticCoprimeBilinear N₁ N₂ a b m := by
    simp only [quadraticDivisorBilinear, quadraticCoprimeBilinear, one_dvd, and_true]
  simpa only [he, Finset.sum_singleton, one_dvd, ite_true, if_true,
    Finset.card_singleton, Nat.cast_one, mul_one] using h

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticVaryingUnit
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Frequency-dependent smooth weights at the divisor-one boundary -/

namespace Ostmann

open MeasureTheory
open scoped Classical BigOperators SchwartzMap FourierTransform

theorem quadratic_unit_varying_weighted_bound (f : ℕ → 𝓢(ℝ, ℂ))
    (ω : ℝ → ℝ) (hω : Integrable ω) (hω₀ : ∀ u, 0 ≤ ω u) (M N₁ N₂ : ℕ)
    (v w : ℕ → ℂ) (K₁ K₂ : ℝ) (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂)
    (h₁ : QuadraticSieveBound M N₁ K₁) (h₂ : QuadraticSieveBound M N₂ K₂)
    (hf : ∀ m ∈ oddSquarefreeRange M, ∀ u : ℝ, ‖𝓕 (f m) u‖ ≤ ω u) :
    (∑ m ∈ oddSquarefreeRange M, ‖quadraticLogWeightedDivisor (f m) N₁ N₂ 1 v w m‖) ≤
      (∫ u : ℝ, ω u) *
        (Real.sqrt (2 * K₁ * quadraticDivisorMoment N₁ v) *
          Real.sqrt (2 * K₂ * quadraticDivisorMoment N₂ w)) := by
  let G (m : ℕ) (u : ℝ) := ‖𝓕 (f m) u‖ *
    ‖quadraticDivisorBilinear N₁ N₂ 1 (quadraticLogModulate u v) (quadraticLogModulate (-u) w) m‖
  let T := Real.sqrt (2 * K₁ * quadraticDivisorMoment N₁ v) *
    Real.sqrt (2 * K₂ * quadraticDivisorMoment N₂ w)
  have hI (m : ℕ) : Integrable (G m) := by
    simpa only [G, norm_mul] using (quadratic_log_integrand_integrable (f m) N₁ N₂ 1 v w m).norm
  have hsum : Integrable (fun u : ℝ => ∑ m ∈ oddSquarefreeRange M, G m u) :=
    integrable_finsetSum _ (fun m _ => hI m)
  have hb (u : ℝ) : (∑ m ∈ oddSquarefreeRange M, G m u) ≤ ω u * T := by
    calc
      _ ≤ ∑ m ∈ oddSquarefreeRange M, ω u *
          ‖quadraticDivisorBilinear N₁ N₂ 1
            (quadraticLogModulate u v) (quadraticLogModulate (-u) w) m‖ := by
        apply Finset.sum_le_sum
        intro m hm
        exact mul_le_mul_of_nonneg_right (hf m hm u) (norm_nonneg _)
      _ = ω u * ∑ m ∈ oddSquarefreeRange M,
          ‖quadraticDivisorBilinear N₁ N₂ 1
            (quadraticLogModulate u v) (quadraticLogModulate (-u) w) m‖ := by
        rw [Finset.mul_sum]
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (hω₀ u)
        simpa only [T, quadraticDivisorMoment_logModulate] using
          quadratic_unit_divisor_bound M N₁ N₂ K₁ K₂ hK₁ hK₂ h₁ h₂
            (quadraticLogModulate u v) (quadraticLogModulate (-u) w)
  calc
    _ ≤ ∑ m ∈ oddSquarefreeRange M, ∫ u : ℝ, G m u :=
      Finset.sum_le_sum (fun m _ => quadratic_log_weighted_norm (f m) N₁ N₂ 1 v w m)
    _ = ∫ u : ℝ, ∑ m ∈ oddSquarefreeRange M, G m u :=
      (integral_finsetSum _ (fun m _ => hI m)).symm
    _ ≤ ∫ u : ℝ, ω u * T := integral_mono hsum (hω.mul_const T) hb
    _ = _ := integral_mul_const T _

theorem quadratic_unit_varying_weighted_gauss_bound (f : ℕ → 𝓢(ℝ, ℂ))
    (ω : ℝ → ℝ) (hω : Integrable ω) (hω₀ : ∀ u, 0 ≤ ω u) (M N₁ N₂ : ℕ)
    (v w : ℕ → ℂ) (K₁ K₂ : ℝ) (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂)
    (h₁ : QuadraticSieveBound M N₁ K₁) (h₂ : QuadraticSieveBound M N₂ K₂)
    (hf : ∀ m ∈ oddSquarefreeRange M, ∀ u : ℝ, ‖𝓕 (f m) u‖ ≤ ω u) :
    (∑ m ∈ oddSquarefreeRange M, ‖quadraticLogWeightedGaussDivisor (f m) N₁ N₂ 1 v w m‖) ≤
      3 * (∫ u : ℝ, ω u) *
        (Real.sqrt (2 * K₁ * quadraticDivisorMoment N₁ v) *
          Real.sqrt (2 * K₂ * quadraticDivisorMoment N₂ w)) := by
  have hleft := quadratic_unit_varying_weighted_bound f ω hω hω₀ M N₁ N₂
    (quadraticGaussLeft v) (quadraticGaussRight w) K₁ K₂ hK₁ hK₂ h₁ h₂ hf
  simp only [quadraticDivisorMoment_gaussLeft, quadraticDivisorMoment_gaussRight] at hleft
  have hright := quadratic_unit_varying_weighted_bound f ω hω hω₀ M N₁ N₂
    (quadraticThreeClass (quadraticGaussLeft v))
    (quadraticThreeClass (quadraticGaussRight w)) K₁ K₂ hK₁ hK₂ h₁ h₂ hf
  have hright' : (∑ m ∈ oddSquarefreeRange M,
      ‖quadraticLogWeightedDivisor (f m) N₁ N₂ 1
        (quadraticThreeClass (quadraticGaussLeft v))
        (quadraticThreeClass (quadraticGaussRight w)) m‖) ≤
      (∫ u : ℝ, ω u) *
        (Real.sqrt (2 * K₁ * quadraticDivisorMoment N₁ v) *
          Real.sqrt (2 * K₂ * quadraticDivisorMoment N₂ w)) := by
    apply hright.trans
    apply mul_le_mul_of_nonneg_left _ (integral_nonneg hω₀)
    apply mul_le_mul _ _ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    · apply Real.sqrt_le_sqrt
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa only [quadraticDivisorMoment_gaussLeft] using
        quadraticDivisorMoment_threeClass N₁ (quadraticGaussLeft v)
    · apply Real.sqrt_le_sqrt
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa only [quadraticDivisorMoment_gaussRight] using
        quadraticDivisorMoment_threeClass N₂ (quadraticGaussRight w)
  calc
    _ ≤ ∑ m ∈ oddSquarefreeRange M,
        (‖quadraticLogWeightedDivisor (f m) N₁ N₂ 1 (quadraticGaussLeft v) (quadraticGaussRight w) m‖ +
        2 * ‖quadraticLogWeightedDivisor (f m) N₁ N₂ 1
          (quadraticThreeClass (quadraticGaussLeft v))
          (quadraticThreeClass (quadraticGaussRight w)) m‖) := by
      apply Finset.sum_le_sum
      intro m _
      rw [quadratic_log_weighted_gauss_split]
      exact (norm_sub_le _ _).trans (by norm_num [norm_mul])
    _ = (∑ m ∈ oddSquarefreeRange M,
        ‖quadraticLogWeightedDivisor (f m) N₁ N₂ 1 (quadraticGaussLeft v) (quadraticGaussRight w) m‖) +
        2 * ∑ m ∈ oddSquarefreeRange M, ‖quadraticLogWeightedDivisor (f m) N₁ N₂ 1
          (quadraticThreeClass (quadraticGaussLeft v))
          (quadraticThreeClass (quadraticGaussRight w)) m‖ := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    _ ≤ _ := by nlinarith [hleft, hright']

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticUnitRoot
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform root-kernel estimates at divisor one -/

namespace Ostmann

open MeasureTheory
open scoped Classical BigOperators SchwartzMap FourierTransform

theorem quadratic_unit_positive_root_gauss_bound (ρ : 𝓢(ℝ, ℂ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (M N : ℕ) (X : ℕ → ℝ), 0 < N →
      (∀ m ∈ oddSquarefreeRange M, 0 < X m) →
      ∀ (v w : ℕ → ℂ) (K₁ K₂ : ℝ), 0 ≤ K₁ → 0 ≤ K₂ →
      (∀ n < N, v n = 0) → (∀ n < N, w n = 0) →
      QuadraticSieveBound M (2 * N) K₁ → QuadraticSieveBound M (2 * N) K₂ →
      (∑ m ∈ oddSquarefreeRange M, ‖quadraticRootGaussDivisor ρ (X m) N 1 v w m‖) ≤
        C * (Real.sqrt (2 * K₁ * quadraticDivisorMoment (2 * N) v) *
          Real.sqrt (2 * K₂ * quadraticDivisorMoment (2 * N) w)) := by
  obtain ⟨C, hC, hc⟩ := quadratic_log_root_kernel_envelope ρ 0
  let J := ∫ u : ℝ, quadraticFourierEnvelope u
  have hJ : 0 ≤ J := integral_nonneg quadraticFourierEnvelope_nonneg
  refine ⟨3 * C * J, by positivity, ?_⟩
  intro M N X hN hX v w K₁ K₂ hK₁ hK₂ hv hw h₁ h₂
  let f := fun m => quadraticLogRootKernel ρ (X m) N
  let ω := fun u : ℝ => C * quadraticFourierEnvelope u
  have hω : Integrable ω := quadraticFourierEnvelope_integrable.const_mul C
  have hω₀ : ∀ u, 0 ≤ ω u := fun u => mul_nonneg hC (quadraticFourierEnvelope_nonneg u)
  have hf : ∀ m ∈ oddSquarefreeRange M, ∀ u : ℝ, ‖𝓕 (f m) u‖ ≤ ω u := by
    intro m hm u
    simpa only [pow_zero, div_one, min_self, mul_one] using
      hc N hN (X m) (X m) (hX m hm) le_rfl u
  have hbound := quadratic_unit_varying_weighted_gauss_bound f ω hω hω₀
    M (2 * N) (2 * N) v w K₁ K₂ hK₁ hK₂ h₁ h₂ hf
  have he : (∑ m ∈ oddSquarefreeRange M,
      ‖quadraticRootGaussDivisor ρ (X m) N 1 v w m‖) =
      ∑ m ∈ oddSquarefreeRange M,
        ‖quadraticLogWeightedGaussDivisor (f m) (2 * N) (2 * N) 1 v w m‖ := by
    apply Finset.sum_congr rfl
    intro m _
    rw [quadratic_root_gauss_divisor_eq ρ (X m) hN 1 v w m hv hw]
  rw [he]
  convert hbound using 1
  all_goals try with_reducible_and_instances rfl
  dsimp only [ω, J]
  rw [integral_const_mul]
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticUnitMiddle
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original middle-frequency window including the unit divisor -/

namespace Ostmann

open scoped Classical BigOperators SchwartzMap FourierTransform

theorem quadratic_unit_middle_divisor_bound (ρ : 𝓢(ℝ, ℂ)) (a : ℝ) (ha : 1 ≤ |a|) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (M : ℝ) (e B N : ℕ), 0 < M → 0 < e → 0 < N →
      ∀ (l : ℤ), l ≠ 0 → ∀ (v w : ℕ → ℂ) (K₁ K₂ : ℝ), 0 ≤ K₁ → 0 ≤ K₂ →
      (∀ n < N, v n = 0) → (∀ n < N, w n = 0) →
      QuadraticSieveBound B (2 * N) K₁ → QuadraticSieveBound B (2 * N) K₂ →
      (∑ b ∈ oddSquarefreeRange B, ‖quadraticMiddleDivisor ρ a ha M e N 1 v w b l‖) ≤
        C * (Real.sqrt (2 * K₁ * quadraticDivisorMoment (2 * N) v) *
          Real.sqrt (2 * K₂ * quadraticDivisorMoment (2 * N) w)) := by
  obtain ⟨C, hC, hc⟩ := quadratic_unit_positive_root_gauss_bound (𝓕 (quadraticFourierSquare ρ a ha))
  refine ⟨C, hC, ?_⟩
  intro M e B N hM he hN l hl v w K₁ K₂ hK₁ hK₂ hv hw h₁ h₂
  let X := fun b : ℕ => (l.natAbs : ℝ) / 1 * Real.sqrt ((e : ℝ) / (M * b))
  have hX : ∀ b ∈ oddSquarefreeRange B, 0 < X b := by
    intro b hb
    have hb₀ : 0 < b := (Finset.mem_Icc.mp (Finset.mem_filter.mp hb).1).1
    simpa only [X, Nat.cast_one] using
      quadratic_middle_parameter_pos hM he hb₀ (show 0 < (1 : ℕ) by decide) hl
  have hbound := hc B N X hN hX v w K₁ K₂ hK₁ hK₂ hv hw h₁ h₂
  apply le_trans (le_of_eq ?_) hbound
  apply Finset.sum_congr rfl
  intro b hb
  have hb₀ : 0 < b := (Finset.mem_Icc.mp (Finset.mem_filter.mp hb).1).1
  rw [quadratic_middle_divisor_eq ρ a ha hM he hb₀]
  simp only [X, Nat.cast_one]

theorem quadratic_unit_middle_window_bound (ρ : 𝓢(ℝ, ℂ)) (a : ℝ) (ha : 1 ≤ |a|) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (M : ℝ) (e B N : ℕ), 0 < M → 0 < e → 0 < N →
      ∀ (L : ℕ) (v w : ℕ → ℂ) (K₁ K₂ : ℝ), 0 ≤ K₁ → 0 ≤ K₂ →
      (∀ n < N, v n = 0) → (∀ n < N, w n = 0) →
      QuadraticSieveBound B (2 * N) K₁ → QuadraticSieveBound B (2 * N) K₂ →
      (∑ b ∈ oddSquarefreeRange B, ‖quadraticMiddleWindow ρ a ha M e N 1 v w b L‖) ≤
        (2 * L + 1) * C * (Real.sqrt (2 * K₁ * quadraticDivisorMoment (2 * N) v) *
          Real.sqrt (2 * K₂ * quadraticDivisorMoment (2 * N) w)) := by
  obtain ⟨C, hC, hc⟩ := quadratic_unit_middle_divisor_bound ρ a ha
  refine ⟨C, hC, ?_⟩
  intro M e B N hM he hN L v w K₁ K₂ hK₁ hK₂ hv hw h₁ h₂
  let T := Real.sqrt (2 * K₁ * quadraticDivisorMoment (2 * N) v) *
    Real.sqrt (2 * K₂ * quadraticDivisorMoment (2 * N) w)
  let U := Finset.Icc (-(L : ℤ)) L
  let f := fun (l : ℤ) (b : ℕ) =>
    if l = 0 then (0 : ℝ) else ‖quadraticMiddleDivisor ρ a ha M e N 1 v w b l‖
  have hpoint (l : ℤ) : (∑ b ∈ oddSquarefreeRange B, f l b) ≤ C * T := by
    by_cases hl : l = 0
    · simp only [f, hl, ite_true, if_true, Finset.sum_const_zero]
      dsimp [T]; positivity
    · simpa only [f, hl, ite_false, if_false] using
        hc M e B N hM he hN l hl v w K₁ K₂ hK₁ hK₂ hv hw h₁ h₂
  have hcard : U.card = 2 * L + 1 := by
    dsimp only [U]
    rw [Int.card_Icc]
    omega
  calc
    _ ≤ ∑ b ∈ oddSquarefreeRange B, ∑ l ∈ U, f l b := by
      apply Finset.sum_le_sum
      intro b _
      rw [quadratic_middle_window_eq]
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro l _
      by_cases hl : l = 0 <;> simp [f, hl]
    _ = ∑ l ∈ U, ∑ b ∈ oddSquarefreeRange B, f l b := Finset.sum_comm
    _ ≤ ∑ _l ∈ U, C * T := Finset.sum_le_sum (fun l _ => hpoint l)
    _ = _ := by
      rw [Finset.sum_const, nsmul_eq_mul, hcard]
      push_cast
      ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticUnitCorrectionBounds
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Filtered boundary corrections retain the full frequency comparison -/

namespace Ostmann

open scoped Classical BigOperators

theorem quadratic_filtered_unit_bound (B : ℕ) (P : ℕ → Prop) [DecidablePred P]
    (c F : ℕ → ℂ) {A : ℝ} (hA : 0 ≤ A)
    (hc : ∀ b ∈ oddSquarefreeRange (2 * B), B ≤ b → P b → ‖c b‖ ≤ A) :
    ‖∑ b ∈ oddSquarefreeRange (2 * B), if B ≤ b ∧ P b then c b * F b else 0‖ ≤
      A * ∑ b ∈ oddSquarefreeRange (2 * B), ‖F b‖ := by
  calc
    _ ≤ ∑ b ∈ oddSquarefreeRange (2 * B), A * ‖F b‖ := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro b hb
      split_ifs with h
      · rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hc b hb h.1 h.2) (norm_nonneg _)
      · rw [norm_zero]
        exact mul_nonneg hA (norm_nonneg _)
    _ = _ := by rw [Finset.mul_sum]

theorem quadratic_filtered_unit_root_weight (B d : ℕ) (hB : 0 < B) (hd : 0 < d)
    (P : ℕ → Prop) [DecidablePred P] (F : ℕ → ℂ) :
    ‖∑ b ∈ oddSquarefreeRange (2 * B), if B ≤ b ∧ P b then
        (((ArithmeticFunction.moebius d : ℂ) / d) / (Real.sqrt b : ℂ)) * F b else 0‖ ≤
      (1 / ((d : ℝ) * Real.sqrt B)) * ∑ b ∈ oddSquarefreeRange (2 * B), ‖F b‖ := by
  apply quadratic_filtered_unit_bound B P _ F (by positivity)
  intro b _ hb _
  exact quadratic_moebius_root_weight hd hB le_rfl hb

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticUnitCorrectionGrowth
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The missing unit-divisor endpoint has the same normalized growth rate -/

namespace Ostmann

open scoped Classical BigOperators

theorem quadratic_growth_unit_cost {C ε ξ : ℝ} (hC : 0 ≤ C)
    (B N : ℕ) (v w : ℕ → ℂ) :
    Real.sqrt (2 * quadraticGrowthCutoff C ε ξ B N 0 * quadraticDivisorMoment N v) *
      Real.sqrt (2 * quadraticGrowthCutoff C ε ξ B N 0 * quadraticDivisorMoment N w) ≤
        quadraticGrowthDivisorBudget C ε ξ B N 1 v w := by
  simpa only [pow_zero, Nat.cast_one, mul_one] using
    quadratic_growth_cutoff_cost hC (show 0 < (1 : ℕ) by decide) v w
      (i := 0) (j := 0) (by norm_num)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticUnitMiddleGrowth
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The normalized middle correction at the divisor-one boundary -/

namespace Ostmann

open scoped Classical BigOperators SchwartzMap

theorem quadratic_middle_unit_growth (ρ : 𝓢(ℝ, ℂ)) (a : ℝ) (ha : 1 ≤ |a|) :
    ∃ Cρ : ℝ, 0 ≤ Cρ ∧ ∀ C ε ξ M J : ℝ, 0 ≤ C →
      ∀ e B N L : ℕ, 0 < M → 0 < e → 0 < B → 0 < N → 1 ≤ J →
      quadraticCorrectionBase M N e B / (8 * J) ≤ 1 →
      ∀ P : ℕ → Prop, ∀ v w : ℕ → ℂ,
      (∀ n < N, v n = 0) → (∀ n < N, w n = 0) →
      QuadraticSieveBound (2 * B) (2 * N) (quadraticGrowthCutoff C ε ξ (2 * B) (2 * N) 0) →
      ‖((Real.sqrt M / Real.sqrt e : ℝ) : ℂ) *
          quadraticMiddleCorrectionUnit ρ a ha M e B N L P v w‖ ≤
        128 * J * (2 * L + 1) * Cρ * quadraticCorrectionGrowthScale C ε ξ M e B N v w := by
  classical
  obtain ⟨Cρ, hCρ, hcρ⟩ := quadratic_unit_middle_window_bound ρ a ha
  refine ⟨Cρ, hCρ, ?_⟩
  intro C ε ξ M J hC e B N L hM he hB hN hJ hcut P v w hv hw hmat
  let T := quadraticGrowthDivisorBudget C ε ξ (2 * B) (2 * N) 1 v w
  let K := quadraticGrowthCutoff C ε ξ (2 * B) (2 * N) 0
  have hK : 0 ≤ K := quadratic_growth_cutoff_nonneg hC _ _ _
  have hroot := quadratic_growth_unit_cost (ε := ε) (ξ := ξ) hC (2 * B) (2 * N) v w
  have hl : ‖quadraticMiddleCorrectionUnit ρ a ha M e B N L P v w‖ ≤
      ((2 * L + 1) * Cρ * T) / Real.sqrt B := by
    have hf := quadratic_filtered_unit_root_weight B 1 hB (by decide) P
      (fun b => quadraticMiddleWindow ρ a ha M e N 1 v w b L)
    have hu := (hcρ M e (2 * B) N hM he hN L v w K K hK hK hv hw hmat hmat).trans
      (mul_le_mul_of_nonneg_left hroot (show 0 ≤ (2 * L + 1 : ℝ) * Cρ by positivity))
    have hf' : ‖quadraticMiddleCorrectionUnit ρ a ha M e B N L P v w‖ ≤
        (1 / Real.sqrt B) * ∑ b ∈ oddSquarefreeRange (2 * B),
          ‖quadraticMiddleWindow ρ a ha M e N 1 v w b L‖ := by
      simpa [quadraticMiddleCorrectionUnit] using hf
    exact hf'.trans (by simpa [T, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      mul_le_mul_of_nonneg_left hu (show 0 ≤ 1 / Real.sqrt (B : ℝ) by positivity))
  have hb := quadratic_first_high_budget hM (show (0 : ℝ) < N by exact_mod_cast hN)
    he hB (show 0 < (1 : ℕ) by decide) hJ
    (show 0 ≤ C * (((2 * B : ℕ) : ℝ) * (2 * N : ℕ)) ^ ε by positivity)
    (show 0 ≤ ((2 * B : ℕ) : ℝ) ^ ξ by positivity)
    (show 0 ≤ Real.sqrt (quadraticDivisorMoment (2 * N) v) *
      Real.sqrt (quadraticDivisorMoment (2 * N) w) by positivity) (by simpa using hcut)
  have hb' : (Real.sqrt M / (Real.sqrt e * Real.sqrt B)) * T ≤
      128 * J * quadraticCorrectionGrowthScale C ε ξ M e B N v w := by
    simpa only [T, quadraticGrowthDivisorBudget, quadraticCorrectionGrowthScale,
      Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, mul_one, mul_assoc] using hb
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  apply (mul_le_mul_of_nonneg_left hl (by positivity)).trans
  calc
    _ = ((2 * L + 1) * Cρ) * (Real.sqrt M / (Real.sqrt e * Real.sqrt B) * T) := by ring
    _ ≤ ((2 * L + 1) * Cρ) * (128 * J * quadraticCorrectionGrowthScale C ε ξ M e B N v w) :=
      mul_le_mul_of_nonneg_left hb' (by positivity)
    _ = _ := by ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticWholeMiddleGrowth
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The complete middle-divisor correction, with the unit boundary retained -/

namespace Ostmann

open scoped Classical BigOperators SchwartzMap

theorem quadratic_whole_middle_growth (ρ : 𝓢(ℝ, ℂ)) (a : ℝ) (ha : 1 ≤ |a|) :
    ∃ Cu Cb : ℝ, 0 ≤ Cu ∧ 0 ≤ Cb ∧ ∀ C ε ξ M J : ℝ, 0 ≤ C →
      ∀ e B N Q L : ℕ, 0 < M → 0 < e → 0 < B → 0 < N → 1 ≤ Q → 1 ≤ J →
      ∀ P : ℕ → ℕ → Prop, ∀ v w : ℕ → ℂ,
      (∀ n < N, v n = 0) → (∀ n < N, w n = 0) →
      (∀ d ∈ Finset.Icc 1 Q, ∀ b ∈ oddSquarefreeRange (2 * B), B ≤ b → P d b →
        quadraticCorrectionBase M N e B / (4 * J) ≤ (d : ℝ)) →
      (∀ i ≤ Nat.log 2 (2 * N), QuadraticSieveBound (2 * B) (2 * N / 2 ^ i)
        (quadraticGrowthCutoff C ε ξ (2 * B) (2 * N) i)) →
      ‖((Real.sqrt M / Real.sqrt e : ℝ) : ℂ) *
          quadraticMiddleCorrectionTotal ρ a ha M e B N Q L P v w‖ ≤
        (128 * J * (2 * L + 1) * ((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ) ^ 2 *
          quadraticCorrectionGrowthScale C ε ξ M e B N v w) *
            (Cu + ((Nat.log 2 Q + 1 : ℕ) : ℝ) * Cb) := by
  classical
  obtain ⟨Cu, hCu, hcU⟩ := quadratic_middle_unit_growth ρ a ha
  obtain ⟨Cb, hCb, hcB⟩ := quadratic_middle_band_growth ρ a ha
  refine ⟨Cu, Cb, hCu, hCb, ?_⟩
  intro C ε ξ M J hC e B N Q L hM he hB hN hQ hJ P v w hv hw hP hmat
  let S := quadraticCorrectionGrowthScale C ε ξ M e B N v w
  let U := 128 * J * (2 * L + 1) * Cu * ((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ) ^ 2 * S
  let V := 128 * J * (2 * L + 1) * Cb * ((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ) ^ 2 * S
  let F := fun d => ((Real.sqrt M / Real.sqrt e : ℝ) : ℂ) *
    ∑ b ∈ oddSquarefreeRange (2 * B), if B ≤ b ∧ P d b then
      (((ArithmeticFunction.moebius d : ℂ) / d) / (Real.sqrt b : ℂ)) *
        quadraticMiddleWindow ρ a ha M e N d v w b L else 0
  have hS : 0 ≤ S := by dsimp [S, quadraticCorrectionGrowthScale]; positivity
  have hU : 0 ≤ U := by dsimp [U]; positivity
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hlog : (1 : ℝ) ≤ ((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ) ^ 2 := by
    have hh : (1 : ℝ) ≤ ((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_left 1 _
    nlinarith
  have hunit : ‖F 1‖ ≤ U := by
    by_cases hc : quadraticCorrectionBase M N e B / (8 * J) ≤ 1
    · have hu := hcU C ε ξ M J hC e B N L hM he hB hN hJ hc (P 1) v w hv hw
        (by simpa only [pow_zero, Nat.div_one] using hmat 0 (Nat.zero_le _))
      have heq : F 1 = ((Real.sqrt M / Real.sqrt e : ℝ) : ℂ) * quadraticMiddleCorrectionUnit ρ a ha M e B N L (P 1) v w := by
        simp [F, quadraticMiddleCorrectionUnit]
      rw [heq]
      apply hu.trans
      change 128 * J * (2 * L + 1) * Cu * S ≤ U
      dsimp [U]
      nlinarith [mul_le_mul_of_nonneg_left hlog
        (show 0 ≤ 128 * J * (2 * L + 1) * Cu * S by positivity)]
    · have hz : F 1 = 0 := by
        dsimp [F]
        have hh : (∑ b ∈ oddSquarefreeRange (2 * B), if B ≤ b ∧ P 1 b then
            (((ArithmeticFunction.moebius 1 : ℂ) / 1) / (Real.sqrt b : ℂ)) *
              quadraticMiddleWindow ρ a ha M e N 1 v w b L else 0) = 0 := by
          apply Finset.sum_eq_zero
          intro b hb
          have hn : ¬ (B ≤ b ∧ P 1 b) := by
            intro h
            apply hc
            have hh := hP 1 (Finset.mem_Icc.mpr ⟨le_rfl, hQ⟩) b hb h.1 h.2
            have hid : quadraticCorrectionBase M N e B / (8 * J) =
                (quadraticCorrectionBase M N e B / (4 * J)) / 2 := by ring
            rw [hid]
            norm_num only [Nat.cast_one] at hh
            linarith
          simp only [hn, ite_false, if_false]
        simp only [Nat.cast_one]
        rw [hh, mul_zero]
      rw [hz, norm_zero]
      exact hU
  have hblock (j : ℕ) (_hj : j < Nat.log 2 Q + 1) :
      ‖∑ d ∈ Finset.Ioc (2 ^ j) (2 * 2 ^ j), if d ≤ Q then F d else 0‖ ≤ V := by
    let D := 2 ^ j
    let P' := fun d b => d ≤ Q ∧ P d b
    have heq : (∑ d ∈ Finset.Ioc D (2 * D), if d ≤ Q then F d else 0) =
        ((Real.sqrt M / Real.sqrt e : ℝ) : ℂ) * quadraticMiddleCorrectionBand ρ a ha M e B N D L P' v w := by
      simp only [quadraticMiddleCorrectionBand, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d _
      dsimp only [F, P']
      by_cases hd : d ≤ Q
      · simp only [hd, ite_true, if_true, true_and, Finset.mul_sum]
      · simp only [hd, ite_false, if_false, false_and, and_false, Finset.sum_const_zero, mul_zero]
    change ‖∑ d ∈ Finset.Ioc D (2 * D), if d ≤ Q then F d else 0‖ ≤ V
    rw [heq]
    by_cases hc : quadraticCorrectionBase M N e B / (8 * J) ≤ (D : ℝ)
    · exact hcB C ε ξ M J hC e B N D L hM he hB hN
        (by dsimp [D]; positivity) hJ hc P' v w hv hw hmat
    · have hz : quadraticMiddleCorrectionBand ρ a ha M e B N D L P' v w = 0 := by
        unfold quadraticMiddleCorrectionBand
        apply Finset.sum_eq_zero
        intro d hd
        apply Finset.sum_eq_zero
        intro b hb
        have hn : ¬ (B ≤ b ∧ P' d b) := by
          intro h
          have hdp := (Finset.mem_Ioc.mp hd).1
          have hbound := hP d (Finset.mem_Icc.mpr ⟨Nat.succ_le_of_lt ((Nat.zero_le D).trans_lt hdp), h.2.1⟩) b hb h.1 h.2.2
          apply hc
          have hhi : (d : ℝ) ≤ 2 * D := by exact_mod_cast (Finset.mem_Ioc.mp hd).2
          calc
            _ = (quadraticCorrectionBase M N e B / (4 * J)) / 2 := by ring
            _ ≤ (d : ℝ) / 2 := div_le_div_of_nonneg_right hbound (by norm_num)
            _ ≤ D := by linarith
        simp only [hn, ite_false, if_false]
      rw [hz, mul_zero, norm_zero]
      exact hV
  have hb := quadratic_correction_divisor_bound hQ F U (fun _ => V) hunit hblock
  have heq : (∑ d ∈ Finset.Icc 1 Q, F d) =
      ((Real.sqrt M / Real.sqrt e : ℝ) : ℂ) * quadraticMiddleCorrectionTotal ρ a ha M e B N Q L P v w := by
    simp only [F, quadraticMiddleCorrectionTotal, Finset.mul_sum]
  rw [heq] at hb
  apply hb.trans_eq
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  dsimp [U, V, S]
  push_cast
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticOriginalCutoffGrowth
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The complete bounds apply to the literal rounded Poisson cutoffs -/

namespace Ostmann

open scoped Classical BigOperators

theorem quadratic_original_lower_cut {M H N J : ℝ} {e B b d : ℕ}
    (hM : 0 < M) (hH : 0 < H) (hN : 0 < N) (hNH : N ≤ 2 * H)
    (he : 0 < e) (hB : 0 < B) (hJ : 1 ≤ J) (hb : B ≤ b) (hb' : b ≤ 2 * B)
    (hcut : quadraticSecondLower (quadraticCorrectionBase M H e b) J < (d : ℝ)) :
    quadraticCorrectionBase M N e B / (4 * (2 * J)) ≤ (d : ℝ) := by
  have hlo := (quadratic_correction_cutoff_band hM hH he hB hJ hb hb').1
  have hdouble := quadratic_correction_base_double hM hH hN hNH he hB
  calc
    _ ≤ (2 * quadraticCorrectionBase M H e B) / (4 * (2 * J)) := by gcongr
    _ = quadraticCorrectionBase M H e B / (4 * J) := by ring
    _ ≤ quadraticSecondLower (quadraticCorrectionBase M H e b) J := hlo
    _ ≤ d := hcut.le

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticOriginalMiddleGrowth
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Every full correction uses its original frequency-dependent cutoff -/

namespace Ostmann

open scoped Classical BigOperators SchwartzMap

theorem quadratic_whole_original_middle_growth (ρ : 𝓢(ℝ, ℂ)) (a : ℝ) (ha : 1 ≤ |a|) :
    ∃ Cu Cb : ℝ, 0 ≤ Cu ∧ 0 ≤ Cb ∧ ∀ C ε ξ M H J : ℝ, 0 ≤ C →
      ∀ e B N Q L : ℕ, 0 < M → 0 < H → (N : ℝ) ≤ 2 * H →
      0 < e → 0 < B → 0 < N → 1 ≤ Q → 1 ≤ J →
      ∀ R : ℕ → ℕ → Prop, ∀ v w : ℕ → ℂ,
      (∀ n < N, v n = 0) → (∀ n < N, w n = 0) →
      (∀ i ≤ Nat.log 2 (2 * N), QuadraticSieveBound (2 * B) (2 * N / 2 ^ i)
        (quadraticGrowthCutoff C ε ξ (2 * B) (2 * N) i)) →
      ‖((Real.sqrt M / Real.sqrt e : ℝ) : ℂ) *
          quadraticMiddleCorrectionTotal ρ a ha M e B N Q L
            (fun d b => R d b ∧ quadraticSecondLower (quadraticCorrectionBase M H e b) J < (d : ℝ) ∧
              (d : ℝ) ≤ quadraticSecondUpper (quadraticCorrectionBase M H e b) J) v w‖ ≤
        (128 * (2 * J) * (2 * L + 1) * ((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ) ^ 2 *
          quadraticCorrectionGrowthScale C ε ξ M e B N v w) *
            (Cu + ((Nat.log 2 Q + 1 : ℕ) : ℝ) * Cb) := by
  obtain ⟨Cu, Cb, hCu, hCb, hc⟩ := quadratic_whole_middle_growth ρ a ha
  refine ⟨Cu, Cb, hCu, hCb, ?_⟩
  intro C ε ξ M H J hC e B N Q L hM hH hNH he hB hN hQ hJ R v w hv hw hmat
  apply hc C ε ξ M (2 * J) hC e B N Q L hM he hB hN hQ (by linarith) _ v w hv hw _ hmat
  intro d _ b hb hbB hp
  exact quadratic_original_lower_cut hM hH (by exact_mod_cast hN) hNH he hB hJ hbB
    (Finset.mem_Icc.mp (Finset.mem_filter.mp hb).1).2 hp.2.1

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticFullMiddleGrowth
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The entire original middle correction at the current sieve exponent -/

namespace Ostmann

open scoped Classical BigOperators SchwartzMap

theorem quadratic_full_middle_growth_oai (ρ : 𝓢(ℝ, ℂ)) (a : ℝ) (ha : 1 ≤ |a|) :
    ∃ Cu Cb : ℝ, 0 ≤ Cu ∧ 0 ≤ Cb ∧ ∀ C ε ξ M H J : ℝ,
      0 ≤ C → 0 ≤ ε → 1 / 2 ≤ ξ → ξ ≤ 2 → ∀ e N Q K L : ℕ,
      0 < M → 0 < H → (N : ℝ) ≤ 2 * H → 0 < e →
      0 < N → 1 ≤ Q → 0 < K → 1 ≤ J →
      ∀ R : ℕ → ℕ → Prop, ∀ v w : ℕ → ℂ,
      (∀ n < N, v n = 0) → (∀ n < N, w n = 0) →
      (∀ B : ℕ, 0 < B → B ≤ K → ∀ i ≤ Nat.log 2 (2 * N),
        QuadraticSieveBound (2 * B) (2 * N / 2 ^ i)
          (quadraticGrowthCutoff C ε ξ (2 * B) (2 * N) i)) →
      ‖((Real.sqrt M / Real.sqrt e : ℝ) : ℂ) *
          quadraticFullMiddleCorrection ρ a ha M H J e N Q K L R v w‖ ≤
        ((Nat.log 2 K + 1 : ℕ) : ℝ) *
          ((128 * (2 * J) * (2 * L + 1) * ((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ) ^ 2 *
            (10 * C * (4 * (K : ℝ) * N) ^ ε *
              (M + Real.sqrt M * (K : ℝ) ^ (ξ - 1 / 2)) *
                (Real.sqrt (quadraticDivisorMoment (2 * N) v) *
                  Real.sqrt (quadraticDivisorMoment (2 * N) w)))) *
                    (Cu + ((Nat.log 2 Q + 1 : ℕ) : ℝ) * Cb)) := by
  classical
  obtain ⟨Cu, Cb, hCu, hCb, hc⟩ := quadratic_whole_original_middle_growth ρ a ha
  refine ⟨Cu, Cb, hCu, hCb, ?_⟩
  intro C ε ξ M H J hC hε hξ hξ' e N Q K L hM hH hNH he hN hQ hK hJ R v w hv hw hmat
  apply quadratic_correction_frequency_bound
  intro i hi
  let B := 2 ^ i
  have hB : 0 < B := by dsimp [B]; positivity
  have hBK : B ≤ K := quadratic_frequency_block_le hK hi
  let R' := fun d b => b ≤ K ∧ b < 2 * B ∧ R d b
  have heq : (∑ d ∈ Finset.Icc 1 Q, ∑ b ∈ oddSquarefreeRange (2 * B),
      if B ≤ b ∧ b ≤ K ∧ b < 2 * B then
        (if R d b ∧ quadraticSecondLower (quadraticCorrectionBase M H e b) J < (d : ℝ) ∧
        (d : ℝ) ≤ quadraticSecondUpper (quadraticCorrectionBase M H e b) J then
          (((ArithmeticFunction.moebius d : ℂ) / d) / (Real.sqrt b : ℂ)) *
            quadraticMiddleWindow ρ a ha M e N d v w b L else 0) else 0) =
      quadraticMiddleCorrectionTotal ρ a ha M e B N Q L
        (fun d b => R' d b ∧ quadraticSecondLower (quadraticCorrectionBase M H e b) J < (d : ℝ) ∧
          (d : ℝ) ≤ quadraticSecondUpper (quadraticCorrectionBase M H e b) J) v w := by
    unfold quadraticMiddleCorrectionTotal
    apply Finset.sum_congr rfl
    intro d _
    apply Finset.sum_congr rfl
    intro b _
    dsimp [R']
    by_cases h₁ : B ≤ b <;> by_cases h₂ : b ≤ K <;> by_cases h₃ : b < 2 * B <;>
      simp [h₁, h₂, h₃]
  change ‖((Real.sqrt M / Real.sqrt e : ℝ) : ℂ) * _‖ ≤ _
  rw [heq]
  apply (hc C ε ξ M H J hC e B N Q L hM hH hNH he hB hN hQ hJ R' v w hv hw
    (hmat B hB hBK)).trans
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
    (quadratic_correction_growth_uniform hC hε hξ hξ' hM he hB hBK le_rfl v w)
      (show 0 ≤ 128 * (2 * J) * (2 * L + 1) * ((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ) ^ 2 by positivity))
        (by positivity)

end Ostmann

end OAI
end

theorem solution : type_of% @OAI.Ostmann.quadratic_full_middle_growth_oai := @OAI.Ostmann.quadratic_full_middle_growth_oai
