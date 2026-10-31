-- Prove2me | solution 1 for OAI.Ostmann.quadratic_first_total_growth
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T06:48:09.961525+00:00
-- url     : https://prove2.me/submissions/2757422c-ea94-4a4b-9aee-491a15e0696c

import Mathlib
import Definitions.Def_OAIQ095D003
import Definitions.Def_OAIQ095D005
import Theorems.Thm_OAI_Ostmann_quadratic_full_middle_growth

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

omit [DecidableEq ι] in
 theorem complex_self_quadratic (u : ι → ℂ) :
    star u ⬝ᵥ u = ((∑ s, ‖u s‖ ^ 2 : ℝ) : ℂ) := by
  simp only [dotProduct, Pi.star_apply, Complex.ofReal_sum, Complex.ofReal_pow]
  apply Finset.sum_congr rfl
  intro s _
  simpa only [Complex.star_def] using Complex.conj_mul' (u s)

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
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticAmplificationBias
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A fixed quadratic bias produces a large shared coefficient test -/

namespace Ostmann

open scoped BigOperators Classical

theorem norm_jacobi_complex_le (u : ℤ) (p : ℕ) : ‖(jacobiSym u p : ℂ)‖ ≤ 1 := by
  rcases jacobiSym.trichotomy u p with h | h | h <;> simp [h]

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

 theorem quadraticPairKernel_squarefree {n₁ n₂ : ℕ}
    (h₁ : Squarefree n₁) (h₂ : Squarefree n₂) :
    Squarefree (quadraticPairKernel n₁ n₂) := by
  apply (Nat.squarefree_mul (Nat.coprime_div_gcd_div_gcd
    (Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero h₁.ne_zero)))).mpr
  exact ⟨h₁.squarefree_of_dvd (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left n₁ n₂)),
    h₂.squarefree_of_dvd (Nat.div_dvd_of_dvd (Nat.gcd_dvd_right n₁ n₂))⟩

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

 theorem QuadraticSieveBound.mono_constant {M N : ℕ} {K L : ℝ}
    (h : QuadraticSieveBound M N K) (hKL : K ≤ L) : QuadraticSieveBound M N L := by
  intro b
  exact (h b).trans (mul_le_mul_of_nonneg_right hKL
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))

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

 theorem quadratic_gauss_divisor_bilinear_split (N₁ N₂ d : ℕ)
    (a b : ℕ → ℂ) (m : ℤ) :
    quadraticGaussDivisorBilinear N₁ N₂ d a b m =
      quadraticDivisorBilinear N₁ N₂ d (quadraticGaussLeft a) (quadraticGaussRight b) m -
      2 * quadraticDivisorBilinear N₁ N₂ d
        (quadraticThreeClass (quadraticGaussLeft a))
        (quadraticThreeClass (quadraticGaussRight b)) m := by
  unfold quadraticGaussDivisorBilinear quadraticDivisorBilinear
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

 theorem quadratic_frequency_coeff (a : ℤ) (c : ℕ) (m : ℤ)
    (v : ℕ → ℂ) {n : ℕ} (hn : n ≠ 0) :
    v n * (jacobiSym (a * (c : ℤ) ^ 2 * m) n : ℂ) =
      quadraticFrequencyTwist a c v n * (jacobiSym m n : ℂ) := by
  rw [quadratic_frequency_character a c m hn]
  unfold quadraticFrequencyTwist
  split_ifs <;> ring

 theorem quadratic_frequency_conj_coeff (a : ℤ) (c : ℕ) (m : ℤ)
    (v : ℕ → ℂ) {n : ℕ} (hn : n ≠ 0) :
    conj (v n) * (jacobiSym (a * (c : ℤ) ^ 2 * m) n : ℂ) =
      conj (quadraticFrequencyTwist a c v n) * (jacobiSym m n : ℂ) := by
  simpa only [map_mul, map_intCast] using
    congrArg conj (quadratic_frequency_coeff a c m v hn)

 theorem quadraticFrequencyTwist_norm (a : ℤ) (c : ℕ) (v : ℕ → ℂ) (n : ℕ) :
    ‖quadraticFrequencyTwist a c v n‖ ≤ ‖v n‖ := by
  unfold quadraticFrequencyTwist
  split_ifs
  · rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right (norm_jacobi_complex_le a n) (norm_nonneg _)).trans_eq
      (one_mul _)
  · simp

 theorem quadraticFrequencyTwist_moment (a : ℤ) (c N : ℕ) (v : ℕ → ℂ) :
    quadraticDivisorMoment N (quadraticFrequencyTwist a c v) ≤ quadraticDivisorMoment N v := by
  apply Finset.sum_le_sum
  intro n _
  gcongr
  exact quadraticFrequencyTwist_norm a c v n

 theorem quadraticFrequencyTwist_zero (a : ℤ) (c : ℕ) (v : ℕ → ℂ) {n : ℕ}
    (hn : v n = 0) : quadraticFrequencyTwist a c v n = 0 := by
  simp [quadraticFrequencyTwist, hn]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticSqrtCoefficients
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual square-root denominator in the first Poisson comparison -/

namespace Ostmann

open scoped Classical BigOperators

 theorem quadraticSqrtNormalize_norm_sq (v : ℕ → ℂ) (n : ℕ) :
    ‖quadraticSqrtNormalize v n‖ ^ 2 = ‖v n‖ ^ 2 / (n : ℝ) := by
  rw [quadraticSqrtNormalize, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), div_pow, Real.sq_sqrt (Nat.cast_nonneg n)]

 theorem quadraticSqrtNormalize_moment (N R : ℕ) (hN : 0 < N) (v : ℕ → ℂ)
    (hv : ∀ n < N, v n = 0) :
    quadraticDivisorMoment R (quadraticSqrtNormalize v) ≤ quadraticDivisorMoment R v / N := by
  unfold quadraticDivisorMoment
  rw [Finset.sum_div]
  apply Finset.sum_le_sum
  intro n _
  rw [quadraticSqrtNormalize_norm_sq, ← mul_div_assoc]
  by_cases hn : n < N
  · simp [hv n hn]
  · apply div_le_div_of_nonneg_left (by positivity) (by exact_mod_cast hN)
    exact_mod_cast (Nat.le_of_not_gt hn)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticBilinearTwist
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual signed frequencies in the full correction matrices -/

namespace Ostmann

open scoped Classical BigOperators ComplexConjugate

theorem quadratic_gauss_bilinear_twist (N₁ N₂ d : ℕ) (v w : ℕ → ℂ) (u m : ℤ) :
    quadraticGaussDivisorBilinear N₁ N₂ d v w (u * m) =
      quadraticGaussDivisorBilinear N₁ N₂ d
        (quadraticFrequencyTwist u 1 v) (quadraticFrequencyTwist u 1 w) m := by
  unfold quadraticGaussDivisorBilinear
  apply Finset.sum_congr rfl
  intro s hs
  apply Finset.sum_congr rfl
  intro t ht
  have h₁ := quadratic_frequency_coeff u 1 m v (Finset.mem_filter.mp hs).2.2.ne_zero
  have h₂ := quadratic_frequency_conj_coeff u 1 m w (Finset.mem_filter.mp ht).2.2.ne_zero
  simp only [Nat.cast_one, one_pow, mul_one] at h₁ h₂
  calc
    _ = (if s.Coprime t ∧ d ∣ s * t then (1 : ℂ) else 0) *
        (v s * (jacobiSym (u * m) s : ℂ)) * (conj (w t) * (jacobiSym (u * m) t : ℂ)) *
          quadraticGaussMultiplier (s * t) := by ring
    _ = _ := by rw [h₁, h₂]; ring

theorem quadratic_sqrt_twist_commute (u : ℤ) (v : ℕ → ℂ) :
    quadraticFrequencyTwist u 1 (quadraticSqrtNormalize v) =
      quadraticSqrtNormalize (quadraticFrequencyTwist u 1 v) := by
  funext n
  simp [quadraticFrequencyTwist, quadraticSqrtNormalize, div_eq_mul_inv, mul_assoc]

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

theorem quadratic_low_weight_balance {M H J : ℝ} {e B D : ℕ}
    (hM : 0 < M) (hH : 0 < H) (he : 0 < e) (hB : 0 < B) (hD : 0 < D)
    (hJ : 1 ≤ J) (hcut : (D : ℝ) ≤ 2 * quadraticCorrectionBase M H e B * J) :
    M / ((e : ℝ) * H) ≤
      2 * J * min (M / ((e : ℝ) * H))
        (Real.sqrt M / (Real.sqrt e * Real.sqrt B * D)) := by
  let α := M / ((e : ℝ) * H)
  let β := Real.sqrt M / (Real.sqrt e * Real.sqrt B)
  have hα : 0 ≤ α := by dsimp [α]; positivity
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have hi : α * quadraticCorrectionBase M H e B = β :=
    quadratic_correction_weight_identity hM hH he hB
  have hh := mul_le_mul_of_nonneg_left hcut hα
  have hab : α ≤ 2 * J * (β / D) := by
    calc
      α ≤ (2 * J * β) / D := (le_div_iff₀ hDR).mpr (by nlinarith [hi])
      _ = _ := by ring
  have hαJ : α ≤ 2 * J * α := by nlinarith
  change α ≤ 2 * J * min α (Real.sqrt M / (Real.sqrt e * Real.sqrt B * D))
  have heq : Real.sqrt M / (Real.sqrt e * Real.sqrt B * D) = β / D := by dsimp [β]; ring
  rw [heq]
  by_cases hle : α ≤ β / D
  · rw [min_eq_left hle]
    exact hαJ
  · rw [min_eq_right (le_of_not_ge hle)]
    exact hab

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
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticSieveDuality
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reciprocity and duality interchange the two quadratic-sieve lengths -/

namespace Ostmann

open Matrix
open scoped BigOperators Classical

 theorem QuadraticSieveBound.transpose {M N : ℕ} {K : ℝ} (hK : 0 ≤ K)
    (h : QuadraticSieveBound N M K) : QuadraticSieveBound M N (2 * K) := by
  let U := oddSquarefreeRange M
  let V := oddSquarefreeRange N
  let F : Matrix U V ℂ := .of (fun m n => (jacobiSym (n.val : ℤ) m.val : ℂ))
  have hdual (b : U → ℂ) :
      (∑ n : V, ‖(Fᴴ *ᵥ b) n‖ ^ 2) ≤ 2 * K * ∑ m : U, ‖b m‖ ^ 2 := by
    let b' : ℕ → ℂ := fun m => if hm : m ∈ U then b ⟨m, hm⟩ else 0
    have hE : quadraticSieveEnergy M b' = ∑ m : U, ‖b m‖ ^ 2 := by
      symm
      calc
        _ = ∑ m : U, ‖b' m.val‖ ^ 2 := by
          apply Finset.sum_congr rfl
          intro m _
          simp [b']
        _ = ∑ m ∈ U, ‖b' m‖ ^ 2 := Finset.sum_coe_sort U (fun m : ℕ => ‖b' m‖ ^ 2)
    have hpoint (n : V) : (Fᴴ *ᵥ b) n = quadraticTransposeSum M b' n.val := by
      change (∑ m : U, star ((jacobiSym (n.val : ℤ) m.val : ℂ)) * b m) = _
      calc
        _ = ∑ m : U, b' m.val * (jacobiSym (n.val : ℤ) m.val : ℂ) := by
          apply Finset.sum_congr rfl
          intro m _
          simp only [star_intCast]
          simp [b', mul_comm]
        _ = _ := Finset.sum_coe_sort U (fun m : ℕ => b' m * (jacobiSym (n.val : ℤ) m : ℂ))
    have hsum : (∑ n : V, ‖(Fᴴ *ᵥ b) n‖ ^ 2) =
        ∑ n ∈ V, ‖quadraticTransposeSum M b' n‖ ^ 2 := by
      calc
        _ = ∑ n : V, ‖quadraticTransposeSum M b' n.val‖ ^ 2 := by simp_rw [hpoint]
        _ = _ := Finset.sum_coe_sort V (fun n : ℕ => ‖quadraticTransposeSum M b' n‖ ^ 2)
    rw [hsum, ← hE]
    exact quadraticTranspose_of_bound h b'
  intro b
  have hb := finite_matrix_duality F (2 * K) (by positivity) hdual (fun n => b n.val)
  have hpoint (m : U) : (F *ᵥ fun n => b n.val) m = quadraticSieveSum N b m.val := by
    change (∑ n : V, (jacobiSym (n.val : ℤ) m.val : ℂ) * b n.val) = _
    calc
      _ = ∑ n : V, b n.val * (jacobiSym (n.val : ℤ) m.val : ℂ) := by
        apply Finset.sum_congr rfl
        intro n _
        ring
      _ = _ := Finset.sum_coe_sort V (fun n : ℕ => b n * (jacobiSym (n : ℤ) m.val : ℂ))
  have hleft : (∑ m : U, ‖(F *ᵥ fun n => b n.val) m‖ ^ 2) =
      ∑ m ∈ U, ‖quadraticSieveSum N b m‖ ^ 2 := by
    calc
      _ = ∑ m : U, ‖quadraticSieveSum N b m.val‖ ^ 2 := by simp_rw [hpoint]
      _ = _ := Finset.sum_coe_sort U (fun m : ℕ => ‖quadraticSieveSum N b m‖ ^ 2)
  have hright : (∑ n : V, ‖b n.val‖ ^ 2) = quadraticSieveEnergy N b :=
    Finset.sum_coe_sort V (fun n : ℕ => ‖b n‖ ^ 2)
  rw [hleft, hright] at hb
  exact hb

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticSieveGrowth
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The precise exponent induction for the actual quadratic-sieve matrices -/

namespace Ostmann

theorem quadratic_growth_shortened_transpose {ξ : ℝ} (h : QuadraticSieveGrowth ξ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ B N d : ℕ, 1 ≤ B → 1 ≤ d → d ≤ N →
      QuadraticSieveBound B (N / d)
        (C * ((B : ℝ) * N) ^ ε * ((B : ℝ) ^ ξ + (N : ℝ) / d)) := by
  obtain ⟨C, hC, hc⟩ := h ε hε
  refine ⟨2 * C, by positivity, ?_⟩
  intro B N d hB hd hdN
  have hdiv : 1 ≤ N / d := Nat.div_pos hdN hd
  have hBR : (0 : ℝ) < B := by exact_mod_cast hB
  have hDR : (0 : ℝ) < d := by exact_mod_cast hd
  have hNR : (0 : ℝ) < N := by exact_mod_cast hd.trans hdN
  have hfloor : ((N / d : ℕ) : ℝ) ≤ (N : ℝ) / d := Nat.cast_div_le
  have hfloorN : ((N / d : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.div_le_self N d
  have hfactor : 0 ≤ C * (((N / d : ℕ) : ℝ) * B) ^ ε * (((N / d : ℕ) : ℝ) + (B : ℝ) ^ ξ) := by positivity
  apply ((hc (N / d) B hdiv hB).transpose hfactor).mono_constant
  have hp : (((N / d : ℕ) : ℝ) * B) ^ ε ≤ ((B : ℝ) * N) ^ ε := by
    apply Real.rpow_le_rpow (by positivity) _ hε.le
    nlinarith [mul_le_mul_of_nonneg_right hfloorN hBR.le]
  calc
    _ = (2 * C) * (((N / d : ℕ) : ℝ) * B) ^ ε * ((B : ℝ) ^ ξ + ((N / d : ℕ) : ℝ)) := by ring
    _ ≤ _ := by gcongr

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

theorem quadratic_first_low_budget {M N J F Y E : ℝ} {e B D : ℕ}
    (hM : 0 < M) (hN : 0 < N) (he : 0 < e) (hB : 0 < B) (hD : 0 < D)
    (hJ : 1 ≤ J) (hF : 0 ≤ F) (hY : 0 ≤ Y) (hE : 0 ≤ E)
    (hcut : (D : ℝ) ≤ 2 * quadraticCorrectionBase M N e B * J) :
    (M / ((e : ℝ) * N)) * quadraticGrowthBandBudget F Y (2 * N) D E ≤
      32 * J * F * (2 * (M / e) + Real.sqrt (2 * (M / e)) / Real.sqrt B * Y) * E := by
  have heR : (0 : ℝ) < e := by exact_mod_cast he
  have hBR : (0 : ℝ) < B := by exact_mod_cast hB
  have hDR : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hα : M / ((e : ℝ) * N) = (M / e) / N := by ring
  have hβ : Real.sqrt M / (Real.sqrt e * Real.sqrt B * D) =
      Real.sqrt (M / e) / (Real.sqrt B * D) := by
    rw [Real.sqrt_div hM.le]
    ring
  have hw := quadratic_low_weight_balance hM hN he hB hD hJ hcut
  rw [hα, hβ] at hw
  have hb := quadratic_first_doubled_band_balance (div_pos hM heR) hN hBR hDR hF hY hE
  have ht : 0 ≤ quadraticGrowthBandBudget F Y (2 * N) D E :=
    quadratic_growth_band_budget_nonneg hF hY (by positivity) (by positivity) hE
  rw [hα]
  calc
    _ ≤ (2 * J * min ((M / e) / N) (Real.sqrt (M / e) / (Real.sqrt B * D))) *
        quadraticGrowthBandBudget F Y (2 * N) D E := mul_le_mul_of_nonneg_right hw ht
    _ = (2 * J) * (min ((M / e) / N) (Real.sqrt (M / e) / (Real.sqrt B * D)) *
        quadraticGrowthBandBudget F Y (2 * N) D E) := by ring
    _ ≤ (2 * J) * (16 * F * (2 * (M / e) + Real.sqrt (2 * (M / e)) / Real.sqrt B * Y) * E) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by ring

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
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticUniformGauss
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform unweighted divisor comparison with the actual Gauss factor -/

namespace Ostmann

open scoped Classical BigOperators

 theorem quadratic_gauss_uniform_bound (M N₁ N₂ D : ℕ)
    (a b : ℕ → ℂ) (K₁ K₂ : ℕ → ℝ) (T : ℝ) (hT : 0 ≤ T)
    (hK₁ : ∀ i ≤ Nat.log 2 N₁, 0 ≤ K₁ i)
    (hK₂ : ∀ j ≤ Nat.log 2 N₂, 0 ≤ K₂ j)
    (h₁ : ∀ i ≤ Nat.log 2 N₁, QuadraticSieveBound M (N₁ / 2 ^ i) (K₁ i))
    (h₂ : ∀ j ≤ Nat.log 2 N₂, QuadraticSieveBound M (N₂ / 2 ^ j) (K₂ j))
    (hcost : ∀ i ≤ Nat.log 2 N₁, ∀ j ≤ Nat.log 2 N₂,
      D < 4 * (2 ^ i * 2 ^ j) → 2 ^ i * 2 ^ j ≤ 2 * D →
      Real.sqrt (2 * K₁ i * (2 ^ i : ℕ) * quadraticDivisorMoment N₁ a) *
        Real.sqrt (2 * K₂ j * (2 ^ j : ℕ) * quadraticDivisorMoment N₂ b) ≤ T) :
    (∑ d ∈ Finset.Ioc D (2 * D), ∑ m ∈ oddSquarefreeRange M,
      ‖quadraticGaussDivisorBilinear N₁ N₂ d a b m‖) ≤
      3 *
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
  have hb₁ := quadratic_bilinear_uniform_bound M N₁ N₂ D
    (quadraticGaussLeft a) (quadraticGaussRight b) K₁ K₂ T hT hK₁ hK₂ h₁ h₂ hc₁
  have hb₂ := quadratic_bilinear_uniform_bound M N₁ N₂ D
    (quadraticThreeClass (quadraticGaussLeft a))
    (quadraticThreeClass (quadraticGaussRight b)) K₁ K₂ T hT hK₁ hK₂ h₁ h₂ hc₂
  calc
    _ ≤ ∑ d ∈ Finset.Ioc D (2 * D), ∑ m ∈ oddSquarefreeRange M,
        (‖quadraticDivisorBilinear N₁ N₂ d (quadraticGaussLeft a) (quadraticGaussRight b) m‖ +
        2 * ‖quadraticDivisorBilinear N₁ N₂ d
          (quadraticThreeClass (quadraticGaussLeft a))
          (quadraticThreeClass (quadraticGaussRight b)) m‖) := by
      apply Finset.sum_le_sum
      intro d _
      apply Finset.sum_le_sum
      intro m _
      rw [quadratic_gauss_divisor_bilinear_split]
      exact (norm_sub_le _ _).trans (by norm_num [norm_mul])
    _ = (∑ d ∈ Finset.Ioc D (2 * D), ∑ m ∈ oddSquarefreeRange M,
        ‖quadraticDivisorBilinear N₁ N₂ d (quadraticGaussLeft a) (quadraticGaussRight b) m‖) +
        2 * (∑ d ∈ Finset.Ioc D (2 * D), ∑ m ∈ oddSquarefreeRange M,
          ‖quadraticDivisorBilinear N₁ N₂ d
          (quadraticThreeClass (quadraticGaussLeft a))
          (quadraticThreeClass (quadraticGaussRight b)) m‖) := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    _ ≤ _ := by nlinarith [hb₁, hb₂]

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

theorem quadratic_growth_cutoff_bounds {ξ : ℝ} (h : QuadraticSieveGrowth ξ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ B N : ℕ, 0 < B → 0 < N →
      ∀ i ≤ Nat.log 2 N,
        QuadraticSieveBound B (N / 2 ^ i) (quadraticGrowthCutoff C ε ξ B N i) := by
  obtain ⟨C, hC, hc⟩ := quadratic_growth_shortened_transpose h ε hε
  refine ⟨C, hC, ?_⟩
  intro B N hB hN i hi
  apply hc B N (2 ^ i) hB (by exact one_le_pow₀ (by norm_num))
  exact (Nat.pow_le_pow_right (by norm_num) hi).trans
    (Nat.pow_log_le_self 2 hN.ne')

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
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticCorrectionReindex
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact pair-to-divisor rearrangement for the retained corrections -/

namespace Ostmann

open scoped Classical BigOperators ComplexConjugate

theorem quadratic_coprime_divisor_reindex (N : ℕ) (F : ℕ → ℕ → ℕ → ℂ) :
    (∑ s ∈ oddSquarefreeRange (2 * N), ∑ t ∈ oddSquarefreeRange (2 * N),
      if s.Coprime t then ∑ d ∈ (s * t).divisors, F s t d else 0) =
    ∑ d ∈ Finset.Icc 1 ((2 * N) ^ 2),
      ∑ s ∈ oddSquarefreeRange (2 * N), ∑ t ∈ oddSquarefreeRange (2 * N),
        if s.Coprime t ∧ d ∣ s * t then F s t d else 0 := by
  have hlocal (s : ℕ) (hs : s ∈ oddSquarefreeRange (2 * N))
      (t : ℕ) (ht : t ∈ oddSquarefreeRange (2 * N)) :
      (if s.Coprime t then ∑ d ∈ (s * t).divisors, F s t d else 0) =
      ∑ d ∈ Finset.Icc 1 ((2 * N) ^ 2),
        if s.Coprime t ∧ d ∣ s * t then F s t d else 0 := by
    obtain ⟨hsr, _, hss⟩ := Finset.mem_filter.mp hs
    obtain ⟨htr, _, hst⟩ := Finset.mem_filter.mp ht
    have hq : s * t ≠ 0 := mul_ne_zero hss.ne_zero hst.ne_zero
    have hqtop : s * t ≤ (2 * N) ^ 2 := by
      simpa only [pow_two] using Nat.mul_le_mul (Finset.mem_Icc.mp hsr).2
        (Finset.mem_Icc.mp htr).2
    have heq : (Finset.Icc 1 ((2 * N) ^ 2)).filter (fun d => d ∣ s * t) = (s * t).divisors := by
      ext d
      simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
      constructor
      · intro h
        exact ⟨h.2, hq⟩
      · intro h
        have hd := Nat.mem_divisors.mpr h
        exact ⟨⟨Nat.pos_of_mem_divisors hd,
          (Nat.le_of_dvd (Nat.pos_of_ne_zero hq) h.1).trans hqtop⟩, h.1⟩
    by_cases hc : s.Coprime t
    · rw [ite_eq_left hc]
      have heq' : (Finset.Icc 1 ((2 * N) ^ 2)).filter
          (fun d => s.Coprime t ∧ d ∣ s * t) = (s * t).divisors := by
        convert heq using 1
        all_goals try with_reducible_and_instances rfl
        ext d
        simp only [Finset.mem_filter]
        exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, hc, h.2⟩⟩
      rw [← Finset.sum_filter, heq']
    · simp [hc]
  calc
    _ = ∑ s ∈ oddSquarefreeRange (2 * N), ∑ t ∈ oddSquarefreeRange (2 * N),
        ∑ d ∈ Finset.Icc 1 ((2 * N) ^ 2),
          if s.Coprime t ∧ d ∣ s * t then F s t d else 0 := by
      apply Finset.sum_congr rfl
      intro s hs
      exact Finset.sum_congr rfl (fun t ht => hlocal s hs t ht)
    _ = _ := by
      conv_lhs =>
        arg 2
        ext s
        rw [Finset.sum_comm]
      rw [Finset.sum_comm]

theorem quadratic_sqrt_gauss_divisor (N d : ℕ) (v w : ℕ → ℂ) (m : ℤ) :
    quadraticGaussDivisorBilinear (2 * N) (2 * N) d
      (quadraticSqrtNormalize v) (quadraticSqrtNormalize w) m =
    ∑ s ∈ oddSquarefreeRange (2 * N), ∑ t ∈ oddSquarefreeRange (2 * N),
      ((if s.Coprime t ∧ d ∣ s * t then (1 : ℂ) else 0) *
        v s * conj (w t) * quadraticGaussMultiplier (s * t) *
        (jacobiSym m s : ℂ) * (jacobiSym m t : ℂ)) /
          (Real.sqrt (s * t : ℕ) : ℂ) := by
  unfold quadraticGaussDivisorBilinear quadraticSqrtNormalize
  apply Finset.sum_congr rfl
  intro s _hs
  apply Finset.sum_congr rfl
  intro t _ht
  rw [map_div₀, Complex.conj_ofReal]
  have hr : (Real.sqrt (s * t : ℕ) : ℂ) =
      (Real.sqrt s : ℂ) * (Real.sqrt t : ℂ) := by
    rw [Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg s), Complex.ofReal_mul]
  rw [hr]
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticNormalizedGauss
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The first divisor correction gains its actual square-root denominator -/

namespace Ostmann

open scoped Classical BigOperators

theorem quadratic_sqrt_normalized_gauss_bound (M N D : ℕ) (hN : 0 < N)
    (v w : ℕ → ℂ) (hv : ∀ n < N, v n = 0) (hw : ∀ n < N, w n = 0)
    (K₁ K₂ : ℕ → ℝ) (T : ℝ) (hT : 0 ≤ T)
    (hK₁ : ∀ i ≤ Nat.log 2 (2 * N), 0 ≤ K₁ i)
    (hK₂ : ∀ j ≤ Nat.log 2 (2 * N), 0 ≤ K₂ j)
    (h₁ : ∀ i ≤ Nat.log 2 (2 * N), QuadraticSieveBound M (2 * N / 2 ^ i) (K₁ i))
    (h₂ : ∀ j ≤ Nat.log 2 (2 * N), QuadraticSieveBound M (2 * N / 2 ^ j) (K₂ j))
    (hcost : ∀ i ≤ Nat.log 2 (2 * N), ∀ j ≤ Nat.log 2 (2 * N),
      D < 4 * (2 ^ i * 2 ^ j) → 2 ^ i * 2 ^ j ≤ 2 * D →
      Real.sqrt (2 * K₁ i * (2 ^ i : ℕ) * quadraticDivisorMoment (2 * N) v) *
        Real.sqrt (2 * K₂ j * (2 ^ j : ℕ) * quadraticDivisorMoment (2 * N) w) ≤ T) :
    (∑ d ∈ Finset.Ioc D (2 * D), ∑ m ∈ oddSquarefreeRange M,
      ‖quadraticGaussDivisorBilinear (2 * N) (2 * N) d
        (quadraticSqrtNormalize v) (quadraticSqrtNormalize w) m‖) ≤
      3 * ((((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ)) ^ 2 * T) / N := by
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  have hnorm : ∀ i ≤ Nat.log 2 (2 * N), ∀ j ≤ Nat.log 2 (2 * N),
      D < 4 * (2 ^ i * 2 ^ j) → 2 ^ i * 2 ^ j ≤ 2 * D →
      Real.sqrt (2 * K₁ i * (2 ^ i : ℕ) *
        quadraticDivisorMoment (2 * N) (quadraticSqrtNormalize v)) *
      Real.sqrt (2 * K₂ j * (2 ^ j : ℕ) *
        quadraticDivisorMoment (2 * N) (quadraticSqrtNormalize w)) ≤ T / N := by
    intro i hi j hj hd₁ hd₂
    calc
      _ ≤ Real.sqrt (2 * K₁ i * (2 ^ i : ℕ) * (quadraticDivisorMoment (2 * N) v / N)) *
          Real.sqrt (2 * K₂ j * (2 ^ j : ℕ) * (quadraticDivisorMoment (2 * N) w / N)) := by
        apply mul_le_mul _ _ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
        · exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left
            (quadraticSqrtNormalize_moment N (2 * N) hN v hv) (by have := hK₁ i hi; positivity))
        · exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left
            (quadraticSqrtNormalize_moment N (2 * N) hN w hw) (by have := hK₂ j hj; positivity))
      _ = (Real.sqrt (2 * K₁ i * (2 ^ i : ℕ) * quadraticDivisorMoment (2 * N) v) *
          Real.sqrt (2 * K₂ j * (2 ^ j : ℕ) * quadraticDivisorMoment (2 * N) w)) / N := by
        rw [← mul_div_assoc, ← mul_div_assoc, Real.sqrt_div' _ hNr.le, Real.sqrt_div' _ hNr.le,
          div_mul_div_comm, ← pow_two, Real.sq_sqrt hNr.le]
      _ ≤ _ := div_le_div_of_nonneg_right (hcost i hi j hj hd₁ hd₂) hNr.le
  have hh := quadratic_gauss_uniform_bound M (2 * N) (2 * N) D
    (quadraticSqrtNormalize v) (quadraticSqrtNormalize w) K₁ K₂ (T / N)
    (div_nonneg hT hNr.le) hK₁ hK₂ h₁ h₂ hnorm
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  simp only [Nat.cast_add, Nat.cast_one]
  ring

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

theorem quadratic_variable_high_band_bound (B N D : ℕ) (hB : 0 < B) (hD : 0 < D)
    (P : ℕ → ℕ → Prop) [DecidableRel P]
    (v w : ℕ → ℂ) (K₁ K₂ : ℕ → ℝ) (T : ℝ) (hT : 0 ≤ T)
    (hK₁ : ∀ i ≤ Nat.log 2 (2 * N), 0 ≤ K₁ i)
    (hK₂ : ∀ j ≤ Nat.log 2 (2 * N), 0 ≤ K₂ j)
    (h₁ : ∀ i ≤ Nat.log 2 (2 * N), QuadraticSieveBound (2 * B) (2 * N / 2 ^ i) (K₁ i))
    (h₂ : ∀ j ≤ Nat.log 2 (2 * N), QuadraticSieveBound (2 * B) (2 * N / 2 ^ j) (K₂ j))
    (hcost : ∀ i ≤ Nat.log 2 (2 * N), ∀ j ≤ Nat.log 2 (2 * N),
      D < 4 * (2 ^ i * 2 ^ j) → 2 ^ i * 2 ^ j ≤ 2 * D →
      Real.sqrt (2 * K₁ i * (2 ^ i : ℕ) * quadraticDivisorMoment (2 * N) v) *
        Real.sqrt (2 * K₂ j * (2 ^ j : ℕ) * quadraticDivisorMoment (2 * N) w) ≤ T) :
    ‖∑ d ∈ Finset.Ioc D (2 * D), ∑ b ∈ oddSquarefreeRange (2 * B),
      if B ≤ b ∧ P d b then
        (((ArithmeticFunction.moebius d : ℂ) / d) / (Real.sqrt b : ℂ)) *
          quadraticGaussDivisorBilinear (2 * N) (2 * N) d v w b else 0‖ ≤
      3 * ((((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ)) ^ 2 * T) / ((D : ℝ) * Real.sqrt B) := by
  classical
  apply (quadratic_variable_correction_weight
    (fun d b => quadraticGaussDivisorBilinear (2 * N) (2 * N) d v w b) hD hB P).trans
  have hh := quadratic_gauss_uniform_bound (2 * B) (2 * N) (2 * N) D v w
    K₁ K₂ T hT hK₁ hK₂ h₁ h₂ hcost
  calc
    _ ≤ (1 / ((D : ℝ) * Real.sqrt B)) *
        (3 * (((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ) * (Nat.log 2 (2 * N) + 1) * T)) :=
      mul_le_mul_of_nonneg_left hh (by positivity)
    _ = _ := by push_cast; ring

theorem quadratic_variable_low_correction_weight (F : ℕ → ℕ → ℂ) (D B : ℕ)
    (P : ℕ → ℕ → Prop) [DecidableRel P] :
    ‖∑ d ∈ Finset.Ioc D (2 * D), ∑ b ∈ oddSquarefreeRange (2 * B),
      if B ≤ b ∧ P d b then (ArithmeticFunction.moebius d : ℂ) * F d b else 0‖ ≤
      ∑ d ∈ Finset.Ioc D (2 * D), ∑ b ∈ oddSquarefreeRange (2 * B), ‖F d b‖ := by
  classical
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro d _
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro b _
  split_ifs
  · rw [norm_mul]
    have hμ : ‖(ArithmeticFunction.moebius d : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_intCast]
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hμ (norm_nonneg (F d b))
  · simpa only [norm_zero] using norm_nonneg (F d b)

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

theorem quadratic_variable_low_band_bound (B N D : ℕ) (hN : 0 < N)
    (P : ℕ → ℕ → Prop) [DecidableRel P]
    (v w : ℕ → ℂ) (hv : ∀ n < N, v n = 0) (hw : ∀ n < N, w n = 0)
    (K₁ K₂ : ℕ → ℝ) (T : ℝ) (hT : 0 ≤ T)
    (hK₁ : ∀ i ≤ Nat.log 2 (2 * N), 0 ≤ K₁ i)
    (hK₂ : ∀ j ≤ Nat.log 2 (2 * N), 0 ≤ K₂ j)
    (h₁ : ∀ i ≤ Nat.log 2 (2 * N), QuadraticSieveBound (2 * B) (2 * N / 2 ^ i) (K₁ i))
    (h₂ : ∀ j ≤ Nat.log 2 (2 * N), QuadraticSieveBound (2 * B) (2 * N / 2 ^ j) (K₂ j))
    (hcost : ∀ i ≤ Nat.log 2 (2 * N), ∀ j ≤ Nat.log 2 (2 * N),
      D < 4 * (2 ^ i * 2 ^ j) → 2 ^ i * 2 ^ j ≤ 2 * D →
      Real.sqrt (2 * K₁ i * (2 ^ i : ℕ) * quadraticDivisorMoment (2 * N) v) *
        Real.sqrt (2 * K₂ j * (2 ^ j : ℕ) * quadraticDivisorMoment (2 * N) w) ≤ T) :
    ‖∑ d ∈ Finset.Ioc D (2 * D), ∑ b ∈ oddSquarefreeRange (2 * B),
      if B ≤ b ∧ P d b then (ArithmeticFunction.moebius d : ℂ) *
        quadraticGaussDivisorBilinear (2 * N) (2 * N) d
          (quadraticSqrtNormalize v) (quadraticSqrtNormalize w) b else 0‖ ≤
      3 * (((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ) ^ 2 * T) / N := by
  exact (quadratic_variable_low_correction_weight _ D B P).trans
    (quadratic_sqrt_normalized_gauss_bound (2 * B) N D hN v w hv hw
      K₁ K₂ T hT hK₁ hK₂ h₁ h₂ hcost)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticGrowthCorrectionBands
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Original low and high correction bands from the actual growth matrices -/

namespace Ostmann

open scoped Classical BigOperators

theorem quadratic_low_band_growth {C ε ξ M J : ℝ} (hC : 0 ≤ C)
    {e B N D : ℕ} (hM : 0 < M) (he : 0 < e) (hB : 0 < B) (hN : 0 < N) (hD : 0 < D)
    (hJ : 1 ≤ J) (hcut : (D : ℝ) ≤ 2 * quadraticCorrectionBase M N e B * J)
    (P : ℕ → ℕ → Prop) (v w : ℕ → ℂ)
    (hv : ∀ n < N, v n = 0) (hw : ∀ n < N, w n = 0)
    (hmat : ∀ i ≤ Nat.log 2 (2 * N), QuadraticSieveBound (2 * B) (2 * N / 2 ^ i)
      (quadraticGrowthCutoff C ε ξ (2 * B) (2 * N) i)) :
    ‖((M / e : ℝ) : ℂ) * quadraticLowCorrectionBand B N D P v w‖ ≤
      96 * J * ((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ) ^ 2 *
        quadraticCorrectionGrowthScale C ε ξ M e B N v w := by
  classical
  let T := quadraticGrowthDivisorBudget C ε ξ (2 * B) (2 * N) D v w
  have hT : 0 ≤ T := quadratic_growth_divisor_budget_nonneg hC _ _ _ _ _
  have hl := quadratic_variable_low_band_bound B N D hN P v w hv hw
    (quadraticGrowthCutoff C ε ξ (2 * B) (2 * N))
    (quadraticGrowthCutoff C ε ξ (2 * B) (2 * N)) T hT
    (fun i _ => quadratic_growth_cutoff_nonneg hC _ _ i)
    (fun i _ => quadratic_growth_cutoff_nonneg hC _ _ i) hmat hmat
    (fun _ _ _ _ _ hp => quadratic_growth_cutoff_cost hC hD v w hp)
  change ‖quadraticLowCorrectionBand B N D P v w‖ ≤ _ at hl
  have hb := quadratic_first_low_budget hM (show (0 : ℝ) < N by exact_mod_cast hN)
    he hB hD hJ
    (show 0 ≤ C * (((2 * B : ℕ) : ℝ) * (2 * N : ℕ)) ^ ε by positivity)
    (show 0 ≤ ((2 * B : ℕ) : ℝ) ^ ξ by positivity)
    (show 0 ≤ Real.sqrt (quadraticDivisorMoment (2 * N) v) *
      Real.sqrt (quadraticDivisorMoment (2 * N) w) by positivity) hcut
  have hb' : (M / ((e : ℝ) * N)) * T ≤
      32 * J * quadraticCorrectionGrowthScale C ε ξ M e B N v w := by
    simpa only [T, quadraticGrowthDivisorBudget, quadraticCorrectionGrowthScale,
      Nat.cast_mul, Nat.cast_ofNat, mul_assoc] using hb
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (div_pos hM (by exact_mod_cast he))]
  apply (mul_le_mul_of_nonneg_left hl (by positivity)).trans
  calc
    _ = (3 * ((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ) ^ 2) * (M / ((e : ℝ) * N) * T) := by ring
    _ ≤ (3 * ((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ) ^ 2) *
        (32 * J * quadraticCorrectionGrowthScale C ε ξ M e B N v w) :=
      mul_le_mul_of_nonneg_left hb' (by positivity)
    _ = _ := by ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticHighBandGrowth
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual high-divisor correction with its original normalizer -/

namespace Ostmann

open scoped Classical BigOperators

theorem quadratic_high_band_growth {C ε ξ M J : ℝ} (hC : 0 ≤ C)
    {e B N D : ℕ} (hM : 0 < M) (he : 0 < e) (hB : 0 < B) (hN : 0 < N) (hD : 0 < D)
    (hJ : 1 ≤ J) (hcut : quadraticCorrectionBase M N e B / (8 * J) ≤ (D : ℝ))
    (P : ℕ → ℕ → Prop) (v w : ℕ → ℂ)
    (hmat : ∀ i ≤ Nat.log 2 (2 * N), QuadraticSieveBound (2 * B) (2 * N / 2 ^ i)
      (quadraticGrowthCutoff C ε ξ (2 * B) (2 * N) i)) :
    ‖((Real.sqrt M / Real.sqrt e : ℝ) : ℂ) * quadraticHighCorrectionBand B N D P v w‖ ≤
      384 * J * ((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ) ^ 2 *
        quadraticCorrectionGrowthScale C ε ξ M e B N v w := by
  classical
  let T := quadraticGrowthDivisorBudget C ε ξ (2 * B) (2 * N) D v w
  have hT : 0 ≤ T := quadratic_growth_divisor_budget_nonneg hC _ _ _ _ _
  have hl := quadratic_variable_high_band_bound B N D hB hD P v w
    (quadraticGrowthCutoff C ε ξ (2 * B) (2 * N))
    (quadraticGrowthCutoff C ε ξ (2 * B) (2 * N)) T hT
    (fun i _ => quadratic_growth_cutoff_nonneg hC _ _ i)
    (fun i _ => quadratic_growth_cutoff_nonneg hC _ _ i) hmat hmat
    (fun _ _ _ _ _ hp => quadratic_growth_cutoff_cost hC hD v w hp)
  change ‖quadraticHighCorrectionBand B N D P v w‖ ≤ _ at hl
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
    _ = (3 * ((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ) ^ 2) *
        (Real.sqrt M / (Real.sqrt e * Real.sqrt B * D) * T) := by ring
    _ ≤ (3 * ((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ) ^ 2) *
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

theorem quadratic_correction_base_mono {M H N : ℝ} {e B : ℕ}
    (hM : 0 < M) (hH : 0 < H) (hHN : H ≤ N) (he : 0 < e) (hB : 0 < B) :
    quadraticCorrectionBase M H e B ≤ quadraticCorrectionBase M N e B := by
  rw [quadratic_correction_base_formula hM hH he hB,
    quadratic_correction_base_formula hM (hH.trans_le hHN) he hB]
  gcongr

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

theorem quadratic_gauss_unit_divisor_bound (M N₁ N₂ : ℕ) (K₁ K₂ : ℝ)
    (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂)
    (h₁ : QuadraticSieveBound M N₁ K₁) (h₂ : QuadraticSieveBound M N₂ K₂)
    (a b : ℕ → ℂ) :
    (∑ m ∈ oddSquarefreeRange M, ‖quadraticGaussDivisorBilinear N₁ N₂ 1 a b m‖) ≤
      3 * (Real.sqrt (2 * K₁ * quadraticDivisorMoment N₁ a) *
        Real.sqrt (2 * K₂ * quadraticDivisorMoment N₂ b)) := by
  have hleft := quadratic_unit_divisor_bound M N₁ N₂ K₁ K₂ hK₁ hK₂ h₁ h₂
    (quadraticGaussLeft a) (quadraticGaussRight b)
  simp only [quadraticDivisorMoment_gaussLeft, quadraticDivisorMoment_gaussRight] at hleft
  have hright := quadratic_unit_divisor_bound M N₁ N₂ K₁ K₂ hK₁ hK₂ h₁ h₂
    (quadraticThreeClass (quadraticGaussLeft a)) (quadraticThreeClass (quadraticGaussRight b))
  have hright' : (∑ m ∈ oddSquarefreeRange M,
      ‖quadraticDivisorBilinear N₁ N₂ 1 (quadraticThreeClass (quadraticGaussLeft a))
        (quadraticThreeClass (quadraticGaussRight b)) m‖) ≤
      Real.sqrt (2 * K₁ * quadraticDivisorMoment N₁ a) *
        Real.sqrt (2 * K₂ * quadraticDivisorMoment N₂ b) := by
    apply hright.trans
    apply mul_le_mul _ _ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    · apply Real.sqrt_le_sqrt
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa only [quadraticDivisorMoment_gaussLeft] using
        quadraticDivisorMoment_threeClass N₁ (quadraticGaussLeft a)
    · apply Real.sqrt_le_sqrt
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa only [quadraticDivisorMoment_gaussRight] using
        quadraticDivisorMoment_threeClass N₂ (quadraticGaussRight b)
  calc
    _ ≤ ∑ m ∈ oddSquarefreeRange M,
        (‖quadraticDivisorBilinear N₁ N₂ 1 (quadraticGaussLeft a) (quadraticGaussRight b) m‖ +
        2 * ‖quadraticDivisorBilinear N₁ N₂ 1 (quadraticThreeClass (quadraticGaussLeft a))
          (quadraticThreeClass (quadraticGaussRight b)) m‖) := by
      apply Finset.sum_le_sum
      intro m _
      rw [quadratic_gauss_divisor_bilinear_split]
      exact (norm_sub_le _ _).trans (by norm_num [norm_mul])
    _ = (∑ m ∈ oddSquarefreeRange M,
        ‖quadraticDivisorBilinear N₁ N₂ 1 (quadraticGaussLeft a) (quadraticGaussRight b) m‖) +
        2 * ∑ m ∈ oddSquarefreeRange M,
          ‖quadraticDivisorBilinear N₁ N₂ 1 (quadraticThreeClass (quadraticGaussLeft a))
            (quadraticThreeClass (quadraticGaussRight b)) m‖ := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    _ ≤ _ := by linarith

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

theorem quadratic_unit_sqrt_gauss_bound (M N : ℕ) (hN : 0 < N)
    (v w : ℕ → ℂ) (hv : ∀ n < N, v n = 0) (hw : ∀ n < N, w n = 0)
    (K₁ K₂ : ℝ) (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂)
    (h₁ : QuadraticSieveBound M (2 * N) K₁) (h₂ : QuadraticSieveBound M (2 * N) K₂) :
    (∑ m ∈ oddSquarefreeRange M,
      ‖quadraticGaussDivisorBilinear (2 * N) (2 * N) 1
        (quadraticSqrtNormalize v) (quadraticSqrtNormalize w) m‖) ≤
      3 * (Real.sqrt (2 * K₁ * quadraticDivisorMoment (2 * N) v) *
        Real.sqrt (2 * K₂ * quadraticDivisorMoment (2 * N) w)) / N := by
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  have hroot : Real.sqrt (2 * K₁ * quadraticDivisorMoment (2 * N) (quadraticSqrtNormalize v)) *
      Real.sqrt (2 * K₂ * quadraticDivisorMoment (2 * N) (quadraticSqrtNormalize w)) ≤
      (Real.sqrt (2 * K₁ * quadraticDivisorMoment (2 * N) v) *
        Real.sqrt (2 * K₂ * quadraticDivisorMoment (2 * N) w)) / N := by
    calc
      _ ≤ Real.sqrt (2 * K₁ * (quadraticDivisorMoment (2 * N) v / N)) *
          Real.sqrt (2 * K₂ * (quadraticDivisorMoment (2 * N) w / N)) := by
        apply mul_le_mul _ _ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
        · exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left
            (quadraticSqrtNormalize_moment N (2 * N) hN v hv) (by positivity))
        · exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left
            (quadraticSqrtNormalize_moment N (2 * N) hN w hw) (by positivity))
      _ = _ := by
        rw [← mul_div_assoc, ← mul_div_assoc, Real.sqrt_div' _ hNr.le, Real.sqrt_div' _ hNr.le,
          div_mul_div_comm, ← pow_two, Real.sq_sqrt hNr.le]
  exact (quadratic_gauss_unit_divisor_bound M (2 * N) (2 * N) K₁ K₂ hK₁ hK₂ h₁ h₂ _ _).trans
    (by simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hroot (by norm_num : (0 : ℝ) ≤ 3))

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

theorem quadratic_low_unit_growth {C ε ξ M J : ℝ} (hC : 0 ≤ C)
    {e B N : ℕ} (hM : 0 < M) (he : 0 < e) (hB : 0 < B) (hN : 0 < N)
    (hJ : 1 ≤ J) (hcut : 1 ≤ 2 * quadraticCorrectionBase M N e B * J)
    (P : ℕ → Prop) (v w : ℕ → ℂ)
    (hv : ∀ n < N, v n = 0) (hw : ∀ n < N, w n = 0)
    (hmat : QuadraticSieveBound (2 * B) (2 * N)
      (quadraticGrowthCutoff C ε ξ (2 * B) (2 * N) 0)) :
    ‖((M / e : ℝ) : ℂ) * quadraticLowCorrectionUnit B N P v w‖ ≤
      96 * J * quadraticCorrectionGrowthScale C ε ξ M e B N v w := by
  classical
  let T := quadraticGrowthDivisorBudget C ε ξ (2 * B) (2 * N) 1 v w
  let K := quadraticGrowthCutoff C ε ξ (2 * B) (2 * N) 0
  have hK : 0 ≤ K := quadratic_growth_cutoff_nonneg hC _ _ _
  have hroot := quadratic_growth_unit_cost (ε := ε) (ξ := ξ) hC (2 * B) (2 * N) v w
  have hl : ‖quadraticLowCorrectionUnit B N P v w‖ ≤ 3 * T / N := by
    have hf := quadratic_filtered_unit_bound B P (fun _ => 1)
      (fun b => quadraticGaussDivisorBilinear (2 * N) (2 * N) 1
        (quadraticSqrtNormalize v) (quadraticSqrtNormalize w) b)
      (A := 1) (by norm_num) (by intros; norm_num)
    have hu := quadratic_unit_sqrt_gauss_bound (2 * B) N hN v w hv hw K K hK hK hmat hmat
    apply (show ‖quadraticLowCorrectionUnit B N P v w‖ ≤ _ by simpa [quadraticLowCorrectionUnit] using hf).trans
    apply hu.trans
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hroot (by norm_num : (0 : ℝ) ≤ 3)) (Nat.cast_nonneg N)
  have hb := quadratic_first_low_budget hM (show (0 : ℝ) < N by exact_mod_cast hN)
    he hB (show 0 < (1 : ℕ) by decide) hJ
    (show 0 ≤ C * (((2 * B : ℕ) : ℝ) * (2 * N : ℕ)) ^ ε by positivity)
    (show 0 ≤ ((2 * B : ℕ) : ℝ) ^ ξ by positivity)
    (show 0 ≤ Real.sqrt (quadraticDivisorMoment (2 * N) v) *
      Real.sqrt (quadraticDivisorMoment (2 * N) w) by positivity) (by simpa using hcut)
  have hb' : (M / ((e : ℝ) * N)) * T ≤
      32 * J * quadraticCorrectionGrowthScale C ε ξ M e B N v w := by
    simpa only [T, quadraticGrowthDivisorBudget, quadraticCorrectionGrowthScale,
      Nat.cast_mul, Nat.cast_ofNat, mul_assoc] using hb
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (div_pos hM (by exact_mod_cast he))]
  apply (mul_le_mul_of_nonneg_left hl (by positivity)).trans
  calc
    _ = 3 * (M / ((e : ℝ) * N) * T) := by ring
    _ ≤ 3 * (32 * J * quadraticCorrectionGrowthScale C ε ξ M e B N v w) :=
      mul_le_mul_of_nonneg_left hb' (by norm_num)
    _ = _ := by ring

theorem quadratic_high_unit_growth {C ε ξ M J : ℝ} (hC : 0 ≤ C)
    {e B N : ℕ} (hM : 0 < M) (he : 0 < e) (hB : 0 < B) (hN : 0 < N)
    (hJ : 1 ≤ J) (hcut : quadraticCorrectionBase M N e B / (8 * J) ≤ 1)
    (P : ℕ → Prop) (v w : ℕ → ℂ)
    (hmat : QuadraticSieveBound (2 * B) (2 * N)
      (quadraticGrowthCutoff C ε ξ (2 * B) (2 * N) 0)) :
    ‖((Real.sqrt M / Real.sqrt e : ℝ) : ℂ) * quadraticHighCorrectionUnit B N P v w‖ ≤
      384 * J * quadraticCorrectionGrowthScale C ε ξ M e B N v w := by
  classical
  let T := quadraticGrowthDivisorBudget C ε ξ (2 * B) (2 * N) 1 v w
  let K := quadraticGrowthCutoff C ε ξ (2 * B) (2 * N) 0
  have hK : 0 ≤ K := quadratic_growth_cutoff_nonneg hC _ _ _
  have hroot := quadratic_growth_unit_cost (ε := ε) (ξ := ξ) hC (2 * B) (2 * N) v w
  have hl : ‖quadraticHighCorrectionUnit B N P v w‖ ≤ 3 * T / Real.sqrt B := by
    have hf := quadratic_filtered_unit_root_weight B 1 hB (by decide) P
      (fun b => quadraticGaussDivisorBilinear (2 * N) (2 * N) 1 v w b)
    have hu := (quadratic_gauss_unit_divisor_bound (2 * B) (2 * N) (2 * N)
      K K hK hK hmat hmat v w).trans
      (mul_le_mul_of_nonneg_left hroot (by norm_num : (0 : ℝ) ≤ 3))
    have hf' : ‖quadraticHighCorrectionUnit B N P v w‖ ≤
        (1 / Real.sqrt B) * ∑ b ∈ oddSquarefreeRange (2 * B),
          ‖quadraticGaussDivisorBilinear (2 * N) (2 * N) 1 v w b‖ := by
      simpa [quadraticHighCorrectionUnit] using hf
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
    _ = 3 * (Real.sqrt M / (Real.sqrt e * Real.sqrt B) * T) := by ring
    _ ≤ 3 * (128 * J * quadraticCorrectionGrowthScale C ε ξ M e B N v w) :=
      mul_le_mul_of_nonneg_left hb' (by norm_num)
    _ = _ := by ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticWholeHighGrowth
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The complete high-divisor correction, with the unit boundary retained -/

namespace Ostmann

open scoped Classical BigOperators

theorem quadratic_whole_high_growth {C ε ξ M J : ℝ} (hC : 0 ≤ C)
    {e B N Q : ℕ} (hM : 0 < M) (he : 0 < e) (hB : 0 < B) (hN : 0 < N) (hQ : 1 ≤ Q)
    (hJ : 1 ≤ J) (P : ℕ → ℕ → Prop) (v w : ℕ → ℂ)
    (hP : ∀ d ∈ Finset.Icc 1 Q, ∀ b ∈ oddSquarefreeRange (2 * B), B ≤ b → P d b →
      quadraticCorrectionBase M N e B / (4 * J) ≤ (d : ℝ))
    (hmat : ∀ i ≤ Nat.log 2 (2 * N), QuadraticSieveBound (2 * B) (2 * N / 2 ^ i)
      (quadraticGrowthCutoff C ε ξ (2 * B) (2 * N) i)) :
    ‖((Real.sqrt M / Real.sqrt e : ℝ) : ℂ) * quadraticHighCorrectionTotal B N Q P v w‖ ≤
      ((Nat.log 2 Q + 2 : ℕ) : ℝ) *
        (384 * J * ((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ) ^ 2 *
          quadraticCorrectionGrowthScale C ε ξ M e B N v w) := by
  classical
  let S := quadraticCorrectionGrowthScale C ε ξ M e B N v w
  let V := 384 * J * ((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ) ^ 2 * S
  let F := fun d => ((Real.sqrt M / Real.sqrt e : ℝ) : ℂ) *
    ∑ b ∈ oddSquarefreeRange (2 * B), if B ≤ b ∧ P d b then
      (((ArithmeticFunction.moebius d : ℂ) / d) / (Real.sqrt b : ℂ)) *
        quadraticGaussDivisorBilinear (2 * N) (2 * N) d
          v w b else 0
  have hS : 0 ≤ S := by dsimp [S, quadraticCorrectionGrowthScale]; positivity
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hlog : (1 : ℝ) ≤ ((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ) ^ 2 := by
    have hh : (1 : ℝ) ≤ ((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_left 1 _
    nlinarith
  have hunit : ‖F 1‖ ≤ V := by
    by_cases hc : quadraticCorrectionBase M N e B / (8 * J) ≤ 1
    · have hu := quadratic_high_unit_growth hC hM he hB hN hJ hc (P 1) v w
        (by simpa only [pow_zero, Nat.div_one] using hmat 0 (Nat.zero_le _))
      have heq : F 1 = ((Real.sqrt M / Real.sqrt e : ℝ) : ℂ) * quadraticHighCorrectionUnit B N (P 1) v w := by
        simp [F, quadraticHighCorrectionUnit]
      rw [heq]
      apply hu.trans
      change 384 * J * S ≤ V
      dsimp [V]
      nlinarith [mul_le_mul_of_nonneg_left hlog (show 0 ≤ 384 * J * S by positivity)]
    · have hz : F 1 = 0 := by
        dsimp [F]
        have hh : (∑ b ∈ oddSquarefreeRange (2 * B), if B ≤ b ∧ P 1 b then
            (((ArithmeticFunction.moebius 1 : ℂ) / 1) / (Real.sqrt b : ℂ)) *
              quadraticGaussDivisorBilinear (2 * N) (2 * N) 1
                v w b else 0) = 0 := by
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
      exact hV
  have hblock (j : ℕ) (_hj : j < Nat.log 2 Q + 1) :
      ‖∑ d ∈ Finset.Ioc (2 ^ j) (2 * 2 ^ j), if d ≤ Q then F d else 0‖ ≤ V := by
    let D := 2 ^ j
    let P' := fun d b => d ≤ Q ∧ P d b
    have heq : (∑ d ∈ Finset.Ioc D (2 * D), if d ≤ Q then F d else 0) =
        ((Real.sqrt M / Real.sqrt e : ℝ) : ℂ) * quadraticHighCorrectionBand B N D P' v w := by
      simp only [quadraticHighCorrectionBand, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d _
      dsimp only [F, P']
      by_cases hd : d ≤ Q
      · simp only [hd, ite_true, if_true, true_and, Finset.mul_sum]
      · simp only [hd, ite_false, if_false, false_and, and_false, Finset.sum_const_zero, mul_zero]
    change ‖∑ d ∈ Finset.Ioc D (2 * D), if d ≤ Q then F d else 0‖ ≤ V
    rw [heq]
    by_cases hc : quadraticCorrectionBase M N e B / (8 * J) ≤ (D : ℝ)
    · exact quadratic_high_band_growth hC hM he hB hN (by dsimp [D]; positivity)
        hJ hc P' v w hmat
    · have hz : quadraticHighCorrectionBand B N D P' v w = 0 := by
        unfold quadraticHighCorrectionBand
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
  have hb := quadratic_correction_divisor_bound hQ F V (fun _ => V) hunit hblock
  have heq : (∑ d ∈ Finset.Icc 1 Q, F d) =
      ((Real.sqrt M / Real.sqrt e : ℝ) : ℂ) * quadraticHighCorrectionTotal B N Q P v w := by
    simp only [F, quadraticHighCorrectionTotal, Finset.mul_sum]
  rw [heq] at hb
  apply hb.trans_eq
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  dsimp [V, S]
  push_cast
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticWholeLowGrowth
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The complete low-divisor correction, with the unit boundary retained -/

namespace Ostmann

open scoped Classical BigOperators

theorem quadratic_whole_low_growth {C ε ξ M J : ℝ} (hC : 0 ≤ C)
    {e B N Q : ℕ} (hM : 0 < M) (he : 0 < e) (hB : 0 < B) (hN : 0 < N) (hQ : 1 ≤ Q)
    (hJ : 1 ≤ J) (P : ℕ → ℕ → Prop) (v w : ℕ → ℂ)
    (hv : ∀ n < N, v n = 0) (hw : ∀ n < N, w n = 0)
    (hP : ∀ d ∈ Finset.Icc 1 Q, ∀ b ∈ oddSquarefreeRange (2 * B), B ≤ b → P d b →
      (d : ℝ) ≤ 2 * quadraticCorrectionBase M N e B * J)
    (hmat : ∀ i ≤ Nat.log 2 (2 * N), QuadraticSieveBound (2 * B) (2 * N / 2 ^ i)
      (quadraticGrowthCutoff C ε ξ (2 * B) (2 * N) i)) :
    ‖((M / e : ℝ) : ℂ) * quadraticLowCorrectionTotal B N Q P v w‖ ≤
      ((Nat.log 2 Q + 2 : ℕ) : ℝ) *
        (96 * J * ((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ) ^ 2 *
          quadraticCorrectionGrowthScale C ε ξ M e B N v w) := by
  classical
  let S := quadraticCorrectionGrowthScale C ε ξ M e B N v w
  let V := 96 * J * ((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ) ^ 2 * S
  let F := fun d => ((M / e : ℝ) : ℂ) *
    ∑ b ∈ oddSquarefreeRange (2 * B), if B ≤ b ∧ P d b then
      (ArithmeticFunction.moebius d : ℂ) *
        quadraticGaussDivisorBilinear (2 * N) (2 * N) d
          (quadraticSqrtNormalize v) (quadraticSqrtNormalize w) b else 0
  have hS : 0 ≤ S := by dsimp [S, quadraticCorrectionGrowthScale]; positivity
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hlog : (1 : ℝ) ≤ ((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ) ^ 2 := by
    have hh : (1 : ℝ) ≤ ((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_left 1 _
    nlinarith
  have hunit : ‖F 1‖ ≤ V := by
    by_cases hc : 1 ≤ 2 * quadraticCorrectionBase M N e B * J
    · have hu := quadratic_low_unit_growth hC hM he hB hN hJ hc (P 1) v w hv hw
        (by simpa only [pow_zero, Nat.div_one] using hmat 0 (Nat.zero_le _))
      have heq : F 1 = ((M / e : ℝ) : ℂ) * quadraticLowCorrectionUnit B N (P 1) v w := by
        simp [F, quadraticLowCorrectionUnit]
      rw [heq]
      apply hu.trans
      change 96 * J * S ≤ V
      dsimp [V]
      nlinarith [mul_le_mul_of_nonneg_left hlog (show 0 ≤ 96 * J * S by positivity)]
    · have hz : F 1 = 0 := by
        dsimp [F]
        have hh : (∑ b ∈ oddSquarefreeRange (2 * B), if B ≤ b ∧ P 1 b then
            (ArithmeticFunction.moebius 1 : ℂ) *
              quadraticGaussDivisorBilinear (2 * N) (2 * N) 1
                (quadraticSqrtNormalize v) (quadraticSqrtNormalize w) b else 0) = 0 := by
          apply Finset.sum_eq_zero
          intro b hb
          have hn : ¬ (B ≤ b ∧ P 1 b) := by
            intro h
            apply hc
            simpa only [Nat.cast_one] using
              hP 1 (Finset.mem_Icc.mpr ⟨le_rfl, hQ⟩) b hb h.1 h.2
          simp only [hn, ite_false, if_false]
        rw [hh, mul_zero]
      rw [hz, norm_zero]
      exact hV
  have hblock (j : ℕ) (_hj : j < Nat.log 2 Q + 1) :
      ‖∑ d ∈ Finset.Ioc (2 ^ j) (2 * 2 ^ j), if d ≤ Q then F d else 0‖ ≤ V := by
    let D := 2 ^ j
    let P' := fun d b => d ≤ Q ∧ P d b
    have heq : (∑ d ∈ Finset.Ioc D (2 * D), if d ≤ Q then F d else 0) =
        ((M / e : ℝ) : ℂ) * quadraticLowCorrectionBand B N D P' v w := by
      simp only [quadraticLowCorrectionBand, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d _
      dsimp only [F, P']
      by_cases hd : d ≤ Q
      · simp only [hd, ite_true, if_true, true_and, Finset.mul_sum]
      · simp only [hd, ite_false, if_false, false_and, and_false, Finset.sum_const_zero, mul_zero]
    change ‖∑ d ∈ Finset.Ioc D (2 * D), if d ≤ Q then F d else 0‖ ≤ V
    rw [heq]
    by_cases hc : (D : ℝ) ≤ 2 * quadraticCorrectionBase M N e B * J
    · exact quadratic_low_band_growth hC hM he hB hN (by dsimp [D]; positivity)
        hJ hc P' v w hv hw hmat
    · have hz : quadraticLowCorrectionBand B N D P' v w = 0 := by
        unfold quadraticLowCorrectionBand
        apply Finset.sum_eq_zero
        intro d hd
        apply Finset.sum_eq_zero
        intro b hb
        have hn : ¬ (B ≤ b ∧ P' d b) := by
          intro h
          have hdp := (Finset.mem_Ioc.mp hd).1
          have hbound := hP d (Finset.mem_Icc.mpr ⟨Nat.succ_le_of_lt ((Nat.zero_le D).trans_lt hdp), h.2.1⟩) b hb h.1 h.2.2
          exact hc ((by exact_mod_cast hdp.le : (D : ℝ) ≤ d).trans hbound)
        simp only [hn, ite_false, if_false]
      rw [hz, mul_zero, norm_zero]
      exact hV
  have hb := quadratic_correction_divisor_bound hQ F V (fun _ => V) hunit hblock
  have heq : (∑ d ∈ Finset.Icc 1 Q, F d) =
      ((M / e : ℝ) : ℂ) * quadraticLowCorrectionTotal B N Q P v w := by
    simp only [F, quadraticLowCorrectionTotal, Finset.mul_sum]
  rw [heq] at hb
  apply hb.trans_eq
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  dsimp [V, S]
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

theorem quadratic_second_lower_le_upper {X J : ℝ} (hX : 0 ≤ X) (hJ : 1 ≤ J) :
    quadraticSecondLower X J ≤ quadraticSecondUpper X J := by
  have hlo : quadraticSecondLower X J ≤ X := by
    unfold quadraticSecondLower
    exact div_le_self hX (by linarith)
  have hhi : X ≤ quadraticSecondUpper X J := by
    unfold quadraticSecondUpper
    nlinarith [mul_le_mul_of_nonneg_left hJ hX]
  exact hlo.trans hhi

theorem quadratic_original_low_cut {M H N J : ℝ} {e B b d : ℕ}
    (hM : 0 < M) (hH : 0 < H) (hHN : H ≤ N) (he : 0 < e) (hB : 0 < B) (hJ : 1 ≤ J)
    (hb : B ≤ b) (hb' : b ≤ 2 * B)
    (hcut : (d : ℝ) ≤ quadraticSecondUpper (quadraticCorrectionBase M H e b) J) :
    (d : ℝ) ≤ 2 * quadraticCorrectionBase M N e B * J := by
  have hhi := (quadratic_correction_cutoff_band hM hH he hB hJ hb hb').2.2.2
  have hmono := quadratic_correction_base_mono hM hH hHN he hB
  exact (hcut.trans hhi).trans (by gcongr)

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

theorem quadratic_whole_original_low_growth {C ε ξ M H J : ℝ} (hC : 0 ≤ C)
    {e B N Q : ℕ} (hM : 0 < M) (hH : 0 < H) (hHN : H ≤ N)
    (he : 0 < e) (hB : 0 < B) (hN : 0 < N) (hQ : 1 ≤ Q) (hJ : 1 ≤ J)
    (R : ℕ → ℕ → Prop) (v w : ℕ → ℂ)
    (hv : ∀ n < N, v n = 0) (hw : ∀ n < N, w n = 0)
    (hmat : ∀ i ≤ Nat.log 2 (2 * N), QuadraticSieveBound (2 * B) (2 * N / 2 ^ i)
      (quadraticGrowthCutoff C ε ξ (2 * B) (2 * N) i)) :
    ‖((M / e : ℝ) : ℂ) * quadraticLowCorrectionTotal B N Q
        (fun d b => R d b ∧ (d : ℝ) ≤ quadraticSecondUpper (quadraticCorrectionBase M H e b) J) v w‖ ≤
      ((Nat.log 2 Q + 2 : ℕ) : ℝ) *
        (96 * J * ((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ) ^ 2 *
          quadraticCorrectionGrowthScale C ε ξ M e B N v w) := by
  apply quadratic_whole_low_growth hC hM he hB hN hQ hJ _ v w hv hw _ hmat
  intro d _ b hb hbB hp
  exact quadratic_original_low_cut hM hH hHN he hB hJ hbB
    (Finset.mem_Icc.mp (Finset.mem_filter.mp hb).1).2 hp.2

theorem quadratic_whole_original_high_growth {C ε ξ M H J : ℝ} (hC : 0 ≤ C)
    {e B N Q : ℕ} (hM : 0 < M) (hH : 0 < H) (hNH : (N : ℝ) ≤ 2 * H)
    (he : 0 < e) (hB : 0 < B) (hN : 0 < N) (hQ : 1 ≤ Q) (hJ : 1 ≤ J)
    (R : ℕ → ℕ → Prop) (v w : ℕ → ℂ)
    (hmat : ∀ i ≤ Nat.log 2 (2 * N), QuadraticSieveBound (2 * B) (2 * N / 2 ^ i)
      (quadraticGrowthCutoff C ε ξ (2 * B) (2 * N) i)) :
    ‖((Real.sqrt M / Real.sqrt e : ℝ) : ℂ) * quadraticHighCorrectionTotal B N Q
        (fun d b => R d b ∧ quadraticSecondUpper (quadraticCorrectionBase M H e b) J < (d : ℝ)) v w‖ ≤
      ((Nat.log 2 Q + 2 : ℕ) : ℝ) *
        (384 * (2 * J) * ((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ) ^ 2 *
          quadraticCorrectionGrowthScale C ε ξ M e B N v w) := by
  apply quadratic_whole_high_growth hC hM he hB hN hQ (by linarith : 1 ≤ 2 * J) _ v w _ hmat
  intro d _ b hb hbB hp
  have hX : 0 ≤ quadraticCorrectionBase M H e b := Real.sqrt_nonneg _
  apply quadratic_original_lower_cut hM hH (by exact_mod_cast hN) hNH he hB hJ hbB
    (Finset.mem_Icc.mp (Finset.mem_filter.mp hb).1).2
  exact (quadratic_second_lower_le_upper hX hJ).trans_lt hp.2

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticFullHighGrowth
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The entire original high correction at the current sieve exponent -/

namespace Ostmann

open scoped Classical BigOperators

theorem quadratic_full_high_growth {C ε ξ M H J : ℝ} (hC : 0 ≤ C) (hε : 0 ≤ ε)
    (hξ : 1 / 2 ≤ ξ) (hξ' : ξ ≤ 2) {e N Q K : ℕ}
    (hM : 0 < M) (hH : 0 < H) (hNH : (N : ℝ) ≤ 2 * H) (he : 0 < e)
    (hN : 0 < N) (hQ : 1 ≤ Q) (hK : 0 < K) (hJ : 1 ≤ J)
    (R : ℕ → ℕ → Prop) (v w : ℕ → ℂ)
    (hmat : ∀ B : ℕ, 0 < B → B ≤ K → ∀ i ≤ Nat.log 2 (2 * N),
      QuadraticSieveBound (2 * B) (2 * N / 2 ^ i)
        (quadraticGrowthCutoff C ε ξ (2 * B) (2 * N) i)) :
    ‖((Real.sqrt M / Real.sqrt e : ℝ) : ℂ) * quadraticFullHighCorrection M H J e N Q K R v w‖ ≤
      ((Nat.log 2 K + 1 : ℕ) : ℝ) * (((Nat.log 2 Q + 2 : ℕ) : ℝ) *
        (384 * (2 * J) * ((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ) ^ 2 *
          (10 * C * (4 * (K : ℝ) * N) ^ ε *
            (M + Real.sqrt M * (K : ℝ) ^ (ξ - 1 / 2)) *
              (Real.sqrt (quadraticDivisorMoment (2 * N) v) *
                Real.sqrt (quadraticDivisorMoment (2 * N) w))))) := by
  classical
  apply quadratic_correction_frequency_bound
  intro i hi
  let B := 2 ^ i
  have hB : 0 < B := by dsimp [B]; positivity
  have hBK : B ≤ K := quadratic_frequency_block_le hK hi
  let R' := fun d b => b ≤ K ∧ b < 2 * B ∧ R d b
  have heq : (∑ d ∈ Finset.Icc 1 Q, ∑ b ∈ oddSquarefreeRange (2 * B),
      if B ≤ b ∧ b ≤ K ∧ b < 2 * B then
        (if R d b ∧ quadraticSecondUpper (quadraticCorrectionBase M H e b) J < (d : ℝ) then
          (((ArithmeticFunction.moebius d : ℂ) / d) / (Real.sqrt b : ℂ)) * quadraticGaussDivisorBilinear (2 * N) (2 * N) d
            v w b else 0) else 0) =
      quadraticHighCorrectionTotal B N Q
        (fun d b => R' d b ∧ quadraticSecondUpper (quadraticCorrectionBase M H e b) J < (d : ℝ)) v w := by
    unfold quadraticHighCorrectionTotal
    apply Finset.sum_congr rfl
    intro d _
    apply Finset.sum_congr rfl
    intro b _
    dsimp [R']
    by_cases h₁ : B ≤ b <;> by_cases h₂ : b ≤ K <;> by_cases h₃ : b < 2 * B <;>
      simp [h₁, h₂, h₃]
  change ‖((Real.sqrt M / Real.sqrt e : ℝ) : ℂ) * _‖ ≤ _
  rw [heq]
  apply (quadratic_whole_original_high_growth hC hM hH hNH he hB hN hQ hJ R' v w
    (hmat B hB hBK)).trans
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
    (quadratic_correction_growth_uniform hC hε hξ hξ' hM he hB hBK le_rfl v w)
      (show 0 ≤ 384 * (2 * J) * ((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ) ^ 2 by positivity))
        (Nat.cast_nonneg _)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticFullLowGrowth
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The entire original low correction at the current sieve exponent -/

namespace Ostmann

open scoped Classical BigOperators

theorem quadratic_full_low_growth {C ε ξ M H J : ℝ} (hC : 0 ≤ C) (hε : 0 ≤ ε)
    (hξ : 1 / 2 ≤ ξ) (hξ' : ξ ≤ 2) {e N Q K : ℕ}
    (hM : 0 < M) (hH : 0 < H) (hHN : H ≤ N) (he : 0 < e)
    (hN : 0 < N) (hQ : 1 ≤ Q) (hK : 0 < K) (hJ : 1 ≤ J)
    (R : ℕ → ℕ → Prop) (v w : ℕ → ℂ)
    (hv : ∀ n < N, v n = 0) (hw : ∀ n < N, w n = 0)
    (hmat : ∀ B : ℕ, 0 < B → B ≤ K → ∀ i ≤ Nat.log 2 (2 * N),
      QuadraticSieveBound (2 * B) (2 * N / 2 ^ i)
        (quadraticGrowthCutoff C ε ξ (2 * B) (2 * N) i)) :
    ‖((M / e : ℝ) : ℂ) * quadraticFullLowCorrection M H J e N Q K R v w‖ ≤
      ((Nat.log 2 K + 1 : ℕ) : ℝ) * (((Nat.log 2 Q + 2 : ℕ) : ℝ) *
        (96 * J * ((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ) ^ 2 *
          (10 * C * (4 * (K : ℝ) * N) ^ ε *
            (M + Real.sqrt M * (K : ℝ) ^ (ξ - 1 / 2)) *
              (Real.sqrt (quadraticDivisorMoment (2 * N) v) *
                Real.sqrt (quadraticDivisorMoment (2 * N) w))))) := by
  classical
  apply quadratic_correction_frequency_bound
  intro i hi
  let B := 2 ^ i
  have hB : 0 < B := by dsimp [B]; positivity
  have hBK : B ≤ K := quadratic_frequency_block_le hK hi
  let R' := fun d b => b ≤ K ∧ b < 2 * B ∧ R d b
  have heq : (∑ d ∈ Finset.Icc 1 Q, ∑ b ∈ oddSquarefreeRange (2 * B),
      if B ≤ b ∧ b ≤ K ∧ b < 2 * B then
        (if R d b ∧ (d : ℝ) ≤ quadraticSecondUpper (quadraticCorrectionBase M H e b) J then
          (ArithmeticFunction.moebius d : ℂ) * quadraticGaussDivisorBilinear (2 * N) (2 * N) d
            (quadraticSqrtNormalize v) (quadraticSqrtNormalize w) b else 0) else 0) =
      quadraticLowCorrectionTotal B N Q
        (fun d b => R' d b ∧ (d : ℝ) ≤ quadraticSecondUpper (quadraticCorrectionBase M H e b) J) v w := by
    unfold quadraticLowCorrectionTotal
    apply Finset.sum_congr rfl
    intro d _
    apply Finset.sum_congr rfl
    intro b _
    dsimp [R']
    by_cases h₁ : B ≤ b <;> by_cases h₂ : b ≤ K <;> by_cases h₃ : b < 2 * B <;>
      simp [h₁, h₂, h₃]
  change ‖((M / e : ℝ) : ℂ) * _‖ ≤ _
  rw [heq]
  apply (quadratic_whole_original_low_growth hC hM hH hHN he hB hN hQ hJ R' v w hv hw
    (hmat B hB hBK)).trans
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
    (quadratic_correction_growth_uniform hC hε hξ hξ' hM he hB hBK le_rfl v w)
      (show 0 ≤ 96 * J * ((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ) ^ 2 by positivity))
        (Nat.cast_nonneg _)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticCorrectionEnvelope
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One explicit envelope for the three original second-Poisson corrections -/

namespace Ostmann

open MeasureTheory Set
open scoped Classical BigOperators SchwartzMap FourierTransform

theorem quadraticCorrectionEnvelope_nonneg {C ε ξ M J : ℝ}
    (hC : 0 ≤ C) (hM : 0 ≤ M) (hJ : 0 ≤ J) (N Q K L : ℕ) (v w : ℕ → ℂ) :
    0 ≤ quadraticCorrectionEnvelope C ε ξ M J N Q K L v w := by
  unfold quadraticCorrectionEnvelope
  positivity

theorem quadratic_second_combination_growth (ρ : 𝓢(ℝ, ℂ)) (a : ℝ) (ha : 1 ≤ |a|) :
    ∃ A : ℝ, 0 < A ∧ ∀ C ε ξ M H J : ℝ,
      0 ≤ C → 0 ≤ ε → 1 / 2 ≤ ξ → ξ ≤ 2 → ∀ e N Q K L : ℕ,
      0 < M → 0 < H → H ≤ N → (N : ℝ) ≤ 2 * H → 0 < e →
      0 < N → 1 ≤ Q → 0 < K → 1 ≤ J →
      ∀ R : ℕ → ℕ → Prop, ∀ v w : ℕ → ℂ,
      (∀ n < N, v n = 0) → (∀ n < N, w n = 0) →
      (∀ B : ℕ, 0 < B → B ≤ K → ∀ i ≤ Nat.log 2 (2 * N),
        QuadraticSieveBound (2 * B) (2 * N / 2 ^ i)
          (quadraticGrowthCutoff C ε ξ (2 * B) (2 * N) i)) →
      ‖(-𝓕 ρ 0 / 2 * ((M / e : ℝ) : ℂ)) *
          quadraticFullLowCorrection M H J e N Q K R v w -
        (((quadraticFresnelPhase a / (Real.sqrt |a| : ℂ)) *
          ∫ x in Ioi (0 : ℝ), ρ (x ^ 2)) / 2 * ((Real.sqrt M / Real.sqrt e : ℝ) : ℂ)) *
          quadraticFullHighCorrection M H J e N Q K R v w +
        (((1 : ℂ) / 2) * ((Real.sqrt M / Real.sqrt e : ℝ) : ℂ)) *
          quadraticFullMiddleCorrection ρ a ha M H J e N Q K L R v w‖ ≤
        A * quadraticCorrectionEnvelope C ε ξ M J N Q K L v w := by
  obtain ⟨Cu, Cb, hCu, hCb, hc⟩ := quadratic_full_middle_growth ρ a ha
  let F := ‖-𝓕 ρ 0 / 2‖
  let P := ‖((quadraticFresnelPhase a / (Real.sqrt |a| : ℂ)) *
    ∫ x in Ioi (0 : ℝ), ρ (x ^ 2)) / 2‖
  let A := 1 + 960 * F + 7680 * P + 2560 * (Cu + Cb)
  have hF : 0 ≤ F := norm_nonneg _
  have hP : 0 ≤ P := norm_nonneg _
  refine ⟨A, by dsimp [A]; positivity, ?_⟩
  intro C ε ξ M H J hC hε hξ hξ' e N Q K L hM hH hHN hNH he hN hQ hK hJ R v w hv hw hmat
  let T := C * (4 * (K : ℝ) * N) ^ ε * (M + Real.sqrt M * (K : ℝ) ^ (ξ - 1 / 2)) *
    (Real.sqrt (quadraticDivisorMoment (2 * N) v) * Real.sqrt (quadraticDivisorMoment (2 * N) w))
  let W := J * ((Nat.log 2 K + 1 : ℕ) : ℝ) * ((Nat.log 2 Q + 2 : ℕ) : ℝ) *
    ((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ) ^ 2 * T
  let E := quadraticCorrectionEnvelope C ε ξ M J N Q K L v w
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hE : 0 ≤ E := quadraticCorrectionEnvelope_nonneg hC hM.le (by linarith) _ _ _ _ _ _
  have hWE : W ≤ E := by
    change W ≤ (2 * (L : ℝ) + 1) * W
    nlinarith [show 0 ≤ (L : ℝ) by positivity]
  have hl := quadratic_full_low_growth hC hε hξ hξ' hM hH hHN he hN hQ hK hJ R v w hv hw hmat
  have hh := quadratic_full_high_growth hC hε hξ hξ' hM hH hNH he hN hQ hK hJ R v w hmat
  have hm := hc C ε ξ M H J hC hε hξ hξ' e N Q K L hM hH hNH he hN hQ hK hJ R v w hv hw hmat
  have hlow : ‖((M / e : ℝ) : ℂ) * quadraticFullLowCorrection M H J e N Q K R v w‖ ≤ 960 * E := by
    apply hl.trans
    calc
      _ = 960 * W := by dsimp [W, T]; ring
      _ ≤ 960 * E := by gcongr
  have hhigh : ‖((Real.sqrt M / Real.sqrt e : ℝ) : ℂ) *
      quadraticFullHighCorrection M H J e N Q K R v w‖ ≤ 7680 * E := by
    apply hh.trans
    calc
      _ = 7680 * W := by dsimp [W, T]; ring
      _ ≤ 7680 * E := by gcongr
  have hbracket : Cu + ((Nat.log 2 Q + 1 : ℕ) : ℝ) * Cb ≤
      ((Nat.log 2 Q + 2 : ℕ) : ℝ) * (Cu + Cb) := by
    push_cast
    nlinarith [show 0 ≤ (Nat.log 2 Q : ℝ) by positivity]
  have hmiddle : ‖((Real.sqrt M / Real.sqrt e : ℝ) : ℂ) *
      quadraticFullMiddleCorrection ρ a ha M H J e N Q K L R v w‖ ≤ 2560 * (Cu + Cb) * E := by
    apply hm.trans
    calc
      _ = (2560 * J * (2 * L + 1) * ((Nat.log 2 K + 1 : ℕ) : ℝ) *
        ((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ) ^ 2 * T) *
          (Cu + ((Nat.log 2 Q + 1 : ℕ) : ℝ) * Cb) := by dsimp [T]; ring
      _ ≤ (2560 * J * (2 * L + 1) * ((Nat.log 2 K + 1 : ℕ) : ℝ) *
        ((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ) ^ 2 * T) *
          (((Nat.log 2 Q + 2 : ℕ) : ℝ) * (Cu + Cb)) := by gcongr
      _ = 2560 * (Cu + Cb) * E := by dsimp [E, quadraticCorrectionEnvelope, T]; ring
  have hhalf : ‖(1 : ℂ) / 2‖ ≤ 1 := by norm_num
  let l := ((M / e : ℝ) : ℂ) * quadraticFullLowCorrection M H J e N Q K R v w
  let h := ((Real.sqrt M / Real.sqrt e : ℝ) : ℂ) * quadraticFullHighCorrection M H J e N Q K R v w
  let m := ((Real.sqrt M / Real.sqrt e : ℝ) : ℂ) *
    quadraticFullMiddleCorrection ρ a ha M H J e N Q K L R v w
  simp only [mul_assoc]
  change ‖(-𝓕 ρ 0 / 2) * l -
    (((quadraticFresnelPhase a / (Real.sqrt |a| : ℂ)) *
      ∫ x in Ioi (0 : ℝ), ρ (x ^ 2)) / 2) * h + ((1 : ℂ) / 2) * m‖ ≤ A * E
  apply (norm_add_le _ _).trans
  apply (add_le_add (norm_sub_le _ _) (le_refl _)).trans
  rw [norm_mul (-𝓕 ρ 0 / 2) l,
    norm_mul (((quadraticFresnelPhase a / (Real.sqrt |a| : ℂ)) *
      ∫ x in Ioi (0 : ℝ), ρ (x ^ 2)) / 2) h, norm_mul ((1 : ℂ) / 2) m]
  have hmid' := mul_le_mul hhalf hmiddle (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  have hlo' := mul_le_mul_of_nonneg_left hlow hF
  have hhi' := mul_le_mul_of_nonneg_left hhigh hP
  change F * ‖l‖ + P * ‖h‖ + ‖(1 : ℂ) / 2‖ * ‖m‖ ≤ A * E
  dsimp only [A]
  nlinarith

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

theorem quadratic_gcd_coefficient_energy {N D : ℕ} (hD : Squarefree D) (ho : Odd D)
    (v : ℕ → ℂ) :
    quadraticSieveEnergy (N / D) (quadraticDivisibilityCoeff D v) ≤ quadraticSieveEnergy N v := by
  rw [quadraticSieveEnergy_divisibility D N hD ho]
  apply Finset.sum_le_sum
  intro n _
  dsimp only
  split_ifs
  · rfl
  · simp

theorem quadratic_coprime_kernel_sum (N : ℕ) (v w : ℕ → ℂ) (F : ℕ → ℂ) :
    (∑ z ∈ quadraticGcdPairs N 1, v z.1 * conj (w z.2) * F (z.1 * z.2)) =
      ∑ s ∈ oddSquarefreeRange N, ∑ t ∈ oddSquarefreeRange N,
        if s.Coprime t then v s * conj (w t) * F (s * t) else 0 := by
  unfold quadraticGcdPairs
  rw [Finset.sum_filter, Finset.product_eq_sprod, Finset.sum_product]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticGcdRangeBridge
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A genuine dyadic range after removing the common divisor -/

namespace Ostmann

open scoped Classical BigOperators ComplexConjugate

theorem quadratic_gcd_pair_range_extension {L U : ℕ} (hLU : L ≤ U)
    (v w : ℕ → ℂ) (F : ℕ → ℂ) :
    (∑ z ∈ quadraticGcdPairs U 1,
      quadraticRangeCoeff L v z.1 * conj (quadraticRangeCoeff L w z.2) * F (z.1 * z.2)) =
      ∑ z ∈ quadraticGcdPairs L 1, v z.1 * conj (w z.2) * F (z.1 * z.2) := by
  have hsub : quadraticGcdPairs L 1 ⊆ quadraticGcdPairs U 1 := by
    intro z hz
    obtain ⟨hz, hg⟩ := Finset.mem_filter.mp hz
    obtain ⟨hs, ht⟩ := Finset.mem_product.mp hz
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨oddSquarefreeRange_mono hLU hs, oddSquarefreeRange_mono hLU ht⟩, hg⟩
  have hz (z : ℕ × ℕ) (hu : z ∈ quadraticGcdPairs U 1) (hl : z ∉ quadraticGcdPairs L 1) :
      quadraticRangeCoeff L v z.1 * conj (quadraticRangeCoeff L w z.2) * F (z.1 * z.2) = 0 := by
    obtain ⟨hu, hg⟩ := Finset.mem_filter.mp hu
    obtain ⟨hs, ht⟩ := Finset.mem_product.mp hu
    by_cases h₁ : z.1 ≤ L
    · have h₂ : ¬ z.2 ≤ L := by
        intro h₂
        apply hl
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, hg⟩
        · obtain ⟨hr, ho, hsf⟩ := Finset.mem_filter.mp hs
          exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hr).1, h₁⟩, ho, hsf⟩
        · obtain ⟨hr, ho, hsf⟩ := Finset.mem_filter.mp ht
          exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hr).1, h₂⟩, ho, hsf⟩
      simp [quadraticRangeCoeff, h₂]
    · simp [quadraticRangeCoeff, h₁]
  rw [← Finset.sum_subset hsub hz]
  apply Finset.sum_congr rfl
  intro z hz
  obtain ⟨hz, _⟩ := Finset.mem_filter.mp hz
  obtain ⟨hs, ht⟩ := Finset.mem_product.mp hz
  have h₁ := (Finset.mem_Icc.mp (Finset.mem_filter.mp hs).1).2
  have h₂ := (Finset.mem_Icc.mp (Finset.mem_filter.mp ht).1).2
  simp [quadraticRangeCoeff, h₁, h₂]

theorem quadratic_gcd_block_range (R D : ℕ) :
    (2 * R) / D ≤ 2 * quadraticGcdBlockSize R D := by
  have h₁ : (((2 * R) / D : ℕ) : ℝ) ≤ (2 * (R : ℝ)) / D := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using (Nat.cast_div_le (m := 2 * R) (n := D) (α := ℝ))
  have h₂ : (R : ℝ) / D ≤ (quadraticGcdBlockSize R D : ℝ) := Nat.le_ceil _
  have hh : (((2 * R) / D : ℕ) : ℝ) ≤ 2 * (quadraticGcdBlockSize R D : ℝ) := by
    rw [mul_div_assoc] at h₁
    linarith
  exact_mod_cast hh

theorem quadratic_gcd_block_lower {R D : ℕ} (hD : 0 < D) (v : ℕ → ℂ)
    (hv : ∀ n < R, v n = 0) {n : ℕ} (hn : n < quadraticGcdBlockSize R D) :
    quadraticGcdBlockCoeff R D v n = 0 := by
  have hnr : (n : ℝ) < (R : ℝ) / D := (Nat.lt_ceil).mp hn
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have hmul : D * n < R := by
    have hh := (lt_div_iff₀ hDR).mp hnr
    rw [mul_comm] at hh
    exact_mod_cast hh
  simp [quadraticGcdBlockCoeff, quadraticRangeCoeff, quadraticDivisibilityCoeff, hv _ hmul]

theorem quadratic_gcd_block_reindex {R D : ℕ} (hD : Squarefree D) (ho : Odd D)
    (v w : ℕ → ℂ) (F : ℕ → ℂ) :
    (∑ z ∈ quadraticGcdPairs (2 * R) D,
      v z.1 * conj (w z.2) * F (quadraticPairKernel z.1 z.2)) =
      ∑ z ∈ quadraticGcdPairs (2 * quadraticGcdBlockSize R D) 1,
        quadraticGcdBlockCoeff R D v z.1 * conj (quadraticGcdBlockCoeff R D w z.2) * F (z.1 * z.2) := by
  rw [quadratic_gcd_coefficient_reindex hD ho]
  exact (quadratic_gcd_pair_range_extension (quadratic_gcd_block_range R D)
    (quadraticDivisibilityCoeff D v) (quadraticDivisibilityCoeff D w) F).symm

theorem quadratic_range_energy {L U : ℕ} (hLU : L ≤ U) (v : ℕ → ℂ) :
    quadraticSieveEnergy U (quadraticRangeCoeff L v) = quadraticSieveEnergy L v := by
  unfold quadraticSieveEnergy
  have he : (∑ n ∈ oddSquarefreeRange L, ‖quadraticRangeCoeff L v n‖ ^ 2) =
      ∑ n ∈ oddSquarefreeRange U, ‖quadraticRangeCoeff L v n‖ ^ 2 := by
    apply Finset.sum_subset (oddSquarefreeRange_mono hLU)
    intro n hn hnL
    have hnl : ¬ n ≤ L := by
      intro hh
      apply hnL
      obtain ⟨hr, ho, hsf⟩ := Finset.mem_filter.mp hn
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hr).1, hh⟩, ho, hsf⟩
    simp [quadraticRangeCoeff, hnl]
  rw [← he]
  apply Finset.sum_congr rfl
  intro n hn
  simp [quadraticRangeCoeff, (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).2]

theorem quadratic_gcd_block_energy {R D : ℕ} (hD : Squarefree D) (ho : Odd D)
    (v : ℕ → ℂ) :
    quadraticSieveEnergy (2 * quadraticGcdBlockSize R D) (quadraticGcdBlockCoeff R D v) ≤
      quadraticSieveEnergy (2 * R) v := by
  unfold quadraticGcdBlockCoeff
  rw [quadratic_range_energy (quadratic_gcd_block_range R D)]
  exact quadratic_gcd_coefficient_energy hD ho v

theorem quadraticGcdBlockSize_pos {R D : ℕ} (hR : 0 < R) (hD : 0 < D) :
    0 < quadraticGcdBlockSize R D := by
  apply Nat.ceil_pos.mpr
  exact div_pos (by exact_mod_cast hR) (by exact_mod_cast hD)

theorem quadraticGcdBlockSize_le {R D : ℕ} (hD : 0 < D) :
    quadraticGcdBlockSize R D ≤ R := by
  apply Nat.ceil_le.mpr
  exact div_le_self (Nat.cast_nonneg _) (by exact_mod_cast hD)

theorem quadraticGcdBlockSize_comparable {R D : ℕ} (hD : 0 < D) (hDR : D ≤ R) :
    (R : ℝ) / D ≤ quadraticGcdBlockSize R D ∧
      (quadraticGcdBlockSize R D : ℝ) ≤ 2 * ((R : ℝ) / D) := by
  have hpos : (0 : ℝ) < D := by exact_mod_cast hD
  have hbase : 1 ≤ (R : ℝ) / D := (le_div_iff₀ hpos).mpr (by simpa only [one_mul] using (show (D : ℝ) ≤ R by exact_mod_cast hDR))
  constructor
  · exact Nat.le_ceil _
  · have hh := Nat.ceil_lt_add_one (show 0 ≤ (R : ℝ) / D by positivity)
    change (quadraticGcdBlockSize R D : ℝ) < (R : ℝ) / D + 1 at hh
    linarith

theorem quadratic_gcd_block_divisor_moment (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ R D : ℕ, Squarefree D → Odd D → ∀ v : ℕ → ℂ,
      quadraticDivisorMoment (2 * quadraticGcdBlockSize R D) (quadraticGcdBlockCoeff R D v) ≤
        C * (2 * (R : ℝ)) ^ ε * quadraticSieveEnergy (2 * R) v := by
  obtain ⟨C, hC, hc⟩ := quadratic_divisor_moment_bound ε hε
  refine ⟨C, hC, ?_⟩
  intro R D hD ho v
  apply (hc _ _).trans
  have hsize : (2 * quadraticGcdBlockSize R D : ℝ) ≤ 2 * R := by
    exact_mod_cast Nat.mul_le_mul_left 2 (quadraticGcdBlockSize_le (Nat.pos_of_ne_zero hD.ne_zero))
  have hpow := Real.rpow_le_rpow (by positivity) hsize hε.le
  have henergy := quadratic_gcd_block_energy (R := R) hD ho v
  have hn : 0 ≤ quadraticSieveEnergy (2 * quadraticGcdBlockSize R D) (quadraticGcdBlockCoeff R D v) :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  simp only [Nat.cast_mul, Nat.cast_ofNat]
  exact mul_le_mul (mul_le_mul_of_nonneg_left hpow hC.le) henergy hn (by positivity)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticGcdTwistMoment
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Every actual signed gcd coefficient keeps the original moment budget -/

namespace Ostmann

theorem quadratic_gcd_twist_moment (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ R D : ℕ, Squarefree D → Odd D →
      ∀ u : ℤ, ∀ v : ℕ → ℂ,
        quadraticDivisorMoment (2 * quadraticGcdBlockSize R D)
          (quadraticFrequencyTwist u 1 (quadraticGcdBlockCoeff R D v)) ≤
            C * (2 * (R : ℝ)) ^ ε * quadraticSieveEnergy (2 * R) v := by
  obtain ⟨C, hC, hc⟩ := quadratic_gcd_block_divisor_moment ε hε
  refine ⟨C, hC, ?_⟩
  intro R D hD ho u v
  exact (quadraticFrequencyTwist_moment u 1 _ _).trans (hc R D hD ho v)

theorem quadratic_gcd_twist_lower {R D : ℕ} (hD : 0 < D)
    (u : ℤ) (v : ℕ → ℂ) (hv : ∀ n < R, v n = 0) {n : ℕ}
    (hn : n < quadraticGcdBlockSize R D) :
    quadraticFrequencyTwist u 1 (quadraticGcdBlockCoeff R D v) n = 0 :=
  quadraticFrequencyTwist_zero u 1 _ (quadratic_gcd_block_lower hD v hv hn)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticCorrectionMoment
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The correction envelope uses only the original coefficient energy -/

namespace Ostmann

theorem quadraticCorrectionScalar_nonneg {C ε ξ M J : ℝ}
    (hC : 0 ≤ C) (hM : 0 ≤ M) (hJ : 0 ≤ J) (N Q K L : ℕ) :
    0 ≤ quadraticCorrectionScalar C ε ξ M J N Q K L := by
  unfold quadraticCorrectionScalar
  positivity

theorem quadraticCorrectionEnvelope_diagonal (C ε ξ M J : ℝ) (N Q K L : ℕ) (v : ℕ → ℂ) :
    quadraticCorrectionEnvelope C ε ξ M J N Q K L v v =
      quadraticCorrectionScalar C ε ξ M J N Q K L * quadraticDivisorMoment (2 * N) v := by
  have hv : 0 ≤ quadraticDivisorMoment (2 * N) v := by
    unfold quadraticDivisorMoment
    positivity
  unfold quadraticCorrectionEnvelope quadraticCorrectionScalar
  rw [Real.mul_self_sqrt hv]
  ring

theorem quadratic_gcd_correction_moment {δ : ℝ} (hδ : 0 < δ) :
    ∃ A : ℝ, 0 < A ∧ ∀ C ε ξ M J : ℝ, 0 ≤ C → 0 ≤ M → 0 ≤ J →
      ∀ R D Q K L : ℕ, Squarefree D → Odd D → ∀ u : ℤ, ∀ v : ℕ → ℂ,
        quadraticCorrectionEnvelope C ε ξ M J (quadraticGcdBlockSize R D) Q K L
          (quadraticFrequencyTwist u 1 (quadraticGcdBlockCoeff R D v))
          (quadraticFrequencyTwist u 1 (quadraticGcdBlockCoeff R D v)) ≤
        quadraticCorrectionScalar C ε ξ M J (quadraticGcdBlockSize R D) Q K L *
          (A * (2 * (R : ℝ)) ^ δ * quadraticSieveEnergy (2 * R) v) := by
  obtain ⟨A, hA, hm⟩ := quadratic_gcd_twist_moment δ hδ
  refine ⟨A, hA, ?_⟩
  intro C ε ξ M J hC hM hJ R D Q K L hD ho u v
  rw [quadraticCorrectionEnvelope_diagonal]
  exact mul_le_mul_of_nonneg_left (hm R D hD ho u v)
    (quadraticCorrectionScalar_nonneg hC hM hJ _ _ _ _)

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
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticCorrectionNormalization
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The three original divisor weights after Gauss normalization -/

namespace Ostmann

open MeasureTheory Set
open scoped Classical BigOperators SchwartzMap FourierTransform

theorem quadratic_scaled_divisor_sum (S : Finset ℕ) (X : ℝ) (F : ℕ → ℂ) :
    (∑ d ∈ S, (ArithmeticFunction.moebius d : ℂ) * ((X / d : ℝ) : ℂ) * F d) =
      (X : ℂ) * ∑ d ∈ S, ((ArithmeticFunction.moebius d : ℂ) / d) * F d := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d _
  push_cast
  ring

theorem quadratic_second_correction_normalized (ρ : 𝓢(ℝ, ℂ)) (a : ℝ) (ha : 1 ≤ |a|)
    {M : ℝ} {e q b : ℕ} (hM : 0 < M) (he : 0 < e) (hq : 0 < q) (hb : 0 < b)
    (U V : ℝ) (L : ℕ) :
    (((M / ((e : ℝ) * Real.sqrt q) : ℝ) : ℂ)) *
      quadraticSecondCorrection q ρ a ha (quadraticSecondScale M e q b) U V L =
    -(((M / ((e : ℝ) * Real.sqrt q) : ℝ) : ℂ)) / 2 * 𝓕 ρ 0 *
      (∑ d ∈ q.divisors.filter (fun d : ℕ => (d : ℝ) ≤ V), (ArithmeticFunction.moebius d : ℂ)) -
    (((Real.sqrt M / (Real.sqrt e * Real.sqrt b) : ℝ) : ℂ)) / 2 *
      ((quadraticFresnelPhase a / (Real.sqrt |a| : ℂ)) *
        ∫ x in Ioi (0 : ℝ), ρ (x ^ 2)) *
      (∑ d ∈ q.divisors.filter (fun d : ℕ => V < (d : ℝ)), (ArithmeticFunction.moebius d : ℂ) / d) +
    (((Real.sqrt M / (Real.sqrt e * Real.sqrt b) : ℝ) : ℂ)) / 2 *
      (∑ d ∈ q.divisors.filter (fun d : ℕ => U < (d : ℝ) ∧ (d : ℝ) ≤ V),
        ((ArithmeticFunction.moebius d : ℂ) / d) *
          quadraticLatticeWindow (𝓕 (quadraticFourierSquare ρ a ha))
            (quadraticSecondScale M e q b / d) L) := by
  let X := quadraticSecondScale M e q b
  let α : ℂ := ((M / ((e : ℝ) * Real.sqrt q) : ℝ) : ℂ)
  let β : ℂ := ((Real.sqrt M / (Real.sqrt e * Real.sqrt b) : ℝ) : ℂ)
  have hn : α * (X : ℂ) = β := by
    dsimp [α, β, X]
    rw [← Complex.ofReal_mul, quadratic_second_main_normalizer hM he hq hb]
  have hh : (∑ d ∈ q.divisors.filter (fun d : ℕ => V < (d : ℝ)),
      (ArithmeticFunction.moebius d : ℂ) * ((X / d : ℝ) : ℂ)) =
      (X : ℂ) * ∑ d ∈ q.divisors.filter (fun d : ℕ => V < (d : ℝ)),
        (ArithmeticFunction.moebius d : ℂ) / d := by
    simpa only [mul_one] using quadratic_scaled_divisor_sum
      (q.divisors.filter (fun d : ℕ => V < (d : ℝ))) X (fun _ => 1)
  have hm := quadratic_scaled_divisor_sum
    (q.divisors.filter (fun d : ℕ => U < (d : ℝ) ∧ (d : ℝ) ≤ V)) X
    (fun d => quadraticLatticeWindow (𝓕 (quadraticFourierSquare ρ a ha)) (X / d) L)
  change α * quadraticSecondCorrection q ρ a ha X U V L = _
  unfold quadraticSecondCorrection
  rw [hh, hm]
  calc
    _ = -α / 2 * 𝓕 ρ 0 *
        (∑ d ∈ q.divisors.filter (fun d : ℕ => (d : ℝ) ≤ V), (ArithmeticFunction.moebius d : ℂ)) -
      (α * (X : ℂ)) / 2 *
        ((quadraticFresnelPhase a / (Real.sqrt |a| : ℂ)) * ∫ x in Ioi (0 : ℝ), ρ (x ^ 2)) *
        (∑ d ∈ q.divisors.filter (fun d : ℕ => V < (d : ℝ)), (ArithmeticFunction.moebius d : ℂ) / d) +
      (α * (X : ℂ)) / 2 *
        (∑ d ∈ q.divisors.filter (fun d : ℕ => U < (d : ℝ) ∧ (d : ℝ) ≤ V),
          ((ArithmeticFunction.moebius d : ℂ) / d) *
            quadraticLatticeWindow (𝓕 (quadraticFourierSquare ρ a ha)) (X / d) L) := by ring
    _ = _ := by rw [hn]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticFilteredCorrection
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Filtered divisor corrections retain the original coefficient arrays -/

namespace Ostmann

open scoped Classical BigOperators ComplexConjugate

theorem quadratic_filtered_divisor_reindex (N : ℕ) (P : ℕ → Prop) [DecidablePred P]
    (H : ℕ → ℂ) (F : ℕ → ℕ → ℂ) :
    (∑ s ∈ oddSquarefreeRange (2 * N), ∑ t ∈ oddSquarefreeRange (2 * N),
      if s.Coprime t then F s t * (∑ d ∈ (s * t).divisors.filter P, H d) else 0) =
    ∑ d ∈ (Finset.Icc 1 ((2 * N) ^ 2)).filter P,
      H d * (∑ s ∈ oddSquarefreeRange (2 * N), ∑ t ∈ oddSquarefreeRange (2 * N),
        if s.Coprime t ∧ d ∣ s * t then F s t else 0) := by
  calc
    _ = ∑ s ∈ oddSquarefreeRange (2 * N), ∑ t ∈ oddSquarefreeRange (2 * N),
        if s.Coprime t then
          ∑ d ∈ (s * t).divisors, if P d then H d * F s t else 0
        else 0 := by
      apply Finset.sum_congr rfl
      intro s _
      apply Finset.sum_congr rfl
      intro t _
      by_cases hc : s.Coprime t
      · rw [ite_eq_left hc, ite_eq_left hc, Finset.mul_sum, Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro d _
        by_cases hp : P d <;> simp [hp, mul_comm]
      · rw [ite_eq_right hc, ite_eq_right hc]
    _ = ∑ d ∈ Finset.Icc 1 ((2 * N) ^ 2),
        ∑ s ∈ oddSquarefreeRange (2 * N), ∑ t ∈ oddSquarefreeRange (2 * N),
          if s.Coprime t ∧ d ∣ s * t then
            (if P d then H d * F s t else 0) else 0 :=
      quadratic_coprime_divisor_reindex N _
    _ = _ := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro d _
      by_cases hp : P d
      · simp only [hp, ite_true, if_true, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro s _
        apply Finset.sum_congr rfl
        intro t _
        simp only [mul_ite, mul_zero]
      · simp [hp]

theorem quadratic_low_correction_reindex (N : ℕ) (V : ℝ) (v w : ℕ → ℂ) (m : ℤ) :
    (∑ s ∈ oddSquarefreeRange (2 * N), ∑ t ∈ oddSquarefreeRange (2 * N),
      if s.Coprime t then
        (v s * conj (w t) * quadraticGaussMultiplier (s * t) *
          (jacobiSym m s : ℂ) * (jacobiSym m t : ℂ) / (Real.sqrt (s * t : ℕ) : ℂ)) *
        (∑ d ∈ (s * t).divisors.filter (fun d : ℕ => (d : ℝ) ≤ V),
          (ArithmeticFunction.moebius d : ℂ)) else 0) =
    ∑ d ∈ (Finset.Icc 1 ((2 * N) ^ 2)).filter (fun d : ℕ => (d : ℝ) ≤ V),
      (ArithmeticFunction.moebius d : ℂ) *
        quadraticGaussDivisorBilinear (2 * N) (2 * N) d
          (quadraticSqrtNormalize v) (quadraticSqrtNormalize w) m := by
  rw [quadratic_filtered_divisor_reindex]
  apply Finset.sum_congr rfl
  intro d _
  rw [quadratic_sqrt_gauss_divisor]
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro t _
  simp only [ite_mul, zero_mul, one_mul, ite_div, zero_div]

theorem quadratic_high_correction_reindex (N : ℕ) (V : ℝ) (v w : ℕ → ℂ) (m : ℤ) :
    (∑ s ∈ oddSquarefreeRange (2 * N), ∑ t ∈ oddSquarefreeRange (2 * N),
      if s.Coprime t then
        (v s * conj (w t) * quadraticGaussMultiplier (s * t) *
          (jacobiSym m s : ℂ) * (jacobiSym m t : ℂ)) *
        (∑ d ∈ (s * t).divisors.filter (fun d : ℕ => V < (d : ℝ)),
          (ArithmeticFunction.moebius d : ℂ) / d) else 0) =
    ∑ d ∈ (Finset.Icc 1 ((2 * N) ^ 2)).filter (fun d : ℕ => V < (d : ℝ)),
      ((ArithmeticFunction.moebius d : ℂ) / d) *
        quadraticGaussDivisorBilinear (2 * N) (2 * N) d v w m := by
  rw [quadratic_filtered_divisor_reindex]
  apply Finset.sum_congr rfl
  intro d _
  unfold quadraticGaussDivisorBilinear
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro t _
  simp only [ite_mul, zero_mul, one_mul]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticFullCorrectionReindex
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The literal frequency-first corrections are the bounded full sums -/

namespace Ostmann

open scoped Classical BigOperators SchwartzMap

theorem quadratic_weighted_filter_sum (S T : Finset ℕ) (P : ℕ → ℕ → Prop)
    (c : ℕ → ℂ) (f : ℕ → ℕ → ℂ) :
    (∑ b ∈ S, c b * ∑ d ∈ T.filter (fun d => P d b), f d b) =
      ∑ d ∈ T, ∑ b ∈ S, if P d b then c b * f d b else 0 := by
  classical
  simp only [Finset.sum_filter, Finset.mul_sum, mul_ite, mul_zero]
  exact Finset.sum_comm

theorem quadratic_full_low_reindex (M H J : ℝ) (e N Q K : ℕ) (v w : ℕ → ℂ) :
    (∑ b ∈ oddSquarefreeRange K,
      ∑ d ∈ (Finset.Icc 1 Q).filter (fun d : ℕ =>
        (d : ℝ) ≤ quadraticSecondUpper (quadraticCorrectionBase M H e b) J),
        (ArithmeticFunction.moebius d : ℂ) * quadraticGaussDivisorBilinear (2 * N) (2 * N) d
          (quadraticSqrtNormalize v) (quadraticSqrtNormalize w) b) =
      quadraticFullLowCorrection M H J e N Q K (fun _ _ => True) v w := by
  simpa only [one_mul, true_and, quadraticFullLowCorrection] using
    quadratic_weighted_filter_sum (oddSquarefreeRange K) (Finset.Icc 1 Q)
      (fun d b => (d : ℝ) ≤ quadraticSecondUpper (quadraticCorrectionBase M H e b) J)
      (fun _ => 1) (fun d b => (ArithmeticFunction.moebius d : ℂ) *
        quadraticGaussDivisorBilinear (2 * N) (2 * N) d
          (quadraticSqrtNormalize v) (quadraticSqrtNormalize w) b)

theorem quadratic_full_high_reindex (M H J : ℝ) (e N Q K : ℕ) (v w : ℕ → ℂ) :
    (∑ b ∈ oddSquarefreeRange K, (1 / (Real.sqrt b : ℂ)) *
      ∑ d ∈ (Finset.Icc 1 Q).filter (fun d : ℕ =>
        quadraticSecondUpper (quadraticCorrectionBase M H e b) J < (d : ℝ)),
        ((ArithmeticFunction.moebius d : ℂ) / d) *
          quadraticGaussDivisorBilinear (2 * N) (2 * N) d v w b) =
      quadraticFullHighCorrection M H J e N Q K (fun _ _ => True) v w := by
  rw [quadratic_weighted_filter_sum]
  unfold quadraticFullHighCorrection
  apply Finset.sum_congr rfl
  intro d _
  apply Finset.sum_congr rfl
  intro b _
  simp only [true_and]
  split_ifs <;> ring

theorem quadratic_full_middle_reindex (ρ : 𝓢(ℝ, ℂ)) (a : ℝ) (ha : 1 ≤ |a|)
    (M H J : ℝ) (e N Q K L : ℕ) (v w : ℕ → ℂ) :
    (∑ b ∈ oddSquarefreeRange K, (1 / (Real.sqrt b : ℂ)) *
      ∑ d ∈ (Finset.Icc 1 Q).filter (fun d : ℕ =>
        quadraticSecondLower (quadraticCorrectionBase M H e b) J < (d : ℝ) ∧
        (d : ℝ) ≤ quadraticSecondUpper (quadraticCorrectionBase M H e b) J),
        ((ArithmeticFunction.moebius d : ℂ) / d) *
          quadraticMiddleWindow ρ a ha M e N d v w b L) =
      quadraticFullMiddleCorrection ρ a ha M H J e N Q K L (fun _ _ => True) v w := by
  classical
  simp only [Finset.sum_filter, Finset.mul_sum, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  unfold quadraticFullMiddleCorrection
  apply Finset.sum_congr rfl
  intro d _
  apply Finset.sum_congr rfl
  intro b _
  simp only [true_and]
  split_ifs <;> ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticGcdCorrectionReindex
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The literal first-Poisson corrections are the bounded Gauss matrices -/

namespace Ostmann

open scoped Classical BigOperators ComplexConjugate

theorem quadratic_gcd_gauss_reindex {R D : ℕ} (hD : Squarefree D) (ho : Odd D)
    (v w : ℕ → ℂ) (m : ℤ) (F : ℕ → ℂ) :
    (∑ z ∈ quadraticGcdPairs (2 * R) D,
      v z.1 * conj (w z.2) *
        (quadraticGaussMultiplier (quadraticPairKernel z.1 z.2) *
          (jacobiSym m (quadraticPairKernel z.1 z.2) : ℂ) * F (quadraticPairKernel z.1 z.2))) =
      ∑ s ∈ oddSquarefreeRange (2 * quadraticGcdBlockSize R D),
        ∑ t ∈ oddSquarefreeRange (2 * quadraticGcdBlockSize R D),
          if s.Coprime t then
            (quadraticGcdBlockCoeff R D v s * conj (quadraticGcdBlockCoeff R D w t) *
              quadraticGaussMultiplier (s * t) * (jacobiSym m s : ℂ) * (jacobiSym m t : ℂ)) * F (s * t)
          else 0 := by
  rw [quadratic_gcd_block_reindex hD ho v w
    (fun q => quadraticGaussMultiplier q * (jacobiSym m q : ℂ) * F q)]
  rw [quadratic_coprime_kernel_sum (2 * quadraticGcdBlockSize R D)
    (quadraticGcdBlockCoeff R D v) (quadraticGcdBlockCoeff R D w)
    (fun q => quadraticGaussMultiplier q * (jacobiSym m q : ℂ) * F q)]
  apply Finset.sum_congr rfl
  intro s hs
  apply Finset.sum_congr rfl
  intro t ht
  by_cases hc : s.Coprime t
  · rw [ite_eq_left hc, ite_eq_left hc,
      jacobiSym.mul_right' m (Finset.mem_filter.mp hs).2.2.ne_zero
        (Finset.mem_filter.mp ht).2.2.ne_zero, Int.cast_mul]
    ring
  · rw [ite_eq_right hc, ite_eq_right hc]

theorem quadratic_gcd_low_correction_reindex {R D : ℕ} (hD : Squarefree D) (ho : Odd D)
    (v w : ℕ → ℂ) (m : ℤ) (V : ℝ) :
    (∑ z ∈ quadraticGcdPairs (2 * R) D,
      v z.1 * conj (w z.2) *
        (quadraticGaussMultiplier (quadraticPairKernel z.1 z.2) *
          (jacobiSym m (quadraticPairKernel z.1 z.2) : ℂ) *
          ((1 / (Real.sqrt (quadraticPairKernel z.1 z.2) : ℂ)) *
            ∑ d ∈ (quadraticPairKernel z.1 z.2).divisors.filter (fun d : ℕ => (d : ℝ) ≤ V),
              (ArithmeticFunction.moebius d : ℂ)))) =
      ∑ d ∈ (Finset.Icc 1 ((2 * quadraticGcdBlockSize R D) ^ 2)).filter (fun d : ℕ => (d : ℝ) ≤ V),
        (ArithmeticFunction.moebius d : ℂ) *
          quadraticGaussDivisorBilinear (2 * quadraticGcdBlockSize R D) (2 * quadraticGcdBlockSize R D) d
            (quadraticSqrtNormalize (quadraticGcdBlockCoeff R D v))
            (quadraticSqrtNormalize (quadraticGcdBlockCoeff R D w)) m := by
  rw [quadratic_gcd_gauss_reindex hD ho v w m
    (fun q => (1 / (Real.sqrt q : ℂ)) *
      ∑ d ∈ q.divisors.filter (fun d : ℕ => (d : ℝ) ≤ V), (ArithmeticFunction.moebius d : ℂ))]
  rw [← quadratic_low_correction_reindex]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro t _
  split_ifs <;> ring

theorem quadratic_gcd_high_correction_reindex {R D : ℕ} (hD : Squarefree D) (ho : Odd D)
    (v w : ℕ → ℂ) (m : ℤ) (V : ℝ) :
    (∑ z ∈ quadraticGcdPairs (2 * R) D,
      v z.1 * conj (w z.2) *
        (quadraticGaussMultiplier (quadraticPairKernel z.1 z.2) *
          (jacobiSym m (quadraticPairKernel z.1 z.2) : ℂ) *
          ∑ d ∈ (quadraticPairKernel z.1 z.2).divisors.filter (fun d : ℕ => V < (d : ℝ)),
            (ArithmeticFunction.moebius d : ℂ) / d)) =
      ∑ d ∈ (Finset.Icc 1 ((2 * quadraticGcdBlockSize R D) ^ 2)).filter (fun d : ℕ => V < (d : ℝ)),
        ((ArithmeticFunction.moebius d : ℂ) / d) *
          quadraticGaussDivisorBilinear (2 * quadraticGcdBlockSize R D) (2 * quadraticGcdBlockSize R D) d
            (quadraticGcdBlockCoeff R D v) (quadraticGcdBlockCoeff R D w) m := by
  rw [quadratic_gcd_gauss_reindex hD ho v w m
    (fun q => ∑ d ∈ q.divisors.filter (fun d : ℕ => V < (d : ℝ)), (ArithmeticFunction.moebius d : ℂ) / d)]
  exact quadratic_high_correction_reindex _ V _ _ m

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticMiddleCorrectionReindex
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original middle divisor correction is the bounded middle matrix -/

namespace Ostmann

open scoped Classical BigOperators ComplexConjugate SchwartzMap FourierTransform

private theorem filtered_parameter_reindex (N : ℕ) (P : ℕ → Prop) [DecidablePred P]
    (F : ℕ → ℕ → ℕ → ℂ) :
    (∑ s ∈ oddSquarefreeRange (2 * N), ∑ t ∈ oddSquarefreeRange (2 * N),
      if s.Coprime t then ∑ d ∈ (s * t).divisors.filter P, F s t d else 0) =
    ∑ d ∈ (Finset.Icc 1 ((2 * N) ^ 2)).filter P,
      ∑ s ∈ oddSquarefreeRange (2 * N), ∑ t ∈ oddSquarefreeRange (2 * N),
        if s.Coprime t ∧ d ∣ s * t then F s t d else 0 := by
  simp only [Finset.sum_filter]
  rw [quadratic_coprime_divisor_reindex]
  apply Finset.sum_congr rfl
  intro d _
  by_cases hp : P d <;> simp [hp]

theorem quadratic_middle_correction_reindex (ρ : 𝓢(ℝ, ℂ)) (a : ℝ) (ha : 1 ≤ |a|)
    (M U V : ℝ) (e N b L : ℕ) (v w : ℕ → ℂ) :
    (∑ s ∈ oddSquarefreeRange (2 * N), ∑ t ∈ oddSquarefreeRange (2 * N),
      if s.Coprime t then
        (v s * conj (w t) * quadraticGaussMultiplier (s * t) *
          (jacobiSym (b : ℤ) s : ℂ) * (jacobiSym (b : ℤ) t : ℂ)) *
        (∑ d ∈ (s * t).divisors.filter (fun d : ℕ => U < (d : ℝ) ∧ (d : ℝ) ≤ V),
          ((ArithmeticFunction.moebius d : ℂ) / d) *
            quadraticLatticeWindow (𝓕 (quadraticFourierSquare ρ a ha))
              (quadraticSecondScale M e (s * t) b / d) L) else 0) =
    ∑ d ∈ (Finset.Icc 1 ((2 * N) ^ 2)).filter (fun d : ℕ => U < (d : ℝ) ∧ (d : ℝ) ≤ V),
      ((ArithmeticFunction.moebius d : ℂ) / d) *
        quadraticMiddleWindow ρ a ha M e N d v w b L := by
  simp_rw [Finset.mul_sum]
  rw [filtered_parameter_reindex]
  apply Finset.sum_congr rfl
  intro d _
  unfold quadraticMiddleWindow
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  simp only [ite_mul, zero_mul, one_mul, mul_ite, mul_zero]
  split_ifs <;> ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticGcdMiddleCorrection
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original middle correction after gcd removal and the signed twist -/

namespace Ostmann

open scoped Classical BigOperators ComplexConjugate SchwartzMap FourierTransform

theorem quadratic_gcd_middle_correction_reindex (ρ : 𝓢(ℝ, ℂ)) (a : ℝ) (ha : 1 ≤ |a|)
    {R D : ℕ} (hD : Squarefree D) (ho : Odd D) (M U V : ℝ) (e b L : ℕ)
    (v w : ℕ → ℂ) (u : ℤ) :
    (∑ z ∈ quadraticGcdPairs (2 * R) D,
      v z.1 * conj (w z.2) *
        (quadraticGaussMultiplier (quadraticPairKernel z.1 z.2) *
          (jacobiSym (u * b) (quadraticPairKernel z.1 z.2) : ℂ) *
          ∑ d ∈ (quadraticPairKernel z.1 z.2).divisors.filter
              (fun d : ℕ => U < (d : ℝ) ∧ (d : ℝ) ≤ V),
            ((ArithmeticFunction.moebius d : ℂ) / d) *
              quadraticLatticeWindow (𝓕 (quadraticFourierSquare ρ a ha))
                (quadraticSecondScale M e (quadraticPairKernel z.1 z.2) b / d) L)) =
      ∑ d ∈ (Finset.Icc 1 ((2 * quadraticGcdBlockSize R D) ^ 2)).filter
          (fun d : ℕ => U < (d : ℝ) ∧ (d : ℝ) ≤ V),
        ((ArithmeticFunction.moebius d : ℂ) / d) *
          quadraticMiddleWindow ρ a ha M e (quadraticGcdBlockSize R D) d
            (quadraticFrequencyTwist u 1 (quadraticGcdBlockCoeff R D v))
            (quadraticFrequencyTwist u 1 (quadraticGcdBlockCoeff R D w)) b L := by
  have htw (f : ℕ → ℂ) (n : ℕ) :
      quadraticFrequencyTwist u 1 f n = (jacobiSym u n : ℂ) * f n := by
    unfold quadraticFrequencyTwist
    exact ite_eq_left (Nat.coprime_one_left n)
  rw [quadratic_gcd_gauss_reindex hD ho v w (u * b)
    (fun q => ∑ d ∈ q.divisors.filter (fun d : ℕ => U < (d : ℝ) ∧ (d : ℝ) ≤ V),
      ((ArithmeticFunction.moebius d : ℂ) / d) *
        quadraticLatticeWindow (𝓕 (quadraticFourierSquare ρ a ha))
          (quadraticSecondScale M e q b / d) L)]
  rw [← quadratic_middle_correction_reindex]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro t _
  by_cases hc : s.Coprime t
  · simp only [ite_eq_left hc, htw, map_mul, map_intCast]
    rw [jacobiSym.mul_left, jacobiSym.mul_left, Int.cast_mul, Int.cast_mul]
    ring
  · rw [ite_eq_right hc, ite_eq_right hc]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticSignedGcdCorrections
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Signed first-transform corrections use the original gcd coefficient arrays -/

namespace Ostmann

open scoped Classical BigOperators ComplexConjugate

theorem quadratic_gcd_low_signed_reindex {R D : ℕ} (hD : Squarefree D) (ho : Odd D)
    (v w : ℕ → ℂ) (u : ℤ) (b : ℕ) (V : ℝ) :
    (∑ z ∈ quadraticGcdPairs (2 * R) D,
      v z.1 * conj (w z.2) *
        (quadraticGaussMultiplier (quadraticPairKernel z.1 z.2) *
          (jacobiSym (u * b) (quadraticPairKernel z.1 z.2) : ℂ) *
          ((1 / (Real.sqrt (quadraticPairKernel z.1 z.2) : ℂ)) *
            ∑ d ∈ (quadraticPairKernel z.1 z.2).divisors.filter (fun d : ℕ => (d : ℝ) ≤ V),
              (ArithmeticFunction.moebius d : ℂ)))) =
      ∑ d ∈ (Finset.Icc 1 ((2 * quadraticGcdBlockSize R D) ^ 2)).filter (fun d : ℕ => (d : ℝ) ≤ V),
        (ArithmeticFunction.moebius d : ℂ) *
          quadraticGaussDivisorBilinear (2 * quadraticGcdBlockSize R D) (2 * quadraticGcdBlockSize R D) d
            (quadraticSqrtNormalize (quadraticFrequencyTwist u 1 (quadraticGcdBlockCoeff R D v)))
            (quadraticSqrtNormalize (quadraticFrequencyTwist u 1 (quadraticGcdBlockCoeff R D w))) b := by
  rw [quadratic_gcd_low_correction_reindex hD ho v w (u * b) V]
  apply Finset.sum_congr rfl
  intro d _
  rw [quadratic_gauss_bilinear_twist, quadratic_sqrt_twist_commute, quadratic_sqrt_twist_commute]

theorem quadratic_gcd_high_signed_reindex {R D : ℕ} (hD : Squarefree D) (ho : Odd D)
    (v w : ℕ → ℂ) (u : ℤ) (b : ℕ) (V : ℝ) :
    (∑ z ∈ quadraticGcdPairs (2 * R) D,
      v z.1 * conj (w z.2) *
        (quadraticGaussMultiplier (quadraticPairKernel z.1 z.2) *
          (jacobiSym (u * b) (quadraticPairKernel z.1 z.2) : ℂ) *
          ∑ d ∈ (quadraticPairKernel z.1 z.2).divisors.filter (fun d : ℕ => V < (d : ℝ)),
            (ArithmeticFunction.moebius d : ℂ) / d)) =
      ∑ d ∈ (Finset.Icc 1 ((2 * quadraticGcdBlockSize R D) ^ 2)).filter (fun d : ℕ => V < (d : ℝ)),
        ((ArithmeticFunction.moebius d : ℂ) / d) *
          quadraticGaussDivisorBilinear (2 * quadraticGcdBlockSize R D) (2 * quadraticGcdBlockSize R D) d
            (quadraticFrequencyTwist u 1 (quadraticGcdBlockCoeff R D v))
            (quadraticFrequencyTwist u 1 (quadraticGcdBlockCoeff R D w)) b := by
  rw [quadratic_gcd_high_correction_reindex hD ho v w (u * b) V]
  apply Finset.sum_congr rfl
  intro d _
  rw [quadratic_gauss_bilinear_twist]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticGcdSecondFrequency
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The literal second-Poisson correction at one signed frequency -/

namespace Ostmann

open MeasureTheory Set
open scoped Classical BigOperators ComplexConjugate SchwartzMap FourierTransform

theorem quadratic_gcd_second_frequency_split (ρ : 𝓢(ℝ, ℂ)) (a : ℝ) (ha : 1 ≤ |a|)
    {M : ℝ} (hM : 0 < M) (H J : ℝ) {R D e b : ℕ}
    (hD : Squarefree D) (ho : Odd D) (he : 0 < e) (hb : 0 < b)
    (u : ℤ) (v w : ℕ → ℂ) :
    let N := quadraticGcdBlockSize R D
    let v' := quadraticFrequencyTwist u 1 (quadraticGcdBlockCoeff R D v)
    let w' := quadraticFrequencyTwist u 1 (quadraticGcdBlockCoeff R D w)
    let U := quadraticSecondLower (quadraticCorrectionBase M H e b) J
    let V := quadraticSecondUpper (quadraticCorrectionBase M H e b) J
    let L := quadraticSecondWindow J
    quadraticGcdSecondFrequency ρ a ha M H J R D e b u v w =
      (-𝓕 ρ 0 / 2 * ((M / e : ℝ) : ℂ)) *
        (∑ d ∈ (Finset.Icc 1 ((2 * N) ^ 2)).filter (fun d : ℕ => (d : ℝ) ≤ V),
          (ArithmeticFunction.moebius d : ℂ) * quadraticGaussDivisorBilinear (2 * N) (2 * N) d
            (quadraticSqrtNormalize v') (quadraticSqrtNormalize w') b) -
      (((quadraticFresnelPhase a / (Real.sqrt |a| : ℂ)) *
        ∫ x in Ioi (0 : ℝ), ρ (x ^ 2)) / 2 *
        ((Real.sqrt M / (Real.sqrt e * Real.sqrt b) : ℝ) : ℂ)) *
        (∑ d ∈ (Finset.Icc 1 ((2 * N) ^ 2)).filter (fun d : ℕ => V < (d : ℝ)),
          ((ArithmeticFunction.moebius d : ℂ) / d) * quadraticGaussDivisorBilinear (2 * N) (2 * N) d v' w' b) +
      (((1 : ℂ) / 2) * ((Real.sqrt M / (Real.sqrt e * Real.sqrt b) : ℝ) : ℂ)) *
        (∑ d ∈ (Finset.Icc 1 ((2 * N) ^ 2)).filter (fun d : ℕ => U < (d : ℝ) ∧ (d : ℝ) ≤ V),
          ((ArithmeticFunction.moebius d : ℂ) / d) * quadraticMiddleWindow ρ a ha M e N d v' w' b L) := by
  dsimp only
  rw [← quadratic_gcd_low_signed_reindex hD ho v w u b,
    ← quadratic_gcd_high_signed_reindex hD ho v w u b,
    ← quadratic_gcd_middle_correction_reindex ρ a ha hD ho M
      (quadraticSecondLower (quadraticCorrectionBase M H e b) J)
      (quadraticSecondUpper (quadraticCorrectionBase M H e b) J) e b (quadraticSecondWindow J) v w u]
  simp only [Finset.mul_sum]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  unfold quadraticGcdSecondFrequency
  apply Finset.sum_congr rfl
  intro z hz
  obtain ⟨hz, _⟩ := Finset.mem_filter.mp hz
  obtain ⟨hs, ht⟩ := Finset.mem_product.mp hz
  have hq : 0 < quadraticPairKernel z.1 z.2 := Nat.pos_of_ne_zero
    (quadraticPairKernel_squarefree (Finset.mem_filter.mp hs).2.2 (Finset.mem_filter.mp ht).2.2).ne_zero
  have hn := quadratic_second_correction_normalized ρ a ha hM he hq hb
    (quadraticSecondLower (quadraticCorrectionBase M H e b) J)
    (quadraticSecondUpper (quadraticCorrectionBase M H e b) J) (quadraticSecondWindow J)
  dsimp only [quadraticSecondDyadicCorrection]
  simp only [quadraticCorrectionBase] at hn ⊢
  rw [hn]
  simp only [← Finset.mul_sum]
  push_cast
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticGcdSecondTotal
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The full signed second correction is exactly the three bounded sums -/

namespace Ostmann

open MeasureTheory Set
open scoped Classical BigOperators ComplexConjugate SchwartzMap FourierTransform

theorem quadratic_gcd_second_total_split (ρ : 𝓢(ℝ, ℂ)) (a : ℝ) (ha : 1 ≤ |a|)
    {M : ℝ} (hM : 0 < M) (H J : ℝ) {R D e : ℕ}
    (hD : Squarefree D) (ho : Odd D) (he : 0 < e) (K : ℕ)
    (u : ℤ) (v w : ℕ → ℂ) :
    let N := quadraticGcdBlockSize R D
    let v' := quadraticFrequencyTwist u 1 (quadraticGcdBlockCoeff R D v)
    let w' := quadraticFrequencyTwist u 1 (quadraticGcdBlockCoeff R D w)
    quadraticGcdSecondTotal ρ a ha M H J R D e K u v w =
      (-𝓕 ρ 0 / 2 * ((M / e : ℝ) : ℂ)) *
        quadraticFullLowCorrection M H J e N ((2 * N) ^ 2) K (fun _ _ => True) v' w' -
      (((quadraticFresnelPhase a / (Real.sqrt |a| : ℂ)) *
        ∫ x in Ioi (0 : ℝ), ρ (x ^ 2)) / 2 * ((Real.sqrt M / Real.sqrt e : ℝ) : ℂ)) *
        quadraticFullHighCorrection M H J e N ((2 * N) ^ 2) K (fun _ _ => True) v' w' +
      (((1 : ℂ) / 2) * ((Real.sqrt M / Real.sqrt e : ℝ) : ℂ)) *
        quadraticFullMiddleCorrection ρ a ha M H J e N ((2 * N) ^ 2) K (quadraticSecondWindow J)
          (fun _ _ => True) v' w' := by
  let N := quadraticGcdBlockSize R D
  let v' := quadraticFrequencyTwist u 1 (quadraticGcdBlockCoeff R D v)
  let w' := quadraticFrequencyTwist u 1 (quadraticGcdBlockCoeff R D w)
  let cL := -𝓕 ρ 0 / 2 * ((M / e : ℝ) : ℂ)
  let cH := ((quadraticFresnelPhase a / (Real.sqrt |a| : ℂ)) *
    ∫ x in Ioi (0 : ℝ), ρ (x ^ 2)) / 2 * ((Real.sqrt M / Real.sqrt e : ℝ) : ℂ)
  let cM := ((1 : ℂ) / 2) * ((Real.sqrt M / Real.sqrt e : ℝ) : ℂ)
  let lo := fun b => ∑ d ∈ (Finset.Icc 1 ((2 * N) ^ 2)).filter (fun d : ℕ =>
      (d : ℝ) ≤ quadraticSecondUpper (quadraticCorrectionBase M H e b) J),
    (ArithmeticFunction.moebius d : ℂ) * quadraticGaussDivisorBilinear (2 * N) (2 * N) d
      (quadraticSqrtNormalize v') (quadraticSqrtNormalize w') b
  let hi := fun b => ∑ d ∈ (Finset.Icc 1 ((2 * N) ^ 2)).filter (fun d : ℕ =>
      quadraticSecondUpper (quadraticCorrectionBase M H e b) J < (d : ℝ)),
    ((ArithmeticFunction.moebius d : ℂ) / d) * quadraticGaussDivisorBilinear (2 * N) (2 * N) d v' w' b
  let mi := fun b => ∑ d ∈ (Finset.Icc 1 ((2 * N) ^ 2)).filter (fun d : ℕ =>
      quadraticSecondLower (quadraticCorrectionBase M H e b) J < (d : ℝ) ∧
      (d : ℝ) ≤ quadraticSecondUpper (quadraticCorrectionBase M H e b) J),
    ((ArithmeticFunction.moebius d : ℂ) / d) *
      quadraticMiddleWindow ρ a ha M e N d v' w' b (quadraticSecondWindow J)
  have hp (b : ℕ) (hb : b ∈ oddSquarefreeRange K) :
      quadraticGcdSecondFrequency ρ a ha M H J R D e b u v w =
        cL * lo b - cH * ((1 / (Real.sqrt b : ℂ)) * hi b) +
          cM * ((1 / (Real.sqrt b : ℂ)) * mi b) := by
    have hs := quadratic_gcd_second_frequency_split (R := R) ρ a ha hM H J hD ho he
      (Finset.mem_Icc.mp (Finset.mem_filter.mp hb).1).1 u v w
    dsimp only at hs
    dsimp only [cL, cH, cM, lo, hi, mi, N, v', w']
    convert hs using 1 <;> first | (with_reducible_and_instances rfl) | (push_cast; ring)
  have hsum : quadraticGcdSecondTotal ρ a ha M H J R D e K u v w =
      cL * (∑ b ∈ oddSquarefreeRange K, lo b) -
        cH * (∑ b ∈ oddSquarefreeRange K, (1 / (Real.sqrt b : ℂ)) * hi b) +
        cM * (∑ b ∈ oddSquarefreeRange K, (1 / (Real.sqrt b : ℂ)) * mi b) := by
    unfold quadraticGcdSecondTotal
    rw [show (∑ b ∈ oddSquarefreeRange K, quadraticGcdSecondFrequency ρ a ha M H J R D e b u v w) =
      ∑ b ∈ oddSquarefreeRange K, (cL * lo b - cH * ((1 / (Real.sqrt b : ℂ)) * hi b) +
        cM * ((1 / (Real.sqrt b : ℂ)) * mi b)) from Finset.sum_congr rfl hp]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hsum]
  rw [show (∑ b ∈ oddSquarefreeRange K, lo b) = _ from quadratic_full_low_reindex M H J e N _ K v' w',
    show (∑ b ∈ oddSquarefreeRange K, (1 / (Real.sqrt b : ℂ)) * hi b) = _ from
      quadratic_full_high_reindex M H J e N _ K v' w',
    show (∑ b ∈ oddSquarefreeRange K, (1 / (Real.sqrt b : ℂ)) * mi b) = _ from
      quadratic_full_middle_reindex ρ a ha M H J e N _ K (quadraticSecondWindow J) v' w']

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticFirstCorrectionIdentity
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original first-transform correction is the finite signed gcd family -/

namespace Ostmann

open scoped Classical BigOperators ComplexConjugate

private theorem four_sum_rotate {ι κ ν μ : Type*}
    (S : Finset ι) (T : Finset κ) (U : Finset ν) (V : Finset μ) (F : ι → κ → ν → μ → ℂ) :
    (∑ z ∈ S, ∑ e ∈ T, ∑ a ∈ U, ∑ b ∈ V, F z e a b) =
      ∑ e ∈ T, ∑ a ∈ U, ∑ b ∈ V, ∑ z ∈ S, F z e a b := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  exact Finset.sum_comm

theorem quadratic_first_correction_identity (M R K D : ℕ) (H J : ℝ) (v w : ℕ → ℂ) :
    (∑ z ∈ quadraticGcdPairs (2 * R) D,
      v z.1 * conj (w z.2) * quadraticFirstSecondCorrections M D (quadraticPairKernel z.1 z.2) K H J) =
      ∑ e ∈ (2 * D).divisors, (ArithmeticFunction.moebius e : ℂ) *
        ∑ a : quadraticPoissonSigns,
          quadraticGcdSecondTotal quadraticSieveWeight (a : ℤ)
            (quadraticPoissonSigns_abs a.property) M H J R D e K ((e : ℤ) * a) v w := by
  unfold quadraticFirstSecondCorrections quadraticGcdSecondTotal quadraticGcdSecondFrequency
  simp only [Finset.mul_sum]
  rw [four_sum_rotate]
  apply Finset.sum_congr rfl
  intro e _
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro z _
  simp only [jacobiSym.mul_left, Int.cast_mul]
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticGcdSecondGrowth
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual signed gcd term at the current quadratic-sieve exponent -/

namespace Ostmann

open scoped Classical BigOperators SchwartzMap

theorem quadraticCorrectionScalar_scale (C ε ξ M J : ℝ) (N Q K L : ℕ) :
    quadraticCorrectionScalar C ε ξ M J N Q K L =
      C * quadraticCorrectionScalar 1 ε ξ M J N Q K L := by
  unfold quadraticCorrectionScalar
  ring

theorem quadratic_gcd_second_growth {ξ ε δ : ℝ} (h : QuadraticSieveGrowth ξ)
    (hξ : 1 / 2 ≤ ξ) (hξ' : ξ ≤ 2) (hε : 0 < ε) (hδ : 0 < δ)
    (ρ : 𝓢(ℝ, ℂ)) (a : ℝ) (ha : 1 ≤ |a|) :
    ∃ A : ℝ, 0 < A ∧ ∀ M J : ℝ, 0 < M → 1 ≤ J →
      ∀ R D e K : ℕ, 0 < R → Squarefree D → Odd D → D ≤ R → 0 < e → 0 < K →
      ∀ u : ℤ, ∀ v : ℕ → ℂ, (∀ n < R, v n = 0) →
        ‖quadraticGcdSecondTotal ρ a ha M ((R : ℝ) / D) J R D e K u v v‖ ≤
          A * quadraticCorrectionScalar 1 ε ξ M J (quadraticGcdBlockSize R D)
            ((2 * quadraticGcdBlockSize R D) ^ 2) K (quadraticSecondWindow J) *
              (2 * (R : ℝ)) ^ δ * quadraticSieveEnergy (2 * R) v := by
  obtain ⟨A₀, hA₀, hc⟩ := quadratic_second_combination_growth ρ a ha
  obtain ⟨C, hC, hmat⟩ := quadratic_growth_cutoff_bounds h hε
  obtain ⟨A₁, hA₁, hmom⟩ := quadratic_gcd_correction_moment hδ
  refine ⟨A₀ * C * A₁, by positivity, ?_⟩
  intro M J hM hJ R D e K hR hD ho hDR he hK u v hv
  have hD₀ : 0 < D := Nat.pos_of_ne_zero hD.ne_zero
  have hH : 0 < (R : ℝ) / D := div_pos (by exact_mod_cast hR) (by exact_mod_cast hD₀)
  have hN := quadraticGcdBlockSize_pos hR hD₀
  obtain ⟨hHN, hNH⟩ := quadraticGcdBlockSize_comparable hD₀ hDR
  have hs : ∀ n < quadraticGcdBlockSize R D,
      quadraticFrequencyTwist u 1 (quadraticGcdBlockCoeff R D v) n = 0 :=
    fun n hn => quadratic_gcd_twist_lower hD₀ u v hv hn
  have hQ : 1 ≤ (2 * quadraticGcdBlockSize R D) ^ 2 := by
    have : 1 ≤ quadraticGcdBlockSize R D := hN
    nlinarith
  have hb := hc C ε ξ M ((R : ℝ) / D) J hC.le hε.le hξ hξ' e
    (quadraticGcdBlockSize R D) ((2 * quadraticGcdBlockSize R D) ^ 2) K (quadraticSecondWindow J)
    hM hH hHN hNH he hN hQ hK hJ (fun _ _ => True)
    (quadraticFrequencyTwist u 1 (quadraticGcdBlockCoeff R D v))
    (quadraticFrequencyTwist u 1 (quadraticGcdBlockCoeff R D v)) hs hs
    (fun B hB _ => hmat (2 * B) (2 * quadraticGcdBlockSize R D) (by omega) (by omega))
  have hm := hmom C ε ξ M J hC.le hM.le (by linarith)
    R D ((2 * quadraticGcdBlockSize R D) ^ 2) K (quadraticSecondWindow J) hD ho u v
  calc
    _ ≤ A₀ * quadraticCorrectionEnvelope C ε ξ M J (quadraticGcdBlockSize R D)
        ((2 * quadraticGcdBlockSize R D) ^ 2) K (quadraticSecondWindow J)
        (quadraticFrequencyTwist u 1 (quadraticGcdBlockCoeff R D v))
        (quadraticFrequencyTwist u 1 (quadraticGcdBlockCoeff R D v)) := by
      rw [quadratic_gcd_second_total_split ρ a ha hM _ _ hD ho he]
      exact hb
    _ ≤ A₀ * (quadraticCorrectionScalar C ε ξ M J (quadraticGcdBlockSize R D)
        ((2 * quadraticGcdBlockSize R D) ^ 2) K (quadraticSecondWindow J) *
          (A₁ * (2 * (R : ℝ)) ^ δ * quadraticSieveEnergy (2 * R) v)) :=
      mul_le_mul_of_nonneg_left hm hA₀.le
    _ = _ := by rw [quadraticCorrectionScalar_scale]; ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticFirstTotalGrowth
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Every original first-transform correction, with all four signs retained -/

namespace Ostmann

open scoped Classical BigOperators ComplexConjugate

theorem quadratic_first_total_growth_oai {ξ ε δ : ℝ} (h : QuadraticSieveGrowth ξ)
    (hξ : 1 / 2 ≤ ξ) (hξ' : ξ ≤ 2) (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ A : ℝ, 0 < A ∧ ∀ M R D K : ℕ, 0 < M → 0 < R → Squarefree D → Odd D → D ≤ R → 0 < K →
      ∀ J : ℝ, 1 ≤ J → ∀ v : ℕ → ℂ, (∀ n < R, v n = 0) →
        ‖∑ z ∈ quadraticGcdPairs (2 * R) D, v z.1 * conj (v z.2) *
          quadraticFirstSecondCorrections M D (quadraticPairKernel z.1 z.2) K ((R : ℝ) / D) J‖ ≤
        A * (2 * D : ℝ) * quadraticCorrectionScalar 1 ε ξ M J (quadraticGcdBlockSize R D)
          ((2 * quadraticGcdBlockSize R D) ^ 2) K (quadraticSecondWindow J) *
            (2 * (R : ℝ)) ^ δ * quadraticSieveEnergy (2 * R) v := by
  classical
  have ha (a : quadraticPoissonSigns) := quadratic_gcd_second_growth h hξ hξ' hε hδ
    quadraticSieveWeight (a : ℤ) (quadraticPoissonSigns_abs a.property)
  choose A hA hbound using ha
  let C := 1 + ∑ a : quadraticPoissonSigns, A a
  have hC : 0 < C := by
    have := Finset.sum_nonneg (fun a (_ : a ∈ (Finset.univ : Finset quadraticPoissonSigns)) => (hA a).le)
    change 0 < 1 + (∑ a : quadraticPoissonSigns, A a)
    linarith only [this]
  refine ⟨C, hC, ?_⟩
  intro M R D K hM hR hD ho hDR hK J hJ v hv
  let T := quadraticCorrectionScalar 1 ε ξ M J (quadraticGcdBlockSize R D)
    ((2 * quadraticGcdBlockSize R D) ^ 2) K (quadraticSecondWindow J) *
      (2 * (R : ℝ)) ^ δ * quadraticSieveEnergy (2 * R) v
  have hT : 0 ≤ T := by
    dsimp [T]
    exact mul_nonneg (mul_nonneg
      (quadraticCorrectionScalar_nonneg zero_le_one (by positivity) (by linarith) _ _ _ _)
      (Real.rpow_nonneg (by positivity) _)) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  rw [quadratic_first_correction_identity]
  calc
    _ ≤ ∑ e ∈ (2 * D).divisors, ∑ a : quadraticPoissonSigns,
        ‖quadraticGcdSecondTotal quadraticSieveWeight (a : ℤ)
          (quadraticPoissonSigns_abs a.property) M ((R : ℝ) / D) J R D e K ((e : ℤ) * a) v v‖ := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro e _
      rw [norm_mul]
      have he : ‖(ArithmeticFunction.moebius e : ℂ)‖ ≤ 1 := by
        rw [Complex.norm_intCast]
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := e)
      exact (mul_le_mul_of_nonneg_right he (norm_nonneg _)).trans
        (by simpa only [one_mul] using norm_sum_le (Finset.univ : Finset quadraticPoissonSigns) _)
    _ ≤ ∑ e ∈ (2 * D).divisors, ∑ a : quadraticPoissonSigns, A a * T := by
      apply Finset.sum_le_sum
      intro e he
      apply Finset.sum_le_sum
      intro a _
      simpa only [T, mul_assoc] using hbound a M J (by exact_mod_cast hM) hJ
        R D e K hR hD ho hDR (Nat.pos_of_mem_divisors he) hK ((e : ℤ) * a) v hv
    _ = ((2 * D).divisors.card : ℝ) * ((∑ a : quadraticPoissonSigns, A a) * T) := by
      simp only [← Finset.sum_mul, Finset.sum_const, nsmul_eq_mul]
      ring
    _ ≤ (2 * D : ℝ) * (C * T) := by
      apply mul_le_mul
      · exact_mod_cast Nat.card_divisors_le_self (2 * D)
      · apply mul_le_mul_of_nonneg_right _ hT
        change (∑ a : quadraticPoissonSigns, A a) ≤ 1 + (∑ a : quadraticPoissonSigns, A a)
        linarith
      · exact mul_nonneg (Finset.sum_nonneg fun a _ => (hA a).le) hT
      · positivity
    _ = _ := by dsimp [T]; ring

end Ostmann

end OAI
end

theorem solution : type_of% @OAI.Ostmann.quadratic_first_total_growth_oai := @OAI.Ostmann.quadratic_first_total_growth_oai
