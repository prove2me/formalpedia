-- Prove2me | solution 1 for OAI.Ostmann.publishedQuadraticLargeSieve
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T06:44:32.402455+00:00
-- url     : https://prove2.me/submissions/a06421ac-0d46-4336-8409-9b3c7bda69e8

import Mathlib
import Definitions.Def_OAIQ095D006
import Theorems.Thm_OAI_Ostmann_quadratic_rough_power_growth

section
-- module Solutions.OAIQ095_OS.Compat
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
/-- Mathlib d13f23b's `Finset.sum_le_sum_of_injOn`; ours has no such lemma (LipschitzHilbert, oaiq-090). -/
theorem sum_le_sum_of_injOn {ι κ M : Type*} [DecidableEq κ] [AddCommMonoid M] [PartialOrder M]
    [IsOrderedAddMonoid M] {s : Finset ι} {t : Finset κ} {f : ι → M} {g : κ → M} (e : ι → κ)
    (he : Set.InjOn e s) (hest : s.image e ⊆ t) (hf : ∀ i ∈ s, f i ≤ g (e i))
    (hg : ∀ j ∈ t, j ∉ s.image e → 0 ≤ g j) : ∑ i ∈ s, f i ≤ ∑ j ∈ t, g j := by
  calc ∑ i ∈ s, f i ≤ ∑ i ∈ s, g (e i) := Finset.sum_le_sum hf
    _ = ∑ j ∈ s.image e, g j := (Finset.sum_image he).symm
    _ ≤ ∑ j ∈ t, g j := Finset.sum_le_sum_of_subset_of_nonneg hest hg
end OAICompat434

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
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticSieve_PrimeJacobiCharacter
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
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
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
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
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_OrdinaryPrimeIntervals
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The ordinary prime interval and its normalization

The conductor-one character is trivial, so the ordinary prime prior has
no Page correction. Its logarithmic interval mass and inverse bound are
derived from the same published theta input.
-/

namespace Ostmann

open Filter MeasureTheory

theorem PublishedProgressionInput.localZero_one (P : PublishedProgressionInput) :
    P.localZero 1 = none := by
  cases he : P.localZero 1 with
  | none => rfl
  | some e => exact False.elim (e.modulus_ne_one (Nat.dvd_one.mp (P.divides 1 e he)))

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

 theorem primitive_character_sieve {q : ℕ} [NeZero q] {ι : Type*} [Fintype ι]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (c : ι → ℂ) (a : ι → ZMod q) :
    ‖∑ j, c j * χ⁻¹ (a j)‖ ^ 2 ≤
      ∑ u : (ZMod q)ˣ, ‖∑ j, c j * ZMod.stdAddChar ((u : ZMod q) * a j)‖ ^ 2 := by
  let U : (ZMod q)ˣ → ℂ := fun u => star (χ u)
  let V : (ZMod q)ˣ → ℂ := fun u => ∑ j, c j * ZMod.stdAddChar ((u : ZMod q) * a j)
  have hid : star U ⬝ᵥ V = (∑ j, c j * χ⁻¹ (a j)) * gaussSum χ ZMod.stdAddChar := by
    change (∑ u : (ZMod q)ˣ, star (star (χ u)) * ∑ j, c j * ZMod.stdAddChar ((u : ZMod q) * a j)) = _
    simp only [star_star, Finset.mul_sum]
    rw [Finset.sum_comm]
    calc
      _ = ∑ j, c j * ∑ u : (ZMod q)ˣ, χ u * ZMod.stdAddChar ((u : ZMod q) * a j) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro u _
        ring
      _ = _ := by simp_rw [primitive_unit_gauss χ hχ]; rw [Finset.sum_mul]; congr 1; funext j; ring
  have hU : (∑ u, ‖U u‖ ^ 2) ≤ (q : ℝ) := by
    have hcard : Fintype.card (ZMod q)ˣ ≤ Fintype.card (ZMod q) :=
      Fintype.card_le_of_injective (fun u : (ZMod q)ˣ => (u : ZMod q)) Units.val_injective
    simp only [U, norm_star, χ.unit_norm_eq_one, one_pow, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, mul_one]
    exact_mod_cast (hcard.trans_eq (ZMod.card q))
  have hh := finite_complex_cauchy_schwarz U V
  rw [hid, norm_mul, mul_pow, primitive_gauss_norm_sq χ hχ] at hh
  have hE : 0 ≤ ∑ u, ‖V u‖ ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hm := hh.trans (mul_le_mul_of_nonneg_right hU hE)
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  exact (mul_le_mul_iff_right₀ hq).mp (by simpa only [mul_comm] using hm)

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

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_ProgressionPrincipalPNT
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The conductor-one consequence of the progression input

The principal smooth PNT is not an independent input: the conductor-one
theta estimate, elementary prime-power removal and partial summation suffice.
-/

namespace Ostmann

open Filter
open scoped Classical BigOperators

theorem primeProgressionTheta_one (x : ℝ) :
    primeProgressionTheta 1 0 x = Chebyshev.theta x := by
  rw [Chebyshev.theta_eq_sum_Icc]
  simp [primeProgressionTheta, primeProgressionLog, Finset.sum_filter, Nat.ModEq, Nat.mod_one]

theorem PublishedProgressionInput.principal_theta_bound (P : PublishedProgressionInput)
    (x : ℝ) (hx : 2 ≤ x) :
    |Chebyshev.theta x - x| ≤
      P.errorConstant * x * Real.exp (-P.decay * Real.sqrt (Real.log x)) := by
  have h := P.theta 1 le_rfl 0 (by norm_num) x hx
  simpa only [primeProgressionTheta_one, P.localZero_one, pageCoefficient, pageBeta,
    Nat.totient_one, Nat.cast_one, thetaMainTerm, zero_mul, zero_div, sub_zero, div_one]
    using h

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_SummandSizePrimeBand
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Elementary dyadic prime counts used in the summand-size argument -/

namespace Ostmann

open Filter
open scoped Classical BigOperators

 theorem actual_theta_relative_small {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, |Chebyshev.theta x - x| ≤ ε * x := by
  let P := actualProgressionInput
  have ht := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 P.decay P.decay_pos).comp
    (Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop)
  simp only [Real.rpow_zero, one_mul, Function.comp_def] at ht
  have hCt := ht.const_mul P.errorConstant
  rw [mul_zero] at hCt
  have hsmall := hCt.eventually_lt_const hε
  filter_upwards [hsmall, eventually_ge_atTop (2 : ℝ)] with x he hx
  have hbound := P.principal_theta_bound x hx
  have hm := mul_le_mul_of_nonneg_right he.le (by linarith : 0 ≤ x)
  nlinarith

 theorem mem_sizePrimeBand {Q p : ℕ} :
    p ∈ sizePrimeBand Q ↔ p.Prime ∧ Q < p ∧ p ≤ 2 * Q := by
  simp only [sizePrimeBand, Finset.mem_sdiff, Nat.mem_primesLE]
  constructor
  · rintro ⟨⟨hle, hp⟩, hnot⟩
    have hn : ¬ p ≤ Q := fun hh => hnot ⟨hh, hp⟩
    exact ⟨hp, by omega, hle⟩
  · rintro ⟨hp, hlo, hhi⟩
    exact ⟨⟨hhi, hp⟩, by omega⟩

 theorem sizePrimeBand_log_sum (Q : ℕ) :
    (∑ p ∈ sizePrimeBand Q, Real.log (p : ℝ)) =
      Chebyshev.theta (2 * Q : ℕ) - Chebyshev.theta Q := by
  rw [Chebyshev.theta_eq_sum_primesLE_log, Chebyshev.theta_eq_sum_primesLE_log]
  have hsub : Nat.primesLE Q ⊆ Nat.primesLE (2 * Q) := by
    intro p hp
    obtain ⟨hpQ, hpprime⟩ := Nat.mem_primesLE.mp hp
    exact Nat.mem_primesLE.mpr ⟨by omega, hpprime⟩
  simpa only [sizePrimeBand] using
    eq_sub_of_add_eq (Finset.sum_sdiff (f := fun p : ℕ => Real.log (p : ℝ)) hsub)

 theorem sizePrimeBand_eventual_bounds :
    ∀ᶠ Q : ℕ in atTop, 2 ≤ Q ∧
      (Q : ℝ) / (4 * Real.log (2 * Q)) ≤ (sizePrimeBand Q).card ∧
      (∑ p ∈ sizePrimeBand Q, Real.log (p : ℝ)) ≤ 3 * Q := by
  have ht := actual_theta_relative_small (by norm_num : (0 : ℝ) < 1 / 4)
  have htN := tendsto_natCast_atTop_atTop.eventually ht
  obtain ⟨N, hN⟩ := eventually_atTop.mp htN
  filter_upwards [eventually_ge_atTop (max N 2)] with Q hQ
  have hQ2 : 2 ≤ Q := (le_max_right _ _).trans hQ
  have hQN : N ≤ Q := (le_max_left _ _).trans hQ
  have hQp : (0 : ℝ) < Q := by exact_mod_cast (by omega : 0 < Q)
  have h1 := hN Q hQN
  have h2 := hN (2 * Q) (by omega)
  simp only [Nat.cast_mul, Nat.cast_ofNat] at h2
  have hmass : (Q : ℝ) / 4 ≤ ∑ p ∈ sizePrimeBand Q, Real.log (p : ℝ) := by
    rw [sizePrimeBand_log_sum]
    push_cast
    rw [abs_le] at h1 h2
    nlinarith
  have hupper : (∑ p ∈ sizePrimeBand Q, Real.log (p : ℝ)) ≤ 3 * Q := by
    rw [sizePrimeBand_log_sum]
    push_cast
    rw [abs_le] at h1 h2
    nlinarith
  have hcount : (∑ p ∈ sizePrimeBand Q, Real.log (p : ℝ)) ≤
      (sizePrimeBand Q).card * Real.log (2 * Q) := by
    calc
      _ ≤ ∑ _p ∈ sizePrimeBand Q, Real.log (2 * (Q : ℝ)) := by
        apply Finset.sum_le_sum
        intro p hp
        have hmem := mem_sizePrimeBand.mp hp
        exact Real.log_le_log (by exact_mod_cast hmem.1.pos) (by exact_mod_cast hmem.2.2)
      _ = _ := by simp
  have hl : 0 < Real.log (2 * (Q : ℝ)) := Real.log_pos (by exact_mod_cast (by omega : 1 < 2 * Q))
  refine ⟨hQ2, ?_, hupper⟩
  apply (div_le_iff₀ (by positivity : 0 < 4 * Real.log (2 * (Q : ℝ)))).mpr
  nlinarith

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

 theorem QuadraticSieveBound.mono_constant {M N : ℕ} {K L : ℝ}
    (h : QuadraticSieveBound M N K) (hKL : K ≤ L) : QuadraticSieveBound M N L := by
  intro b
  exact (h b).trans (mul_le_mul_of_nonneg_right hKL
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))

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

 theorem quadraticSquarefreePart_of_squarefree {m : ℕ} (hm : Squarefree m) :
    quadraticSquarePart m = 1 ∧ quadraticSquarefreePart m = m := by
  exact quadratic_squarefree_factor_unique
    (quadraticSquarePart_pos (Nat.pos_of_ne_zero hm.ne_zero)).ne'
    one_ne_zero (quadraticSquarefreePart_squarefree m) hm
    (by simpa using quadraticSquarePart_factor m)

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

theorem quadraticSieveWeight_eq_one {x : ℝ} (hx : x ∈ Set.Icc 1 2) :
    quadraticSieveWeight x = 1 := by
  have hh : quadraticSieveBump x = 1 := quadraticSieveBump.one_of_mem_closedBall (by
    change |x - 3 / 2| ≤ 1 / 2
    rw [abs_le]
    constructor <;> linarith [hx.1, hx.2])
  rw [quadraticSieveWeight_apply, hh, Complex.ofReal_one]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticSmoothedEnergy
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The literal smoothed odd moment and its large-kernel part -/

namespace Ostmann

open scoped Classical BigOperators

theorem quadratic_rough_dyadic_domination {M N K : ℕ} (hM : 0 < M) (hK : K < M)
    (b : ℕ → ℂ) :
    (∑ m ∈ (oddSquarefreeRange (2 * M)).filter (M ≤ ·),
      ‖quadraticTransposeSum N b m‖ ^ 2) ≤ quadraticRoughEnergy M N K b := by
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hw (m : ℕ) (hm : m ∈ (oddSquarefreeRange (2 * M)).filter (M ≤ ·)) :
      quadraticSieveBump ((m : ℝ) / M) = 1 := by
    obtain ⟨hm, hlo⟩ := Finset.mem_filter.mp hm
    have hhi := (Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1).2
    have hh := quadraticSieveWeight_eq_one (x := (m : ℝ) / M)
      (show (m : ℝ) / M ∈ Set.Icc 1 2 from ⟨
        (le_div_iff₀ hMR).mpr (by simpa only [one_mul] using (show (M : ℝ) ≤ m by exact_mod_cast hlo)),
        (div_le_iff₀ hMR).mpr (by exact_mod_cast hhi)⟩)
    rw [quadraticSieveWeight_apply] at hh
    exact_mod_cast hh
  calc
    _ = ∑ m ∈ (oddSquarefreeRange (2 * M)).filter (M ≤ ·),
        quadraticSieveBump ((m : ℝ) / M) * ‖quadraticTransposeSum N b m‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [hw m hm, one_mul]
    _ ≤ quadraticRoughEnergy M N K b := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro m hm
        obtain ⟨hm, hlo⟩ := Finset.mem_filter.mp hm
        obtain ⟨hi, ho, hsf⟩ := Finset.mem_filter.mp hm
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_filter.mpr ⟨?_, ho⟩, ?_⟩
        · apply Finset.mem_Icc.mpr
          obtain ⟨hl, hh⟩ := Finset.mem_Icc.mp hi
          omega
        · rw [(quadraticSquarefreePart_of_squarefree hsf).2]
          omega
      · intro m _ _
        exact mul_nonneg (quadraticSieveBump_nonneg _) (sq_nonneg _)

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

theorem quadraticDyadicDivisors_subset_double (N j : ℕ) :
    quadraticDyadicDivisors N j ⊆ oddSquarefreeRange (2 * 2 ^ j) := by
  intro n hn
  have hmem := (Finset.mem_filter.mp hn).1
  have hbound := (quadraticDyadicDivisors_bounds hn).2
  rw [pow_succ] at hbound
  obtain ⟨hi, ho, hs⟩ := Finset.mem_filter.mp hmem
  exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
    ⟨(Finset.mem_Icc.mp hi).1, by omega⟩, ho, hs⟩

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
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticSieveDuality
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
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
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticSieveAdditiveStart
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The initial quadratic-sieve bound from the proved additive large sieve -/

namespace Ostmann

open scoped BigOperators Classical

private theorem sum_interval_extension {R : Type*} [AddCommMonoid R]
    (N : ℕ) (S : Finset ℕ) (hS : ∀ n ∈ S, n ≤ N) (f : ℕ → R) :
    (∑ n : Fin (N + 1), if n.val ∈ S then f n.val else 0) = ∑ n ∈ S, f n := by
  rw [Fin.sum_univ_eq_sum_range (fun n : ℕ => if n ∈ S then f n else 0)]
  have hsub : S ⊆ Finset.range (N + 1) := by
    intro n hn
    exact Finset.mem_range.mpr (by have := hS n hn; omega)
  have hh := Finset.sum_subset hsub (f := fun n => if n ∈ S then f n else 0)
    (by intro n _ hn; simp [hn])
  simpa only [Finset.sum_ite_mem, Finset.inter_self] using hh.symm

private theorem quadraticArray_energy (N : ℕ) (b : ℕ → ℂ) :
    (∑ n, ‖quadraticArray N b n‖ ^ 2) = quadraticSieveEnergy N b := by
  have hh := sum_interval_extension N (oddSquarefreeRange N)
    (fun n hn => (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).2) (fun n => ‖b n‖ ^ 2)
  simpa only [quadraticArray, apply_ite, norm_zero, ite_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, quadraticSieveEnergy] using hh

private theorem quadraticArray_character_sum (N : ℕ) (b : ℕ → ℂ) (m : ℕ) [NeZero m] :
    (∑ n, quadraticArray N b n * (jacobiComplex m)⁻¹ (n.val : ZMod m)) =
      quadraticSieveSum N b m := by
  rw [(jacobiComplex_isQuadratic m).inv]
  have hh := sum_interval_extension N (oddSquarefreeRange N)
    (fun n hn => (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).2)
    (fun n => b n * (jacobiComplex m) (n : ZMod m))
  simpa only [quadraticArray, ite_mul, zero_mul, jacobiComplex_natCast,
    realJacobi, Complex.ofReal_intCast, quadraticSieveSum] using hh

 theorem quadraticSieveBound_additive (M N : ℕ) (hM : 1 ≤ M) :
    QuadraticSieveBound M N ((N : ℝ) + 1 + (M : ℝ) ^ 2) := by
  intro b
  let c := quadraticArray N b
  have hpoint (m : ℕ) (hm : m ∈ oddSquarefreeRange M) :
      ‖quadraticSieveSum N b m‖ ^ 2 ≤
        ∑ h ∈ reducedNumerators m, ‖additiveSieveSum c 0 m h‖ ^ 2 := by
    obtain ⟨hmrange, hmodd, hmsq⟩ := Finset.mem_filter.mp hm
    let : NeZero m := ⟨by have := (Finset.mem_Icc.mp hmrange).1; omega⟩
    have hi := primitive_character_sieve (jacobiComplex m)
      (jacobiComplex_squarefree_primitive m hmsq hmodd) c (fun n => (n.val : ZMod m))
    rw [quadraticArray_character_sum] at hi
    rw [sum_reducedNumerators_eq_units]
    simpa only [additiveSieveSum, sieveAdditivePhase_eq_stdAddChar, zero_add,
      Int.cast_natCast, ZMod.natCast_zmod_val, c] using hi
  have hsub : oddSquarefreeRange M ⊆ Finset.Icc 1 M := Finset.filter_subset _ _
  calc
    _ ≤ ∑ m ∈ oddSquarefreeRange M, ∑ h ∈ reducedNumerators m, ‖additiveSieveSum c 0 m h‖ ^ 2 :=
      Finset.sum_le_sum (fun m hm => hpoint m hm)
    _ ≤ ∑ m ∈ Finset.Icc 1 M, ∑ h ∈ reducedNumerators m, ‖additiveSieveSum c 0 m h‖ ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun _ _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    _ ≤ ((N + 1 : ℕ) + (M : ℝ) ^ 2) * ∑ n, ‖c n‖ ^ 2 :=
      publishedAdditiveLargeSieve (N + 1) M (by omega) hM 0 c
    _ = _ := by rw [show (∑ n, ‖c n‖ ^ 2) = quadraticSieveEnergy N b from quadraticArray_energy N b]; push_cast; ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticSieveInitial
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The initial exponent for the quadratic large sieve

The proved additive large sieve and quadratic reciprocity give the starting
exponent two in Heath-Brown's iteration, with an absolute constant.
-/

namespace Ostmann

 theorem quadraticSieveBound_initial (M N : ℕ) (hM : 1 ≤ M) (hN : 1 ≤ N) :
    QuadraticSieveBound M N (4 * ((M : ℝ) + (N : ℝ) ^ 2)) := by
  have h := (quadraticSieveBound_additive N M hN).transpose
    (by positivity : 0 ≤ (M : ℝ) + 1 + (N : ℝ) ^ 2)
  apply h.mono_constant
  have hM' : (1 : ℝ) ≤ M := by exact_mod_cast hM
  nlinarith [sq_nonneg (N : ℝ)]

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

theorem quadratic_sieve_growth_two : QuadraticSieveGrowth 2 := by
  intro ε hε
  refine ⟨4, by norm_num, ?_⟩
  intro M N hM hN
  apply (quadraticSieveBound_initial M N hM hN).mono_constant
  have hMR : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hprod := one_le_mul_of_one_le_of_one_le hMR hNR
  have hp : 1 ≤ ((M : ℝ) * N) ^ ε := Real.one_le_rpow hprod hε.le
  have hs : 0 ≤ (M : ℝ) + (N : ℝ) ^ 2 := by positivity
  rw [Real.rpow_two]
  nlinarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticBalancedKernel
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual rounded kernel cutoff in the long-row range -/

namespace Ostmann

theorem quadratic_balanced_kernel_bounds {η : ℝ} (hη : 0 ≤ η)
    {M N : ℕ} (hM : 0 < M) (hN : 0 < N)
    (hsep : 4 * (N : ℝ) * (((M : ℝ) * N) ^ η) ≤ M) :
    0 < quadraticBalancedKernel η M N ∧ quadraticBalancedKernel η M N < M ∧
      (quadraticBalancedKernel η M N : ℝ) ≤
        8 * (N : ℝ) ^ 2 * (((M : ℝ) * N) ^ η) / M + 1 ∧
      8 * (N : ℝ) ^ 2 * (((M : ℝ) * N) ^ η) ≤
        (M : ℝ) * quadraticBalancedKernel η M N := by
  let Y := ((M : ℝ) * N) ^ η
  let q := 8 * (N : ℝ) ^ 2 * Y / M
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hY : 1 ≤ Y := Real.one_le_rpow (one_le_mul_of_one_le_of_one_le
    (by exact_mod_cast hM) hNR) hη
  have hq : 0 < q := by dsimp [q]; positivity
  have hM₄ : (4 : ℝ) ≤ M := by
    have : 1 ≤ (N : ℝ) * Y := one_le_mul_of_one_le_of_one_le hNR hY
    change 4 * (N : ℝ) * Y ≤ M at hsep
    nlinarith
  have hqM : q ≤ (M : ℝ) / 2 := by
    apply (div_le_iff₀ hMR).mpr
    have hs := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 4 * N * Y) hsep 2
    have hYsq : Y ≤ Y ^ 2 := by nlinarith
    have hm := mul_le_mul_of_nonneg_left hYsq (sq_nonneg (N : ℝ))
    nlinarith
  have hlo : q ≤ (quadraticBalancedKernel η M N : ℝ) := Nat.le_ceil _
  have hhi : (quadraticBalancedKernel η M N : ℝ) < q + 1 := Nat.ceil_lt_add_one hq.le
  have hK : (0 : ℝ) < quadraticBalancedKernel η M N := hq.trans_le hlo
  have hKM : (quadraticBalancedKernel η M N : ℝ) < M := by linarith
  refine ⟨by exact_mod_cast hK, by exact_mod_cast hKM, hhi.le, ?_⟩
  have hh := (div_le_iff₀ hMR).mp hlo
  simpa only [mul_comm] using hh

theorem quadratic_balanced_kernel_cutoff {η : ℝ} (hη : 0 ≤ η)
    {M N : ℕ} (hM : 0 < M) (hN : 0 < N)
    (hsep : 4 * (N : ℝ) * (((M : ℝ) * N) ^ η) ≤ M) :
    2 * (2 * (N : ℝ)) ^ 2 * (((M : ℝ) * N) ^ η) ≤
      (M : ℝ) * ((quadraticBalancedKernel η M N : ℝ) + 1) := by
  have hh := (quadratic_balanced_kernel_bounds hη hM hN hsep).2.2.2
  nlinarith [Nat.cast_nonneg (α := ℝ) M]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticBalancedScale
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The balanced kernel gives Heath-Brown's improved long-row scale -/

namespace Ostmann

theorem quadratic_balanced_power_identity {M N Y ξ : ℝ}
    (hM : 0 < M) (hN : 0 < N) (hY : 0 ≤ Y) :
    Real.sqrt M * (16 * N ^ 2 * Y / M) ^ (ξ - 1 / 2) =
      16 ^ (ξ - 1 / 2) * Y ^ (ξ - 1 / 2) * (M ^ (1 - ξ) * N ^ (2 * ξ - 1)) := by
  have hm : M ^ (1 - ξ) = M ^ (1 / 2 : ℝ) / M ^ (ξ - 1 / 2) := by
    rw [← Real.rpow_sub hM]
    congr 1
    ring
  have hn : (N ^ 2) ^ (ξ - 1 / 2) = N ^ (2 * ξ - 1) := by
    rw [← Real.rpow_natCast N 2, ← Real.rpow_mul hN.le]
    congr 1
    ring
  rw [Real.div_rpow (by positivity) hM.le, Real.mul_rpow (by positivity) hY,
    Real.mul_rpow (by norm_num) (by positivity), hn, Real.sqrt_eq_rpow, hm]
  ring

theorem quadratic_balanced_scale {ξ η : ℝ} (hξ : 1 / 2 ≤ ξ) (hξ' : ξ ≤ 2)
    (hη : 0 ≤ η) {M N : ℕ} (hM : 0 < M) (hN : 0 < N)
    (hsep : 4 * (N : ℝ) * (((M : ℝ) * N) ^ η) ≤ M) :
    quadraticDescentScale ξ M N (quadraticBalancedKernel η M N) ≤
      300 * (((M : ℝ) * N) ^ η) ^ 2 *
        ((M : ℝ) + (M : ℝ) ^ (1 - ξ) * (N : ℝ) ^ (2 * ξ - 1)) := by
  let K := quadraticBalancedKernel η M N
  let Y := ((M : ℝ) * N) ^ η
  let S := (M : ℝ) ^ (1 - ξ) * (N : ℝ) ^ (2 * ξ - 1)
  have hM₁ : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hN₁ : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hY : 1 ≤ Y := Real.one_le_rpow (one_le_mul_of_one_le_of_one_le hM₁ hN₁) hη
  obtain ⟨hK, _, hKu, hKl⟩ := quadratic_balanced_kernel_bounds hη hM hN hsep
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  have hNM : (N : ℝ) ≤ M := by
    have hh := mul_le_mul_of_nonneg_left hY hNR.le
    change 4 * (N : ℝ) * Y ≤ M at hsep
    nlinarith
  have hSm : 0 ≤ S := by dsimp [S]; positivity
  have hYm : 1 ≤ Y ^ 2 := one_le_pow₀ hY
  have hsqrtM : Real.sqrt M ≤ M := Real.sqrt_le_self_iff.mpr (Or.inr hM₁)
  have htail : Real.sqrt M * N / Real.sqrt K ≤ M := by
    apply (div_le_iff₀ (Real.sqrt_pos.mpr hKR)).mpr
    have hsq : (Real.sqrt M * (N : ℝ)) ^ 2 ≤ ((M : ℝ) * Real.sqrt K) ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hMR.le, Real.sq_sqrt hKR.le]
      have hyN := mul_le_mul_of_nonneg_left hY (sq_nonneg (N : ℝ))
      change 8 * (N : ℝ) ^ 2 * Y ≤ (M : ℝ) * K at hKl
      nlinarith
    exact (sq_le_sq₀ (by positivity) (by positivity)).mp hsq
  have hkernel : Real.sqrt M * (K : ℝ) ^ (ξ - 1 / 2) ≤
      4 * M + 256 * Y ^ 2 * S := by
    by_cases hq : 8 * (N : ℝ) ^ 2 * Y / M ≤ 1
    · have hK₂ : (K : ℝ) ≤ 2 := by
        change (K : ℝ) ≤ 8 * (N : ℝ) ^ 2 * Y / M + 1 at hKu
        linarith
      have hp : (K : ℝ) ^ (ξ - 1 / 2) ≤ 4 := by
        calc
          _ ≤ (2 : ℝ) ^ (ξ - 1 / 2) := Real.rpow_le_rpow hKR.le hK₂ (by linarith)
          _ ≤ (2 : ℝ) ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
          _ = 4 := by norm_num
      have hh := mul_le_mul_of_nonneg_left hp (Real.sqrt_nonneg (M : ℝ))
      nlinarith
    · have hKq : (K : ℝ) ≤ 16 * (N : ℝ) ^ 2 * Y / M := by
        change (K : ℝ) ≤ 8 * (N : ℝ) ^ 2 * Y / M + 1 at hKu
        rw [show 16 * (N : ℝ) ^ 2 * Y / M = 2 * (8 * (N : ℝ) ^ 2 * Y / M) by ring]
        linarith
      have hp := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow hKR.le hKq (by linarith : 0 ≤ ξ - 1 / 2))
        (Real.sqrt_nonneg (M : ℝ))
      rw [quadratic_balanced_power_identity hMR hNR (by positivity)] at hp
      have hc : (16 : ℝ) ^ (ξ - 1 / 2) ≤ 256 := by
        calc
          _ ≤ (16 : ℝ) ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
          _ = 256 := by norm_num
      have hy : Y ^ (ξ - 1 / 2) ≤ Y ^ (2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hY (by linarith)
      rw [Real.rpow_two] at hy
      have hh : (16 : ℝ) ^ (ξ - 1 / 2) * Y ^ (ξ - 1 / 2) * S ≤ 256 * Y ^ 2 * S := by
        gcongr
      change Real.sqrt M * (K : ℝ) ^ (ξ - 1 / 2) ≤ _ at hp
      exact hp.trans (hh.trans (le_add_of_nonneg_left (by positivity)))
  change (M : ℝ) + N + Real.sqrt M * (K : ℝ) ^ (ξ - 1 / 2) +
    Real.sqrt M * N / Real.sqrt K ≤ 300 * Y ^ 2 * ((M : ℝ) + S)
  have hmY := mul_le_mul_of_nonneg_right hYm hMR.le
  have hsY : 0 ≤ Y ^ 2 * S := mul_nonneg (sq_nonneg Y) hSm
  nlinarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticLongRows
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The improved bound in the long-row range -/

namespace Ostmann

open scoped Classical BigOperators

theorem quadratic_long_rows {ξ : ℝ} (h : QuadraticSieveGrowth ξ)
    (hξ : 1 / 2 ≤ ξ) (hξ' : ξ ≤ 2) (ε : ℝ) (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ η ≤ ε / 4 ∧ ∃ C : ℝ, 0 < C ∧ ∀ M N : ℕ,
      0 < M → 0 < N → 4 * (N : ℝ) * (((M : ℝ) * N) ^ η) ≤ M →
      ∀ v : ℕ → ℂ,
        (∑ m ∈ (oddSquarefreeRange (2 * M)).filter (M ≤ ·),
          ‖quadraticTransposeSum N v m‖ ^ 2) ≤
          C * ((M : ℝ) * N) ^ ε *
            ((M : ℝ) + (M : ℝ) ^ (1 - ξ) * (N : ℝ) ^ (2 * ξ - 1)) *
              quadraticSieveEnergy N v := by
  obtain ⟨η, hη, hηε, C, hC, hc⟩ := quadratic_rough_power_growth h hξ hξ'
    (ε / 4) (by positivity)
  refine ⟨η, hη, hηε, 300 * C, by positivity, ?_⟩
  intro M N hM hN hsep v
  let K := quadraticBalancedKernel η M N
  obtain ⟨hK, hKM, _, _⟩ := quadratic_balanced_kernel_bounds hη.le hM hN hsep
  have hcut := quadratic_balanced_kernel_cutoff hη.le hM hN hsep
  have hb := hc M N K hM hN hK hKM.le hcut v
  have hs := quadratic_balanced_scale hξ hξ' hη.le hM hN hsep
  have hX : 1 ≤ (M : ℝ) * N := one_le_mul_of_one_le_of_one_le
    (by exact_mod_cast hM) (by exact_mod_cast hN)
  have hXp : 0 < (M : ℝ) * N := lt_of_lt_of_le zero_lt_one hX
  have hpow : (((M : ℝ) * N) ^ (ε / 4)) * ((((M : ℝ) * N) ^ η) ^ 2) ≤
      ((M : ℝ) * N) ^ ε := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hXp.le, ← Real.rpow_add hXp]
    exact Real.rpow_le_rpow_of_exponent_le hX (by linarith)
  have hE : 0 ≤ quadraticSieveEnergy N v := Finset.sum_nonneg fun _ _ => sq_nonneg _
  apply (quadratic_rough_dyadic_domination hM hKM v).trans (hb.trans ?_)
  calc
    _ ≤ C * ((M : ℝ) * N) ^ (ε / 4) *
        (300 * ((((M : ℝ) * N) ^ η) ^ 2) *
          ((M : ℝ) + (M : ℝ) ^ (1 - ξ) * (N : ℝ) ^ (2 * ξ - 1))) *
            quadraticSieveEnergy N v := by gcongr
    _ = (300 * C) * (((M : ℝ) * N) ^ (ε / 4) * ((((M : ℝ) * N) ^ η) ^ 2)) *
        ((M : ℝ) + (M : ℝ) ^ (1 - ξ) * (N : ℝ) ^ (2 * ξ - 1)) *
          quadraticSieveEnergy N v := by ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ hE
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left hpow (by positivity)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticShortRowsScale
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The initial exponent bound in the complementary row range -/

namespace Ostmann

theorem quadratic_short_rows_scale {ξ M N Y : ℝ} (hξ : 1 ≤ ξ) (hξ' : ξ ≤ 2)
    (hM : 0 < M) (hN : 0 < N) (hY : 1 ≤ Y) (hMN : M ≤ 4 * N * Y) :
    N ^ ξ ≤ 4 * Y * (M ^ (1 - ξ) * N ^ (2 * ξ - 1)) := by
  have hm : M ^ (1 - ξ) * M ^ (ξ - 1) = 1 := by
    rw [← Real.rpow_add hM]
    convert Real.rpow_zero M using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    ring
  have hn : N ^ (2 * ξ - 1) / N ^ (ξ - 1) = N ^ ξ := by
    rw [← Real.rpow_sub hN]
    congr 1
    ring
  have he : M ^ (1 - ξ) * N ^ (2 * ξ - 1) * (M / N) ^ (ξ - 1) = N ^ ξ := by
    rw [Real.div_rpow hM.le hN.le]
    calc
      _ = (M ^ (1 - ξ) * M ^ (ξ - 1)) * (N ^ (2 * ξ - 1) / N ^ (ξ - 1)) := by ring
      _ = _ := by rw [hm, hn, one_mul]
  have hratio : M / N ≤ 4 * Y := (div_le_iff₀ hN).mpr (by nlinarith)
  have hp : (M / N) ^ (ξ - 1) ≤ 4 * Y := by
    calc
      _ ≤ (4 * Y) ^ (ξ - 1) := Real.rpow_le_rpow (by positivity) hratio (by linarith)
      _ ≤ (4 * Y) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      _ = _ := Real.rpow_one _
  rw [← he]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ M ^ (1 - ξ) * N ^ (2 * ξ - 1))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticDyadicGrowth
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The improved dyadic-row bound at the current induction exponent -/

namespace Ostmann

open scoped Classical BigOperators

theorem quadratic_dyadic_growth {ξ : ℝ} (h : QuadraticSieveGrowth ξ)
    (hξ : 1 ≤ ξ) (hξ' : ξ ≤ 2) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ M N : ℕ, 0 < M → 0 < N → ∀ v : ℕ → ℂ,
      (∑ m ∈ (oddSquarefreeRange (2 * M)).filter (M ≤ ·),
        ‖quadraticTransposeSum N v m‖ ^ 2) ≤
        C * ((M : ℝ) * N) ^ ε *
          ((M : ℝ) + (M : ℝ) ^ (1 - ξ) * (N : ℝ) ^ (2 * ξ - 1)) *
            quadraticSieveEnergy N v := by
  obtain ⟨η, hη, hηε, A, hA, ha⟩ := quadratic_long_rows h (by linarith) hξ' ε hε
  obtain ⟨B, hB, hb⟩ := h (ε / 4) (by positivity)
  let D := 8 * B * 2 ^ (ε / 4)
  refine ⟨A + D, by dsimp [D]; positivity, ?_⟩
  intro M N hM hN v
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hX : 1 ≤ (M : ℝ) * N := one_le_mul_of_one_le_of_one_le
    (by exact_mod_cast hM) (by exact_mod_cast hN)
  have hXp : 0 < (M : ℝ) * N := lt_of_lt_of_le zero_lt_one hX
  have hE : 0 ≤ quadraticSieveEnergy N v := Finset.sum_nonneg fun _ _ => sq_nonneg _
  by_cases hsep : 4 * (N : ℝ) * (((M : ℝ) * N) ^ η) ≤ M
  · apply (ha M N hM hN hsep v).trans
    have hD : 0 < D := by dsimp [D]; positivity
    gcongr
    linarith
  · have hY : 1 ≤ ((M : ℝ) * N) ^ η := Real.one_le_rpow hX hη.le
    have hs := quadratic_short_rows_scale hξ hξ' hMR hNR hY (le_of_lt (lt_of_not_ge hsep))
    have ht := quadraticTranspose_of_bound (hb (2 * M) N (by omega) hN) v
    have hsmall : 2 * (M : ℝ) + (N : ℝ) ^ ξ ≤
        4 * (((M : ℝ) * N) ^ η) *
          ((M : ℝ) + (M : ℝ) ^ (1 - ξ) * (N : ℝ) ^ (2 * ξ - 1)) := by
      have hm := mul_le_mul_of_nonneg_right hY hMR.le
      nlinarith only [hs, hm, hMR]
    have hpow : ((M : ℝ) * N) ^ (ε / 4) * ((M : ℝ) * N) ^ η ≤
        ((M : ℝ) * N) ^ ε := by
      rw [← Real.rpow_add hXp]
      exact Real.rpow_le_rpow_of_exponent_le hX (by linarith)
    have hprod : (((2 * M : ℕ) : ℝ) * N) ^ (ε / 4) =
        2 ^ (ε / 4) * ((M : ℝ) * N) ^ (ε / 4) := by
      simp only [Nat.cast_mul, Nat.cast_ofNat]
      rw [mul_assoc, Real.mul_rpow (by norm_num) hXp.le]
    apply (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun _ _ _ => sq_nonneg _)).trans (ht.trans ?_)
    simp only [Nat.cast_mul, Nat.cast_ofNat] at ht ⊢
    rw [show (2 * (M : ℝ) * N) ^ (ε / 4) =
      2 ^ (ε / 4) * ((M : ℝ) * N) ^ (ε / 4) by
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using hprod]
    calc
      _ ≤ 2 * (B * (2 ^ (ε / 4) * ((M : ℝ) * N) ^ (ε / 4)) *
          (4 * (((M : ℝ) * N) ^ η) *
            ((M : ℝ) + (M : ℝ) ^ (1 - ξ) * (N : ℝ) ^ (2 * ξ - 1)))) *
              quadraticSieveEnergy N v := by gcongr
      _ = D * (((M : ℝ) * N) ^ (ε / 4) * ((M : ℝ) * N) ^ η) *
          ((M : ℝ) + (M : ℝ) ^ (1 - ξ) * (N : ℝ) ^ (2 * ξ - 1)) *
            quadraticSieveEnergy N v := by dsimp [D]; ring
      _ ≤ (A + D) * ((M : ℝ) * N) ^ ε *
          ((M : ℝ) + (M : ℝ) ^ (1 - ξ) * (N : ℝ) ^ (2 * ξ - 1)) *
            quadraticSieveEnergy N v := by
        apply mul_le_mul_of_nonneg_right _ hE
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul (by linarith) hpow (by positivity) (by dsimp [D]; positivity)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticRowNorm
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The least constant for an actual finite set of quadratic rows -/

namespace Ostmann

open scoped Classical BigOperators

theorem quadraticRowEnergy_trivial (S : Finset ℕ) (N : ℕ) (v : ℕ → ℂ) :
    quadraticRowEnergy S N v ≤ (S.card : ℝ) * N * quadraticSieveEnergy N v := by
  calc
    _ ≤ ∑ _m ∈ S, (N : ℝ) * quadraticSieveEnergy N v :=
      Finset.sum_le_sum (fun _ _ => quadraticTransposeSum_trivial N v _)
    _ = _ := by simp [mul_assoc]

theorem quadraticRow_ratios_bounded (S : Finset ℕ) (N : ℕ) :
    BddAbove (Set.range fun v : ℕ → ℂ =>
      quadraticRowEnergy S N v / quadraticSieveEnergy N v) := by
  refine ⟨(S.card : ℝ) * N, ?_⟩
  rintro y ⟨v, rfl⟩
  have hE : 0 ≤ quadraticSieveEnergy N v := Finset.sum_nonneg fun _ _ => sq_nonneg _
  by_cases hzero : quadraticSieveEnergy N v = 0
  · simp only [hzero, div_zero]
    positivity
  · exact (div_le_iff₀ (lt_of_le_of_ne hE (Ne.symm hzero))).mpr (quadraticRowEnergy_trivial S N v)

theorem quadraticRowNorm_nonneg (S : Finset ℕ) (N : ℕ) : 0 ≤ quadraticRowNorm S N := by
  have hh := le_csSup (quadraticRow_ratios_bounded S N)
    (Set.mem_range_self (f := fun v : ℕ → ℂ =>
      quadraticRowEnergy S N v / quadraticSieveEnergy N v) (fun _ => 0))
  simpa only [quadraticRowNorm, quadraticRowEnergy, quadraticTransposeSum, zero_mul, Finset.sum_const_zero,
    norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div] using hh

theorem quadraticRowNorm_bound (S : Finset ℕ) (N : ℕ) :
    QuadraticRowBound S N (quadraticRowNorm S N) := by
  intro v
  have hE : 0 ≤ quadraticSieveEnergy N v := Finset.sum_nonneg fun _ _ => sq_nonneg _
  by_cases hzero : quadraticSieveEnergy N v = 0
  · have ht := quadraticRowEnergy_trivial S N v
    simpa only [hzero, mul_zero] using ht
  · exact (div_le_iff₀ (lt_of_le_of_ne hE (Ne.symm hzero))).mp
      (le_csSup (quadraticRow_ratios_bounded S N) (Set.mem_range_self v))

theorem quadraticRowNorm_le {S : Finset ℕ} {N : ℕ} {T : ℝ}
    (hT : 0 ≤ T) (h : QuadraticRowBound S N T) : quadraticRowNorm S N ≤ T := by
  apply csSup_le (Set.range_nonempty _)
  rintro y ⟨v, rfl⟩
  have hE : 0 ≤ quadraticSieveEnergy N v := Finset.sum_nonneg fun _ _ => sq_nonneg _
  by_cases hzero : quadraticSieveEnergy N v = 0
  · simpa only [hzero, div_zero] using hT
  · exact (div_le_iff₀ (lt_of_le_of_ne hE (Ne.symm hzero))).mpr (h v)

theorem QuadraticRowBound.mono_constant {S : Finset ℕ} {N : ℕ} {T U : ℝ}
    (h : QuadraticRowBound S N T) (hTU : T ≤ U) : QuadraticRowBound S N U := by
  intro v
  exact (h v).trans (mul_le_mul_of_nonneg_right hTU (Finset.sum_nonneg fun _ _ => sq_nonneg _))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticPrimeIncidence
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Incidence losses in prime dilation are only logarithmic -/

namespace Ostmann

open scoped Classical BigOperators

theorem quadratic_prime_incidence {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    {n B : ℕ} (hn : 0 < n) (hnB : n ≤ B) :
    (P.filter (fun p => p ∣ n)).card ≤ Nat.log 2 B := by
  let Q := P.filter (fun p => p ∣ n)
  have hsub : Q ⊆ n.primeFactors := by
    intro p hp
    exact Nat.mem_primeFactors.mpr ⟨hP p (Finset.mem_filter.mp hp).1,
      (Finset.mem_filter.mp hp).2, Nat.ne_of_gt hn⟩
  have hd : (∏ p ∈ Q, p) ∣ n :=
    (Finset.prod_dvd_prod_of_subset Q n.primeFactors id hsub).trans (Nat.prod_primeFactors_dvd n)
  have hpow : 2 ^ Q.card ≤ n := by
    calc
      _ = ∏ _p ∈ Q, 2 := by simp
      _ ≤ ∏ p ∈ Q, p := Finset.prod_le_prod' (fun p hp => (hP p (Finset.mem_filter.mp hp).1).two_le)
      _ ≤ n := Nat.le_of_dvd hn hd
  exact Nat.le_log_of_pow_le (by norm_num) (hpow.trans hnB)

theorem quadratic_prime_restricted_energy {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    (N : ℕ) (v : ℕ → ℂ) :
    (∑ p ∈ P, quadraticSieveEnergy N (fun n => if p ∣ n then v n else 0)) ≤
      (Nat.log 2 N : ℝ) * quadraticSieveEnergy N v := by
  unfold quadraticSieveEnergy
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  have hi := Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1
  have hcount := quadratic_prime_incidence hP hi.1 hi.2
  simp only [apply_ite, norm_zero, ite_pow, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcount) (sq_nonneg _)

theorem quadratic_prime_bad_rows {P S : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    {B : ℕ} (hS : ∀ m ∈ S, 0 < m ∧ m ≤ B) (N : ℕ) (v : ℕ → ℂ) :
    (∑ p ∈ P, ∑ m ∈ S.filter (fun m => p ∣ m), ‖quadraticTransposeSum N v m‖ ^ 2) ≤
      (Nat.log 2 B : ℝ) * quadraticRowEnergy S N v := by
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  unfold quadraticRowEnergy
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro m hm
  have hcount := quadratic_prime_incidence hP (hS m hm).1 (hS m hm).2
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcount) (sq_nonneg _)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticPrimeTwist
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Prime dilation on the literal quadratic coefficient array -/

namespace Ostmann

open scoped Classical BigOperators

theorem quadraticPrimeTwist_energy (p N : ℕ) (v : ℕ → ℂ) :
    quadraticSieveEnergy N (quadraticPrimeTwist p v) ≤ quadraticSieveEnergy N v := by
  apply Finset.sum_le_sum
  intro n _
  rcases jacobiSym.trichotomy (p : ℤ) n with h | h | h <;> simp [quadraticPrimeTwist, h]

theorem quadratic_prime_twist_identity {p : ℕ} (hp : p.Prime) (N : ℕ)
    (v : ℕ → ℂ) (m : ℤ) :
    quadraticTransposeSum N v m =
      quadraticTransposeSum N (quadraticPrimeTwist p v) ((p : ℤ) * m) +
        quadraticTransposeSum N (fun n => if p ∣ n then v n else 0) m := by
  unfold quadraticTransposeSum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  have hn₀ := (Finset.mem_filter.mp hn).2.2.ne_zero
  unfold quadraticPrimeTwist
  rw [jacobiSym.mul_left, Int.cast_mul]
  by_cases hd : p ∣ n
  · have hc : ¬ p.Coprime n := by simpa only [hp.coprime_iff_not_dvd, not_not] using hd
    have hj : jacobiSym (p : ℤ) n = 0 := (jacobiSym.eq_zero_iff).mpr ⟨hn₀, by exact hc⟩
    simp [hd, hj]
  · have hc : p.Coprime n := hp.coprime_iff_not_dvd.mpr hd
    have hj : (jacobiSym (p : ℤ) n : ℂ) ^ 2 = 1 := by exact_mod_cast jacobiSym.sq_one (by exact hc)
    simp only [ite_eq_right hd, zero_mul, add_zero]
    calc
      _ = v n * (jacobiSym m n : ℂ) * (1 : ℂ) := by ring
      _ = v n * (jacobiSym m n : ℂ) * (jacobiSym (p : ℤ) n : ℂ) ^ 2 := by rw [hj]
      _ = _ := by ring

theorem quadratic_prime_twist_point_bound {p : ℕ} (hp : p.Prime) (N : ℕ)
    (v : ℕ → ℂ) (m : ℕ) :
    ‖quadraticTransposeSum N v m‖ ^ 2 ≤
      2 * ‖quadraticTransposeSum N (quadraticPrimeTwist p v) (p * m : ℕ)‖ ^ 2 +
        2 * ‖quadraticTransposeSum N (fun n => if p ∣ n then v n else 0) m‖ ^ 2 := by
  rw [quadratic_prime_twist_identity hp N v m]
  have hh := norm_add_le
    (quadraticTransposeSum N (quadraticPrimeTwist p v) ((p : ℤ) * m))
    (quadraticTransposeSum N (fun n => if p ∣ n then v n else 0) m)
  have hs := pow_le_pow_left₀ (norm_nonneg _) hh 2
  push_cast
  nlinarith [sq_nonneg (‖quadraticTransposeSum N (quadraticPrimeTwist p v) ((p : ℤ) * m)‖ -
    ‖quadraticTransposeSum N (fun n => if p ∣ n then v n else 0) m‖)]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticPrimeDilation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A finite prime-dilation comparison between actual row matrices -/

namespace Ostmann

open scoped Classical BigOperators

theorem quadratic_prime_dilation {P S T : Finset ℕ} {N R : ℕ} {U : ℝ}
    (hP : ∀ p ∈ P, p.Prime) (hP₀ : 0 < P.card)
    (hS : ∀ m ∈ S, 0 < m ∧ m ≤ R)
    (hmap : ∀ p ∈ P, ∀ m ∈ S, ¬p ∣ m → p * m ∈ T)
    (hcount : 2 * (2 * Nat.log 2 N + Nat.log 2 R) ≤ P.card)
    (hU : 0 ≤ U) (hT : QuadraticRowBound T N U) :
    QuadraticRowBound S N (4 * U) := by
  let A := quadraticRowNorm S N
  let L : ℝ := 2 * (Nat.log 2 N : ℝ) + Nat.log 2 R
  let Q : ℝ := P.card
  have hA : 0 ≤ A := quadraticRowNorm_nonneg S N
  have hAb : QuadraticRowBound S N A := quadraticRowNorm_bound S N
  have hQ : 0 < Q := by dsimp [Q]; exact_mod_cast hP₀
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hLQ : 2 * L ≤ Q := by dsimp [L, Q]; exact_mod_cast hcount
  have hgood (p : ℕ) (hp : p ∈ P) (v : ℕ → ℂ) :
      (∑ m ∈ S.filter (fun m => ¬p ∣ m), ‖quadraticTransposeSum N v m‖ ^ 2) ≤
        2 * U * quadraticSieveEnergy N v +
          2 * A * quadraticSieveEnergy N (fun n => if p ∣ n then v n else 0) := by
    have hfirst : (∑ m ∈ S.filter (fun m => ¬p ∣ m),
        ‖quadraticTransposeSum N (quadraticPrimeTwist p v) (p * m : ℕ)‖ ^ 2) ≤
        quadraticRowEnergy T N (quadraticPrimeTwist p v) := by
      apply OAI.sum_le_sum_of_injOn (fun m => p * m)
      · intro a _ b _ hab
        exact Nat.eq_of_mul_eq_mul_left (hP p hp).pos hab
      · intro x hx
        obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hx
        exact hmap p hp m (Finset.mem_filter.mp hm).1 (Finset.mem_filter.mp hm).2
      · intro m _
        rfl
      · intro m _ _
        exact sq_nonneg _
    have hsecond : (∑ m ∈ S.filter (fun m => ¬p ∣ m),
        ‖quadraticTransposeSum N (fun n => if p ∣ n then v n else 0) m‖ ^ 2) ≤
        quadraticRowEnergy S N (fun n => if p ∣ n then v n else 0) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => sq_nonneg _)
    have ht := (hT (quadraticPrimeTwist p v)).trans
      (mul_le_mul_of_nonneg_left (quadraticPrimeTwist_energy p N v) hU)
    calc
      _ ≤ ∑ m ∈ S.filter (fun m => ¬p ∣ m),
          (2 * ‖quadraticTransposeSum N (quadraticPrimeTwist p v) (p * m : ℕ)‖ ^ 2 +
            2 * ‖quadraticTransposeSum N (fun n => if p ∣ n then v n else 0) m‖ ^ 2) :=
        Finset.sum_le_sum (fun m _ => quadratic_prime_twist_point_bound (hP p hp) N v m)
      _ = 2 * (∑ m ∈ S.filter (fun m => ¬p ∣ m),
          ‖quadraticTransposeSum N (quadraticPrimeTwist p v) (p * m : ℕ)‖ ^ 2) +
          2 * (∑ m ∈ S.filter (fun m => ¬p ∣ m),
            ‖quadraticTransposeSum N (fun n => if p ∣ n then v n else 0) m‖ ^ 2) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      _ ≤ _ := by
        have h₁ := hfirst.trans ht
        have h₂ := hsecond.trans (hAb (fun n => if p ∣ n then v n else 0))
        linarith
  have hall (v : ℕ → ℂ) : Q * quadraticRowEnergy S N v ≤
      (2 * Q * U + L * A) * quadraticSieveEnergy N v := by
    have hsplit : Q * quadraticRowEnergy S N v =
        (∑ p ∈ P, ∑ m ∈ S.filter (fun m => ¬p ∣ m), ‖quadraticTransposeSum N v m‖ ^ 2) +
        ∑ p ∈ P, ∑ m ∈ S.filter (fun m => p ∣ m), ‖quadraticTransposeSum N v m‖ ^ 2 := by
      rw [← Finset.sum_add_distrib]
      have hs (p : ℕ) : (∑ m ∈ S.filter (fun m => ¬p ∣ m), ‖quadraticTransposeSum N v m‖ ^ 2) +
          (∑ m ∈ S.filter (fun m => p ∣ m), ‖quadraticTransposeSum N v m‖ ^ 2) =
          quadraticRowEnergy S N v := by
        simpa only [not_not, quadraticRowEnergy] using Finset.sum_filter_add_sum_filter_not S
          (fun m => ¬p ∣ m) (fun m => ‖quadraticTransposeSum N v m‖ ^ 2)
      simp_rw [hs]
      simp only [Q, Finset.sum_const, nsmul_eq_mul]
    have hg := Finset.sum_le_sum (fun p hp => hgood p hp v)
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul] at hg
    rw [← Finset.mul_sum] at hg
    have he := mul_le_mul_of_nonneg_left (quadratic_prime_restricted_energy hP N v)
      (show 0 ≤ 2 * A by positivity)
    have hb := (quadratic_prime_bad_rows hP hS N v).trans
      (mul_le_mul_of_nonneg_left (hAb v) (Nat.cast_nonneg _))
    rw [hsplit]
    dsimp [Q, L]
    nlinarith only [hg, he, hb]
  let W := (2 * Q * U + L * A) / Q
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hWb : QuadraticRowBound S N W := by
    intro v
    apply (mul_le_mul_iff_left₀ hQ).mp
    have hh := hall v
    convert hh using 1 <;> first | (with_reducible_and_instances rfl) | ((try dsimp only [W]) <;> field_simp)
  have hupper := (le_div_iff₀ hQ).mp (quadraticRowNorm_le hW hWb)
  have hhalf := mul_le_mul_of_nonneg_right hLQ hA
  have hprod : Q * A ≤ Q * (4 * U) := by nlinarith only [hupper, hhalf]
  have hfinal : A ≤ 4 * U := by nlinarith only [hprod, hQ]
  exact hAb.mono_constant hfinal

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticWideRows
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Adjacent dyadic intervals and the actual prime-dilation image -/

namespace Ostmann

open scoped Classical BigOperators

theorem quadraticWideRows_energy (M N : ℕ) (v : ℕ → ℂ) :
    quadraticRowEnergy (quadraticWideRows M) N v ≤
      (∑ m ∈ (oddSquarefreeRange (2 * M)).filter (M ≤ ·), ‖quadraticTransposeSum N v m‖ ^ 2) +
      ∑ m ∈ (oddSquarefreeRange (2 * (2 * M))).filter (2 * M ≤ ·), ‖quadraticTransposeSum N v m‖ ^ 2 := by
  have hs := Finset.sum_filter_add_sum_filter_not (quadraticWideRows M) (fun m => m ≤ 2 * M)
    (fun m => ‖quadraticTransposeSum N v m‖ ^ 2)
  rw [quadraticRowEnergy, ← hs]
  apply add_le_add
  · apply Finset.sum_le_sum_of_subset_of_nonneg _ (fun _ _ _ => sq_nonneg _)
    intro m hm
    obtain ⟨hm, hhi⟩ := Finset.mem_filter.mp hm
    obtain ⟨hm, hlo⟩ := Finset.mem_filter.mp hm
    obtain ⟨hi, ho, hsf⟩ := Finset.mem_filter.mp hm
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hi).1, hhi⟩, ho, hsf⟩, hlo⟩
  · apply Finset.sum_le_sum_of_subset_of_nonneg _ (fun _ _ _ => sq_nonneg _)
    intro m hm
    obtain ⟨hm, hhi⟩ := Finset.mem_filter.mp hm
    obtain ⟨hm, _⟩ := Finset.mem_filter.mp hm
    apply Finset.mem_filter.mpr
    refine ⟨?_, by omega⟩
    simpa only [show 2 * (2 * M) = 4 * M by omega] using hm

theorem quadratic_wide_rows_growth {ξ : ℝ} (h : QuadraticSieveGrowth ξ)
    (hξ : 1 ≤ ξ) (hξ' : ξ ≤ 2) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ M N : ℕ, 0 < M → 0 < N →
      QuadraticRowBound (quadraticWideRows M) N
        (C * ((M : ℝ) * N) ^ ε *
          ((M : ℝ) + (M : ℝ) ^ (1 - ξ) * (N : ℝ) ^ (2 * ξ - 1))) := by
  obtain ⟨C, hC, hc⟩ := quadratic_dyadic_growth h hξ hξ' ε hε
  refine ⟨C * (1 + 2 * 2 ^ ε), by positivity, ?_⟩
  intro M N hM hN v
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hNM : (0 : ℝ) < N := by exact_mod_cast hN
  have hE : 0 ≤ quadraticSieveEnergy N v := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hS : 0 ≤ (M : ℝ) ^ (1 - ξ) * (N : ℝ) ^ (2 * ξ - 1) := by positivity
  have hscale : ((2 * M : ℕ) : ℝ) + ((2 * M : ℕ) : ℝ) ^ (1 - ξ) * (N : ℝ) ^ (2 * ξ - 1) ≤
      2 * ((M : ℝ) + (M : ℝ) ^ (1 - ξ) * (N : ℝ) ^ (2 * ξ - 1)) := by
    have hp : ((2 * M : ℕ) : ℝ) ^ (1 - ξ) ≤ (M : ℝ) ^ (1 - ξ) := by
      simp only [Nat.cast_mul, Nat.cast_ofNat]
      rw [Real.mul_rpow (by norm_num) hMR.le]
      have hh : (2 : ℝ) ^ (1 - ξ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hh (Real.rpow_nonneg hMR.le _)
    have hh := mul_le_mul_of_nonneg_right hp (Real.rpow_nonneg hNM.le (2 * ξ - 1))
    simp only [Nat.cast_mul, Nat.cast_ofNat] at hh ⊢
    nlinarith
  have hprod : (((2 * M : ℕ) : ℝ) * N) ^ ε = 2 ^ ε * ((M : ℝ) * N) ^ ε := by
    simp only [Nat.cast_mul, Nat.cast_ofNat]
    rw [mul_assoc, Real.mul_rpow (by norm_num) (by positivity)]
  have hsecond := hc (2 * M) N (by omega) hN v
  rw [hprod] at hsecond
  have hb : C * (2 ^ ε * ((M : ℝ) * N) ^ ε) *
      (((2 * M : ℕ) : ℝ) + ((2 * M : ℕ) : ℝ) ^ (1 - ξ) * (N : ℝ) ^ (2 * ξ - 1)) *
        quadraticSieveEnergy N v ≤
      C * (2 ^ ε * ((M : ℝ) * N) ^ ε) *
        (2 * ((M : ℝ) + (M : ℝ) ^ (1 - ξ) * (N : ℝ) ^ (2 * ξ - 1))) *
          quadraticSieveEnergy N v := by gcongr
  have hfirst := hc M N hM hN v
  have htotal := (quadraticWideRows_energy M N v).trans (add_le_add hfirst (hsecond.trans hb))
  convert htotal using 1
  all_goals try with_reducible_and_instances rfl
  ring

theorem quadratic_prime_dilation_image {M Q p m : ℕ} (hQ : 2 ≤ Q)
    (hp : p.Prime) (hpQ : Q < p) (hp2Q : p ≤ 2 * Q)
    (hm : m ∈ (oddSquarefreeRange (2 * M)).filter (M ≤ ·)) (hpm : ¬p ∣ m) :
    p * m ∈ quadraticWideRows (Q * M) := by
  obtain ⟨hm, hlow⟩ := Finset.mem_filter.mp hm
  obtain ⟨hm, ho, hsf⟩ := Finset.mem_filter.mp hm
  obtain ⟨hm₁, hm₂⟩ := Finset.mem_Icc.mp hm
  have hcop := hp.coprime_iff_not_dvd.mpr hpm
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by nlinarith [hp.pos], ?_⟩,
    (hp.odd_of_ne_two (by omega)).mul ho, (Nat.squarefree_mul hcop).mpr ⟨hp.squarefree, hsf⟩⟩, ?_⟩
  · have hh := Nat.mul_le_mul hp2Q hm₂
    nlinarith
  · exact Nat.mul_le_mul hpQ.le hlow

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticDilationPrimes
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Enough actual dilation primes from the proved principal prime estimate -/

namespace Ostmann

open Filter
open scoped Classical BigOperators

theorem quadratic_dilation_primes_sqrt :
    ∀ᶠ Q : ℕ in atTop, 2 ≤ Q ∧ Real.sqrt Q ≤ (sizePrimeBand Q).card := by
  have hlog := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).bound
    (by norm_num : (0 : ℝ) < 1 / 8)
  obtain ⟨A, hA⟩ := eventually_atTop.mp (tendsto_natCast_atTop_atTop.eventually hlog)
  filter_upwards [sizePrimeBand_eventual_bounds, eventually_ge_atTop A] with Q hband hQA
  have hQ : (0 : ℝ) < Q := by exact_mod_cast (by omega : 0 < Q)
  have hh := hA (2 * Q) (by omega)
  simp only [Nat.cast_mul, Nat.cast_ofNat, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (by positivity : 0 ≤ 2 * (Q : ℝ)) (1 / 2 : ℝ))] at hh
  rw [← Real.sqrt_eq_rpow, Real.sqrt_mul (by norm_num)] at hh
  have hs2 : Real.sqrt 2 ≤ 2 := by
    have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    nlinarith [Real.sqrt_nonneg (2 : ℝ)]
  have hsmall : 4 * Real.log (2 * (Q : ℝ)) ≤ Real.sqrt Q := by
    have hm := mul_le_mul_of_nonneg_right hs2 (Real.sqrt_nonneg (Q : ℝ))
    nlinarith [le_abs_self (Real.log (2 * (Q : ℝ)))]
  have hden : 0 < 4 * Real.log (2 * (Q : ℝ)) := by
    apply mul_pos (by norm_num)
    apply Real.log_pos
    have : (2 : ℝ) ≤ Q := by exact_mod_cast hband.1
    linarith
  refine ⟨hband.1, le_trans ?_ hband.2.1⟩
  apply (le_div_iff₀ hden).mpr
  have hm := mul_le_mul_of_nonneg_left hsmall (Real.sqrt_nonneg (Q : ℝ))
  simpa only [Real.mul_self_sqrt hQ.le] using hm

theorem quadratic_dilation_prime_supply (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 2 ≤ C ∧ ∀ X Q : ℕ, 0 < X →
      C * (X : ℝ) ^ δ ≤ Q →
        2 ≤ Q ∧ 6 * Nat.log 2 X ≤ (sizePrimeBand Q).card := by
  obtain ⟨Q₀, hQ₀⟩ := eventually_atTop.mp quadratic_dilation_primes_sqrt
  let A := 1 + ((δ / 2) * Real.log 2)⁻¹
  let C := (Q₀ : ℝ) + 2 + (6 * A) ^ 2
  have hA : 0 < A := by dsimp [A]; positivity
  have hC : 2 ≤ C := by dsimp [C]; nlinarith [sq_nonneg (6 * A), Nat.cast_nonneg (α := ℝ) Q₀]
  refine ⟨C, hC, ?_⟩
  intro X Q hX hCQ
  have hXp : (0 : ℝ) < X := by exact_mod_cast hX
  have hX₁ : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hp : 1 ≤ (X : ℝ) ^ δ := Real.one_le_rpow hX₁ hδ.le
  have hQreal : (Q₀ : ℝ) ≤ Q := by
    have : (Q₀ : ℝ) ≤ C := by dsimp [C]; nlinarith [sq_nonneg (6 * A)]
    have hle := le_mul_of_one_le_right (by linarith : 0 ≤ C) hp
    exact this.trans (hle.trans hCQ)
  have hband := hQ₀ Q (by exact_mod_cast hQreal)
  have hlog : (Nat.log 2 X : ℝ) ≤ A * (X : ℝ) ^ (δ / 2) := by
    have hh := quadratic_dyadic_count_bound (δ / 2) (by positivity) X hX
    dsimp [A]
    push_cast at hh
    linarith
  have hroot : 6 * A * (X : ℝ) ^ (δ / 2) ≤ Real.sqrt Q := by
    apply (Real.le_sqrt (by positivity) (Nat.cast_nonneg Q)).mpr
    have hCbig : (6 * A) ^ 2 ≤ C := by dsimp [C]; nlinarith [Nat.cast_nonneg (α := ℝ) Q₀]
    have he : ((X : ℝ) ^ (δ / 2)) ^ 2 = (X : ℝ) ^ δ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hXp.le]
      congr 1
      ring
    rw [mul_pow, mul_pow, he]
    have hh := mul_le_mul_of_nonneg_right hCbig (Real.rpow_nonneg hXp.le δ)
    nlinarith
  refine ⟨hband.1, ?_⟩
  have hh := (mul_le_mul_of_nonneg_left hlog (by norm_num : (0 : ℝ) ≤ 6)).trans
    (by simpa only [mul_assoc] using hroot.trans hband.2)
  exact_mod_cast hh

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticDyadicDilation
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Quantitative row enlargement using the constructed prime family -/

namespace Ostmann

open scoped Classical BigOperators

theorem quadratic_dyadic_dilation (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 2 ≤ C ∧ ∀ M N Q : ℕ, 0 < M → 0 < N →
      C * ((2 * (M : ℝ) * N) ^ δ) ≤ Q → ∀ U : ℝ, 0 ≤ U →
      QuadraticRowBound (quadraticWideRows (Q * M)) N U →
      QuadraticRowBound ((oddSquarefreeRange (2 * M)).filter (M ≤ ·)) N (4 * U) := by
  obtain ⟨C, hC, hc⟩ := quadratic_dilation_prime_supply δ hδ
  refine ⟨C, hC, ?_⟩
  intro M N Q hM hN hQ U hU hbound
  have hX : 0 < 2 * M * N := by positivity
  obtain ⟨hQ₂, hcount⟩ := hc (2 * M * N) Q hX
    (by simpa only [Nat.cast_mul, Nat.cast_ofNat] using hQ)
  have hNlog : Nat.log 2 N ≤ Nat.log 2 (2 * M * N) :=
    Nat.log_mono_right (by nlinarith)
  have hMlog : Nat.log 2 (2 * M) ≤ Nat.log 2 (2 * M * N) :=
    Nat.log_mono_right (by nlinarith)
  have hlogpos : 1 ≤ Nat.log 2 (2 * M * N) :=
    Nat.le_log_of_pow_le (by norm_num) (by norm_num; nlinarith)
  apply quadratic_prime_dilation (P := sizePrimeBand Q) (R := 2 * M)
    (fun p hp => (mem_sizePrimeBand.mp hp).1) (by omega)
    (fun m hm => ?_) (fun p hp m hm hpm => ?_)
    (by omega) hU hbound
  · have hi := Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hm).1).1
    exact hi
  · obtain ⟨hp, hpQ, hp2Q⟩ := mem_sizePrimeBand.mp hp
    exact quadratic_prime_dilation_image hQ₂ hp hpQ hp2Q hm hpm

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticBalancedExponent
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The balanced exponent and an explicit enlarged row cutoff -/

namespace Ostmann

theorem quadratic_improved_exponent_bounds {ξ : ℝ} (hξ : 1 ≤ ξ) :
    1 ≤ quadraticImprovedExponent ξ ∧ quadraticImprovedExponent ξ ≤ 2 := by
  have hpos : 0 < ξ := by linarith
  have hdiv : 1 / ξ ≤ 1 := (div_le_one hpos).mpr hξ
  unfold quadraticImprovedExponent
  constructor <;> linarith [one_div_pos.mpr hpos]

theorem quadratic_improved_exponent_balance {ξ : ℝ} (hξ : 0 < ξ) :
    quadraticImprovedExponent ξ * ξ = 2 * ξ - 1 := by
  unfold quadraticImprovedExponent
  field_simp

theorem quadratic_balanced_row_power {ξ N L : ℝ} (hξ : 1 ≤ ξ) (hN : 0 < N)
    (hL : N ^ quadraticImprovedExponent ξ ≤ L) :
    L ^ (1 - ξ) * N ^ (2 * ξ - 1) ≤ N ^ quadraticImprovedExponent ξ := by
  have hp : 0 < N ^ quadraticImprovedExponent ξ := Real.rpow_pos_of_pos hN _
  calc
    _ ≤ (N ^ quadraticImprovedExponent ξ) ^ (1 - ξ) * N ^ (2 * ξ - 1) :=
      mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_nonpos hp hL (by linarith)) (by positivity)
    _ = N ^ quadraticImprovedExponent ξ := by
      rw [← Real.rpow_mul hN.le, ← Real.rpow_add hN]
      congr 1
      have hh := quadratic_improved_exponent_balance (by linarith : 0 < ξ)
      nlinarith

theorem quadratic_dilation_cutoff_bounds {C δ p : ℝ} (hC : 1 ≤ C) (hδ : 0 ≤ δ)
    {M N : ℕ} (hM : 0 < M) (hN : 0 < N) :
    C * (2 * (M : ℝ) * N) ^ δ ≤ quadraticDilationCutoff C δ p M N ∧
      (N : ℝ) ^ p ≤ ((quadraticDilationCutoff C δ p M N * M : ℕ) : ℝ) ∧
      ((quadraticDilationCutoff C δ p M N * M : ℕ) : ℝ) ≤
        (C + 1) * (2 * (M : ℝ) * N) ^ δ * ((M : ℝ) + (N : ℝ) ^ p) := by
  let Y := (2 * (M : ℝ) * N) ^ δ
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hY : 1 ≤ Y := Real.one_le_rpow (by
    have hM₁ : (1 : ℝ) ≤ M := by exact_mod_cast hM
    have hN₁ : (1 : ℝ) ≤ N := by exact_mod_cast hN
    nlinarith) hδ
  have hlo : C * Y * max 1 ((N : ℝ) ^ p / M) ≤ quadraticDilationCutoff C δ p M N := Nat.le_ceil _
  have hhi : (quadraticDilationCutoff C δ p M N : ℝ) ≤
      C * Y * max 1 ((N : ℝ) ^ p / M) + 1 := (Nat.ceil_lt_add_one (by positivity)).le
  have hCY : 1 ≤ C * Y := one_le_mul_of_one_le_of_one_le hC hY
  have hmax : max 1 ((N : ℝ) ^ p / M) * M = max (M : ℝ) ((N : ℝ) ^ p) := by
    rw [max_mul_of_nonneg _ _ hMR.le, one_mul, div_mul_cancel₀ _ hMR.ne']
  refine ⟨?_, ?_, ?_⟩
  · exact (le_mul_of_one_le_right (by positivity) (le_max_left _ _)).trans hlo
  · have hh := mul_le_mul_of_nonneg_right hlo hMR.le
    rw [Nat.cast_mul]
    calc
      _ ≤ max (M : ℝ) ((N : ℝ) ^ p) := le_max_right _ _
      _ ≤ C * Y * max (M : ℝ) ((N : ℝ) ^ p) := le_mul_of_one_le_left (by positivity) hCY
      _ ≤ _ := by simpa only [mul_assoc, hmax] using hh
  · have hh := mul_le_mul_of_nonneg_right hhi hMR.le
    have hm : (M : ℝ) ≤ Y * ((M : ℝ) + (N : ℝ) ^ p) := by nlinarith [Real.rpow_pos_of_pos hNR p]
    have hmaxsum : max (M : ℝ) ((N : ℝ) ^ p) ≤ (M : ℝ) + (N : ℝ) ^ p :=
      max_le (le_add_of_nonneg_right (by positivity)) (le_add_of_nonneg_left hMR.le)
    rw [Nat.cast_mul]
    calc
      _ ≤ C * Y * max (M : ℝ) ((N : ℝ) ^ p) + M := by
        simpa only [add_mul, one_mul, mul_assoc, hmax] using hh
      _ ≤ C * Y * ((M : ℝ) + (N : ℝ) ^ p) + Y * ((M : ℝ) + (N : ℝ) ^ p) := by gcongr
      _ = _ := by dsimp [Y]; ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticDilationPowerCost
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The enlarged balanced row interval costs only a small power -/

namespace Ostmann

theorem quadratic_dilation_power_cost {ξ δ a D M N L : ℝ}
    (hξ : 1 ≤ ξ) (hδ : 0 ≤ δ) (hδ' : δ ≤ 1) (ha : 0 ≤ a) (hD : 1 ≤ D)
    (hM : 1 ≤ M) (hN : 1 ≤ N) (hL : N ^ quadraticImprovedExponent ξ ≤ L)
    (hLu : L ≤ D * (2 * M * N) ^ δ * (M + N ^ quadraticImprovedExponent ξ)) :
    (L * N) ^ a * (L + L ^ (1 - ξ) * N ^ (2 * ξ - 1)) ≤
      (3 * D * (4 * D) ^ a) * (M * N) ^ (4 * a + δ) *
        (M + N ^ quadraticImprovedExponent ξ) := by
  let X := M * N
  let H := M + N ^ quadraticImprovedExponent ξ
  have hMp : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have hNp : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hXp : 0 < X := mul_pos hMp hNp
  have hX : 1 ≤ X := one_le_mul_of_one_le_of_one_le hM hN
  have hHp : 0 < H := by dsimp [H]; positivity
  have hLp : 0 < L := lt_of_lt_of_le (by positivity) hL
  have hMX : M ≤ X := le_mul_of_one_le_right hMp.le hN
  have hNX : N ≤ X := le_mul_of_one_le_left hNp.le hM
  have hH : H ≤ 2 * X ^ 2 := by
    have hp := Real.rpow_le_rpow_of_exponent_le hN (quadratic_improved_exponent_bounds hξ).2
    rw [Real.rpow_two] at hp
    have hs := pow_le_pow_left₀ hNp.le hNX 2
    have hXX := le_self_pow₀ hX (by norm_num : (2 : ℕ) ≠ 0)
    dsimp [H]
    nlinarith
  have htwoX : 1 ≤ 2 * X := by linarith
  have hLpoly : L ≤ 4 * D * X ^ 3 := by
    have hp : (2 * X) ^ δ ≤ 2 * X := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le htwoX hδ'
    calc
      _ ≤ D * (2 * X) ^ δ * H := by simpa only [X, H, mul_assoc] using hLu
      _ ≤ D * (2 * X) * (2 * X ^ 2) := by gcongr
      _ = _ := by ring
  have hLN : L * N ≤ 4 * D * X ^ 4 := by
    calc
      _ ≤ (4 * D * X ^ 3) * X := mul_le_mul hLpoly hNX hNp.le (by positivity)
      _ = _ := by ring
  have hmass : L + L ^ (1 - ξ) * N ^ (2 * ξ - 1) ≤ 3 * D * X ^ δ * H := by
    have hs := quadratic_balanced_row_power hξ hNp hL
    have htwo : (2 : ℝ) ^ δ ≤ 2 := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hδ'
    have hpow : 1 ≤ X ^ δ := Real.one_le_rpow hX hδ
    have hsum : N ^ quadraticImprovedExponent ξ ≤ X ^ δ * H := by
      have hh : N ^ quadraticImprovedExponent ξ ≤ H := le_add_of_nonneg_left hMp.le
      exact hh.trans (le_mul_of_one_le_left hHp.le hpow)
    have hLshort : L ≤ 2 * D * X ^ δ * H := by
      calc
        _ ≤ D * (2 * X) ^ δ * H := by simpa only [X, H, mul_assoc] using hLu
        _ = D * (2 ^ δ * X ^ δ) * H := by rw [Real.mul_rpow (by norm_num) hXp.le]
        _ = (D * X ^ δ * H) * 2 ^ δ := by ring
        _ ≤ (D * X ^ δ * H) * 2 := mul_le_mul_of_nonneg_left htwo (by positivity)
        _ = _ := by ring
    have hDX := mul_le_mul_of_nonneg_right hD (show 0 ≤ X ^ δ * H by positivity)
    nlinarith only [hs, hsum, hLshort, hDX]
  have hpower : (L * N) ^ a ≤ (4 * D) ^ a * X ^ (4 * a) := by
    calc
      _ ≤ (4 * D * X ^ 4) ^ a := Real.rpow_le_rpow (by positivity) hLN ha
      _ = _ := by
        rw [Real.mul_rpow (by positivity) (by positivity)]
        congr 1
        rw [← Real.rpow_natCast X 4, ← Real.rpow_mul hXp.le]
        norm_num
  calc
    _ ≤ ((4 * D) ^ a * X ^ (4 * a)) * (3 * D * X ^ δ * H) :=
      mul_le_mul hpower hmass (by positivity) (by positivity)
    _ = _ := by
      change _ = (3 * D * (4 * D) ^ a) * X ^ (4 * a + δ) * H
      rw [Real.rpow_add hXp]
      ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticDyadicImprovement
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Prime dilation improves the exponent on every dyadic row interval -/

namespace Ostmann

open scoped Classical BigOperators

theorem quadratic_dyadic_improvement {ξ : ℝ} (h : QuadraticSieveGrowth ξ)
    (hξ : 1 ≤ ξ) (hξ' : ξ ≤ 2) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ M N : ℕ, 0 < M → 0 < N →
      QuadraticRowBound ((oddSquarefreeRange (2 * M)).filter (M ≤ ·)) N
        (C * ((M : ℝ) * N) ^ ε * ((M : ℝ) + (N : ℝ) ^ quadraticImprovedExponent ξ)) := by
  let δ := min (ε / 2) 1
  let a := ε / 8
  have hδ : 0 < δ := lt_min (by positivity) (by norm_num)
  have hδ₁ : δ ≤ 1 := min_le_right _ _
  have ha : 0 < a := by dsimp [a]; positivity
  have hexp : 4 * a + δ ≤ ε := by
    have hd := min_le_left (ε / 2) (1 : ℝ)
    dsimp [a, δ]
    linarith
  obtain ⟨C₀, hC₀, hdilate⟩ := quadratic_dyadic_dilation δ hδ
  obtain ⟨B, hB, hwide⟩ := quadratic_wide_rows_growth h hξ hξ' a ha
  let D := C₀ + 1
  let F := 3 * D * (4 * D) ^ a
  have hD : 1 ≤ D := by dsimp [D]; linarith
  have hF : 0 < F := by dsimp [F]; positivity
  refine ⟨4 * B * F, by positivity, ?_⟩
  intro M N hM hN
  let Q := quadraticDilationCutoff C₀ δ (quadraticImprovedExponent ξ) M N
  let L := Q * M
  have hM₁ : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hN₁ : (1 : ℝ) ≤ N := by exact_mod_cast hN
  obtain ⟨hQ, hL, hLu⟩ := quadratic_dilation_cutoff_bounds (by linarith : 1 ≤ C₀) hδ.le hM hN
    (p := quadraticImprovedExponent ξ)
  have hLp : (0 : ℝ) < L := lt_of_lt_of_le (by positivity) hL
  have hLn : 0 < L := by exact_mod_cast hLp
  have hcost := quadratic_dilation_power_cost hξ hδ.le hδ₁ ha.le hD hM₁ hN₁ hL hLu
  have hX : 1 ≤ (M : ℝ) * N := one_le_mul_of_one_le_of_one_le hM₁ hN₁
  have hp : ((M : ℝ) * N) ^ (4 * a + δ) ≤ ((M : ℝ) * N) ^ ε :=
    Real.rpow_le_rpow_of_exponent_le hX hexp
  let U := B * (((L : ℝ) * N) ^ a) *
    ((L : ℝ) + (L : ℝ) ^ (1 - ξ) * (N : ℝ) ^ (2 * ξ - 1))
  have hU : 0 ≤ U := by dsimp [U]; positivity
  have hb := hdilate M N Q hM hN hQ U hU (hwide L N hLn hN)
  apply hb.mono_constant
  have hscale : 0 ≤ (M : ℝ) + (N : ℝ) ^ quadraticImprovedExponent ξ := by positivity
  calc
    4 * U = (4 * B) * ((((L : ℝ) * N) ^ a) *
        ((L : ℝ) + (L : ℝ) ^ (1 - ξ) * (N : ℝ) ^ (2 * ξ - 1))) := by dsimp [U]; ring
    _ ≤ (4 * B) * (F * ((M : ℝ) * N) ^ (4 * a + δ) *
        ((M : ℝ) + (N : ℝ) ^ quadraticImprovedExponent ξ)) :=
      mul_le_mul_of_nonneg_left hcost (by positivity)
    _ ≤ (4 * B) * (F * ((M : ℝ) * N) ^ ε *
        ((M : ℝ) + (N : ℝ) ^ quadraticImprovedExponent ξ)) := by gcongr
    _ = _ := by ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticFullRows
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Passing from disjoint dyadic rows to the full quadratic matrix -/

namespace Ostmann

open scoped Classical BigOperators

theorem quadratic_full_rows_of_dyadic {p ε C : ℝ} (hε : 0 ≤ ε) (hC : 0 ≤ C)
    {M N : ℕ} (hM : 0 < M)
    (h : ∀ R : ℕ, 0 < R → QuadraticRowBound
      ((oddSquarefreeRange (2 * R)).filter (R ≤ ·)) N
      (C * ((R : ℝ) * N) ^ ε * ((R : ℝ) + (N : ℝ) ^ p))) :
    QuadraticRowBound (oddSquarefreeRange M) N
      ((Nat.log 2 M + 1 : ℕ) * C * ((M : ℝ) * N) ^ ε * ((M : ℝ) + (N : ℝ) ^ p)) := by
  intro v
  have hE : 0 ≤ quadraticSieveEnergy N v := Finset.sum_nonneg fun _ _ => sq_nonneg _
  unfold quadraticRowEnergy
  rw [← quadratic_dyadic_divisors_sum M]
  calc
    _ ≤ ∑ _j ∈ Finset.range (Nat.log 2 M + 1),
        C * ((M : ℝ) * N) ^ ε * ((M : ℝ) + (N : ℝ) ^ p) * quadraticSieveEnergy N v := by
      apply Finset.sum_le_sum
      intro j hj
      have hR : 0 < 2 ^ j := by positivity
      have hRM : 2 ^ j ≤ M := (Nat.pow_le_pow_right (by norm_num : 0 < 2)
        (by have := Finset.mem_range.mp hj; omega)).trans (Nat.pow_log_le_self 2 (by omega))
      have hsub : quadraticDyadicDivisors M j ⊆
          (oddSquarefreeRange (2 * 2 ^ j)).filter (2 ^ j ≤ ·) := by
        intro m hm
        exact Finset.mem_filter.mpr
          ⟨quadraticDyadicDivisors_subset_double M j hm, (quadraticDyadicDivisors_bounds hm).1⟩
      apply (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => sq_nonneg _)).trans
      apply (h (2 ^ j) hR v).trans
      apply mul_le_mul_of_nonneg_right _ hE
      apply mul_le_mul
      · apply mul_le_mul_of_nonneg_left _ hC
        exact Real.rpow_le_rpow (by positivity)
          (mul_le_mul_of_nonneg_right (by exact_mod_cast hRM) (Nat.cast_nonneg N)) hε
      · exact add_le_add (by exact_mod_cast hRM) le_rfl
      · positivity
      · positivity
    _ = _ := by simp; ring

theorem quadratic_sieve_of_row_bound {M N : ℕ} {T : ℝ}
    (h : QuadraticRowBound (oddSquarefreeRange M) N T) : QuadraticSieveBound M N (2 * T) := by
  intro v
  have hv := h v
  have hw := h (reciprocityTwist v)
  rw [quadraticSieveEnergy_reciprocityTwist] at hw
  have htw : reciprocityTwist (reciprocityTwist v) = v := by
    funext n
    simp only [reciprocityTwist]
    split_ifs <;> simp
  have hs : (∑ m ∈ oddSquarefreeRange M, ‖quadraticSieveSum N v m‖ ^ 2) ≤
      quadraticRowEnergy (oddSquarefreeRange M) N v +
        quadraticRowEnergy (oddSquarefreeRange M) N (reciprocityTwist v) := by
    unfold quadraticRowEnergy
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro m hm
    have ho := (Finset.mem_filter.mp hm).2.1
    rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp ho) with h1 | h3
    · rw [quadraticTransposeSum_one_mod_four N v m h1]
      linarith [sq_nonneg ‖quadraticTransposeSum N (reciprocityTwist v) m‖]
    · rw [quadraticTransposeSum_three_mod_four N (reciprocityTwist v) m h3, htw]
      linarith [sq_nonneg ‖quadraticTransposeSum N v m‖]
  nlinarith only [hs, hv, hw]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticGrowthBridge
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Recovering the full matrix bound from uniform dyadic estimates -/

namespace Ostmann

theorem quadratic_growth_of_dyadic (p : ℝ)
    (h : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ M N : ℕ, 0 < M → 0 < N →
      QuadraticRowBound ((oddSquarefreeRange (2 * M)).filter (M ≤ ·)) N
        (C * ((M : ℝ) * N) ^ ε * ((M : ℝ) + (N : ℝ) ^ p))) :
    QuadraticSieveGrowth p := by
  intro ε hε
  obtain ⟨C, hC, hc⟩ := h (ε / 2) (by positivity)
  let A := 1 + ((ε / 2) * Real.log 2)⁻¹
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨2 * C * A, by positivity, ?_⟩
  intro M N hM hN
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hXp : 0 < (M : ℝ) * N := mul_pos hMR hNR
  have hMX : (M : ℝ) ≤ (M : ℝ) * N := le_mul_of_one_le_right hMR.le (by exact_mod_cast hN)
  have hl : ((Nat.log 2 M + 1 : ℕ) : ℝ) ≤ A * ((M : ℝ) * N) ^ (ε / 2) := by
    apply (quadratic_dyadic_count_bound (ε / 2) (by positivity) M hM).trans
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow hMR.le hMX (by positivity)) hA.le
  have hfull := quadratic_full_rows_of_dyadic (by positivity : (0 : ℝ) ≤ ε / 2)
    hC.le (by omega : 0 < M) (fun R hR => hc R N hR hN)
  apply (quadratic_sieve_of_row_bound hfull).mono_constant
  have he : ((M : ℝ) * N) ^ ε =
      ((M : ℝ) * N) ^ (ε / 2) * ((M : ℝ) * N) ^ (ε / 2) := by
    rw [← Real.rpow_add hXp]
    congr 1
    ring
  calc
    _ ≤ 2 * ((A * ((M : ℝ) * N) ^ (ε / 2)) * C *
        ((M : ℝ) * N) ^ (ε / 2) * ((M : ℝ) + (N : ℝ) ^ p)) := by gcongr
    _ = _ := by rw [he]; ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticSieveProof
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Heath-Brown's quadratic large sieve from the proved exponent descent -/

namespace Ostmann

theorem quadratic_sieve_growth_improve {ξ : ℝ} (h : QuadraticSieveGrowth ξ)
    (hξ : 1 ≤ ξ) (hξ' : ξ ≤ 2) : QuadraticSieveGrowth (quadraticImprovedExponent ξ) :=
  quadratic_growth_of_dyadic _ (quadratic_dyadic_improvement h hξ hξ')

theorem quadraticSieveExponent_bounds (r : ℕ) :
    1 ≤ quadraticSieveExponent r ∧ quadraticSieveExponent r ≤ 2 := by
  have hr : (1 : ℝ) ≤ (r : ℝ) + 1 := by have := Nat.cast_nonneg (α := ℝ) r; linarith
  have hdiv : 1 / ((r : ℝ) + 1) ≤ 1 := (div_le_one (by positivity)).mpr hr
  unfold quadraticSieveExponent
  constructor <;> linarith [one_div_pos.mpr (by positivity : (0 : ℝ) < (r : ℝ) + 1)]

theorem quadraticSieveExponent_step (r : ℕ) :
    quadraticImprovedExponent (quadraticSieveExponent r) = quadraticSieveExponent (r + 1) := by
  have h₁ : (r : ℝ) + 1 ≠ 0 := by positivity
  have h₂ : (r : ℝ) + 2 ≠ 0 := by positivity
  unfold quadraticImprovedExponent quadraticSieveExponent
  push_cast
  field_simp
  ring

theorem quadratic_sieve_growth_sequence (r : ℕ) : QuadraticSieveGrowth (quadraticSieveExponent r) := by
  induction r with
  | zero =>
    convert quadratic_sieve_growth_two using 1
    all_goals try with_reducible_and_instances rfl
    norm_num [quadraticSieveExponent]
  | succ r ih =>
    rw [← quadraticSieveExponent_step]
    exact quadratic_sieve_growth_improve ih (quadraticSieveExponent_bounds r).1 (quadraticSieveExponent_bounds r).2

/-- Heath-Brown's odd-squarefree quadratic large sieve
(1995, Theorem 1), in the range used for the prime decomposition. -/
theorem publishedQuadraticLargeSieve_oai : PublishedQuadraticLargeSieve := by
  intro ε hε
  obtain ⟨r, hr⟩ := exists_nat_gt (2 / ε)
  have hrp : (0 : ℝ) < (r : ℝ) + 1 := by positivity
  have hsmall : 1 / ((r : ℝ) + 1) ≤ ε / 2 := by
    apply (div_le_iff₀ hrp).mpr
    have hh := (div_lt_iff₀ hε).mp hr
    nlinarith
  obtain ⟨C, hC, hc⟩ := quadratic_sieve_growth_sequence r (ε / 2) (by positivity)
  refine ⟨C, hC, ?_⟩
  intro M N hM hN v
  have hMR : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hXp : 0 < (M : ℝ) * N := by positivity
  have hX : 1 ≤ (M : ℝ) * N := one_le_mul_of_one_le_of_one_le hMR hNR
  have hNpow : (N : ℝ) ^ (1 / ((r : ℝ) + 1)) ≤ ((M : ℝ) * N) ^ (ε / 2) := by
    apply (Real.rpow_le_rpow_of_exponent_le hNR hsmall).trans
    exact Real.rpow_le_rpow (Nat.cast_nonneg N)
      (le_mul_of_one_le_left (Nat.cast_nonneg N) hMR) (by positivity)
  have hS : (M : ℝ) + (N : ℝ) ^ quadraticSieveExponent r ≤
      (((M : ℝ) * N) ^ (ε / 2)) * ((M : ℝ) + N) := by
    rw [quadraticSieveExponent, Real.rpow_add (by positivity : (0 : ℝ) < N), Real.rpow_one]
    have hm := mul_le_mul_of_nonneg_right (Real.one_le_rpow hX (by positivity : (0 : ℝ) ≤ ε / 2))
      (Nat.cast_nonneg M)
    have hn := mul_le_mul_of_nonneg_left hNpow (Nat.cast_nonneg N)
    nlinarith only [hm, hn]
  have hp : ((M : ℝ) * N) ^ ε =
      ((M : ℝ) * N) ^ (ε / 2) * ((M : ℝ) * N) ^ (ε / 2) := by
    rw [← Real.rpow_add hXp]
    congr 1
    ring
  apply (hc M N hM hN v).trans
  calc
    _ ≤ C * ((M : ℝ) * N) ^ (ε / 2) *
        ((((M : ℝ) * N) ^ (ε / 2)) * ((M : ℝ) + N)) * quadraticSieveEnergy N v := by
      apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
      exact mul_le_mul_of_nonneg_left hS (by positivity)
    _ = _ := by rw [hp]; ring

end Ostmann

end OAI
end

theorem solution : type_of% @OAI.Ostmann.publishedQuadraticLargeSieve_oai := @OAI.Ostmann.publishedQuadraticLargeSieve_oai
