-- Prove2me | solution 1 for OAI.SevenEighths.HeckeFamily.LFunction_ne_zero_of_one_le_re
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T01:40:55.74243+00:00
-- url     : https://prove2.me/submissions/863ca50d-b3f7-4e19-8144-d51bae9cbe84

import Mathlib
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B016
import Theorems.Thm_OAI_SmoothMobiusCorrection_prime_norm_two_le

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Mellin.LocalNonvanishing
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar

open Filter Asymptotics

open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter

namespace ShortDraftHeckeBridge

theorem normFiber_LSeries_eq_pair_inverse
    {q r : ℕ} (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r)
    (weight : Ideal O → ℂ)
    (hcoeff : ∀ n : ℕ, n ≠ 0 → normFiberCoeff weight n = pairInverseCoeff χ ψ n)
    (s : ℂ) :
    LSeries (normFiberCoeff weight) s = LSeries (pairInverseCoeff χ ψ) s := by
  exact LSeries_congr (fun {n} hn => hcoeff n hn) s

theorem pair_inverse_euler_identity
    {q r : ℕ} [NeZero q] [NeZero r]
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r)
    (s : ℂ) (hs : 1 < s.re) :
    χ.LFunction s * ψ.LFunction s * LSeries (pairInverseCoeff χ ψ) s = 1 := by
  have hχsum : LSeriesSummable (fun n : ℕ => χ n * (ArithmeticFunction.moebius n : ℂ)) s := by
    exact DirichletCharacter.LSeriesSummable_mul χ
      (ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs)
  have hψsum : LSeriesSummable (fun n : ℕ => ψ n * (ArithmeticFunction.moebius n : ℂ)) s := by
    exact DirichletCharacter.LSeriesSummable_mul ψ
      (ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs)
  rw [pairInverseCoeff, LSeries_convolution' hχsum hψsum,
    χ.LFunction_eq_LSeries hs, ψ.LFunction_eq_LSeries hs]
  have hχ := DirichletCharacter.LSeries.mul_mu_eq_one χ hs
  have hψ := DirichletCharacter.LSeries.mul_mu_eq_one ψ hs
  change LSeries (χ ·) s * LSeries (fun n : ℕ => χ n * (ArithmeticFunction.moebius n : ℂ)) s = 1 at hχ
  change LSeries (ψ ·) s * LSeries (fun n : ℕ => ψ n * (ArithmeticFunction.moebius n : ℂ)) s = 1 at hψ
  calc
    LSeries (χ ·) s * LSeries (ψ ·) s *
      (LSeries (fun n : ℕ => χ n * (ArithmeticFunction.moebius n : ℂ)) s *
        LSeries (fun n : ℕ => ψ n * (ArithmeticFunction.moebius n : ℂ)) s) =
      (LSeries (χ ·) s * LSeries (fun n : ℕ => χ n * (ArithmeticFunction.moebius n : ℂ)) s) *
      (LSeries (ψ ·) s * LSeries (fun n : ℕ => ψ n * (ArithmeticFunction.moebius n : ℂ)) s) := by ring
    _ = 1 := by rw [hχ, hψ]; ring

end ShortDraftHeckeBridge

open MulChar AddChar

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Arithmetic.NormFiberMellin
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar

open MulChar AddChar

namespace ShortDraftHeckeBridge

theorem baseChangeWeight_prime {q : ℕ} (χ : DirichletCharacter ℂ q)
    (P : Ideal O) (hP : Prime P) :
    baseChangeWeight χ P = -χ (Ideal.absNorm P) := by
  rw [baseChangeWeight, hP.irreducible.moebius_eq]
  norm_num

theorem invCharAF_apply {q : ℕ} (χ : DirichletCharacter ℂ q)
    {n : ℕ} (hn : n ≠ 0) :
    invCharAF χ n = χ n * (ArithmeticFunction.moebius n : ℂ) := by
  change ((toArithmeticFunction (χ ·)).pmul
    (ArithmeticFunction.moebius : ArithmeticFunction ℂ)) n = _
  rw [ArithmeticFunction.pmul_apply]
  simp [toArithmeticFunction, hn]

private theorem invCharAF_mult {q : ℕ} (χ : DirichletCharacter ℂ q) :
    (invCharAF χ).IsMultiplicative := by
  exact (χ.isMultiplicative_toArithmeticFunction).pmul
    (ArithmeticFunction.isMultiplicative_moebius.intCast)

theorem pairAF_mult {q r : ℕ} (χ : DirichletCharacter ℂ q)
    (ψ : DirichletCharacter ℂ r) :
    (pairAF χ ψ).IsMultiplicative :=
  (invCharAF_mult χ).mul (invCharAF_mult ψ)

theorem pairAF_eq_pairInverseCoeff {q r : ℕ}
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r)
    (n : ℕ) : pairAF χ ψ n = pairInverseCoeff χ ψ n := by
  rw [pairAF, ← ArithmeticFunction.coe_mul]
  apply congrFun
  exact (LSeries.convolution_congr
    (fun {k} hk => invCharAF_apply χ hk)
    (fun {k} hk => invCharAF_apply ψ hk))

theorem normFiber_eq_pair_of_prime_powers
    {q r : ℕ} (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r)
    (weight : Ideal O → ℂ)
    (hb : (toArithmeticFunction (normFiberCoeff weight)).IsMultiplicative)
    (hlocal : ∀ p k : ℕ, p.Prime →
      (toArithmeticFunction (normFiberCoeff weight)) (p ^ k) =
        pairAF χ ψ (p ^ k))
    (n : ℕ) (hn : n ≠ 0) :
    normFiberCoeff weight n = pairInverseCoeff χ ψ n := by
  have heq : toArithmeticFunction (normFiberCoeff weight) = pairAF χ ψ :=
    (ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers
      _ hb _ (pairAF_mult χ ψ)).2 hlocal
  have h := congrFun (congrArg DFunLike.coe heq) n
  calc
    normFiberCoeff weight n = (toArithmeticFunction (normFiberCoeff weight)) n := by
      simp [toArithmeticFunction, hn]
    _ = pairAF χ ψ n := h
    _ = pairInverseCoeff χ ψ n := pairAF_eq_pairInverseCoeff χ ψ n

theorem pairAF_prime {q r : ℕ} (χ : DirichletCharacter ℂ q)
    (ψ : DirichletCharacter ℂ r) {p : ℕ} (hp : p.Prime) :
    pairAF χ ψ p = -(χ p + ψ p) := by
  have h1χ : invCharAF χ 1 = 1 := (invCharAF_mult χ).map_one
  have h1ψ : invCharAF ψ 1 = 1 := (invCharAF_mult ψ).map_one
  have hpχ : invCharAF χ p = -χ p := by
    rw [invCharAF_apply χ hp.ne_zero, ArithmeticFunction.moebius_apply_prime hp]
    simp
  have hpψ : invCharAF ψ p = -ψ p := by
    rw [invCharAF_apply ψ hp.ne_zero, ArithmeticFunction.moebius_apply_prime hp]
    simp
  rw [pairAF, ArithmeticFunction.mul_apply]
  conv_lhs => rw [Nat.sum_divisorsAntidiagonal
    (fun a b => invCharAF χ a * invCharAF ψ b)]
  rw [hp.divisors]
  have hnot : 1 ∉ ({p} : Finset ℕ) := by simpa using hp.ne_one.symm
  rw [Finset.sum_insert hnot, Finset.sum_singleton]
  simp [Nat.div_one, Nat.div_self hp.pos, h1χ, h1ψ, hpχ, hpψ]

theorem pairAF_prime_sq {q r : ℕ} (χ : DirichletCharacter ℂ q)
    (ψ : DirichletCharacter ℂ r) {p : ℕ} (hp : p.Prime) :
    pairAF χ ψ (p ^ 2) = χ p * ψ p := by
  have h1χ : invCharAF χ 1 = 1 := (invCharAF_mult χ).map_one
  have h1ψ : invCharAF ψ 1 = 1 := (invCharAF_mult ψ).map_one
  have hpχ : invCharAF χ p = -χ p := by
    rw [invCharAF_apply χ hp.ne_zero, ArithmeticFunction.moebius_apply_prime hp]
    simp
  have hpψ : invCharAF ψ p = -ψ p := by
    rw [invCharAF_apply ψ hp.ne_zero, ArithmeticFunction.moebius_apply_prime hp]
    simp
  have hp2χ : invCharAF χ (p ^ 2) = 0 := by
    rw [invCharAF_apply χ (pow_ne_zero 2 hp.ne_zero),
      ArithmeticFunction.moebius_apply_prime_pow hp (by decide)]
    simp
  have hp2ψ : invCharAF ψ (p ^ 2) = 0 := by
    rw [invCharAF_apply ψ (pow_ne_zero 2 hp.ne_zero),
      ArithmeticFunction.moebius_apply_prime_pow hp (by decide)]
    simp
  have hdiv : (p ^ 2).divisors = ({1, p, p ^ 2} : Finset ℕ) := by
    ext x
    rw [Nat.mem_divisors_prime_pow hp 2]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨j, hj, rfl⟩
      interval_cases j <;> simp
    · rintro (rfl | rfl | rfl)
      · exact ⟨0, by decide, by simp⟩
      · exact ⟨1, by decide, by simp⟩
      · exact ⟨2, by decide, by simp⟩
  rw [pairAF, ArithmeticFunction.mul_apply]
  conv_lhs => rw [Nat.sum_divisorsAntidiagonal
    (fun a b => invCharAF χ a * invCharAF ψ b)]
  rw [hdiv]
  have hpge : 2 ≤ p := hp.two_le
  have h1p2 : 1 ≠ p ^ 2 := by nlinarith
  have hpp2 : p ≠ p ^ 2 := by nlinarith
  have hnot1 : 1 ∉ ({p, p ^ 2} : Finset ℕ) := by
    simp [hp.ne_one.symm, h1p2]
  have hnotp : p ∉ ({p ^ 2} : Finset ℕ) := by
    simp [hpp2]
  rw [Finset.sum_insert hnot1, Finset.sum_insert hnotp, Finset.sum_singleton]
  have hdivp : p ^ 2 / p = p := by simp [pow_two, hp.pos]
  simp [Nat.div_one, hdivp, h1χ,  hpχ, hpψ, hp2χ, hp2ψ]

theorem chiMinusThree_two : chiMinusThree (2 : ℕ) = -1 := by
  have h3 : ringChar (ZMod 3) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; decide
  have h2 : (2 : ZMod 3) ≠ 0 := by decide
  have h21 : (2 : ZMod 3) ≠ 1 := by decide
  change ((quadraticChar (ZMod 3) (2 : ZMod 3) : ℤ) : ℂ) = -1
  rw [quadraticChar_eq_pow_of_char_ne_two h3 h2]
  simp [h21]

theorem chiMinusThree_ne_one : chiMinusThree ≠ 1 := by
  intro h
  have hh := congrArg (fun ξ : DirichletCharacter ℂ 3 => ξ (2 : ℕ)) h
  rw [chiMinusThree_two] at hh
  have hunit : IsUnit (2 : ZMod 3) := by decide
  change (-1 : ℂ) = (1 : DirichletCharacter ℂ 3) (2 : ZMod 3) at hh
  rw [MulChar.one_apply hunit] at hh
  norm_num at hh

theorem not_both_principal {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) :
    ¬ ((χ.changeLevel (Nat.dvd_mul_right q 3) = 1) ∧
      χ.changeLevel (Nat.dvd_mul_right q 3) *
        chiMinusThree.changeLevel (Nat.dvd_mul_left 3 q) = 1) := by
  rintro ⟨hχ, hprod⟩
  rw [hχ, one_mul] at hprod
  have hη : chiMinusThree = 1 :=
    (DirichletCharacter.changeLevel_eq_one_iff (Nat.dvd_mul_left 3 q)).mp hprod
  exact chiMinusThree_ne_one hη

end ShortDraftHeckeBridge
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.FiniteConductor
namespace OAI

namespace SevenEighths.FiniteConductor

open SevenEighths.FiniteFourier
open scoped Classical

noncomputable section

variable {R : Type*} [CommRing R] [Finite R]

theorem FactorsThroughIdeal.mono {χ : MulChar R ℂ} {I J : Ideal R}
    (h : FactorsThroughIdeal χ I) (hJI : J ≤ I) : FactorsThroughIdeal χ J := by
  rw [factorsThroughIdeal_iff] at h ⊢
  exact fun u hu => h u (hJI hu)

end

end SevenEighths.FiniteConductor

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.ConductorPresentation
namespace OAI

namespace SevenEighths

namespace FiniteConductor

variable {R : Type*} [CommRing R] [Finite R]

theorem FactorsThroughIdeal.pow {χ : MulChar R ℂ} {I : Ideal R}
    (hχ : FactorsThroughIdeal χ I) (n : ℕ) : FactorsThroughIdeal (χ ^ n) I := by
  rw [factorsThroughIdeal_iff] at hχ ⊢
  intro u hu
  rw [MulChar.pow_apply_coe, hχ u hu, one_pow]

end FiniteConductor

end SevenEighths

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.NormFiberCharacters
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology

namespace ShortDraftHeckeBridge

theorem baseChangeChar_ne_one_of_one {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ = 1) :
    baseChangeChar χ ≠ 1 := by
  intro h
  apply not_both_principal χ
  constructor
  · simp [hχ]
  · exact h

end ShortDraftHeckeBridge

namespace ShortDraftHeckeBridge

theorem ideals_isRelPrime_of_norms_coprime (I J : Ideal O)
    (h : (Ideal.absNorm I).Coprime (Ideal.absNorm J)) :
    IsRelPrime I J := by
  have hcast : IsCoprime ((Ideal.absNorm I : ℕ) : O)
      ((Ideal.absNorm J : ℕ) : O) := by
    simpa only [map_natCast] using
      (Nat.Coprime.isCoprime h).map (Int.castRingHom O)
  obtain ⟨a, b, hab⟩ := hcast
  apply IsCoprime.isRelPrime
  apply Ideal.isCoprime_iff_exists.mpr
  refine ⟨a * (Ideal.absNorm I : O),
    I.mul_mem_left a (Ideal.absNorm_mem I),
    b * (Ideal.absNorm J : O),
    J.mul_mem_left b (Ideal.absNorm_mem J), hab⟩

theorem baseChangeWeight_mul_of_coprime_norms {q : ℕ}
    (χ : DirichletCharacter ℂ q) (I J : Ideal O)
    (h : (Ideal.absNorm I).Coprime (Ideal.absNorm J)) :
    baseChangeWeight χ (I * J) =
      baseChangeWeight χ I * baseChangeWeight χ J := by
  have hrel := ideals_isRelPrime_of_norms_coprime I J h
  simp only [baseChangeWeight, map_mul, hrel.moebius_mul, Int.cast_mul, Nat.cast_mul]
  ring

theorem baseChangeChar_apply_of_coprime {q : ℕ}
    (χ : DirichletCharacter ℂ q) (n : ℕ)
    (h : n.Coprime (q * 3)) :
    baseChangeChar χ n = χ n * chiMinusThree n := by
  have hc : IsCoprime (n : ℤ) (q * 3 : ℕ) := by
    simpa [Int.isCoprime_iff_nat_coprime, Int.natAbs_mul] using h
  rw [baseChangeChar, MulChar.mul_apply]
  have hχ : χ.changeLevel (Nat.dvd_mul_right q 3) n = χ n := by
    simpa using (DirichletCharacter.changeLevel_eq_cast_of_dvd' χ
      (Nat.dvd_mul_right q 3) hc)
  have hη : chiMinusThree.changeLevel (Nat.dvd_mul_left 3 q) n =
      chiMinusThree n := by
    simpa using (DirichletCharacter.changeLevel_eq_cast_of_dvd' chiMinusThree
      (Nat.dvd_mul_left 3 q) hc)
  rw [hχ, hη]

theorem chiMinusThree_three : chiMinusThree (3 : ℕ) = 0 := by
  simpa using (DirichletCharacter.apply_eq_zero_iff chiMinusThree 3).mpr
    (by simp [Int.isCoprime_iff_nat_coprime])

theorem baseChangeChar_three {q : ℕ} (χ : DirichletCharacter ℂ q) :
    baseChangeChar χ (3 : ℕ) = 0 := by
  simpa using (DirichletCharacter.apply_eq_zero_iff (baseChangeChar χ) 3).mpr
    (by
      intro hc
      have hn : Nat.Coprime 3 (q * 3) := by
        simpa [Int.isCoprime_iff_nat_coprime, Int.natAbs_mul] using hc
      have hself : Nat.Coprime 3 3 := hn.of_dvd_right (Nat.dvd_mul_left 3 q)
      norm_num at hself)

private theorem orderOf_mod3_eq_one {p : ℕ} (h : p % 3 = 1) :
    orderOf (p : ZMod 3) = 1 := by
  have hc : (p : ZMod 3) = 1 :=
    (ZMod.natCast_eq_natCast_iff' p 1 3).2 (by simpa using h)
  simp [hc]

private theorem degree_two : Module.finrank ℚ K = 2 := by
  rw [IsCyclotomicExtension.Rat.finrank 3 K]
  decide

private theorem gal_card_two : Nat.card Gal(K/ℚ) = 2 := by
  rw [IsGaloisGroup.card_eq_finrank Gal(K/ℚ) ℚ K]
  exact degree_two

theorem split_count_of_mod_one {p : ℕ} (hp : p.Prime) (hmod : p % 3 = 1) :
    ((Ideal.span {(p : ℤ)}).primesOver O).ncard = 2 := by
  let : Fact p.Prime := ⟨hp⟩
  have hneq : p ≠ 3 := by
    intro heq
    subst p
    norm_num at hmod
  have hnd := not_dvd_three hp hneq
  have hmain := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
    (Ideal.span {(p : ℤ)}) O Gal(K/ℚ)
  rw [IsCyclotomicExtension.Rat.ramificationIdxIn_eq_of_not_dvd p K hnd,
    IsCyclotomicExtension.Rat.inertiaDegIn_eq_of_not_dvd p K hnd,
    orderOf_mod3_eq_one hmod, gal_card_two] at hmain
  omega

theorem inert_count_of_mod_two {p : ℕ} (hp : p.Prime) (hmod : p % 3 = 2) :
    ((Ideal.span {(p : ℤ)}).primesOver O).ncard = 1 := by
  let : Fact p.Prime := ⟨hp⟩
  have hneq : p ≠ 3 := by
    intro heq
    subst p
    norm_num at hmod
  have hnd := not_dvd_three hp hneq
  have hmain := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
    (Ideal.span {(p : ℤ)}) O Gal(K/ℚ)
  rw [IsCyclotomicExtension.Rat.ramificationIdxIn_eq_of_not_dvd p K hnd,
    IsCyclotomicExtension.Rat.inertiaDegIn_eq_of_not_dvd p K hnd,
    orderOf_mod3_eq_two hmod, gal_card_two] at hmain
  omega

theorem ramified_count :
    ((Ideal.span {(3 : ℤ)}).primesOver O).ncard = 1 := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  exact IsCyclotomicExtension.Rat.ncard_primesOver_of_prime 3 K

theorem absNorm_split {p : ℕ} (hp : p.Prime) (hmod : p % 3 = 1)
    (P : Ideal O) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})] :
    Ideal.absNorm P = p := by
  let : Fact p.Prime := ⟨hp⟩
  have hneq : p ≠ 3 := by
    intro heq
    subst p
    norm_num at hmod
  have hnd := not_dvd_three hp hneq
  have hf : P.inertiaDeg ℤ = 1 := by
    rw [← Ideal.inertiaDegIn_eq_inertiaDeg (Ideal.span {(p : ℤ)}) P Gal(K/ℚ),
      IsCyclotomicExtension.Rat.inertiaDegIn_eq_of_not_dvd p K hnd,
      orderOf_mod3_eq_one hmod]
  rw [← Ideal.pow_inertiaDeg p P, hf, pow_one]

theorem absNorm_ramified
    (P : Ideal O) [P.IsPrime] [P.LiesOver (Ideal.span {(3 : ℤ)})] :
    Ideal.absNorm P = 3 := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hfin : (Ideal.span {(3 : ℤ)}).inertiaDegIn O = 1 := by
    simpa using IsCyclotomicExtension.Rat.inertiaDegIn_eq_of_prime 3 K
  have hf : P.inertiaDeg ℤ = 1 := by
    rw [← Ideal.inertiaDegIn_eq_inertiaDeg (Ideal.span {(3 : ℤ)}) P Gal(K/ℚ)]
    exact hfin
  rw [← Ideal.pow_inertiaDeg 3 P, hf, pow_one]

theorem norm_p_fiber_split {p : ℕ} (hp : p.Prime) (hmod : p % 3 = 1) :
    {I : Ideal O | Ideal.absNorm I = p} =
      (Ideal.span {(p : ℤ)}).primesOver O := by
  ext I
  constructor
  · exact norm_prime_implies_over hp I
  · intro hI
    let : I.IsPrime := hI.1
    let : I.LiesOver (Ideal.span {(p : ℤ)}) := hI.2
    exact absNorm_split hp hmod I

theorem norm_three_fiber :
    {I : Ideal O | Ideal.absNorm I = 3} =
      (Ideal.span {(3 : ℤ)}).primesOver O := by
  ext I
  constructor
  · exact norm_prime_implies_over (by decide) I
  · intro hI
    let : I.IsPrime := hI.1
    let : I.LiesOver (Ideal.span {(3 : ℤ)}) := hI.2
    exact absNorm_ramified I

theorem norm_p_sq_fiber_inert {p : ℕ} (hp : p.Prime) (hmod : p % 3 = 2) :
    {I : Ideal O | Ideal.absNorm I = p ^ 2} =
      (Ideal.span {(p : ℤ)}).primesOver O := by
  ext I
  constructor
  · intro hI
    have hdiv : p ∣ Ideal.absNorm I := by
      rw [hI]
      exact dvd_pow_self p (by decide)
    obtain ⟨P, hPmax, hPunder, hPdiv⟩ :=
      Ideal.exists_isMaximal_dvd_of_dvd_absNorm' hp I hdiv
    have : P.IsPrime := hPmax.isPrime
    have : P.LiesOver (Ideal.span {(p : ℤ)}) := ⟨hPunder.symm⟩
    have hPN : Ideal.absNorm P = p ^ 2 := absNorm_inert hp hmod P
    obtain ⟨J, hIJ⟩ := hPdiv
    have hJN : Ideal.absNorm J = 1 := by
      have heq := congrArg Ideal.absNorm hIJ
      simp only [map_mul] at heq
      rw [hI, hPN] at heq
      have hp2 : 0 < p ^ 2 := pow_pos hp.pos 2
      nlinarith
    have hJtop : J = ⊤ := Ideal.absNorm_eq_one_iff.mp hJN
    subst J
    simp only [Ideal.mul_top] at hIJ
    subst I
    exact ⟨inferInstance, inferInstance⟩
  · intro hI
    let : I.IsPrime := hI.1
    let : I.LiesOver (Ideal.span {(p : ℤ)}) := hI.2
    exact absNorm_inert hp hmod I

theorem norm_p_sq_split_factors {p : ℕ} (hp : p.Prime) (hmod : p % 3 = 1)
    (I : Ideal O) (hI : Ideal.absNorm I = p ^ 2) :
    ∃ P Q : Ideal O,
      P ∈ (Ideal.span {(p : ℤ)}).primesOver O ∧
      Q ∈ (Ideal.span {(p : ℤ)}).primesOver O ∧
      I = P * Q := by
  have hdiv : p ∣ Ideal.absNorm I := by
    rw [hI]
    exact dvd_pow_self p (by decide)
  obtain ⟨P, hPmax, hPunder, hPdiv⟩ :=
    Ideal.exists_isMaximal_dvd_of_dvd_absNorm' hp I hdiv
  have : P.IsPrime := hPmax.isPrime
  have : P.LiesOver (Ideal.span {(p : ℤ)}) := ⟨hPunder.symm⟩
  have hPN : Ideal.absNorm P = p := absNorm_split hp hmod P
  obtain ⟨Q, hIQ⟩ := hPdiv
  have hQN : Ideal.absNorm Q = p := by
    have heq := congrArg Ideal.absNorm hIQ
    simp only [map_mul] at heq
    rw [hI, hPN] at heq
    have hppos := hp.pos
    nlinarith
  exact ⟨P, Q, ⟨inferInstance, inferInstance⟩,
    norm_prime_implies_over hp Q hQN, hIQ⟩

theorem norm_nine_fiber_ramified :
    {I : Ideal O | Ideal.absNorm I = 9} =
      {I : Ideal O | ∃ P : Ideal O,
        P ∈ (Ideal.span {(3 : ℤ)}).primesOver O ∧ I = P ^ 2} := by
  ext I
  constructor
  · intro hI
    have hdiv : 3 ∣ Ideal.absNorm I := by
      rw [hI]
      decide
    obtain ⟨P, hPmax, hPunder, hPdiv⟩ :=
      Ideal.exists_isMaximal_dvd_of_dvd_absNorm' (by decide : Nat.Prime 3) I hdiv
    have : P.IsPrime := hPmax.isPrime
    have : P.LiesOver (Ideal.span {(3 : ℤ)}) := ⟨hPunder.symm⟩
    have hPN : Ideal.absNorm P = 3 := absNorm_ramified P
    obtain ⟨Q, hIQ⟩ := hPdiv
    have hQN : Ideal.absNorm Q = 3 := by
      have heq := congrArg Ideal.absNorm hIQ
      simp only [map_mul] at heq
      rw [hI, hPN] at heq
      omega
    have hQover := norm_prime_implies_over (by decide : Nat.Prime 3) Q hQN
    have hPover : P ∈ (Ideal.span {(3 : ℤ)}).primesOver O :=
      ⟨inferInstance, inferInstance⟩
    have hfinite : ((Ideal.span {(3 : ℤ)}).primesOver O).Finite := by
      rw [← norm_three_fiber]
      exact Ideal.finite_setOfPred_absNorm_eq 3
    have hsub : ∀ {A B : Ideal O},
        A ∈ (Ideal.span {(3 : ℤ)}).primesOver O →
        B ∈ (Ideal.span {(3 : ℤ)}).primesOver O → A = B :=
      (Set.ncard_le_one_iff hfinite).mp (by rw [ramified_count])
    have hPQ : P = Q := hsub hPover hQover
    refine ⟨P, hPover, ?_⟩
    rw [hIQ, ← hPQ, pow_two]
  · rintro ⟨P, hP, rfl⟩
    have : P.IsPrime := hP.1
    have : P.LiesOver (Ideal.span {(3 : ℤ)}) := hP.2
    change Ideal.absNorm (P ^ 2) = 9
    rw [map_pow, absNorm_ramified P]
    norm_num

theorem local_inert_p {q : ℕ} (χ : DirichletCharacter ℂ q)
    {p : ℕ} (hp : p.Prime) (hmod : p % 3 = 2) :
    normFiberCoeff (baseChangeWeight χ) p = 0 := by
  have hf := norm_p_fiber_inert hp hmod
  unfold normFiberCoeff
  simp [hf]

theorem local_split_p {q : ℕ} (χ : DirichletCharacter ℂ q)
    {p : ℕ} (hp : p.Prime) (hmod : p % 3 = 1) :
    normFiberCoeff (baseChangeWeight χ) p = -(2 : ℂ) * χ p := by
  classical
  let hf := Ideal.finite_setOfPred_absNorm_eq (S := O) p
  have hcard : hf.toFinset.card = 2 := by
    rw [← Set.ncard_eq_toFinset_card {I : Ideal O | Ideal.absNorm I = p} hf]
    rw [norm_p_fiber_split hp hmod]
    exact split_count_of_mod_one hp hmod
  have hsum : normFiberCoeff (baseChangeWeight χ) p =
      ∑ I ∈ hf.toFinset, -χ p := by
    unfold normFiberCoeff
    apply Finset.sum_congr rfl
    intro I hI
    have hnorm : Ideal.absNorm I = p := hf.mem_toFinset.mp hI
    have hprime : Prime I :=
      UniqueFactorizationMonoid.irreducible_iff_prime.mp
        (Ideal.irreducible_of_irreducible_absNorm (by
          rw [hnorm]
          exact (Nat.irreducible_iff_nat_prime p).2 hp))
    rw [baseChangeWeight_prime χ I hprime, hnorm]
  rw [hsum]
  simp [hcard]

theorem local_ramified_three {q : ℕ} (χ : DirichletCharacter ℂ q) :
    normFiberCoeff (baseChangeWeight χ) 3 = -χ 3 := by
  classical
  let hf := Ideal.finite_setOfPred_absNorm_eq (S := O) 3
  have hcard : hf.toFinset.card = 1 := by
    rw [← Set.ncard_eq_toFinset_card {I : Ideal O | Ideal.absNorm I = 3} hf]
    rw [norm_three_fiber]
    exact ramified_count
  have hsum : normFiberCoeff (baseChangeWeight χ) 3 =
      ∑ I ∈ hf.toFinset, -χ 3 := by
    unfold normFiberCoeff
    apply Finset.sum_congr rfl
    intro I hI
    have hnorm : Ideal.absNorm I = 3 := hf.mem_toFinset.mp hI
    have hprime : Prime I :=
      UniqueFactorizationMonoid.irreducible_iff_prime.mp
        (Ideal.irreducible_of_irreducible_absNorm (by
          rw [hnorm]
          exact (Nat.irreducible_iff_nat_prime 3).2 (by decide)))
    simpa only [hnorm, Nat.cast_ofNat] using baseChangeWeight_prime χ I hprime
  rw [hsum]
  simp [hcard]

theorem local_inert_p_sq {q : ℕ} (χ : DirichletCharacter ℂ q)
    {p : ℕ} (hp : p.Prime) (hmod : p % 3 = 2) :
    normFiberCoeff (baseChangeWeight χ) (p ^ 2) = -χ (p ^ 2) := by
  classical
  let hf := Ideal.finite_setOfPred_absNorm_eq (S := O) (p ^ 2)
  have hcard : hf.toFinset.card = 1 := by
    rw [← Set.ncard_eq_toFinset_card {I : Ideal O | Ideal.absNorm I = p ^ 2} hf]
    rw [norm_p_sq_fiber_inert hp hmod]
    exact inert_count_of_mod_two hp hmod
  have hsum : normFiberCoeff (baseChangeWeight χ) (p ^ 2) =
      ∑ I ∈ hf.toFinset, -χ (p ^ 2) := by
    unfold normFiberCoeff
    apply Finset.sum_congr rfl
    intro I hI
    have hover : I ∈ (Ideal.span {(p : ℤ)}).primesOver O := by
      rw [← norm_p_sq_fiber_inert hp hmod]
      exact hf.mem_toFinset.mp hI
    have hnorm : Ideal.absNorm I = p ^ 2 := hf.mem_toFinset.mp hI
    let : I.IsPrime := hover.1
    have hprime : Prime I := Ideal.prime_of_isPrime (by
      intro hbot
      have : Ideal.absNorm I = 0 := by rw [hbot]; simp
      rw [hnorm] at this
      exact (pow_ne_zero 2 hp.ne_zero) this) inferInstance
    simpa only [hnorm, Nat.cast_pow] using baseChangeWeight_prime χ I hprime
  rw [hsum]
  simp [hcard]

theorem local_ramified_nine {q : ℕ} (χ : DirichletCharacter ℂ q) :
    normFiberCoeff (baseChangeWeight χ) 9 = 0 := by
  classical
  let hf := Ideal.finite_setOfPred_absNorm_eq (S := O) 9
  unfold normFiberCoeff
  apply Finset.sum_eq_zero
  intro I hI
  have hnorm : Ideal.absNorm I = 9 := hf.mem_toFinset.mp hI
  have hfactor : I ∈ {I : Ideal O | ∃ P : Ideal O,
      P ∈ (Ideal.span {(3 : ℤ)}).primesOver O ∧ I = P ^ 2} := by
    rw [← norm_nine_fiber_ramified]
    exact hnorm
  obtain ⟨P, hP, rfl⟩ := hfactor
  have : P.IsPrime := hP.1
  have : P.LiesOver (Ideal.span {(3 : ℤ)}) := hP.2
  have hPN : Ideal.absNorm P = 3 := absNorm_ramified P
  have hnotunit : ¬ IsUnit P := by
    intro hunit
    have htop : P = ⊤ := Ideal.isUnit_iff.mp hunit
    rw [htop, Ideal.absNorm_top] at hPN
    norm_num at hPN
  have hnot : ¬ Squarefree (P ^ 2) := by
    intro hsq
    apply hnotunit
    exact hsq P (by rw [pow_two])
  rw [baseChangeWeight, UniqueFactorizationMonoid.moebius_of_not_squarefree hnot]
  simp

private theorem baseChangeWeight_prime_sq_zero {q : ℕ} (χ : DirichletCharacter ℂ q)
    (P : Ideal O) (hP : Prime P) :
    baseChangeWeight χ (P ^ 2) = 0 := by
  have hnot : ¬ Squarefree (P ^ 2) := by
    intro hsq
    have hunit : IsUnit P := hsq P (by rw [pow_two])
    exact hP.irreducible.not_isUnit hunit
  rw [baseChangeWeight, UniqueFactorizationMonoid.moebius_of_not_squarefree hnot]
  simp

theorem local_split_p_sq {q : ℕ} (χ : DirichletCharacter ℂ q)
    {p : ℕ} (hp : p.Prime) (hmod : p % 3 = 1) :
    normFiberCoeff (baseChangeWeight χ) (p ^ 2) = χ (p ^ 2) := by
  classical
  let s : Set (Ideal O) := (Ideal.span {(p : ℤ)}).primesOver O
  obtain ⟨P, Q, hPQ, hset⟩ := Set.ncard_eq_two.mp (split_count_of_mod_one hp hmod)
  have hPover : P ∈ s := by
    change P ∈ (Ideal.span {(p : ℤ)}).primesOver O
    rw [hset]
    simp
  have hQover : Q ∈ s := by
    change Q ∈ (Ideal.span {(p : ℤ)}).primesOver O
    rw [hset]
    simp
  let : P.IsPrime := hPover.1
  let : P.LiesOver (Ideal.span {(p : ℤ)}) := hPover.2
  let : Q.IsPrime := hQover.1
  let : Q.LiesOver (Ideal.span {(p : ℤ)}) := hQover.2
  have hPN : Ideal.absNorm P = p := absNorm_split hp hmod P
  have hQN : Ideal.absNorm Q = p := absNorm_split hp hmod Q
  have hPne : P ≠ ⊥ := by
    intro h
    rw [h, Ideal.absNorm_bot] at hPN
    exact hp.ne_zero hPN.symm
  have hQne : Q ≠ ⊥ := by
    intro h
    rw [h, Ideal.absNorm_bot] at hQN
    exact hp.ne_zero hQN.symm
  have hPprime : Prime P := Ideal.prime_of_isPrime hPne inferInstance
  have hQprime : Prime Q := Ideal.prime_of_isPrime hQne inferInstance
  have : P.IsMaximal := (inferInstance : P.IsPrime).isMaximal hPne
  have : Q.IsMaximal := (inferInstance : Q.IsPrime).isMaximal hQne
  have hrel : IsRelPrime P Q := (Ideal.isCoprime_of_isMaximal hPQ).isRelPrime
  have hmu : UniqueFactorizationMonoid.moebius (P * Q) = 1 := by
    rw [hrel.moebius_mul, hPprime.irreducible.moebius_eq,
      hQprime.irreducible.moebius_eq]
    norm_num
  let hf := Ideal.finite_setOfPred_absNorm_eq (S := O) (p ^ 2)
  have hmem : P * Q ∈ hf.toFinset := by
    rw [hf.mem_toFinset]
    change Ideal.absNorm (P * Q) = p ^ 2
    rw [map_mul, hPN, hQN, pow_two]
  calc
    normFiberCoeff (baseChangeWeight χ) (p ^ 2) =
        ∑ I ∈ hf.toFinset, baseChangeWeight χ I := by rfl
    _ = baseChangeWeight χ (P * Q) := by
      apply Finset.sum_eq_single (P * Q)
      · intro I hImem hneq
        have hnorm : Ideal.absNorm I = p ^ 2 := hf.mem_toFinset.mp hImem
        obtain ⟨A, B, hA, hB, rfl⟩ := norm_p_sq_split_factors hp hmod I hnorm
        rw [hset] at hA hB
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hA hB
        rcases hA with hAP | hAQ <;> rcases hB with hBP | hBQ
        · rw [hAP, hBP]
          simpa only [pow_two] using baseChangeWeight_prime_sq_zero χ P hPprime
        · exact False.elim (hneq (by rw [hAP, hBQ]))
        · exact False.elim (hneq (by rw [hAQ, hBP, mul_comm]))
        · rw [hAQ, hBQ]
          simpa only [pow_two] using baseChangeWeight_prime_sq_zero χ Q hQprime
      · intro hnot
        exact False.elim (hnot hmem)
    _ = χ (p ^ 2) := by
      rw [baseChangeWeight, hmu]
      have hnorm : Ideal.absNorm (P * Q) = p ^ 2 := by
        rw [map_mul, hPN, hQN, pow_two]
      simp [hnorm, Nat.cast_pow]

end ShortDraftHeckeBridge

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.LocalEulerIdentities
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology

namespace ShortDraftHeckeBridge

theorem chiMinusThree_mod_one (n : ℕ) (h : n % 3 = 1) :
    chiMinusThree n = 1 := by
  have hc : (n : ZMod 3) = 1 := by
    calc
      (n : ZMod 3) = ((n % 3 : ℕ) : ZMod 3) := by simp
      _ = 1 := by rw [h]; simp
  change ((quadraticChar (ZMod 3) (n : ZMod 3) : ℤ) : ℂ) = 1
  rw [hc]
  simp

theorem chiMinusThree_mod_two (n : ℕ) (h : n % 3 = 2) :
    chiMinusThree n = -1 := by
  have hc : (n : ZMod 3) = 2 := by
    calc
      (n : ZMod 3) = ((n % 3 : ℕ) : ZMod 3) := by simp
      _ = 2 := by rw [h]; simp
  change ((quadraticChar (ZMod 3) (n : ZMod 3) : ℤ) : ℂ) = -1
  rw [hc]
  change chiMinusThree (2 : ℕ) = -1
  exact chiMinusThree_two

private theorem invCharAF_prime_pow_ge_two {q : ℕ}
    (χ : DirichletCharacter ℂ q) {p j : ℕ} (hp : p.Prime) (hj : 2 ≤ j) :
    invCharAF χ (p ^ j) = 0 := by
  rw [invCharAF_apply χ (pow_ne_zero j hp.ne_zero),
    ArithmeticFunction.moebius_apply_prime_pow hp (by omega)]
  simp [show j ≠ 1 by omega]

theorem pairAF_prime_pow_ge_three {q r : ℕ}
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r)
    {p k : ℕ} (hp : p.Prime) (hk : 3 ≤ k) :
    pairAF χ ψ (p ^ k) = 0 := by
  rw [pairAF, ArithmeticFunction.mul_apply]
  conv_lhs => rw [Nat.sum_divisorsAntidiagonal
    (fun a b => invCharAF χ a * invCharAF ψ b)]
  rw [Nat.sum_divisors_prime_pow hp]
  apply Finset.sum_eq_zero
  intro i hi
  have hik : i ≤ k := by
    simpa only [Finset.mem_range, Nat.lt_succ_iff] using hi
  have hdiv : p ^ k / p ^ i = p ^ (k - i) := by
    have heq : k - i + i = k := Nat.sub_add_cancel hik
    calc
      p ^ k / p ^ i = (p ^ (k - i) * p ^ i) / p ^ i := by rw [← pow_add, heq]
      _ = p ^ (k - i) := by simp [hp.ne_zero]
  rw [hdiv]
  by_cases hii : 2 ≤ i
  · rw [invCharAF_prime_pow_ge_two χ hp hii, zero_mul]
  · have hki : 2 ≤ k - i := by omega
    rw [invCharAF_prime_pow_ge_two ψ hp hki, mul_zero]

private theorem base_ring_rank_two : Module.finrank ℤ O = 2 := by
  rw [NumberField.RingOfIntegers.rank ActualEisensteinSieve.K,
    IsCyclotomicExtension.Rat.finrank 3 ActualEisensteinSieve.K]
  decide

theorem baseChangeWeight_zero_of_norm_prime_pow_ge_three {q p k : ℕ}
    (χ : DirichletCharacter ℂ q) (hp : p.Prime) (hk : 3 ≤ k)
    (I : Ideal O) (hI : Ideal.absNorm I = p ^ k) :
    baseChangeWeight χ I = 0 := by
  by_cases hμ : UniqueFactorizationMonoid.moebius I = 0
  · simp [baseChangeWeight, hμ]
  have hsq : Squarefree I := by
    by_contra hnsq
    exact hμ (UniqueFactorizationMonoid.moebius_of_not_squarefree hnsq)
  have hmem : ((p ^ k : ℕ) : O) ∈ I := by
    simpa only [hI] using Ideal.absNorm_mem I
  have hspanle : Ideal.span {((p : O) ^ k)} ≤ I :=
    (Ideal.span_singleton_le_iff_mem I).mpr (by simpa using hmem)
  have hpowdiv : I ∣ (Ideal.span {(p : O)}) ^ k := by
    rw [Ideal.span_singleton_pow]
    exact Ideal.dvd_iff_le.mpr hspanle
  have hdiv : I ∣ Ideal.span {(p : O)} :=
    (hsq.dvd_pow_iff_dvd (by omega : k ≠ 0)).mp hpowdiv
  have hnormdiv := map_dvd Ideal.absNorm hdiv
  rw [hI, Ideal.absNorm_span_natCast, base_ring_rank_two] at hnormdiv
  have hk2 : k ≤ 2 := (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp hnormdiv
  omega

theorem normFiberCoeff_baseChangeWeight_prime_pow_ge_three {q p k : ℕ}
    (χ : DirichletCharacter ℂ q) (hp : p.Prime) (hk : 3 ≤ k) :
    normFiberCoeff (baseChangeWeight χ) (p ^ k) = 0 := by
  classical
  unfold normFiberCoeff
  apply Finset.sum_eq_zero
  intro I hI
  have hnorm : Ideal.absNorm I = p ^ k := by simpa using hI
  exact baseChangeWeight_zero_of_norm_prime_pow_ge_three χ hp hk I hnorm

theorem normFiberCoeff_eq_pairAF_prime_pow_ge_three {q p k : ℕ}
    (χ : DirichletCharacter ℂ q) (hp : p.Prime) (hk : 3 ≤ k) :
    normFiberCoeff (baseChangeWeight χ) (p ^ k) =
      pairAF χ (baseChangeChar χ) (p ^ k) := by
  rw [normFiberCoeff_baseChangeWeight_prime_pow_ge_three χ hp hk,
    pairAF_prime_pow_ge_three χ (baseChangeChar χ) hp hk]

theorem char_prime_zero_of_dvd_level {q p : ℕ}
    (χ : DirichletCharacter ℂ q) (hp : p.Prime) (hd : p ∣ q) :
    χ p = 0 := by
  have hnot : ¬ IsCoprime (p : ℤ) (q : ℕ) := by
    intro hc
    have hn : p.Coprime q := by
      simpa [Int.isCoprime_iff_nat_coprime] using hc
    exact (hp.coprime_iff_not_dvd.mp hn) hd
  simpa using (DirichletCharacter.apply_eq_zero_iff χ (p : ℤ)).mpr hnot

theorem baseChangeChar_prime_zero_of_dvd_q {q p : ℕ}
    (χ : DirichletCharacter ℂ q) (hp : p.Prime) (hd : p ∣ q) :
    baseChangeChar χ p = 0 := by
  have hd' : p ∣ q * 3 := dvd_mul_of_dvd_left hd 3
  exact char_prime_zero_of_dvd_level (baseChangeChar χ) hp hd'

end ShortDraftHeckeBridge

namespace NormSplitArithmetic

theorem eq_parts_of_coprime_square_bounds {a b m n : ℕ}
    (hcop : m.Coprime n) (ha2 : a ∣ m ^ 2) (hb2 : b ∣ n ^ 2)
    (hprod : a * b = m * n) : a = m ∧ b = n := by
  have hm2n : (m ^ 2).Coprime n :=
    (Nat.coprime_pow_left_iff (by decide) m n).mpr hcop
  have hmn2 : m.Coprime (n ^ 2) :=
    (Nat.coprime_pow_right_iff (by decide) m n).mpr hcop
  have han : a.Coprime n := hm2n.coprime_dvd_left ha2
  have hmb : m.Coprime b := hmn2.coprime_dvd_right hb2
  have ha_mn : a ∣ m * n := ⟨b, hprod.symm⟩
  have hm_ab : m ∣ a * b := ⟨n, hprod⟩
  have hn_ab : n ∣ a * b := ⟨m, by rw [hprod, mul_comm]⟩
  have ha_m : a ∣ m := han.dvd_of_dvd_mul_right ha_mn
  have hm_a : m ∣ a := hmb.dvd_of_dvd_mul_right hm_ab
  have hb_n : b ∣ n := by
    have hbn : b.Coprime m := (hmn2.symm).coprime_dvd_left hb2
    have hb_mn : b ∣ n * m := ⟨a, by
      calc
        n * m = m * n := mul_comm n m
        _ = a * b := hprod.symm
        _ = b * a := mul_comm a b⟩
    exact hbn.dvd_of_dvd_mul_right hb_mn
  have hn_b : n ∣ b := han.symm.dvd_of_dvd_mul_left hn_ab
  exact ⟨Nat.dvd_antisymm ha_m hm_a, Nat.dvd_antisymm hb_n hn_b⟩

end NormSplitArithmetic

namespace NormFiberCRT

private theorem ring_rank_two : Module.finrank ℤ O = 2 := by
  rw [NumberField.RingOfIntegers.rank K,
    IsCyclotomicExtension.Rat.finrank 3 K]
  decide

theorem ideal_eq_factors (I : Ideal O) (m n : ℕ)
    (hcop : m.Coprime n) (hI : Ideal.absNorm I = m * n) :
    I = (I ⊔ Ideal.span {(m : O)}) * (I ⊔ Ideal.span {(n : O)}) := by
  let A : Ideal O := Ideal.span {(m : O)}
  let B : Ideal O := Ideal.span {(n : O)}
  have hcast : IsCoprime (m : O) (n : O) := by
    simpa only [map_natCast] using
      (Nat.Coprime.isCoprime hcop).map (Int.castRingHom O)
  have hAB : A ⊔ B = ⊤ := by
    exact Ideal.isCoprime_iff_sup_eq.mp
      ((Ideal.isCoprime_span_singleton_iff (m : O) (n : O)).mpr hcast)
  have hmnmem : ((m * n : ℕ) : O) ∈ I := by
    simpa only [hI] using Ideal.absNorm_mem I
  have hABle : A * B ≤ I := by
    change Ideal.span {(m : O)} * Ideal.span {(n : O)} ≤ I
    rw [Ideal.span_singleton_mul_span_singleton]
    exact (Ideal.span_singleton_le_iff_mem I).mpr (by simpa using hmnmem)
  have hJcop : (I ⊔ A) ⊔ (I ⊔ B) = ⊤ := by
    calc
      (I ⊔ A) ⊔ (I ⊔ B) = I ⊔ (A ⊔ B) := by ac_rfl
      _ = ⊤ := by rw [hAB, sup_top_eq]
  apply le_antisymm
  · rw [Ideal.mul_eq_inf_of_coprime hJcop]
    exact le_inf le_sup_left le_sup_left
  · rw [Ideal.sup_mul, Ideal.mul_sup, Ideal.mul_sup]
    exact sup_le (sup_le Ideal.mul_le_left Ideal.mul_le_left)
      (sup_le Ideal.mul_le_right hABle)

theorem ideal_factor_norms (I : Ideal O) (m n : ℕ)
    (hcop : m.Coprime n) (hI : Ideal.absNorm I = m * n) :
    Ideal.absNorm (I ⊔ Ideal.span {(m : O)}) = m ∧
      Ideal.absNorm (I ⊔ Ideal.span {(n : O)}) = n := by
  have hAm : Ideal.absNorm (Ideal.span {(m : O)}) = m ^ 2 := by
    rw [Ideal.absNorm_span_natCast, ring_rank_two]
  have hBn : Ideal.absNorm (Ideal.span {(n : O)}) = n ^ 2 := by
    rw [Ideal.absNorm_span_natCast, ring_rank_two]
  have hmdiv : Ideal.absNorm (I ⊔ Ideal.span {(m : O)}) ∣ m ^ 2 := by
    rw [← hAm]
    exact Ideal.absNorm_dvd_absNorm_of_le le_sup_right
  have hndiv : Ideal.absNorm (I ⊔ Ideal.span {(n : O)}) ∣ n ^ 2 := by
    rw [← hBn]
    exact Ideal.absNorm_dvd_absNorm_of_le le_sup_right
  have hprod := congrArg Ideal.absNorm (ideal_eq_factors I m n hcop hI)
  rw [map_mul, hI] at hprod
  exact NormSplitArithmetic.eq_parts_of_coprime_square_bounds hcop hmdiv hndiv hprod.symm

end NormFiberCRT

namespace NormFiberMult

private theorem ideal_sup_span_norm_left (I J : Ideal O) (m n : ℕ)
    (hcop : m.Coprime n) (hI : Ideal.absNorm I = m)
    (hJ : Ideal.absNorm J = n) :
    I * J ⊔ Ideal.span {(m : O)} = I := by
  let A : Ideal O := Ideal.span {(m : O)}
  have hmI : A ≤ I := by
    apply (Ideal.span_singleton_le_iff_mem _).mpr
    simpa only [hI] using Ideal.absNorm_mem I
  have hnJ : (n : O) ∈ J := by
    simpa only [hJ] using Ideal.absNorm_mem J
  have hnspan : Ideal.span {(n : O)} ≤ J :=
    (Ideal.span_singleton_le_iff_mem _).mpr hnJ
  have hcast : IsCoprime (m : O) (n : O) := by
    simpa only [map_natCast] using
      (Nat.Coprime.isCoprime hcop).map (Int.castRingHom O)
  have hAB : A ⊔ Ideal.span {(n : O)} = ⊤ := by
    exact Ideal.isCoprime_iff_sup_eq.mp
      ((Ideal.isCoprime_span_singleton_iff (m : O) (n : O)).mpr hcast)
  have hJA : J ⊔ A = ⊤ := by
    apply top_unique
    calc
      ⊤ = A ⊔ Ideal.span {(n : O)} := hAB.symm
      _ ≤ J ⊔ A := sup_le le_sup_right (hnspan.trans le_sup_left)
  apply le_antisymm
  · exact sup_le Ideal.mul_le_left hmI
  · calc
      I = I * (J ⊔ A) := by rw [hJA]; simp
      _ = I * J ⊔ I * A := by rw [Ideal.mul_sup]
      _ ≤ I * J ⊔ A := sup_le le_sup_left
        (Ideal.mul_le_right.trans le_sup_right)

private theorem ideal_sup_span_norm_right (I J : Ideal O) (m n : ℕ)
    (hcop : m.Coprime n) (hI : Ideal.absNorm I = m)
    (hJ : Ideal.absNorm J = n) :
    I * J ⊔ Ideal.span {(n : O)} = J := by
  simpa only [mul_comm] using
    ideal_sup_span_norm_left J I n m hcop.symm hJ hI

theorem weighted_norm_fiber_mul (weight : Ideal O → ℂ)
    (hweight : ∀ I J : Ideal O,
      (Ideal.absNorm I).Coprime (Ideal.absNorm J) →
      weight (I * J) = weight I * weight J)
    (m n : ℕ) (hcop : m.Coprime n) :
    (∑ K ∈ (Ideal.finite_setOfPred_absNorm_eq (S := O) (m * n)).toFinset,
       weight K) =
    (∑ I ∈ (Ideal.finite_setOfPred_absNorm_eq (S := O) m).toFinset,
       weight I) *
    (∑ J ∈ (Ideal.finite_setOfPred_absNorm_eq (S := O) n).toFinset,
       weight J) := by
  let F (k : ℕ) : Finset (Ideal O) :=
    (Ideal.finite_setOfPred_absNorm_eq (S := O) k).toFinset
  have hmem (k : ℕ) (I : Ideal O) : I ∈ F k ↔ Ideal.absNorm I = k := by
    simp [F]
  change (∑ K ∈ F (m * n), weight K) =
    (∑ I ∈ F m, weight I) * (∑ J ∈ F n, weight J)
  calc
    (∑ K ∈ F (m * n), weight K) =
        ∑ p ∈ (F m).product (F n), weight (p.1 * p.2) := by
      refine Finset.sum_bij'
        (fun K _ => (K ⊔ Ideal.span {(m : O)},
                     K ⊔ Ideal.span {(n : O)}))
        (fun p _ => p.1 * p.2) ?_ ?_ ?_ ?_ ?_
      · intro K hK
        have hKnorm : Ideal.absNorm K = m * n := (hmem _ _).mp hK
        obtain ⟨hm, hn⟩ := NormFiberCRT.ideal_factor_norms K m n hcop hKnorm
        simp [Finset.mem_product, hmem, hm, hn]
      · intro p hp
        have hm : Ideal.absNorm p.1 = m := (hmem _ _).mp (Finset.mem_product.mp hp).1
        have hn : Ideal.absNorm p.2 = n := (hmem _ _).mp (Finset.mem_product.mp hp).2
        exact (hmem _ _).mpr (by rw [map_mul, hm, hn])
      · intro K hK
        exact (NormFiberCRT.ideal_eq_factors K m n hcop ((hmem _ _).mp hK)).symm
      · intro p hp
        have hm : Ideal.absNorm p.1 = m := (hmem _ _).mp (Finset.mem_product.mp hp).1
        have hn : Ideal.absNorm p.2 = n := (hmem _ _).mp (Finset.mem_product.mp hp).2
        apply Prod.ext
        · exact ideal_sup_span_norm_left p.1 p.2 m n hcop hm hn
        · exact ideal_sup_span_norm_right p.1 p.2 m n hcop hm hn
      · intro K hK
        exact congrArg weight
          (NormFiberCRT.ideal_eq_factors K m n hcop ((hmem _ _).mp hK))
    _ = ∑ p ∈ (F m).product (F n), weight p.1 * weight p.2 := by
      apply Finset.sum_congr rfl
      intro p hp
      have hm : Ideal.absNorm p.1 = m := (hmem _ _).mp (Finset.mem_product.mp hp).1
      have hn : Ideal.absNorm p.2 = n := (hmem _ _).mp (Finset.mem_product.mp hp).2
      exact hweight p.1 p.2 (by simpa [hm, hn] using hcop)
    _ = (∑ I ∈ F m, weight I) * (∑ J ∈ F n, weight J) := by
      calc
        (∑ p ∈ (F m).product (F n), weight p.1 * weight p.2) =
            ∑ I ∈ F m, ∑ J ∈ F n, weight I * weight J := by
          exact Finset.sum_product' (F m) (F n) (fun I J => weight I * weight J)
        _ = (∑ I ∈ F m, weight I) * (∑ J ∈ F n, weight J) := by
          simp only [← Finset.mul_sum, ← Finset.sum_mul]

end NormFiberMult

namespace ShortDraftHeckeBridge

theorem baseChange_normFiber_mul {q : ℕ}
    (χ : DirichletCharacter ℂ q) (m n : ℕ) (hcop : m.Coprime n) :
    normFiberCoeff (baseChangeWeight χ) (m * n) =
      normFiberCoeff (baseChangeWeight χ) m *
        normFiberCoeff (baseChangeWeight χ) n := by
  exact NormFiberMult.weighted_norm_fiber_mul (baseChangeWeight χ)
    (fun I J h => baseChangeWeight_mul_of_coprime_norms χ I J h) m n hcop

theorem normFiberCoeff_baseChangeWeight_one {q : ℕ}
    (χ : DirichletCharacter ℂ q) :
    normFiberCoeff (baseChangeWeight χ) 1 = 1 := by
  have hsingle :
      (Ideal.finite_setOfPred_absNorm_eq (S := O) 1).toFinset = {⊤} := by
    ext I
    simp [Ideal.absNorm_eq_one_iff]
  unfold normFiberCoeff
  rw [hsingle]
  simp [baseChangeWeight, ← Ideal.one_eq_top]

theorem baseChange_normFiber_isMultiplicative {q : ℕ}
    (χ : DirichletCharacter ℂ q) :
    (toArithmeticFunction (normFiberCoeff (baseChangeWeight χ))).IsMultiplicative := by
  constructor
  · simp [toArithmeticFunction, normFiberCoeff_baseChangeWeight_one]
  · intro m n hcop
    by_cases hm : m = 0
    · simp [hm, toArithmeticFunction]
    by_cases hn : n = 0
    · simp [hn, toArithmeticFunction]
    simpa [toArithmeticFunction, hm, hn, mul_ne_zero hm hn] using
      baseChange_normFiber_mul χ m n hcop

theorem baseChangeChar_prime_apply {q p : ℕ}
    (χ : DirichletCharacter ℂ q) (hp : p.Prime) :
    baseChangeChar χ p = χ p * chiMinusThree p := by
  by_cases hq : p ∣ q
  · rw [baseChangeChar_prime_zero_of_dvd_q χ hp hq,
      char_prime_zero_of_dvd_level χ hp hq, zero_mul]
  by_cases h3 : p = 3
  · subst p
    rw [baseChangeChar_three, chiMinusThree_three, mul_zero]
  have hn3 : ¬p ∣ 3 := by
    intro hd
    rcases (Nat.dvd_prime (by decide : Nat.Prime 3)).1 hd with h1 | h3'
    · exact hp.ne_one h1
    · exact h3 h3'
  have hnot : ¬p ∣ q * 3 := by
    intro hd
    rcases hp.dvd_mul.mp hd with hq' | h3'
    · exact hq hq'
    · exact hn3 h3'
  exact baseChangeChar_apply_of_coprime χ p
    (hp.coprime_iff_not_dvd.mpr hnot)

theorem normFiberCoeff_eq_pairAF_prime {q p : ℕ}
    (χ : DirichletCharacter ℂ q) (hp : p.Prime) :
    normFiberCoeff (baseChangeWeight χ) p =
      pairAF χ (baseChangeChar χ) p := by
  have hlt : p % 3 < 3 := Nat.mod_lt p (by decide)
  have hcase : p % 3 = 0 ∨ p % 3 = 1 ∨ p % 3 = 2 := by omega
  rcases hcase with h0 | h1 | h2
  · have hdiv : 3 ∣ p := Nat.dvd_of_mod_eq_zero h0
    have heq : p = 3 := by
      rcases (Nat.dvd_prime hp).1 hdiv with h1' | h3
      · norm_num at h1'
      · exact h3.symm
    subst p
    rw [local_ramified_three χ,
      pairAF_prime χ (baseChangeChar χ) (by decide),
      baseChangeChar_three χ]
    ring_nf
  · rw [local_split_p χ hp h1, pairAF_prime χ (baseChangeChar χ) hp,
      baseChangeChar_prime_apply χ hp, chiMinusThree_mod_one p h1]
    ring
  · rw [local_inert_p χ hp h2, pairAF_prime χ (baseChangeChar χ) hp,
      baseChangeChar_prime_apply χ hp, chiMinusThree_mod_two p h2]
    ring

theorem normFiberCoeff_eq_pairAF_prime_sq {q p : ℕ}
    (χ : DirichletCharacter ℂ q) (hp : p.Prime) :
    normFiberCoeff (baseChangeWeight χ) (p ^ 2) =
      pairAF χ (baseChangeChar χ) (p ^ 2) := by
  have hlt : p % 3 < 3 := Nat.mod_lt p (by decide)
  have hcase : p % 3 = 0 ∨ p % 3 = 1 ∨ p % 3 = 2 := by omega
  rcases hcase with h0 | h1 | h2
  · have hdiv : 3 ∣ p := Nat.dvd_of_mod_eq_zero h0
    have heq : p = 3 := by
      rcases (Nat.dvd_prime hp).1 hdiv with h1' | h3
      · norm_num at h1'
      · exact h3.symm
    subst p
    have h3 : pairAF χ (baseChangeChar χ) 9 =
        χ (3 : ℕ) * baseChangeChar χ (3 : ℕ) := by
      simpa only [show (3 : ℕ) ^ 2 = 9 by norm_num] using
        (pairAF_prime_sq χ (baseChangeChar χ) (by decide : Nat.Prime 3))
    rw [show (3 : ℕ) ^ 2 = 9 by norm_num, local_ramified_nine χ,
      h3, baseChangeChar_three χ]
    ring
  · rw [local_split_p_sq χ hp h1, pairAF_prime_sq χ (baseChangeChar χ) hp,
      baseChangeChar_prime_apply χ hp, chiMinusThree_mod_one p h1]
    simp only [map_pow]
    ring
  · rw [local_inert_p_sq χ hp h2, pairAF_prime_sq χ (baseChangeChar χ) hp,
      baseChangeChar_prime_apply χ hp, chiMinusThree_mod_two p h2]
    simp only [map_pow]
    ring

theorem normFiberCoeff_eq_pairInverseCoeff_of_local
    {q : ℕ} (χ : DirichletCharacter ℂ q)
    (hprime : ∀ p : ℕ, p.Prime →
      normFiberCoeff (baseChangeWeight χ) p = pairAF χ (baseChangeChar χ) p)
    (hprimeSq : ∀ p : ℕ, p.Prime →
      normFiberCoeff (baseChangeWeight χ) (p ^ 2) =
        pairAF χ (baseChangeChar χ) (p ^ 2))
    (n : ℕ) (hn : n ≠ 0) :
    normFiberCoeff (baseChangeWeight χ) n =
      pairInverseCoeff χ (baseChangeChar χ) n := by
  apply normFiber_eq_pair_of_prime_powers χ (baseChangeChar χ)
    (baseChangeWeight χ) (baseChange_normFiber_isMultiplicative χ) ?_ n hn
  intro p k hp
  by_cases hk0 : k = 0
  · simpa [hk0] using
      (baseChange_normFiber_isMultiplicative χ).map_one.trans
        ((pairAF_mult χ (baseChangeChar χ)).map_one).symm
  by_cases hk1 : k = 1
  · simpa [hk1, toArithmeticFunction, hp.ne_zero] using hprime p hp
  by_cases hk2 : k = 2
  · simpa [hk2, toArithmeticFunction, hp.ne_zero] using hprimeSq p hp
  have hk3 : 3 ≤ k := by omega
  change (if p ^ k = 0 then (0 : ℂ) else
    normFiberCoeff (baseChangeWeight χ) (p ^ k)) = _
  rw [if_neg (pow_ne_zero k hp.ne_zero)]
  exact normFiberCoeff_eq_pairAF_prime_pow_ge_three χ hp hk3

theorem normFiberCoeff_baseChange_eq_pairInverseCoeff
    {q : ℕ} (χ : DirichletCharacter ℂ q)
    (n : ℕ) (hn : n ≠ 0) :
    normFiberCoeff (baseChangeWeight χ) n =
      pairInverseCoeff χ (baseChangeChar χ) n := by
  exact normFiberCoeff_eq_pairInverseCoeff_of_local χ
    (fun p hp => normFiberCoeff_eq_pairAF_prime χ hp)
    (fun p hp => normFiberCoeff_eq_pairAF_prime_sq χ hp) n hn

end ShortDraftHeckeBridge
open Filter Asymptotics

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.PrimeExtraction
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics

open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid

namespace FiniteSFactor

theorem mem_fiber {n : ℕ} {I : Ideal O} : I ∈ fiber n ↔ Ideal.absNorm I = n := by
  simp [fiber]

open scoped Classical

open scoped Classical

end FiniteSFactor

open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.PrimeRows.NormFiberExtraction
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology

namespace ConcretePrimeRowBridge

section

open ActualEisensteinCubic ShortDraftHeckeBridge

private theorem idealMoebius_norm_le_one (I : Ideal O) :
    ‖((UniqueFactorizationMonoid.moebius I : ℤ) : ℂ)‖ ≤ 1 := by
  classical
  by_cases h : Squarefree I
  · rw [h.moebius_eq]
    simp
  · rw [UniqueFactorizationMonoid.moebius_of_not_squarefree h]
    simp

theorem baseChangeWeight_norm_le_one {q : ℕ}
    (χ : DirichletCharacter ℂ q) (I : Ideal O) :
    ‖baseChangeWeight χ I‖ ≤ 1 := by
  rw [baseChangeWeight, norm_mul]
  have hμ := idealMoebius_norm_le_one I
  have hχ := χ.norm_le_one (Ideal.absNorm I)
  exact (mul_le_mul hμ hχ (norm_nonneg _) (by positivity)).trans (by norm_num)

open ActualEisensteinCubic ShortDraftHeckeBridge
open scoped Classical

end

open ShortDraftHeckeBridge FiniteSFactor

open ShortDraftHeckeBridge FiniteSFactor Filter

end ConcretePrimeRowBridge

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.RayExpansion
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid

open scoped BigOperators Classical

open scoped BigOperators Classical
namespace QuadraticDivisorSplit

theorem exists_unique_split (B C D : Ideal O) (hBC : IsCoprime B C)
    (hD : D ∣ B * C) :
    ∃! x : Ideal O × Ideal O, x.1 ∣ B ∧ x.2 ∣ C ∧ x.1 * x.2 = D := by
  obtain ⟨D₁, D₂, h₁, h₂, hprod⟩ := exists_dvd_and_dvd_of_dvd_mul hD
  refine ⟨(D₁, D₂), ⟨h₁, h₂, hprod.symm⟩, ?_⟩
  intro y hy
  apply Prod.ext
  · apply associated_iff_eq.mp
    apply associated_of_dvd_dvd
    · apply (hBC.mono hy.1 h₂).dvd_of_dvd_mul_right
      rw [← hprod, ← hy.2.2]
      exact dvd_mul_right _ _
    · apply (hBC.mono h₁ hy.2.1).dvd_of_dvd_mul_right
      rw [hy.2.2, hprod]
      exact dvd_mul_right _ _
  · apply associated_iff_eq.mp
    apply associated_of_dvd_dvd
    · apply (hBC.symm.mono hy.2.1 h₁).dvd_of_dvd_mul_left
      rw [← hprod, ← hy.2.2]
      exact dvd_mul_left _ _
    · apply (hBC.symm.mono h₂ hy.1).dvd_of_dvd_mul_left
      rw [hy.2.2, hprod]
      exact dvd_mul_left _ _

theorem split_product_injective (B C : Ideal O) (hBC : IsCoprime B C) :
    Function.Injective (fun x : {x : Ideal O × Ideal O // x.1 ∣ B ∧ x.2 ∣ C} =>
      x.val.1 * x.val.2) := by
  intro x y hxy
  have hD : x.val.1 * x.val.2 ∣ B * C := mul_dvd_mul x.property.1 x.property.2
  obtain ⟨z, hz, huniq⟩ := exists_unique_split B C (x.val.1 * x.val.2) hBC hD
  apply Subtype.ext
  exact (huniq x.val ⟨x.property.1, x.property.2, rfl⟩).trans
    (huniq y.val ⟨y.property.1, y.property.2, hxy.symm⟩).symm

open IdealMobiusDivisorSum

theorem divisors_coprime_product (B C : Ideal O) (hB : B ≠ 0) (hC : C ≠ 0)
    (hBC : IsCoprime B C) :
    idealDivisors (B * C) =
      ((idealDivisors B) ×ˢ (idealDivisors C)).image (fun x => x.1 * x.2) := by
  ext D
  rw [mem_idealDivisors (mul_ne_zero hB hC), Finset.mem_image]
  constructor
  · intro hD
    obtain ⟨x, hx, _⟩ := exists_unique_split B C D hBC hD
    exact ⟨x, Finset.mem_product.mpr
      ⟨(mem_idealDivisors hB).mpr hx.1, (mem_idealDivisors hC).mpr hx.2.1⟩, hx.2.2⟩
  · rintro ⟨x, hx, rfl⟩
    exact mul_dvd_mul ((mem_idealDivisors hB).mp (Finset.mem_product.mp hx).1)
      ((mem_idealDivisors hC).mp (Finset.mem_product.mp hx).2)

theorem sum_divisors_coprime_product (B C : Ideal O) (hB : B ≠ 0) (hC : C ≠ 0)
    (hBC : IsCoprime B C) (f : Ideal O → ℂ) :
    (∑ D ∈ idealDivisors (B * C), f D) =
      ∑ D₁ ∈ idealDivisors B, ∑ D₂ ∈ idealDivisors C, f (D₁ * D₂) := by
  rw [divisors_coprime_product B C hB hC hBC, Finset.sum_image]
  · exact Finset.sum_product _ _ _
  · intro x hx y hy hxy
    have hx' : x.1 ∣ B ∧ x.2 ∣ C :=
      ⟨(mem_idealDivisors hB).mp (Finset.mem_product.mp hx).1,
        (mem_idealDivisors hC).mp (Finset.mem_product.mp hx).2⟩
    have hy' : y.1 ∣ B ∧ y.2 ∣ C :=
      ⟨(mem_idealDivisors hB).mp (Finset.mem_product.mp hy).1,
        (mem_idealDivisors hC).mp (Finset.mem_product.mp hy).2⟩
    have he : (⟨x, hx'⟩ : {z : Ideal O × Ideal O // z.1 ∣ B ∧ z.2 ∣ C}) = ⟨y, hy'⟩ :=
      split_product_injective B C hBC hxy
    exact congrArg Subtype.val he

end QuadraticDivisorSplit

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.MobiusEulerCorrection
namespace OAI

noncomputable section

namespace SmoothMobiusCorrection

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

open scoped BigOperators Classical

section
open ActualEisensteinCubic
open IdealMobiusDivisorSum hiding O
open UniqueFactorizationMonoid
open CanonicalRowCompletion (primeValueHom primeValueHom_prime)

theorem primeProduct_ne_zero (s : Finset PrimeIdeal) : primeProduct s ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr (fun P _ => P.property.ne_zero)

theorem factors_primeProduct (s : Finset PrimeIdeal) :
    normalizedFactors (primeProduct s) = s.val.map Subtype.val := by
  have h := normalizedFactors_prod_of_prime
    (m := s.val.map (fun P : PrimeIdeal => P.val)) (by
      intro P hP
      obtain ⟨Q,hQ,rfl⟩ := Multiset.mem_map.mp hP
      exact Q.property)
  simpa only [primeProduct, Finset.prod_eq_multiset_prod] using h

theorem primeSet_primeProduct (s : Finset PrimeIdeal) : primeSet (primeProduct s) = s := by
  ext P
  rw [mem_primeSet]
  simp only [primeSupport, factors_primeProduct, Multiset.mem_toFinset,
    Multiset.mem_map, Finset.mem_val]
  constructor
  · rintro ⟨Q,hQ,he⟩
    have : Q=P := Subtype.ext he
    simpa [this] using hQ
  · intro h
    exact ⟨P,h,rfl⟩

theorem primeProduct_injective : Function.Injective primeProduct := by
  intro s t h
  simpa only [primeSet_primeProduct] using congrArg primeSet h

theorem primeProduct_squarefree (s : Finset PrimeIdeal) : Squarefree (primeProduct s) := by
  rw [squarefree_iff_nodup_normalizedFactors (primeProduct_ne_zero s),factors_primeProduct]
  exact s.nodup.map Subtype.val_injective

theorem primeProduct_primeSet (I : Ideal ActualEisensteinCubic.O) (hI : Squarefree I) :
    primeProduct (primeSet I) = I := by
  unfold primeProduct primeSet
  rw [Finset.prod_image]
  · change (∏ P ∈ (primeSupport I).attach, (fun Q : Ideal ActualEisensteinCubic.O => Q) P.val) = I
    exact (Finset.prod_attach (primeSupport I) (fun Q : Ideal ActualEisensteinCubic.O => Q)).trans
      (squarefree_support_product_self hI)
  · intro P hP Q hQ he
    exact Subtype.ext (congrArg (fun R : PrimeIdeal => R.val) he)

theorem mobiusPrimeCoeff_nonsquarefree (w : Ideal ActualEisensteinCubic.O → ℂ) (I : Ideal ActualEisensteinCubic.O)
    (hI : ¬Squarefree I) : mobiusPrimeCoeff w I=0 := by
  simp [mobiusPrimeCoeff,moebius_of_not_squarefree hI]

theorem mobiusPrimeCoeff_primeProduct (w : Ideal ActualEisensteinCubic.O → ℂ) (s : Finset PrimeIdeal) :
    mobiusPrimeCoeff w (primeProduct s) = ∏ P ∈ s, -w P.val := by
  have hm : (moebius (primeProduct s) : ℂ)=(-1:ℂ)^s.card := by
    rw [(primeProduct_squarefree s).moebius_eq,factors_eq_normalizedFactors,
      factors_primeProduct]
    simp
  rw [mobiusPrimeCoeff,hm]
  simp only [primeProduct,map_prod,primeValueHom_prime _ _ (Subtype.property _)]
  rw [Finset.prod_neg]

theorem mobiusPrimeCoeff_tsum (w : Ideal ActualEisensteinCubic.O → ℂ) :
    (∑' I : Ideal ActualEisensteinCubic.O, mobiusPrimeCoeff w I) =
      ∑' s : Finset PrimeIdeal, ∏ P ∈ s, -w P.val := by
  apply tsum_eq_tsum_of_ne_zero_bij (fun s => primeProduct s.val)
  · exact primeProduct_injective.comp Subtype.val_injective
  · intro I hI
    have hs : Squarefree I := by
      by_contra hs
      exact hI (mobiusPrimeCoeff_nonsquarefree w I hs)
    have hp : (∏ P ∈ primeSet I, -w P.val) ≠ 0 := by
      rw [←mobiusPrimeCoeff_primeProduct,primeProduct_primeSet I hs]
      exact hI
    exact ⟨⟨primeSet I,hp⟩,primeProduct_primeSet I hs⟩
  · intro s
    exact mobiusPrimeCoeff_primeProduct w s.val

theorem mobiusPrimeCoeff_euler (w : Ideal ActualEisensteinCubic.O → ℂ)
    (hw : Summable (fun P : PrimeIdeal => ‖w P.val‖)) :
    (∑' I : Ideal ActualEisensteinCubic.O, mobiusPrimeCoeff w I) =
      ∏' P : PrimeIdeal, (1-w P.val) := by
  rw [mobiusPrimeCoeff_tsum]
  have hs : Summable (fun P : PrimeIdeal => ‖-w P.val‖) := by simpa using hw
  simpa only [sub_eq_add_neg] using
    (tprod_one_add (summable_finsetProd_of_summable_norm hs)).symm

end

section
open ActualEisensteinCubic
open Filter

lemma prime_norm_pos (P : PrimeIdeal) : (0 : ℝ) < Ideal.absNorm P.val := by
  have h := prime_norm_two_le P
  exact_mod_cast (by omega : 0 < Ideal.absNorm P.val)

lemma norm_primeNormPower (P : PrimeIdeal) (s : ℂ) :
    ‖primeNormPower P s‖=(Ideal.absNorm P.val : ℝ)^(-s.re) := by
  exact Complex.norm_cpow_eq_rpow_re_of_pos (prime_norm_pos P) (-s)

lemma one_sub_ne_zero {x : ℂ} (hx : ‖x‖<1) : 1-x≠0 := by
  intro h
  have he : x=1 := (sub_eq_zero.mp h).symm
  simp [he] at hx

end

open ActualEisensteinCubic

open scoped BigOperators Classical
open ActualEisensteinCubic
open ShortDraftHeckeBridge hiding O

lemma normFiber_tsum (a : Ideal ActualEisensteinCubic.O→ℂ) (n : ℕ) :
    (∑'I : {I : Ideal ActualEisensteinCubic.O // Ideal.absNorm I=n},a I.val)=normFiberCoeff a n := by
  let : Fintype {I : Ideal ActualEisensteinCubic.O // Ideal.absNorm I=n} :=
    (Ideal.finite_setOfPred_absNorm_eq (S := ActualEisensteinCubic.O) n).fintype
  rw [tsum_fintype]
  symm
  change (∑I∈FiniteSFactor.fiber n,a I)=_
  apply Finset.sum_bij (fun I hI => (⟨I,FiniteSFactor.mem_fiber.mp hI⟩ : {I : Ideal ActualEisensteinCubic.O // Ideal.absNorm I=n}))
  · intro I hI
    exact Finset.mem_univ _
  · intro I hI J hJ he
    exact congrArg Subtype.val he
  · intro I hI
    exact ⟨I.val,FiniteSFactor.mem_fiber.mpr I.property,rfl⟩
  · intro I hI
    rfl

lemma idealDirichlet_fiber (a : Ideal ActualEisensteinCubic.O→ℂ) (s : ℂ) (n : ℕ) :
    (∑'I : {I : Ideal ActualEisensteinCubic.O // Ideal.absNorm I=n},a I.val*CubicEisenstein.fullIdealWeight s I.val)=
      LSeries.term (normFiberCoeff a) s n := by
  by_cases hn : n=0
  · subst n
    have hz (I : {I : Ideal ActualEisensteinCubic.O // Ideal.absNorm I=0}) : CubicEisenstein.fullIdealWeight s I.val=0 := by
      have hI : I.val=0 := Ideal.absNorm_eq_zero_iff.mp I.property
      simp [CubicEisenstein.fullIdealWeight,hI]
    simp only [hz,mul_zero,tsum_zero,LSeries.term_zero]
  · have ht (I : {I : Ideal ActualEisensteinCubic.O // Ideal.absNorm I=n}) :
        CubicEisenstein.fullIdealWeight s I.val=(n:ℂ)^(-s) := by
      have hI : I.val≠0 := fun h => hn (by rw [←I.property,h,map_zero])
      rw [CubicEisenstein.fullIdealWeight,if_neg hI,I.property]
    simp_rw [ht]
    rw [tsum_mul_right,normFiber_tsum,LSeries.term_of_ne_zero hn,Complex.cpow_neg,div_eq_mul_inv]

lemma idealDirichlet_summable (a : Ideal ActualEisensteinCubic.O→ℂ) (ha : ∀I,‖a I‖≤1) (s : ℂ) (hs : 1<s.re) :
    Summable (fun I : Ideal ActualEisensteinCubic.O => a I*CubicEisenstein.fullIdealWeight s I) := by
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun I => ?_) (CubicEisenstein.fullIdealWeight_summable_norm s hs)
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (ha I)

theorem idealDirichlet_eq_LSeries (a : Ideal ActualEisensteinCubic.O→ℂ) (ha : ∀I,‖a I‖≤1)
    (s : ℂ) (hs : 1<s.re) :
    (∑'I : Ideal ActualEisensteinCubic.O,a I*CubicEisenstein.fullIdealWeight s I)=LSeries (normFiberCoeff a) s := by
  have hh := (idealDirichlet_summable a ha s hs).hasSum.tsum_fiberwise Ideal.absNorm
  change HasSum (fun n : ℕ => ∑'I : {I : Ideal ActualEisensteinCubic.O // Ideal.absNorm I=n},
    a I.val*CubicEisenstein.fullIdealWeight s I.val) _ at hh
  simp_rw [idealDirichlet_fiber] at hh
  exact hh.tsum_eq.symm

end SmoothMobiusCorrection

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.IdealEuler
namespace OAI

namespace SevenEighths.IdealEuler

open ActualEisensteinCubic UniqueFactorizationMonoid
open CompletedGauss (MulFiber mulFiber_moebius_sum)
open SmoothMobiusCorrection (PrimeIdeal)
open scoped BigOperators Classical

noncomputable section

theorem inverseSeries_eq_inv (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (s : ℂ) (hs : 1 < s.re) : inverseSeries a s = (series a s)⁻¹ := by
  calc
    _ = (inverseSeries a s * series a s) * (series a s)⁻¹ := by
      rw [mul_assoc, mul_inv_cancel₀ (series_ne_zero a ha s hs), mul_one]
    _ = _ := by rw [inverseSeries_mul_series a ha s hs, one_mul]

theorem prime_summable_norm (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (s : ℂ) (hs : 1 < s.re) : Summable (fun P : PrimeIdeal => ‖weighted a s P.val‖) :=
  (weighted_summable_norm a ha s hs).comp_injective Subtype.val_injective

theorem prime_norm_lt_one (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (s : ℂ) (hs : 0 < s.re) (P : PrimeIdeal) : ‖weighted a s P.val‖ < 1 := by
  change ‖a P.val * CubicEisenstein.fullIdealWeight s P.val‖ < 1
  simp only [CubicEisenstein.fullIdealWeight, P.property.ne_zero, ite_false, norm_mul]
  change ‖a P.val‖ * ‖SmoothMobiusCorrection.primeNormPower P s‖ < 1
  rw [SmoothMobiusCorrection.norm_primeNormPower]
  apply (mul_le_of_le_one_left (Real.rpow_nonneg (by positivity) _) (ha P.val)).trans_lt
  exact Real.rpow_lt_one_of_one_lt_of_neg
    (by have h := SmoothMobiusCorrection.prime_norm_two_le P
        exact_mod_cast (by omega : 1 < Ideal.absNorm P.val)) (by simpa using neg_neg_of_pos hs)

theorem local_factor_ne_zero (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (s : ℂ) (hs : 0 < s.re) (P : PrimeIdeal) : 1 - weighted a s P.val ≠ 0 :=
  SmoothMobiusCorrection.one_sub_ne_zero (prime_norm_lt_one a ha s hs P)

theorem inverseSeries_euler (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (s : ℂ) (hs : 1 < s.re) :
    inverseSeries a s = ∏' P : PrimeIdeal, (1 - weighted a s P.val) := by
  have h := SmoothMobiusCorrection.mobiusPrimeCoeff_euler (weighted a s)
    (prime_summable_norm a ha s hs)
  simpa only [SmoothMobiusCorrection.mobiusPrimeCoeff, primeValueHom_eq, inverseSeries] using h

theorem euler_hasProd (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (s : ℂ) (hs : 1 < s.re) :
    HasProd (fun P : PrimeIdeal => (1 - weighted a s P.val)⁻¹) (series a s) := by
  have hm : Multipliable (fun P : PrimeIdeal => 1 - weighted a s P.val) := by
    simpa only [sub_eq_add_neg] using multipliable_one_add_of_summable
      (show Summable (fun P : PrimeIdeal => ‖-weighted a s P.val‖) by
        simpa only [norm_neg] using prime_summable_norm a ha s hs)
  have heq : (∏' P : PrimeIdeal, (1 - weighted a s P.val)) = (series a s)⁻¹ :=
    (inverseSeries_euler a ha s hs).symm.trans (inverseSeries_eq_inv a ha s hs)
  have hne : (∏' P : PrimeIdeal, (1 - weighted a s P.val)) ≠ 0 := by
    rw [heq]
    exact inv_ne_zero (series_ne_zero a ha s hs)
  simpa only [heq, inv_inv] using hm.hasProd.inv₀ hne

end

end SevenEighths.IdealEuler

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.Boundary
namespace OAI

namespace SevenEighths.HeckeBoundary

open ActualEisensteinCubic Complex
open SevenEighths.IdealEuler SevenEighths.IdealCharacter
open SmoothMobiusCorrection (PrimeIdeal)
open Asymptotics Filter
open scoped BigOperators Classical Topology

noncomputable section

theorem re_log_comb_nonneg {a : ℝ} (ha₀ : 0 ≤ a) (ha₁ : a < 1)
    {z : ℂ} (hz : ‖z‖ = 1) :
    0 ≤ 3 * (-log (1 - a)).re + 4 * (-log (1 - a * z)).re +
      (-log (1 - a * z ^ 2)).re := by
  have hac₀ : ‖(a : ℂ)‖ < 1 := by
    simp only [Complex.norm_of_nonneg ha₀, ha₁]
  have hac₁ : ‖a * z‖ < 1 := by rwa [norm_mul, hz, mul_one]
  have hac₂ : ‖a * z ^ 2‖ < 1 := by rwa [norm_mul, norm_pow, hz, one_pow, mul_one]
  rw [← ((hasSum_re <| hasSum_taylorSeries_neg_log hac₀).mul_left 3).add
    ((hasSum_re <| hasSum_taylorSeries_neg_log hac₁).mul_left 4) |>.add
    (hasSum_re <| hasSum_taylorSeries_neg_log hac₂) |>.tsum_eq]
  refine tsum_nonneg fun n ↦ ?_
  simp only [← ofReal_pow, div_natCast_re, ofReal_re, mul_pow, mul_re, ofReal_im, zero_mul,
    sub_zero]
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  · simp only [← mul_div_assoc, ← add_div]
    refine div_nonneg ?_ n.cast_nonneg
    rw [← pow_mul, pow_mul', sq, mul_re, ← sq, ← sq, ← sq_norm_sub_sq_re, norm_pow, hz]
    convert! (preTransparency := .instances) (show 0 ≤ 2 * a ^ n * ((z ^ n).re + 1) ^ 2 by positivity) using 1
    ring

theorem re_log_cpow_comb_nonneg {n : ℕ} (hn : 2 ≤ n) {x : ℝ} (hx : 1 < x)
    (y : ℝ) {z : ℂ} (hz : ‖z‖ = 1) :
    0 ≤ 3 * (-log (1 - (n : ℂ) ^ (-x : ℂ))).re +
      4 * (-log (1 - z * (n : ℂ) ^ (-(x + I * y)))).re +
      (-log (1 - z ^ 2 * (n : ℂ) ^ (-(x + 2 * I * y)))).re := by
  have hn' : (n : ℝ) ^ (-x) < 1 := by
    rw [Real.rpow_neg (Nat.cast_nonneg n), inv_lt_one_iff₀]
    exact .inr <| Real.one_lt_rpow (mod_cast one_lt_two.trans_le hn) <| zero_lt_one.trans hx
  have hz' : ‖z * (n : ℂ) ^ (-(I * y))‖ = 1 := by
    rw [norm_mul, hz, ← ofReal_natCast,
      norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast (by omega : (0 : ℕ) < n))]
    simp
  convert! (preTransparency := .instances) re_log_comb_nonneg (by positivity) hn' hz' using 6
  · simp only [ofReal_cpow n.cast_nonneg (-x), ofReal_natCast, ofReal_neg]
  · congr 2
    rw [neg_add, cpow_add _ _ <| mod_cast by omega, ← ofReal_neg,
      ofReal_cpow n.cast_nonneg (-x), ofReal_natCast, mul_left_comm]
  · rw [neg_add, cpow_add _ _ <| mod_cast by omega, ← ofReal_neg,
      ofReal_cpow n.cast_nonneg (-x), ofReal_natCast,
      show -(2 * I * y) = (2 : ℕ) * -(I * y) by ring, cpow_nat_mul, mul_pow,
      mul_left_comm]

theorem summable_neg_log_euler (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (s : ℂ) (hs : 1 < s.re) :
    Summable (fun P : PrimeIdeal => -log (1 - weighted a s P.val)) :=
  (prime_summable_norm a ha s hs).of_norm.clog_one_sub.neg

theorem exp_log_euler_eq_series (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (s : ℂ) (hs : 1 < s.re) :
    exp (∑' P : PrimeIdeal, -log (1 - weighted a s P.val)) = series a s := by
  have hp : HasProd (fun P : PrimeIdeal => (1 - weighted a s P.val)⁻¹)
      (exp (∑' P : PrimeIdeal, -log (1 - weighted a s P.val))) :=
    (summable_neg_log_euler a ha s hs).hasSum.cexp.congr
      (fun S => Finset.prod_congr rfl (fun P _ => by
        simp only [Function.comp_apply]
        rw [exp_neg, exp_log (local_factor_ne_zero a ha s (by linarith) P)]))
  exact hp.unique (euler_hasProd a ha s hs)

theorem re_log_weighted_comb_nonneg (a₀ a₁ a₂ : Ideal O →*₀ ℂ)
    (h : PrimeTriple a₀ a₁ a₂) {x : ℝ} (hx : 1 < x) (y : ℝ) (P : PrimeIdeal) :
    0 ≤ 3 * (-log (1 - weighted a₀ (x : ℂ) P.val)).re +
      4 * (-log (1 - weighted a₁ (x + I * y) P.val)).re +
      (-log (1 - weighted a₂ (x + 2 * I * y) P.val)).re := by
  change 0 ≤ 3 * (-log (1 - a₀ P.val * normWeight (x : ℂ) P.val)).re +
      4 * (-log (1 - a₁ P.val * normWeight (x + I * y) P.val)).re +
      (-log (1 - a₂ P.val * normWeight (x + 2 * I * y) P.val)).re
  rcases h P with ⟨h₀, h₁, h₂⟩ | ⟨h₀, h₁, h₂⟩
  · simp only [h₀, h₁, h₂, zero_mul, sub_zero, log_one, neg_zero, zero_re,
      mul_zero, add_zero, le_refl]
  · simp only [h₀, h₂, one_mul]
    change 0 ≤ 3 * (-log (1 - CubicEisenstein.fullIdealWeight (x : ℂ) P.val)).re +
      4 * (-log (1 - a₁ P.val * CubicEisenstein.fullIdealWeight (x + I * y) P.val)).re +
      (-log (1 - a₁ P.val ^ 2 * CubicEisenstein.fullIdealWeight (x + 2 * I * y) P.val)).re
    simp only [CubicEisenstein.fullIdealWeight, P.property.ne_zero, ite_false]
    exact re_log_cpow_comb_nonneg (SmoothMobiusCorrection.prime_norm_two_le P) hx y h₁

theorem norm_series_product_ge_one (a₀ a₁ a₂ : Ideal O →*₀ ℂ)
    (ha₀ : ∀ I, ‖a₀ I‖ ≤ 1) (ha₁ : ∀ I, ‖a₁ I‖ ≤ 1) (ha₂ : ∀ I, ‖a₂ I‖ ≤ 1)
    (h : PrimeTriple a₀ a₁ a₂) {x : ℝ} (hx : 1 < x) (y : ℝ) :
    1 ≤ ‖series a₀ (x : ℂ) ^ 3 * series a₁ (x + I * y) ^ 4 *
      series a₂ (x + 2 * I * y)‖ := by
  have hs₀ : 1 < (x : ℂ).re := hx
  have hs₁ : 1 < (x + I * y : ℂ).re := by simpa using hx
  have hs₂ : 1 < (x + 2 * I * y : ℂ).re := by simpa using hx
  have H₀ := summable_neg_log_euler a₀ ha₀ _ hs₀
  have H₁ := summable_neg_log_euler a₁ ha₁ _ hs₁
  have H₂ := summable_neg_log_euler a₂ ha₂ _ hs₂
  have hsum₀ := (hasSum_re H₀.hasSum).summable.mul_left 3
  have hsum₁ := (hasSum_re H₁.hasSum).summable.mul_left 4
  have hsum₂ := (hasSum_re H₂.hasSum).summable
  rw [← exp_log_euler_eq_series a₀ ha₀ _ hs₀,
    ← exp_log_euler_eq_series a₁ ha₁ _ hs₁, ← exp_log_euler_eq_series a₂ ha₂ _ hs₂]
  simp only [← exp_nat_mul, Nat.cast_ofNat, ← exp_add, norm_exp, add_re, mul_re,
    re_ofNat, im_ofNat, zero_mul, sub_zero, Real.one_le_exp_iff]
  rw [re_tsum H₀, re_tsum H₁, re_tsum H₂, ← tsum_mul_left, ← tsum_mul_left,
    ← hsum₀.tsum_add hsum₁, ← (hsum₀.add hsum₁).tsum_add hsum₂]
  exact tsum_nonneg fun P => re_log_weighted_comb_nonneg a₀ a₁ a₂ h hx y P

theorem ofResidue_primeTriple (M : Ideal O) [Finite (O ⧸ M)]
    (χ : MulChar (O ⧸ M) ℂ) (hχ : UnitInvariant M χ) :
    PrimeTriple (ofResidue M 1 (one_unitInvariant M))
      (ofResidue M χ hχ) (ofResidue M (χ ^ 2) (square_unitInvariant M χ hχ)) := by
  intro P
  let q := Ideal.Quotient.mk M (Submodule.IsPrincipal.generator P.val)
  have hv (ψ : MulChar (O ⧸ M) ℂ) (hψ : UnitInvariant M ψ) :
      ofResidue M ψ hψ P.val = ψ q := by
    change value M ψ P.val = _
    have hP : P.val ≠ ⊥ := P.property.ne_zero
    simp only [value, hP, ite_false, q]
  rw [hv, hv, hv]
  by_cases hq : IsUnit q
  · right
    refine ⟨MulChar.one_apply hq, ?_, χ.pow_apply' two_ne_zero q⟩
    let : Fintype (O ⧸ M)ˣ := Fintype.ofFinite _
    obtain ⟨u, hu⟩ := hq
    rw [← hu]
    have hn := Complex.norm_eq_one_of_mem_rootsOfUnity (χ.apply_mem_rootsOfUnity u)
    simpa only [MulChar.coe_equivToUnitHom] using hn
  · left
    exact ⟨MulChar.map_nonunit _ hq, MulChar.map_nonunit _ hq, MulChar.map_nonunit _ hq⟩

theorem horizontal_isBigO_of_zero (F : ℂ → ℂ) (t : ℝ)
    (hF : DifferentiableAt ℂ F (1 + I * t)) (hz : F (1 + I * t) = 0) :
    (fun x : ℝ => F (1 + x + I * t)) =O[𝓝[>] 0] fun x : ℝ => (x : ℂ) := by
  simp_rw [add_comm (1 : ℂ), add_assoc]
  have h := hF.hasDerivAt
  rw [← zero_add (1 + _)] at h
  simpa only [zero_add, hz, sub_zero]
    using (Complex.isBigO_comp_ofReal_nhds
      (h.comp_add_const 0 _).differentiableAt.isBigO_sub) |>.mono nhdsWithin_le_nhds

theorem horizontal_isBigO_one (F : ℂ → ℂ) (t : ℝ)
    (hF : ContinuousAt F (1 + I * t)) :
    (fun x : ℝ => F (1 + x + I * t)) =O[𝓝[>] 0] fun _ => (1 : ℂ) := by
  refine IsBigO.mono ?_ nhdsWithin_le_nhds
  simp_rw [add_comm (1 : ℂ), add_assoc]
  rw [← zero_add (1 + _)] at hF
  exact hF.comp (f := fun x : ℝ => x + (1 + I * t)) (x := 0) (by fun_prop)
    |>.tendsto.isBigO_one ℂ

theorem boundary_ne_zero_of_series_eq (a₀ a₁ a₂ : Ideal O →*₀ ℂ)
    (ha₀ : ∀ I, ‖a₀ I‖ ≤ 1) (ha₁ : ∀ I, ‖a₁ I‖ ≤ 1) (ha₂ : ∀ I, ‖a₂ I‖ ≤ 1)
    (h : PrimeTriple a₀ a₁ a₂) (F₀ F₁ F₂ : ℂ → ℂ)
    (hEq₀ : ∀ s : ℂ, 1 < s.re → F₀ s = series a₀ s)
    (hEq₁ : ∀ s : ℂ, 1 < s.re → F₁ s = series a₁ s)
    (hEq₂ : ∀ s : ℂ, 1 < s.re → F₂ s = series a₂ s)
    (t : ℝ)
    (hPole : (fun x : ℝ => F₀ (1 + x)) =O[𝓝[>] 0] fun x => (1 : ℂ) / x)
    (hReg₁ : DifferentiableAt ℂ F₁ (1 + I * t))
    (hReg₂ : ContinuousAt F₂ (1 + 2 * I * t)) : F₁ (1 + I * t) ≠ 0 := by
  intro hz
  have hLower (x : ℝ) (hx : 0 < x) :
      1 ≤ ‖F₀ (1 + x) ^ 3 * F₁ (1 + x + I * t) ^ 4 * F₂ (1 + x + 2 * I * t)‖ := by
    have hs₀ : 1 < (1 + x : ℂ).re := by simp; exact hx
    have hs₁ : 1 < (1 + x + I * t : ℂ).re := by simpa using hs₀
    have hs₂ : 1 < (1 + x + 2 * I * t : ℂ).re := by simpa using hs₀
    rw [hEq₀ _ hs₀, hEq₁ _ hs₁, hEq₂ _ hs₂]
    simpa only [ofReal_add, ofReal_one] using
      norm_series_product_ge_one a₀ a₁ a₂ ha₀ ha₁ ha₂ h (by linarith : 1 < 1 + x) t
  have hReg₂' : ContinuousAt F₂ (1 + I * ((2 * t : ℝ) : ℂ)) := by
    convert (preTransparency := .instances) hReg₂ using 1
    push_cast
    ring
  have help (x : ℝ) : ((1 / x) ^ 3 * x ^ 4 * 1 : ℂ) = x := by
    rcases eq_or_ne x 0 with rfl | hx
    · rw [ofReal_zero, zero_pow (by decide), mul_zero, mul_one]
    · rw [one_div, inv_pow, pow_succ _ 3, ← mul_assoc,
        inv_mul_cancel₀ <| pow_ne_zero 3 (ofReal_ne_zero.mpr hx), one_mul, mul_one]
  have H₀ : (fun _ : ℝ => (1 : ℝ)) =O[𝓝[>] 0]
      fun x => F₀ (1 + x) ^ 3 * F₁ (1 + x + I * t) ^ 4 * F₂ (1 + x + 2 * I * t) :=
    IsBigO.of_bound' <| eventually_nhdsWithin_of_forall
      fun x hx => (norm_one (α := ℝ)).symm ▸ (hLower x hx)
  have H := (hPole.pow 3).mul ((horizontal_isBigO_of_zero F₁ t hReg₁ hz).pow 4)
    |>.mul (horizontal_isBigO_one F₂ (2 * t) hReg₂')
  simp only [ofReal_mul, ofReal_ofNat, mul_left_comm I, ← mul_assoc, help] at H
  replace H := (H₀.trans H).norm_right
  simp only [norm_real] at H
  exact isLittleO_irrefl (.of_forall (fun _ => one_ne_zero)) <|
    H.of_norm_right.trans_isLittleO <| isLittleO_id_one.mono nhdsWithin_le_nhds

section Quadratic

open IdealMobiusDivisorSum (idealDivisors mem_idealDivisors)
open UniqueFactorizationMonoid
open scoped ComplexOrder

theorem idealDivisors_one : idealDivisors (1 : Ideal O) = {1} := by
  ext D
  rw [mem_idealDivisors (show (1 : Ideal O) ≠ ⊥ from one_ne_zero), Finset.mem_singleton]
  exact isUnit_iff_dvd_one.symm.trans isUnit_iff_eq_one

@[simp] theorem zetaConvolutionCoeff_one (a : Ideal O →*₀ ℂ) :
    zetaConvolutionCoeff a 1 = 1 := by
  rw [zetaConvolutionCoeff, if_neg one_ne_zero, idealDivisors_one, Finset.sum_singleton]
  exact map_one a

theorem idealDivisors_prime_pow (P : Ideal O) (hP : Prime P) (k : ℕ) :
    idealDivisors (P ^ k) = (Finset.range (k + 1)).image (fun j => P ^ j) := by
  ext D
  rw [mem_idealDivisors (show P ^ k ≠ ⊥ from pow_ne_zero k hP.ne_zero), Finset.mem_image]
  constructor
  · intro hD
    obtain ⟨j, hj, hDj⟩ := (dvd_prime_pow hP k).mp hD
    exact ⟨j, Finset.mem_range.mpr (by omega), (associated_iff_eq.mp hDj).symm⟩
  · rintro ⟨j, hj, rfl⟩
    exact pow_dvd_pow P (by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hj)

theorem zetaConvolutionCoeff_prime_pow (a : Ideal O →*₀ ℂ) (P : Ideal O)
    (hP : Prime P) (k : ℕ) :
    zetaConvolutionCoeff a (P ^ k) = ∑ j ∈ Finset.range (k + 1), a P ^ j := by
  rw [zetaConvolutionCoeff, if_neg (pow_ne_zero k hP.ne_zero), idealDivisors_prime_pow P hP k,
    Finset.sum_image]
  · simp only [map_pow]
  · exact fun i _ j _ hij => pow_injective_of_not_isUnit hP.not_isUnit hP.ne_zero hij

theorem zetaConvolutionCoeff_mul (a : Ideal O →*₀ ℂ) (B C : Ideal O)
    (hB : B ≠ 0) (hC : C ≠ 0) (hBC : IsRelPrime B C) :
    zetaConvolutionCoeff a (B * C) = zetaConvolutionCoeff a B * zetaConvolutionCoeff a C := by
  have hcop : IsCoprime B C := by
    apply Ideal.isCoprime_iff_sup_eq.mpr
    apply Ideal.isUnit_iff.mp
    exact hBC (Ideal.dvd_iff_le.mpr le_sup_left) (Ideal.dvd_iff_le.mpr le_sup_right)
  simp only [zetaConvolutionCoeff, hB, hC, mul_ne_zero hB hC, ite_false]
  rw [QuadraticDivisorSplit.sum_divisors_coprime_product B C hB hC hcop]
  simp only [map_mul, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_comm

theorem zetaConvolutionCoeff_nonneg (a : Ideal O →*₀ ℂ)
    (ha : ∀ P : Ideal O, Prime P → a P = 0 ∨ a P = 1 ∨ a P = -1)
    (B : Ideal O) : 0 ≤ zetaConvolutionCoeff a B := by
  induction B using UniqueFactorizationMonoid.induction_on_coprime with
  | h0 => simp [zetaConvolutionCoeff]
  | h1 hunit =>
    rw [isUnit_iff_eq_one.mp hunit, zetaConvolutionCoeff_one]
    exact zero_le_one
  | hpr k hP =>
    rw [zetaConvolutionCoeff_prime_pow a _ hP k]
    rcases ha _ hP with hz | ho | hm
    · exact Finset.sum_nonneg (fun j _ => by rw [hz]; exact pow_nonneg (le_refl 0) j)
    · exact Finset.sum_nonneg (fun j _ => by rw [ho, one_pow]; exact zero_le_one)
    · rw [hm, neg_one_geom_sum]
      split_ifs <;> first | exact le_refl 0 | exact zero_le_one
  | @hcp B C hBC hB hC =>
    by_cases hB0 : B = 0
    · simp [hB0, zetaConvolutionCoeff]
    by_cases hC0 : C = 0
    · simp [hC0, zetaConvolutionCoeff]
    rw [zetaConvolutionCoeff_mul a B C hB0 hC0 hBC]
    exact mul_nonneg hB hC

theorem quadratic_normFiber_nonneg (M : Ideal O) (χ : MulChar (O ⧸ M) ℂ)
    (hχ : UnitInvariant M χ) (hquad : χ ^ 2 = 1) (n : ℕ) :
    0 ≤ ShortDraftHeckeBridge.normFiberCoeff
      (zetaConvolutionCoeff (ofResidue M χ hχ)) n := by
  apply Finset.sum_nonneg
  intro B _
  apply zetaConvolutionCoeff_nonneg
  intro P hP
  change value M χ P = 0 ∨ value M χ P = 1 ∨ value M χ P = -1
  have hP0 : P ≠ ⊥ := hP.ne_zero
  simp only [value, hP0, ite_false]
  exact MulChar.isQuadratic_iff_sq_eq_one.mpr hquad _

theorem mulFiber_character_sum (a : Ideal O →*₀ ℂ) (B : Ideal O) (hB : B ≠ 0) :
    (∑' p : CompletedGauss.MulFiber B, a p.val.1) = zetaConvolutionCoeff a B := by
  let e := CompletedGauss.mulFiberDivisorEquiv B hB
  rw [zetaConvolutionCoeff, if_neg hB]
  calc
    _ = ∑' D : {D : Ideal O // D ∈ idealDivisors B}, a D.val :=
      e.tsum_eq (fun D => a D.val)
    _ = _ := by
      rw [tsum_fintype]
      exact (Finset.sum_subtype (idealDivisors B) (fun _ => Iff.rfl) a).symm

theorem zetaConvolution_hasSum (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (s : ℂ) (hs : 1 < s.re) :
    HasSum (fun B : Ideal O => zetaConvolutionCoeff a B * normWeight s B)
      (series a s * CubicEisenstein.fullIdealZeta s) := by
  let F : Ideal O × Ideal O → ℂ := fun p => a p.1 * normWeight s (p.1 * p.2)
  have hprod := (weighted_summable_norm a ha s hs).mul_norm
    (CubicEisenstein.fullIdealWeight_summable_norm s hs)
  have heq (p : Ideal O × Ideal O) :
      weighted a s p.1 * CubicEisenstein.fullIdealWeight s p.2 = F p := by
    change (a p.1 * normWeight s p.1) * normWeight s p.2 = _
    simp only [F, map_mul, mul_assoc]
  have hF : Summable F := hprod.of_norm.congr heq
  have hfiber (B : Ideal O) : (∑' p : CompletedGauss.MulFiber B, F p.val) =
      zetaConvolutionCoeff a B * normWeight s B := by
    by_cases hB : B = 0
    · subst B
      have hz (p : CompletedGauss.MulFiber 0) : F p.val = 0 := by
        simp only [F, p.property, map_zero, mul_zero]
      simp only [hz, tsum_zero, map_zero, mul_zero]
    · calc
        _ = (∑' p : CompletedGauss.MulFiber B, a p.val.1) * normWeight s B := by
          rw [← tsum_mul_right]
          exact tsum_congr (fun p => by simp only [F, p.property])
        _ = _ := by rw [mulFiber_character_sum a B hB]
  have hsum := hF.hasSum.tsum_fiberwise (fun p : Ideal O × Ideal O => p.1 * p.2)
  change HasSum (fun B : Ideal O => ∑' p : CompletedGauss.MulFiber B, F p.val) _ at hsum
  simp_rw [hfiber] at hsum
  convert (preTransparency := .instances) hsum using 1
  calc
    _ = ∑' p : Ideal O × Ideal O,
        weighted a s p.1 * CubicEisenstein.fullIdealWeight s p.2 :=
      tsum_mul_tsum_of_summable_norm (weighted_summable_norm a ha s hs)
        (CubicEisenstein.fullIdealWeight_summable_norm s hs)
    _ = _ := tsum_congr heq

theorem zetaConvolution_normFiber_one (a : Ideal O →*₀ ℂ) :
    ShortDraftHeckeBridge.normFiberCoeff (zetaConvolutionCoeff a) 1 = 1 := by
  have hsingle : (Ideal.finite_setOfPred_absNorm_eq (S := O) 1).toFinset = {1} := by
    ext I
    simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, Finset.mem_singleton]
    exact Ideal.absNorm_eq_one_iff.trans (by rw [Ideal.one_eq_top])
  unfold ShortDraftHeckeBridge.normFiberCoeff
  rw [hsingle, Finset.sum_singleton, zetaConvolutionCoeff_one]

theorem zetaConvolution_LSeries_hasSum (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (s : ℂ) (hs : 1 < s.re) :
    HasSum (LSeries.term (ShortDraftHeckeBridge.normFiberCoeff (zetaConvolutionCoeff a)) s)
      (series a s * CubicEisenstein.fullIdealZeta s) := by
  have h := (zetaConvolution_hasSum a ha s hs).tsum_fiberwise Ideal.absNorm
  change HasSum (fun n : ℕ => ∑' I : {I : Ideal O // Ideal.absNorm I = n},
    zetaConvolutionCoeff a I.val * CubicEisenstein.fullIdealWeight s I.val) _ at h
  simpa only [SmoothMobiusCorrection.idealDirichlet_fiber] using h

theorem zetaConvolution_LSeries_eq (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (s : ℂ) (hs : 1 < s.re) :
    LSeries (ShortDraftHeckeBridge.normFiberCoeff (zetaConvolutionCoeff a)) s =
      series a s * CubicEisenstein.fullIdealZeta s :=
  (zetaConvolution_LSeries_hasSum a ha s hs).tsum_eq

theorem quadratic_product_positive (M : Ideal O) [Finite (O ⧸ M)]
    (χ : MulChar (O ⧸ M) ℂ) (hχ : UnitInvariant M χ) (hquad : χ ^ 2 = 1)
    (F : ℂ → ℂ) (hF : Differentiable ℂ F)
    (hEq : ∀ s : ℂ, 1 < s.re →
      F s = series (ofResidue M χ hχ) s * CubicEisenstein.fullIdealZeta s) (y : ℝ) :
    0 < F y := by
  refine LSeries.positive_of_differentiable_of_eqOn
    (quadratic_normFiber_nonneg M χ hχ hquad)
    (zetaConvolution_normFiber_one (ofResidue M χ hχ) ▸ zero_lt_one) hF
    (x := 1) ?_ ?_ y
  · exact LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
      (fun s hs => (zetaConvolution_LSeries_hasSum (ofResidue M χ hχ)
        (norm_ofResidue_le_one M χ hχ) s hs).summable)
  · intro s hs
    rw [hEq s hs, zetaConvolution_LSeries_eq (ofResidue M χ hχ)
      (norm_ofResidue_le_one M χ hχ) s hs]

theorem fullIdealZeta_eq_dirichlet_product (s : ℂ) (hs : 1 < s.re) :
    CubicEisenstein.fullIdealZeta s = riemannZeta s *
      (ShortDraftHeckeBridge.baseChangeChar (1 : DirichletCharacter ℂ 1)).LFunction s := by
  let a := normWeight 0
  have ha (I : Ideal O) : ‖a I‖ ≤ 1 := by
    by_cases hI : I = ⊥ <;> simp [a, normWeight, CubicEisenstein.fullIdealWeight, hI]
  have hchar (n : ℕ) : (1 : DirichletCharacter ℂ 1) n = 1 := by
    rw [Subsingleton.elim (n : ZMod 1) 1, map_one]
  have hseries : series a s = CubicEisenstein.fullIdealZeta s := by
    apply tsum_congr
    intro I
    by_cases hI : I = ⊥ <;>
      simp [weighted, a, normWeight, CubicEisenstein.fullIdealWeight, hI]
  have hinverse : inverseSeries a s =
      LSeries (ShortDraftHeckeBridge.pairInverseCoeff (1 : DirichletCharacter ℂ 1)
        (ShortDraftHeckeBridge.baseChangeChar (1 : DirichletCharacter ℂ 1))) s := by
    rw [← ShortDraftHeckeBridge.normFiber_LSeries_eq_pair_inverse
      (1 : DirichletCharacter ℂ 1) (ShortDraftHeckeBridge.baseChangeChar (1 : DirichletCharacter ℂ 1))
      (ShortDraftHeckeBridge.baseChangeWeight (1 : DirichletCharacter ℂ 1))
      (ShortDraftHeckeBridge.normFiberCoeff_baseChange_eq_pairInverseCoeff (1 : DirichletCharacter ℂ 1)) s]
    rw [← SmoothMobiusCorrection.idealDirichlet_eq_LSeries
      (ShortDraftHeckeBridge.baseChangeWeight (1 : DirichletCharacter ℂ 1))
      (ConcretePrimeRowBridge.baseChangeWeight_norm_le_one (1 : DirichletCharacter ℂ 1)) s hs]
    apply tsum_congr
    intro I
    by_cases hI : I = ⊥ <;>
      simp [weighted, a, normWeight, CubicEisenstein.fullIdealWeight,
        ShortDraftHeckeBridge.baseChangeWeight, hI, hchar]
  have hi := inverseSeries_mul_series a ha s hs
  have hp := ShortDraftHeckeBridge.pair_inverse_euler_identity
    (1 : DirichletCharacter ℂ 1) (ShortDraftHeckeBridge.baseChangeChar (1 : DirichletCharacter ℂ 1)) s hs
  rw [← hinverse, DirichletCharacter.LFunction_modOne_eq] at hp
  rw [← hseries]
  calc
    series a s = 1 * series a s := (one_mul _).symm
    _ = ((riemannZeta s *
        (ShortDraftHeckeBridge.baseChangeChar (1 : DirichletCharacter ℂ 1)).LFunction s) *
          inverseSeries a s) * series a s := by rw [hp]
    _ = _ := by rw [mul_assoc, hi, mul_one]

theorem regularizedIdealZeta_differentiable : Differentiable ℂ regularizedIdealZeta :=
  (DirichletCharacter.differentiable_LFunctionTrivChar₁ 1).mul
    (DirichletCharacter.differentiable_LFunction
      (ShortDraftHeckeBridge.baseChangeChar_ne_one_of_one
        (1 : DirichletCharacter ℂ 1) rfl))

theorem regularizedIdealZeta_eq (s : ℂ) (hs : 1 < s.re) :
    regularizedIdealZeta s = (s - 1) * CubicEisenstein.fullIdealZeta s := by
  have hs1 : s ≠ 1 := by intro he; simp only [he, one_re, lt_self_iff_false] at hs
  rw [regularizedIdealZeta, DirichletCharacter.LFunctionTrivChar₁,
    Function.update_of_ne hs1, DirichletCharacter.LFunctionTrivChar,
    DirichletCharacter.LFunction_modOne_eq, fullIdealZeta_eq_dirichlet_product s hs,
    mul_assoc]

theorem regularizedIdealZeta_neg_two : regularizedIdealZeta (-2 : ℝ) = 0 := by
  have hz := riemannZeta_neg_two_mul_nat_add_one 0
  rw [Nat.cast_zero, zero_add, mul_one] at hz
  rw [regularizedIdealZeta, DirichletCharacter.LFunctionTrivChar₁,
    Function.update_of_ne (by norm_num : (-2 : ℝ) ≠ (1 : ℂ)),
    DirichletCharacter.LFunctionTrivChar, DirichletCharacter.LFunction_modOne_eq]
  simp only [ofReal_neg, ofReal_ofNat, hz, mul_zero, zero_mul]

theorem differentiable_dslope_of_entire (F : ℂ → ℂ) (hF : Differentiable ℂ F) (c : ℂ) :
    Differentiable ℂ (dslope F c) := by
  rw [← differentiableOn_univ]
  exact (Complex.differentiableOn_dslope (Filter.univ_mem : Set.univ ∈ 𝓝 c)).mpr
    hF.differentiableOn

theorem quadratic_one_ne_zero_of_regularized_zeta (M : Ideal O) [Finite (O ⧸ M)]
    (χ : MulChar (O ⧸ M) ℂ) (hχ : UnitInvariant M χ) (hquad : χ ^ 2 = 1)
    (L R : ℂ → ℂ) (hL : Differentiable ℂ L) (hR : Differentiable ℂ R)
    (hLeq : ∀ s : ℂ, 1 < s.re → L s = series (ofResidue M χ hχ) s)
    (hReq : ∀ s : ℂ, 1 < s.re → R s = (s - 1) * CubicEisenstein.fullIdealZeta s)
    (y : ℝ) (hRy : R y = 0) : L 1 ≠ 0 := by
  intro hz
  let F : ℂ → ℂ := fun s => R s * dslope L 1 s
  have hF : Differentiable ℂ F := hR.mul (differentiable_dslope_of_entire L hL 1)
  have hEq (s : ℂ) (hs : 1 < s.re) :
      F s = series (ofResidue M χ hχ) s * CubicEisenstein.fullIdealZeta s := by
    have hs1 : s ≠ 1 := by intro he; simp only [he, one_re, lt_self_iff_false] at hs
    dsimp only [F]
    rw [hReq s hs, dslope_of_ne L hs1, slope, smul_eq_mul, vsub_eq_sub, hz, sub_zero,
      hLeq s hs]
    field_simp
  have hpos := quadratic_product_positive M χ hχ hquad F hF hEq y
  have hzero : F y = 0 := by simp only [F, hRy, zero_mul]
  exact hzero.not_gt hpos

theorem quadratic_one_ne_zero_of_entire (M : Ideal O) [Finite (O ⧸ M)]
    (χ : MulChar (O ⧸ M) ℂ) (hχ : UnitInvariant M χ) (hquad : χ ^ 2 = 1)
    (L : ℂ → ℂ) (hL : Differentiable ℂ L)
    (hLeq : ∀ s : ℂ, 1 < s.re → L s = series (ofResidue M χ hχ) s) : L 1 ≠ 0 :=
  quadratic_one_ne_zero_of_regularized_zeta M χ hχ hquad L regularizedIdealZeta hL
    regularizedIdealZeta_differentiable hLeq regularizedIdealZeta_eq (-2)
    regularizedIdealZeta_neg_two

theorem normWeight_real_nonneg (x : ℝ) (B : Ideal O) : 0 ≤ normWeight (x : ℂ) B := by
  change 0 ≤ CubicEisenstein.fullIdealWeight (x : ℂ) B
  unfold CubicEisenstein.fullIdealWeight
  split_ifs
  · exact le_rfl
  · rw [← ofReal_natCast, ← ofReal_neg, ← ofReal_cpow (Nat.cast_nonneg _)]
    exact_mod_cast Real.rpow_nonneg (Nat.cast_nonneg (Ideal.absNorm B)) (-x)

theorem norm_series_le_norm_fullIdealZeta (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (x : ℝ) (hx : 1 < x) : ‖series a (x : ℂ)‖ ≤ ‖CubicEisenstein.fullIdealZeta (x : ℂ)‖ := by
  have hs : 1 < (x : ℂ).re := hx
  have hweight (I : Ideal O) :
      CubicEisenstein.fullIdealWeight (x : ℂ) I = (‖CubicEisenstein.fullIdealWeight (x : ℂ) I‖ : ℂ) :=
    eq_coe_norm_of_nonneg (normWeight_real_nonneg x I)
  have hnorm : ‖CubicEisenstein.fullIdealZeta (x : ℂ)‖ =
      ∑' I : Ideal O, ‖CubicEisenstein.fullIdealWeight (x : ℂ) I‖ := by
    unfold CubicEisenstein.fullIdealZeta
    rw [tsum_congr hweight, ← ofReal_tsum,
      Complex.norm_of_nonneg (tsum_nonneg (fun _ => norm_nonneg _))]
  rw [hnorm]
  refine (norm_tsum_le_tsum_norm (weighted_summable_norm a ha _ hs)).trans ?_
  apply Summable.tsum_le_tsum _ (weighted_summable_norm a ha _ hs)
    (CubicEisenstein.fullIdealWeight_summable_norm _ hs)
  intro I
  change ‖a I * CubicEisenstein.fullIdealWeight (x : ℂ) I‖ ≤ _
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (ha I)

theorem fullIdealZeta_isBigO_near_one_horizontal :
    (fun x : ℝ => CubicEisenstein.fullIdealZeta (1 + x)) =O[𝓝[>] 0]
      fun x => (1 : ℂ) / x := by
  have hR : (fun x : ℝ => regularizedIdealZeta (1 + x)) =O[𝓝[>] 0]
      fun _ => (1 : ℂ) := by
    simpa only [ofReal_zero, mul_zero, add_zero] using horizontal_isBigO_one
      regularizedIdealZeta 0 (by simpa using (regularizedIdealZeta_differentiable 1).continuousAt)
  have hB : (fun x : ℝ => (x : ℂ) * CubicEisenstein.fullIdealZeta (1 + x)) =O[𝓝[>] 0]
      fun _ => (1 : ℂ) := hR.congr'
    (eventually_nhdsWithin_of_forall (fun x hx => by
      dsimp only
      rw [regularizedIdealZeta_eq _ (by simpa using hx), add_sub_cancel_left]))
    (Filter.EventuallyEq.refl _ _)
  exact (isBigO_mul_iff_isBigO_div (eventually_nhdsWithin_of_forall
    (fun x hx => ofReal_ne_zero.mpr (ne_of_gt hx)))).mp hB

theorem series_isBigO_near_one_horizontal (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1) :
    (fun x : ℝ => series a (1 + x)) =O[𝓝[>] 0] fun x => (1 : ℂ) / x := by
  have h : (fun x : ℝ => series a (1 + x)) =O[𝓝[>] 0]
      fun x => CubicEisenstein.fullIdealZeta (1 + x) := by
    apply IsBigO.of_bound'
    apply eventually_nhdsWithin_of_forall
    intro x hx
    change 0 < x at hx
    simpa only [ofReal_add, ofReal_one] using
      norm_series_le_norm_fullIdealZeta a ha (1 + x) (by linarith)
  exact h.trans fullIdealZeta_isBigO_near_one_horizontal

theorem residue_boundary_ne_zero_of_series_eq (M : Ideal O) [Finite (O ⧸ M)]
    (χ : MulChar (O ⧸ M) ℂ) (hχ : UnitInvariant M χ) (L L₂ : ℂ → ℂ)
    (hEq : ∀ s : ℂ, 1 < s.re → L s = series (ofResidue M χ hχ) s)
    (hEq₂ : ∀ s : ℂ, 1 < s.re → L₂ s =
      series (ofResidue M (χ ^ 2) (square_unitInvariant M χ hχ)) s)
    (t : ℝ) (hL : DifferentiableAt ℂ L (1 + I * t))
    (hL₂ : ContinuousAt L₂ (1 + 2 * I * t)) : L (1 + I * t) ≠ 0 :=
  boundary_ne_zero_of_series_eq
    (ofResidue M 1 (one_unitInvariant M)) (ofResidue M χ hχ)
    (ofResidue M (χ ^ 2) (square_unitInvariant M χ hχ))
    (norm_ofResidue_le_one M 1 (one_unitInvariant M))
    (norm_ofResidue_le_one M χ hχ)
    (norm_ofResidue_le_one M (χ ^ 2) (square_unitInvariant M χ hχ))
    (ofResidue_primeTriple M χ hχ)
    (series (ofResidue M 1 (one_unitInvariant M))) L L₂ (fun _ _ => rfl)
    hEq hEq₂ t
    (series_isBigO_near_one_horizontal _ (norm_ofResidue_le_one M 1 (one_unitInvariant M)))
    hL hL₂

end Quadratic

end

end SevenEighths.HeckeBoundary

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.Theta
namespace OAI

noncomputable section
open Filter Asymptotics Set MeasureTheory
open scoped Topology BigOperators
namespace SevenEighths.HeckeTheta
open EisensteinTheta

theorem completed_differentiableAt {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ)
    {s : ℂ} (hs₀ : s ≠ 0) (hs₁ : s ≠ 1) : DifferentiableAt ℂ (completed w) s :=
  (pair w).differentiableAt_Λ (Or.inl hs₀) (Or.inl (by simpa using hs₁))

theorem completed_differentiableAt_of_mean_zero {N : ℕ} [NeZero N]
    (w : Fin N × Fin N → ℂ) (hw : ∑ a, w a = 0) {s : ℂ} (hs₀ : s ≠ 0) :
    DifferentiableAt ℂ (completed w) s :=
  (pair w).differentiableAt_Λ (Or.inl hs₀) (Or.inr (pair_g₀_eq_zero w hw))

theorem latticeL_differentiableAt {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ)
    {s : ℂ} (hs₀ : s ≠ 0) (hs₁ : s ≠ 1 ∨ ∑ a, w a = 0) :
    DifferentiableAt ℂ (latticeL w) s := by
  have hΛ : DifferentiableAt ℂ (completed w) s := by
    rcases hs₁ with hs₁ | hw
    · exact completed_differentiableAt w hs₀ hs₁
    · exact completed_differentiableAt_of_mean_zero w hw hs₀
  exact (((differentiable_id.const_cpow (Or.inl
    (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))).differentiableAt).mul
      (Complex.differentiable_one_div_Gamma s)).mul hΛ

end SevenEighths.HeckeTheta

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.Family
namespace OAI

noncomputable section
open scoped BigOperators
namespace SevenEighths.HeckeFamily

theorem continuedLattice_differentiableAt (χ : Character) {s : ℂ}
    (hs₀ : s ≠ 0) (hs₁ : s ≠ 1 ∨ ∑ a, (coefficients χ) a = 0) :
    DifferentiableAt ℂ (continuedLattice χ) s :=
  HeckeTheta.latticeL_differentiableAt (coefficients χ) hs₀ hs₁

end SevenEighths.HeckeFamily

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.CharacterAnalytic
namespace OAI

noncomputable section
open scoped BigOperators
namespace SevenEighths.HeckeCharacterAnalytic

theorem continuedLattice_differentiableAt_nonprincipal (χ : HeckeFamily.Character)
    (hχ : χ.residue ≠ 1) {s : ℂ} (hs₀ : s ≠ 0) :
    DifferentiableAt ℂ (HeckeFamily.continuedLattice χ) s :=
  HeckeFamily.continuedLattice_differentiableAt χ hs₀
    (Or.inr (coefficients_sum_eq_zero χ hχ))

end SevenEighths.HeckeCharacterAnalytic

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.IdealBridge
namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.HeckeFamily

theorem LFunction_differentiableAt (χ : Character) {s : ℂ}
    (hs₀ : s ≠ 0) (hs₁ : s ≠ 1 ∨ χ.residue ≠ 1) :
    DifferentiableAt ℂ (LFunction χ) s := by
  apply DifferentiableAt.div_const
  rcases hs₁ with hs₁ | hχ
  · exact continuedLattice_differentiableAt χ hs₀ (Or.inl hs₁)
  · exact HeckeCharacterAnalytic.continuedLattice_differentiableAt_nonprincipal χ hχ hs₀

end SevenEighths.HeckeFamily

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.BoundaryIntegration
namespace OAI

noncomputable section
namespace SevenEighths.HeckeFamily

theorem LFunction_one_ne_zero_quadratic (χ : Character)
    (hχ : χ.residue ≠ 1) (hquad : χ.residue ^ 2 = 1) : LFunction χ 1 ≠ 0 := by
  let : Finite (O ⧸ χ.modulus) :=
    Ring.HasFiniteQuotients.finiteQuotient χ.modulus_ne_bot
  exact HeckeBoundary.quadratic_one_ne_zero_of_entire χ.modulus χ.residue
    χ.unit_trivial hquad (LFunction χ) (LFunction_entire_nonprincipal χ hχ)
      (fun s hs => LFunction_eq_series χ hs)

theorem LFunction_boundary_ne_zero (χ : Character) (t : ℝ)
    (hpole : t ≠ 0 ∨ χ.residue ≠ 1)
    (hsquare : t ≠ 0 ∨ χ.residue ^ 2 ≠ 1) :
    LFunction χ (1 + Complex.I * t) ≠ 0 := by
  let : Finite (O ⧸ χ.modulus) :=
    Ring.HasFiniteQuotients.finiteQuotient χ.modulus_ne_bot
  have h1 (t : ℝ) (ht : t ≠ 0) : (1 + Complex.I * t : ℂ) ≠ 1 := by
    intro h
    have hi := congrArg Complex.im h
    simp only [Complex.add_im, Complex.one_im, Complex.mul_im, Complex.I_re,
      Complex.ofReal_im, Complex.I_im, Complex.ofReal_re, zero_mul, one_mul,
      zero_add] at hi
    exact ht hi
  have h0 (t : ℝ) : (1 + Complex.I * t : ℂ) ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    norm_num at hr
  apply HeckeBoundary.residue_boundary_ne_zero_of_series_eq χ.modulus χ.residue
    χ.unit_trivial (LFunction χ) (LFunction (χ.power 2))
    (fun s hs => LFunction_eq_series χ hs)
    (fun s hs => LFunction_eq_series (χ.power 2) hs) t
  · apply LFunction_differentiableAt χ (h0 t)
    exact hpole.imp (h1 t) id
  · have heq : (1 + 2 * Complex.I * t : ℂ) = 1 + Complex.I * (2 * t : ℝ) := by
      push_cast
      ring
    rw [heq]
    apply DifferentiableAt.continuousAt (𝕜 := ℂ)
    apply LFunction_differentiableAt (χ.power 2) (h0 (2*t))
    rcases hsquare with ht | hsq
    · exact Or.inl (h1 (2*t) (mul_ne_zero (by norm_num) ht))
    · exact Or.inr hsq

theorem LFunction_one_ne_zero_nonprincipal (χ : Character) (hχ : χ.residue ≠ 1) :
    LFunction χ 1 ≠ 0 := by
  by_cases hquad : χ.residue ^ 2 = 1
  · exact LFunction_one_ne_zero_quadratic χ hχ hquad
  · simpa only [Complex.ofReal_zero, mul_zero, add_zero] using
      LFunction_boundary_ne_zero χ 0 (Or.inr hχ) (Or.inr hquad)

theorem LFunction_ne_zero_of_re_eq_one (χ : Character) {s : ℂ}
    (hs : s.re = 1) (hpole : s ≠ 1 ∨ χ.residue ≠ 1) : LFunction χ s ≠ 0 := by
  have heq : s = 1 + Complex.I * s.im := by
    apply Complex.ext <;> simp [hs]
  by_cases ht : s.im = 0
  · have hs1 : s = 1 := by rw [heq, ht]; simp
    subst s
    exact LFunction_one_ne_zero_nonprincipal χ (hpole.resolve_left (not_not.mpr rfl))
  · rw [heq]
    exact LFunction_boundary_ne_zero χ s.im (Or.inl ht) (Or.inl ht)

theorem LFunction_ne_zero_of_one_le_re_oai (χ : Character) {s : ℂ}
    (hs : 1 ≤ s.re) (hpole : s ≠ 1 ∨ χ.residue ≠ 1) : LFunction χ s ≠ 0 := by
  rcases eq_or_lt_of_le hs with h | h
  · exact LFunction_ne_zero_of_re_eq_one χ h.symm hpole
  · exact LFunction_ne_zero_of_one_lt_re χ h

end SevenEighths.HeckeFamily

end

end OAI
end

theorem solution : type_of% @OAI.SevenEighths.HeckeFamily.LFunction_ne_zero_of_one_le_re_oai := @OAI.SevenEighths.HeckeFamily.LFunction_ne_zero_of_one_le_re_oai
