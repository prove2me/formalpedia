-- Prove2me | solution 1 for OAI.SevenEighths.CenteredMomentDetectorPlainExceptional.source_batch_plain_retained
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T02:27:19.337311+00:00
-- url     : https://prove2.me/submissions/c2b8c142-04b9-48d0-82ac-eb8a079b6405

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B028
import Theorems.Thm_OAI_SevenEighths_CenteredMomentDetectorPlainExceptional_retained_positive_energy_le_source

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.GaussSum.FiniteFourier
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

namespace ActualEisensteinCubic

theorem quotient_char_ne_two_of_two_not_mem (P : Ideal O) [P.IsMaximal]
    (h2 : (2 : O) ∉ P) : ringChar (O ⧸ P) ≠ 2 := by
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  intro heq
  have hz : ((ringChar (O ⧸ P) : ℕ) : O ⧸ P) = 0 := ringChar.Nat.cast_ringChar
  rw [heq] at hz
  apply h2
  exact (Ideal.Quotient.eq_zero_iff_mem).mp (by simpa only [map_ofNat, Nat.cast_ofNat] using hz)

end ActualEisensteinCubic

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Eisenstein.ConstantTermSupport
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
open scoped BigOperators

open scoped BigOperators Classical
namespace CanonicalQuadraticSieve

open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss ConcretePrimeRowBridge
open EisensteinSchwartzPoisson GaussGeneratorTransport PrimaryIdealUnitReindex

theorem badPrime_injective : Function.Injective badPrime := by
  have hgood : lambda ∉ (Ideal.span {(2 : O)} : Ideal O) := by
    have hg := cubicTwoIdeal_good
    change lambda ∉ cubicTwoIdeal at hg
    simpa only [cubicTwoIdeal, Ideal.span_singleton_neg] using hg
  intro i j hij
  cases i <;> cases j
  · rfl
  · exfalso
    apply hgood
    have he : (Ideal.span {lambda} : Ideal O) = Ideal.span {(2 : O)} := hij
    rw [← he]
    exact Ideal.subset_span (by simp)
  · exfalso
    apply hgood
    have he : (Ideal.span {(2 : O)} : Ideal O) = Ideal.span {lambda} := hij
    rw [he]
    exact Ideal.subset_span (by simp)
  · rfl

end CanonicalQuadraticSieve

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.Operations
namespace OAI

noncomputable section
namespace SevenEighths.HeckeFamily

theorem elementCoeff_inverse (χ : Character) (z : O) :
    elementCoeff χ.inverse z = (elementCoeff χ z)⁻¹ := by
  exact MulChar.inv_apply_eq_inv' _ _

end SevenEighths.HeckeFamily

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.ExceptionalRows
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.HeckeExceptionalRows
open HeckeFamily UniqueFactorizationMonoid

theorem row_ideal_dvd (S : Finset (Ideal O)) {u : O} (hu : u ∈ rows S) :
    (Ideal.span {u} : Ideal O) ∣ (∏ P ∈ S, P)^5 := by
  have hI : (Ideal.span {u} : Ideal O) ≠ ⊥ := Ideal.span_singleton_eq_bot.not.mpr hu.1
  have hle : normalizedFactors (Ideal.span {u}) ≤ 5 • S.val := by
    apply Multiset.le_iff_count.mpr
    intro P
    by_cases hP : P ∈ normalizedFactors (Ideal.span {u})
    · have hp := hu.2 P hP
      have hc : S.val.count P = 1 := Multiset.count_eq_one_of_mem S.nodup hp.1
      rw [Multiset.count_nsmul, hc]
      omega
    · simp only [Multiset.count_eq_zero.mpr hP]
      exact Nat.zero_le _
  have hd := Multiset.prod_dvd_prod_of_le hle
  rw [Ideal.prod_normalizedFactors_eq_self hI, Multiset.prod_nsmul] at hd
  change (Ideal.span {u} : Ideal O) ∣ (S.prod id)^5
  simpa only [Finset.prod_val] using hd

theorem row_norm_bound (S : Finset (Ideal O)) (hS : ∀ P ∈ S, Prime P)
    {u : O} (hu : u ∈ rows S) : (Ideal.span {u}).absNorm ≤ bound S := by
  have hd := map_dvd Ideal.absNorm (row_ideal_dvd S hu)
  apply Nat.le_of_dvd _ hd
  apply Nat.pos_of_ne_zero
  rw [ne_eq, Ideal.absNorm_eq_zero_iff]
  exact pow_ne_zero _ (Finset.prod_ne_zero_iff.mpr (fun P hP => (hS P hP).ne_zero))

end SevenEighths.HeckeExceptionalRows

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.Canonical
namespace OAI

noncomputable section
open scoped BigOperators Classical
local notation "O" => ActualEisensteinCubic.O
namespace SevenEighths.CenteredMomentCanonical
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
open CenteredMomentCorrelation

theorem actualSextic_order_six (P : Ideal O) [P.IsMaximal]
    (hg : goodLambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2) :
    orderOf (actualSextic P hg) = 6 := by
  let Φ : MulChar (O ⧸ P) O →* MulChar (O ⧸ P) ℂ :=
    MulChar.ringHomCompHom eisEmbedding
  have hΦ : Function.Injective Φ := by
    intro x y h
    apply MulChar.ext
    intro t
    apply eisEmbedding_injective
    exact congrArg (fun f : MulChar (O ⧸ P) ℂ => f t) h
  exact (orderOf_injective Φ hΦ _).trans (sexticChar_order P hg hchar)

end SevenEighths.CenteredMomentCanonical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CenteredExceptionalProfile
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.CenteredExceptionalProfile
open UniqueFactorizationMonoid HeckeFamily CanonicalRowCompletion
open ConcretePrimeRowBridge hiding O
open CompletedGauss hiding O
open ConcreteTraceCRT
local notation "O" => HeckeFamily.O
open CenteredExceptionalCount CenteredMomentCanonical
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

theorem split_at_prime (I P : Ideal O) (hI : I ≠ 0) [P.IsMaximal] :
    ∃ J : Ideal O, I = P ^ valuation I P * J ∧ J ≠ 0 ∧ IsCoprime J P := by
  let S := (normalizedFactors I).toFinset
  let J := ∏ Q ∈ S.erase P, Q ^ valuation I Q
  have hsplit : I = P ^ valuation I P * J := by
    calc
      I = (normalizedFactors I).prod := (Ideal.prod_normalizedFactors_eq_self hI).symm
      _ = ∏ Q ∈ S, Q ^ valuation I Q := Finset.prod_multiset_count _
      _ = P ^ valuation I P * J := by
        by_cases hP : P ∈ S
        · exact (Finset.mul_prod_erase S (fun Q => Q ^ valuation I Q) hP).symm
        · have hz : valuation I P = 0 := Multiset.count_eq_zero.mpr
            (fun h => hP (Multiset.mem_toFinset.mpr h))
          simp only [J, Finset.erase_eq_of_notMem hP, hz, pow_zero, one_mul]
  refine ⟨J, hsplit, ?_, ?_⟩
  · intro hz
    apply hI
    rw [hsplit, hz, mul_zero]
  · apply IsCoprime.prod_left
    intro Q hQ
    obtain ⟨hQP, hQS⟩ := Finset.mem_erase.mp hQ
    have hp := prime_of_normalized_factor Q (Multiset.mem_toFinset.mp hQS)
    let : Q.IsMaximal := (Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero
    exact (Ideal.isCoprime_of_isMaximal hQP).pow_left

theorem exists_unit_probe (Q K P : Ideal O) (hK : K ≠ 0) [P.IsMaximal]
    (hQP : IsCoprime Q P) (u : (O ⧸ P)ˣ) :
    ∃ n : O, n - 1 ∈ Q ∧ IsCoprime (Ideal.span {n}) K ∧
      Ideal.Quotient.mk P n = (u : O ⧸ P) := by
  obtain ⟨J, hsplit, hJ, hJP⟩ := split_at_prime K P hK
  let e := Ideal.quotientInfEquivQuotientProd (Q * J) P (hQP.mul_left hJP)
  obtain ⟨x, hx⟩ := e.surjective ((1 : O ⧸ Q * J), (u : O ⧸ P))
  obtain ⟨n, rfl⟩ := Ideal.Quotient.mk_surjective x
  change (Ideal.Quotient.mk (Q * J) n, Ideal.Quotient.mk P n) = (1, (u : O ⧸ P)) at hx
  have hnQJ := congrArg Prod.fst hx
  have hnP := congrArg Prod.snd hx
  dsimp only at hnQJ hnP
  have hn : n - 1 ∈ Q * J := Ideal.Quotient.eq.mp (by simpa using hnQJ)
  have hnJ : Ideal.Quotient.mk J n = 1 :=
    (Ideal.Quotient.mk_eq_one_iff_sub_mem _).mpr (Ideal.mul_le_right hn)
  have hcJ : IsCoprime (Ideal.span {n}) J :=
    (IdealCharacter.isUnit_mk_iff_isCoprime _ _).mp (hnJ ▸ isUnit_one)
  have hcP : IsCoprime (Ideal.span {n}) P :=
    (IdealCharacter.isUnit_mk_iff_isCoprime _ _).mp (hnP ▸ u.isUnit)
  refine ⟨n, Ideal.mul_le_left hn, ?_, hnP⟩
  rw [hsplit]
  exact hcP.pow_right.mul_right hcJ

theorem valuation_mod_six_of_unit_agreement (Q K I J P : Ideal O)
    (hK : K ≠ 0) (hI : CanonicalQuadraticSieve.Supported I)
    (hJ : CanonicalQuadraticSieve.Supported J) [P.IsMaximal]
    (hg : λ₀ ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    (hQP : IsCoprime Q P)
    (heq : ∀ n : O, n - 1 ∈ Q → IsCoprime (Ideal.span {n}) K →
      idealRowHom n I = idealRowHom n J) :
    valuation I P % 6 = valuation J P % 6 := by
  obtain ⟨I₀, hsplitI, hI₀, hcI⟩ := split_at_prime I P hI.1
  obtain ⟨J₀, hsplitJ, hJ₀, hcJ⟩ := split_at_prime J P hJ.1
  have hsI : CanonicalQuadraticSieve.Supported I₀ :=
    ((CanonicalQuadraticSieve.supported_mul_iff _ _).mp (hsplitI ▸ hI)).2
  have hsJ : CanonicalQuadraticSieve.Supported J₀ :=
    ((CanonicalQuadraticSieve.supported_mul_iff _ _).mp (hsplitJ ▸ hJ)).2
  have hpows : actualSextic P hg ^ valuation I P = actualSextic P hg ^ valuation J P := by
    apply MulChar.ext
    intro u
    obtain ⟨n, hn, hcK, hnP⟩ := exists_unit_probe (Q * I₀ * J₀) K P hK
      ((hQP.mul_left hcI).mul_left hcJ) u
    have hval := heq n (Ideal.mul_le_left (Ideal.mul_le_left hn)) hcK
    have hIn : n - 1 ∈ I₀ := Ideal.mul_le_right (Ideal.mul_le_left hn)
    have hJn : n - 1 ∈ J₀ := Ideal.mul_le_right hn
    rw [hsplitI, hsplitJ, map_mul, map_mul, map_pow, map_pow,
      idealRowHom_congr_mod I₀ n 1 hIn, idealRowHom_congr_mod J₀ n 1 hJn,
      idealRowHom_one_supported I₀ hsI, idealRowHom_one_supported J₀ hsJ,
      mul_one, mul_one, idealRowHom_prime n P hg, hnP] at hval
    simpa only [MulChar.pow_apply_coe] using hval
  have hm := (pow_eq_pow_iff_modEq.mp hpows)
  rw [actualSextic_order_six P hg hchar] at hm
  exact hm

theorem elementCoeff_eq_one_of_inducedBy (χ ψ : Character) (h : InducedBy χ ψ)
    (Q : Ideal O) (hQ : Q ≠ ⊤) (hψ : Q ≤ ψ.modulus)
    (n : O) (hn : n - 1 ∈ Q) (hc : IsCoprime (Ideal.span {n}) χ.modulus) :
    elementCoeff χ n = 1 := by
  have hn0 : n ≠ 0 := by
    intro hz
    have h1 : (1 : O) ∈ Q := by simpa [hz] using Q.neg_mem hn
    exact hQ ((Ideal.eq_top_iff_one Q).mpr h1)
  rw [elementCoeff_eq_of_inducedBy χ ψ h n hn0 hc]
  change ψ.residue (Ideal.Quotient.mk ψ.modulus n) = 1
  rw [(Ideal.Quotient.mk_eq_one_iff_sub_mem _).mpr (hψ hn), map_one]

theorem actual_row_on_fixed_units (η χ : Character) (m f z : O)
    (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m)
    (u : Oˣ) (a b : ℕ) (r : O)
    (hr : CanonicalQuadraticSieve.Supported (Ideal.span {r}))
    (hpr : λ₀ ^ 2 ∣ r - 1)
    (hx : f ^ 4 * z = (u : O) * λ₀ ^ a * (2 : O) ^ b * r)
    (hχ : ∀ n, elementCoeff χ n = rowTwist (HeckeRowClosure.elementHom η) m f z n)
    (n : O) (hn : n - 1 ∈ Ideal.span {(72 : O)})
    (hc : IsCoprime (Ideal.span {n}) (Ideal.span {m})) :
    elementCoeff χ n = elementCoeff η n * idealRowHom n (Ideal.span {r}) := by
  have hd72 : λ₀ ^ 2 ∣ (72 : O) := ActualEisensteinCubic.lambda_sq_dvd_three.trans
    (show (3 : O) ∣ 72 from ⟨24, by norm_num⟩)
  have hp : λ₀ ^ 2 ∣ n - 1 := hd72.trans (Ideal.mem_span_singleton.mp hn)
  rw [hχ n, rowTwist_eq_actualPeriodicRow_primary _ _ _ _ hmLam hm2 u a b r hr hpr hx n hp]
  change ((elementCoeff η n * coprimalityMask m n) * numeratorBadTwist u a b r hr n) *
    idealRowHom n (Ideal.span {r}) = _
  have hm : coprimalityMask m n = 1 := by
    change (if IsCoprime m n then (1 : ℂ) else 0) = 1
    simp only [((Ideal.isCoprime_span_singleton_iff _ _).mp hc).symm, ite_true]
  rw [hm, numeratorBadTwist_periodic u a b r hr n 1 hn, map_one, mul_one, mul_one]

theorem valuation_span_eq_zero_of_not_mem (x : O) (P : Ideal O) (hx : x ∉ P) :
    valuation (Ideal.span {x}) P = 0 := by
  have hx0 : x ≠ 0 := fun hz => hx (hz ▸ P.zero_mem)
  apply Multiset.count_eq_zero.mpr
  intro hP
  have hle := ((Ideal.mem_normalizedFactors_iff (Ideal.span_singleton_eq_bot.not.mpr hx0)).mp hP).2
  exact hx (hle (Ideal.subset_span (by simp)))

theorem valuation_supported_numerator (x : O) (u : Oˣ) (a b : ℕ) (r : O)
    (hr : r ≠ 0) (hx : x = (u : O) * λ₀ ^ a * (2 : O) ^ b * r)
    (P : Ideal O) (hg : λ₀ ∉ P) (h2 : (2 : O) ∉ P) :
    valuation (Ideal.span {x}) P = valuation (Ideal.span {r}) P := by
  have hu : Ideal.span {(u : O)} = (1 : Ideal O) := by
    simpa only [Ideal.one_eq_top] using (Ideal.span_singleton_eq_top.mpr u.isUnit)
  have hl0 : Ideal.span {λ₀} ≠ (0 : Ideal O) :=
    Ideal.span_singleton_eq_bot.not.mpr PrimaryIdealUnitReindex.lambda_prime_actual.ne_zero
  have h20 : Ideal.span {(2 : O)} ≠ (0 : Ideal O) :=
    Ideal.span_singleton_eq_bot.not.mpr (by norm_num)
  have hr0 : Ideal.span {r} ≠ (0 : Ideal O) := Ideal.span_singleton_eq_bot.not.mpr hr
  rw [hx]
  simp only [← Ideal.span_singleton_mul_span_singleton, ← Ideal.span_singleton_pow, hu, one_mul]
  rw [valuation_mul _ _ _ (mul_ne_zero (pow_ne_zero _ hl0) (pow_ne_zero _ h20)) hr0,
    valuation_mul _ _ _ (pow_ne_zero _ hl0) (pow_ne_zero _ h20), valuation_pow, valuation_pow,
    valuation_span_eq_zero_of_not_mem λ₀ P hg, valuation_span_eq_zero_of_not_mem (2 : O) P h2]
  omega

theorem local_row_valuation_zero (η χ ψ : Character) (h : InducedBy χ ψ)
    (Q K I P : Ideal O) (hQ : Q ≠ ⊤) (hK : K ≠ 0)
    (hψ : Q ≤ ψ.modulus) (hI : CanonicalQuadraticSieve.Supported I)
    [P.IsMaximal] (hg : λ₀ ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    (hQP : IsCoprime Q P) (hηP : IsCoprime η.modulus P)
    (hrow : ∀ n : O, n - 1 ∈ Q → IsCoprime (Ideal.span {n}) K →
      elementCoeff χ n = elementCoeff η n * idealRowHom n I) :
    valuation I P % 6 = 0 := by
  have hzero : valuation (1 : Ideal O) P % 6 = 0 := by
    simp only [valuation, normalizedFactors_one, Multiset.count_zero, Nat.zero_mod]
  rw [← hzero]
  apply valuation_mod_six_of_unit_agreement (Q * η.modulus) (K * χ.modulus) I 1 P
    (mul_ne_zero hK χ.modulus_ne_bot) hI
    (by constructor; exact one_ne_zero; simp only [normalizedFactors_one, Multiset.notMem_zero, false_implies, implies_true]) hg hchar
    (hQP.mul_left hηP)
  intro n hn hc
  obtain ⟨hcK, hcχ⟩ := IsCoprime.mul_right_iff.mp hc
  have hnQ := Ideal.mul_le_left hn
  have hη : elementCoeff η n = 1 := by
    change η.residue (Ideal.Quotient.mk η.modulus n) = 1
    rw [(Ideal.Quotient.mk_eq_one_iff_sub_mem _).mpr (Ideal.mul_le_right hn), map_one]
  have he := elementCoeff_eq_one_of_inducedBy χ ψ h Q hQ hψ n hnQ hcχ
  rw [hrow n hnQ hcK, hη, one_mul] at he
  simpa only [map_one] using he

theorem actual_row_numerator_valuation_zero (η χ ψ : Character) (h : InducedBy χ ψ)
    (Q : Ideal O) (hQ : Q ≠ ⊤) (hQ72 : Q ≤ Ideal.span {(72 : O)}) (hψ : Q ≤ ψ.modulus)
    (m f z : O) (hm : m ≠ 0) (hf : f ≠ 0) (hz : z ≠ 0)
    (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m)
    (hχ : ∀ n, elementCoeff χ n = rowTwist (HeckeRowClosure.elementHom η) m f z n)
    (P : Ideal O) [P.IsMaximal] (hg : λ₀ ∉ P) (h2 : (2 : O) ∉ P)
    (hQP : IsCoprime Q P) (hηP : IsCoprime η.modulus P) :
    valuation (Ideal.span {f ^ 4 * z}) P % 6 = 0 := by
  obtain ⟨u, a, b, r, hr, hpr, hx⟩ :=
    exists_supported_numerator_factorization (f ^ 4 * z) (mul_ne_zero (pow_ne_zero _ hf) hz)
  rw [valuation_supported_numerator _ u a b r (Ideal.span_singleton_eq_bot.not.mp hr.1) hx P hg h2]
  apply local_row_valuation_zero η χ ψ h Q (Ideal.span {m}) (Ideal.span {r}) P hQ
    (Ideal.span_singleton_eq_bot.not.mpr hm) hψ hr hg
    (ActualEisensteinCubic.quotient_char_ne_two_of_two_not_mem P h2) hQP hηP
  intro n hn hc
  exact actual_row_on_fixed_units η χ m f z hmLam hm2 u a b r hr hpr hx hχ n (hQ72 hn) hc

theorem outside_fixed_support (Q : Ideal O) (hQ : Q ≠ 0)
    (hQ72 : Q ≤ Ideal.span {(72 : O)}) (P : Ideal O) (hP : Prime P)
    (hPS : P ∉ (normalizedFactors Q).toFinset) :
    λ₀ ∉ P ∧ (2 : O) ∉ P ∧ IsCoprime Q P := by
  let : P.IsMaximal := (Ideal.isPrime_of_prime hP).isMaximal hP.ne_zero
  have hcop : IsCoprime Q P := by
    apply Ideal.coprime_of_no_prime_ge
    intro J hQJ hPJ hJ
    have hPJ' : P = J := (inferInstance : P.IsMaximal).eq_of_le hJ.ne_top hPJ
    apply hPS
    apply Multiset.mem_toFinset.mpr
    apply (Ideal.mem_normalizedFactors_iff hQ).mpr
    exact ⟨Ideal.isPrime_of_prime hP, hPJ' ▸ hQJ⟩
  have h72 : (72 : O) ∉ P := by
    intro hh
    have hle : Q ≤ P := hQ72.trans ((Ideal.span_singleton_le_iff_mem _).mpr hh)
    have he := Ideal.isCoprime_iff_sup_eq.mp hcop
    rw [sup_eq_right.mpr hle] at he
    exact hP.ne_one (by simpa only [Ideal.one_eq_top] using he)
  have hl : λ₀ ∣ (72 : O) :=
    (dvd_pow_self λ₀ (by decide : (2 : ℕ) ≠ 0)).trans
      (ActualEisensteinCubic.lambda_sq_dvd_three.trans (show (3 : O) ∣ 72 from ⟨24, by norm_num⟩))
  have h2 : (2 : O) ∣ 72 := ⟨36, by norm_num⟩
  refine ⟨?_, ?_, hcop⟩
  · intro hh
    obtain ⟨v, hv⟩ := hl
    exact h72 (hv ▸ P.mul_mem_right v hh)
  · intro hh
    obtain ⟨v, hv⟩ := h2
    exact h72 (hv ▸ P.mul_mem_right v hh)

end SevenEighths.CenteredExceptionalProfile

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.RayPoolGood
namespace OAI

noncomputable section
open scoped Classical Topology
open Filter
namespace SevenEighths.ProbeRaySlots
open HeckeFamily ProbePhysical CanonicalQuadraticSieve PrincipalSignalComparison
local notation "Id" => Ideal HeckeFamily.O

theorem prime_coprime_of_norm_gt (η : Character) (P : PrimeIdeal)
    (hN : (η.modulus.absNorm:ℝ)<(P.val.absNorm:ℝ)) : IsCoprime P.val η.modulus := by
  apply Ideal.coprime_of_no_prime_ge
  intro J hPJ hηJ hJ
  have hmax := (Ideal.isPrime_of_prime P.property).isMaximal P.property.ne_zero
  have heq := hmax.eq_of_le hJ.ne_top hPJ
  rw [←heq] at hηJ
  have hd : P.val∣η.modulus := Ideal.dvd_iff_le.mpr hηJ
  have hn := Nat.le_of_dvd (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr η.modulus_ne_bot))
    (map_dvd Ideal.absNorm hd)
  exact (not_le_of_gt hN) (by exact_mod_cast hn)

end SevenEighths.ProbeRaySlots
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.Dyadic
namespace OAI

noncomputable section
open scoped Classical BigOperators Topology
open MeasureTheory Set
namespace SevenEighths.HeckeDyadic
open HeckeFamily

theorem norm_pos (I : NonzeroIdeal) : 0 < norm I := by
  unfold norm
  exact_mod_cast Nat.pos_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr I.property)

end SevenEighths.HeckeDyadic

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.InverseAmplificationConjugation
namespace OAI

noncomputable section
open scoped Classical ComplexConjugate ContDiff
open Complex
namespace SevenEighths.HeckeInverseAmplification
open HeckeFamily HeckeDyadic

theorem coefficient_inverse_conj (χ : Character) (inv : Bool) (J : Ideal O) :
    coefficient χ.inverse inv J=conj (coefficient χ inv J) := by
  cases inv <;> simp [coefficient,idealCoeff_inverse_conj]

theorem conj_positive_cpow (x : ℝ) (hx : 0<x) (z : ℂ) :
    conj ((x : ℂ)^z)=(x : ℂ)^(conj z) := by
  have hh := Complex.cpow_conj (x : ℂ) z
    (by rw [Complex.arg_ofReal_of_nonneg hx.le]; exact Real.pi_ne_zero.symm)
  simpa only [conj_ofReal] using hh.symm

theorem conj_shift (σ freq : ℝ) : conj (_root_.OAI.SevenEighths.HeckeDyadic.shift σ freq)=_root_.OAI.SevenEighths.HeckeDyadic.shift σ (-freq) := by
  simp only [HeckeDyadic.shift,map_sub,map_mul,conj_ofReal,conj_I,ofReal_neg]
  ring

theorem conj_polynomial (χ : Character) (inv : Bool) (W : ℝ→ℂ)
    (D σ freq : ℝ) (hD : 0<D) :
    conj (polynomial χ inv W D σ freq)=
      polynomial χ.inverse inv (fun x => conj (W x)) D σ (-freq) := by
  unfold polynomial
  rw [map_mul,conj_tsum,conj_positive_cpow D hD]
  have hhalf : conj (-(1/2 : ℂ))= -(1/2 : ℂ) := by
    simp only [map_neg,map_div₀,map_one,map_ofNat]
  rw [hhalf]
  congr 1
  apply tsum_congr
  intro J
  simp only [summand,map_mul,←coefficient_inverse_conj]
  rw [conj_positive_cpow _ (div_pos (norm_pos J) hD),map_neg,conj_shift]

theorem polynomial_inverse_norm (χ : Character) (inv : Bool) (W : ℝ→ℂ)
    (D σ freq : ℝ) (hD : 0<D) :
    ‖polynomial χ.inverse inv (fun x => conj (W x)) D σ (-freq)‖=
      ‖polynomial χ inv W D σ freq‖ := by
  rw [←conj_polynomial χ inv W D σ freq hD,norm_conj]

end SevenEighths.HeckeInverseAmplification

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.DetectorCoefficientTransfer
namespace OAI

noncomputable section
open scoped Classical ComplexConjugate
open Complex
namespace SevenEighths.HeckeDetectorCoefficientTransfer
open HeckeFamily HeckeDyadic HeckeInverseAmplification

theorem polynomial_eq_of_idealCoeff (χ ψ : Character)
    (hc : ∀ J : Ideal O,idealCoeff χ J=idealCoeff ψ J)
    (inv : Bool) (W : ℝ→ℂ) (D σ freq : ℝ) :
    polynomial χ inv W D σ freq=polynomial ψ inv W D σ freq := by
  unfold polynomial
  congr 1
  apply tsum_congr
  intro J
  simp only [summand,coefficient,hc]

theorem norm_of_oriented_coefficients (χ ψ : Character) (reverse : Bool)
    (hc : ∀ J : Ideal O,idealCoeff χ J=
      if reverse then conj (idealCoeff ψ J) else idealCoeff ψ J)
    (inv : Bool) (W : ℝ→ℂ) (D σ freq : ℝ) (hD : 0<D) :
    ‖polynomial χ inv W D σ freq‖=
      ‖polynomial ψ inv (orientedProfile reverse W) D σ (orientedFrequency reverse freq)‖ := by
  cases reverse
  · exact congrArg (fun z : ℂ => ‖z‖) (polynomial_eq_of_idealCoeff χ ψ hc inv W D σ freq)
  · have hc' : ∀ J : Ideal O,idealCoeff χ J=idealCoeff ψ.inverse J := by
      intro J
      simpa only [Bool.true_eq,ite_true,idealCoeff_inverse_conj] using hc J
    rw [polynomial_eq_of_idealCoeff χ ψ.inverse hc' inv W D σ freq]
    have hh := polynomial_inverse_norm ψ inv (fun x => conj (W x)) D σ (-freq) hD
    simpa only [orientedProfile,orientedFrequency,Bool.true_eq,ite_true,conj_conj,neg_neg] using hh

end SevenEighths.HeckeDetectorCoefficientTransfer

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.PrimeRow
namespace OAI

noncomputable section
open scoped Classical ComplexConjugate BigOperators
namespace SevenEighths.HeckePrimeRow
open HeckeFamily HeckeRowClosure CanonicalRowCompletion
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

local instance instFiniteQuotientOIdeal_solutions_r9b5e29_1 : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
local instance instIsPrincipalIdealRingO_solutions_r9b5e29_1 : IsPrincipalIdealRing O := IsCyclotomicExtension.Rat.three_pid K
omit [NeZero M] in
theorem identityClass_coprime {I : Ideal O} (hI : I∈RayQuotient.identityClass M H) :
    IsCoprime I M := by
  obtain ⟨hI,a,ha,u,hu,huH⟩ := hI
  rw [←ha]
  exact (IdealCharacter.isUnit_mk_iff_isCoprime M a).mp (hu ▸ u.isUnit)

omit [NeZero M] in
theorem identityClass_coprime_larger {I J : Ideal O}
    (hI : I∈RayQuotient.identityClass M H) (hMJ : M≤J) : IsCoprime I J := by
  rw [Ideal.isCoprime_iff_sup_eq]
  apply top_unique
  rw [←Ideal.isCoprime_iff_sup_eq.mp (identityClass_coprime M H hI)]
  exact sup_le_sup_left hMJ I

omit [NeZero M] in
theorem identityClass_prime_good (m : O) (hmLam : λ₀∣m) (hMm : M≤Ideal.span {m})
    (P : Ideal O) [P.IsMaximal] (hP : P∈RayQuotient.identityClass M H) : λ₀∉P := by
  have hm : m∉P := (SixthPowerAverage.prime_coprime_span_iff P m).mp
    (identityClass_coprime_larger M H hP hMm)
  intro hLam
  obtain ⟨a,rfl⟩ := hmLam
  exact hm (P.mul_mem_right a hLam)

end SevenEighths.HeckePrimeRow

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.DetectorRelativePrime
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.HeckeDetectorRelativePrime
open HeckeFamily HeckeDetectorPrimeFamily

theorem idealCoeff_ne_zero_of_coprime (ν : Character) (J : Ideal O)
    (hJ : J≠0) (hc : IsCoprime J ν.modulus) : idealCoeff ν J≠0 := by
  have hg := ConcretePrimeRowBridge.idealGenerator_ne_zero J hJ
  rw [←ConcretePrimeRowBridge.span_idealGenerator J,idealCoeff_span ν hg]
  apply MulChar.apply_ne_zero_iff.mpr
  apply (IdealCharacter.isUnit_mk_iff_isCoprime ν.modulus _).mpr
  simpa only [ConcretePrimeRowBridge.span_idealGenerator] using hc

theorem idealCoeff_inverse (ν : Character) (J : Ideal O) :
    idealCoeff ν.inverse J=(idealCoeff ν J)⁻¹ := by
  by_cases hJ : J=0
  · subst J
    simp only [map_zero,inv_zero]
  have hg := ConcretePrimeRowBridge.idealGenerator_ne_zero J hJ
  rw [←ConcretePrimeRowBridge.span_idealGenerator J,idealCoeff_span ν.inverse hg,
    idealCoeff_span ν hg,HeckeFamily.elementCoeff_inverse]

variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

end SevenEighths.HeckeDetectorRelativePrime

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.InverseAmplificationProfiles
namespace OAI

noncomputable section
open scoped Classical ContDiff Topology
open Set Filter Complex
namespace SevenEighths.HeckeInverseAmplification
open HeckeFamily HeckeDyadic

theorem polynomial_twistProfile (χ : Character) (inv : Bool) (W : ℝ→ℂ)
    (D σ freq : ℝ) :
    polynomial χ inv (twistProfile W σ freq) D 0 0=polynomial χ inv W D σ freq := by
  unfold polynomial
  congr 1
  apply tsum_congr
  intro J
  simp [summand,twistProfile,HeckeDyadic.shift,mul_assoc]

end SevenEighths.HeckeInverseAmplification

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.HeckeHeight
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentHeckeHeight
open HeckeFamily CenteredMomentHeckeVolume CenteredMomentHeckeCancellation CenteredMomentHeckeTwist
open CenteredMomentLattice CenteredMomentTwist
open QuadraticInitialBound EisensteinSchwartzPoisson
local notation "O" => ActualEisensteinCubic.O

theorem rowTwistedSum_eq (η χ : Character) (m A₀ z : O)
    (hrow : ∀ n, elementCoeff χ n=CanonicalRowCompletion.rowTwist
      (HeckeRowClosure.elementHom η) m 1 (A₀*z) n)
    (W : ℝ → ℂ) (t X : ℝ) :
    rowTwistedSum η m A₀ z W t X=twistedIdealSum χ W t X := by
  apply tsum_congr
  intro I
  have he := HeckeRowClosure.idealCoeff_eq_row η χ m 1 (A₀*z) hrow I
  simp only [one_pow,mul_one] at he
  rw [he]

end SevenEighths.CenteredMomentHeckeHeight

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.PrimeSlot
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentPrimeSlot
open HeckeFamily HeckeRowClosure HeckePrimeRay HeckePrimeAnnular HeckeDyadic
open CenteredMomentHeckeSlots CenteredMomentWholeSlotDeletion CenteredMomentTwist
local notation "O" => HeckeFamily.O

lemma sqrt_inverse_cpow (D:ℝ) (hD:0<D) :
    (Real.sqrt D:ℂ)⁻¹=(D:ℂ)^(-(1/2:ℂ)) := by
  rw [Complex.cpow_neg,Real.sqrt_eq_rpow]
  congr 1
  simpa using (Complex.ofReal_cpow hD.le (1/2:ℝ))

end SevenEighths.CenteredMomentPrimeSlot

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SlotNormalization
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.CenteredMomentSlotNormalization
open HeckeFamily CenteredMomentHeckeSlots CenteredMomentRetainedEnergy
open CenteredMomentWholeSlotDeletion CenteredMomentHeckeHeight
local notation "O" => HeckeFamily.O

lemma sqrt_product_normalizer {ι:Type*} [Fintype ι] (X:ℝ) (P:ι→ℝ)
    (hX:0≤X) (hP:∀i,0≤P i) :
    ((Real.sqrt X:ℂ)⁻¹)*(∏i,(Real.sqrt (P i):ℂ)⁻¹)=
      (Real.sqrt (X*∏i,P i):ℂ)⁻¹ := by
  rw [Real.sqrt_mul hX,Real.sqrt_prod _ (fun i _=>hP i),Complex.ofReal_mul,
    Complex.ofReal_prod,mul_inv_rev,Finset.prod_inv_distrib]
  ring

theorem selectedProduct_univ {ι:Type*} [Fintype ι] [DecidableEq ι]
    (η:Character) (m A z:O) (W₁ W₂:ℝ→ℂ)
    (S:ι→Finset (Ideal O)) (β:ι→Ideal O→ℂ) (P:ι→ℝ)
    (t X₁ X₂:ℝ) (hX:0≤X₁*X₂) (hP:∀i,0≤P i) :
    selectedProduct Finset.univ η m A z W₁ W₂ S β P t X₁ X₂=
      positiveSlotRow η m A z W₁ W₂ S β P t X₁ X₂ := by
  unfold selectedProduct normalizedSlot positiveSlotRow
  rw [Finset.prod_mul_distrib]
  have he:=sqrt_product_normalizer (X₁*X₂) P hX hP
  calc
    _=((Real.sqrt (X₁*X₂):ℂ)⁻¹*(∏i,(Real.sqrt (P i):ℂ)⁻¹))*
      ((rowTwistedSum η m A z W₁ t X₁*rowTwistedSum η m A z W₂ t X₂)*
        ∏i,rowSlot η m A z (S i) (β i) t) := by ring
    _=_ := by rw [he]

end SevenEighths.CenteredMomentSlotNormalization

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.DetectorDictionary
namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff ComplexConjugate

namespace SevenEighths.CenteredMomentDetectorDictionary
open HeckeFamily HeckeDyadic HeckeRowClosure HeckeInverseAmplification
open CenteredMomentHeckeHeight CenteredMomentHeckeTwist CenteredMomentHeckeSlots
open CenteredMomentRetainedEnergy CenteredMomentWholeSlotDeletion
open CenteredMomentPrimeSlot CenteredMomentSlotNormalization
local notation "O" => HeckeFamily.O

lemma plain_zero_height (χ : Character) (W : ℝ→ℂ) (X : ℝ) (hX : 0<X) :
    polynomial χ false W X 0 0 = (Real.sqrt X:ℂ)⁻¹*twistedIdealSum χ W 0 X := by
  rw [sqrt_inverse_cpow X hX]
  unfold polynomial twistedIdealSum
  congr 1
  have he := tsum_subtype_eq_of_support_subset
    (s := {I : Ideal O | I≠0})
    (f := fun I : Ideal O=>idealCoeff χ I*W ((I.absNorm:ℝ)/X))
    (by intro I hI hi; subst I; exact hI (by simp only [map_zero,zero_mul]))
  change (∑' I : HeckeDyadic.NonzeroIdeal,idealCoeff χ I.val*W ((I.val.absNorm:ℝ)/X))=
    ∑' I : Ideal O,idealCoeff χ I*W ((I.absNorm:ℝ)/X) at he
  simpa only [summand,coefficient,Bool.false_eq_true,ite_false,HeckeDyadic.norm,HeckeDyadic.shift,
    Complex.ofReal_zero,zero_mul,mul_zero,sub_zero,neg_zero,Complex.cpow_zero,mul_one,
    HeckeDyadic.NonzeroIdeal,UnrestrictedIdealReindex.NonzeroIdeal] using he

theorem plain_polynomial_eq_row (η χ : Character) (m A z : O)
    (hrow : ∀n,elementCoeff χ n=CanonicalRowCompletion.rowTwist (elementHom η) m 1 (A*z) n)
    (W : ℝ→ℂ) (X σ t : ℝ) (hX : 0<X) :
    polynomial χ false W X σ t = (Real.sqrt X:ℂ)⁻¹*
      rowTwistedSum η m A z (twistProfile W σ t) 0 X := by
  rw [←polynomial_twistProfile,plain_zero_height _ _ X hX,rowTwistedSum_eq η χ m A z hrow]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem positiveSlotRow_eq_product
    (η χ : Character) (m A z : O)
    (hrow : ∀n,elementCoeff χ n=CanonicalRowCompletion.rowTwist (elementHom η) m 1 (A*z) n)
    (W₁ W₂ : ℝ→ℂ) (S : ι→Finset (Ideal O)) (β : ι→Ideal O→ℂ) (P : ι→ℝ)
    (X₁ X₂ σ t : ℝ) (hX₁ : 0<X₁) (hX₂ : 0<X₂) (hP : ∀i,0<P i) :
    positiveSlotRow η m A z (twistProfile W₁ σ t) (twistProfile W₂ σ t) S β P 0 X₁ X₂ =
      polynomial χ false W₁ X₁ σ t*polynomial χ false W₂ X₂ σ t*
        ∏i,normalizedSlot η m A z (S i) (β i) 0 (P i) := by
  rw [←selectedProduct_univ _ _ _ _ _ _ _ _ _ _ _ _ (mul_pos hX₁ hX₂).le (fun i=>(hP i).le)]
  unfold selectedProduct
  rw [plain_polynomial_eq_row η χ m A z hrow W₁ X₁ σ t hX₁,
    plain_polynomial_eq_row η χ m A z hrow W₂ X₂ σ t hX₂,
    Real.sqrt_mul hX₁.le,Complex.ofReal_mul,mul_inv_rev]
  ring

end SevenEighths.CenteredMomentDetectorDictionary

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.DetectorDictionarySlots
namespace OAI

noncomputable section
open scoped Classical BigOperators ComplexConjugate

namespace SevenEighths.CenteredMomentDetectorDictionary
open HeckeFamily HeckeDyadic HeckeRowClosure CanonicalRowCompletion
open CenteredMomentHeckeSlots CenteredMomentWholeSlotDeletion CenteredMomentPrimeSlot
open HeckeDetectorRelativePrime
local notation "O" => HeckeFamily.O

theorem physical_slot_conj (M : Ideal O) (H : Subgroup (O⧸M)ˣ)
    (η : Character) (m u : O) (hmLam : ConcretePrimeRowBridge.goodLambda∣m)
    (hMm : M≤Ideal.span {m}) (W : ℝ→ℂ) (b D : ℝ) (z : ℂ) (hD : 0<D)
    (hη : ∀P∈primePool M H b D,W ((P.absNorm:ℝ)/D)≠0→IsCoprime P η.modulus) :
    normalizedSlot η m 1 u (primePool M H b D) (physicalSlotCoefficient η W D z) 0 D=
      conj (HeckePrimeRow.canonicalPrimeAmplitude M H u W b D z) := by
  unfold normalizedSlot rowSlot HeckePrimeRow.canonicalPrimeAmplitude
  rw [←sqrt_inverse_cpow D hD,map_mul]
  simp only [map_inv₀,Complex.conj_ofReal,Complex.ofReal_zero,one_mul,mul_zero,Complex.cpow_zero,mul_one,map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro P hP
  have hP' : P∈primePool M H b D := hP
  obtain ⟨_,hp,hclass⟩ := Finset.mem_filter.mp hP
  let : P.IsMaximal := (Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero
  have hg := HeckePrimeRow.identityClass_prime_good M H m hmLam hMm P hclass
  have hcop := HeckePrimeRow.identityClass_coprime_larger M H hclass hMm
  rw [idealRowHom_argument_mul,idealRowHom_prime_sixth_mask m P hg,if_pos hcop,one_mul]
  by_cases hw : W ((P.absNorm:ℝ)/D)=0
  · simp only [physicalSlotCoefficient,hw,zero_mul,map_zero,mul_zero,zero_mul]
  · have hn := idealCoeff_ne_zero_of_coprime η P hp.ne_zero (hη P hP' hw)
    simp only [physicalSlotCoefficient,HeckeDetectorRelativePrime.idealCoeff_inverse,map_mul,starRingEnd_self_apply]
    field_simp

end SevenEighths.CenteredMomentDetectorDictionary

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.DetectorDictionaryRows
namespace OAI

noncomputable section
open scoped Classical BigOperators ComplexConjugate

namespace SevenEighths.CenteredMomentDetectorDictionary
open HeckeFamily HeckeDyadic HeckeRowClosure HeckeInverseAmplification
open HeckeDetectorCoefficientTransfer CenteredMomentRetainedEnergy
open CenteredMomentPrimeSlot CenteredMomentWholeSlotDeletion
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem source_plain_pair_norm
    (M : Ideal O) (H : Subgroup (O⧸M)ˣ)
    (η χ ψ : Character) (m u : O) (reverse : Bool)
    (hrow : ∀n,elementCoeff ψ n=CanonicalRowCompletion.rowTwist (elementHom η) m 1 (1*u) n)
    (hc : ∀I : Ideal O,idealCoeff χ I=if reverse then conj (idealCoeff ψ I) else idealCoeff ψ I)
    (hmLam : ConcretePrimeRowBridge.goodLambda∣m) (hMm : M≤Ideal.span {m})
    (W₁ W₂ : ℝ→ℂ) (V : ι→ℝ→ℂ) (b P : ι→ℝ) (external : ι→ℂ)
    (X₁ X₂ σ t : ℝ) (hX₁ : 0<X₁) (hX₂ : 0<X₂) (hP : ∀i,0<P i)
    (hη : ∀i,∀J∈primePool M H (b i) (P i),V i ((J.absNorm:ℝ)/(P i))≠0→IsCoprime J η.modulus) :
    ‖polynomial χ false W₁ X₁ σ t*polynomial χ false W₂ X₂ σ t*
      ∏i,HeckePrimeRow.canonicalPrimeAmplitude M H u (V i) (b i) (P i) (external i)‖ =
    ‖positiveSlotRow η m 1 u
      (twistProfile (orientedProfile reverse W₁) σ (orientedFrequency reverse t))
      (twistProfile (orientedProfile reverse W₂) σ (orientedFrequency reverse t))
      (fun i=>primePool M H (b i) (P i))
      (fun i=>physicalSlotCoefficient η (V i) (P i) (external i)) P 0 X₁ X₂‖ := by
  rw [positiveSlotRow_eq_product η ψ m 1 u hrow _ _ _ _ P _ _ _ _ hX₁ hX₂ hP]
  simp only [norm_mul,norm_prod]
  rw [norm_of_oriented_coefficients χ ψ reverse hc false W₁ X₁ σ t hX₁,
    norm_of_oriented_coefficients χ ψ reverse hc false W₂ X₂ σ t hX₂]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  rw [physical_slot_conj M H η m u hmLam hMm (V i) (b i) (P i) (external i) (hP i) (hη i),RCLike.norm_conj]

theorem momentData_plain_pair_norm
    (M : Ideal O) (H : Subgroup (O⧸M)ˣ)
    (η χ : Character) (u : FreeRow) (reverse : Bool)
    (hc : ∀I : Ideal O,idealCoeff χ I=if reverse then
      conj (idealCoeff ((ProbeHighRowFamily.momentData η).character (ProbeHighRowFamily.momentElement u)) I)
      else idealCoeff ((ProbeHighRowFamily.momentData η).character (ProbeHighRowFamily.momentElement u)) I)
    (hMm : M≤Ideal.span {ProbeHighRowFamily.rowMaskElement})
    (W₁ W₂ : ℝ→ℂ) (V : ι→ℝ→ℂ) (b P : ι→ℝ) (external : ι→ℂ)
    (X₁ X₂ σ t : ℝ) (hX₁ : 0<X₁) (hX₂ : 0<X₂) (hP : ∀i,0<P i)
    (hη : ∀i,∀J∈primePool M H (b i) (P i),V i ((J.absNorm:ℝ)/(P i))≠0→IsCoprime J η.modulus) :
    ‖polynomial χ false W₁ X₁ σ t*polynomial χ false W₂ X₂ σ t*
      ∏i,HeckePrimeRow.canonicalPrimeAmplitude M H u.val (V i) (b i) (P i) (external i)‖ =
    ‖positiveSlotRow η ProbeHighRowFamily.rowMaskElement 1 u.val
      (twistProfile (orientedProfile reverse W₁) σ (orientedFrequency reverse t))
      (twistProfile (orientedProfile reverse W₂) σ (orientedFrequency reverse t))
      (fun i=>primePool M H (b i) (P i))
      (fun i=>physicalSlotCoefficient η (V i) (P i) (external i)) P 0 X₁ X₂‖ := by
  apply source_plain_pair_norm M H η χ
    ((ProbeHighRowFamily.momentData η).character (ProbeHighRowFamily.momentElement u))
    ProbeHighRowFamily.rowMaskElement u.val reverse _ hc (dvd_mul_left _ _) hMm
    W₁ W₂ V b P external X₁ X₂ σ t hX₁ hX₂ hP hη
  intro n
  simpa only [ProbeHighRowFamily.momentData,ProbeHighRowFamily.momentElement,one_mul] using
    (ProbeHighRowFamily.momentData η).character_spec (ProbeHighRowFamily.momentElement u) n

end SevenEighths.CenteredMomentDetectorDictionary

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.DetectorDictionaryFiber
namespace OAI

noncomputable section
open scoped Classical BigOperators ComplexConjugate

namespace SevenEighths.CenteredMomentDetectorDictionary
open HeckeFamily HeckeDyadic HeckeRowClosure HeckeInverseAmplification
open HeckeDetectorCoefficientTransfer HeckeDetectorRawFiber HeckeDetectorRowwisePolynomial
open HeckeDetectorDyadicProfiles CenteredMomentRetainedEnergy
open CenteredMomentPrimeSlot ProbeHighRowFamily
local notation "O" => HeckeFamily.O
variable {M : Ideal O} {H : Subgroup (O⧸M)ˣ} {Label Slot : Type*}
  {U a ε tstar T allowance : ℝ} {i : ℕ}

theorem fiber_plain_energy_eq (F : Fiber M H Label Slot U a ε tstar T allowance i)
    (η : Character) (hdata : F.rowData=momentData η)
    (hMm : M≤Ideal.span {rowMaskElement}) (hU : 0<U)
    (selected : Finset Slot) (j k : ℕ) (σ t : ℝ)
    (hη : ∀s∈selected,∀J∈primePool M H (F.upper s) (U^(F.widths s)),
      F.profile s ((J.absNorm:ℝ)/(U^(F.widths s)))≠0→IsCoprime J η.modulus) :
    (∑u∈F.rows,‖polynomial (F.family u F.label) false ((logProfile^[j]) positiveAnnular) (U^F.m) σ t*
      polynomial (F.family u F.label) false ((logProfile^[k]) positiveAnnular) (U^F.m) σ t*
        F.physicalProduct selected u‖^2)=
      ∑u∈F.rows,‖detectorPositiveRow F η selected j k σ t u‖^2 := by
  apply Finset.sum_congr rfl
  intro u hu
  congr 1
  have hc := F.row_coeff u hu
  rw [hdata] at hc
  have he := momentData_plain_pair_norm M H η (F.family u F.label) u F.reverse hc hMm
    ((logProfile^[j]) positiveAnnular) ((logProfile^[k]) positiveAnnular)
    (fun s : selected=>F.profile s.val) (fun s : selected=>F.upper s.val)
    (fun s : selected=>U^(F.widths s.val)) (fun s : selected=>F.external s.val)
    (U^F.m) (U^F.m) σ t (Real.rpow_pos_of_pos hU _) (Real.rpow_pos_of_pos hU _)
    (fun s=>Real.rpow_pos_of_pos hU _) (fun s=>hη s.val s.property)
  have hprod := Finset.prod_coe_sort selected (fun s=>HeckePrimeRow.canonicalPrimeAmplitude M H u.val
    (F.profile s) (F.upper s) (U^(F.widths s)) (F.external s))
  rw [hprod] at he
  simpa only [detectorPositiveRow,Fiber.physicalProduct,HeckeDetectorPhysicalSelection.physical,
    Finset.prod_coe_sort] using he

end SevenEighths.CenteredMomentDetectorDictionary

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.DetectorDictionarySupport
namespace OAI

noncomputable section
open scoped Classical Topology
open Filter
namespace SevenEighths.CenteredMomentDetectorDictionary
open HeckeFamily CenteredMomentPrimeSlot
local notation "O" => HeckeFamily.O

lemma annular_prime_coprime (η : Character) (a D : ℝ) (ha : 0<a) (hD : 0<D)
    (hlarge : (η.modulus.absNorm:ℝ)/a<D)
    (W : ℝ→ℂ) (hs : Function.support W⊆Set.Ici a)
    (P : Ideal O) (hp : Prime P) (hW : W ((P.absNorm:ℝ)/D)≠0) :
    IsCoprime P η.modulus := by
  apply ProbeRaySlots.prime_coprime_of_norm_gt η ⟨P,hp⟩
  have hlo : a*D≤(P.absNorm:ℝ) := (le_div_iff₀ hD).mp (hs hW)
  have hh : (η.modulus.absNorm:ℝ)<a*D := by
    have hh := (div_lt_iff₀ ha).mp hlarge
    nlinarith
  exact hh.trans_le hlo

theorem eventually_primePool_coprime (η : Character) (a : ℝ) (ha : 0<a) :
    ∀ᶠD : ℝ in atTop,∀(M : Ideal O)(H : Subgroup (O⧸M)ˣ)(W : ℝ→ℂ)(b : ℝ),
      Function.support W⊆Set.Ici a →
      ∀P∈primePool M H b D,W ((P.absNorm:ℝ)/D)≠0→IsCoprime P η.modulus := by
  filter_upwards [eventually_gt_atTop (0:ℝ),eventually_gt_atTop ((η.modulus.absNorm:ℝ)/a)] with D hD hlarge
  intro M H W b hs P hP hW
  exact annular_prime_coprime η a D ha hD hlarge W hs P (Finset.mem_filter.mp hP).2.1 hW

theorem eventually_primePool_power_coprime (η : Character) (a ell : ℝ) (ha : 0<a) (hell : 0<ell) :
    ∀ᶠZ : ℝ in atTop,∀(M : Ideal O)(H : Subgroup (O⧸M)ˣ)(W : ℝ→ℂ)(b : ℝ),
      Function.support W⊆Set.Ici a →
      ∀P∈primePool M H b (Z^ell),W ((P.absNorm:ℝ)/(Z^ell))≠0→IsCoprime P η.modulus :=
  (tendsto_rpow_atTop hell).eventually (eventually_primePool_coprime η a ha)

end SevenEighths.CenteredMomentDetectorDictionary

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.DetectorDictionarySource
namespace OAI

noncomputable section
open scoped Classical BigOperators Topology
open Filter

namespace SevenEighths.CenteredMomentDetectorDictionary
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open ProbePhysical CenteredMomentPrimeSlot
local notation "O" => HeckeFamily.O

lemma source_product_le_rowMask (S : Finset (Ideal O))
    (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆S) :
    (∏P∈S,P)≤Ideal.span {rowMaskElement} := by
  apply Ideal.dvd_iff_le.mp
  have hne : (Ideal.span {ConcretePrimeRowBridge.goodLambda}:Ideal O)≠Ideal.span {(2:O)} := by
    intro he
    have hh : CanonicalQuadraticSieve.badPrime false=CanonicalQuadraticSieve.badPrime true := he
    have hh := CanonicalQuadraticSieve.badPrime_injective hh
    cases hh
  have hd := Finset.prod_dvd_prod_of_subset CanonicalQuadraticSieve.fixedBadPrimes S (fun P : Ideal O=>P) hbad
  have he : (∏P∈CanonicalQuadraticSieve.fixedBadPrimes,P)=Ideal.span {rowMaskElement} := by
    change (∏P∈({Ideal.span {ConcretePrimeRowBridge.goodLambda},Ideal.span {(2:O)}} : Finset (Ideal O)),P)=_
    rw [Finset.prod_pair hne]
    unfold rowMaskElement
    rw [←Ideal.span_singleton_mul_span_singleton]
    exact mul_comm _ _
  rwa [he] at hd

variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

attribute [local instance] OAI.SevenEighths.CenteredMomentDetectorDictionary.instFiniteQuotientOIdeal_solutions
lemma sourceMomentData_base (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P) (η : Character)
    (j : Sum Bool (RayQuotient.Characters M H)) :
    sourceMomentData M H hH S hS η j=momentData (sourceMomentBase M H hH S hS η j) := by
  rcases j with b|θ
  · cases b <;> rfl
  · rfl

theorem eventually_source_slots_coprime {N : ℕ}
    (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P) (η : Character)
    (ell : Fin N→ℝ) (hell : ∀i,0<ell i) (a : ℝ) (ha : 0<a) :
    ∀ᶠZ : ℝ in atTop,∀j : Sum Bool (RayQuotient.Characters M H),∀i : Fin N,
      ∀d : ℝ,d≠0→∀(W : ℝ→ℂ)(b : ℝ),Function.support W⊆Set.Ici a→
      ∀P∈primePool M H b ((Z^d)^(ell i/d)),
        W ((P.absNorm:ℝ)/((Z^d)^(ell i/d)))≠0→
          IsCoprime P (sourceMomentBase M H hH S hS η j).modulus := by
  have he : ∀ᶠZ : ℝ in atTop,∀j : Sum Bool (RayQuotient.Characters M H),∀i : Fin N,
      ∀(W : ℝ→ℂ)(b : ℝ),Function.support W⊆Set.Ici a→
      ∀P∈primePool M H b (Z^(ell i)),W ((P.absNorm:ℝ)/(Z^(ell i)))≠0→
        IsCoprime P (sourceMomentBase M H hH S hS η j).modulus := by
    apply Filter.eventually_all.mpr
    intro j
    apply Filter.eventually_all.mpr
    intro i
    filter_upwards [eventually_primePool_power_coprime (sourceMomentBase M H hH S hS η j)
      a (ell i) ha (hell i)] with Z hz
    exact hz M H
  filter_upwards [he,eventually_ge_atTop (0:ℝ)] with Z hz hZ
  intro j i d hd W b hs
  have heq : (Z^d)^(ell i/d)=Z^(ell i) := by
    rw [←Real.rpow_mul hZ,mul_div_cancel₀ _ hd]
  rw [heq]
  exact hz j i W b hs

end SevenEighths.CenteredMomentDetectorDictionary

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.DetectorPlainFiberSource
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ComplexConjugate

namespace SevenEighths.CenteredMomentDetectorPlainFiberSource
open HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeRowClosure
open CenteredMomentDetectorDictionary CenteredMomentDetectorPlainSource
open CenteredMomentRetainedEnergy CenteredMomentSourceRow CenteredMomentSourceMass
open CenteredMomentUncenteredTerminal CenteredMomentHeckeColumnWindow
open CenteredMomentRestrictedSource CenteredMomentRestrictedEnergy
open CenteredMomentNaturalFixedRaySource ProbeHighRowFamily HeckeDetectorRawFiber
open HeckeDetectorCoefficientTransfer HeckeDetectorRowwisePolynomial HeckeDetectorDyadicProfiles
open CenteredMomentPrimeSlot CanonicalQuadraticSieve CenteredMomentRowNorm
open CenteredMomentSecondHeightFamily ConcreteTraceCRT ActualEisensteinCubic
local notation "O"=>HeckeFamily.O
variable {M:Ideal O}{H:Subgroup (O⧸M)ˣ}{Label Slot:Type*}
variable {U a ε tstar T allowance:ℝ}{i:ℕ}

lemma radialMajorant_nonneg (x:ℝ):0≤(radialMajorant x).re:=
  (Classical.choose_spec DetectorDictionaryInverseRawRealRadial.exists_real_raw_radial_majorant).2.1 x

lemma radialMajorant_one (x:ℝ)(hx:x∈Set.Icc (0:ℝ) 1):radialMajorant x=1:=
  (Classical.choose_spec DetectorDictionaryInverseRawRealRadial.exists_real_raw_radial_majorant).2.2.2 x hx

end SevenEighths.CenteredMomentDetectorPlainFiberSource

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourceInternal
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentNaturalFixedRaySource
open HeckeFamily CenteredExceptionalProfile CenteredExceptionalCount
open HeckeRowClosure CanonicalRowCompletion ConcretePrimeRowBridge
open CenteredMomentNaturalRowSource UniqueFactorizationMonoid
local notation "O" => HeckeFamily.O

lemma internalQ_ne_zero (Q : Ideal O) (hQ : Q≠0) (η₀ : Character) : internalQ Q η₀≠0 :=
  Ideal.inf_ne_bot_of_ne_bot hQ η₀.modulus_ne_bot

lemma internalQ_ne_top (Q : Ideal O) (hQ : Q≠⊤) (η₀ : Character) : internalQ Q η₀≠⊤ := by
  intro h
  exact hQ (top_le_iff.mp (h ▸ (inf_le_left : internalQ Q η₀≤Q)))

variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

end SevenEighths.CenteredMomentNaturalFixedRaySource

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourceFixedIdeal
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentNaturalFixedRaySource
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentDetectorDictionary CenteredMomentNaturalRowSource
open CenteredExceptionalProfile CenteredMomentSecondHeightFamily ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O

variable {Δ : ℝ} {D : Parameters.HighData Δ}

lemma sourceFixedIdeal_ne_zero (F : ProbeFinalAssembly.SourceData D) : sourceFixedIdeal F≠0 :=
  Ideal.inf_ne_bot_of_ne_bot (NeZero.ne F.modulus)
    (Ideal.span_singleton_eq_bot.not.mpr (by norm_num : (72:O)≠0))

lemma sourceFixedIdeal_ne_top (F : ProbeFinalAssembly.SourceData D) : sourceFixedIdeal F≠⊤ := by
  have hmem : Ideal.span {goodLambda}∈F.S := by
    apply F.exclusions.bad
    change Ideal.span {goodLambda}∈({Ideal.span {goodLambda},Ideal.span {(2:O)}} : Finset (Ideal O))
    simp
  have hle : F.modulus≤Ideal.span {goodLambda} := by
    apply Ideal.dvd_iff_le.mp
    exact Finset.dvd_prod_of_mem (fun P : Ideal O=>P) hmem
  have hprime := (F.maximal _ hmem).isPrime
  intro h
  exact hprime.ne_top (top_le_iff.mp (h ▸ (inf_le_left.trans hle : sourceFixedIdeal F≤Ideal.span {goodLambda})))

lemma sourceFixedIdeal_le_72 (F : ProbeFinalAssembly.SourceData D) : sourceFixedIdeal F≤Ideal.span {(72:O)} := inf_le_right

end SevenEighths.CenteredMomentNaturalFixedRaySource

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.DetectorEnergyInitialState
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap Topology
open Filter

namespace SevenEighths.CenteredMomentDetectorEnergyInitialState
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentEnergyState CenteredMomentRadialEligibleEnergy
open CenteredMomentSecondHeightFamily CenteredExceptionalProfile
open CenteredMomentNaturalFixedRaySource ConcretePrimeRowBridge
open CenteredMomentDetectorPlainFiberSource CenteredMomentDetectorDictionary
open CenteredMomentFiniteProfileExceptional
local notation "O"=>HeckeFamily.O

variable {Δ:ℝ}{D:Parameters.HighData Δ}

lemma source_keep_iff (F:ProbeFinalAssembly.SourceData D)(η:Character)(u:FreeRow):
    initialKeep η (internalQ (sourceFixedIdeal F) η) u.val↔¬sourceExceptional F η u:=by
  exact and_iff_right u.property.1

end SevenEighths.CenteredMomentDetectorEnergyInitialState

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourceFreeExceptional
namespace OAI

noncomputable section
open scoped Classical BigOperators Topology
open Filter

namespace SevenEighths.CenteredMomentNaturalFixedRaySource
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily UniqueFactorizationMonoid
open CenteredMomentDetectorDictionary CenteredExceptionalProfile CenteredExceptionalCount
open ConcretePrimeRowBridge CenteredMomentSecondHeightFamily
local notation "O" => HeckeFamily.O

theorem fixed_inducing_free_support (η : Character) (Q : Ideal O)
    (hQ0 : Q≠0) (hQ : Q≠⊤) (hQ72 : Q≤Ideal.span {(72:O)}) (hQη : Q≤η.modulus)
    (m : O) (hm : m≠0) (hml : goodLambda∣m) (hm2 : (2:O)∣m)
    (u : FreeRow) (hu : FixedInducingRow η Q m 1 u.val) :
    u.val∈HeckeExceptionalRows.rows (normalizedFactors Q).toFinset := by
  obtain ⟨χ,ψ,hprim,hind,hψ,hχ⟩:=hu
  refine ⟨u.property.1,?_⟩
  intro P hP
  refine ⟨?_,u.property.2 P⟩
  by_contra hout
  have hp : Prime P:=prime_of_normalized_factor P hP
  let : P.IsMaximal:=(Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero
  obtain ⟨hl,h2,hQP⟩:=outside_fixed_support Q hQ0 hQ72 P hp hout
  have hηP : IsCoprime η.modulus P:=hQP.of_isCoprime_of_dvd_left (Ideal.dvd_iff_le.mpr hQη)
  have hz:=actual_row_numerator_valuation_zero η χ ψ hind Q hQ hQ72 hψ
    m 1 u.val hm one_ne_zero u.property.1 hml hm2
    (by simpa only [one_mul] using hχ) P hl h2 hQP hηP
  simp only [one_pow,one_mul,valuation] at hz
  have hpos:=Multiset.count_pos.mpr hP
  have hlt:=u.property.2 P
  omega

variable {Δ : ℝ} {D : Parameters.HighData Δ}

lemma source_exceptional_norm (F : ProbeFinalAssembly.SourceData D) (η : Character)
    (u : FreeRow) (hu : sourceExceptional F η u) :
    (Ideal.span {u.val}).absNorm≤ sourceExceptionalBound F η := by
  apply HeckeExceptionalRows.row_norm_bound _
    (fun P hP=>prime_of_normalized_factor P (Multiset.mem_toFinset.mp hP))
  apply fixed_inducing_free_support η (internalQ (sourceFixedIdeal F) η)
    (internalQ_ne_zero _ (sourceFixedIdeal_ne_zero F) η)
    (internalQ_ne_top _ (sourceFixedIdeal_ne_top F) η)
    (inf_le_left.trans (sourceFixedIdeal_le_72 F)) inf_le_right
    (fixedBadMask*idealGenerator 1)
    (mul_ne_zero fixedBadMask_ne_zero (idealGenerator_ne_zero _ one_ne_zero))
    ((dvd_mul_right _ _).trans (dvd_mul_right _ _))
    ((dvd_mul_left _ _).trans (dvd_mul_right _ _)) u hu

theorem eventually_source_no_exceptional (F : ProbeFinalAssembly.SourceData D) (η : Character) :
    ∀ᶠZ : ℝ in atTop,∀label : Sum Bool (RayQuotient.Characters F.modulus ⊤),∀u : FreeRow,
      Z^(1/100:ℝ)≤ rowNorm u →
      ¬sourceExceptional F (sourceMomentBase F.modulus ⊤ le_top F.S F.exclusions.prime η label) u := by
  have hh : ∀ᶠZ : ℝ in atTop,∀label : Sum Bool (RayQuotient.Characters F.modulus ⊤),
      (sourceExceptionalBound F (sourceMomentBase F.modulus ⊤ le_top F.S F.exclusions.prime η label):ℝ)<Z^(1/100:ℝ) := by
    apply Filter.eventually_all.mpr
    intro label
    exact (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/100)).eventually (eventually_gt_atTop _)
  filter_upwards [hh] with Z hz
  intro label u hu hex
  have hb : rowNorm u≤(sourceExceptionalBound F
      (sourceMomentBase F.modulus ⊤ le_top F.S F.exclusions.prime η label):ℝ) := by
    change ((Ideal.span {u.val}).absNorm:ℝ)≤_
    exact_mod_cast source_exceptional_norm F _ u hex
  exact (not_lt_of_ge (hu.trans hb)) (hz label)

end SevenEighths.CenteredMomentNaturalFixedRaySource

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.DetectorPlainExceptional
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap Topology
open Filter

namespace SevenEighths.CenteredMomentDetectorPlainExceptional
open HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeRowClosure
open CenteredMomentDetectorDictionary CenteredMomentDetectorPlainSource
open CenteredMomentDetectorPlainFiberSource CenteredMomentDetectorEnergyInitialState
open CenteredMomentRetainedEnergy CenteredMomentSourceRow CenteredMomentSourceMass
open CenteredMomentUncenteredTerminal CenteredMomentHeckeColumnWindow
open CenteredMomentRestrictedSource CenteredMomentRestrictedEnergy
open CenteredMomentNaturalFixedRaySource ProbeHighRowFamily HeckeDetectorRawFiber HeckeDetectorBatch
open HeckeDetectorCoefficientTransfer HeckeDetectorRowwisePolynomial HeckeDetectorDyadicProfiles
open CenteredMomentPrimeSlot CanonicalQuadraticSieve CenteredMomentRowNorm
open CenteredMomentSecondHeightFamily ConcreteTraceCRT ActualEisensteinCubic
local notation "O"=>HeckeFamily.O
variable {M:Ideal O}{H:Subgroup (O⧸M)ˣ}{Label Slot:Type*}
variable {U a ε tstar T allowance:ℝ}{i:ℕ}

variable {Δ:ℝ}{D:Parameters.HighData Δ}

theorem source_fibers_eventually_retained (S:ProbeFinalAssembly.SourceData D)(η:Character):
    ∀ᶠZ:ℝ in atTop,∀rows:Finset FreeRow,
      (∀u∈rows,Z^(1/100:ℝ)≤ rowNorm u)→
      ∀(d a ε tstar T allowance:ℝ)(i:ℕ)
      (B:Batch S.modulus ⊤ (Sum Bool (RayQuotient.Characters S.modulus ⊤)) (Fin D.N)
        (Z^d) a ε tstar T allowance i),B.rows⊆rows→
      ∀bin label J K,∀hne:(B.fiberRows bin label J K).Nonempty,
      let η₀:=sourceMomentBase S.modulus ⊤ le_top S.S S.exclusions.prime η label;
      (∀u∈(B.fiber bin label J K hne).rows,
        initialKeep η₀ (internalQ (sourceFixedIdeal S) η₀) u.val) ∧
      ((B.fiber bin label J K hne).rows.filter (sourceExceptional S η₀))=∅:=by
  filter_upwards [eventually_source_no_exceptional S η] with Z hz
  intro rows hrows d a ε tstar T allowance i B hB bin label J K hne η₀
  have hk:∀u∈(B.fiber bin label J K hne).rows,
      initialKeep η₀ (internalQ (sourceFixedIdeal S) η₀) u.val:=by
    intro u hu
    apply (source_keep_iff S η₀ u).mpr
    apply hz label u
    apply hrows u
    apply hB
    simp only [Batch.fiber,HeckeDetectorFiberPartition.toFiber,
      HeckeDetectorFiberPartition.fiber,Finset.mem_filter] at hu
    exact hu.1
  refine ⟨hk,?_⟩
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro u hu
  obtain ⟨hu,hex⟩:=Finset.mem_filter.mp hu
  exact ((source_keep_iff S η₀ u).mp (hk u hu)) hex

theorem source_batch_plain_retained_oai (S:ProbeFinalAssembly.SourceData D)(η:Character):
    ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀rows:Finset FreeRow,
      (∀u∈rows,Z^(1/100:ℝ)≤ rowNorm u)→
      ∀d:ℝ,d≠0→∀(a ε tstar T allowance:ℝ)(i:ℕ)
      (B:Batch S.modulus ⊤ (Sum Bool (RayQuotient.Characters S.modulus ⊤)) (Fin D.N)
        (Z^d) a ε tstar T allowance i),B.rows⊆rows→
      B.data=sourceMomentData S.modulus ⊤ le_top S.S S.exclusions.prime η→
      B.profile=(fun _ x=>(S.w x:ℂ))→B.widths=(fun s=>D.ell s/d)→
      ∀bin label J K,∀hne:(B.fiberRows bin label J K).Nonempty,
      ∀selected:Finset (Fin D.N),∀j k:ℕ,∀σ t:ℝ,
      let F:=B.fiber bin label J K hne;
      let η₀:=sourceMomentBase S.modulus ⊤ le_top S.S S.exclusions.prime η label;
      (∑u∈F.rows,‖polynomial (F.family u F.label) false ((logProfile^[j]) positiveAnnular)
        ((Z^d)^F.m) σ t*polynomial (F.family u F.label) false ((logProfile^[k]) positiveAnnular)
        ((Z^d)^F.m) σ t*F.physicalProduct selected u‖^2)≤
        retainedSourceEnergy (initialKeep η₀ (internalQ (sourceFixedIdeal S) η₀))
          F η₀ selected j k σ t radialMajorant:=by
  filter_upwards [source_fibers_eventually_retained S η,
    eventually_source_slots_coprime S.modulus ⊤ le_top S.S S.exclusions.prime η
      D.ell (fun s=>(D.slots_bounds s).1) 1 (by norm_num),eventually_gt_atTop (1:ℝ)] with Z hret hcop hZ
  refine ⟨hZ,?_⟩
  intro rows hrows d hd a ε tstar T allowance i B hB hdata hprofile hwidth
    bin label J K hne selected j k σ t F η₀
  have hU:0<Z^d:=Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _
  have hdataF:F.rowData=momentData η₀:=by
    change B.data label=momentData η₀
    rw [hdata,sourceMomentData_base]
  have hMm:S.modulus≤Ideal.span {rowMaskElement}:=source_product_le_rowMask S.S S.exclusions.bad
  have hη:∀s∈selected,∀I∈primePool S.modulus ⊤ (F.upper s) ((Z^d)^(F.widths s)),
      F.profile s ((I.absNorm:ℝ)/((Z^d)^(F.widths s)))≠0→IsCoprime I η₀.modulus:=by
    intro s hs I hI hn
    change I∈primePool S.modulus ⊤ (B.upper s) ((Z^d)^(B.widths s)) at hI
    change B.profile s ((I.absNorm:ℝ)/((Z^d)^(B.widths s)))≠0 at hn
    rw [hwidth] at hI
    rw [hwidth,hprofile] at hn
    exact hcop label s d hd (fun x=>(S.w x:ℂ)) (B.upper s)
      (by
        intro x hx
        have hn:S.w x≠0:=by simpa using hx
        exact (S.support hn).1.le) I hI hn
  rw [fiber_plain_energy_eq F η₀ hdataF hMm hU selected j k σ t hη]
  exact retained_positive_energy_le_source _ radialMajorant radialMajorant_nonneg radialMajorant_one
    F η₀ selected j k σ t hU (hret rows hrows d a ε tstar T allowance i B hB bin label J K hne).1

end SevenEighths.CenteredMomentDetectorPlainExceptional

end

end OAI
end

theorem solution : type_of% @OAI.SevenEighths.CenteredMomentDetectorPlainExceptional.source_batch_plain_retained_oai := @OAI.SevenEighths.CenteredMomentDetectorPlainExceptional.source_batch_plain_retained_oai
