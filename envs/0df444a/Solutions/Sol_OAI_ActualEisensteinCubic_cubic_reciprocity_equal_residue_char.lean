-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.cubic_reciprocity_equal_residue_char
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:24:55.24689+00:00
-- url     : https://prove2.me/submissions/b82ff780-08cf-4ad6-b844-8aad42203a99

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_CubicTrace
import Definitions.Def_OAI_NumberTheory_DirichletL_Fourier_PositiveLogProfiles
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_SquarePhaseFactorization
import Theorems.Thm_OAI_ActualEisensteinCubic_exists_primary_prime_factorization
import Theorems.Thm_OAI_ActualEisensteinCubic_prime_divisor_residue_char_ne
import Theorems.Thm_OAI_ActualEisensteinCubic_neg_add_primary
import Theorems.Thm_OAI_ActualEisensteinCubic_prime_generator_not_mem_of_ne
import Theorems.Thm_OAI_ActualEisensteinCubic_A3_cubicChar_neg_one
import Theorems.Thm_OAI_ActualEisensteinCubic_cubic_reciprocity_distinct_residue_char
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_verticalSlice_apply
import Theorems.Thm_OAI_FiniteGaussPhase_productElementCRT_mk
import Theorems.Thm_OAI_IdealGaussCRT_quotientProdEquivPi_mk
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
import Theorems.Thm_OAI_LocalLogFourier_positiveLogProfile_apply
attribute [local simp] OAI.ActualEisensteinCubic.principalSexticRow_mk
attribute [local simp] OAI.EisensteinSchwartzPoisson.verticalSlice_apply
attribute [local simp] OAI.FiniteGaussPhase.productElementCRT_mk
attribute [local simp] OAI.IdealGaussCRT.quotientProdEquivPi_mk
attribute [local simp] OAI.IdealGaussCRT.traceProdChar_mk
attribute [local simp] OAI.LocalLogFourier.positiveLogProfile_apply



set_option autoImplicit false
open OAI
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
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
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
open OAI.ActualEisensteinCubic
namespace OAI.ActualEisensteinCubic
theorem _root_.solution
    (P Q : Ideal O) [P.IsMaximal] [Q.IsMaximal]
    (hPgood : lambda ∉ P) (hQgood : lambda ∉ Q)
    (hne : P ≠ Q) (hchar : ringChar (O ⧸ Q) = ringChar (O ⧸ P))
    (p q : O) (hP : P = Ideal.span {p}) (hQ : Q = Ideal.span {q})
    (hpprimary : lambda ^ 2 ∣ p - 1) (hqprimary : lambda ^ 2 ∣ q - 1) :
    cubicChar P hPgood (Ideal.Quotient.mk P q) =
      cubicChar Q hQgood (Ideal.Quotient.mk Q p) := by
  classical
  let t : O := -(p + q)
  have hpP : p ∈ P := by rw [hP]; exact Ideal.subset_span (by simp)
  have hqQ : q ∈ Q := by rw [hQ]; exact Ideal.subset_span (by simp)
  have hqP : q ∉ P := prime_generator_not_mem_of_ne P Q hne q hQ
  have hpQ : p ∉ Q := prime_generator_not_mem_of_ne Q P hne.symm p hP
  have htP : t ∉ P := by
    intro ht
    have hs : p + q ∈ P := by simpa only [t, neg_neg] using P.neg_mem ht
    exact hqP (by simpa only [add_sub_cancel_left] using P.sub_mem hs hpP)
  have htQ : t ∉ Q := by
    intro ht
    have hs : p + q ∈ Q := by simpa only [t, neg_neg] using Q.neg_mem ht
    exact hpQ (by simpa only [add_sub_cancel_right] using Q.sub_mem hs hqQ)
  have ht0 : t ≠ 0 := fun h => htP (h ▸ P.zero_mem)
  obtain ⟨s, hst, hs⟩ := exists_primary_prime_factorization t ht0
    (neg_add_primary p q hpprimary hqprimary)
  have hlocal : ∀ r ∈ s,
      cubicChar P hPgood (Ideal.Quotient.mk P r) =
      cubicChar Q hQgood (Ideal.Quotient.mk Q r) := by
    intro r hr
    let R : Ideal O := Ideal.span {r}
    let : R.IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible (hs r hr).1.irreducible
    have hrR : r ∈ R := Ideal.subset_span (by simp)
    have htR : t ∈ R := Ideal.mem_span_singleton.mpr (hst ▸ Multiset.dvd_prod hr)
    have hRgood : lambda ∉ R := primary_maximal_divisor_good t
      (neg_add_primary p q hpprimary hqprimary) R htR
    have hRP := prime_divisor_residue_char_ne P Q R hne hchar t htP htQ htR
    have hRQ : ringChar (O ⧸ R) ≠ ringChar (O ⧸ Q) := by rwa [hchar]
    rw [cubic_reciprocity_distinct_residue_char P R hPgood hRgood hRP
      p r hP rfl hpprimary (hs r hr).2,
      cubic_reciprocity_distinct_residue_char Q R hQgood hRgood hRQ
      q r hQ rfl hqprimary (hs r hr).2]
    have hsum : Ideal.Quotient.mk R p + Ideal.Quotient.mk R q = 0 := by
      have hz := Ideal.Quotient.eq_zero_iff_mem.mpr htR
      simpa only [t, map_neg, map_add, neg_eq_zero] using hz
    have heq : Ideal.Quotient.mk R p = -Ideal.Quotient.mk R q := eq_neg_of_add_eq_zero_left hsum
    rw [heq, ← neg_one_mul (Ideal.Quotient.mk R q), map_mul,
      A3_cubicChar_neg_one, one_mul]
  have hmul : ∀ f : Multiset O,
      (∀ r ∈ f, cubicChar P hPgood (Ideal.Quotient.mk P r) =
        cubicChar Q hQgood (Ideal.Quotient.mk Q r)) →
      cubicChar P hPgood (Ideal.Quotient.mk P f.prod) =
        cubicChar Q hQgood (Ideal.Quotient.mk Q f.prod) := by
    intro f
    induction f using Multiset.induction_on with
    | empty => intro _; simp
    | @cons r f ih =>
      intro hf
      simp only [Multiset.prod_cons, map_mul]
      rw [hf r (Multiset.mem_cons_self _ _), ih
        (fun x hx => hf x (Multiset.mem_cons_of_mem hx))]
  have htval := hmul s hlocal
  rw [hst] at htval
  have hpzero : Ideal.Quotient.mk P p = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hpP
  have hqzero : Ideal.Quotient.mk Q q = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hqQ
  simp only [t, map_neg, map_add, hpzero, hqzero, zero_add, add_zero] at htval
  rw [← neg_one_mul (Ideal.Quotient.mk P q), map_mul, A3_cubicChar_neg_one, one_mul,
    ← neg_one_mul (Ideal.Quotient.mk Q p), map_mul, A3_cubicChar_neg_one, one_mul] at htval
  exact htval
end OAI.ActualEisensteinCubic
