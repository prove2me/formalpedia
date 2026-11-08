-- Prove2me | solution 1 for OAI.CubicEisenstein.idealTotient_moebius
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T09:31:53.091079+00:00
-- url     : https://prove2.me/submissions/8f5590de-170b-44ad-bdc6-b998f3b2c59e

import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_ConjugateProfiles
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_RamifiedNormWeights
import Theorems.Thm_OAI_CubicEisenstein_residue_unit_mobius
import Theorems.Thm_OAI_CubicEisenstein_sum_indicator_const
import Theorems.Thm_OAI_CubicEisenstein_card_quotient_multiples

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
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators Classical
open OAI.CubicEisenstein
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal UniqueFactorizationMonoid
open IdealMobiusDivisorSum (idealDivisors mem_idealDivisors sum_moebius_divisors)
namespace OAI.CubicEisenstein
theorem _root_.solution (I : Ideal O) (hI : I ≠ 0) :
    (idealTotient I:ℂ)=(Ideal.absNorm I:ℂ)*
      ∑ J ∈ idealDivisors I, (moebius J:ℂ)/(Ideal.absNorm J:ℂ) := by
  let : Finite (O ⧸ I) := I.finiteQuotientOfFreeOfNeBot hI
  let : Fintype (O ⧸ I) := Fintype.ofFinite _
  classical
  have hcount : (idealTotient I:ℂ)=∑ r : O ⧸ I,
      @ite ℂ (IsUnit r) (Classical.propDecidable _) 1 0 := by
    have h := sum_indicator_const (R := O ⧸ I) IsUnit (1:ℂ)
    rw [mul_one] at h
    calc
      _ = (Nat.card {r : O ⧸ I // IsUnit r}:ℂ) := by
        exact_mod_cast Nat.card_congr (unitsSubtypeEquiv (O ⧸ I))
      _ = _ := h.symm
  rw [hcount]
  have hs : (∑ r : O ⧸ I, @ite ℂ (IsUnit r) (Classical.propDecidable _) 1 0) =
      ∑ r : O ⧸ I, ∑ J ∈ idealDivisors I,
        if Quotient.out r ∈ J then (moebius J:ℂ) else 0 := by
    apply Finset.sum_congr rfl
    intro r hr
    exact residue_unit_mobius I hI r
  rw [hs]
  rw [Finset.sum_comm]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro J hJ
  rw [sum_indicator_const,card_quotient_multiples I J hI
    (Ideal.dvd_iff_le.mp ((mem_idealDivisors hI).mp hJ))]
  ring
end OAI.CubicEisenstein
