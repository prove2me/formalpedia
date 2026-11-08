-- Prove2me | solution 1 for OAI.CubicEisenstein.card_quotient_multiples
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T09:27:19.730109+00:00
-- url     : https://prove2.me/submissions/2d7aaa65-b8a5-4d4f-b715-f5af90be0c08

import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_ConjugateProfiles
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_RamifiedNormWeights
import Theorems.Thm_OAI_CubicEisenstein_card_ring_eq_card_mul_kernel

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
theorem _root_.solution (I J : Ideal O) (hI : I ≠ 0) (hIJ : I ≤ J) :
    (Nat.card {r : O ⧸ I // Quotient.out r ∈ J}:ℂ)=
      (Ideal.absNorm I:ℂ)/(Ideal.absNorm J:ℂ) := by
  let f : (O ⧸ I) →+* (O ⧸ J) := Ideal.Quotient.factor hIJ
  have hf : Function.Surjective f := Ideal.Quotient.factor_surjective hIJ
  have hpred (r : O ⧸ I) : Quotient.out r ∈ J ↔ f r=0 := by
    have hfr : f r=Ideal.Quotient.mk J (Quotient.out r) := by
      calc
        f r = f (Ideal.Quotient.mk I (Quotient.out r)) :=
          congrArg f (Ideal.Quotient.mk_out r).symm
        _ = _ := Ideal.Quotient.factor_mk hIJ _
    rw [← Ideal.Quotient.eq_zero_iff_mem,hfr]
  let e : {r : O ⧸ I // Quotient.out r ∈ J} ≃ f.toAddMonoidHom.ker :=
    Equiv.subtypeEquivRight hpred
  have hcard := card_ring_eq_card_mul_kernel f hf
  have hJ : J ≠ 0 := fun h => hI (le_antisymm (h ▸ hIJ) bot_le)
  have hnJ : (Ideal.absNorm J:ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hJ)
  rw [Nat.card_congr e]
  apply (eq_div_iff hnJ).mpr
  have hh : Nat.card f.toAddMonoidHom.ker * Ideal.absNorm J = Ideal.absNorm I :=
    (Nat.mul_comm _ _).trans hcard.symm
  exact_mod_cast hh
end OAI.CubicEisenstein
