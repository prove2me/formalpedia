-- Prove2me | solution 1 for OAI.CubicEisenstein.idealTotient_pow_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T09:30:20.402235+00:00
-- url     : https://prove2.me/submissions/5b65bd95-3d4a-4542-8e71-9f6c467a012b

import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_ConjugateProfiles
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_RamifiedNormWeights
import Theorems.Thm_OAI_CubicEisenstein_card_units_mul_card_target

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
namespace OAI.CubicEisenstein
theorem _root_.solution (I : Ideal O) (hI : I ≠ 0) (n : ℕ) :
    idealTotient (I^(n+1))=Ideal.absNorm I^n*idealTotient I := by
  let f : (O ⧸ I^(n+1)) →+* (O ⧸ I) :=
    Ideal.Quotient.factor (Ideal.pow_le_self (Nat.succ_ne_zero n))
  have hf : Function.Surjective f := Ideal.Quotient.factor_surjective _
  have hu (x : O ⧸ I^(n+1)) : IsUnit (f x) ↔ IsUnit x := by
    obtain ⟨x,rfl⟩ := Ideal.Quotient.mk_surjective x
    exact (Ideal.Quotient.isUnit_mk_pow_iff_isUnit_mk I (Nat.succ_ne_zero n)).symm
  have h := card_units_mul_card_target f hf hu
  change Ideal.absNorm I*idealTotient (I^(n+1))=
    Ideal.absNorm (I^(n+1))*idealTotient I at h
  rw [map_pow] at h
  have hpos : 0<Ideal.absNorm I := Nat.pos_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  apply Nat.eq_of_mul_eq_mul_left hpos
  calc
    _ = Ideal.absNorm I^(n+1)*idealTotient I := h
    _ = _ := by ring
end OAI.CubicEisenstein
