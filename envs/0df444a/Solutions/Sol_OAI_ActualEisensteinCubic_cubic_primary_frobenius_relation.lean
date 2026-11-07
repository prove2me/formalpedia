-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.cubic_primary_frobenius_relation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:22:00.101198+00:00
-- url     : https://prove2.me/submissions/13db0abc-fd34-4003-81e1-9b33264bec31

import Definitions.Def_OAI_NumberTheory_DirichletL_PrimeRows_ActiveGaussFactorization
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_CubicTrace
import Theorems.Thm_OAI_ActualEisensteinCubic_cubicChar_reduce_ne_one
import Theorems.Thm_OAI_ActualEisensteinCubic_cubicGauss_cube_reduce
import Theorems.Thm_OAI_CubicFrobenius_card_cast_ne_zero
import Theorems.Thm_OAI_CubicFrobenius_gauss_cube_residue_relation
import Theorems.Thm_OAI_ActualEisensteinCubic_cubicChar_pow_three
import Theorems.Thm_OAI_ActualEisensteinCubic_cubicChar_reduce
import Theorems.Thm_OAI_ActualEisensteinCubic_cubic_roots_reduce_injective
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_verticalSlice_apply
import Theorems.Thm_OAI_FiniteGaussPhase_productElementCRT_mk
import Theorems.Thm_OAI_IdealGaussCRT_quotientProdEquivPi_mk
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
attribute [local simp] OAI.ActualEisensteinCubic.principalSexticRow_mk
attribute [local simp] OAI.EisensteinSchwartzPoisson.verticalSlice_apply
attribute [local simp] OAI.FiniteGaussPhase.productElementCRT_mk
attribute [local simp] OAI.IdealGaussCRT.quotientProdEquivPi_mk
attribute [local simp] OAI.IdealGaussCRT.traceProdChar_mk



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
open OAI.ActualEisensteinCubic
namespace OAI.ActualEisensteinCubic
theorem _root_.solution (P Q : Ideal O) [P.IsMaximal] [Q.IsMaximal]
    (hPgood : lambda ∉ P) (hQgood : lambda ∉ Q)
    (hchar : ringChar (O ⧸ Q) ≠ ringChar (O ⧸ P))
    (p : O) (hP : P = Ideal.span {p}) (hprimary : lambda ^ 2 ∣ p - 1) :
    cubicChar P hPgood (Nat.card (O ⧸ Q) : O ⧸ P) *
      cubicChar Q hQgood (Ideal.Quotient.mk Q (p * (Nat.card (O ⧸ P) : O))) = 1 := by
  classical
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Field (O ⧸ Q) := Ideal.Quotient.field Q
  let : Fintype (O ⧸ P) := Fintype.ofFinite _
  let : Fintype (O ⧸ Q) := Fintype.ofFinite _
  let ψ := AddChar.FiniteField.primitiveChar (O ⧸ P) (O ⧸ Q) hchar
  let E := CyclotomicField ψ.n (O ⧸ Q)
  let η : (O ⧸ Q) →+* E := algebraMap (O ⧸ Q) E
  let χ := (cubicChar P hPgood).ringHomComp (Ideal.Quotient.mk Q)
  let a : O ⧸ Q := -(Ideal.Quotient.mk Q p) * (Fintype.card (O ⧸ P) : O ⧸ Q)
  let m := (Fintype.card (O ⧸ Q) - 1) / 3
  have hqdiv : 3 ∣ Fintype.card (O ⧸ Q) - 1 := by
    simpa only [Nat.card_eq_fintype_card] using card_sub_one_div_three Q hQgood
  have hqpos : 0 < Fintype.card (O ⧸ Q) := Fintype.card_pos
  have hm : Fintype.card (O ⧸ Q) = 3 * m + 1 := by
    dsimp [m]
    omega
  have hcube : gaussSum (χ.ringHomComp η) ψ.char ^ 3 = η a := by
    have hc := cubicGauss_cube_reduce P Q hPgood hQgood p hP hprimary η ψ.char ψ.prim
    convert hc using 1
    · rfl
    · simp only [a, map_mul, map_neg, map_natCast, Nat.card_eq_fintype_card]
  have hrel := CubicFrobenius.gauss_cube_residue_relation (O ⧸ P) (O ⧸ Q) E
    hchar χ (cubicChar_reduce_ne_one P Q hPgood hQgood) ψ.char ψ.prim a m hm hcube
  have heuler := cubicChar_reduce Q hQgood
    (Ideal.Quotient.mk Q (-p * (Nat.card (O ⧸ P) : O)))
  have heuler' : Ideal.Quotient.mk Q
      (cubicChar Q hQgood (Ideal.Quotient.mk Q (-p * (Nat.card (O ⧸ P) : O)))) = a ^ m := by
    simpa only [a, m, map_mul, map_neg, map_natCast, Nat.card_eq_fintype_card] using heuler
  rw [← heuler'] at hrel
  change Ideal.Quotient.mk Q (cubicChar P hPgood (Fintype.card (O ⧸ Q) : O ⧸ P)) *
    Ideal.Quotient.mk Q (cubicChar Q hQgood
      (Ideal.Quotient.mk Q (-p * (Nat.card (O ⧸ P) : O)))) = 1 at hrel
  have hx : (Fintype.card (O ⧸ Q) : O ⧸ P) ≠ 0 :=
    CubicFrobenius.card_cast_ne_zero (O ⧸ Q) (O ⧸ P) hchar.symm
  have hy : Ideal.Quotient.mk Q (-p * (Nat.card (O ⧸ P) : O)) ≠ 0 := by
    intro hz
    rw [hz, MulChar.map_zero, map_zero, mul_zero] at hrel
    exact zero_ne_one hrel
  have hxcube : (cubicChar P hPgood (Fintype.card (O ⧸ Q) : O ⧸ P)) ^ 3 = 1 := by
    rw [← MulChar.pow_apply' _ (by decide : (3 : ℕ) ≠ 0), cubicChar_pow_three]
    exact MulChar.one_apply (isUnit_iff_ne_zero.mpr hx)
  have hycube : (cubicChar Q hQgood
      (Ideal.Quotient.mk Q (-p * (Nat.card (O ⧸ P) : O)))) ^ 3 = 1 := by
    rw [← MulChar.pow_apply' _ (by decide : (3 : ℕ) ≠ 0), cubicChar_pow_three]
    exact MulChar.one_apply (isUnit_iff_ne_zero.mpr hy)
  have hprod : cubicChar P hPgood (Fintype.card (O ⧸ Q) : O ⧸ P) *
      cubicChar Q hQgood (Ideal.Quotient.mk Q (-p * (Nat.card (O ⧸ P) : O))) = 1 := by
    apply cubic_roots_reduce_injective Q hQgood
    · rw [mul_pow, hxcube, hycube, mul_one]
    · simp
    · simpa only [map_mul, map_one] using hrel
  have hminus : cubicChar Q hQgood (-1 : O ⧸ Q) = 1 :=
    MulChar.val_neg_one_eq_one_of_odd_order (by decide : Odd 3) (cubicChar_pow_three Q hQgood)
  have hneg : Ideal.Quotient.mk Q (-p * (Nat.card (O ⧸ P) : O)) =
      (-1) * Ideal.Quotient.mk Q (p * (Nat.card (O ⧸ P) : O)) := by
    simp only [map_mul, map_neg, map_natCast]
    ring
  rw [hneg, map_mul, hminus, one_mul] at hprod
  simpa only [Nat.card_eq_fintype_card] using hprod
end OAI.ActualEisensteinCubic
