-- Prove2me | solution 1 for OAI.CubicRamified.cubicValue_omega_primary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:20:46.081216+00:00
-- url     : https://prove2.me/submissions/619af191-cf70-4ddf-8411-63a40cd8b404

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_IdealMobius
import Definitions.Def_OAI_NumberTheory_DirichletL_Reciprocity_CubicJacobi
import Theorems.Thm_OAI_CubicRamified_primary_card_exponent
import Theorems.Thm_OAI_ActualEisensteinCubic_cubicChar_omega
import Theorems.Thm_OAI_ActualEisensteinCubic_qNat_eq_absNorm_span
import Theorems.Thm_OAI_ShortDraftLatticeCount_coords_eval
import Theorems.Thm_OAI_ShortDraftLatticeCount_qO_nonneg


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
open scoped BigOperators Classical
open OAI.CubicRamified
open ActualEisensteinCubic CubicJacobiGlobal CompletedGauss
open ActualEisensteinCubic CubicJacobiGlobal CompletedGauss
namespace OAI.CubicRamified
theorem _root_.solution (P : Ideal O) [P.IsMaximal]
    (hg : lambda ∉ P) (A B : ℤ) (hP : P = Ideal.span {primaryCoord A B}) :
    cubicChar P hg (Ideal.Quotient.mk P omega) =
      omega ^ ((2 * A - B) % 3).toNat := by
  have hn : (Nat.card (O ⧸ P) : ℤ) =
      (1 + 3 * A)^2 - (1 + 3 * A)*(3 * B) + (3 * B)^2 := by
    change (Ideal.absNorm P : ℤ) = _
    rw [hP, ← qNat_eq_absNorm_span]
    unfold ShortDraftLatticeCount.qNat
    rw [Int.toNat_of_nonneg (ShortDraftLatticeCount.qO_nonneg _)]
    rw [primaryCoord, ShortDraftLatticeCount.coords_eval]
    rfl
  have hn' : (Nat.card (O ⧸ P) : ℤ) =
      1 + 9*(A^2 - A*B + B^2) + 3*(2*A-B) := by nlinarith [hn]
  rw [cubicChar_omega]
  apply ((omega_primitive.isOfFinOrder (by decide)).pow_inj_mod).mpr
  rw [← omega_primitive.eq_orderOf]
  let : Fintype (O ⧸ P) := Fintype.ofFinite _
  have hcard : 1 < Nat.card (O ⧸ P) := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card
  exact primary_card_exponent (Nat.card (O ⧸ P)) A B hcard hn'
end OAI.CubicRamified
