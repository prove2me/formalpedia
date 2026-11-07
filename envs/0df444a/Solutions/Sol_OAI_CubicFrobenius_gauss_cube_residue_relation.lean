-- Prove2me | solution 1 for OAI.CubicFrobenius.gauss_cube_residue_relation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:12:49.327808+00:00
-- url     : https://prove2.me/submissions/ed00bb0b-5cdf-4c06-98ab-983a5bc80ff6

import Definitions.Def_OAI_NumberTheory_DirichletL_PrimeRows_ActiveGaussFactorization
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_CubicTrace
import Theorems.Thm_OAI_CubicFrobenius_card_cast_ne_zero
import Theorems.Thm_OAI_CubicFrobenius_gaussSum_pow_card
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
open OAI.CubicFrobenius
namespace OAI.CubicFrobenius
theorem _root_.solution (F F' E : Type*) [Field F] [Fintype F]
    [Field F'] [Fintype F'] [Field E] [Algebra F' E]
    (hchar : ringChar F' ≠ ringChar F)
    (χ : MulChar F F') (hχ : χ ≠ 1) (ψ : AddChar F E) (hψ : ψ.IsPrimitive)
    (a : F') (m : ℕ) (hm : Fintype.card F' = 3 * m + 1)
    (hcube : gaussSum (χ.ringHomComp (algebraMap F' E)) ψ ^ 3 = algebraMap F' E a) :
    χ (Fintype.card F' : F) * a ^ m = 1 := by
  let ξ := χ.ringHomComp (algebraMap F' E)
  have hξ : ξ ≠ 1 := (MulChar.ringHomComp_ne_one_iff (algebraMap F' E).injective).mpr hχ
  have hcard : (Fintype.card F : E) ≠ 0 := by
    rw [← map_natCast (algebraMap F' E)]
    exact (map_ne_zero (algebraMap F' E)).mpr (card_cast_ne_zero F F' hchar)
  have hg : gaussSum ξ ψ ≠ 0 := gaussSum_ne_zero_of_nontrivial hcard hξ hψ
  have hq : (Fintype.card F' : F) ≠ 0 := card_cast_ne_zero F' F hchar.symm
  let u : Fˣ := (isUnit_iff_ne_zero.mpr hq).unit
  have hu : (u : F) = Fintype.card F' := (isUnit_iff_ne_zero.mpr hq).unit_spec
  have hshift := gaussSum_mulShift ξ ψ u
  rw [hu, ← gaussSum_pow_card F F' E χ ψ] at hshift
  have hp : gaussSum ξ ψ ^ Fintype.card F' =
      algebraMap F' E (a ^ m) * gaussSum ξ ψ := by
    rw [hm, pow_succ, pow_mul, hcube, map_pow]
  rw [hp] at hshift
  have hone : ξ (Fintype.card F' : F) * algebraMap F' E (a ^ m) = 1 := by
    apply mul_right_cancel₀ hg
    simpa only [mul_assoc, one_mul] using hshift
  apply (algebraMap F' E).injective
  simpa only [ξ, map_mul, map_one, MulChar.ringHomComp_apply] using hone
end OAI.CubicFrobenius
