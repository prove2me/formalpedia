-- Prove2me | solution 1 for OAI.CubicRamified.cubicValue_lambda_primary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:35:15.854135+00:00
-- url     : https://prove2.me/submissions/447f5db1-e783-4e1d-b84c-961abc3aff94

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_IdealMobius
import Definitions.Def_OAI_NumberTheory_DirichletL_Reciprocity_CubicJacobi
import Theorems.Thm_OAI_CubicRamified_cubicValue_lambda_two
import Theorems.Thm_OAI_CubicRamified_cubicValue_lambda_seven
import Theorems.Thm_OAI_CubicRamified_primaryCoord_eq
import Theorems.Thm_OAI_CubicRamified_primaryCoord_primary
import Theorems.Thm_OAI_CubicRamified_primaryCoord_ne_zero
import Theorems.Thm_OAI_CubicRamified_cubicValue_omega_primary
import Theorems.Thm_OAI_CubicRamified_omega_isUnit
import Theorems.Thm_OAI_CubicRamified_omega_four
import Theorems.Thm_OAI_CubicRamified_omega_five
import Theorems.Thm_OAI_CubicRamified_cubicValue_neg
import Theorems.Thm_OAI_CubicRamified_cubicValue_omega_two
import Theorems.Thm_OAI_CubicRamified_cubicValue_omega_seven
import Theorems.Thm_OAI_CubicRamified_supplement_of_factor
import Theorems.Thm_OAI_CubicRamified_omega_six
import Theorems.Thm_OAI_ActualEisensteinCubic_omega_sq_for_norm
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_halfEulerIterateCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperFourierRayCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperRealRayCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_verticalSlice_apply
import Theorems.Thm_OAI_FiniteGaussPhase_productElementCRT_mk
import Theorems.Thm_OAI_IdealGaussCRT_quotientProdEquivPi_mk
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
import Theorems.Thm_OAI_LocalLogFourier_positiveLogProfile_apply
import Theorems.Thm_OAI_QuadraticGaussRay_residueQuotientFour_mk
attribute [local simp] OAI.ActualEisensteinCubic.principalSexticRow_mk
attribute [local simp] OAI.EisensteinSchwartzPoisson.halfEulerIterateCLM_apply
attribute [local simp] OAI.EisensteinSchwartzPoisson.paperFourierRayCLM_apply
attribute [local simp] OAI.EisensteinSchwartzPoisson.paperRealRayCLM_apply
attribute [local simp] OAI.EisensteinSchwartzPoisson.verticalSlice_apply
attribute [local simp] OAI.FiniteGaussPhase.productElementCRT_mk
attribute [local simp] OAI.IdealGaussCRT.quotientProdEquivPi_mk
attribute [local simp] OAI.IdealGaussCRT.traceProdChar_mk
attribute [local simp] OAI.LocalLogFourier.positiveLogProfile_apply
attribute [local simp] OAI.QuadraticGaussRay.residueQuotientFour_mk


section
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
namespace CubicJacobiGlobal
open ActualEisensteinCubic CompletedGauss
end CubicJacobiGlobal
namespace CubicRamified
open ActualEisensteinCubic CubicJacobiGlobal CompletedGauss
open ActualEisensteinCubic CubicJacobiGlobal CompletedGauss
open ActualEisensteinCubic CubicJacobiGlobal CompletedGauss
private theorem supplement_case00 (P : Ideal O) [P.IsMaximal]
    (hg : lambda ∉ P) (k l : ℤ)
    (hP : P = Ideal.span {primaryCoord (3*k+0) (3*l+0)}) :
    cubicChar P hg (Ideal.Quotient.mk P lambda) = omega ^ 0 := by
  have hw : cubicChar P hg (Ideal.Quotient.mk P omega) = omega ^ 0 := by
    rw [cubicValue_omega_primary P hg _ _ hP]
    congr 1
    omega
  refine supplement_of_factor P cubicTwoIdeal hg cubicTwoIdeal_good
    (primaryCoord (3*k+0) (3*l+0)) (-2) (-(omega ^ 2))
    (primaryCoord (k) (l)) hP rfl (primaryCoord_primary _ _) neg_two_primary
    (omega_isUnit.pow 2).neg (primaryCoord_ne_zero _ _) (primaryCoord_primary _ _) ?_ 0 ?_
  · simp only [primaryCoord_eq, lambda_def]
    push_cast
    all_goals ring_nf
    all_goals simp only [omega_five, omega_four, omega_primitive.pow_eq_one, omega_sq_for_norm]
    all_goals ring
  · simp only [cubicValue_neg, map_pow, cubicValue_lambda_two,
      cubicValue_omega_two, hw, pow_zero, ]
    all_goals ring_nf
    all_goals simp only [  omega_six,
      ]
private theorem supplement_case01 (P : Ideal O) [P.IsMaximal]
    (hg : lambda ∉ P) (k l : ℤ)
    (hP : P = Ideal.span {primaryCoord (3*k+0) (3*l+1)}) :
    cubicChar P hg (Ideal.Quotient.mk P lambda) = omega ^ 0 := by
  have hw : cubicChar P hg (Ideal.Quotient.mk P omega) = omega ^ 2 := by
    rw [cubicValue_omega_primary P hg _ _ hP]
    congr 1
    omega
  refine supplement_of_factor P cubicTwoIdeal hg cubicTwoIdeal_good
    (primaryCoord (3*k+0) (3*l+1)) (-2) (omega ^ 1)
    (primaryCoord (l) (-k + l)) hP rfl (primaryCoord_primary _ _) neg_two_primary
    (omega_isUnit.pow 1) (primaryCoord_ne_zero _ _) (primaryCoord_primary _ _) ?_ 0 ?_
  · simp only [primaryCoord_eq, lambda_def]
    push_cast
    all_goals ring_nf
    all_goals simp only [ omega_four, omega_primitive.pow_eq_one, omega_sq_for_norm]
    all_goals ring
  · simp only [  cubicValue_lambda_two,
      cubicValue_omega_two, hw, pow_zero, pow_one]
    all_goals ring_nf
    all_goals simp only [   omega_five,
       omega_sq_for_norm]
private theorem supplement_case02 (P : Ideal O) [P.IsMaximal]
    (hg : lambda ∉ P) (k l : ℤ)
    (hP : P = Ideal.span {primaryCoord (3*k+0) (3*l+2)}) :
    cubicChar P hg (Ideal.Quotient.mk P lambda) = omega ^ 0 := by
  have hw : cubicChar P hg (Ideal.Quotient.mk P omega) = omega ^ 1 := by
    rw [cubicValue_omega_primary P hg _ _ hP]
    congr 1
    omega
  refine supplement_of_factor P sevenIdeal hg sevenIdeal_good
    (primaryCoord (3*k+0) (3*l+2)) sevenPrime (-(omega ^ 0))
    (primaryCoord (-k + l) (-k)) hP rfl (primaryCoord_primary _ _) sevenPrime_primary
    (omega_isUnit.pow 0).neg (primaryCoord_ne_zero _ _) (primaryCoord_primary _ _) ?_ 0 ?_
  · simp only [primaryCoord_eq, lambda_def, sevenPrime]
    push_cast
    all_goals ring_nf
    all_goals simp only [  omega_primitive.pow_eq_one, omega_sq_for_norm]
    all_goals ring
  · simp only [cubicValue_neg,  cubicValue_lambda_seven,
        pow_zero,  map_one]
private theorem supplement_case10 (P : Ideal O) [P.IsMaximal]
    (hg : lambda ∉ P) (k l : ℤ)
    (hP : P = Ideal.span {primaryCoord (3*k+1) (3*l+0)}) :
    cubicChar P hg (Ideal.Quotient.mk P lambda) = omega ^ 1 := by
  have hw : cubicChar P hg (Ideal.Quotient.mk P omega) = omega ^ 2 := by
    rw [cubicValue_omega_primary P hg _ _ hP]
    congr 1
    omega
  refine supplement_of_factor P cubicTwoIdeal hg cubicTwoIdeal_good
    (primaryCoord (3*k+1) (3*l+0)) (-2) (omega ^ 2)
    (primaryCoord (-k - 1) (-l)) hP rfl (primaryCoord_primary _ _) neg_two_primary
    (omega_isUnit.pow 2) (primaryCoord_ne_zero _ _) (primaryCoord_primary _ _) ?_ 1 ?_
  · simp only [primaryCoord_eq, lambda_def]
    push_cast
    all_goals ring_nf
    all_goals simp only [omega_five, omega_four, omega_primitive.pow_eq_one, omega_sq_for_norm]
    all_goals ring
  · simp only [ map_pow, cubicValue_lambda_two,
      cubicValue_omega_two, hw,  pow_one]
    all_goals ring_nf
private theorem supplement_case11 (P : Ideal O) [P.IsMaximal]
    (hg : lambda ∉ P) (k l : ℤ)
    (hP : P = Ideal.span {primaryCoord (3*k+1) (3*l+1)}) :
    cubicChar P hg (Ideal.Quotient.mk P lambda) = omega ^ 1 := by
  have hw : cubicChar P hg (Ideal.Quotient.mk P omega) = omega ^ 1 := by
    rw [cubicValue_omega_primary P hg _ _ hP]
    congr 1
    omega
  refine supplement_of_factor P sevenIdeal hg sevenIdeal_good
    (primaryCoord (3*k+1) (3*l+1)) sevenPrime (-(omega ^ 2))
    (primaryCoord (k) (l)) hP rfl (primaryCoord_primary _ _) sevenPrime_primary
    (omega_isUnit.pow 2).neg (primaryCoord_ne_zero _ _) (primaryCoord_primary _ _) ?_ 1 ?_
  · simp only [primaryCoord_eq, lambda_def, sevenPrime]
    push_cast
    all_goals ring_nf
    all_goals simp only [omega_five, omega_four, omega_primitive.pow_eq_one, omega_sq_for_norm]
    all_goals ring
  · simp only [cubicValue_neg, map_pow, cubicValue_lambda_seven,
      cubicValue_omega_seven, hw,  pow_one]
    all_goals ring_nf
private theorem supplement_case12 (P : Ideal O) [P.IsMaximal]
    (hg : lambda ∉ P) (k l : ℤ)
    (hP : P = Ideal.span {primaryCoord (3*k+1) (3*l+2)}) :
    cubicChar P hg (Ideal.Quotient.mk P lambda) = omega ^ 1 := by
  have hw : cubicChar P hg (Ideal.Quotient.mk P omega) = omega ^ 0 := by
    rw [cubicValue_omega_primary P hg _ _ hP]
    congr 1
    omega
  refine supplement_of_factor P cubicTwoIdeal hg cubicTwoIdeal_good
    (primaryCoord (3*k+1) (3*l+2)) (-2) (-(omega ^ 1))
    (primaryCoord (-l - 1) (k - l)) hP rfl (primaryCoord_primary _ _) neg_two_primary
    (omega_isUnit.pow 1).neg (primaryCoord_ne_zero _ _) (primaryCoord_primary _ _) ?_ 1 ?_
  · simp only [primaryCoord_eq, lambda_def]
    push_cast
    all_goals ring_nf
    all_goals simp only [ omega_four, omega_primitive.pow_eq_one, omega_sq_for_norm]
    all_goals ring
  · simp only [cubicValue_neg,  cubicValue_lambda_two,
      cubicValue_omega_two, hw, pow_zero, pow_one]
    all_goals ring_nf
    all_goals simp only [   omega_five,
       omega_sq_for_norm]
private theorem supplement_case20 (P : Ideal O) [P.IsMaximal]
    (hg : lambda ∉ P) (k l : ℤ)
    (hP : P = Ideal.span {primaryCoord (3*k+2) (3*l+0)}) :
    cubicChar P hg (Ideal.Quotient.mk P lambda) = omega ^ 2 := by
  have hw : cubicChar P hg (Ideal.Quotient.mk P omega) = omega ^ 1 := by
    rw [cubicValue_omega_primary P hg _ _ hP]
    congr 1
    omega
  refine supplement_of_factor P sevenIdeal hg sevenIdeal_good
    (primaryCoord (3*k+2) (3*l+0)) sevenPrime (-(omega ^ 1))
    (primaryCoord (-l) (k - l + 1)) hP rfl (primaryCoord_primary _ _) sevenPrime_primary
    (omega_isUnit.pow 1).neg (primaryCoord_ne_zero _ _) (primaryCoord_primary _ _) ?_ 2 ?_
  · simp only [primaryCoord_eq, lambda_def, sevenPrime]
    push_cast
    all_goals ring_nf
    all_goals simp only [ omega_four, omega_primitive.pow_eq_one, omega_sq_for_norm]
    all_goals ring
  · simp only [cubicValue_neg,  cubicValue_lambda_seven,
      cubicValue_omega_seven, hw,  pow_one]
    all_goals ring_nf
    all_goals simp only [   omega_five,
       omega_sq_for_norm]
private theorem supplement_case21 (P : Ideal O) [P.IsMaximal]
    (hg : lambda ∉ P) (k l : ℤ)
    (hP : P = Ideal.span {primaryCoord (3*k+2) (3*l+1)}) :
    cubicChar P hg (Ideal.Quotient.mk P lambda) = omega ^ 2 := by
  have hw : cubicChar P hg (Ideal.Quotient.mk P omega) = omega ^ 0 := by
    rw [cubicValue_omega_primary P hg _ _ hP]
    congr 1
    omega
  refine supplement_of_factor P cubicTwoIdeal hg cubicTwoIdeal_good
    (primaryCoord (3*k+2) (3*l+1)) (-2) (-(omega ^ 0))
    (primaryCoord (-k + l - 1) (-k - 1)) hP rfl (primaryCoord_primary _ _) neg_two_primary
    (omega_isUnit.pow 0).neg (primaryCoord_ne_zero _ _) (primaryCoord_primary _ _) ?_ 2 ?_
  · simp only [primaryCoord_eq, lambda_def]
    push_cast
    all_goals ring_nf
    all_goals simp only [  omega_primitive.pow_eq_one, omega_sq_for_norm]
    all_goals ring
  · simp only [cubicValue_neg,  cubicValue_lambda_two,
        pow_zero,  map_one]
private theorem supplement_case22 (P : Ideal O) [P.IsMaximal]
    (hg : lambda ∉ P) (k l : ℤ)
    (hP : P = Ideal.span {primaryCoord (3*k+2) (3*l+2)}) :
    cubicChar P hg (Ideal.Quotient.mk P lambda) = omega ^ 2 := by
  have hw : cubicChar P hg (Ideal.Quotient.mk P omega) = omega ^ 2 := by
    rw [cubicValue_omega_primary P hg _ _ hP]
    congr 1
    omega
  refine supplement_of_factor P cubicTwoIdeal hg cubicTwoIdeal_good
    (primaryCoord (3*k+2) (3*l+2)) (-2) (omega ^ 0)
    (primaryCoord (k - l) (k + 1)) hP rfl (primaryCoord_primary _ _) neg_two_primary
    (omega_isUnit.pow 0) (primaryCoord_ne_zero _ _) (primaryCoord_primary _ _) ?_ 2 ?_
  · simp only [primaryCoord_eq, lambda_def]
    push_cast
    all_goals ring_nf
    all_goals simp only [  omega_primitive.pow_eq_one, omega_sq_for_norm]
    all_goals ring
  · simp only [  cubicValue_lambda_two,
        pow_zero,  map_one]
end CubicRamified
end
end OAI
end

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
open ActualEisensteinCubic CubicJacobiGlobal CompletedGauss
namespace OAI.CubicRamified
theorem _root_.solution (P : Ideal O) [P.IsMaximal]
    (hg : lambda ∉ P) (A B : ℤ)
    (hP : P = Ideal.span {primaryCoord A B}) :
    cubicChar P hg (Ideal.Quotient.mk P lambda) = omega ^ (A % 3).toNat := by
  have hA : A = 3 * (A / 3) + A % 3 := by omega
  have hB : B = 3 * (B / 3) + B % 3 := by omega
  have hAa : A % 3 = 0 ∨ A % 3 = 1 ∨ A % 3 = 2 := by omega
  have hBb : B % 3 = 0 ∨ B % 3 = 1 ∨ B % 3 = 2 := by omega
  rcases hAa with ha | ha | ha <;> rcases hBb with hb | hb | hb
  · have hp : P = Ideal.span {primaryCoord (3*(A/3)+0) (3*(B/3)+0)} := by
      rw [show 3*(A/3)+0 = A by omega, show 3*(B/3)+0 = B by omega]
      exact hP
    simpa only [ha, Int.reduceToNat] using supplement_case00 P hg (A/3) (B/3) hp
  · have hp : P = Ideal.span {primaryCoord (3*(A/3)+0) (3*(B/3)+1)} := by
      rw [show 3*(A/3)+0 = A by omega, show 3*(B/3)+1 = B by omega]
      exact hP
    simpa only [ha, Int.reduceToNat] using supplement_case01 P hg (A/3) (B/3) hp
  · have hp : P = Ideal.span {primaryCoord (3*(A/3)+0) (3*(B/3)+2)} := by
      rw [show 3*(A/3)+0 = A by omega, show 3*(B/3)+2 = B by omega]
      exact hP
    simpa only [ha, Int.reduceToNat] using supplement_case02 P hg (A/3) (B/3) hp
  · have hp : P = Ideal.span {primaryCoord (3*(A/3)+1) (3*(B/3)+0)} := by
      rw [show 3*(A/3)+1 = A by omega, show 3*(B/3)+0 = B by omega]
      exact hP
    simpa only [ha, Int.reduceToNat] using supplement_case10 P hg (A/3) (B/3) hp
  · have hp : P = Ideal.span {primaryCoord (3*(A/3)+1) (3*(B/3)+1)} := by
      rw [show 3*(A/3)+1 = A by omega, show 3*(B/3)+1 = B by omega]
      exact hP
    simpa only [ha, Int.reduceToNat] using supplement_case11 P hg (A/3) (B/3) hp
  · have hp : P = Ideal.span {primaryCoord (3*(A/3)+1) (3*(B/3)+2)} := by
      rw [show 3*(A/3)+1 = A by omega, show 3*(B/3)+2 = B by omega]
      exact hP
    simpa only [ha, Int.reduceToNat] using supplement_case12 P hg (A/3) (B/3) hp
  · have hp : P = Ideal.span {primaryCoord (3*(A/3)+2) (3*(B/3)+0)} := by
      rw [show 3*(A/3)+2 = A by omega, show 3*(B/3)+0 = B by omega]
      exact hP
    simpa only [ha, Int.reduceToNat] using supplement_case20 P hg (A/3) (B/3) hp
  · have hp : P = Ideal.span {primaryCoord (3*(A/3)+2) (3*(B/3)+1)} := by
      rw [show 3*(A/3)+2 = A by omega, show 3*(B/3)+1 = B by omega]
      exact hP
    simpa only [ha, Int.reduceToNat] using supplement_case21 P hg (A/3) (B/3) hp
  · have hp : P = Ideal.span {primaryCoord (3*(A/3)+2) (3*(B/3)+2)} := by
      rw [show 3*(A/3)+2 = A by omega, show 3*(B/3)+2 = B by omega]
      exact hP
    simpa only [ha, Int.reduceToNat] using supplement_case22 P hg (A/3) (B/3) hp
end OAI.CubicRamified
