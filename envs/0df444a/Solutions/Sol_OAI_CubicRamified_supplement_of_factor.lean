-- Prove2me | solution 1 for OAI.CubicRamified.supplement_of_factor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:33:21.659968+00:00
-- url     : https://prove2.me/submissions/8af148d0-2fe6-4ad3-b7c6-c4faff141b36

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_IdealMobius
import Definitions.Def_OAI_NumberTheory_DirichletL_Reciprocity_CubicJacobi
import Theorems.Thm_OAI_CubicRamified_cubicValue_cube
import Theorems.Thm_OAI_CubicRamified_cubicValue_ne_zero
import Theorems.Thm_OAI_CubicRamified_ramified_comparison_of_factor
import Theorems.Thm_OAI_CubicRamified_eq_of_cube_one_of_sq_eq

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
theorem _root_.solution
    (P Q : Ideal O) [P.IsMaximal] [Q.IsMaximal]
    (hgP : lambda ∉ P) (hgQ : lambda ∉ Q)
    (p q u r : O) (hP : P = Ideal.span {p}) (hQ : Q = Ideal.span {q})
    (hp : lambda ^ 2 ∣ p - 1) (hq : lambda ^ 2 ∣ q - 1)
    (hu : IsUnit u) (hr0 : r ≠ 0) (hr : lambda ^ 2 ∣ r - 1)
    (hfactor : p - q = lambda ^ 2 * u * r)
    (j : ℕ)
    (hscalar : (cubicChar Q hgQ (Ideal.Quotient.mk Q lambda)) ^ 2 *
        cubicChar Q hgQ (Ideal.Quotient.mk Q u) =
      (omega ^ j)^2 * cubicChar P hgP (Ideal.Quotient.mk P u)) :
    cubicChar P hgP (Ideal.Quotient.mk P lambda) = omega ^ j := by
  apply eq_of_cube_one_of_sq_eq
  · exact cubicValue_cube P hgP lambda hgP
  · rw [← pow_mul, Nat.mul_comm j, pow_mul, omega_primitive.pow_eq_one, one_pow]
  · apply mul_right_cancel₀ (cubicValue_ne_zero P hgP u (Ideal.notMem_of_isUnit P hu))
    exact (ramified_comparison_of_factor P Q hgP hgQ p q u r hP hQ hp hq
      hu.ne_zero hr0 hr hfactor).trans hscalar
end OAI.CubicRamified
