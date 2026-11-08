-- Prove2me | solution 1 for OAI.CubicEisenstein.heightLog_first_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T11:25:12.146313+00:00
-- url     : https://prove2.me/submissions/e927e836-8d3c-466c-81c7-993bd20b3f43

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_PrincipalDifference
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_SpatialDerivatives
import Theorems.Thm_OAI_CubicEisenstein_abs_le_inv_of_mul_sq_le_one
import Theorems.Thm_OAI_CubicEisenstein_heightLog_eikonal


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
open scoped BigOperators Classical SchwartzMap
open Filter
open scoped BigOperators Classical Topology
open OAI.CubicEisenstein
namespace OAI.CubicEisenstein
theorem _root_.solution (A B C D x y v : ℝ)
    (hrel : A*D=B^2+C^2) (hv : 0<v)
    (hq : quadraticHeightDenominator A B C D x y v≠0) :
    |heightLogDx A B C D x y v|≤1/v ∧
    |heightLogDy A B C D x y v|≤1/v ∧
    |heightLogDv A B C D x y v|≤1/v := by
  have he := heightLog_eikonal A B C D x y v hrel hv.ne' hq
  have hx := mul_nonneg (sq_nonneg v) (sq_nonneg (heightLogDx A B C D x y v))
  have hy := mul_nonneg (sq_nonneg v) (sq_nonneg (heightLogDy A B C D x y v))
  have hz := mul_nonneg (sq_nonneg v) (sq_nonneg (heightLogDv A B C D x y v))
  exact ⟨abs_le_inv_of_mul_sq_le_one hv (by nlinarith),
    abs_le_inv_of_mul_sq_le_one hv (by nlinarith),
    abs_le_inv_of_mul_sq_le_one hv (by nlinarith)⟩
end OAI.CubicEisenstein
