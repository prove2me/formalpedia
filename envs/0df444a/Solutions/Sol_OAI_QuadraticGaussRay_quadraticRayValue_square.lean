-- Prove2me | solution 1 for OAI.QuadraticGaussRay.quadraticRayValue_square
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T00:45:20.483634+00:00
-- url     : https://prove2.me/submissions/e7d25799-5ae5-403f-8e2c-d4539523692f

import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_UniformKernelBounds
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_FiniteOperator
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_CrossFactorization
import Theorems.Thm_OAI_ActualEisensteinCubic_breveGaussianFourTerms_formula


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
open OAI.QuadraticGaussRay
open EisensteinEPrimaryPhase ActualEisensteinCoordinates ActualEisensteinCubic
namespace OAI.QuadraticGaussRay
theorem _root_.solution (r : Coord) (hr : odd r) :
    quadraticRayValue (mul r r) = 1 := by
  have hi : (Complex.I : ℂ)⁻¹ = -Complex.I := by
    apply inv_eq_of_mul_eq_one_right
    norm_num
  have h : mul r r = (1, 0) ∨ mul r r = (3, 3) ∨ mul r r = (0, 1) := by
    decide +revert
  rcases h with h | h | h
  · rw [h]
    change breveGaussianFourTerms 1 0 = 1
    rw [breveGaussianFourTerms_formula]
    norm_num [hi]
  · rw [h]
    change breveGaussianFourTerms 3 3 = 1
    rw [breveGaussianFourTerms_formula]
    norm_num [hi]
  · rw [h]
    change breveGaussianFourTerms 0 1 = 1
    rw [breveGaussianFourTerms_formula]
    norm_num [hi]
    ring
end OAI.QuadraticGaussRay
