-- Prove2me | solution 1 for OAI.CompletedGauss.cusp_coefficient_normalization
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T19:31:42.503785+00:00
-- url     : https://prove2.me/submissions/afef0447-1341-493c-a733-98cc726e578e

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_LocalCutoffs
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_CompletedDyadicRows

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
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical
open OAI.CompletedGauss
open CompletedDyadic
namespace OAI.CompletedGauss
theorem _root_.solution (m n b : ℝ) (hn : 0<n) (hb : 0<b) :
    (3:ℝ)^(m/6)*Real.sqrt b/Real.sqrt ((3:ℝ)^m*n*b^3)=
      1/((3:ℝ)^(m/3)*Real.sqrt n*b) := by
  have hroot : Real.sqrt ((3:ℝ)^m)=(3:ℝ)^(m/6)*(3:ℝ)^(m/3) := by
    rw [Real.sqrt_eq_rpow,←Real.rpow_mul (by norm_num),←Real.rpow_add (by norm_num)]
    congr 1
    ring
  have hbroot : Real.sqrt (b^3)=b*Real.sqrt b := by
    rw [show b^3=b^2*b by ring,Real.sqrt_mul (sq_nonneg b),Real.sqrt_sq hb.le]
  rw [Real.sqrt_mul (mul_nonneg (by positivity) hn.le),Real.sqrt_mul (by positivity),hroot,hbroot]
  have hr1 : (3:ℝ)^(m/6)≠0 := ne_of_gt (Real.rpow_pos_of_pos (by norm_num) _)
  have hr2 : (3:ℝ)^(m/3)≠0 := ne_of_gt (Real.rpow_pos_of_pos (by norm_num) _)
  have hbn : Real.sqrt b≠0 := ne_of_gt (Real.sqrt_pos.mpr hb)
  field_simp
end OAI.CompletedGauss
