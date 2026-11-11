-- Prove2me | solution 1 for OAI.CubicEisenstein.radial_bessel_coefficient_norm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T00:51:56.071052+00:00
-- url     : https://prove2.me/submissions/7d953cbc-3db2-4bde-b843-de7394787d09

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_BesselMellinTransform
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_VerticalContourShift

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
open Filter MeasureTheory
open scoped Classical BigOperators Topology
open Filter MeasureTheory
open scoped Classical BigOperators Topology
open OAI.CubicEisenstein
namespace OAI.CubicEisenstein
theorem _root_.solution (r q σ : ℝ) (hr : 0<r) (hq : 0<q) (a : ℂ) :
    ‖a*(r:ℂ)‖*‖((q*Real.sqrt r:ℝ):ℂ)‖^(-(2*σ+1))=
      q^(-(2*σ+1))*(‖a‖*r^(1/2-σ)) := by
  rw [norm_mul,Complex.norm_of_nonneg hr.le,
    Complex.norm_of_nonneg (mul_pos hq (Real.sqrt_pos.mpr hr)).le,
    Real.mul_rpow hq.le (Real.sqrt_nonneg r),Real.sqrt_eq_rpow,
    ←Real.rpow_mul hr.le]
  have hp : r*r^((1/2)*(-(2*σ+1)))=r^(1/2-σ) := by
    calc
      _=r^1*r^((1/2)*(-(2*σ+1))) := by rw [Real.rpow_one]
      _=r^(1+(1/2)*(-(2*σ+1))) := (Real.rpow_add hr _ _).symm
      _=_ := by congr 1;ring
  calc
    _=q^(-(2*σ+1))*(‖a‖*(r*r^((1/2)*(-(2*σ+1))))) := by ring
    _=_ := by rw [hp]
end OAI.CubicEisenstein
