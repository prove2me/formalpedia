-- Prove2me | solution 1 for OAI.ShortDraftCRT.fixed_completion_congr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T23:11:10.950992+00:00
-- url     : https://prove2.me/submissions/65a8f3aa-0c03-4bf3-ab8a-6370fbe1f857

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_CuspAverage
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_BesselMellinTransform

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
open scoped BigOperators Classical
open OAI.ShortDraftCRT
variable {R : Type*} [CommRing R]
variable [IsDomain R]
namespace OAI.ShortDraftCRT
theorem _root_.solution (M c r r0 a a0 b b0 d d0 : R)
    (hc : c≠0) (hr : IsCoprime M r)
    (hdet : a*d-b*(c*r)=1) (hdet0 : a0*d0-b0*(c*r0)=1)
    (ha : M*c∣a-a0) (hd : M*c∣d-d0) (hrr : M∣r-r0) : M∣b-b0 := by
  have hprod : M*c∣a*d-a0*d0 := by
    have h1 := dvd_mul_of_dvd_left ha d
    have h2 := dvd_mul_of_dvd_right hd a0
    convert dvd_add h1 h2 using 1 ; ring
  have hcancel : M*c∣c*(b*r-b0*r0) := by
    convert hprod using 1
    linear_combination -hdet+hdet0
  have hbr : M∣b*r-b0*r0 := by
    rw [mul_comm M c] at hcancel
    exact (mul_dvd_mul_iff_left hc).mp hcancel
  have hsub : M∣(b-b0)*r := by
    have hsmall := dvd_mul_of_dvd_right hrr b0
    convert dvd_sub hbr hsmall using 1 ; ring
  exact hr.dvd_of_dvd_mul_right hsub
end OAI.ShortDraftCRT
