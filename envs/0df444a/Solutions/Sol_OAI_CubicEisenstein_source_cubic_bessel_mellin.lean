-- Prove2me | solution 1 for OAI.CubicEisenstein.source_cubic_bessel_mellin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T23:53:37.005769+00:00
-- url     : https://prove2.me/submissions/0cfff7ba-8c4f-49ba-85ff-25d52d9355d1

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_CuspAverage
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_BesselMellinTransform
import Theorems.Thm_OAI_CubicEisenstein_schlafliBesselK_cubic_scaled_mellin

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
open OAI.CubicEisenstein
open Filter MeasureTheory
open scoped BigOperators Classical Topology
open Finset AddChar MulChar EisensteinEmbedding
namespace OAI.CubicEisenstein
theorem _root_.solution (s freq : ℂ)
    (hs : -(1/3)<s.re) (hfreq : freq≠0) :
    (∫v : ℝ in Set.Ioi 0,(v:ℂ)^(2*s)*schlafliBesselK (1/3) (4*Real.pi*‖freq‖*v)) =
      ((2:ℂ)^(2*s-1)*Complex.Gamma (s+1/3)*Complex.Gamma (s+2/3))/
        ((4*Real.pi*‖freq‖:ℝ):ℂ)^(2*s+1) := by
  have hc : 0<4*Real.pi*‖freq‖ := by positivity
  have ht : 1/3<(2*s+1).re := by norm_num; linarith
  have hh := schlafliBesselK_cubic_scaled_mellin (2*s+1) (4*Real.pi*‖freq‖) ht hc
  rw [show (2*s+1:ℂ)-1=2*s by ring,
    show (2*s+1:ℂ)-2=2*s-1 by ring,
    show ((2*s+1:ℂ)-1/3)/2=s+1/3 by ring,
    show ((2*s+1:ℂ)+1/3)/2=s+2/3 by ring,Complex.cpow_neg] at hh
  rw [hh]
  ring
end OAI.CubicEisenstein
