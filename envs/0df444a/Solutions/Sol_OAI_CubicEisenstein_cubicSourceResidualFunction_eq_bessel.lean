-- Prove2me | solution 1 for OAI.CubicEisenstein.cubicSourceResidualFunction_eq_bessel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T02:38:34.39103+00:00
-- url     : https://prove2.me/submissions/b0f93423-5924-47b2-a599-97030a433e7c

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_PrimePowerGaussSums
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_SourceBesselExpansion
import Theorems.Thm_OAI_CubicEisenstein_sourceBesselFunction_continuous
import Theorems.Thm_OAI_CubicEisenstein_sourceBesselFunction_represents_projection
import Theorems.Thm_OAI_CubicEisenstein_cubicSourceResidualFunction_continuous
import Theorems.Thm_OAI_CubicEisenstein_cubicSourceResidualFunction_represents_projection


set_option autoImplicit false
open OAI
noncomputable section
open OAI.CubicEisenstein
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
open scoped BigOperators Classical Topology
local notation "O" => ActualEisensteinCubic.O
namespace OAI.CubicEisenstein
theorem _root_.solution : cubicSourceResidualFunction=sourceBesselFunction := by
  have he : cubicSourceResidualFunction=ᵐ[hyperbolicVolume]sourceBesselFunction := by
    filter_upwards [cubicSourceResidualFunction_represents_projection,sourceBesselFunction_represents_projection]
      with w hw hs
    exact hw.symm.trans hs
  exact Measure.eq_of_ae_eq he cubicSourceResidualFunction_continuous sourceBesselFunction_continuous
end OAI.CubicEisenstein
