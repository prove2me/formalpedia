-- Prove2me | solution 1 for OAI.CubicEisenstein.mobiusSpatialDenominator_contDiff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T09:58:38.723743+00:00
-- url     : https://prove2.me/submissions/3ed5b423-6b31-4a70-9073-bdbe68e4be34

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_PowerfulParts
import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_LogarithmicBins
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_RowCaps

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
open scoped BigOperators Classical
open scoped BigOperators Classical
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Matrix ContDiff
open OAI.CubicEisenstein
namespace OAI.CubicEisenstein
theorem _root_.solution (g : SL(2,ℂ)) : ContDiff ℝ ∞ (mobiusSpatialDenominator g) := by
  unfold mobiusSpatialDenominator
  have hz : ContDiff ℝ ∞ (fun p => g 1 0*spatialHorizontal p+g 1 1) :=
    (contDiff_const.mul spatialHorizontal_contDiff).add contDiff_const
  have hre := Complex.reCLM.contDiff.comp hz
  have him := Complex.imCLM.contDiff.comp hz
  change ContDiff ℝ ∞ (fun p =>
    (g 1 0*spatialHorizontal p+g 1 1).re*(g 1 0*spatialHorizontal p+g 1 1).re+
    (g 1 0*spatialHorizontal p+g 1 1).im*(g 1 0*spatialHorizontal p+g 1 1).im+
    Complex.normSq (g 1 0)*(p 2)^2)
  exact ((hre.mul hre).add (him.mul him)).add (contDiff_const.mul ((contDiff_apply ℝ ℝ 2).pow 2))
end OAI.CubicEisenstein
