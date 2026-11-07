-- Prove2me | solution 1 for OAI.CubicRamified.symbol_lambda_congr_mod_nine
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:23:30.976041+00:00
-- url     : https://prove2.me/submissions/17d059cc-e0f9-4402-9b42-11cbd33d41d7

import Definitions.Def_OAI_NumberTheory_DirichletL_Reciprocity_CubicJacobi
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_ReflectionBrackets
import Definitions.Def_OAI_NumberTheory_DirichletL_Reciprocity_RamifiedSymbol
import Theorems.Thm_OAI_CubicRamified_symbol_lambda_eq_linearRay
import Theorems.Thm_OAI_CubicRamified_linearRay_congr_mod_nine

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
namespace OAI.CubicRamified
theorem _root_.solution (x y : O)
    (hx : lambda ^ 2 ∣ x-1) (hy : lambda ^ 2 ∣ y-1) (hxy : (9 : O) ∣ x-y) :
    symbol lambda x = symbol lambda y := by
  rw [symbol_lambda_eq_linearRay x hx, symbol_lambda_eq_linearRay y hy]
  exact linearRay_congr_mod_nine 1 0 x y hx hy hxy
end OAI.CubicRamified
