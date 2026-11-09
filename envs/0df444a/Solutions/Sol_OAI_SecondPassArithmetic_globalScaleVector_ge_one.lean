-- Prove2me | solution 1 for OAI.SecondPassArithmetic.globalScaleVector_ge_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T03:56:20.231888+00:00
-- url     : https://prove2.me/submissions/0df86992-0b93-4826-bad2-089bc5b98596

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_CommonMasks
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_QuotientTopology
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_ScaleCaps
import Theorems.Thm_OAI_SecondPassArithmetic_actualSecondRow_ne_zero
import Theorems.Thm_OAI_SecondPassArithmetic_element_norm_ge_one
import Theorems.Thm_OAI_SecondPassArithmetic_primeProductNorm_ge_one
import Theorems.Thm_OAI_SecondPassArithmetic_primeProduct_ne_zero


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
open OAI.SecondPassArithmetic
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm)
open ConcreteTraceCRT (eisEmbedding)
variable {ι : Type*} [DecidableEq ι]
  (p : ι → OAI.SecondPassArithmetic.O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
include hp
namespace OAI.SecondPassArithmetic
theorem _root_.solution (side : Bool) (x : GlobalSecondData ι) (hk : x.source.frequency ≠ 0) :
    ∀ i,1 ≤ globalScaleVector p side x i := by
  intro i
  fin_cases i
  · exact primeProductNorm_ge_one p hp (x.cube.sideDivisor side)
  · exact primeProductNorm_ge_one p hp x.common
  · exact primeProductNorm_ge_one p hp x.firstCommon
  · exact primeProductNorm_ge_one p hp (x.source.sourceCommon\x.source.divisor)
  · change 1 ≤ globalCubeJNorm p x
    exact element_norm_ge_one _ (primeProduct_ne_zero p hp x.cube.support _)
  · exact primeProductNorm_ge_one p hp x.firstDivisor
  · exact primeProductNorm_ge_one p hp x.source.divisor
  · exact primeProductNorm_ge_one p hp x.source.overlap
  · change 1 ≤ ‖eisEmbedding (actualSecondRow p x.firstDivisor x.source.divisor x.source.frequency)‖^2
    exact element_norm_ge_one _ (actualSecondRow_ne_zero p _ _ _ hk)
  · change 1 ≤ (globalCubeActiveRoot p x)^2
    exact element_norm_ge_one _ (Finset.prod_ne_zero_iff.mpr (fun i hi => hp i))
end OAI.SecondPassArithmetic
