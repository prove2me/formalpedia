-- Prove2me | solution 1 for OAI.SecondPassArithmetic.globalScaleVector_le_caps
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T04:26:17.88806+00:00
-- url     : https://prove2.me/submissions/6d77c573-0049-4cfd-a9e7-71168c11af39

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_CommonMasks
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_QuotientTopology
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_ScaleCaps
import Theorems.Thm_OAI_SecondPassArithmetic_globalSupported_small_norms
import Theorems.Thm_OAI_SecondPassArithmetic_globalCube_radical_bound
import Theorems.Thm_OAI_SecondPassArithmetic_globalSupported_divisor_bound
import Theorems.Thm_OAI_SecondPassArithmetic_globalSupported_cutoff_row_bound
import Theorems.Thm_OAI_SecondPassArithmetic_CubeCoordinates_support_pos
import Theorems.Thm_OAI_SecondPassArithmetic_cube_label_norm_bounds
import Theorems.Thm_OAI_SecondPassArithmetic_primeProductNorm_mono


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
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical
open OAI.SecondPassArithmetic
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm primeProduct)
open ConcreteTraceCRT (eisEmbedding)
variable {ι : Type*} [DecidableEq ι]
  (p : ι → OAI.SecondPassArithmetic.O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
include hp
namespace OAI.SecondPassArithmetic
theorem _root_.solution (ell B Y M Z : ℝ) (hell : 0 < ell) (hB : 0 ≤ B)
    (hY : 0 < Y) (hZ : 0 ≤ Z) (side : Bool) (x : GlobalSecondData ι) (hx : GlobalSecondAdmissible x)
    (hs : SecondSourceSupport p (globalFirstColumnScale p ell x side/primeProductNorm p x.firstCommon) M x.source)
    (hb₁ : ‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ B)
    (hb₂ : ‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ B)
    (hk : x.source.frequency ∈ firstCoreSecondCutoff p x.firstCommon (globalFirstColumnScale p ell x side)
      Y M Z x.source.sourceCommon x.source.divisor) :
    ∀ i,globalScaleVector p side x i ≤ globalNormCaps ell B Y M Z i := by
  obtain ⟨ha,hc,ht,hr,he,hv⟩ := globalSupported_small_norms p hp ell M hell side x hx hs
  have hd := globalSupported_divisor_bound p hp ell B M hell hB side x hx hs hb₁ hb₂
  have hrow := globalSupported_cutoff_row_bound p hp ell B Y M Z hell hB hY hZ side x hx hs hb₁ hb₂ hk
  have hJ := (cube_label_norm_bounds p hp x.cube.support x.cube.leftExponent x.cube.rightExponent
    x.cube.leftBit x.cube.rightBit x.cube.support_pos B hB hb₁ hb₂).1
  have hrad := globalCube_radical_bound p hp B hB x hb₁ hb₂
  have hactive : (globalCubeActiveRoot p x)^2 ≤ B^2 :=
    (primeProductNorm_mono p hp (Finset.filter_subset _ _)).trans hrad
  intro i
  fin_cases i
  · exact ha
  · exact hc
  · exact ht
  · exact hr
  · exact hJ
  · exact hd
  · exact he
  · exact hv
  · exact hrow
  · exact hactive
end OAI.SecondPassArithmetic
