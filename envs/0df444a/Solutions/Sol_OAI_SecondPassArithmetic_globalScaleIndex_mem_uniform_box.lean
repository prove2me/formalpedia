-- Prove2me | solution 1 for OAI.SecondPassArithmetic.globalScaleIndex_mem_uniform_box
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T05:55:30.115794+00:00
-- url     : https://prove2.me/submissions/4316cd47-f3c2-4b98-a112-c9d2a3511243

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_FundamentalDomain
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_GlobalScales
import Theorems.Thm_OAI_SecondPassArithmetic_globalRowScaleFloor_pos
import Theorems.Thm_OAI_SecondPassArithmetic_globalNormCaps_antitone_row
import Theorems.Thm_OAI_SecondPassArithmetic_globalRowScaleFloor_le_pooled
import Theorems.Thm_OAI_SecondPassArithmetic_globalPooledRowScale_pos
import Theorems.Thm_OAI_SecondPassArithmetic_globalScaleIndex_mem_box
import Theorems.Thm_OAI_SecondPassArithmetic_globalScaleVector_le_caps


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
open FirstPassCubeLabels (primeProduct primeProductNorm)
open ConcreteTraceCRT (eisEmbedding)
variable {ι : Type*} [DecidableEq ι]
  (p : ι → OAI.SecondPassArithmetic.O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
include hp
namespace OAI.SecondPassArithmetic
theorem _root_.solution (K ell B F M H : ℝ)
    (hK : 0 < K) (hell : 0 < ell) (hB : 0 < B) (hF : 0 < F) (hH : 0 ≤ H)
    (side : Bool) (x : GlobalSecondData ι) (hx : GlobalSecondAdmissible x)
    (hs : SecondSourceSupport p (globalFirstColumnScale p ell x side/primeProductNorm p x.firstCommon) M x.source)
    (hb₁ : ‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ B)
    (hb₂ : ‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ B)
    (hk0 : x.source.frequency ≠ 0)
    (hk : x.source.frequency ∈ firstCoreSecondCutoff p x.firstCommon (globalFirstColumnScale p ell x side)
      (globalPooledRowScale K ell B F (globalScaleIndex p side x)) M H x.source.sourceCommon x.source.divisor) :
    globalScaleIndex p side x ∈
      globalLogBox (globalNormCaps ell B (globalRowScaleFloor K ell B F M) M H) := by
  have hY := globalPooledRowScale_pos K ell B F hK hell hB hF (globalScaleIndex p side x)
  have hfloor := globalRowScaleFloor_pos K ell B F M hK hell hB hF
  have hlower := globalRowScaleFloor_le_pooled p hp K ell B F M hK hell hB hF side x hx hk0 hs hb₁ hb₂
  have hcaps := globalScaleVector_le_caps p hp ell B _ M H hell hB.le hY hH side x hx hs hb₁ hb₂ hk
  apply globalScaleIndex_mem_box p hp side x hk0
  intro i
  exact (hcaps i).trans (globalNormCaps_antitone_row ell B _ _ M H hfloor hlower hH i)
end OAI.SecondPassArithmetic
