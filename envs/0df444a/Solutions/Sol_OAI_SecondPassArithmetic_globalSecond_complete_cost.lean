-- Prove2me | solution 1 for OAI.SecondPassArithmetic.globalSecond_complete_cost
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-08T19:56:47.384799+00:00
-- url     : https://prove2.me/submissions/bbfca64f-bb3f-4f8b-95fe-acf433ad5355

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_HighKernelGeometry
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_QuotientTopology
import Theorems.Thm_OAI_SecondPassArithmetic_globalCubeJNorm_pos
import Theorems.Thm_OAI_SecondPassArithmetic_globalCubeActiveRoot_pos
import Theorems.Thm_OAI_SecondPassArithmetic_globalBaseLabel_norm
import Theorems.Thm_OAI_FirstPassCubeLabels_primeProductNorm_pos


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
open OAI.SecondPassArithmetic
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm primeProduct jLabel b0Label cubeActiveSupport)
open ConcreteTraceCRT (eisEmbedding)
variable {ι : Type*} [DecidableEq ι]
  (p : ι → OAI.SecondPassArithmetic.O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
include hp
omit [∀ (i : ι), (span {p i}).IsMaximal]
namespace OAI.SecondPassArithmetic
theorem _root_.solution (K ell B F : ℝ) (hK : 0 < K) (hell : 0 < ell)
    (hB : 0 < B) (hF : 0 < F) (x : GlobalSecondData ι) (side : Bool) :
    (K/(primeProductNorm p x.firstDivisor*ell*B^2*F*globalCubeActiveRoot p x)) *
      (globalFirstRowScale p K ell B F x *
        ‖eisEmbedding (secondBaseLabel p x.cube.support x.common x.cube.leftExponent x.cube.rightExponent
          x.cube.leftBit x.cube.rightBit)‖^2*Real.exp 2/globalFirstColumnScale p ell x side) *
      ((B*globalCubeActiveRoot p x/globalCubeJNorm p x)*primeProductNorm p x.firstCommon*
        primeProductNorm p (x.source.sourceCommon\x.source.divisor)) =
    Real.exp 2*globalSecondDelta p B F x side*B^2/globalCubeJNorm p x := by
  rw [globalBaseLabel_norm]
  have hC := (FirstPassCubeLabels.primeProductNorm_pos p hp x.common).ne'
  have hd := (FirstPassCubeLabels.primeProductNorm_pos p hp x.firstDivisor).ne'
  have ha := (FirstPassCubeLabels.primeProductNorm_pos p hp (x.cube.sideDivisor side)).ne'
  have hJ := (globalCubeJNorm_pos p hp x).ne'
  have hc := (globalCubeActiveRoot_pos p hp x).ne'
  unfold globalFirstRowScale globalFirstColumnScale globalSecondDelta
  field_simp
end OAI.SecondPassArithmetic
