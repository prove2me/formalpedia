-- Prove2me | solution 1 for OAI.SecondPassArithmetic.globalBin_mask_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T05:04:59.474597+00:00
-- url     : https://prove2.me/submissions/51285667-48e3-4a2b-b0cb-98d0a8cae2f6

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_HyperbolicVolume
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_UniformTransfer
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_GlobalBinLoss
import Theorems.Thm_OAI_ActualEisensteinCubic_eisEmbedding_norm_sq_eq_absNorm_span
import Theorems.Thm_OAI_FirstPassCubeLabels_primeProductNorm_pos
import Theorems.Thm_OAI_SecondPassArithmetic_CubeCoordinates_support_pos
import Theorems.Thm_OAI_SecondPassArithmetic_cube_label_norm_bounds
import Theorems.Thm_OAI_SecondPassArithmetic_globalLogRep_ge_one
import Theorems.Thm_OAI_SecondPassArithmetic_globalLogRep_pos
import Theorems.Thm_OAI_SecondPassArithmetic_globalScaleIndex_bounds
import Theorems.Thm_OAI_SecondPassArithmetic_globalSecondMask_span
import Theorems.Thm_OAI_SecondPassIntegration_restored_child_mask_norm


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
theorem _root_.solution (B F : ℝ) (hB : 0 < B) (hF : 1 ≤ F)
    (side : Bool) (x : GlobalSecondData ι) (hk : x.source.frequency ≠ 0) (m : O)
    (hb₁ : ‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ B)
    (hb₂ : ‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ B) :
    ‖eisEmbedding (fixedTripleMask m (globalSecondFixedTriple p x))‖^2 ≤
      ‖eisEmbedding m‖^2*(Real.exp 1)^2*globalPooledDelta B F (globalScaleIndex p side x) := by
  let j := globalScaleIndex p side x
  have hb0 := (cube_label_norm_bounds p hp x.cube.support x.cube.leftExponent x.cube.rightExponent
    x.cube.leftBit x.cube.rightBit x.cube.support_pos B hB.le hb₁ hb₂).2.1
  have he : ‖eisEmbedding (fixedTripleMask m (globalSecondFixedTriple p x))‖^2 =
      ‖eisEmbedding (globalSecondMask p m x)‖^2 := by
    rw [eisEmbedding_norm_sq_eq_absNorm_span,eisEmbedding_norm_sq_eq_absNorm_span,globalSecondMask_span]
  rw [he]
  have ht := (globalScaleIndex_bounds p hp side x hk 2).2
  have hr := (globalScaleIndex_bounds p hp side x hk 3).2
  change primeProductNorm p x.firstCommon ≤ globalLogRep j 2*Real.exp 1 at ht
  change primeProductNorm p (x.source.sourceCommon\x.source.divisor) ≤ globalLogRep j 3*Real.exp 1 at hr
  have ht0 := (FirstPassCubeLabels.primeProductNorm_pos p hp x.firstCommon).le
  have hr0 := (FirstPassCubeLabels.primeProductNorm_pos p hp (x.source.sourceCommon\x.source.divisor)).le
  have hj2 := (globalLogRep_pos j 2).le
  have hj3 := (globalLogRep_pos j 3).le
  have ha := globalLogRep_ge_one j 0
  change ‖eisEmbedding ((m*_*_)*∏ i∈x.firstCommon,p i)‖^2 ≤ _
  rw [SecondPassIntegration.restored_child_mask_norm]
  calc
    _ ≤ ‖eisEmbedding m‖^2*B*(globalLogRep j 3*Real.exp 1)*(globalLogRep j 2*Real.exp 1) := by gcongr
    _ ≤ ‖eisEmbedding m‖^2*(B*F*globalLogRep j 0)*(globalLogRep j 3*Real.exp 1)*(globalLogRep j 2*Real.exp 1) := by
      gcongr
      calc
        B = B*1*1 := by ring
        _ ≤ _ := by gcongr
    _ = _ := by unfold globalPooledDelta;ring
end OAI.SecondPassArithmetic
