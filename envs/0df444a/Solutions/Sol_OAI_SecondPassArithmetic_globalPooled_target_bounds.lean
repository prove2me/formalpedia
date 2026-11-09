-- Prove2me | solution 1 for OAI.SecondPassArithmetic.globalPooled_target_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T04:04:18.096095+00:00
-- url     : https://prove2.me/submissions/1b148656-b9a8-4a17-a7a2-48d2082e0e58

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_CommonMasks
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_QuotientTopology
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_ScaleCaps
import Theorems.Thm_OAI_SecondPassArithmetic_globalLogRep_pos
import Theorems.Thm_OAI_SecondPassArithmetic_globalScaleVector_ge_one
import Theorems.Thm_OAI_SecondPassArithmetic_globalScaleIndex_bounds
import Theorems.Thm_OAI_SecondPassArithmetic_globalBaseLabel_norm
import Theorems.Thm_OAI_SecondPassArithmetic_secondSupportNewLabel_norm


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
open FirstPassCubeLabels (primeProductNorm)
open ConcreteTraceCRT (eisEmbedding)
variable {ι : Type*} [DecidableEq ι]
  (p : ι → OAI.SecondPassArithmetic.O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
include hp
namespace OAI.SecondPassArithmetic
theorem _root_.solution (side : Bool) (x : GlobalSecondData ι) (hk : x.source.frequency ≠ 0) :
    let j := globalScaleIndex p side x
    (Ideal.absNorm (SecondPassFiber.newLabel (globalSecondTuple p x)) : ℝ) ≤ globalPooledLabelScale j ∧
    ‖eisEmbedding (SecondPassFiber.newRow (globalSecondTuple p x))‖^2 ≤ globalLogRep j 8*Real.exp 1 := by
  let j := globalScaleIndex p side x
  have hb (i : Fin 10) := (globalScaleIndex_bounds p hp side x hk i).2
  refine ⟨?_,hb 8⟩
  have he : (Ideal.absNorm (SecondPassFiber.newLabel (globalSecondTuple p x)) : ℝ) =
      globalScaleVector p side x 1*globalScaleVector p side x 4*
        globalScaleVector p side x 6*globalScaleVector p side x 7 := by
    rw [show SecondPassFiber.newLabel (globalSecondTuple p x) =
      secondSupportNewLabel p x.cube.support x.cube.leftExponent x.cube.rightExponent x.cube.leftBit x.cube.rightBit
        (expansionSupportData x.common x.firstDivisor x.source) from rfl,
      secondSupportNewLabel_norm,globalBaseLabel_norm]
    rfl
  rw [he]
  calc
    _ ≤ (globalLogRep j 1*Real.exp 1)*(globalLogRep j 4*Real.exp 1)*
        (globalLogRep j 6*Real.exp 1)*(globalLogRep j 7*Real.exp 1) := by
      have hpos (i : Fin 10) := (globalScaleVector_ge_one p hp side x hk i).trans' (by norm_num : (0:ℝ) ≤ 1)
      have hr1 := (globalLogRep_pos j 1).le
      have hr4 := (globalLogRep_pos j 4).le
      have hr6 := (globalLogRep_pos j 6).le
      have hr7 := (globalLogRep_pos j 7).le
      gcongr <;> first | exact hpos _ | exact hb _
    _ = globalPooledLabelScale j := by
      unfold globalPooledLabelScale
      rw [show (4:ℝ)=1+1+1+1 by norm_num,Real.exp_add,Real.exp_add,Real.exp_add]
      ring
end OAI.SecondPassArithmetic
