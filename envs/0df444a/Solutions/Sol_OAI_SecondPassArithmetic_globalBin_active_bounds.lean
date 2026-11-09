-- Prove2me | solution 1 for OAI.SecondPassArithmetic.globalBin_active_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T04:51:52.128209+00:00
-- url     : https://prove2.me/submissions/4ede6582-27ce-4e3b-b12b-5fcdae3bcf01

import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_ArithmeticBins
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_HyperbolicVolume
import Theorems.Thm_OAI_SecondPassArithmetic_globalCubeActiveRoot_pos
import Theorems.Thm_OAI_SecondPassArithmetic_globalLogRep_pos
import Theorems.Thm_OAI_SecondPassArithmetic_globalScaleIndex_bounds


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
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups
open scoped BigOperators Classical
open OAI.SecondPassArithmetic
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct primeProductNorm)
open ConcreteTraceCRT (eisEmbedding)
variable {ι : Type*} [DecidableEq ι]
  (p : ι → OAI.SecondPassArithmetic.O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
include hp
namespace OAI.SecondPassArithmetic
theorem _root_.solution (side : Bool) (x : GlobalSecondData ι) (hk : x.source.frequency ≠ 0) :
    Real.sqrt (globalLogRep (globalScaleIndex p side x) 9) ≤ globalCubeActiveRoot p x ∧
    globalCubeActiveRoot p x ≤ Real.sqrt (globalLogRep (globalScaleIndex p side x) 9)*Real.exp 1 := by
  have hr := globalScaleIndex_bounds p hp side x hk 9
  change globalLogRep (globalScaleIndex p side x) 9 ≤ (globalCubeActiveRoot p x)^2 ∧
    (globalCubeActiveRoot p x)^2 ≤ globalLogRep (globalScaleIndex p side x) 9*Real.exp 1 at hr
  have hx := (globalCubeActiveRoot_pos p hp x).le
  constructor
  · exact Real.sqrt_le_iff.mpr ⟨hx,hr.1⟩
  · have hs := Real.sq_sqrt (globalLogRep_pos (globalScaleIndex p side x) 9).le
    have he : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
    have hrep := (globalLogRep_pos (globalScaleIndex p side x) 9).le
    have hm : (globalCubeActiveRoot p x)^2 ≤
        (Real.sqrt (globalLogRep (globalScaleIndex p side x) 9)*Real.exp 1)^2 := by
      calc
        _ ≤ globalLogRep (globalScaleIndex p side x) 9*Real.exp 1 := hr.2
        _ ≤ globalLogRep (globalScaleIndex p side x) 9*(Real.exp 1)^2 := by gcongr; nlinarith
        _ = _ := by rw [mul_pow,hs]
    exact (sq_le_sq₀ hx (mul_nonneg (Real.sqrt_nonneg _) (Real.exp_pos 1).le)).mp hm
end OAI.SecondPassArithmetic
