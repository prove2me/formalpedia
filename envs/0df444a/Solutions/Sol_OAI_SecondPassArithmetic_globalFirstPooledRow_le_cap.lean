-- Prove2me | solution 1 for OAI.SecondPassArithmetic.globalFirstPooledRow_le_cap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T09:56:29.350706+00:00
-- url     : https://prove2.me/submissions/85fa8bbd-51b0-417c-8aab-0a5b3983ceda

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_PowerfulParts
import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_LogarithmicBins
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_RowCaps
import Theorems.Thm_OAI_FirstPassCubeLabels_primeProductNorm_pos
import Theorems.Thm_OAI_FirstPassCubeLabels_primeProductNorm_union
import Theorems.Thm_OAI_SecondPassArithmetic_globalCube_radical_bound
import Theorems.Thm_OAI_SecondPassArithmetic_globalLogRep_ge_one
import Theorems.Thm_OAI_SecondPassArithmetic_globalLogRep_pos
import Theorems.Thm_OAI_SecondPassArithmetic_globalScaleIndex_bounds
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
open OAI.SecondPassArithmetic
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm primeProduct)
open ConcreteTraceCRT (eisEmbedding)
variable {ι : Type*} [DecidableEq ι]
  (p : ι → OAI.SecondPassArithmetic.O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
include hp
namespace OAI.SecondPassArithmetic
theorem _root_.solution (K ell B F : ℝ)
    (hK : 0<K) (hell : 0<ell) (hB : 0<B) (hF : 0<F)
    (b : GlobalCubeBlock ι) (hadm : GlobalCubeAdmissible b)
    (hb₁ : ‖eisEmbedding (primeProduct p b.cube.support b.cube.leftExponent)‖^2≤B)
    (hb₂ : ‖eisEmbedding (primeProduct p b.cube.support b.cube.rightExponent)‖^2≤B) :
    globalFirstPooledRow p K ell B F true (b.withCommon ∅)≤globalFirstRowCap K ell B F := by
  let x := (b.withCommon ∅).append (⟨∅,∅,∅,1⟩ : SecondExpansionData ι)
  let j := globalScaleIndex p true x
  have hbds := globalScaleIndex_bounds p hp true x (by exact one_ne_zero)
  have hd := (hbds 5).1
  have hc := (hbds 1).2
  change globalLogRep j 5≤primeProductNorm p b.firstDivisor at hd
  change primeProductNorm p b.common≤globalLogRep j 1*Real.exp 1 at hc
  have hrad := globalCube_radical_bound p hp B hB.le x hb₁ hb₂
  have h1p := globalLogRep_pos j 1
  have hd' : globalLogRep j 5≤globalLogRep j 1*Real.exp 1*B^2 := by
    calc
      _ ≤ primeProductNorm p b.firstDivisor := hd
      _ ≤ primeProductNorm p (b.common∪b.cube.support) := primeProductNorm_mono p hp hadm.2.2
      _ = primeProductNorm p b.common*primeProductNorm p b.cube.support :=
        FirstPassCubeLabels.primeProductNorm_union p _ _ hadm.2.1
      _ ≤ (globalLogRep j 1*Real.exp 1)*B^2 :=
        mul_le_mul hc hrad (FirstPassCubeLabels.primeProductNorm_pos p hp _).le (by positivity)
  have h1 := globalLogRep_ge_one j 1
  have h4 := globalLogRep_ge_one j 4
  have h4p := globalLogRep_pos j 4
  have hm : globalLogRep j 1≤(globalLogRep j 1)^2*globalLogRep j 4 := by
    calc
      globalLogRep j 1 = globalLogRep j 1*1*1 := by ring
      _ ≤ globalLogRep j 1*globalLogRep j 1*globalLogRep j 4 := by gcongr
      _ = _ := by ring
  have hr : globalLogRep j 5/((globalLogRep j 1)^2*globalLogRep j 4)≤Real.exp 1*B^2 := by
    apply (div_le_iff₀ (mul_pos (sq_pos_of_pos h1p) h4p)).mpr
    calc
      _ ≤ globalLogRep j 1*Real.exp 1*B^2 := hd'
      _ ≤ ((globalLogRep j 1)^2*globalLogRep j 4)*Real.exp 1*B^2 := by gcongr
      _ = _ := by ring
  change Real.exp 1*ell^2*B^4*F^2*globalLogRep j 5/(K*(globalLogRep j 1)^2*globalLogRep j 4)≤_
  calc
    _ = (Real.exp 1*ell^2*B^4*F^2/K)*(globalLogRep j 5/((globalLogRep j 1)^2*globalLogRep j 4)) := by ring
    _ ≤ (Real.exp 1*ell^2*B^4*F^2/K)*(Real.exp 1*B^2) :=
      mul_le_mul_of_nonneg_left hr (by positivity)
    _ = globalFirstRowCap K ell B F := by unfold globalFirstRowCap; ring
end OAI.SecondPassArithmetic
