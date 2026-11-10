-- Prove2me | solution 1 for OAI.SecondPassArithmetic.globalFirstRowScale_le_pooled
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T09:51:24.565911+00:00
-- url     : https://prove2.me/submissions/5009d29e-ef2a-4053-bb4b-3edfd9814ff0

import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_SourceTransfer
import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_LogarithmicBins
import Theorems.Thm_OAI_FirstPassCubeLabels_primeProductNorm_pos
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
open OAI.SecondPassArithmetic
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm primeProduct aLabel dilationLabel jLabel cubeActiveSupport)
open ConcreteTraceCRT (eisEmbedding)
variable {ι : Type*} [DecidableEq ι]
  (p : ι → OAI.SecondPassArithmetic.O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
include hp
namespace OAI.SecondPassArithmetic
theorem _root_.solution (K ell B F : ℝ)
    (hK : 0<K) (hell : 0<ell) (hB : 0<B) (hF : 0<F) (b : GlobalCubeBlock ι) :
    globalFirstRowScale p K ell B F ((b.withCommon ∅).append ⟨∅,∅,∅,1⟩) ≤
      globalFirstPooledRow p K ell B F true (b.withCommon ∅) := by
  let x := (b.withCommon ∅).append (⟨∅,∅,∅,1⟩ : SecondExpansionData ι)
  let j := globalScaleIndex p true x
  have hbds := globalScaleIndex_bounds p hp true x (by exact one_ne_zero)
  have hd := (hbds 5).2
  have hc := (hbds 1).1
  have hJ := (hbds 4).1
  change primeProductNorm p b.firstDivisor≤globalLogRep j 5*Real.exp 1 at hd
  change globalLogRep j 1≤primeProductNorm p b.common at hc
  change globalLogRep j 4≤globalCubeJNorm p x at hJ
  change ell^2*B^4*F^2*primeProductNorm p b.firstDivisor/
      (K*(primeProductNorm p b.common)^2*globalCubeJNorm p x) ≤
    Real.exp 1*ell^2*B^4*F^2*globalLogRep j 5/(K*(globalLogRep j 1)^2*globalLogRep j 4)
  have hdpos := (FirstPassCubeLabels.primeProductNorm_pos p hp b.firstDivisor).le
  have h5 := (globalLogRep_pos j 5).le
  apply div_le_div₀ (by positivity)
  · calc
      _ ≤ ell^2*B^4*F^2*(globalLogRep j 5*Real.exp 1) := by gcongr
      _ = _ := by ring
  · exact mul_pos (mul_pos hK (sq_pos_of_pos (globalLogRep_pos j 1))) (globalLogRep_pos j 4)
  · exact mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (globalLogRep_pos j 1).le hc 2) hK.le)
      hJ (globalLogRep_pos j 4).le (by positivity)
end OAI.SecondPassArithmetic
