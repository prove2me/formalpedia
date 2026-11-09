-- Prove2me | solution 1 for OAI.SecondPassArithmetic.globalSupported_small_norms
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T03:57:36.993169+00:00
-- url     : https://prove2.me/submissions/3b601947-1b56-4438-acb8-54ffd35e9fdc

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_CommonMasks
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_QuotientTopology
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_ScaleCaps
import Theorems.Thm_OAI_SecondPassArithmetic_primeProductNorm_ge_one
import Theorems.Thm_OAI_SecondPassArithmetic_primeProductNorm_mono

section
namespace OAI
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
namespace SecondPassArithmetic
section
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct bit parity retained b0Exponent aLabel jLabel j2Label squarefreeLabel b0Label)
variable {ι : Type*} [DecidableEq ι]
variable (p : ι → OAI.SecondPassArithmetic.O) [∀ i,(Ideal.span {p i}).IsMaximal]
end
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm)
open ConcreteTraceCRT (eisEmbedding)
section
variable {ι : Type*} [DecidableEq ι]
  (p : ι → OAI.SecondPassArithmetic.O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
end
end SecondPassArithmetic
open scoped BigOperators Classical SchwartzMap
namespace CanonicalQuadraticSieve
open ActualEisensteinCubic ConcretePrimeRowBridge IdealMobiusDivisorSum EisensteinSchwartzPoisson
end CanonicalQuadraticSieve
open scoped BigOperators Classical
namespace SecondPassArithmetic
section
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm)
open ConcreteTraceCRT (eisEmbedding)
variable {ι : Type*} [DecidableEq ι]
  (p : ι → OAI.SecondPassArithmetic.O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
end
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm primeProduct)
open ConcreteTraceCRT (eisEmbedding)
private theorem five_factor_bounds (a b c d e : ℝ) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hc : 1 ≤ c) (hd : 1 ≤ d) (he : 1 ≤ e) :
    a ≤ a*b*c*d*e ∧ b ≤ a*b*c*d*e ∧ c ≤ a*b*c*d*e ∧ d ≤ a*b*c*d*e ∧ e ≤ a*b*c*d*e := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · calc
      a = a*1*1*1*1 := by ring
      _ ≤ _ := by gcongr
  · calc
      b = 1*b*1*1*1 := by ring
      _ ≤ _ := by gcongr
  · calc
      c = 1*1*c*1*1 := by ring
      _ ≤ _ := by gcongr
  · calc
      d = 1*1*1*d*1 := by ring
      _ ≤ _ := by gcongr
  · calc
      e = 1*1*1*1*e := by ring
      _ ≤ _ := by gcongr
variable {ι : Type*} [DecidableEq ι]
  (p : ι → OAI.SecondPassArithmetic.O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
end SecondPassArithmetic
end
end OAI
end

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
omit [∀ (i : ι), (span {p i}).IsMaximal]
namespace OAI.SecondPassArithmetic
theorem _root_.solution (ell M : ℝ) (_hell : 0 < ell) (side : Bool)
    (x : GlobalSecondData ι) (hx : GlobalSecondAdmissible x)
    (hs : SecondSourceSupport p (globalFirstColumnScale p ell x side/primeProductNorm p x.firstCommon) M x.source) :
    primeProductNorm p (x.cube.sideDivisor side) ≤ ell*Real.exp M ∧
    primeProductNorm p x.common ≤ ell*Real.exp M ∧
    primeProductNorm p x.firstCommon ≤ ell*Real.exp M ∧
    primeProductNorm p (x.source.sourceCommon\x.source.divisor) ≤ ell*Real.exp M ∧
    primeProductNorm p x.source.divisor ≤ ell*Real.exp M ∧
    primeProductNorm p x.source.overlap ≤ ell*Real.exp M := by
  have ha := primeProductNorm_ge_one p hp (x.cube.sideDivisor side)
  have hc := primeProductNorm_ge_one p hp x.common
  have ht := primeProductNorm_ge_one p hp x.firstCommon
  have hg := primeProductNorm_ge_one p hp x.source.sourceCommon
  have hv := primeProductNorm_ge_one p hp x.source.overlap
  have hden : 0 < primeProductNorm p (x.cube.sideDivisor side)*primeProductNorm p x.common*primeProductNorm p x.firstCommon := by positivity
  have heq : (globalFirstColumnScale p ell x side/primeProductNorm p x.firstCommon)*Real.exp M =
      (ell*Real.exp M)/(primeProductNorm p (x.cube.sideDivisor side)*primeProductNorm p x.common*primeProductNorm p x.firstCommon) := by
    unfold globalFirstColumnScale
    ring
  have hprod := (le_div_iff₀ hden).mp (hs.2.trans_eq heq)
  have hprod' : primeProductNorm p (x.cube.sideDivisor side)*primeProductNorm p x.common*
      primeProductNorm p x.firstCommon*primeProductNorm p x.source.sourceCommon*primeProductNorm p x.source.overlap ≤ ell*Real.exp M := by
    convert hprod using 1 <;> first | rfl | ring
  obtain ⟨ha',hc',ht',hg',hv'⟩ := five_factor_bounds _ _ _ _ _ ha hc ht hg hv
  refine ⟨ha'.trans hprod',hc'.trans hprod',ht'.trans hprod',?_,?_,hv'.trans hprod'⟩
  · exact (primeProductNorm_mono p hp Finset.sdiff_subset).trans (hg'.trans hprod')
  · exact (primeProductNorm_mono p hp hx.2.1).trans (hg'.trans hprod')
end OAI.SecondPassArithmetic
