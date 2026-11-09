-- Prove2me | solution 1 for OAI.SecondPassArithmetic.globalSecondOuterWeight_bin_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T04:13:21.175004+00:00
-- url     : https://prove2.me/submissions/71cb6ae9-0771-4f91-8634-3d3d529b36d4

import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_ScaleCaps
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_PoissonComparison
import Theorems.Thm_OAI_SecondPassArithmetic_globalSecondOuterWeight_norm_le
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
open scoped BigOperators Classical
open OAI.SecondPassArithmetic
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm b0Label jLabel)
open ConcreteTraceCRT (eisEmbedding)
variable {ι : Type*} [DecidableEq ι]
  (p : ι → OAI.SecondPassArithmetic.O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,lambda ∉ Ideal.span {p i})
namespace OAI.SecondPassArithmetic
theorem _root_.solution
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (Ψ : O →* ℂ) (hΨ : ∀ a,‖Ψ a‖ ≤ 1) (m : O) (z : SecondRayIndex)
    (ell Y : ℝ) (hell : 0 < ell) (hY : 0 ≤ Y) (side : Bool) (x : GlobalSecondData ι)
    (hk : x.source.frequency ≠ 0) :
    ‖globalSecondOuterWeight p hp hcop hg Ψ m z ell Y side x‖ ≤
      globalPooledOuterBound z ell Y (globalScaleIndex p side x) := by
  apply (globalSecondOuterWeight_norm_le p hp hcop hg hinj hc Ψ hΨ m z ell Y hell hY side x).trans
  let j := globalScaleIndex p side x
  have ha := (globalScaleIndex_bounds p hp side x hk 0).2
  have hc' := (globalScaleIndex_bounds p hp side x hk 1).2
  have ht := (globalScaleIndex_bounds p hp side x hk 2).2
  have hr := (globalScaleIndex_bounds p hp side x hk 3).2
  change primeProductNorm p (x.cube.sideDivisor side) ≤ globalLogRep j 0*Real.exp 1 at ha
  change primeProductNorm p x.common ≤ globalLogRep j 1*Real.exp 1 at hc'
  change primeProductNorm p x.firstCommon ≤ globalLogRep j 2*Real.exp 1 at ht
  change primeProductNorm p (x.source.sourceCommon\x.source.divisor) ≤ globalLogRep j 3*Real.exp 1 at hr
  have hn : Y*primeProductNorm p x.firstCommon*primeProductNorm p (x.source.sourceCommon\x.source.divisor)/
      (globalFirstColumnScale p ell x side)^2 =
      Y*primeProductNorm p x.firstCommon*primeProductNorm p (x.source.sourceCommon\x.source.divisor)*
        (primeProductNorm p (x.cube.sideDivisor side))^2*(primeProductNorm p x.common)^2/ell^2 := by
    have hA := (FirstPassCubeLabels.primeProductNorm_pos p hp (x.cube.sideDivisor side)).ne'
    have hC := (FirstPassCubeLabels.primeProductNorm_pos p hp x.common).ne'
    unfold globalFirstColumnScale
    field_simp

  rw [hn]
  have h0 := (FirstPassCubeLabels.primeProductNorm_pos p hp (x.cube.sideDivisor side)).le
  have h1 := (FirstPassCubeLabels.primeProductNorm_pos p hp x.common).le
  have h2 := (FirstPassCubeLabels.primeProductNorm_pos p hp x.firstCommon).le
  have h3 := (FirstPassCubeLabels.primeProductNorm_pos p hp (x.source.sourceCommon\x.source.divisor)).le
  have hr0 := (globalLogRep_pos j 0).le
  have hr1 := (globalLogRep_pos j 1).le
  have hr2 := (globalLogRep_pos j 2).le
  have hr3 := (globalLogRep_pos j 3).le
  calc
    _ ≤ (Y*(globalLogRep j 2*Real.exp 1)*(globalLogRep j 3*Real.exp 1)*
      (globalLogRep j 0*Real.exp 1)^2*(globalLogRep j 1*Real.exp 1)^2/ell^2)*‖secondRayCoefficient z‖ := by gcongr
    _ = _ := by unfold globalPooledOuterBound;ring
end OAI.SecondPassArithmetic
