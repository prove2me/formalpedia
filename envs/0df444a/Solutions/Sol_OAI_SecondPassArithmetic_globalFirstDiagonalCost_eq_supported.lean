-- Prove2me | solution 1 for OAI.SecondPassArithmetic.globalFirstDiagonalCost_eq_supported
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T11:06:38.100434+00:00
-- url     : https://prove2.me/submissions/d7e4edef-e29c-4c71-b6a0-4a2fc0e8ee13

import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_DivisorTargets
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_NormalizedMass
import Theorems.Thm_OAI_SecondPassArithmetic_globalFirstColumnMass_zero_off_support

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
open scoped BigOperators Classical SchwartzMap
open OAI.SecondPassArithmetic
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm)
variable {ι : Type*} [DecidableEq ι]
  (p : ι → OAI.SecondPassArithmetic.O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hg : ∀i,lambda∉Ideal.span {p i})
include hp
namespace OAI.SecondPassArithmetic
theorem _root_.solution (pool : Finset ι) (s : Finset (GlobalFirstData ι))
    (w : GlobalFirstData ι → ℂ) (Ψ : O →* ℂ) (m : O) (g W : 𝓢(ℝ,ℂ))
    (ell M U : ℝ) (hell : 0<ell) (hM : ∀t,g t≠0 → |t|≤M)
    (hU : ell*Real.exp M≤U) (side : Bool) (Y : GlobalFirstData ι → ℝ) :
    globalFirstDiagonalCost p hg pool s w Ψ m g W ell side Y=
      globalFirstDiagonalCost p hg pool
        (s.filter (fun b => primeProductNorm p b.common≤U ∧ primeProductNorm p b.firstCommon≤U))
        w Ψ m g W ell side Y := by
  unfold globalFirstDiagonalCost
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro b hb hn
  have hoff : ¬(primeProductNorm p b.common≤U ∧ primeProductNorm p b.firstCommon≤U) := by
    intro h; exact hn (Finset.mem_filter.mpr ⟨hb,h⟩)
  have hz := globalFirstColumnMass_zero_off_support p hp hg pool b Ψ m g ell M U hell hM hU side hoff
  change globalFirstColumnMass p hg pool b Ψ m g ell side=0 at hz
  change ‖w b‖*(primeProductNorm p b.firstCommon)⁻¹*
    (|Y b| *‖EisensteinSchwartzPoisson.paperRadialFourier W 0‖*globalFirstColumnMass p hg pool b Ψ m g ell side)=0
  rw [hz,mul_zero,mul_zero]
end OAI.SecondPassArithmetic
