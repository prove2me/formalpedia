-- Prove2me | solution 1 for OAI.SecondPassArithmetic.globalFirstFamilyWeight_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T08:56:06.103193+00:00
-- url     : https://prove2.me/submissions/0c9235e6-6c7d-4ccf-8d7e-f05e833d5a78

import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_SquarefreeTransfer
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_CubeBlocks
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_PowerfulParts
import Theorems.Thm_OAI_FirstPassCubeLabels_coreRayCoefficient_norm_le
import Theorems.Thm_OAI_SecondPassArithmetic_firstCoreOuter_norm_le
import Theorems.Thm_OAI_SecondPassArithmetic_mem_globalFirstFamilySet


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
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct firstLogDensity)
open ConcreteTraceCRT (eisEmbedding)
open RayFourExpansion (RayCharacter crossCoeff gCoeff)
variable {ι : Type*} [DecidableEq ι]
  (p : ι → OAI.SecondPassArithmetic.O) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hg : ∀ i,lambda ∉ Ideal.span {p i})
namespace OAI.SecondPassArithmetic
theorem _root_.solution (blocks : Finset (GlobalCubeBlock ι))
    (w : GlobalCubeBlock ι → ℝ) (Γ : ℝ) (hw : ∀ b∈blocks,0≤w b ∧ w b≤Γ)
    (Ψ : O →* ℂ) (hΨ : ∀ a,‖Ψ a‖≤1) (m : O) (side : Bool) (r : FirstCoreIndex)
    (pool : Finset ι) (d : GlobalFirstData ι) (hd : d∈globalFirstFamilySet pool blocks) :
    0≤globalFirstFamilyWeight p hg w Ψ m side r d ∧
      globalFirstFamilyWeight p hg w Ψ m side r d≤Γ*firstCoreUniformWeight r := by
  have hw' := hw d.block ((mem_globalFirstFamilySet pool blocks d).mp hd).1
  constructor
  · exact mul_nonneg hw'.1 (norm_nonneg _)
  · have h1 := firstCoreOuter_norm_le p hg d.cube.support
      (fun i => d.cube.leftExponent i+d.cube.rightExponent i) d.cube.leftBit d.cube.rightBit
      side Ψ m d.firstCommon r
    have h2 := FirstPassCubeLabels.coreRayCoefficient_norm_le p
      (FirstPassCubeLabels.cubeOddSupport d.cube.support
        (fun i => d.cube.leftExponent i+d.cube.rightExponent i) d.cube.leftBit d.cube.rightBit)
      side r.1 r.2.1 r.2.2
    have hnorm : ‖firstCoreOuter p hg d.cube.support
        (fun i => d.cube.leftExponent i+d.cube.rightExponent i) d.cube.leftBit d.cube.rightBit
        side Ψ m d.firstCommon r‖≤firstCoreUniformWeight r :=
      (h1.trans (mul_le_of_le_one_right (norm_nonneg _) (hΨ _))).trans h2
    exact mul_le_mul hw'.2 hnorm (norm_nonneg _) (hw'.1.trans hw'.2)
end OAI.SecondPassArithmetic
