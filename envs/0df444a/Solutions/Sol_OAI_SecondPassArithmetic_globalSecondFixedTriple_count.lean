-- Prove2me | solution 1 for OAI.SecondPassArithmetic.globalSecondFixedTriple_count
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T16:26:09.76919+00:00
-- url     : https://prove2.me/submissions/5748745d-9ce6-46c6-8e4a-18f5ac7333c6

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_SeedDefects
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_GlobalEncoding
import Theorems.Thm_OAI_SecondPassArithmetic_globalSecondFixedTriple_nonzero
import Theorems.Thm_OAI_SecondPassArithmetic_globalSecondFixedTriple_norm_bounds
import Theorems.Thm_OAI_DescentFiberCost_fixed_triple_count


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
open FirstPassCubeLabels (primeProduct aLabel b0Label jLabel cubeActiveSupport primeProductNorm)
open ConcreteTraceCRT (eisEmbedding)
variable {ι : Type*} [DecidableEq ι]
  (p : ι → OAI.SecondPassArithmetic.O) [∀ i, (Ideal.span {p i}).IsMaximal]
namespace OAI.SecondPassArithmetic
theorem _root_.solution (hp : ∀ i,p i ≠ 0)
    (s : Finset (GlobalSecondData ι)) (B H J T R : ℝ)
    (hB : 0 ≤ B) (hJ : 0 < J) (hscale : 1 ≤ B*H/J) (hT : 1 ≤ T) (hR : 1 ≤ R)
    (hb₁ : ∀ x∈s, ‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ B)
    (hb₂ : ∀ x∈s, ‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ B)
    (hactive : ∀ x∈s, ‖eisEmbedding (∏ i ∈ cubeActiveSupport x.cube.support
      (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit,p i)‖ ≤ H)
    (hlabel : ∀ x∈s, J ≤ ‖eisEmbedding (jLabel p x.cube.support
      (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)‖^2)
    (ht : ∀ x∈s, primeProductNorm p x.firstCommon ≤ T)
    (hr : ∀ x∈s, primeProductNorm p (x.source.sourceCommon\x.source.divisor) ≤ R) :
    ((s.image (globalSecondFixedTriple p)).card : ℝ) ≤ 128^3*(B*H/J)*T*R := by
  apply DescentFiberCost.fixed_triple_count _ _ _ _ hscale hT hR
  · intro q hq
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hq
    exact globalSecondFixedTriple_nonzero p hp x
  · intro q hq
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hq
    exact globalSecondFixedTriple_norm_bounds p hp x B H J T R hB hJ
      (hb₁ x hx) (hb₂ x hx) (hactive x hx) (hlabel x hx) (ht x hx) (hr x hx)
end OAI.SecondPassArithmetic
