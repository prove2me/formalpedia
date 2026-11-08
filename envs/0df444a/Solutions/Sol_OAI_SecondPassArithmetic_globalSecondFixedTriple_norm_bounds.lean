-- Prove2me | solution 1 for OAI.SecondPassArithmetic.globalSecondFixedTriple_norm_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T16:15:00.715206+00:00
-- url     : https://prove2.me/submissions/b3c67499-b120-4603-a28a-1f1381e7837a

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_SeedDefects
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_GlobalEncoding
import Theorems.Thm_OAI_SecondPassArithmetic_CubeCoordinates_support_pos
import Theorems.Thm_OAI_ActualEisensteinCubic_eisEmbedding_norm_sq_eq_absNorm_span
import Theorems.Thm_OAI_SecondPassArithmetic_cube_label_norm_bounds
import Theorems.Thm_OAI_SecondPassArithmetic_primeProductNorm_eq_ideal_norm


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
omit [∀ (i : ι), (span {p i}).IsMaximal]
namespace OAI.SecondPassArithmetic
theorem _root_.solution (hp : ∀ i,p i ≠ 0)
    (x : GlobalSecondData ι) (B H J T R : ℝ) (hB : 0 ≤ B) (hJ : 0 < J)
    (hb₁ : ‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ B)
    (hb₂ : ‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ B)
    (hactive : ‖eisEmbedding (∏ i ∈ cubeActiveSupport x.cube.support
      (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit,p i)‖ ≤ H)
    (hlabel : J ≤ ‖eisEmbedding (jLabel p x.cube.support
      (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)‖^2)
    (ht : primeProductNorm p x.firstCommon ≤ T)
    (hr : primeProductNorm p (x.source.sourceCommon\x.source.divisor) ≤ R) :
    (Ideal.absNorm (globalSecondFixedTriple p x).1 : ℝ) ≤ B*H/J ∧
    (Ideal.absNorm (globalSecondFixedTriple p x).2.1 : ℝ) ≤ T ∧
    (Ideal.absNorm (globalSecondFixedTriple p x).2.2 : ℝ) ≤ R := by
  obtain ⟨_,_,hb0⟩ := cube_label_norm_bounds p hp x.cube.support
    x.cube.leftExponent x.cube.rightExponent x.cube.leftBit x.cube.rightBit
    x.cube.support_pos B hB hb₁ hb₂
  refine ⟨?_,?_,?_⟩
  · change (Ideal.absNorm (Ideal.span {_}) : ℝ) ≤ _
    rw [← eisEmbedding_norm_sq_eq_absNorm_span]
    apply hb0.trans
    exact div_le_div₀ (mul_nonneg hB ((norm_nonneg _).trans hactive))
      (mul_le_mul_of_nonneg_left hactive hB) hJ hlabel
  · exact (primeProductNorm_eq_ideal_norm p _).symm ▸ ht
  · exact (primeProductNorm_eq_ideal_norm p _).symm ▸ hr
end OAI.SecondPassArithmetic
