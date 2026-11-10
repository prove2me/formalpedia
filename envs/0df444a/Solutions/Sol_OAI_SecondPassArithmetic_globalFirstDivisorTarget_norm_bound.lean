-- Prove2me | solution 1 for OAI.SecondPassArithmetic.globalFirstDivisorTarget_norm_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T11:00:55.768116+00:00
-- url     : https://prove2.me/submissions/c6741196-b12a-4d40-991a-91c26aeeb1a0

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_SmoothTests
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_DivisorTargets
import Theorems.Thm_OAI_FirstPassCubeLabels_primeProductNorm_pos
import Theorems.Thm_OAI_SecondPassArithmetic_globalCube_radical_bound
import Theorems.Thm_OAI_SecondPassArithmetic_primeProductNorm_eq_ideal_norm


set_option autoImplicit false
open OAI
noncomputable section
open OAI.SecondPassArithmetic
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
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm primeProduct cubeActiveSupport)
open ConcreteTraceCRT (eisEmbedding)
open IdealMobiusDivisorSum (idealDivisors mem_idealDivisors)
variable {ι : Type*} [DecidableEq ι]
  (p : ι → OAI.SecondPassArithmetic.O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hinj : Function.Injective (fun i => Ideal.span {p i}))
include hp
omit [∀ (i : ι), (span {p i}).IsMaximal]
namespace OAI.SecondPassArithmetic
theorem _root_.solution (b : GlobalFirstData ι) (B U : ℝ)
    (hB : 0≤B) (hU : 0≤U) (hc : primeProductNorm p b.common≤U)
    (hb1 : ‖eisEmbedding (primeProduct p b.cube.support b.cube.leftExponent)‖^2≤B)
    (hb2 : ‖eisEmbedding (primeProduct p b.cube.support b.cube.rightExponent)‖^2≤B) :
    (Ideal.absNorm (globalFirstDivisorTarget p (globalFirstCountKey b)) : ℝ)≤U*B^2 := by
  have hrad := globalCube_radical_bound p hp B hB (b.append ⟨∅,∅,∅,1⟩) hb1 hb2
  change (Ideal.absNorm ((∏i∈b.common,Ideal.span {p i})*(∏i∈b.cube.support,Ideal.span {p i})) : ℝ)≤_
  rw [map_mul,Nat.cast_mul,←primeProductNorm_eq_ideal_norm,←primeProductNorm_eq_ideal_norm]
  exact mul_le_mul hc hrad (FirstPassCubeLabels.primeProductNorm_pos p hp _).le hU
end OAI.SecondPassArithmetic
