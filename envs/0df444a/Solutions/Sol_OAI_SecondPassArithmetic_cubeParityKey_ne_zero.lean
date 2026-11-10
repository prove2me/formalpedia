-- Prove2me | solution 1 for OAI.SecondPassArithmetic.cubeParityKey_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T10:53:43.543277+00:00
-- url     : https://prove2.me/submissions/1fdf5fea-b866-47df-8cad-8f18f0b52d1c

import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_RowCaps
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_SmoothTests
import Theorems.Thm_OAI_SecondPassArithmetic_primeProduct_ne_zero


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
open scoped BigOperators Classical
open OAI.SecondPassArithmetic
open ActualEisensteinCubic
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm primeProduct aLabel squarefreeLabel b0Label j2Label cubeActiveSupport)
open ConcreteTraceCRT (eisEmbedding)
open IdealMobiusDivisorSum (idealDivisors mem_idealDivisors)
variable {ι : Type*} [DecidableEq ι]
  (p : ι → OAI.SecondPassArithmetic.O) [∀ i,(Ideal.span {p i}).IsMaximal]
variable (hp : ∀ i,p i≠0)
include hp
omit [∀ (i : ι), (span {p i}).IsMaximal]
namespace OAI.SecondPassArithmetic
theorem _root_.solution (x : CubeCoordinates ι) :
    (cubeParityKey p x).1≠0 ∧ (cubeParityKey p x).2≠0 := by
  constructor
  · exact (Ideal.span_singleton_eq_bot.not).mpr (primeProduct_ne_zero p hp _ _)
  · exact (Ideal.span_singleton_eq_bot.not).mpr
      (mul_ne_zero (primeProduct_ne_zero p hp _ _) (primeProduct_ne_zero p hp _ _))
end OAI.SecondPassArithmetic
