-- Prove2me | solution 1 for OAI.SecondPassArithmetic.ceil_strict_of_half
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-08T19:42:03.238386+00:00
-- url     : https://prove2.me/submissions/7e938470-d04b-49a7-bdec-7a2a31079418

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_HighKernelGeometry
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_QuotientTopology

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
open FirstPassCubeLabels (primeProductNorm primeProduct)
open ConcreteTraceCRT (eisEmbedding)
namespace OAI.SecondPassArithmetic
theorem _root_.solution {a b : ℝ} (hb : 2 ≤ b) (ha : a ≤ b/2) : ⌈a⌉₊ < ⌈b⌉₊ := by
  have hc : b ≤ (⌈b⌉₊ : ℝ) := Nat.le_ceil b
  have hn : 2 ≤ ⌈b⌉₊ := by exact_mod_cast (hb.trans hc)
  have hn1 : 1 ≤ ⌈b⌉₊ := by omega
  have hbound : a ≤ ((⌈b⌉₊-1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hn1,Nat.cast_one]
    have hh : (2 : ℝ) ≤ ⌈b⌉₊ := by exact_mod_cast hn
    linarith
  have hf : ⌈a⌉₊ ≤ ⌈b⌉₊-1 := Nat.ceil_le.mpr hbound
  omega
end OAI.SecondPassArithmetic
