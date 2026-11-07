-- Prove2me | solution 1 for OAI.ConcretePrimeRowBridge.columnWeight_norm_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:22:05.47136+00:00
-- url     : https://prove2.me/submissions/657c1261-8024-45c4-af7c-ff6c9526de92

import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_PrimeExtraction
import Definitions.Def_OAI_NumberTheory_DirichletL_PrimeRows_NormFiberExtraction
import Theorems.Thm_OAI_ConcretePrimeRowBridge_baseChangeWeight_norm_le_one

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
open OAI.ConcretePrimeRowBridge
open ActualEisensteinCubic ShortDraftHeckeBridge
namespace OAI.ConcretePrimeRowBridge
theorem _root_.solution {q : ℕ}
    (χ : DirichletCharacter ℂ q) (W : ℕ → ℂ)
    (hW : ∀ n, ‖W n‖ ≤ 1) (x : O) :
    ‖columnWeight χ W x‖ ≤ 1 := by
  rw [columnWeight, norm_mul]
  have hμ := baseChangeWeight_norm_le_one χ (Ideal.span {x})
  have hW' := hW (Ideal.absNorm (Ideal.span {x}))
  exact (mul_le_mul hμ hW' (norm_nonneg _) (by positivity)).trans (by norm_num)
end OAI.ConcretePrimeRowBridge
