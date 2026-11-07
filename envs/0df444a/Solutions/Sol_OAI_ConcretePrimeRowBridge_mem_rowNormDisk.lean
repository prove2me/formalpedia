-- Prove2me | solution 1 for OAI.ConcretePrimeRowBridge.mem_rowNormDisk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:18:55.109363+00:00
-- url     : https://prove2.me/submissions/aec8327c-395f-40cb-8562-e8ed095742f4

import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_PrimeExtraction
import Definitions.Def_OAI_NumberTheory_DirichletL_PrimeRows_NormFiberExtraction
import Theorems.Thm_OAI_ShortDraftLatticeCount_mem_rowNormBall_of_absNorm_le


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
open ActualEisensteinCubic ShortDraftHeckeBridge
open scoped Classical
namespace OAI.ConcretePrimeRowBridge
theorem _root_.solution {H : ℕ} {u : O} :
    u ∈ rowNormDisk H ↔
      0 < Ideal.absNorm (Ideal.span {u}) ∧
      Ideal.absNorm (Ideal.span {u}) ≤ H := by
  classical
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · intro h
    exact Finset.mem_filter.mpr
      ⟨ShortDraftLatticeCount.mem_rowNormBall_of_absNorm_le H u h.2, h⟩
end OAI.ConcretePrimeRowBridge
