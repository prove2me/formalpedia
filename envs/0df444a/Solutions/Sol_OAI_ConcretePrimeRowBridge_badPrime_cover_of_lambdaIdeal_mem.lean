-- Prove2me | solution 1 for OAI.ConcretePrimeRowBridge.badPrime_cover_of_lambdaIdeal_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:22:38.588643+00:00
-- url     : https://prove2.me/submissions/d5ebdb5f-554d-42c7-bf45-ef3239c5d680

import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_PrimeExtraction
import Definitions.Def_OAI_NumberTheory_DirichletL_PrimeRows_NormFiberExtraction
import Theorems.Thm_OAI_ConcretePrimeRowBridge_goodLambdaIdeal_maximal

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
open ShortDraftHeckeBridge FiniteSFactor
namespace OAI.ConcretePrimeRowBridge
theorem _root_.solution
    (S : Finset (Ideal O))
    (hS : (Ideal.span {goodLambda} : Ideal O) ∈ S) :
    ∀ P : Ideal O, P.IsMaximal → goodLambda ∈ P → P ∈ S := by
  intro P hP hmem
  have hle : (Ideal.span {goodLambda} : Ideal O) ≤ P :=
    (Ideal.span_singleton_le_iff_mem P).mpr hmem
  have heq : (Ideal.span {goodLambda} : Ideal O) = P :=
    goodLambdaIdeal_maximal.eq_of_le hP.ne_top hle
  rwa [heq] at hS
end OAI.ConcretePrimeRowBridge
