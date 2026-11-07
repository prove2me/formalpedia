-- Prove2me | solution 1 for OAI.CompletedGauss.cubeWeight_span
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:18:26.894481+00:00
-- url     : https://prove2.me/submissions/e1a7af63-7a9e-444b-adc8-56567c5c8dde

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_CrossSeparation
import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_IdealMobius
import Theorems.Thm_OAI_CompletedGauss_primaryGenerator_span
import Theorems.Thm_OAI_ActualEisensteinCubic_qNat_eq_absNorm_span


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
open scoped BigOperators Classical
open OAI.CompletedGauss
open ActualEisensteinCubic ConcreteTraceCRT
namespace OAI.CompletedGauss
theorem _root_.solution (Ψ : O →* ℂ) (n : O) (hn : n ≠ 0)
    (hp : lambda ^ 2 ∣ n - 1) :
    cubeWeight Ψ (Ideal.span {n}) =
      star (FiniteGaussPhase.angularFactor n) ^ 3 * Ψ n ^ 3 /
        (ShortDraftLatticeCount.qNat n : ℂ) := by
  change star (FiniteGaussPhase.angularFactor (primaryGenerator (Ideal.span {n}))) ^ 3 *
    Ψ (primaryGenerator (Ideal.span {n})) ^ 3 / (Ideal.absNorm (Ideal.span {n}) : ℂ) = _
  rw [primaryGenerator_span n hn hp, qNat_eq_absNorm_span]
end OAI.CompletedGauss
