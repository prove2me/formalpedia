-- Prove2me | solution 1 for OAI.QuadraticMainOperatorBound.ideal_quadraticRow_norm_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T00:24:11.818489+00:00
-- url     : https://prove2.me/submissions/d03f9e13-5a8f-4cd6-9917-be4b84c36a33

import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_UniformKernelBounds
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_FiniteOperator
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_CrossFactorization
import Theorems.Thm_OAI_ActualEisensteinCubic_finiteSquarefreeRow_norm_le_one


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
open scoped BigOperators Classical
open OAI.QuadraticMainOperatorBound
open IdealMobiusDivisorSum QuadraticMainBoundary IdealCoprimeSieveOperator FiniteSieveOperator
open ConcretePrimeRowBridge ActualEisensteinCubic
namespace OAI.QuadraticMainOperatorBound
theorem _root_.solution (F : Finset (Ideal O))
    (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (hFgood : ∀ I ∈ F, ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, goodLambda ∉ P)
    (J : Ideal O) (z : O) : ‖(idealSexticRow F hFpos hFgood J z) ^ 3‖ ≤ 1 := by
  let : ∀ i : primePool F, (i.val).IsMaximal := primePool_maximal F hFpos
  rw [norm_pow]
  apply pow_le_one₀ (norm_nonneg _)
  exact finiteSquarefreeRow_norm_le_one (fun i : primePool F => i.val)
    (primePool_good F hFgood) (idealSupport F J) z
end OAI.QuadraticMainOperatorBound
