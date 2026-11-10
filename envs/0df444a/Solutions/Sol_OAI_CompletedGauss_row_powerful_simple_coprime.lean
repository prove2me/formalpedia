-- Prove2me | solution 1 for OAI.CompletedGauss.row_powerful_simple_coprime
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T08:57:32.485722+00:00
-- url     : https://prove2.me/submissions/2f42f101-28d2-4a89-8ddf-6f0f5a144ba6

import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_SquarefreeTransfer
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_CubeBlocks
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_PowerfulParts
import Theorems.Thm_OAI_CompletedGauss_rowPowerfulPart_ne_zero
import Theorems.Thm_OAI_CompletedGauss_rowSimplePart_ne_zero
import Theorems.Thm_OAI_CompletedGauss_normalizedFactors_rowPowerfulPart
import Theorems.Thm_OAI_CompletedGauss_normalizedFactors_rowSimplePart

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
open OAI.CompletedGauss
open ActualEisensteinCubic CanonicalQuadraticSieve QuadraticSquarefreeKernel UniqueFactorizationMonoid
namespace OAI.CompletedGauss
theorem _root_.solution (I : Ideal O) :
    IsCoprime (rowPowerfulPart I) (rowSimplePart I) := by
  apply ideals_coprime_of_relprime
  apply (isRelPrime_iff_no_prime_factors (rowPowerfulPart_ne_zero I)).mpr
  intro P hp hs hP
  have hp' := (UniqueFactorizationMonoid.mem_normalizedFactors_iff (rowPowerfulPart_ne_zero I)).mpr ⟨hP,hp⟩
  have hs' := (UniqueFactorizationMonoid.mem_normalizedFactors_iff (rowSimplePart_ne_zero I)).mpr ⟨hP,hs⟩
  rw [normalizedFactors_rowPowerfulPart] at hp'
  rw [normalizedFactors_rowSimplePart] at hs'
  exact (Multiset.mem_filter.mp hs').2 (Multiset.mem_filter.mp hp').2
end OAI.CompletedGauss
