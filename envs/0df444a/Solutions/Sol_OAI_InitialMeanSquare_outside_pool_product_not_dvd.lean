-- Prove2me | solution 1 for OAI.InitialMeanSquare.outside_pool_product_not_dvd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T12:05:04.131104+00:00
-- url     : https://prove2.me/submissions/a28bf9d7-8b80-47b3-b192-0d28e105f6ee

import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_InputEnergy
import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_OutsideIdeals

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
open scoped BigOperators Classical SchwartzMap ContDiff
open OAI.InitialMeanSquare
open ActualEisensteinCubic ConcretePrimeRowBridge CanonicalQuadraticSieve
open FirstPassCubeLabels (primeProductNorm normalizedColumn columnLog)
namespace OAI.InitialMeanSquare
theorem _root_.solution (S : Finset (Ideal O)) (D : ℕ)
    (hSp : ∀ P ∈ S, Prime P) (T : Finset (primePool (outsideSquarefreeIdeals S D))) :
    ∀ P ∈ S, ¬ P ∣ ∏ i ∈ T,i.val := by
  intro P hPS hdiv
  obtain ⟨i,hi,hPi⟩ := ((hSp P hPS).dvd_finsetProd_iff
    (fun i : primePool (outsideSquarefreeIdeals S D) => i.val)).mp hdiv
  obtain ⟨I,hIF,hiI⟩ := mem_primePool_iff.mp i.property
  have ho : I ∈ outsideIdealsUpTo S D := (Finset.mem_filter.mp hIF).1
  have hn := outsideIdealsUpTo_ne_bot S D I ho
  have hd : i.val ∣ I := (UniqueFactorizationMonoid.mem_normalizedFactors_iff hn).mp hiI |>.2
  exact (mem_outsideIdealsUpTo.mp ho).2.2 P hPS (hPi.trans hd)
end OAI.InitialMeanSquare
