-- Prove2me | solution 1 for OAI.CubicEisenstein.compact_finite_pi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T09:34:36.357805+00:00
-- url     : https://prove2.me/submissions/1d33849a-1638-4657-86c5-2e720aeb447d

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_VariationalLaplacian
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_ReopenedFibers
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_CompactEnergyFamilies

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
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical
open Filter MeasureTheory
open scoped BigOperators Classical Topology
open OAI.CubicEisenstein
namespace OAI.CubicEisenstein
theorem _root_.solution {E G ι : Type*} [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup G] [NormedSpace ℂ G]
    (T : ι→E→L[ℂ]G) (hT : ∀i,IsCompactOperator (T i)) :
    IsCompactOperator (ContinuousLinearMap.pi T) := by
  let K : ι→Set G := fun i => closure ((T i) '' Metric.ball (0 : E) 1)
  have hK : ∀i,IsCompact (K i) := fun i => (hT i).isCompact_closure_image_ball 1
  refine ⟨Set.pi Set.univ K,isCompact_univ_pi hK,?_⟩
  apply Filter.mem_of_superset (Metric.ball_mem_nhds (0 : E) (by norm_num : (0 : ℝ)<1))
  intro x hx
  exact fun i hi => subset_closure ⟨x,hx,rfl⟩
end OAI.CubicEisenstein
