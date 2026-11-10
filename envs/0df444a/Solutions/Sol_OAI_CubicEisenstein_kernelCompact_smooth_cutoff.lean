-- Prove2me | solution 1 for OAI.CubicEisenstein.kernelCompact_smooth_cutoff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T11:34:15.489587+00:00
-- url     : https://prove2.me/submissions/0b57a8e3-1eb4-4763-9dc4-4d285099c6e2

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_ReflectedBranches
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_CuspHeight

set_option autoImplicit false
open OAI
noncomputable section
open OAI.CubicEisenstein
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
open scoped BigOperators Classical Topology ContDiff Manifold
namespace OAI.CubicEisenstein
theorem _root_.solution (K : Set KernelQuotient) (hK : IsCompact K) :
    ∃χ : KernelQuotient→ℝ,ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℝ) ∞ χ ∧
      HasCompactSupport χ ∧ (∀q∈K,χ=ᶠ[𝓝 q](fun _ => 1)) ∧ ∀q,χ q∈Set.Icc 0 1 := by
  obtain ⟨J,hJ,hKJ⟩ := exists_compact_superset hK
  obtain ⟨χ,hχone,hχzero,hχrange⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
    𝓘(ℝ,SpatialCoordinates) hK.isClosed hKJ (n := (⊤ : ℕ∞))
  refine ⟨χ,χ.contMDiff,?_,?_,hχrange⟩
  · apply HasCompactSupport.of_support_subset_isCompact hJ
    intro q hq
    by_contra hn
    exact hq (hχzero q hn)
  · intro q hq
    exact hχone.filter_mono (nhds_le_nhdsSet hq)
end OAI.CubicEisenstein
