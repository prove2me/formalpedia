-- Prove2me | solution 1 for OAI.CubicEisenstein.kernelEisensteinL2Correction_graph_eventually
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T00:55:04.965073+00:00
-- url     : https://prove2.me/submissions/bf229d89-dc05-4417-92bc-0bc8167faae2

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_FredholmAlternative
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_MeromorphicResolvent
import Theorems.Thm_OAI_CubicEisenstein_kernelEisensteinPencil_eventually_isUnit
import Theorems.Thm_OAI_CubicEisenstein_kernelEisensteinL2Correction_graph

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
open scoped Topology
open scoped Topology
open Filter MeasureTheory
open scoped BigOperators Classical Topology InnerProductSpace
namespace OAI.CubicEisenstein
theorem _root_.solution (a b : ℝ) (ha : 0<a) (hab : a<b) :
    ∀ᶠ s : ℂ in 𝓝[≠] (4/3:ℂ),
    (kernelEisensteinL2Correction a b ha hab s,
      kernelL2Defect a b ha hab s + kernelEisensteinSpectralParameter s •
        kernelEisensteinL2Correction a b ha hab s)∈kernelEnergyLaplacian.graph := by
  filter_upwards [kernelEisensteinPencil_eventually_isUnit] with s hs
  exact kernelEisensteinL2Correction_graph a b ha hab s hs
end OAI.CubicEisenstein
