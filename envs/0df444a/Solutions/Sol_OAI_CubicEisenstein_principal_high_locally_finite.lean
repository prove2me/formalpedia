-- Prove2me | solution 1 for OAI.CubicEisenstein.principal_high_locally_finite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T11:30:10.323983+00:00
-- url     : https://prove2.me/submissions/50e7ac40-e5a7-42b2-aa5d-ea958c9f0396

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_ReflectedBranches
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_CuspHeight
import Theorems.Thm_OAI_CubicEisenstein_cosetHeight_upperPoint_rowHeight
import Theorems.Thm_OAI_CubicEisenstein_hyperbolicSpatialCoordinates_continuous
import Theorems.Thm_OAI_CubicEisenstein_hyperbolicSpatialCoordinates_reconstruct
import Theorems.Thm_OAI_CubicEisenstein_locally_finite_high_rows


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
open scoped BigOperators Classical Topology MatrixGroups ContDiff
namespace OAI.CubicEisenstein
theorem _root_.solution (w : HyperbolicSpace) :
    ∃U : Set HyperbolicSpace,IsOpen U ∧ w∈U ∧ ∃T : Finset CuspCosets,
      ∀z∈U,∀x∉T,cosetHeight x z<1 := by
  obtain ⟨U,hU,hw,T,hT⟩ := locally_finite_high_rows (hyperbolicSpatialCoordinates w)
    (hyperbolicSpatialCoordinates_positive w)
  refine ⟨hyperbolicSpatialCoordinates ⁻¹' U,hU.preimage hyperbolicSpatialCoordinates_continuous,
    hw,T,?_⟩
  intro z hz x hx
  have hh := (hT _ hz).2 x hx
  rw [←cosetHeight_upperPoint_rowHeight x _ (hyperbolicSpatialCoordinates_positive z),
    hyperbolicSpatialCoordinates_reconstruct] at hh
  exact hh
end OAI.CubicEisenstein
