-- Prove2me | solution 1 for OAI.CubicEisenstein.sourceCuspRemainder_principal_cubic_decay
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T09:52:19.026756+00:00
-- url     : https://prove2.me/submissions/a46f2a9b-773e-40b6-8a97-5d48e7f94822

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_CoverTrace
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_CubeCuspAverage
import Theorems.Thm_OAI_CubicEisenstein_sourceCuspRemainder_one
import Theorems.Thm_OAI_CubicEisenstein_SubexponentialBesselCoefficients_fullFunction_zero_cubic_decay


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
open scoped BigOperators Classical Topology MatrixGroups
open OAI.CubicEisenstein
open ConcreteTraceCRT CubicKubota EisensteinCuspModThree
local notation "O" => ActualEisensteinCubic.O
namespace OAI.CubicEisenstein
theorem _root_.solution (a : ℝ) (ha : 0<a) :
    ∃K : ℝ,0≤K ∧ ∀z : ℂ,∀v : ℝ,∀hv : 0<v,a≤v→
      ‖sourceCuspRemainder (1:SL(2,ActualEisensteinCubic.O)) z v hv‖≤K/v^3 := by
  obtain ⟨K,hK,hbound⟩ := sourceBesselCoefficients.fullFunction_zero_cubic_decay a ha
  refine ⟨K,hK,?_⟩
  intro z v hv hav
  rw [sourceCuspRemainder_one]
  exact hbound v hv z hav
end OAI.CubicEisenstein
