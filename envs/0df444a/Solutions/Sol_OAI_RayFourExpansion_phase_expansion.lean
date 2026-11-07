-- Prove2me | solution 1 for OAI.RayFourExpansion.phase_expansion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:24:29.27214+00:00
-- url     : https://prove2.me/submissions/aa2fd7db-2b49-4863-b744-9a3f7beadea7

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_IdealMobius
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_CompletedExpansion
import Theorems.Thm_OAI_FiniteRayExpansion_zeroExtendUnits_fourier
import Theorems.Thm_OAI_FiniteRayExpansion_zeroExtendUnits_restrict

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
open OAI.RayFourExpansion
open ActualEisensteinCubic ConcreteTraceCRT ActualEisensteinCoordinates QuadraticGaussRay
open FiniteRayExpansion
namespace OAI.RayFourExpansion
theorem _root_.solution (f : RayRing → ℂ) (a : O) :
    rayMask a * f (Ideal.Quotient.mk (Ideal.span {(4 : O)}) a) =
      ∑ χ : RayCharacter, phaseCoeff f χ * rayCharacter χ a := by
  rw [rayMask, ← zeroExtendUnits_restrict]
  exact zeroExtendUnits_fourier _ _
end OAI.RayFourExpansion
