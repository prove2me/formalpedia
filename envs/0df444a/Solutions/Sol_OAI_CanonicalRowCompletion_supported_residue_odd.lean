-- Prove2me | solution 1 for OAI.CanonicalRowCompletion.supported_residue_odd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T16:18:12.713033+00:00
-- url     : https://prove2.me/submissions/3485ccfc-c911-450c-8bbf-f0b5f21e1e9a

import Definitions.Def_OAI_NumberTheory_DirichletL_RowCompletion_ThetaNonvanishing
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_CuspResidues
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_ConjugateLevelAction
import Theorems.Thm_OAI_ActualEisensteinCoordinates_odd_residue_iff_not_two_dvd
import Theorems.Thm_OAI_CanonicalQuadraticSieve_supported_span_iff


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
open scoped BigOperators
open scoped BigOperators Classical
open OAI.CanonicalRowCompletion
open ActualEisensteinCubic
open CompletedGauss hiding O
open CanonicalQuadraticSieve hiding O
open CubicJacobiGlobal hiding O
open QuadraticGaussRay hiding O
open QuadraticAllOddCRT
open ActualEisensteinCoordinates hiding O omega
open UniqueFactorizationMonoid
namespace OAI.CanonicalRowCompletion
theorem _root_.solution (p : ActualEisensteinCubic.O) (hs : Supported (Ideal.span {p})) : EisensteinEPrimaryPhase.odd (residue p) :=
  (ActualEisensteinCoordinates.odd_residue_iff_not_two_dvd p).mpr ((supported_span_iff p).mp hs).2
end OAI.CanonicalRowCompletion
