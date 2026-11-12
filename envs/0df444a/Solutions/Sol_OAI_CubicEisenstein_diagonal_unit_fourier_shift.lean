-- Prove2me | solution 1 for OAI.CubicEisenstein.diagonal_unit_fourier_shift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T09:33:32.144372+00:00
-- url     : https://prove2.me/submissions/a4ab71e7-23c6-40ac-a164-acfe200f0884

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_CubeCuspAverage
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_InverseCorrespondence
import Theorems.Thm_OAI_CubicEisenstein_period_integral_twisted_translation
import Theorems.Thm_OAI_CubicEisenstein_diagonal_unit_weighted_periodic

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
open scoped BigOperators Classical
open OAI.CubicEisenstein
open Filter MeasureTheory
open scoped BigOperators Classical MatrixGroups
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicRamified
local notation "Eis" => ActualEisensteinCubic.O
namespace OAI.CubicEisenstein
theorem _root_.solution (u t:Eisˣ) (j:ℕ) (h:Eis)
    (hr:(↑u⁻¹:Eis)^2*(t:Eis)=omega^j ∨ (↑u⁻¹:Eis)^2*(t:Eis)=-(omega^j))
    (hbase:(3:Eis)∣h+ramifiedAffineParameter j 0*(t:Eis))
    (v:ℝ) (hv:0<v) (s b:ℂ) :
    (∫z in periodDomain,eisenstein (integralComplexMatrix (unitCuspDiagonal u)*
      integralComplexMatrix (lowerCuspMatrix (t:Eis))*upperSection (z+b) v hv) s*
        ShortDraftTrace.breveE (-ninthCuspFrequency h*z))=
      ShortDraftTrace.breveE (ninthCuspFrequency h*b)*
        ∫z in periodDomain,eisenstein (integralComplexMatrix (unitCuspDiagonal u)*
          integralComplexMatrix (lowerCuspMatrix (t:Eis))*upperSection z v hv) s*
            ShortDraftTrace.breveE (-ninthCuspFrequency h*z) :=
  period_integral_twisted_translation
    (fun z=>eisenstein (integralComplexMatrix (unitCuspDiagonal u)*integralComplexMatrix (lowerCuspMatrix (t:Eis))*upperSection z v hv) s)
    (ninthCuspFrequency h) (diagonal_unit_weighted_periodic u t j h hr hbase v hv s) b
end OAI.CubicEisenstein
