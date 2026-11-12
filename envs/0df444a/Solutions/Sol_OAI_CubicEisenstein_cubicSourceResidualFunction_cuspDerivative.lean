-- Prove2me | solution 1 for OAI.CubicEisenstein.cubicSourceResidualFunction_cuspDerivative
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T06:35:42.079043+00:00
-- url     : https://prove2.me/submissions/c212a5c7-5890-4f4b-9ee0-d3444207106c

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_SourceBesselExpansion
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_InverseCuspCoordinates
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_ReflectedCuspMellin
import Theorems.Thm_OAI_CubicEisenstein_cubicSourceResidualFunction_translate_split_differentiableAt
import Theorems.Thm_OAI_CubicEisenstein_cuspDerivative_of_transform
import Theorems.Thm_OAI_CubicEisenstein_cubicSourceResidualFunction_levelThree

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
open scoped BigOperators Classical Topology MatrixGroups
open Finset AddChar MulChar EisensteinEmbedding
namespace OAI.CubicEisenstein
theorem _root_.solution (G : CubicKubota.levelThree)
    (g H : SL(2,ℂ)) (hfactor : g=complexMatrix G*H) (hc : g 1 0≠0)
    (v : ℝ) (hv : 0<v) :
    horizontalWirtingerBar (fun z=>cubicSourceResidualFunction (upperPoint z v hv)) (g 0 0/g 1 0)=
      (CubicKubota.complexCharacter G*(-1/((g 1 0)^2*(v:ℂ)^2)))*
        horizontalWirtingerZ
          (fun z=>cubicSourceResidualFunction (H•upperPoint z (1/(‖g 1 0‖^2*v)) (by positivity)))
          (-g 1 1/g 1 0) := by
  refine cuspDerivative_of_transform cubicSourceResidualFunction g H
    (CubicKubota.complexCharacter G) ?_ hc v hv ?_
  · intro w
    rw [hfactor,mul_smul,cubicSourceResidualFunction_levelThree]
  · exact cubicSourceResidualFunction_translate_split_differentiableAt H _ (by positivity)
end OAI.CubicEisenstein
