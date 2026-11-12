-- Prove2me | solution 1 for OAI.CubicEisenstein.sourceCusp_scaled_periodic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T09:19:09.456527+00:00
-- url     : https://prove2.me/submissions/e147fd01-cd3a-4bac-a628-ef819c89a48e

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_IntegralCover
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_CoverTrace
import Theorems.Thm_OAI_CubicEisenstein_scaled_cusp_periodic_upper
import Theorems.Thm_OAI_CubicEisenstein_cubicSourceResidualFunction_automorphy
import Theorems.Thm_OAI_CubicEisenstein_sourceCuspRepresentative_periodic
import Theorems.Thm_OAI_EisensteinCuspModThree_three_cusp_decomposition


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
open ConcreteTraceCRT CubicKubota EisensteinCuspModThree
local notation "O" => ActualEisensteinCubic.O
namespace OAI.CubicEisenstein
theorem _root_.solution (M : SL(2,ActualEisensteinCubic.O)) (v : ℝ) (hv : 0<v)
    (n : ActualEisensteinCubic.O) (z : ℂ) :
    cubicSourceResidualFunction (integralComplexMatrix M •
      upperPoint (3*(z+3*eisEmbedding n)) v hv)=
    cubicSourceResidualFunction (integralComplexMatrix M • upperPoint (3*z) v hv) := by
  obtain ⟨G,j,T,hT,_,_,hM⟩ := three_cusp_decomposition M
  have he (w : HyperbolicSpace) : cubicSourceResidualFunction (integralComplexMatrix M • w)=
      levelTwoComplexCharacter G*cubicSourceResidualFunction
        (integralComplexMatrix (cuspRepresentative j) • (integralComplexMatrix T • w)) := by
    rw [hM,map_mul,map_mul,mul_smul,mul_smul,cubicSourceResidualFunction_automorphy]
  calc
    _ = levelTwoComplexCharacter G*cubicSourceResidualFunction
        (integralComplexMatrix (cuspRepresentative j) •
          (integralComplexMatrix T • upperPoint (3*(z+3*eisEmbedding n)) v hv)) := he _
    _ = levelTwoComplexCharacter G*cubicSourceResidualFunction
        (integralComplexMatrix (cuspRepresentative j) •
          (integralComplexMatrix T • upperPoint (3*z) v hv)) :=
      congrArg (fun w : ℂ=>levelTwoComplexCharacter G*w)
        (scaled_cusp_periodic_upper
          (fun w=>cubicSourceResidualFunction (integralComplexMatrix (cuspRepresentative j) • w))
          v hv (sourceCuspRepresentative_periodic j v hv) T hT n z)
    _ = _ := (he _).symm
end OAI.CubicEisenstein
