-- Prove2me | solution 1 for OAI.CubicEisenstein.cubeSource_primary_upper_average
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T09:53:58.718749+00:00
-- url     : https://prove2.me/submissions/6dc85c45-bd6c-426f-bb49-753cfe9a115c

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_InverseCorrespondence
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_CorrespondenceTests
import Theorems.Thm_OAI_CubicEisenstein_cubeSource_summand_average
import Theorems.Thm_OAI_CubicEisenstein_cubeAverage_cusp_integral
import Theorems.Thm_OAI_CubicEisenstein_cubicSourceResidualFunction_continuous
import Theorems.Thm_OAI_CubicKubota_CubeCuspData_right_upper_character
import Theorems.Thm_OAI_CubicKubota_CubeCuspData_right_upper_exponent
import Theorems.Thm_OAI_CubicKubota_actualCubeCuspPhaseSum_normalized


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
open MeasureTheory
open scoped Classical MatrixGroups BigOperators
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicKubota EisensteinCuspModThree
local notation "Eis" => ActualEisensteinCubic.O
namespace OAI.CubicEisenstein
theorem _root_.solution (A:levelTwo) (T:SL(2,Eis)) (hT:T 1 0=0)
    (p:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1)
    (hA:lambda^2∣((A:SL(2,Eis)) 0 0)-1) (v:ℝ) (hv:0<v) :
    (∫z in periodDomain,cubeAverage p hp.ne_zero cubicSourceResidualFunction
      (integralComplexMatrix ((A:SL(2,Eis))*T) • upperPoint (3*(eisEmbedding (p^3)*z)) v hv))=
      (Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹*sourceCuspConstant ((A:SL(2,Eis))*T)*(v:ℂ)^(2/3:ℂ) := by
  let d (r:Eis⧸Ideal.span {p^3}):=actualCubeCuspData (A:SL(2,Eis)) p
    (GaussianShiftedPartition.representative (p^3) r) hp hprimary
  rw [cubeAverage_cusp_integral p hp.ne_zero cubicSourceResidualFunction
    cubicSourceResidualFunction_continuous ((A:SL(2,Eis))*T) (p^3) v hv]
  have hpoint (r:Eis⧸Ideal.span {p^3}):
      (∫z in periodDomain,cubicSourceResidualFunction
        (cubeAverageMatrix p hp.ne_zero (GaussianShiftedPartition.representative (p^3) r) •
          (integralComplexMatrix ((A:SL(2,Eis))*T) • upperPoint (3*(eisEmbedding (p^3)*z)) v hv)))=
      complexCharacter ⟨(d r).matrix*(A:SL(2,Eis))⁻¹,(d r).congruent⟩*
        sourceCuspConstant ((A:SL(2,Eis))*T)*(v:ℂ)^(2/3:ℂ)*cubeCuspHeightWeight p (d r).exponent:=by
    rw [cubeSource_summand_average ((d r).right_upper T hT) hp.ne_zero v hv,
      CubeCuspData.right_upper_character,CubeCuspData.right_upper_exponent]
  simp_rw [hpoint]
  have hsum:(∑' r:Eis⧸Ideal.span {p^3},
      complexCharacter ⟨(d r).matrix*(A:SL(2,Eis))⁻¹,(d r).congruent⟩*
        sourceCuspConstant ((A:SL(2,Eis))*T)*(v:ℂ)^(2/3:ℂ)*cubeCuspHeightWeight p (d r).exponent)=
      (sourceCuspConstant ((A:SL(2,Eis))*T)*(v:ℂ)^(2/3:ℂ))*
        actualCubeCuspPhaseSum A p hp hprimary (cubeCuspHeightWeight p):=by
    unfold actualCubeCuspPhaseSum
    rw [←tsum_mul_left]
    apply tsum_congr
    intro r
    change _=(sourceCuspConstant ((A:SL(2,Eis))*T)*(v:ℂ)^(2/3:ℂ))*
      (cubeCuspHeightWeight p (d r).exponent*complexCharacter
        ⟨(d r).matrix*(A:SL(2,Eis))⁻¹,(d r).congruent⟩)
    ring
  rw [hsum]
  calc
    _=((Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹^3*
      actualCubeCuspPhaseSum A p hp hprimary (cubeCuspHeightWeight p))*
        (sourceCuspConstant ((A:SL(2,Eis))*T)*(v:ℂ)^(2/3:ℂ)):=by ring
    _=_:=by rw [actualCubeCuspPhaseSum_normalized A p hp hprimary hA];ring
end OAI.CubicEisenstein
