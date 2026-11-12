-- Prove2me | solution 1 for OAI.CubicEisenstein.cubeSource_difference_eq_remainders
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T10:25:22.563921+00:00
-- url     : https://prove2.me/submissions/fea8820d-cd17-48a8-bab9-0000b7d93cc2

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_InverseCorrespondence
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_CorrespondenceTests
import Theorems.Thm_OAI_CubicEisenstein_cubeSource_remainder_summand
import Theorems.Thm_OAI_CubicEisenstein_cubeSource_leading_sum
import Theorems.Thm_OAI_ConcreteTraceCRT_finite_quotient_span


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
theorem _root_.solution (M:SL(2,Eis)) (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (z:ℂ) (v:ℝ) (hv:0<v) :
    cubeAverage p hp.ne_zero cubicSourceResidualFunction (integralComplexMatrix M • upperPoint z v hv)-
      (Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹*cubicSourceResidualFunction (integralComplexMatrix M • upperPoint z v hv)=
    (Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹^3 *
      (∑' r:Eis⧸Ideal.span {p^3},
        let d:=actualCubeCuspData M p (GaussianShiftedPartition.representative (p^3) r) hp hprimary
        cubeReducedRemainder d hp.ne_zero z v hv)-
      (Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹*sourceCuspRemainder M z v hv := by
  let d (r:Eis⧸Ideal.span {p^3}):=actualCubeCuspData M p
    (GaussianShiftedPartition.representative (p^3) r) hp hprimary
  let:Finite (Eis⧸Ideal.span {p^3}):=finite_quotient_span (pow_ne_zero 3 hp.ne_zero)
  have hpoint (r:Eis⧸Ideal.span {p^3}):
      cubicSourceResidualFunction (cubeAverageMatrix p hp.ne_zero
        (GaussianShiftedPartition.representative (p^3) r) • (integralComplexMatrix M • upperPoint z v hv))=
      cubeReducedRemainder (d r) hp.ne_zero z v hv+(v:ℂ)^(2/3:ℂ)*
        (sourceCuspLeadingCoefficient (d r).matrix*cubeCuspHeightWeight p (d r).exponent):=by
    rw [cubeSource_remainder_summand (d r) hp.ne_zero z v hv]
    ring
  have hu:cubeAverage p hp.ne_zero cubicSourceResidualFunction (integralComplexMatrix M • upperPoint z v hv)=
      (Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹^3 *
        (∑' r:Eis⧸Ideal.span {p^3},cubeReducedRemainder (d r) hp.ne_zero z v hv)+
      (Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹*sourceCuspLeadingCoefficient M*(v:ℂ)^(2/3:ℂ):=by
    unfold cubeAverage
    have hs1:Summable (fun r:Eis⧸Ideal.span {p^3}=>cubeReducedRemainder (d r) hp.ne_zero z v hv):=Summable.of_finite
    have hs2:Summable (fun r:Eis⧸Ideal.span {p^3}=>(v:ℂ)^(2/3:ℂ)*
      (sourceCuspLeadingCoefficient (d r).matrix*cubeCuspHeightWeight p (d r).exponent)):=Summable.of_finite
    rw [tsum_congr hpoint,hs1.tsum_add hs2,tsum_mul_left]
    calc
      _=(Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹^3 *
          (∑' r:Eis⧸Ideal.span {p^3},cubeReducedRemainder (d r) hp.ne_zero z v hv)+
        (v:ℂ)^(2/3:ℂ)*((Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹^3 *
          (∑' r:Eis⧸Ideal.span {p^3},sourceCuspLeadingCoefficient (d r).matrix*cubeCuspHeightWeight p (d r).exponent)):=by ring
      _=_:=by rw [cubeSource_leading_sum M p hp hprimary];ring
  rw [hu]
  unfold sourceCuspRemainder
  ring
end OAI.CubicEisenstein
