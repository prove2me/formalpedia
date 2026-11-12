-- Prove2me | solution 1 for OAI.CubicEisenstein.sourceCusp_average_complex_upper
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T09:36:01.189017+00:00
-- url     : https://prove2.me/submissions/1133ba19-9420-448c-b942-7705a5443be5

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_CoverTrace
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_CubeCuspAverage
import Theorems.Thm_OAI_CubicEisenstein_sourceCusp_average_enlarged_affine
import Theorems.Thm_OAI_CubicEisenstein_complex_upper_triangular_action


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
open OAI.CubicEisenstein
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups
open ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O
namespace OAI.CubicEisenstein
theorem _root_.solution (M : SL(2,ActualEisensteinCubic.O)) (T : SL(2,ℂ))
    (hT : T 1 0=0) (b d : ActualEisensteinCubic.O) (hd : d≠0)
    (hscale : (T 0 0/T 1 1)*eisEmbedding b=eisEmbedding d)
    (v : ℝ) (hv : 0<v) :
    (∫z in periodDomain,cubicSourceResidualFunction
      (integralComplexMatrix M • (T • upperPoint (3*(eisEmbedding b*z)) v hv)))=
      sourceCuspConstant M*((v/‖T 1 1‖^2:ℝ):ℂ)^(2/3:ℂ) := by
  have hcoord (z : ℂ) : (T 0 0*(3*(eisEmbedding b*z))+T 0 1)/T 1 1=
      3*(eisEmbedding d*z+(T 0 1/T 1 1)/3) := by
    rw [add_div]
    rw [show T 0 0*(3*(eisEmbedding b*z))/T 1 1=
      3*((T 0 0/T 1 1)*eisEmbedding b)*z by ring,hscale]
    ring
  simp_rw [complex_upper_triangular_action T hT,hcoord]
  exact sourceCusp_average_enlarged_affine M d hd _ _ _
end OAI.CubicEisenstein
