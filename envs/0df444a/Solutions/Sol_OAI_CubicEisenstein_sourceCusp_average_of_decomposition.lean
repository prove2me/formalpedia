-- Prove2me | solution 1 for OAI.CubicEisenstein.sourceCusp_average_of_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T06:29:07.571081+00:00
-- url     : https://prove2.me/submissions/486ef206-73ac-4463-b61d-4ac28a8e49a0

import Definitions.Def_OAI_NumberTheory_DirichletL_Cusp_ResiduesModThree
import Definitions.Def_OAI_NumberTheory_DirichletL_Reciprocity_PrimaryCongruences
import Theorems.Thm_OAI_CubicEisenstein_period_integral_upper_triangular
import Theorems.Thm_OAI_CubicEisenstein_sourceCuspRepresentative_periodic
import Theorems.Thm_OAI_CubicEisenstein_sourceCuspRepresentative_average
import Theorems.Thm_OAI_CubicEisenstein_cubicSourceResidualFunction_automorphy


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
open scoped BigOperators Classical
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups
open OAI.CubicEisenstein
open ConcreteTraceCRT CubicKubota EisensteinCuspModThree
local notation "O" => ActualEisensteinCubic.O
namespace OAI.CubicEisenstein
theorem _root_.solution (M : SL(2,ActualEisensteinCubic.O)) (G : levelTwo) (j : Fin 3)
    (T : SL(2,ActualEisensteinCubic.O)) (hT : T 1 0=0) (hM : M=(G:SL(2,ActualEisensteinCubic.O))*cuspRepresentative j*T)
    (v : ℝ) (hv : 0<v) :
    (∫z in periodDomain,cubicSourceResidualFunction (integralComplexMatrix M • upperPoint (3*z) v hv))=
      (levelTwoComplexCharacter G*(if j=0 then sourcePrincipalCuspConstant else 0))*(v:ℂ)^(2/3:ℂ) := by
  have he (z : ℂ) : cubicSourceResidualFunction (integralComplexMatrix M • upperPoint (3*z) v hv)=
      levelTwoComplexCharacter G*cubicSourceResidualFunction
        (integralComplexMatrix (cuspRepresentative j) • (integralComplexMatrix T • upperPoint (3*z) v hv)) := by
    rw [hM,map_mul,map_mul,mul_smul,mul_smul,cubicSourceResidualFunction_automorphy]
  simp_rw [he]
  rw [integral_const_mul]
  have hi := period_integral_upper_triangular
    (fun w=>cubicSourceResidualFunction (integralComplexMatrix (cuspRepresentative j) • w))
    v hv (sourceCuspRepresentative_periodic j v hv) T hT
  rw [hi,sourceCuspRepresentative_average]
  ring
end OAI.CubicEisenstein
