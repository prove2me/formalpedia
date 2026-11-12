-- Prove2me | solution 1 for OAI.CubicEisenstein.cubeSource_remainder_summand
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T09:33:23.163069+00:00
-- url     : https://prove2.me/submissions/45c086ec-5190-4e79-bbff-9081f4bc9d49

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_InverseCorrespondence
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_CorrespondenceTests
import Theorems.Thm_OAI_CubicEisenstein_complex_upper_triangular_action
import Theorems.Thm_OAI_CubicEisenstein_cubeCuspTriangular_entries
import Theorems.Thm_OAI_CubicEisenstein_cubeCuspTriangular_factor
import Theorems.Thm_OAI_CubicEisenstein_cubeCuspTriangular_height


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
theorem _root_.solution {M:SL(2,Eis)} {p q:Eis}
    (d:CubeCuspData M p q) (hp:p≠0) (z:ℂ) (v:ℝ) (hv:0<v) :
    cubicSourceResidualFunction (cubeAverageMatrix p hp q • (integralComplexMatrix M • upperPoint z v hv))=
      cubeReducedRemainder d hp z v hv+
        sourceCuspLeadingCoefficient d.matrix*(v:ℂ)^(2/3:ℂ)*cubeCuspHeightWeight p d.exponent := by
  rw [←mul_smul,cubeCuspTriangular_factor d hp,mul_smul,
    complex_upper_triangular_action (cubeCuspTriangular d hp) (cubeCuspTriangular_entries d hp).2.1]
  unfold cubeReducedRemainder sourceCuspRemainder
  rw [cubeCuspTriangular_height d hp v hv]
  ring
end OAI.CubicEisenstein
