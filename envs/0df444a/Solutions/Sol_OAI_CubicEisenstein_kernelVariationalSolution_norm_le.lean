-- Prove2me | solution 1 for OAI.CubicEisenstein.kernelVariationalSolution_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T22:48:51.970169+00:00
-- url     : https://prove2.me/submissions/cc06de55-31d9-49d2-9e9b-20e0e9a85f96

import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_PaddedPassage
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_VariationalLaplacian
import Theorems.Thm_OAI_CubicEisenstein_kernelEnergyMass_opNorm_le

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
open scoped BigOperators Classical Topology ContDiff
open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff InnerProductSpace
namespace OAI.CubicEisenstein
theorem _root_.solution (F : KernelQuotientL2) :
    ‖kernelVariationalSolution F‖≤‖F‖ := by
  have hnorm : ‖kernelVariationalSolution‖=‖kernelEnergyMass‖ :=
    ContinuousLinearMap.adjoint.norm_map _
  calc
    ‖kernelVariationalSolution F‖≤‖kernelVariationalSolution‖*‖F‖ :=
      kernelVariationalSolution.le_opNorm F
    _ ≤1*‖F‖ := mul_le_mul_of_nonneg_right (hnorm ▸ kernelEnergyMass_opNorm_le) (norm_nonneg F)
    _ = _ := one_mul _
end OAI.CubicEisenstein
