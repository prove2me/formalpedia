-- Prove2me | solution 1 for OAI.CubicEisenstein.kernel_compact_coercivity_extend
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T13:35:34.634061+00:00
-- url     : https://prove2.me/submissions/d4892a0f-cc3a-4d63-a498-4f8709db6bda

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_BarrierPotential
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_CutoffOrders
import Theorems.Thm_OAI_CubicEisenstein_kernelEnergyGraphCore_dense
import Theorems.Thm_OAI_CubicEisenstein_kernelGradientToL2_norm_sq
import Theorems.Thm_OAI_CubicEisenstein_quadraticHeightDenominator_continuous
attribute [local fun_prop] OAI.CubicEisenstein.quadraticHeightDenominator_continuous



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
open OAI.CubicEisenstein
open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff
namespace OAI.CubicEisenstein
theorem _root_.solution
    (K : Set KernelQuotient) (hK : MeasurableSet K) (C : ℝ)
    (hcore : ∀f : kernelSmoothTests,‖kernelSmoothTestsToL2 f‖^2≤kernelDirichletEnergy f+
      C*‖kernelMassRestrictionCLM K hK (kernelSmoothTestsToL2 f)‖^2)
    (u : KernelEnergyGraph) :
    ‖kernelEnergyMass u‖^2≤‖kernelEnergyGradient u‖^2+C*‖kernelEnergyMassRestriction K hK u‖^2 := by
  exact kernelEnergyGraphCore_dense.induction_on u
    (isClosed_le (by fun_prop) (by fun_prop)) (fun f => by
      change ‖kernelSmoothTestsToL2 f‖^2≤‖kernelGradientToL2 f‖^2+
        C*‖kernelMassRestrictionCLM K hK (kernelSmoothTestsToL2 f)‖^2
      rw [kernelGradientToL2_norm_sq]
      exact hcore f)
end OAI.CubicEisenstein
