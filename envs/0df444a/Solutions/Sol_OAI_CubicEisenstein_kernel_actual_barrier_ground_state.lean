-- Prove2me | solution 1 for OAI.CubicEisenstein.kernel_actual_barrier_ground_state
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T14:16:16.283966+00:00
-- url     : https://prove2.me/submissions/3218868a-f2f3-4893-9b12-b73f4bb0b788

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_BarrierPotential
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_CutoffOrders
import Theorems.Thm_OAI_CubicEisenstein_kernel_ground_state_inequality
import Theorems.Thm_OAI_CubicEisenstein_kernelBarrierPotential_continuous
import Theorems.Thm_OAI_CubicEisenstein_kernelBarrierPotential_equation
import Theorems.Thm_OAI_CubicEisenstein_kernelQuotientBarrier_contMDiff
import Theorems.Thm_OAI_CubicEisenstein_kernelQuotientBarrier_one_le


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
open scoped BigOperators Classical Topology ContDiff Manifold
open OAI.CubicEisenstein
open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff Manifold
namespace OAI.CubicEisenstein
theorem _root_.solution (f : kernelSmoothTests) :
    (∫q,kernelBarrierPotential 2 3 q*‖f.1 q‖^2∂integralQuotientVolume globalKubotaKernel)≤
      kernelDirichletEnergy f :=
  kernel_ground_state_inequality (kernelQuotientBarrier 2 3) (kernelBarrierPotential 2 3)
    (kernelQuotientBarrier_contMDiff 2 3 (by norm_num) (by norm_num))
    (fun q => lt_of_lt_of_le zero_lt_one (kernelQuotientBarrier_one_le 2 3 (by norm_num) (by norm_num) q))
    (kernelBarrierPotential_continuous 2 3 (by norm_num) (by norm_num))
    (kernelBarrierPotential_equation 2 3 (by norm_num) (by norm_num)) f
end OAI.CubicEisenstein
