-- Prove2me | solution 1 for OAI.CubicEisenstein.kernelSourceEnergyPullback_mass
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T06:24:47.144371+00:00
-- url     : https://prove2.me/submissions/250d9729-002f-42b3-89f6-44ed3f7a0b57

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_AffineCuspFourier
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_IntegralCover
import Theorems.Thm_OAI_CubicEisenstein_kernelSourceEnergyPullback_core
import Theorems.Thm_OAI_CubicEisenstein_kernelEnergyGraphCore_dense
import Theorems.Thm_OAI_CubicEisenstein_kernelEnergyMass_core


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
open scoped BigOperators Classical Topology MatrixGroups Manifold ContDiff
open Finset AddChar MulChar EisensteinEmbedding
namespace OAI.CubicEisenstein
theorem _root_.solution (M : CubicKubota.levelTwo) (u : KernelEnergyGraph) :
    kernelEnergyMass (kernelSourceEnergyPullback M u)=kernelSourcePullback M (kernelEnergyMass u) := by
  apply congrFun (kernelEnergyGraphCore_dense.equalizer
    (kernelEnergyMass.continuous.comp (kernelSourceEnergyPullback M).continuous)
    ((kernelSourcePullback M).continuous.comp kernelEnergyMass.continuous) ?_) u
  funext f
  change kernelEnergyMass (kernelSourceEnergyPullback M (kernelEnergyGraphCore f))=
    kernelSourcePullback M (kernelEnergyMass (kernelEnergyGraphCore f))
  rw [kernelSourceEnergyPullback_core,kernelEnergyMass_core,kernelEnergyMass_core,kernelSourceTest_mass]
end OAI.CubicEisenstein
