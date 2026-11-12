-- Prove2me | solution 1 for OAI.CubicEisenstein.kernelSource_variationalSolution
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T07:54:57.870909+00:00
-- url     : https://prove2.me/submissions/a3dcc13d-aa78-4d58-ba99-b3d5e7a2ae37

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_AffineCuspFourier
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_IntegralCover
import Theorems.Thm_OAI_CubicEisenstein_kernelSourceEnergyPullback_mass
import Theorems.Thm_OAI_CubicEisenstein_kernelSourceEnergyPullback_surjective
import Theorems.Thm_OAI_CubicEisenstein_kernelEnergyGraph_inner
import Theorems.Thm_OAI_CubicEisenstein_kernelVariationalSolution_equation
import Theorems.Thm_OAI_CubicEisenstein_kernelVariationalSolution_unique


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
open scoped BigOperators Classical Topology MatrixGroups InnerProductSpace
open Finset AddChar MulChar EisensteinEmbedding
namespace OAI.CubicEisenstein
theorem _root_.solution (M : CubicKubota.levelTwo) (F : KernelQuotientL2) :
    kernelSourceEnergyPullback M (kernelVariationalSolution F)=
      kernelVariationalSolution (kernelSourcePullback M F) := by
  apply kernelVariationalSolution_unique
  intro v
  obtain ⟨w,rfl⟩ := kernelSourceEnergyPullback_surjective M v
  rw [←kernelEnergyGraph_inner,LinearIsometry.inner_map_map,
    kernelSourceEnergyPullback_mass,LinearIsometry.inner_map_map,kernelEnergyGraph_inner]
  exact kernelVariationalSolution_equation F w
end OAI.CubicEisenstein
