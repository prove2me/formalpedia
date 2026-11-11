-- Prove2me | solution 1 for OAI.CubicEisenstein.kernelRegularPencil_center_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T15:11:52.224072+00:00
-- url     : https://prove2.me/submissions/22a418e5-7e86-47d9-8262-76b94002c3f8

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_FredholmAlternative
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_MeromorphicResolvent
import Theorems.Thm_OAI_CubicEisenstein_kernelRegularPencil_apply
import Theorems.Thm_OAI_CubicEisenstein_ker_orthogonal_restriction_injective
import Theorems.Thm_OAI_CubicEisenstein_kernelSpectralFormOperator_selfAdjoint
import Theorems.Thm_OAI_CubicEisenstein_kernel_theta_spectral_fredholm
import Theorems.Thm_OAI_CubicEisenstein_selfAdjoint_range_eq_ker_orthogonal


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
open scoped Topology
open Filter MeasureTheory
open scoped BigOperators Classical Topology InnerProductSpace
namespace OAI.CubicEisenstein
theorem _root_.solution : IsUnit (kernelRegularPencil (8/9:ℂ)) := by
  apply (ContinuousLinearMap.isUnit_iff_bijective (𝕜 := ℂ) (E := kernelThetaRegular)).mpr
  constructor
  · intro u v huv
    apply ker_orthogonal_restriction_injective (kernelSpectralFormOperator (8/9:ℂ))
    exact congrArg (fun w : kernelThetaRegular => (w:KernelEnergyGraph)) huv
  · intro v
    have he : (kernelSpectralFormOperator (8/9:ℂ)).range=kernelThetaRegular := by
      exact selfAdjoint_range_eq_ker_orthogonal _
        (by convert kernelSpectralFormOperator_selfAdjoint (8/9) using 1 ; norm_num)
        kernel_theta_spectral_fredholm.isClosed_range
    have hv : (v:KernelEnergyGraph)∈(kernelSpectralFormOperator (8/9:ℂ)).range := by
      rw [he]
      exact v.2
    obtain ⟨u,hu⟩ := hv
    change kernelSpectralFormOperator (8/9:ℂ) u=(v:KernelEnergyGraph) at hu
    let w : kernelThetaRegular := ⟨u-kernelThetaNull.starProjection u,kernelThetaNull.sub_starProjection_mem_orthogonal u⟩
    refine ⟨w,Subtype.ext ?_⟩
    rw [kernelRegularPencil_apply]
    change kernelSpectralFormOperator (8/9:ℂ) (u-kernelThetaNull.starProjection u)=v
    rw [map_sub,hu]
    have hz : kernelSpectralFormOperator (8/9:ℂ) (kernelThetaNull.starProjection u)=0 :=
      kernelThetaNull.starProjection_apply_mem u
    rw [hz,sub_zero]
end OAI.CubicEisenstein
