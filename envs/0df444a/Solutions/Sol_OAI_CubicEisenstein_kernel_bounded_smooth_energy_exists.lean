-- Prove2me | solution 1 for OAI.CubicEisenstein.kernel_bounded_smooth_energy_exists
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T18:35:10.846547+00:00
-- url     : https://prove2.me/submissions/cc8a7ab9-9711-44fb-a3a6-e5ee11636697

import Definitions.Def_OAI_NumberTheory_DirichletL_RowCompletion_ThetaNonvanishing
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_CutoffApproximation
import Theorems.Thm_OAI_CubicEisenstein_kernelFunctionCutoff_mass_tendsto
import Theorems.Thm_OAI_CubicEisenstein_kernelFunctionCutoff_gradient_tendsto

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
open scoped BigOperators Classical Topology ContDiff Manifold
namespace OAI.CubicEisenstein
theorem _root_.solution (f : KernelQuotient→ℂ)
    (hf : ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℂ) ∞ f)
    (hfL : MemLp f 2 (integralQuotientVolume globalKubotaKernel))
    (hgL : MemLp (kernelFunctionGradient f) 2 KernelFundamentalVolume)
    (B G : ℝ) (hB : 0≤B) (hG : 0≤G) (hfB : ∀q,‖f q‖≤B)
    (hgrad : ∀p : EuclideanSpatial,0<p 2→∀j : Fin 3,
      ‖(p 2:ℂ)*fderiv ℝ (kernelFunctionField f) p (euclideanCoordinateVector j)‖≤G) :
    ∃u : KernelEnergyGraph,kernelEnergyMass u=hfL.toLp f ∧
      kernelEnergyGradient u=hgL.toLp (kernelFunctionGradient f) := by
  let x : KernelEnergyAmbient:=WithLp.toLp 2 (hfL.toLp f,hgL.toLp (kernelFunctionGradient f))
  have hm := kernelFunctionCutoff_mass_tendsto f hf hfL B hB hfB
  have hg := kernelFunctionCutoff_gradient_tendsto f hf hgL B G hB hG hfB hgrad
  have hp := hm.prodMk_nhds hg
  have ht : Tendsto (fun n => kernelEnergyCore (kernelFunctionCutoff n f hf)) atTop (𝓝 x) := by
    have h := (WithLp.prodContinuousLinearEquiv 2 ℂ KernelQuotientL2 KernelGradientL2).symm.continuous.continuousAt.tendsto.comp hp
    exact h
  have hx : x∈kernelEnergyGraphSubmodule := by
    change x∈closure (Set.range kernelEnergyCore)
    exact mem_closure_of_tendsto ht (Eventually.of_forall (fun n => ⟨kernelFunctionCutoff n f hf,rfl⟩))
  exact ⟨⟨x,hx⟩,rfl,rfl⟩
end OAI.CubicEisenstein
