-- Prove2me | solution 1 for OAI.CubicEisenstein.kernelFunctionCutoff_gradient_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T18:27:01.221537+00:00
-- url     : https://prove2.me/submissions/4adffeaa-7d65-4d41-87f3-2e5f73fcd6d9

import Definitions.Def_OAI_NumberTheory_DirichletL_RowCompletion_ThetaNonvanishing
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_CutoffApproximation
import Theorems.Thm_OAI_CubicEisenstein_l2_tendsto_of_bounded_eventuallyEq
import Theorems.Thm_OAI_CubicEisenstein_kernelFunctionGradient_bound
import Theorems.Thm_OAI_CubicEisenstein_kernelFunctionCutoff_gradient_eventually
import Theorems.Thm_OAI_CubicEisenstein_kernelFunctionCutoff_gradient_bound

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
    (hgL : MemLp (kernelFunctionGradient f) 2 KernelFundamentalVolume)
    (B G : ℝ) (hB : 0≤B) (hG : 0≤G) (hfB : ∀q,‖f q‖≤B)
    (hgrad : ∀p : EuclideanSpatial,0<p 2→∀j : Fin 3,
      ‖(p 2:ℂ)*fderiv ℝ (kernelFunctionField f) p (euclideanCoordinateVector j)‖≤G) :
    Tendsto (fun n => kernelGradientToL2 (kernelFunctionCutoff n f hf)) atTop
      (𝓝 (hgL.toLp (kernelFunctionGradient f))) := by
  obtain ⟨D,hD,hbound⟩ := kernelFunctionCutoff_gradient_bound f hf B G hB hG hfB hgrad
  apply l2_tendsto_of_bounded_eventuallyEq KernelFundamentalVolume
    (fun n w => kernelGradientAt w (kernelFunctionCutoff n f hf)) (kernelFunctionGradient f)
    (fun n => kernelGradientAt_memLp (kernelFunctionCutoff n f hf)) hgL D (3*G) hD (by positivity)
    hbound (kernelFunctionGradient_bound f G hG hgrad)
  exact kernelFunctionCutoff_gradient_eventually f hf
end OAI.CubicEisenstein
