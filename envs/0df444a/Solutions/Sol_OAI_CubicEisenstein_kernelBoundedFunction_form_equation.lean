-- Prove2me | solution 1 for OAI.CubicEisenstein.kernelBoundedFunction_form_equation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T18:34:18.928061+00:00
-- url     : https://prove2.me/submissions/9362f034-a838-4df7-af29-f541626b9022

import Definitions.Def_OAI_NumberTheory_DirichletL_RowCompletion_ThetaNonvanishing
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_CutoffApproximation
import Theorems.Thm_OAI_CubicEisenstein_kernelFunctionCutoff_gradient_tendsto
import Theorems.Thm_OAI_CubicEisenstein_kernelFunctionCutoff_uniform_near
import Theorems.Thm_OAI_CubicEisenstein_kernelDirichletForm_supported_equation
import Theorems.Thm_OAI_CubicEisenstein_kernelGradientToL2_inner
import Theorems.Thm_OAI_CubicEisenstein_positiveEuclideanLaplacian_congr


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
open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff Manifold
namespace OAI.CubicEisenstein
theorem _root_.solution (f : KernelQuotient→ℂ)
    (hf : ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℂ) ∞ f)
    (hgL : MemLp (kernelFunctionGradient f) 2 KernelFundamentalVolume)
    (B G : ℝ) (hB : 0≤B) (hG : 0≤G) (hfB : ∀q,‖f q‖≤B)
    (hgrad : ∀p : EuclideanSpatial,0<p 2→∀j : Fin 3,
      ‖(p 2:ℂ)*fderiv ℝ (kernelFunctionField f) p (euclideanCoordinateVector j)‖≤G)
    (A : KernelQuotient→ℂ) (hA : MemLp A 2 (integralQuotientVolume globalKubotaKernel))
    (hEq : ∀p : EuclideanSpatial,0<p 2→
      positiveEuclideanLaplacian (kernelFunctionField f) p=A (kernelEuclideanProjection p))
    (g : kernelSmoothTests) :
    inner ℂ (hgL.toLp (kernelFunctionGradient f)) (kernelGradientToL2 g)=
      inner ℂ (hA.toLp A) (kernelSmoothTestsToL2 g) := by
  obtain ⟨N,hN⟩ := kernelFunctionCutoff_uniform_near f hf (tsupport g.1) g.2.2
  have hconstant : ∀ᶠn : ℕ in atTop,
      inner ℂ (kernelGradientToL2 (kernelFunctionCutoff n f hf)) (kernelGradientToL2 g)=
        inner ℂ (hA.toLp A) (kernelSmoothTestsToL2 g) := by
    filter_upwards [eventually_ge_atTop N] with n hn
    rw [kernelGradientToL2_inner,kernelL2_inner_toLp_smooth]
    apply kernelDirichletForm_supported_equation (kernelFunctionCutoff n f hf) g A hA
    intro p hp hpg
    change positiveEuclideanLaplacian (kernelTestField (kernelFunctionCutoff n f hf)) p=A (kernelEuclideanProjection p)
    rw [positiveEuclideanLaplacian_congr _ _ p (hN n hn p hp hpg)]
    exact hEq p hp
  have hlim : Tendsto (fun n => inner ℂ (kernelGradientToL2 (kernelFunctionCutoff n f hf))
      (kernelGradientToL2 g)) atTop (𝓝 (inner ℂ (hgL.toLp (kernelFunctionGradient f)) (kernelGradientToL2 g))) :=
    (kernelFunctionCutoff_gradient_tendsto f hf hgL B G hB hG hfB hgrad).inner
      (tendsto_const_nhds (x := kernelGradientToL2 g))
  exact tendsto_nhds_unique hlim (tendsto_const_nhds.congr' (hconstant.mono (fun n hn => hn.symm)))
end OAI.CubicEisenstein
