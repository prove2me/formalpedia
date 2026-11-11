-- Prove2me | solution 1 for OAI.CubicEisenstein.kernel_bounded_smooth_operator_graph
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T18:59:45.101215+00:00
-- url     : https://prove2.me/submissions/e1cb5697-be56-42e9-affb-d05e0f95a582

import Definitions.Def_OAI_NumberTheory_DirichletL_RowCompletion_ThetaNonvanishing
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_CutoffApproximation
import Theorems.Thm_OAI_CubicEisenstein_kernelFunctionGradient_memLp
import Theorems.Thm_OAI_CubicEisenstein_kernel_bounded_smooth_energy_exists
import Theorems.Thm_OAI_CubicEisenstein_kernelBoundedFunction_form_equation
import Theorems.Thm_OAI_CubicEisenstein_kernelEnergyGradient_core
import Theorems.Thm_OAI_CubicEisenstein_kernelEnergyGraphCore_dense
import Theorems.Thm_OAI_CubicEisenstein_kernelEnergyMass_core
import Theorems.Thm_OAI_CubicEisenstein_kernelVariationalSolution_unique
import Theorems.Thm_OAI_CubicEisenstein_quadraticHeightDenominator_continuous
attribute [local fun_prop] OAI.CubicEisenstein.quadraticHeightDenominator_continuous



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
    (hfL : MemLp f 2 (integralQuotientVolume globalKubotaKernel))
    (B G : ℝ) (hB : 0≤B) (hG : 0≤G) (hfB : ∀q,‖f q‖≤B)
    (hgrad : ∀p : EuclideanSpatial,0<p 2→∀j : Fin 3,
      ‖(p 2:ℂ)*fderiv ℝ (kernelFunctionField f) p (euclideanCoordinateVector j)‖≤G)
    (A : KernelQuotient→ℂ) (hA : MemLp A 2 (integralQuotientVolume globalKubotaKernel))
    (hEq : ∀p : EuclideanSpatial,0<p 2→
      positiveEuclideanLaplacian (kernelFunctionField f) p=A (kernelEuclideanProjection p)) :
    (hfL.toLp f,hA.toLp A)∈kernelEnergyLaplacian.graph := by
  have hgL := kernelFunctionGradient_memLp f hf G hG hgrad
  obtain ⟨u,hum,hug⟩ := kernel_bounded_smooth_energy_exists f hf hfL hgL B G hB hG hfB hgrad
  have hform (v : KernelEnergyGraph) :
      inner ℂ (kernelEnergyGradient u) (kernelEnergyGradient v)=inner ℂ (hA.toLp A) (kernelEnergyMass v) := by
    exact kernelEnergyGraphCore_dense.induction_on v
      (isClosed_eq (by fun_prop : Continuous (fun v : KernelEnergyGraph =>
        inner ℂ (kernelEnergyGradient u) (kernelEnergyGradient v)))
        (by fun_prop : Continuous (fun v : KernelEnergyGraph => inner ℂ (hA.toLp A) (kernelEnergyMass v))))
      (fun g => by
        rw [hug,kernelEnergyGradient_core,kernelEnergyMass_core]
        exact kernelBoundedFunction_form_equation f hf hgL B G hB hG hfB hgrad A hA hEq g)
  have hu : u=kernelVariationalSolution (hfL.toLp f+hA.toLp A) := by
    apply kernelVariationalSolution_unique
    intro v
    rw [hum,hform v,inner_add_left]
  have hm := congrArg kernelEnergyMass hu
  rw [hum] at hm
  rw [kernelEnergyLaplacian_graph,mem_kernelLaplacianGraph]
  exact hm.symm
end OAI.CubicEisenstein
