-- Prove2me | solution 1 for OAI.CubicEisenstein.kernelFunctionCutoff_gradient_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T18:19:57.446429+00:00
-- url     : https://prove2.me/submissions/ee05c36f-5088-4dad-a39a-0fda6ce997af

import Definitions.Def_OAI_NumberTheory_DirichletL_RowCompletion_ThetaNonvanishing
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_CutoffApproximation
import Theorems.Thm_OAI_CubicEisenstein_norm_three_vector_bound
import Theorems.Thm_OAI_CubicEisenstein_kernelFunctionCutoff_scaled_deriv_bound
import Theorems.Thm_OAI_CubicEisenstein_euclideanCoordinateVector_eq_basis
import Theorems.Thm_OAI_CubicEisenstein_hyperbolicHeight_pos
import Theorems.Thm_OAI_CubicEisenstein_kernelExhaustionCutoff_scaled_fderiv_bound


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
    (B G : ℝ) (hB : 0≤B) (hG : 0≤G) (hfB : ∀q,‖f q‖≤B)
    (hgrad : ∀p : EuclideanSpatial,0<p 2→∀j : Fin 3,
      ‖(p 2:ℂ)*fderiv ℝ (kernelFunctionField f) p (euclideanCoordinateVector j)‖≤G) :
    ∃D : ℝ,0≤D ∧ ∀n : ℕ,∀w : HyperbolicSpace,‖kernelGradientAt w (kernelFunctionCutoff n f hf)‖≤D := by
  obtain ⟨D,hD,hcut⟩ := kernelExhaustionCutoff_scaled_fderiv_bound
  refine ⟨3*(G+B*D),by positivity,?_⟩
  intro n w
  apply norm_three_vector_bound _ (G+B*D) (by positivity)
  intro j
  change ‖(hyperbolicHeight w:ℂ)*fderiv ℝ (kernelTestField (kernelFunctionCutoff n f hf))
    (hyperbolicEuclideanCoordinates w) (EuclideanSpace.basisFun (Fin 3) ℝ j)‖≤_
  rw [←euclideanCoordinateVector_eq_basis]
  exact kernelFunctionCutoff_scaled_deriv_bound f hf B G D hB hfB hgrad hcut n
    (hyperbolicEuclideanCoordinates w) (hyperbolicHeight_pos w) j
end OAI.CubicEisenstein
