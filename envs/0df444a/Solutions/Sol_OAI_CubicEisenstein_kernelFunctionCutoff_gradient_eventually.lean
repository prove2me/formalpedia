-- Prove2me | solution 1 for OAI.CubicEisenstein.kernelFunctionCutoff_gradient_eventually
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T18:19:56.051495+00:00
-- url     : https://prove2.me/submissions/acafe256-f4bb-48da-8b3d-8300c9a73e19

import Definitions.Def_OAI_NumberTheory_DirichletL_RowCompletion_ThetaNonvanishing
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_CutoffApproximation
import Theorems.Thm_OAI_CubicEisenstein_kernelFunctionCutoff_field_eventually
import Theorems.Thm_OAI_CubicEisenstein_euclideanCoordinateVector_eq_basis
import Theorems.Thm_OAI_CubicEisenstein_hyperbolicHeight_pos


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
    (hf : ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℂ) ∞ f) (w : HyperbolicSpace) :
    ∀ᶠn : ℕ in atTop,kernelGradientAt w (kernelFunctionCutoff n f hf)=kernelFunctionGradient f w := by
  filter_upwards [kernelFunctionCutoff_field_eventually f hf
    (hyperbolicEuclideanCoordinates w) (hyperbolicHeight_pos w)] with n hn
  apply (WithLp.equiv 2 (Fin 3→ℂ)).injective
  funext j
  change (hyperbolicHeight w:ℂ)*fderiv ℝ (kernelTestField (kernelFunctionCutoff n f hf)) _ _=
    (hyperbolicHeight w:ℂ)*fderiv ℝ (kernelFunctionField f) _ _
  rw [hn.fderiv_eq,euclideanCoordinateVector_eq_basis]
end OAI.CubicEisenstein
