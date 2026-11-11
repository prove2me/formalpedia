-- Prove2me | solution 1 for OAI.CubicEisenstein.kernelEisensteinRemainder_operator_equation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T19:06:47.109209+00:00
-- url     : https://prove2.me/submissions/615fa8b8-f888-4a1c-b6ad-a2da59d5a36f

import Definitions.Def_OAI_NumberTheory_DirichletL_RowCompletion_ThetaNonvanishing
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_CutoffApproximation
import Theorems.Thm_OAI_CubicEisenstein_eisensteinRemainder_coordinate_equation
import Theorems.Thm_OAI_CubicEisenstein_kernelQuotientDefect_euclidean_eq
import Theorems.Thm_OAI_CubicEisenstein_axisLaplacian_congr_positive
import Theorems.Thm_OAI_CubicEisenstein_kernelEisensteinRemainder_euclidean_eq
import Theorems.Thm_OAI_CubicEisenstein_kernelEisensteinRemainder_euclidean_smooth
import Theorems.Thm_OAI_CubicEisenstein_positiveEuclideanLaplacian_eq_axis


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
open scoped BigOperators Classical Topology ContDiff Manifold Matrix
namespace OAI.CubicEisenstein
theorem _root_.solution (a b : ℝ) (ha : 1<a) (hab : a<b)
    (s : ℂ) (hs : 2<s.re) (p : EuclideanSpatial) (hp : 0<p 2) :
    positiveEuclideanLaplacian (kernelFunctionField (kernelEisensteinRemainder a b s hs)) p=
      kernelQuotientDefect a b s (kernelEuclideanProjection p)+
        kernelEisensteinSpectralParameter s*kernelEisensteinRemainder a b s hs (kernelEuclideanProjection p) := by
  let f := kernelFunctionField (kernelEisensteinRemainder a b s hs)
  have hf : ∀q,0<q 2→ContDiffAt ℝ ∞ f q := kernelEisensteinRemainder_euclidean_smooth a b ha hab s hs
  have he : ∀q : SpatialCoordinates,0<q 2→f (WithLp.toLp 2 q)=eisensteinRemainderField a b s q := by
    intro q hq
    exact kernelEisensteinRemainder_euclidean_eq a b s hs (WithLp.toLp 2 q) hq
  rw [positiveEuclideanLaplacian_eq_axis f hf p hp,
    axisLaplacian_congr_positive _ _ he p.ofLp hp,
    eisensteinRemainder_coordinate_equation a b ha hab s hs p.ofLp hp,
    kernelQuotientDefect_euclidean_eq a b s p hp,kernelEisensteinRemainder_euclidean_eq a b s hs p hp]
  rfl
end OAI.CubicEisenstein
