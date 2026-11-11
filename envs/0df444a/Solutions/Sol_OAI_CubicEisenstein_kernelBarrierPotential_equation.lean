-- Prove2me | solution 1 for OAI.CubicEisenstein.kernelBarrierPotential_equation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T14:05:05.050945+00:00
-- url     : https://prove2.me/submissions/70e9550d-d67c-4803-a1fc-25a2def31798

import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_UnitRows
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_CuspHeight
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_BarrierPotential
import Theorems.Thm_OAI_CubicEisenstein_kernelQuotientBarrier_laplace_defect
import Theorems.Thm_OAI_CubicEisenstein_kernelQuotientBarrier_one_le


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
open scoped BigOperators Classical Topology ContDiff Manifold
namespace OAI.CubicEisenstein
theorem _root_.solution (a b : ℝ) (ha : 1<a) (hab : a<b)
    (p : EuclideanSpatial) (hp : 0<p 2) :
    positiveEuclideanLaplacian
      (fun q => (kernelQuotientBarrier a b (kernelEuclideanProjection q):ℂ)) p=
        ((kernelBarrierPotential a b (kernelEuclideanProjection p)*
          kernelQuotientBarrier a b (kernelEuclideanProjection p):ℝ):ℂ) := by
  rw [kernelQuotientBarrier_laplace_defect a b ha hab p hp]
  apply congrArg Complex.ofReal
  have hn : kernelQuotientBarrier a b (kernelEuclideanProjection p)≠0 := by
    have hq := kernelQuotientBarrier_one_le a b ha.le hab (kernelEuclideanProjection p)
    linarith
  rw [kernelBarrierPotential,add_mul,one_mul,div_mul_cancel₀ _ hn]
end OAI.CubicEisenstein
