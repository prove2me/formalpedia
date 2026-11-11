-- Prove2me | solution 1 for OAI.CubicEisenstein.kernelQuotientBarrier_laplace_defect
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T13:48:48.647723+00:00
-- url     : https://prove2.me/submissions/fdee010d-d630-4943-850e-5c1048ceea29

import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_UnitRows
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_CuspHeight
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_BarrierPotential
import Theorems.Thm_OAI_CubicEisenstein_cuspBarrierField_laplace_defect
import Theorems.Thm_OAI_CubicEisenstein_cuspBarrier_euclidean_eq
import Theorems.Thm_OAI_CubicEisenstein_cuspBarrierDefect_euclidean_eq
import Theorems.Thm_OAI_CubicEisenstein_axisLaplacian_congr_positive
import Theorems.Thm_OAI_CubicEisenstein_cuspBarrier_euclidean_contDiffAt
import Theorems.Thm_OAI_CubicEisenstein_positiveEuclideanLaplacian_eq_axis


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
open scoped BigOperators Classical Topology ContDiff MatrixGroups
namespace OAI.CubicEisenstein
theorem _root_.solution (a b : ℝ) (ha : 1<a) (hab : a<b)
    (p : EuclideanSpatial) (hp : 0<p 2) :
    positiveEuclideanLaplacian
      (fun q => (kernelQuotientBarrier a b (kernelEuclideanProjection q):ℂ)) p=
        ((kernelQuotientBarrier a b (kernelEuclideanProjection p)+
          kernelQuotientBarrierDefect a b (kernelEuclideanProjection p):ℝ):ℂ) := by
  have hf : ∀q,0<q 2→ContDiffAt ℝ ∞
      (fun q => (kernelQuotientBarrier a b (kernelEuclideanProjection q):ℂ)) q :=
    fun q hq => Complex.ofRealCLM.contDiff.contDiffAt.comp q
      (cuspBarrier_euclidean_contDiffAt a b ha.le hab q hq)
  rw [positiveEuclideanLaplacian_eq_axis _ hf p hp]
  have he : ∀q : SpatialCoordinates,0<q 2→
      (kernelQuotientBarrier a b (kernelEuclideanProjection (WithLp.toLp 2 q)):ℂ)=
        (cuspBarrierField a b q:ℂ) := by
    intro q hq
    exact congrArg Complex.ofReal (cuspBarrier_euclidean_eq a b (WithLp.toLp 2 q) hq)
  rw [axisLaplacian_congr_positive _ _ he p.ofLp hp]
  have hh := cuspBarrierField_laplace_defect a b ha hab p.ofLp hp
  change -axisLaplacian _ p.ofLp=((cuspBarrier a b (euclideanToHyperbolic p)+
    cuspBarrierDefect a b (euclideanToHyperbolic p):ℝ):ℂ)
  rw [cuspBarrier_euclidean_eq a b p hp,cuspBarrierDefect_euclidean_eq a b p hp,Complex.ofReal_add]
  exact sub_eq_iff_eq_add.mp hh |>.trans (add_comm _ _)
end OAI.CubicEisenstein
