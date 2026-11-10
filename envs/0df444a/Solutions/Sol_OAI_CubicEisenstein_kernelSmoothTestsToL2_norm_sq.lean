-- Prove2me | solution 1 for OAI.CubicEisenstein.kernelSmoothTestsToL2_norm_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T19:24:26.399346+00:00
-- url     : https://prove2.me/submissions/07d75a0a-fbfa-472b-90a1-03329bd8602b

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_BranchScaling
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_LocalCutoffs

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
open OAI.CubicEisenstein
open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff ENNReal
namespace OAI.CubicEisenstein
theorem _root_.solution (f : kernelSmoothTests) :
    ‖kernelSmoothTestsToL2 f‖^2=
      ∫q,‖f.1 q‖^2∂integralQuotientVolume globalKubotaKernel := by
  calc
    ‖kernelSmoothTestsToL2 f‖^2=inner ℝ (kernelSmoothTestsToL2 f) (kernelSmoothTestsToL2 f) :=
      (real_inner_self_eq_norm_sq _).symm
    _ = ∫q,inner ℝ (kernelSmoothTestsToL2 f q) (kernelSmoothTestsToL2 f q)
        ∂integralQuotientVolume globalKubotaKernel := rfl
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [(kernelSmoothTests_memLp f).coeFn_toLp] with q hq
      change inner ℝ (((kernelSmoothTests_memLp f).toLp f.1) q)
        (((kernelSmoothTests_memLp f).toLp f.1) q)=_
      rw [hq,real_inner_self_eq_norm_sq]
end OAI.CubicEisenstein
