-- Prove2me | solution 1 for OAI.EisensteinSchwartzPoisson.scaled_eisenstein_cauchy_summable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:15:51.339207+00:00
-- url     : https://prove2.me/submissions/7473c3d7-31b7-4a7c-9581-d300a3927f64

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_ActiveConductor
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_CubicTrace
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_MixedConversion
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_summable_scaled_cauchy_int
import Theorems.Thm_OAI_ActualEisensteinCubic_eisEmbedding_eval_norm_sq
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_inverse_square_le_cauchy_product


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
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open OAI.EisensteinSchwartzPoisson
open ConcreteTraceCRT ActualEisensteinCubic
namespace OAI.EisensteinSchwartzPoisson
theorem _root_.solution (K : ℝ) (hK : 0 < K) :
    Summable (fun h : O => ((1 + K * ‖eisEmbedding h‖ ^ 2) ^ 2)⁻¹) := by
  let b := Real.sqrt K
  have hb : 0 < b := Real.sqrt_pos.mpr hK
  have hbsq : b ^ 2 = K := Real.sq_sqrt hK.le
  have hs := summable_scaled_cauchy_int b hb
  have hp := hs.mul_of_nonneg hs (fun _ => by positivity) (fun _ => by positivity)
  apply (latticeCoordEquiv.symm.summable_iff).mp
  change Summable (fun p : ℤ × ℤ =>
    ((1 + K * ‖eisEmbedding (latticeCoordEquiv.symm p)‖ ^ 2) ^ 2)⁻¹)
  apply Summable.of_nonneg_of_le (fun _ => by positivity) _ (hp.mul_left 4)
  intro p
  apply inverse_square_le_cauchy_product (b * (p.1 : ℝ)) (b * (p.2 : ℝ))
    (K * ‖eisEmbedding (latticeCoordEquiv.symm p)‖ ^ 2) (by positivity)
  change ((b * (p.1 : ℝ)) ^ 2 + (b * (p.2 : ℝ)) ^ 2) / 2 ≤
    K * ‖eisEmbedding (ActualEisensteinCoordinates.eval p.1 p.2)‖ ^ 2
  rw [eisEmbedding_eval_norm_sq]
  push_cast
  nlinarith [mul_nonneg hK.le (sq_nonneg ((p.1 : ℝ) - (p.2 : ℝ)))]
end OAI.EisensteinSchwartzPoisson
