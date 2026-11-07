-- Prove2me | solution 1 for OAI.EisensteinSchwartzPoisson.scaled_eisenstein_cauchy_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:18:03.246497+00:00
-- url     : https://prove2.me/submissions/2468e6de-1aa1-482d-b108-ada98f72ff0b

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_ActiveConductor
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_CubicTrace
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_MixedConversion
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_summable_scaled_cauchy_int
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_scaled_cauchy_int_bound
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_scaled_eisenstein_cauchy_summable
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
    (∑' h : O, ((1 + K * ‖eisEmbedding h‖ ^ 2) ^ 2)⁻¹) ≤
      4 * (1 + Real.pi / Real.sqrt K) ^ 2 := by
  let b := Real.sqrt K
  have hb : 0 < b := Real.sqrt_pos.mpr hK
  have hbsq : b ^ 2 = K := Real.sq_sqrt hK.le
  have hs := summable_scaled_cauchy_int b hb
  have hp := hs.mul_of_nonneg hs (fun _ => by positivity) (fun _ => by positivity)
  have he : (∑' h : O, ((1 + K * ‖eisEmbedding h‖ ^ 2) ^ 2)⁻¹) =
      ∑' p : ℤ × ℤ, ((1 + K * ‖eisEmbedding (latticeCoordEquiv.symm p)‖ ^ 2) ^ 2)⁻¹ :=
    (latticeCoordEquiv.symm.tsum_eq _).symm
  rw [he]
  calc
    _ ≤ ∑' p : ℤ × ℤ, 4 * ((1 + (b * (p.1 : ℝ)) ^ 2)⁻¹ *
          (1 + (b * (p.2 : ℝ)) ^ 2)⁻¹) := by
      apply ((latticeCoordEquiv.symm.summable_iff).mpr
        (scaled_eisenstein_cauchy_summable K hK)).tsum_le_tsum _ (hp.mul_left 4)
      intro p
      apply inverse_square_le_cauchy_product _ _ _ (by positivity)
      change ((b * (p.1 : ℝ)) ^ 2 + (b * (p.2 : ℝ)) ^ 2) / 2 ≤
        K * ‖eisEmbedding (ActualEisensteinCoordinates.eval p.1 p.2)‖ ^ 2
      rw [eisEmbedding_eval_norm_sq]
      push_cast
      nlinarith [mul_nonneg hK.le (sq_nonneg ((p.1 : ℝ) - (p.2 : ℝ)))]
    _ = 4 * (∑' n : ℤ, (1 + (b * (n : ℝ)) ^ 2)⁻¹) ^ 2 := by
      rw [tsum_mul_left, ← hs.tsum_mul_tsum hs hp, pow_two]
    _ ≤ 4 * (1 + Real.pi / b) ^ 2 := by
      gcongr
      exact scaled_cauchy_int_bound b hb
end OAI.EisensteinSchwartzPoisson
