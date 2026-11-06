-- Prove2me | solution 1 for OAI.GaussianShiftedPartition.actual_quadratic_shifted_partition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:46:24.116217+00:00
-- url     : https://prove2.me/submissions/aa7c8e46-2ae9-418e-bea4-f2b42f4f67f3

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_QuadraticNormalization
import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_BinaryGaussian
import Theorems.Thm_OAI_GaussianShiftedPartition_representative_spec
import Theorems.Thm_OAI_ConcreteTraceCRT_finite_quotient_span
import Theorems.Thm_OAI_GaussianAbelPartition_actual_quadratic_gaussian_partition
import Theorems.Thm_OAI_GaussianFiberEquiv_fiber_tsum


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
open OAI.GaussianShiftedPartition
open ActualEisensteinCubic ConcreteTraceCRT ConcreteBreveE
namespace OAI.GaussianShiftedPartition
theorem _root_.solution (c : O) (hc : c ≠ 0)
    (W : O → ℂ)
    (hsum : Summable (fun z : O =>
      (eisTraceModChar ShortDraftTrace.breveE breveE_period_coordinates c hc)
        ((Ideal.Quotient.mk (Ideal.span {c}) z) ^ 2) * W z)) :
    letI : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
    letI : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
    (∑' z : O,
      (eisTraceModChar ShortDraftTrace.breveE breveE_period_coordinates c hc)
        ((Ideal.Quotient.mk (Ideal.span {c}) z) ^ 2) * W z) =
      ∑ r : O ⧸ Ideal.span {c},
        (eisTraceModChar ShortDraftTrace.breveE breveE_period_coordinates c hc)
          (r ^ 2) *
          ∑' w : O, W (representative c r + c*w) := by
  let : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
  let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  rw [GaussianAbelPartition.actual_quadratic_gaussian_partition c hc W hsum]
  apply Finset.sum_congr rfl
  intro r hr
  congr 1
  exact GaussianFiberEquiv.fiber_tsum c hc r
    (representative c r) (representative_spec c r) W
end OAI.GaussianShiftedPartition
