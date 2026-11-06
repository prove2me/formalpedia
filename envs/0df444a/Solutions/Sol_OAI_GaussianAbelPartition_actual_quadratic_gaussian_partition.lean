-- Prove2me | solution 1 for OAI.GaussianAbelPartition.actual_quadratic_gaussian_partition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:27:29.973102+00:00
-- url     : https://prove2.me/submissions/bd34de91-da40-4df0-92b2-2ed90e9f80b3

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_QuadraticTrace
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_QuadraticNormalization
import Theorems.Thm_OAI_GaussianAbelPartition_tsum_periodic_weighted_partition
import Theorems.Thm_OAI_ConcreteTraceCRT_finite_quotient_span


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
open OAI.GaussianAbelPartition
open ConcreteTraceCRT ConcreteBreveE ActualEisensteinCubic
namespace OAI.GaussianAbelPartition
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
          ∑' z : ((Ideal.Quotient.mk (Ideal.span {c})) ⁻¹' {r}), W z.1 := by
  let : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
  let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  exact tsum_periodic_weighted_partition
    (Ideal.Quotient.mk (Ideal.span {c}))
    (fun r => (eisTraceModChar ShortDraftTrace.breveE breveE_period_coordinates c hc)
      (r ^ 2)) W hsum
end OAI.GaussianAbelPartition
