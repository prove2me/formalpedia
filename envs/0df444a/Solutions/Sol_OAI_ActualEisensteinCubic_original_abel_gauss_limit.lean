-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.original_abel_gauss_limit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:55:33.54773+00:00
-- url     : https://prove2.me/submissions/41ab49f8-2693-4a03-8b69-947fde79c9c4

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_GaussianDualLimit
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_GaussianFiberMass
import Theorems.Thm_OAI_ActualEisensteinCubic_actual_oscillatory_kernel_summable
import Theorems.Thm_OAI_ActualEisensteinCubic_actual_O_fiber_gaussian_mass
import Theorems.Thm_OAI_ConcreteTraceCRT_finite_quotient_span
import Theorems.Thm_OAI_GaussianShiftedPartition_actual_quadratic_shifted_partition
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
attribute [local simp] OAI.IdealGaussCRT.traceProdChar_mk



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
open OAI.ActualEisensteinCubic
open scoped Topology
open Filter EisensteinEmbedding ConcreteTraceCRT Complex
namespace OAI.ActualEisensteinCubic
theorem _root_.solution (c : O) (hc : c ≠ 0) :
    letI : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
    letI : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
    let a := (ActualEisensteinCoordinates.coords c).1
    let b := (ActualEisensteinCoordinates.coords c).2
    let K : ℂ := ((2 / (Real.sqrt 3 *
      (((a*a-a*b+b*b : ℤ) : ℝ))) : ℝ) : ℂ)
    Tendsto (fun η : ℝ => (η : ℂ) *
      (∑' z : O,
        (eisTraceModChar ShortDraftTrace.breveE
          ConcreteBreveE.breveE_period_coordinates c hc)
          (Ideal.Quotient.mk (Ideal.span {c}) z ^ 2) *
        Complex.exp (-(Real.pi : ℂ) * (η : ℂ) *
          (‖eisEmbedding z‖ ^ 2 : ℂ))))
      (𝓝[>] (0 : ℝ))
      (𝓝 (K * ∑ r : O ⧸ Ideal.span {c},
        (eisTraceModChar ShortDraftTrace.breveE
          ConcreteBreveE.breveE_period_coordinates c hc) (r ^ 2))) := by
  let : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
  let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  let a := (ActualEisensteinCoordinates.coords c).1
  let b := (ActualEisensteinCoordinates.coords c).2
  let K : ℂ := ((2 / (Real.sqrt 3 *
    (((a*a-a*b+b*b : ℤ) : ℝ))) : ℝ) : ℂ)
  let ψ := eisTraceModChar ShortDraftTrace.breveE
    ConcreteBreveE.breveE_period_coordinates c hc
  let W (η : ℝ) (z : O) := Complex.exp (-(Real.pi : ℂ) * (η : ℂ) *
    (‖eisEmbedding z‖ ^ 2 : ℂ))
  have hfiber (r : O ⧸ Ideal.span {c}) :
      Tendsto (fun η : ℝ => (η : ℂ) *
        (∑' w : O, W η (GaussianShiftedPartition.representative c r + c*w)))
        (𝓝[>] (0 : ℝ)) (𝓝 K) := by
    simpa only [K, a, b, W] using
      actual_O_fiber_gaussian_mass c
        (GaussianShiftedPartition.representative c r) hc
  have hsum : Tendsto (fun η : ℝ =>
      ∑ r : O ⧸ Ideal.span {c}, ψ (r ^ 2) *
        ((η : ℂ) * (∑' w : O, W η
          (GaussianShiftedPartition.representative c r + c*w))))
      (𝓝[>] (0 : ℝ))
      (𝓝 (∑ r : O ⧸ Ideal.span {c}, ψ (r ^ 2) * K)) := by
    apply tendsto_finsetSum Finset.univ
    intro r hr
    exact (hfiber r).const_mul (ψ (r ^ 2))
  have hpoint (η : ℝ) (hη : 0 < η) :
      (η : ℂ) * (∑' z : O, ψ
        (Ideal.Quotient.mk (Ideal.span {c}) z ^ 2) * W η z) =
      ∑ r : O ⧸ Ideal.span {c}, ψ (r ^ 2) *
        ((η : ℂ) * (∑' w : O, W η
          (GaussianShiftedPartition.representative c r + c*w))) := by
    have hpart := GaussianShiftedPartition.actual_quadratic_shifted_partition
      c hc (W η) (actual_oscillatory_kernel_summable c hc hη)
    change (∑' z : O, ψ (Ideal.Quotient.mk (Ideal.span {c}) z ^ 2) * W η z) =
      ∑ r : O ⧸ Ideal.span {c}, ψ (r ^ 2) *
        ∑' w : O, W η (GaussianShiftedPartition.representative c r + c*w) at hpart
    rw [hpart, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    ring
  have heq : (fun η : ℝ => (η : ℂ) *
      (∑' z : O, ψ (Ideal.Quotient.mk (Ideal.span {c}) z ^ 2) * W η z)) =ᶠ[
        𝓝[>] (0 : ℝ)]
      (fun η : ℝ => ∑ r : O ⧸ Ideal.span {c}, ψ (r ^ 2) *
        ((η : ℂ) * (∑' w : O, W η
          (GaussianShiftedPartition.representative c r + c*w)))) := by
    filter_upwards [self_mem_nhdsWithin] with η hη
    exact hpoint η hη
  have hlim := hsum.congr' heq.symm
  simpa only [K, ψ, W, Finset.mul_sum, mul_comm] using hlim
end OAI.ActualEisensteinCubic
