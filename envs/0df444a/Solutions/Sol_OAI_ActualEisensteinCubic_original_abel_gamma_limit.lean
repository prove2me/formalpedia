-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.original_abel_gamma_limit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:25:37.64935+00:00
-- url     : https://prove2.me/submissions/c836f99c-d5f1-44e9-acbe-84ee8df337d4

import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_GaussianMoments
import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_OscillatoryGaussian
import Theorems.Thm_OAI_ActualEisensteinCoordinates_eval_coords
import Theorems.Thm_OAI_ActualEisensteinCubic_eisEmbedding_eval_norm_sq
import Theorems.Thm_OAI_ActualEisensteinCubic_original_abel_gauss_limit
import Theorems.Thm_OAI_ConcreteTraceCRT_finite_quotient_span
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
open ActualEisensteinCubic
open OAI.ActualEisensteinCubic
open scoped Topology
open Filter EisensteinEmbedding ConcreteTraceCRT Complex
namespace OAI.ActualEisensteinCubic
theorem _root_.solution (c : O) (hc : c ≠ 0) :
    letI : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
    letI : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
    Tendsto (fun η : ℝ => (η : ℂ) *
      (∑' z : O,
        (eisTraceModChar ShortDraftTrace.breveE
          ConcreteBreveE.breveE_period_coordinates c hc)
          (Ideal.Quotient.mk (Ideal.span {c}) z ^ 2) *
        Complex.exp (-(Real.pi : ℂ) * (η : ℂ) *
          (‖eisEmbedding z‖ ^ 2 : ℂ))))
      (𝓝[>] (0 : ℝ))
      (𝓝 ((((2 / (Real.sqrt 3 * ‖eisEmbedding c‖) : ℝ) : ℂ) *
        quadraticGammaO c hc))) := by
  let : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
  let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  let a := (ActualEisensteinCoordinates.coords c).1
  let b := (ActualEisensteinCoordinates.coords c).2
  let ψ := eisTraceModChar ShortDraftTrace.breveE
    ConcreteBreveE.breveE_period_coordinates c hc
  let S : ℂ := ∑ r : O ⧸ Ideal.span {c}, ψ (r ^ 2)
  have hceq : c = ActualEisensteinCoordinates.eval a b :=
    (ActualEisensteinCoordinates.eval_coords c).symm
  have hq : (((a*a-a*b+b*b : ℤ) : ℝ)) = ‖eisEmbedding c‖ ^ 2 := by
    calc
      (((a*a-a*b+b*b : ℤ) : ℝ)) =
          ‖eisEmbedding (ActualEisensteinCoordinates.eval a b)‖ ^ 2 :=
        (eisEmbedding_eval_norm_sq a b).symm
      _ = ‖eisEmbedding c‖ ^ 2 := by rw [← hceq]
  have hn : ‖eisEmbedding c‖ ≠ 0 :=
    ne_of_gt (norm_pos_iff.mpr (ConcreteTraceCRT.eisEmbedding_ne_zero hc))
  have hnC : (‖eisEmbedding c‖ : ℂ) ≠ 0 := by exact_mod_cast hn
  have hsqrtC : (Real.sqrt 3 : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0:ℝ) < 3)))
  have hgamma : quadraticGammaO c hc = S / (‖eisEmbedding c‖ : ℂ) := rfl
  have h := original_abel_gauss_limit c hc
  convert h using 1
  rw [hgamma, hq]
  push_cast
  field_simp [hnC, hsqrtC]
  dsimp only [S]
end OAI.ActualEisensteinCubic
