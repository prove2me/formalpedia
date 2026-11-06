-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.breveE_quarter_trace
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:17:16.5752+00:00
-- url     : https://prove2.me/submissions/6decfb9e-a1c5-4b13-90ef-70c3fc5e3c75

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_LocalProductAssembly
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_RamifiedTracePhase
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
import Theorems.Thm_OAI_ShortDraftTrace_omega_conj
import Theorems.Thm_OAI_ShortDraftTrace_trace_div_lam
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
open OAI.ActualEisensteinCubic
open EisensteinEmbedding ConcreteTraceCRT Complex
namespace OAI.ActualEisensteinCubic
theorem _root_.solution (a b : ℤ) :
    ShortDraftTrace.breveE
      ((((a : ℂ) + (b : ℂ) * omega3) / eisLam) / 4) =
      Complex.I ^ b := by
  have htrace := ShortDraftTrace.trace_div_lam omega3 omega3_sq
    ShortDraftTrace.omega_conj a b
  have hconj : ∀ z : ℂ, star (z / 4) = star z / 4 := by
    intro z
    simp
  change Complex.exp (2 * Real.pi * Complex.I *
    (((((a : ℂ) + (b : ℂ) * omega3) / eisLam) / 4) +
      star (((((a : ℂ) + (b : ℂ) * omega3) / eisLam) / 4)))) = _
  rw [hconj]
  have hL : ((a : ℂ) + (b : ℂ) * omega3) / eisLam +
      star (((a : ℂ) + (b : ℂ) * omega3) / eisLam) = (b : ℂ) := by
    simpa only [eisLam, Complex.star_def] using htrace
  have harg : 2 * Real.pi * Complex.I *
      (((((a : ℂ) + (b : ℂ) * omega3) / eisLam) / 4) +
        (star (((a : ℂ) + (b : ℂ) * omega3) / eisLam)) / 4) =
      (b : ℂ) * (Real.pi / 2 * Complex.I) := by
    rw [← add_div, hL]
    ring
  rw [harg, Complex.exp_int_mul, Complex.exp_pi_div_two_mul_I]
end OAI.ActualEisensteinCubic
