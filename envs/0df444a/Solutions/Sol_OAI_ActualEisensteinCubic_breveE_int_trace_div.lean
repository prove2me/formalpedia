-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.breveE_int_trace_div
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:22:26.671033+00:00
-- url     : https://prove2.me/submissions/1a2d3f9b-354b-4bbf-be13-d9a5333ebcf0

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_LatticeCount
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_QuadraticTrace
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
theorem _root_.solution (q u v : ℤ) (_hq : q ≠ 0) :
    ShortDraftTrace.breveE
      ((((u : ℂ) + (v : ℂ) * omega3) / eisLam) / q) =
      Complex.exp (2 * Real.pi * Complex.I * (v : ℂ) / q) := by
  have htrace := ShortDraftTrace.trace_div_lam omega3 omega3_sq
    ShortDraftTrace.omega_conj u v
  have hL : ((u : ℂ) + (v : ℂ) * omega3) / eisLam +
      star (((u : ℂ) + (v : ℂ) * omega3) / eisLam) = (v : ℂ) := by
    simpa only [eisLam, Complex.star_def] using htrace
  change Complex.exp (2 * Real.pi * Complex.I *
    (((((u : ℂ) + (v : ℂ) * omega3) / eisLam) / q) +
      star (((((u : ℂ) + (v : ℂ) * omega3) / eisLam) / q)))) = _
  rw [show star (((u : ℂ) + (v : ℂ) * omega3) / eisLam / q) =
      star (((u : ℂ) + (v : ℂ) * omega3) / eisLam) / q by simp]
  rw [← add_div, hL]
  congr 1
  ring
end OAI.ActualEisensteinCubic
