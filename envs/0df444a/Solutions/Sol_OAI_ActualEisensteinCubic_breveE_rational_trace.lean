-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.breveE_rational_trace
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:22:14.962977+00:00
-- url     : https://prove2.me/submissions/e5bde1a7-786a-46d7-88fa-adadc1c585fd

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
open EisensteinEmbedding ConcreteTraceCRT ConcreteBreveE
namespace OAI.ActualEisensteinCubic
theorem _root_.solution (m : ℕ) [NeZero m] (a b : ℤ) :
    ShortDraftTrace.breveE
      ((((a : ℂ) + (b : ℂ) * omega3) / eisLam) / m) =
      (ZMod.stdAddChar (N := m)) (b : ZMod m) := by
  have htrace := ShortDraftTrace.trace_div_lam omega3 omega3_sq
    ShortDraftTrace.omega_conj a b
  have hconj : ∀ z : ℂ, star (z / m) = star z / m := by
    intro z
    simp
  change Complex.exp (2 * Real.pi * Complex.I *
    (((((a : ℂ) + (b : ℂ) * omega3) / eisLam) / m) +
      star (((((a : ℂ) + (b : ℂ) * omega3) / eisLam) / m)))) = _
  rw [hconj]
  have hL : ((a : ℂ) + (b : ℂ) * omega3) / eisLam +
      star (((a : ℂ) + (b : ℂ) * omega3) / eisLam) = (b : ℂ) := by
    simpa only [eisLam, Complex.star_def] using htrace
  have harg : 2 * Real.pi * Complex.I *
      (((((a : ℂ) + (b : ℂ) * omega3) / eisLam) / m) +
        (star (((a : ℂ) + (b : ℂ) * omega3) / eisLam)) / m) =
      2 * Real.pi * Complex.I * (b : ℂ) / m := by
    rw [← add_div, hL]
    ring
  rw [harg, ZMod.stdAddChar_coe]
end OAI.ActualEisensteinCubic
