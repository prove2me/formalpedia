-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.breveE_quadratic_coordinate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:23:36.279207+00:00
-- url     : https://prove2.me/submissions/6536d69d-764d-4f7b-a964-400260b4a948

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_LatticeCount
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_QuadraticTrace
import Theorems.Thm_OAI_ActualEisensteinCubic_breveE_int_trace_div
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
open OAI.ActualEisensteinCubic
open EisensteinEmbedding ConcreteTraceCRT Complex
namespace OAI.ActualEisensteinCubic
theorem _root_.solution (a b x y : ℤ)
    (hq : a*a - a*b + b*b ≠ 0) :
    let c : ℂ := (a : ℂ) + (b : ℂ) * omega3
    let z : ℂ := (x : ℂ) + (y : ℂ) * omega3
    ShortDraftTrace.breveE (z ^ 2 / (c * eisLam)) =
      Complex.exp (2 * Real.pi * Complex.I *
        ((-b*x*x + 2*a*x*y + (b-a)*y*y : ℤ) : ℂ) /
        ((a*a-a*b+b*b : ℤ) : ℂ)) := by
  let c : ℂ := (a : ℂ) + (b : ℂ) * omega3
  let z : ℂ := (x : ℂ) + (y : ℂ) * omega3
  let cb : ℂ := ((a-b : ℤ) : ℂ) - (b : ℂ) * omega3
  let q : ℤ := a*a-a*b+b*b
  let U : ℤ := (x*x-y*y)*(a-b)+b*(2*x*y-y*y)
  let V : ℤ := -b*x*x+2*a*x*y+(b-a)*y*y
  have hnorm : c * cb = (q : ℂ) := by
    dsimp [c, cb, q]
    push_cast
    linear_combination -(b : ℂ)^2 * omega3_sq
  have hnum : z ^ 2 * cb = (U : ℂ) + (V : ℂ) * omega3 := by
    dsimp [z, cb, U, V]
    push_cast
    linear_combination
      ((y : ℂ)^2 * ((a : ℂ)-(b : ℂ)-(b : ℂ)*omega3) -
        (b : ℂ) * (2*(x : ℂ)*(y : ℂ)-(y : ℂ)^2)) * omega3_sq
  have hqC : (q : ℂ) ≠ 0 := by
    dsimp [q]
    exact_mod_cast hq
  have hc : c ≠ 0 := by
    intro hc
    apply hqC
    rw [← hnorm, hc, zero_mul]
  have hcb : cb ≠ 0 := by
    intro hcb
    apply hqC
    rw [← hnorm, hcb, mul_zero]
  have hdiv : z ^ 2 / (c * eisLam) =
      ((z ^ 2 * cb) / eisLam) / q := by
    rw [← hnorm]
    field_simp [hc, hcb, eisLam_ne_zero]
  change ShortDraftTrace.breveE (z ^ 2 / (c * eisLam)) = _
  rw [hdiv, hnum, breveE_int_trace_div q U V (by simpa [q] using hq)]
end OAI.ActualEisensteinCubic
