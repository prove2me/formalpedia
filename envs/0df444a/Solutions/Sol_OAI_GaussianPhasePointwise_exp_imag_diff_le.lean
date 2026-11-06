-- Prove2me | solution 1 for OAI.GaussianPhasePointwise.exp_imag_diff_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:48:10.375208+00:00
-- url     : https://prove2.me/submissions/670f513a-b074-4594-9b29-63b32f9e0c00

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_GaussianDualLimit
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_GaussianFiberMass
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
open OAI.GaussianPhasePointwise
namespace OAI.GaussianPhasePointwise
theorem _root_.solution (u v : ℝ) :
    ‖Complex.exp (Complex.I * (u : ℂ)) -
      Complex.exp (Complex.I * (v : ℂ))‖ ≤ |u - v| := by
  have heq :
      Complex.exp (Complex.I * (u : ℂ)) -
        Complex.exp (Complex.I * (v : ℂ)) =
      (Complex.exp (Complex.I * ((u - v : ℝ) : ℂ)) - 1) *
        Complex.exp (Complex.I * (v : ℂ)) := by
    rw [sub_mul, one_mul, ← Complex.exp_add]
    congr 1
    push_cast
    ring_nf
  rw [heq, norm_mul, Complex.norm_exp_I_mul_ofReal, mul_one]
  simpa only [Real.norm_eq_abs] using
    (Real.norm_exp_I_mul_ofReal_sub_one_le (x := u - v))
end OAI.GaussianPhasePointwise
