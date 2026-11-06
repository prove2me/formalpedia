-- Prove2me | solution 2 for OAI.ShortDraftTrace.breveE_period_integer
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T23:12:49.227284+00:00
-- url     : https://prove2.me/submissions/15dc2e11-3abb-400f-bcc6-311e9517aa0c

import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LogProfiles
import Definitions.Def_OAI_NumberTheory_DirichletL_ChineseRemainder_AdditiveCharacters
set_option autoImplicit false
open OAI
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open OAI.ShortDraftTrace
open Complex
open scoped ComplexConjugate

theorem solution (a b : ℤ) :
    breveE ((a : ℂ) + (b : ℂ) * ω₃) = 1 := by
  change Complex.exp (2 * Real.pi * Complex.I *
    (((a : ℂ) + (b : ℂ) * ω₃) + conj ((a : ℂ) + (b : ℂ) * ω₃))) = 1
  have hω : conj ω₃ = -ω₃ - 1 := by
    rw [← omega_sq]
    apply Complex.ext <;>
      simp [ω₃, Complex.div_re, Complex.div_im, pow_two] <;>
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
  have hsum : ((a : ℂ) + (b : ℂ) * ω₃) +
      conj ((a : ℂ) + (b : ℂ) * ω₃) = ((2 * a - b : ℤ) : ℂ) := by
    simp only [map_add, map_mul, map_intCast, hω]
    push_cast
    ring
  rw [hsum]
  convert Complex.exp_int_mul_two_pi_mul_I (2 * a - b) using 1 <;> ring
