-- Prove2me | solution 1 for OAI.ShortDraftTrace.breveE_period_integer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:05:23.019432+00:00
-- url     : https://prove2.me/submissions/7d8c7387-96e8-4104-9c06-76bfa9665adb

import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LogProfiles
import Definitions.Def_OAI_NumberTheory_DirichletL_ChineseRemainder_AdditiveCharacters
import Theorems.Thm_OAI_ShortDraftTrace_omega_conj

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
namespace OAI.ShortDraftTrace
theorem _root_.solution (a b : ℤ) :
    breveE ((a : ℂ) + (b : ℂ) * ω₃) = 1 := by
  have htrace : ((a : ℂ) + (b : ℂ) * ω₃) +
      conj ((a : ℂ) + (b : ℂ) * ω₃) = ((2 * a - b : ℤ) : ℂ) := by
    rw [map_add, map_intCast, map_mul, map_intCast, omega_conj, omega_sq]
    push_cast
    ring
  change Complex.exp (2 * Real.pi * Complex.I *
    (((a : ℂ) + (b : ℂ) * ω₃) + conj ((a : ℂ) + (b : ℂ) * ω₃))) = 1
  rw [htrace]
  calc
    _ = Complex.exp (((2 * a - b : ℤ) : ℂ) *
          (2 * Real.pi * Complex.I)) := by congr 1; ring
    _ = Complex.exp (2 * Real.pi * Complex.I) ^ (2 * a - b : ℤ) :=
        Complex.exp_int_mul _ _
    _ = 1 := by rw [Complex.exp_two_pi_mul_I, one_zpow]
end OAI.ShortDraftTrace
