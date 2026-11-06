-- Prove2me | solution 1 for OAI.ShortDraftTrace.breveE_period_lam
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T22:28:27.917194+00:00
-- url     : https://prove2.me/submissions/b96a1066-20ed-4fdd-985d-6ec3f84ec17c

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

section Generic

variable (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0)
  (hconj : conj ω = ω ^ 2)

include hω hconj

omit hconj in
private lemma lam_ne_zero : (1 + 2 * ω : ℂ) ≠ 0 := by
  intro h
  have hw : ω = -(1 : ℂ) / 2 := by linear_combination h / 2
  rw [hw] at hω
  norm_num at hω

private lemma conj_lam : conj (1 + 2 * ω) = -(1 + 2 * ω) := by
  rw [map_add, map_one, map_mul, map_ofNat, hconj]
  linear_combination 2 * hω

omit hconj in
private lemma omega_sub_square : ω - ω ^ 2 = 1 + 2 * ω := by
  linear_combination -hω

private lemma trace_div_lam (a b : ℤ) :
    ((a : ℂ) + (b : ℂ) * ω) / (1 + 2 * ω) +
      conj (((a : ℂ) + (b : ℂ) * ω) / (1 + 2 * ω)) = (b : ℂ) := by
  have hl := lam_ne_zero ω hω
  simp only [map_div₀, map_add, map_intCast, map_mul, hconj,
    conj_lam ω hω hconj]
  rw [div_neg, ← sub_eq_add_neg, ← sub_div]
  calc
    ((a : ℂ) + (b : ℂ) * ω - ((a : ℂ) + (b : ℂ) * ω ^ 2)) /
        (1 + 2 * ω) = (b : ℂ) * (ω - ω ^ 2) / (1 + 2 * ω) := by ring
    _ = (b : ℂ) := by rw [omega_sub_square ω hω]; field_simp

private lemma trace_character_period (a b : ℤ) :
    Complex.exp (2 * Real.pi * Complex.I *
      ((((a : ℂ) + (b : ℂ) * ω) / (1 + 2 * ω)) +
       conj (((a : ℂ) + (b : ℂ) * ω) / (1 + 2 * ω)))) = 1 := by
  rw [trace_div_lam ω hω hconj a b]
  calc
    _ = Complex.exp ((b : ℂ) * (2 * Real.pi * Complex.I)) := by congr 1; ring
    _ = Complex.exp (2 * Real.pi * Complex.I) ^ b := Complex.exp_int_mul _ _
    _ = 1 := by rw [Complex.exp_two_pi_mul_I, one_zpow]

end Generic

private theorem omega_conj_aux : conj ω₃ = ω₃ ^ 2 := by
  rw [omega_sq]
  unfold ω₃
  simp only [map_div₀, map_add, map_neg, map_one, map_mul,
    Complex.conj_ofReal, Complex.conj_I, map_ofNat]
  ring

theorem solution (a b : ℤ) :
    breveE (((a : ℂ) + (b : ℂ) * ω₃) / (1 + 2 * ω₃)) = 1 := by
  change Complex.exp (2 * Real.pi * Complex.I *
    ((((a : ℂ) + (b : ℂ) * ω₃) / (1 + 2 * ω₃)) +
     conj (((a : ℂ) + (b : ℂ) * ω₃) / (1 + 2 * ω₃)))) = 1
  apply trace_character_period ω₃
  · rw [omega_sq]; ring
  · exact omega_conj_aux
