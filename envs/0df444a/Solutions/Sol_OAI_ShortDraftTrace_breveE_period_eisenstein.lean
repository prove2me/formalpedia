-- Prove2me | solution 1 for OAI.ShortDraftTrace.breveE_period_eisenstein
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T22:28:33.4302+00:00
-- url     : https://prove2.me/submissions/fed135f9-2b9b-4630-b9a2-bcdd3bd0c121

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

private lemma lam_ne_zero_aux (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) :
    (1 + 2 * ω : ℂ) ≠ 0 := by
  intro h
  have hw : ω = -(1 : ℂ) / 2 := by linear_combination h / 2
  rw [hw] at hω
  norm_num at hω

private lemma conj_lam_aux (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0)
    (hconj : conj ω = ω ^ 2) : conj (1 + 2 * ω) = -(1 + 2 * ω) := by
  rw [map_add, map_one, map_mul, map_ofNat, hconj]
  linear_combination 2 * hω

private lemma omega_sub_square_aux (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) :
    ω - ω ^ 2 = 1 + 2 * ω := by
  linear_combination -hω

private lemma trace_div_lam_aux (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0)
    (hconj : conj ω = ω ^ 2) (a b : ℤ) :
    ((a : ℂ) + (b : ℂ) * ω) / (1 + 2 * ω) +
      conj (((a : ℂ) + (b : ℂ) * ω) / (1 + 2 * ω)) = (b : ℂ) := by
  have hl := lam_ne_zero_aux ω hω
  simp only [map_div₀, map_add, map_intCast, map_mul, hconj,
    conj_lam_aux ω hω hconj]
  rw [div_neg, ← sub_eq_add_neg, ← sub_div]
  calc
    ((a : ℂ) + (b : ℂ) * ω - ((a : ℂ) + (b : ℂ) * ω ^ 2)) /
        (1 + 2 * ω) = (b : ℂ) * (ω - ω ^ 2) / (1 + 2 * ω) := by ring
    _ = (b : ℂ) := by rw [omega_sub_square_aux ω hω]; field_simp

private lemma omega_conj_aux : conj ω₃ = ω₃ ^ 2 := by
  rw [omega_sq]
  unfold ω₃
  simp only [map_div₀, map_add, map_neg, map_one, map_mul,
    Complex.conj_ofReal, Complex.conj_I, map_ofNat]
  ring

private lemma eisenstein_trace_period_aux (a b : ℤ) :
    Complex.exp (2 * Real.pi * Complex.I *
      ((((a : ℂ) + (b : ℂ) * ω₃) / (1 + 2 * ω₃)) +
       conj (((a : ℂ) + (b : ℂ) * ω₃) / (1 + 2 * ω₃)))) = 1 := by
  have hω : ω₃ ^ 2 + ω₃ + 1 = 0 := by rw [omega_sq]; ring
  rw [trace_div_lam_aux ω₃ hω omega_conj_aux a b]
  calc
    _ = Complex.exp ((b : ℂ) * (2 * Real.pi * Complex.I)) := by congr 1; ring
    _ = Complex.exp (2 * Real.pi * Complex.I) ^ b := Complex.exp_int_mul _ _
    _ = 1 := by rw [Complex.exp_two_pi_mul_I, one_zpow]

theorem solution (x : eisensteinSubring) :
    breveE (((x : ℂ) / (lamEis : ℂ))) = 1 := by
  obtain ⟨a, b, h⟩ := x.property
  change breveE ((x : ℂ) / (1 + 2 * ω₃)) = 1
  rw [h]
  exact eisenstein_trace_period_aux a b
