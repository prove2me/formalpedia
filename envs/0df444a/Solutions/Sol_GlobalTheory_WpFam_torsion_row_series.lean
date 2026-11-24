-- Prove2me | solution 1 for GlobalTheory.WpFam.torsion_row_series
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:36:37.430031+00:00
-- url     : https://prove2.me/submissions/c1aeb5c9-7c81-4892-90f5-59323fb661a3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZetaActRefl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RootOfUnityExpZModAdditiveCharacterProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TorsionPointRowSumEqQExpansionSeries
import Theorems.Thm_GlobalTheory_WpFam_AddCharZMod_main

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam
namespace GlobalTheory.WpFam
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in
private lemma exp_two_pi_I_div_pow_eq_mul (N : ℕ) (hN : (N : ℂ) ≠ 0) (d : ℕ) (τ c : ℂ) (j : ℕ) :
    Complex.exp (2 * Real.pi * Complex.I * ((d * τ + c) / N)) ^ j
      = Complex.exp (2 * Real.pi * Complex.I * (j * c) / N)
        * Complex.exp (2 * Real.pi * Complex.I * τ / N) ^ (d * j) := by
  rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 1
  push_cast
  field_simp
  ring
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in
private lemma wpFam_ch_natCast_mul (N : ℕ) [NeZero N] (j : ℕ) (b : ZMod N) :
    _root_.GlobalTheory.WpFam.ch N ((j : ZMod N) * b)
      = Complex.exp (2 * Real.pi * Complex.I * (j * (b.val : ℂ)) / N) := by
  have h := (_root_.GlobalTheory.WpFam.AddCharZMod.main N).1 ((j * b.val : ℕ) : ℤ)
  have hc : (((j * b.val : ℕ) : ℤ) : ZMod N) = (j : ZMod N) * b := by
    push_cast
    rw [ZMod.natCast_zmod_val]
  rw [hc] at h
  rw [h]
  congr 1
  first | (push_cast; ring) | push_cast
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in
private lemma wpFam_ch_neg_natCast_mul (N : ℕ) [NeZero N] (j : ℕ) (b : ZMod N) :
    _root_.GlobalTheory.WpFam.ch N (-((j : ZMod N) * b))
      = Complex.exp (2 * Real.pi * Complex.I * (j * -(b.val : ℂ)) / N) := by
  have h := (_root_.GlobalTheory.WpFam.AddCharZMod.main N).1 (-((j * b.val : ℕ) : ℤ))
  have hc : ((-((j * b.val : ℕ) : ℤ) : ℤ) : ZMod N) = -((j : ZMod N) * b) := by
    push_cast
    rw [ZMod.natCast_zmod_val]
  rw [hc] at h
  rw [h]
  congr 1
  first | (push_cast; ring) | push_cast
end GlobalTheory.WpFam
end

set_option autoImplicit false
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam
open GlobalTheory GlobalTheory.WpFam
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
namespace GlobalTheory.WpFam
namespace _root_.GlobalTheory.WpFam
theorem _root_.solution : ∀ (N : ℕ) [NeZero N] (e : ℕ) (τ : ℍ) (b : ZMod N) (d : ℕ+), 1 ≤ e → (∑' m : ℤ, 1 / ((((d : ℕ) : ℂ) * τ + (b.val : ℂ)) / N + m) ^ (e + 1) = (-(2 * (Real.pi : ℂ) * Complex.I)) ^ (e + 1) / (e.factorial : ℂ) * ∑' j : ℕ+, ((j : ℕ) : ℂ) ^ e * _root_.GlobalTheory.WpFam.ch N (((j : ℕ) : ZMod N) * b) * Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * τ / N) ^ ((d : ℕ) * (j : ℕ))) ∧ ∑' m : ℤ, 1 / ((-((d : ℕ) : ℂ) * τ + (b.val : ℂ)) / N + m) ^ (e + 1) = (-(2 * (Real.pi : ℂ) * Complex.I)) ^ (e + 1) / (e.factorial : ℂ) * ((-1) ^ (e + 1) * ∑' j : ℕ+, ((j : ℕ) : ℂ) ^ e * _root_.GlobalTheory.WpFam.ch N (-(((j : ℕ) : ZMod N) * b)) * Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * τ / N) ^ ((d : ℕ) * (j : ℕ))) := by
  intro N _ e τ b d he
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have him : ∀ c : ℂ, c.im = 0 → 0 < ((((d : ℕ) : ℂ) * τ + c) / N).im := by
    intro c hc
    rw [Complex.div_natCast_im]
    have h1 : (((d : ℕ) : ℂ) * (τ : ℂ) + c).im = ((d : ℕ) : ℝ) * τ.im := by
      simp [Complex.mul_im, hc]
    rw [h1]
    exact div_pos (mul_pos (by exact_mod_cast d.pos) τ.im_pos) hN
  constructor
  · have h := EisensteinSeries.qExpansion_identity_pnat he
      ⟨(((d : ℕ) : ℂ) * τ + (b.val : ℂ)) / N, him _ (Complex.natCast_im _)⟩
    simp only [UpperHalfPlane.coe_mk] at h
    have hS : (∑' j : ℕ+, ((j : ℕ) : ℂ) ^ e * Complex.exp (2 * Real.pi * Complex.I
        * ((((d : ℕ) : ℂ) * τ + (b.val : ℂ)) / N)) ^ (j : ℕ))
        = ∑' j : ℕ+, ((j : ℕ) : ℂ) ^ e * _root_.GlobalTheory.WpFam.ch N (((j : ℕ) : ZMod N) * b)
          * Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * τ / N) ^ ((d : ℕ) * (j : ℕ)) :=
      tsum_congr fun j => by
        rw [exp_two_pi_I_div_pow_eq_mul N hNc, wpFam_ch_natCast_mul]
        ring
    rw [h, hS]
    ring
  · have h := EisensteinSeries.qExpansion_identity_pnat he
      ⟨(((d : ℕ) : ℂ) * τ + -(b.val : ℂ)) / N, him _
        (by rw [Complex.neg_im, Complex.natCast_im, neg_zero])⟩
    simp only [UpperHalfPlane.coe_mk] at h
    have hterm : ∀ m : ℤ, 1 / ((-((d : ℕ) : ℂ) * τ + (b.val : ℂ)) / N + m) ^ (e + 1)
        = (-1) ^ (e + 1) * (1 / ((((d : ℕ) : ℂ) * τ + -(b.val : ℂ)) / N + ((-m : ℤ) : ℂ)) ^ (e + 1)) := by
      intro m
      rw [show (-((d : ℕ) : ℂ) * τ + (b.val : ℂ)) / N + m
          = -((((d : ℕ) : ℂ) * τ + -(b.val : ℂ)) / N + ((-m : ℤ) : ℂ)) by push_cast; ring]
      rw [neg_pow, one_div, one_div, mul_inv, ← inv_pow, inv_neg, inv_one]
    have hre : ∑' m : ℤ, 1 / ((((d : ℕ) : ℂ) * τ + -(b.val : ℂ)) / N + ((-m : ℤ) : ℂ)) ^ (e + 1)
        = ∑' m : ℤ, 1 / ((((d : ℕ) : ℂ) * τ + -(b.val : ℂ)) / N + (m : ℂ)) ^ (e + 1) :=
      (Equiv.neg ℤ).tsum_eq
        (fun m : ℤ => 1 / ((((d : ℕ) : ℂ) * τ + -(b.val : ℂ)) / N + (m : ℂ)) ^ (e + 1))
    have hS : (∑' j : ℕ+, ((j : ℕ) : ℂ) ^ e * Complex.exp (2 * Real.pi * Complex.I
        * ((((d : ℕ) : ℂ) * τ + -(b.val : ℂ)) / N)) ^ (j : ℕ))
        = ∑' j : ℕ+, ((j : ℕ) : ℂ) ^ e * _root_.GlobalTheory.WpFam.ch N (-(((j : ℕ) : ZMod N) * b))
          * Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * τ / N) ^ ((d : ℕ) * (j : ℕ)) :=
      tsum_congr fun j => by
        rw [exp_two_pi_I_div_pow_eq_mul N hNc, wpFam_ch_neg_natCast_mul]
        ring
    rw [tsum_congr hterm, tsum_mul_left, hre, h, hS]
    ring
end _root_.GlobalTheory.WpFam
end GlobalTheory.WpFam
