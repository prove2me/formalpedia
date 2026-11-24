-- Prove2me | solution 1 for GlobalTheory.WpFam.isIntegral_coefficients
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:37:08.603445+00:00
-- url     : https://prove2.me/submissions/8b112d74-b99a-4314-90c0-b65fedd09375

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZetaActRefl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RootOfUnityExpZModAdditiveCharacterProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsIntegralWeierstrassTorsionQCoefficients
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
private lemma one_sub_mul_sum_range_natCast_mul_pow_add (x : ℂ) (n : ℕ) :
    (1 - x) * ∑ i ∈ Finset.range n, (i : ℂ) * x ^ i + n * x ^ n =
      ∑ i ∈ Finset.range n, x ^ (i + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ← ih]
    push_cast
    ring
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in
private lemma isIntegral_natCast_div_one_sub_of_isIntegral_of_ne_one (ζ : ℂ) (M : ℕ) (hζ : IsIntegral ℤ ζ)
    (hM : ζ ^ M = 1) (h1 : ζ ≠ 1) : IsIntegral ℤ ((M : ℂ) / (1 - ζ)) := by
  have hsub : (1 - ζ) ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  have hgeom : ∑ i ∈ Finset.range M, ζ ^ (i + 1) = 0 := by
    simp_rw [pow_succ]
    rw [← Finset.sum_mul, geom_sum_eq h1, hM, sub_self, zero_div, zero_mul]
  have key := one_sub_mul_sum_range_natCast_mul_pow_add ζ M
  rw [hgeom, hM, mul_one] at key
  have hq : (M : ℂ) / (1 - ζ) = -∑ i ∈ Finset.range M, (i : ℂ) * ζ ^ i := by
    rw [div_eq_iff hsub]
    linear_combination key
  rw [hq]
  exact (IsIntegral.sum _ fun i _ => (isIntegral_natCast i).mul (hζ.pow i)).neg
end GlobalTheory.WpFam
end

set_option autoImplicit false
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam
open GlobalTheory GlobalTheory.WpFam
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
namespace GlobalTheory.WpFam
namespace _root_.GlobalTheory.WpFam
theorem _root_.solution : ∀ (N : ℕ) [NeZero N] (M : ℕ) (x : Fin 2 → ZMod N) (k : ℕ),
    0 < M → M • x = 0 → IsIntegral ℤ ((M : ℂ) ^ 2 * _root_.GlobalTheory.WpFam.cB N x k) ∧
      IsIntegral ℤ ((M : ℂ) ^ 3 * _root_.GlobalTheory.WpFam.cD N x k) ∧ IsIntegral ℤ (12 * (M : ℂ) ^ 2 * _root_.GlobalTheory.WpFam.cP N x k) ∧
      IsIntegral ℤ (12 * _root_.GlobalTheory.WpFam.cG N k) := by
  intro N _ M x k _ hx
  obtain ⟨-, -, hzero, -, hpow, -, -, hint⟩ :=
    _root_.GlobalTheory.WpFam.AddCharZMod.main N
  have h12 : IsIntegral ℤ (12 : ℂ) := by simpa using isIntegral_natCast (R := ℤ) (B := ℂ) 12
  have htw : ∀ (a : ℕ) (s : ℂ), IsIntegral ℤ s →
      IsIntegral ℤ (_root_.GlobalTheory.WpFam.cSum N a s x k) := by
    intro a s hs
    unfold _root_.GlobalTheory.WpFam.cSum
    refine IsIntegral.sum _ fun m _ => ((isIntegral_natCast m).pow a).mul ?_
    refine IsIntegral.add ?_ (hs.mul ?_)
    · split_ifs
      · exact hint _
      · exact isIntegral_zero
    · split_ifs
      · exact hint _
      · exact isIntegral_zero
  have hG : IsIntegral ℤ (12 * _root_.GlobalTheory.WpFam.cG N k) := by
    unfold _root_.GlobalTheory.WpFam.cG
    split_ifs
    · rw [show (12 : ℂ) * (-1 / 12) = -1 by norm_num]
      exact isIntegral_one.neg
    · exact h12.mul ((isIntegral_natCast 2).mul (isIntegral_natCast _))
    · simp [isIntegral_zero]
  have hB : IsIntegral ℤ ((M : ℂ) ^ 2 * _root_.GlobalTheory.WpFam.cB N x k) ∧
      IsIntegral ℤ ((M : ℂ) ^ 3 * _root_.GlobalTheory.WpFam.cD N x k) := by
    unfold _root_.GlobalTheory.WpFam.cB _root_.GlobalTheory.WpFam.cD
    split_ifs with hk h0
    · by_cases h1 : _root_.GlobalTheory.WpFam.ch N (x 1) = 1
      · simp [h1, isIntegral_zero]
      · have hζM : _root_.GlobalTheory.WpFam.ch N (x 1) ^ M = 1 := by
          have hx1 := congr_fun hx 1
          simp only [Pi.smul_apply, nsmul_eq_mul, Pi.zero_apply] at hx1
          rw [← hpow, hx1, hzero]
        have hq := isIntegral_natCast_div_one_sub_of_isIntegral_of_ne_one _ M (hint (x 1)) hζM h1
        constructor
        · rw [show (M : ℂ) ^ 2 * (_root_.GlobalTheory.WpFam.ch N (x 1) / (1 - _root_.GlobalTheory.WpFam.ch N (x 1)) ^ 2)
              = _root_.GlobalTheory.WpFam.ch N (x 1) * ((M : ℂ) / (1 - _root_.GlobalTheory.WpFam.ch N (x 1))) ^ 2 by
              rw [div_pow]; ring]
          exact (hint _).mul (hq.pow 2)
        · rw [show (M : ℂ) ^ 3 * (_root_.GlobalTheory.WpFam.ch N (x 1) * (1 + _root_.GlobalTheory.WpFam.ch N (x 1)) /
              (1 - _root_.GlobalTheory.WpFam.ch N (x 1)) ^ 3) = _root_.GlobalTheory.WpFam.ch N (x 1) *
              (1 + _root_.GlobalTheory.WpFam.ch N (x 1)) *
              ((M : ℂ) / (1 - _root_.GlobalTheory.WpFam.ch N (x 1))) ^ 3 by rw [div_pow]; ring]
          exact ((hint _).mul (isIntegral_one.add (hint _))).mul (hq.pow 3)
    · simp [isIntegral_zero]
    · exact ⟨((isIntegral_natCast M).pow 2).mul (htw 1 1 isIntegral_one),
        ((isIntegral_natCast M).pow 3).mul (htw 2 (-1) isIntegral_one.neg)⟩
  refine ⟨hB.1, hB.2, ?_, hG⟩
  unfold _root_.GlobalTheory.WpFam.cP
  split_ifs
  · simp [isIntegral_zero]
  · rw [show 12 * (M : ℂ) ^ 2 * (_root_.GlobalTheory.WpFam.cB N x k - _root_.GlobalTheory.WpFam.cG N k)
        = 12 * ((M : ℂ) ^ 2 * _root_.GlobalTheory.WpFam.cB N x k) -
          (M : ℂ) ^ 2 * (12 * _root_.GlobalTheory.WpFam.cG N k) by ring]
    exact (h12.mul hB.1).sub (((isIntegral_natCast M).pow 2).mul hG)
end _root_.GlobalTheory.WpFam
end GlobalTheory.WpFam
